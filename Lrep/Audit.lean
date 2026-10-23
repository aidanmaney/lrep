/-
The gloss audit (`lrep audit FILE`): asks a model whether a program's descriptions agree
with what it does. Gloss is unchecked, so "the backup file" on a value that came from the
production database would otherwise pass review. The audit annotates review and never fails
a build: compilation never depends on a model.

The request goes to the Claude Messages API over HTTPS with `curl`, since Lean has no
Anthropic SDK. Credentials come from `ANTHROPIC_API_KEY`, or from an `ant auth login` profile.
-/
import Lrep
import Lrep.Server

namespace Lrep
open Lean (Json)

def auditModel : String := "claude-opus-5-5"

private def auditSystem : String :=
  "You audit programs written in lrep, a language whose source is constrained English. " ++
  "Each sentence mixes program words with gloss: descriptive words the compiler ignores. " ++
  "The residue is the program with the gloss removed, and the references say what each " ++
  "`it`, name and description resolves to. Report only gloss that misdescribes what the " ++
  "program does: a description that contradicts where a value came from, what an op does, " ++
  "or what a section is about. Claims (sentences starting \"This section\") are verified by the " ++
  "checker, and a claim constrains only the effect kind it names: \"only reads from X\" says nothing " ++
  "about deletes. Never report a claim. Do not report style, grammar or missing detail. An empty list " ++
  "is the right answer for a program whose descriptions are accurate."

mutual
/-- Every sentence, list items included, in source order. -/
def flatSent : TSent → List TSent
  | t@(.mk _ _ _ _ sub) => t :: flatItems sub
def flatItems : List (List TSent) → List TSent
  | [] => []
  | it :: rest => flatSents it ++ flatItems rest
def flatSents : List TSent → List TSent
  | [] => []
  | s :: rest => flatSent s ++ flatSents rest
end

/-- What the model sees for one file: each sentence as written, its residue, and what its
references resolve to. -/
def auditInput (r : FileResult) : String :=
  let refsOn (line : Nat) := r.refs.filter (·.1.line == line) |>.map (·.2)
  let body := r.tsections.flatMap fun s =>
    s!"## {s.name}" :: ((flatSents s.sents).flatMap fun t =>
      let line := t.span.line
      let written := r.lines.getD (line - 1) ""
      let refs := refsOn line
      [s!"line {line}: {trimStr written}", s!"  residue: {residueLine t.toks t.term}"] ++
        refs.map (s!"  {·}"))
  "\n".intercalate body

private def findingsSchema : J :=
  .obj [("type", .str "object"),
        ("properties", .obj [("findings", .obj [("type", .str "array"),
          ("items", .obj [("type", .str "object"),
            ("properties", .obj [("line", .obj [("type", .str "integer")]),
                                 ("gloss", .obj [("type", .str "string")]),
                                 ("concern", .obj [("type", .str "string")])]),
            ("required", .arr [.str "line", .str "gloss", .str "concern"]),
            ("additionalProperties", .bool false)])])]),
        ("required", .arr [.str "findings"]),
        ("additionalProperties", .bool false)]

/-- The Messages API request body. -/
def auditRequest (r : FileResult) : J :=
  .obj [("model", .str auditModel), ("max_tokens", .num 16000),
        ("fallbacks", .str "default"),
        ("system", .str auditSystem),
        ("output_config", .obj [("effort", .str "medium"),
          ("format", .obj [("type", .str "json_schema"), ("schema", findingsSchema)])]),
        ("messages", .arr [.obj [("role", .str "user"),
          ("content", .str s!"Audit this program's gloss.\n\n{auditInput r}")]])]

/-- Request headers, given a credential: an API key, or an OAuth access token. -/
def auditHeaders (cred : Sum String String) : List String :=
  let auth := match cred with
    | .inl key => [s!"x-api-key: {key}"]
    | .inr token => [s!"Authorization: Bearer {token}"]
  let betas := match cred with
    | .inl _ => "server-side-fallback-2026-07-01"
    | .inr _ => "server-side-fallback-2026-07-01,oauth-2025-04-20"
  ["Content-Type: application/json", "anthropic-version: 2026-10-21", s!"anthropic-beta: {betas}"] ++ auth

/-- An API key from the environment, else a short-lived token from the `ant` CLI's profile. -/
def auditCredential : IO (Option (Sum String String)) := do
  if let some k := (← IO.getEnv "ANTHROPIC_API_KEY") then
    if !k.isEmpty then return some (.inl k)
  try
    let out ← IO.Process.output { cmd := "ant", args := #["auth", "print-credentials", "--access-token"] }
    let t := trimStr out.stdout
    if out.exitCode == 0 && !t.isEmpty then return some (.inr t) else return none
  catch _ => return none

structure Finding where
  line : Nat
  gloss : String
  concern : String

/-- Reads the findings out of a Messages API response. -/
def parseAudit (resp : String) : Except String (List Finding) := do
  let j ← Json.parse resp
  if let .ok e := j.getObjVal? "error" then
    throw s!"the API returned an error: {(e.getObjValAs? String "message").toOption.getD e.compress}"
  let stop := (j.getObjValAs? String "stop_reason").toOption.getD ""
  if stop == "refusal" then throw "the model declined to audit this file"
  let blocks ← j.getObjValAs? (List Json) "content"
  let text := String.join (blocks.filterMap fun b =>
    if (b.getObjValAs? String "type").toOption == some "text" then (b.getObjValAs? String "text").toOption else none)
  let out ← Json.parse text
  let fs ← out.getObjValAs? (List Json) "findings"
  fs.mapM fun f => do
    pure ⟨← f.getObjValAs? Nat "line", ← f.getObjValAs? String "gloss", ← f.getObjValAs? String "concern"⟩

/-- Sends the request. Headers go through a temporary file so the credential never appears
in the process list. -/
def sendAudit (cred : Sum String String) (body : J) : IO String := do
  let dir ← IO.FS.createTempDir
  let hdr := dir / "headers"
  IO.FS.writeFile hdr ("\n".intercalate (auditHeaders cred) ++ "\n")
  try
    let args := #["-sS", "https://api.anthropic.com/v1/messages", "-H", s!"@{hdr}", "--data-binary", "@-"]
    let child ← IO.Process.spawn { cmd := "curl", args, stdin := .piped, stdout := .piped, stderr := .piped }
    let (stdin, child) ← child.takeStdin
    stdin.putStr body.compact
    stdin.flush
    let out ← child.stdout.readToEnd
    let err ← child.stderr.readToEnd
    let code ← child.wait
    if code != 0 then throw (IO.userError s!"curl failed: {trimStr err}")
    pure out
  finally
    IO.FS.removeDirAll dir

end Lrep
