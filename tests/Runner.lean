/-
The corpus runner: checks every `tests/cases/<name>/input.lrep` and compares diagnostic
codes and lines, claim verdicts and, where given, the residue against `expect.json`.
-/
import Lrep
import Lrep.Server
import Lrep.Diff
import Lrep.Dataflow
import Lrep.Runtime
import Lrep.Core
import Lrep.Audit

open Lrep
open Lean (Json)

structure Outcome where
  name : String
  failures : List String

def codesOf (r : FileResult) : List (String × Nat) :=
  (r.diags.map fun d => (d.code, d.span.line)).mergeSort fun a b =>
    a.2 < b.2 || (a.2 == b.2 && a.1 ≤ b.1)

def showCodes (cs : List (String × Nat)) : String :=
  "[" ++ ", ".intercalate (cs.map fun (c, l) => s!"{c}@{l}") ++ "]"

def runCase (dir : System.FilePath) : IO Outcome := do
  let name := dir.fileName.getD dir.toString
  let expectSrc ← IO.FS.readFile (dir / "expect.json")
  let r ← checkFile (dir / "input.lrep").toString
  -- Read the result back through the same JSON `lrep check --json` prints.
  let out ← IO.ofExcept (Json.parse (r.toJ.pretty 0))
  let expect ← IO.ofExcept (Json.parse expectSrc)
  let mut fails : List String := []
  let want ← IO.ofExcept (expect.getObjValAs? (List (String × Nat)) "codes")
  let want := want.mergeSort fun a b => a.2 < b.2 || (a.2 == b.2 && a.1 ≤ b.1)
  let diags ← IO.ofExcept (out.getObjValAs? (List Json) "diagnostics")
  let got ← diags.mapM fun d => do
    pure ((← IO.ofExcept (d.getObjValAs? String "code")), (← IO.ofExcept (d.getObjValAs? Nat "line")))
  let got := got.mergeSort fun a b => a.2 < b.2 || (a.2 == b.2 && a.1 ≤ b.1)
  if got != want then
    fails := fails ++ [s!"codes: expected {showCodes want}, got {showCodes got}"]
  match expect.getObjVal? "claims" with
  | .ok (.obj kvs) =>
    let sections ← IO.ofExcept (out.getObjValAs? (List Json) "sections")
    let claims ← sections.flatMapM fun s => IO.ofExcept (s.getObjValAs? (List Json) "claims")
    for (text, v) in kvs.toList do
      let wantHolds ← IO.ofExcept v.getBool?
      let found := claims.find? fun c => (c.getObjValAs? String "text").toOption == some text
      match found with
      | none => fails := fails ++ [s!"claim \"{text}\" not found"]
      | some c =>
        let holds ← IO.ofExcept (c.getObjValAs? Bool "holds")
        if holds != wantHolds then
          fails := fails ++ [s!"claim \"{text}\": expected holds={wantHolds}, got {holds}"]
  | _ => pure ()
  match expect.getObjValAs? String "residue" with
  | .ok res =>
    if !r.residueOk then fails := fails ++ ["residue: refused"]
    else if r.residue != res then
      fails := fails ++ [s!"residue: expected\n{res}\ngot\n{r.residue}"]
  | .error _ => pure ()
  pure ⟨name, fails⟩

/-- Language-server checks: hover text and lenses on corpus files. Each is a file, a
1-based position, and words the hover must contain. -/
def hoverChecks : List (String × Nat × Nat × String) :=
  [("serve-log", 3, 42, "refers to the result of `open` on line 3, a file"),
   ("serve-log", 3, 37, "**serve**"),
   ("serve-log", 6, 40, "✗ fails; witnesses on line 3"),
   ("serve-log", 6, 15, "✓ holds"),
   ("ship-old-logs", 6, 7, "refers to the current file of the loop on line 5"),
   ("ship-old-logs", 5, 19, "refers to the result of `list` on line 3, a list of file"),
   ("description-unique", 4, 12, "refers to the result of `open` on line 3, a file"),
   ("qual-location-ok", 3, 10, "✓ the description holds"),
   ("qual-provenance-bad", 4, 11, "✗ \"log\" describes a value whose contents come from \"/var/db/production.db\""),
   ("qual-provenance-bad", 4, 11, "its contents come from \"/var/db/production.db\"")]

def runServerChecks : IO Nat := do
  let mut failed := 0
  for (name, line, col, want) in hoverChecks do
    let r ← checkFile s!"tests/cases/{name}/input.lrep"
    let got := (hoverAt r line col).getD "(no hover)"
    if (got.splitOn want).length < 2 then
      failed := failed + 1
      IO.println s!"FAIL  hover {name}:{line}:{col}\n      expected to contain: {want}\n      got: {got}"
  let r ← checkFile "tests/cases/ship-old-logs/input.lrep"
  let ls := lenses r
  let want := ["✓ 2 claims hold",
               "reads /var/log/app · writes s3://acme-logs/app · connects to s3://acme-logs"]
  if ls.map (·.2) != want then
    failed := failed + 1
    IO.println s!"FAIL  lenses ship-old-logs: got {ls.map (·.2)}"
  -- The dataflow view: the listing feeds the loop, the element feeds compress, and the
  -- archive feeds upload.
  let dot := r.dataflow
  for edge in ["b0_0 -> b0_1 [label=\"in\"]", "b0_1 -> b0_2 [label=\"object\"]", "b0_2 -> b0_3 [label=\"object\"]"] do
    if (dot.splitOn edge).length < 2 then
      failed := failed + 1
      IO.println s!"FAIL  dataflow ship-old-logs: missing {edge}"
  -- Semantic tokens: five numbers per token, the heading first, as a namespace.
  let sr ← checkFile "tests/cases/serve-log/input.lrep"
  let data := semanticData sr
  if data.length % 5 != 0 || data.take 5 != [0, 0, 15, 0, 0] then
    failed := failed + 1
    IO.println s!"FAIL  semantic tokens serve-log: {data.take 10}"
  -- `serve` on line 3 is a program word with the `op` modifier.
  let progIdx := (semanticTypes.idxOf? "lrepProgram").getD 99
  let opBit := 2 ^ ((semanticModifiers.idxOf? "op").getD 99)
  let spans := semanticSpans sr
  if !spans.any (fun (sp, ty, m) => sp.line == 3 && sp.col == 35 && ty == progIdx && m == opBit) then
    failed := failed + 1
    IO.println "FAIL  semantic tokens: serve is not a program word marked op"
  -- The core view: the composite op's call, then its inlined body indented under it,
  -- with values numbered without gaps.
  let cr ← checkFile "examples/composite/retire-old-logs.lrep"
  let core := cr.coreText
  for want in ["v0 := list(directory \"/var/log/app\")", "for v1 in v0 do", "      retire(v1, to: url",
               "        v2 := compress(v1)\n        upload(v2, to: url", "        delete(v1)\n    end", "claim never spawn"] do
    if (core.splitOn want).length < 2 then
      failed := failed + 1
      IO.println s!"FAIL  core view: missing {want}"
  IO.println s!"{hoverChecks.length + 12 - failed}/{hoverChecks.length + 12} server and view checks passed"
  pure failed

/-- Claim-diff checks: each `tests/diffs/<name>/` has `old.lrep`, `new.lrep` and an
`expect.json` listing `[kind, first claim text]` per change and whether it is flagged. -/
def runDiffChecks : IO Nat := do
  let root : System.FilePath := "tests/diffs"
  let dirs := ((← root.readDir).map (·.path)).toList.mergeSort fun a b => a.toString ≤ b.toString
  let mut failed := 0
  for d in dirs do
    let ro ← checkFile (d / "old.lrep").toString
    let rn ← checkFile (d / "new.lrep").toString
    let ds := diffFiles ro rn
    let got := ds.flatMap fun (_, cs) => cs.map fun c => match c with
      | .added v => ("added", v.claim.text) | .removed v => ("removed", v.claim.text)
      | .weakened o _ => ("weakened", o.claim.text) | .strengthened o _ => ("strengthened", o.claim.text)
      | .verdict _ n => ("verdict", n.claim.text)
    let gotFlag := ds.any (·.2.any Change.flagged)
    let expect ← IO.ofExcept (Json.parse (← IO.FS.readFile (d / "expect.json")))
    let want ← IO.ofExcept (expect.getObjValAs? (List (String × String)) "changes")
    let wantFlag ← IO.ofExcept (expect.getObjValAs? Bool "flagged")
    if got != want || gotFlag != wantFlag then
      failed := failed + 1
      IO.println s!"FAIL  diff {d.fileName.getD ""}: expected {want} flagged={wantFlag}, got {got} flagged={gotFlag}"
  IO.println s!"{dirs.length - failed}/{dirs.length} diff checks passed"
  pure failed

/-- Runtime checks: each `tests/run/<name>/` sets up files in a fresh root, runs the program
there, and compares which sections completed, whether the sandbox stopped it, and the files
left behind. -/
def runRuntimeChecks : IO Nat := do
  let root : System.FilePath := "tests/run"
  let dirs := ((← root.readDir).map (·.path)).toList.mergeSort fun a b => a.toString ≤ b.toString
  let mut failed := 0
  for d in dirs do
    let name := d.fileName.getD ""
    let jail : System.FilePath := (← IO.currentDir) / ".lake" / "run-tests" / name
    if ← jail.pathExists then IO.FS.removeDirAll jail
    IO.FS.createDirAll jail
    let setup ← IO.ofExcept (Json.parse (← IO.FS.readFile (d / "setup.json")))
    let expect ← IO.ofExcept (Json.parse (← IO.FS.readFile (d / "expect.json")))
    let real (p : String) : System.FilePath := (p.splitOn "/").filter (· != "") |>.foldl (fun (a : System.FilePath) (s : String) => a / s) jail
    if let .ok (.obj fs) := setup.getObjVal? "files" then
      for (p, v) in fs.toList do
        if let some dir := (real p).parent then IO.FS.createDirAll dir
        IO.FS.writeFile (real p) (v.getStr?.toOption.getD "")
    if let .ok olds := setup.getObjValAs? (List String) "old" then
      for p in olds do
        let _ ← IO.Process.output { cmd := "touch", args := #["-t", "200001010000", (real p).toString] }
    let r ← checkFile (d / "input.lrep").toString
    let proj ← loadProject d
    let mut fails : List String := []
    if r.hasErrors then fails := fails ++ ["the program has errors"]
    else
      let res ← runFile proj.lex r (some jail)
      let wantDone ← IO.ofExcept (expect.getObjValAs? (List Bool) "completed")
      let gotDone := res.sections.map (·.2.1)
      if gotDone != wantDone then
        fails := fails ++ [s!"completed: expected {wantDone}, got {gotDone}; log {res.sections.map (·.2.2)}"]
      let wantSandbox ← IO.ofExcept (expect.getObjValAs? Bool "sandbox")
      if res.sandboxViolation != wantSandbox then
        fails := fails ++ [s!"sandbox: expected {wantSandbox}, got {res.sandboxViolation}"]
      if let .ok (.obj fs) := expect.getObjVal? "files" then
        for (p, v) in fs.toList do
          let want := v.getStr?.toOption.getD ""
          if !(← (real p).pathExists) then fails := fails ++ [s!"{p} is missing"]
          else
            let got ← IO.FS.readFile (real p)
            if got != want then fails := fails ++ [s!"{p}: expected {want.quote}, got {got.quote}"]
      if let .ok ps := expect.getObjValAs? (List String) "absent" then
        for p in ps do
          if ← (real p).pathExists then fails := fails ++ [s!"{p} should not exist"]
    if !fails.isEmpty then
      failed := failed + 1
      IO.println s!"FAIL  run {name}"
      for f in fails do IO.println s!"      {f}"
  IO.println s!"{dirs.length - failed}/{dirs.length} runtime checks passed"
  pure failed

/-- Gloss-audit checks, offline: the request's shape, and parsing canned responses. -/
def runAuditChecks : IO Nat := do
  let r ← checkFile "tests/cases/prog-backup-config/input.lrep"
  let req := (auditRequest r).compact
  let mut failed := 0
  for want in ["\"model\": \"claude-opus-5-5\"", "\"fallbacks\": \"default\"", "\"effort\": \"medium\"",
               "json_schema", "`Config` refers to the result of `read` on line 3"] do
    if (req.splitOn want).length < 2 then
      failed := failed + 1
      IO.println s!"FAIL  audit request lacks {want}"
  let found := "{\"stop_reason\": \"end_turn\", \"content\": [{\"type\": \"text\", \"text\": " ++
    "\"{\\\"findings\\\": [{\\\"line\\\": 4, \\\"gloss\\\": \\\"backup\\\", \\\"concern\\\": \\\"x\\\"}]}\"}]}"
  match parseAudit found with
  | .ok [f] => if f.line != 4 || f.gloss != "backup" then failed := failed + 1; IO.println "FAIL  audit finding misread"
  | _ => failed := failed + 1; IO.println "FAIL  audit findings not parsed"
  match parseAudit "{\"stop_reason\": \"refusal\", \"content\": []}" with
  | .error _ => pure ()
  | .ok _ => failed := failed + 1; IO.println "FAIL  audit refusal not reported"
  match parseAudit "{\"type\": \"error\", \"error\": {\"message\": \"bad key\"}}" with
  | .error e => if (e.splitOn "bad key").length < 2 then failed := failed + 1; IO.println s!"FAIL  audit error: {e}"
  | .ok _ => failed := failed + 1; IO.println "FAIL  audit API error not reported"
  IO.println s!"{8 - failed}/8 audit checks passed"
  pure failed

/-- Vocabulary-diff checks: each `tests/vocab-diffs/<name>/` has `old.json`, `new.json` and
an `expect.json` listing `[flagged, words the change's text contains]` per change. -/
def runVocabDiffChecks : IO Nat := do
  let root : System.FilePath := "tests/vocab-diffs"
  let dirs := ((← root.readDir).map (·.path)).toList.mergeSort fun a b => a.toString ≤ b.toString
  let mut failed := 0
  for d in dirs do
    let va ← IO.ofExcept (loadVocab (← IO.FS.readFile (d / "old.json")))
    let vb ← IO.ofExcept (loadVocab (← IO.FS.readFile (d / "new.json")))
    let got := diffVocabs va vb
    let expect ← IO.ofExcept (Json.parse (← IO.FS.readFile (d / "expect.json")))
    let want ← IO.ofExcept (expect.getObjValAs? (List (Bool × String)) "changes")
    let ok := got.length == want.length && (got.zip want).all fun (g, (f, t)) => g.flagged == f && (g.text.splitOn t).length > 1
    if !ok then
      failed := failed + 1
      IO.println s!"FAIL  vocab-diff {d.fileName.getD ""}: expected {want}, got {got.map fun c => (c.flagged, c.text)}"
  IO.println s!"{dirs.length - failed}/{dirs.length} vocab-diff checks passed"
  pure failed

/-- Example checks: every program in `examples/` passes, except those in `caught/`, which
fail with the codes `examples/README.md` shows. Bodies of composite ops (`vocab/`) aren't
programs on their own. -/
def exampleCodes : List (String × List String) :=
  [("caught/claims-too-little.lrep", ["E040"]),
   ("caught/misleading-words.lrep", ["E034", "E034", "E034"]),
   ("caught/run-defeats-claims.lrep", ["E040"]),
   ("caught/unknown-verb.lrep", ["E020"])]

partial def lrepFiles (dir : System.FilePath) : IO (List System.FilePath) := do
  let mut out := []
  for e in ← dir.readDir do
    if ← e.path.isDir then
      if e.fileName != "vocab" then out := out ++ (← lrepFiles e.path)
    else if e.path.extension == some "lrep" then out := out ++ [e.path]
  pure out

def runExampleChecks : IO Nat := do
  let files := (← lrepFiles "examples").mergeSort fun a b => a.toString ≤ b.toString
  let mut failed := 0
  for f in files do
    let rel := (f.toString.drop "examples/".length).toString
    let r ← checkFile f.toString
    let got := r.diags.filter Diagnostic.isError |>.map (·.code)
    let want := (exampleCodes.lookup rel).getD []
    if got != want then
      failed := failed + 1
      IO.println s!"FAIL  example {rel}: expected {want}, got {got}"
  IO.println s!"{files.length - failed}/{files.length} example checks passed"
  pure failed

def main : IO UInt32 := do
  let root : System.FilePath := "tests/cases"
  let entries ← root.readDir
  let dirs := (entries.map (·.path)).toList.mergeSort fun a b => a.toString ≤ b.toString
  let mut failed := 0
  for d in dirs do
    if ← (d / "input.lrep").pathExists then
      let o ← runCase d
      if o.failures.isEmpty then IO.println s!"ok    {o.name}"
      else
        failed := failed + 1
        IO.println s!"FAIL  {o.name}"
        for f in o.failures do IO.println s!"      {f}"
  IO.println s!"{dirs.length - failed}/{dirs.length} cases passed"
  let serverFailed ← runServerChecks
  let diffFailed ← runDiffChecks
  let runFailed ← runRuntimeChecks
  let auditFailed ← runAuditChecks
  let vocabFailed ← runVocabDiffChecks
  let exampleFailed ← runExampleChecks
  pure (if failed + serverFailed + diffFailed + runFailed + auditFailed + vocabFailed + exampleFailed == 0 then 0 else 1)
