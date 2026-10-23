/-
The language server (`lrep lsp`): diagnostics as you type, hover for what `it`, each
description and each name refers to and for each op's signature, and a code lens per section
with its inferred effects and the status of every claim. A failing claim's diagnostic lists
its witnesses, the counterexample path.

Hover and lenses are pure functions of a `FileResult`; only the JSON-RPC loop does IO.
Columns are code points, which match LSP's UTF-16 columns for ASCII sources.
-/
import Lrep

namespace Lrep
open Lean (Json)

/-! ## Hover -/

private def contains (sp : Span) (line col : Nat) : Bool :=
  sp.line == line && sp.col ≤ col && col < max sp.endCol (sp.col + 1)

private def width (sp : Span) : Nat := sp.endCol - sp.col

mutual
def sentToks : TSent → List Tok
  | .mk toks _ _ _ sub => toks ++ itemToks sub
def itemToks : List (List TSent) → List Tok
  | [] => []
  | it :: rest => sentsToks it ++ itemToks rest
def sentsToks : List TSent → List Tok
  | [] => []
  | s :: rest => sentToks s ++ sentsToks rest
end

def FileResult.tokens (r : FileResult) : List Tok := r.tsections.flatMap (sentsToks ·.sents)

private def sortsText (ps : List String) : String := " or ".intercalate ps

private def effectText (ds : List EffDecl) : String :=
  if ds.isEmpty then "none"
  else ", ".intercalate (ds.map fun d =>
    let on := match d.on with
      | .object => "its object" | .subject => "its subject"
      | .label l => s!"its \"{l}\" argument" | .top => "anything"
    s!"{d.kind} {on}")

/-- An op's signature: its object, labels, result, effects and forms. -/
def opSignature (o : OpDef) : String :=
  let obj := if o.object.isEmpty then "" else s!" ‹{sortsText o.object}›"
  let labels := o.labels.map fun (l, ps) =>
    if o.required.contains l then s!" {l} ‹{sortsText ps}›" else s!" [{l} ‹{sortsText ps}›]"
  let ret := match o.returns with
    | some r => s!" → {if r.list then s!"a list of {r.sort}" else r.sort}"
    | none => ""
  let claims := match o.names with
    | some k => s!"in claims: names every {k} effect" ++
        (if o.claimLabels.isEmpty then "" else s!", labels {", ".intercalate o.claimLabels}")
    | none => "in claims: names its own calls"
  s!"**{o.base}**{obj}{String.join labels}{ret}\n\neffects: {effectText o.effects}\n\n{claims}\n\nforms: {", ".intercalate (o.forms.map (·.2) |>.eraseDups)}"

private def structureMeaning : String → String
  | "it" => "the topic; must not be a list"
  | "them" => "the topic; must be a list"
  | "then" => "sequence" | "and" => "collect values, conditions or claims"
  | "or" => "either condition" | "if" => "conditional" | "otherwise" => "alternative to the preceding if"
  | "not" => "negates a predicate" | "is" => "applies a predicate" | "are" => "applies a predicate to a list"
  | "for each" => "iterates over a finite list" | "as" => "declares a name"
  | "this section" => "the enclosing section, as a claim's subject"
  | "fails" => "the previous statement failed"
  | _ => "structure word"

/-- What a token is, for hover. -/
def describeTok (t : Tok) : Option String :=
  match t.cls with
  | .op o _ => some (opSignature o)
  | .pred p =>
    let labels := p.labels.map fun (l, ps) => s!" {l} ‹{sortsText ps}›"
    some s!"**{p.forms.headD ""}** (predicate) on ‹{sortsText p.subject}›{String.join labels}\n\neffects: {effectText p.effects}"
  | .sort s pl =>
    let lit := match s.literal with
      | .path => "a path string" | .url => "a URL string" | .string => "a string"
      | .int => "a number" | .none => "no literal (in memory)"
    some s!"**{s.name}** (sort{if pl then ", plural: a list" else ""}), written as {lit}"
  | .unit u => some s!"unit of **{u.sort}**"
  | .const c => some s!"**{c.forms.headD ""}** (constant {c.sort})"
  | .qual q =>
    let w := if q.within.isEmpty then "" else s!"; lies within {", ".intercalate q.within}"
    let f := if q.origins.isEmpty then "" else s!"; its contents come from {", ".intercalate q.origins}"
    some s!"**{q.forms.headD ""}** (qualifier, checked){w}{f}"
  | .struct w => some s!"**{w}**: {structureMeaning w}"
  | .label l => some s!"**{l}**: argument label"
  | .claim w => some s!"**{w}**: claim word"
  | .name => some s!"**{t.text}**: a name"
  | .gloss | .article => some "gloss: the compiler ignores this word"
  | .aside => some "aside: an explanation the compiler ignores"
  | _ => none

/-- Hover text at a 1-based line and column: a reference's referent, a claim's status, or
the token's meaning, whichever span is smallest. -/
def hoverAt (r : FileResult) (line col : Nat) : Option String :=
  let refs := r.refs.filter (contains ·.1 line col) |>.map fun (sp, m) => (sp, m)
  let claims := r.sections.flatMap fun s => s.verdicts.filterMap fun v =>
    if contains v.claim.span line col then
      let lines := (v.witnesses.map (·.site.line)).eraseDups
      let status := if v.holds then "✓ holds" else
        "✗ fails; witnesses on line" ++ (if lines.length > 1 then "s " else " ") ++
          ", ".intercalate (lines.map toString)
      some (v.claim.span, s!"claim `{v.claim.text}`: {status}")
    else none
  let toks := r.tokens.filter (contains ·.span line col) |>.filterMap fun t =>
    (describeTok t).map (t.span, ·)
  -- A reference beats its token; otherwise the smallest span wins.
  match refs.head? with
  | some (_, m) =>
    let tokMore := (toks.find? fun (sp, _) => refs.any (·.1 == sp)).map (·.2)
    some (m ++ (tokMore.map ("\n\n" ++ ·)).getD "")
  | none =>
    -- Inside a claim, its status comes first, then what the word under the cursor means.
    let tok := (toks.foldl (init := none) fun best (sp, m) =>
      match best with
      | some (bs, _) => if width sp < width bs then some (sp, m) else best
      | none => some (sp, m)).map (·.2)
    match claims.head?, tok with
    | some (_, c), some t => some (c ++ "\n\n" ++ t)
    | some (_, c), none => some c
    | none, t => t

/-! ## Code lenses -/

/-- A resource as a reader writes it: a path, URL or host, `anywhere` for unknown. -/
def plainRes : Res → String
  | .path segs _ => pathString segs
  | .url sc h segs => s!"{sc}://{h}{if segs.isEmpty then "" else pathString segs}"
  | .host sc h => if sc.isEmpty then h else s!"{sc}://{h}"
  | .port n => s!"port {n}"
  | .cmd c => s!"\"{c}\""
  | .top => "anywhere"

private def kindVerb : Kind → String
  | .read => "reads" | .write => "writes" | .delete => "deletes"
  | .listen => "listens on" | .connect => "connects to" | .spawn => "runs"

/-- Per section: its claims' status, then its effects grouped by kind. Short enough to read
above a heading. -/
def lenses (r : FileResult) : List (Span × String) :=
  (r.tsections.zip r.sections).flatMap fun (ts, s) =>
    let failing := s.verdicts.filter (!·.holds)
    let n := s.verdicts.length
    let claims : List String :=
      if n == 0 then ["no claims"]
      else if failing.isEmpty then [s!"✓ {n} claim{if n == 1 then "" else "s"} hold{if n == 1 then "s" else ""}"]
      else [s!"✗ {failing.length} of {n} claims fail: " ++ "; ".intercalate (failing.map (·.claim.text))]
    let kinds := [Kind.read, .write, .delete, .listen, .connect, .spawn]
    let groups := kinds.filterMap fun k =>
      let rs := (s.effects.filter (·.kind == k)).map (plainRes ·.res) |>.eraseDups
      if rs.isEmpty then none
      else some s!"{kindVerb k} {if rs.length > 3 then s!"{rs.length} places" else ", ".intercalate rs}"
    let effs := if groups.isEmpty then "no effects" else " · ".intercalate groups
    (claims ++ [effs]).map (ts.span, ·)

/-! ## Semantic tokens

Highlighting from the real classifier, so it follows the project's vocabularies and language
exactly. Program words share one style, claim words are set apart,
literals in a literal colour, asides like comments, and gloss left plain. The finer classes
(op, sort, label and so on) are modifiers, for themes that want them. -/

def semanticTypes : List String :=
  ["namespace", "lrepProgram", "lrepClaim", "string", "number", "comment"]

def semanticModifiers : List String :=
  ["op", "predicate", "sort", "constant", "qualifier", "name", "structure", "label"]

private def typeIndex (t : String) : Nat := (semanticTypes.idxOf? t).getD 0

/-- A modifier bit set with one modifier. -/
private def modBit (m : String) : Nat := 2 ^ ((semanticModifiers.idxOf? m).getD 0)

/-- The semantic type and modifiers of a token; gloss and articles get none, so they stay plain. -/
def tokenType : Cls → Option (Nat × Nat)
  | .op _ _ => some (typeIndex "lrepProgram", modBit "op")
  | .pred _ => some (typeIndex "lrepProgram", modBit "predicate")
  | .sort _ _ | .unit _ => some (typeIndex "lrepProgram", modBit "sort")
  | .const _ => some (typeIndex "lrepProgram", modBit "constant")
  | .qual _ => some (typeIndex "lrepProgram", modBit "qualifier")
  | .name => some (typeIndex "lrepProgram", modBit "name")
  | .struct _ => some (typeIndex "lrepProgram", modBit "structure")
  | .label _ => some (typeIndex "lrepProgram", modBit "label")
  | .claim _ => some (typeIndex "lrepClaim", 0)
  | .str _ => some (typeIndex "string", 0)
  | .int _ => some (typeIndex "number", 0)
  | .aside => some (typeIndex "comment", 0)
  | _ => none

/-- Every highlighted span, in document order: headings, then each token with a type. -/
def semanticSpans (r : FileResult) : List (Span × Nat × Nat) :=
  let heads := r.tsections.map fun s => (s.span, typeIndex "namespace", 0)
  let toks := r.tokens.filterMap fun t => (tokenType t.cls).map fun (ty, m) => (t.span, ty, m)
  (heads ++ toks).filter (fun (sp, _, _) => sp.line > 0 && sp.endCol > sp.col)
    |>.mergeSort fun a b => a.1.line < b.1.line || (a.1.line == b.1.line && a.1.col ≤ b.1.col)

/-- LSP's encoding: five numbers per token, each position relative to the previous token. -/
def semanticData (r : FileResult) : List Nat :=
  let step (acc : List Nat × Nat × Nat) (x : Span × Nat × Nat) : List Nat × Nat × Nat :=
    let (out, pl, pc) := acc
    let (sp, ty, m) := x
    let line := sp.line - 1
    let col := sp.col - 1
    let dl := line - pl
    let dc := if dl == 0 then col - pc else col
    (out ++ [dl, dc, sp.endCol - sp.col, ty, m], line, col)
  ((semanticSpans r).foldl step ([], 0, 0)).1

/-! ## JSON-RPC -/

def uriToPath (uri : String) : String :=
  let p := if uri.startsWith "file://" then String.ofList (uri.toList.drop 7) else uri
  -- Percent-decoding for the characters paths commonly contain.
  (p.replace "%20" " ").replace "%3A" ":"

private def pos (line col : Nat) : J := .obj [("line", .num (line - 1)), ("character", .num (col - 1))]

private def range (sp : Span) : J :=
  if sp.line == 0 then .obj [("start", pos 1 1), ("end", pos 1 1)]
  else .obj [("start", pos sp.line sp.col), ("end", pos sp.line (max sp.endCol (sp.col + 1)))]

def lspDiagnostics (uri : String) (r : FileResult) : J :=
  .obj [("uri", .str uri), ("diagnostics", .arr (r.diags.map fun d =>
    .obj ([("range", range d.span), ("severity", .num (if d.isError then 1 else 2)),
           ("code", .str d.code), ("source", .str "lrep"),
           ("message", .str (d.message ++ (d.fix.map (fun f => s!"\nfix: {f.label}")).getD ""))] ++
          (if d.related.isEmpty then [] else
            [("relatedInformation", .arr (d.related.map fun rel =>
              .obj [("location", .obj [("uri", .str uri), ("range", range rel.span)]),
                    ("message", .str rel.message)]))]))))]

/-- The capabilities `initialize` answers with. -/
def capabilities : J :=
  .obj [("capabilities", .obj [("textDocumentSync", .num 1), ("hoverProvider", .bool true),
          ("codeLensProvider", .obj [("resolveProvider", .bool false)]),
          ("semanticTokensProvider", .obj [
            ("legend", .obj [("tokenTypes", .arr (semanticTypes.map .str)),
                             ("tokenModifiers", .arr (semanticModifiers.map .str))]),
            ("full", .bool true)])]),
        ("serverInfo", .obj [("name", .str "lrep"), ("version", .str "0.1.0")])]

def hoverJ (r : FileResult) (line col : Nat) : J :=
  match hoverAt r line col with
  | some m => .obj [("contents", .obj [("kind", .str "markdown"), ("value", .str m)])]
  | none => .null

def lensesJ (r : FileResult) : J :=
  .arr ((lenses r).map fun (sp, title) =>
    .obj [("range", range sp), ("command", .obj [("title", .str title), ("command", .str "")])])

/-- A JSON id echoed back as written. -/
def idJ (j : Json) : J :=
  match j with
  | .str s => .str s
  | .num n => match n.mantissa.toNat? with | some k => .num k | none => .null
  | _ => .null

private def message (body : J) : String :=
  let s := body.compact
  s!"Content-Length: {s.utf8ByteSize}\r\n\r\n{s}"

private def send (out : IO.FS.Stream) (body : J) : IO Unit := do
  out.putStr (message body)
  out.flush

private def readMessage (inp : IO.FS.Stream) : IO (Option Json) := do
  let mut len : Option Nat := none
  repeat
    let line ← inp.getLine
    if line.isEmpty then return none
    let l := trimStr line
    if l.isEmpty then break
    if l.toLower.startsWith "content-length:" then
      len := (trimStr (String.ofList (l.toList.drop 15))).toNat?
  match len with
  | none => return none
  | some n =>
    let mut bytes := ByteArray.empty
    while bytes.size < n do
      let chunk ← inp.read (n - bytes.size).toUSize
      if chunk.isEmpty then return none
      bytes := bytes ++ chunk
    match String.fromUTF8? bytes with
    | some s => return (Json.parse s).toOption
    | none => return none

private def analyse (uri text : String) : IO FileResult := do
  let path : System.FilePath := uriToPath uri
  let proj ← loadProject (path.parent.getD ".")
  let r := checkSource proj.lex (path.fileName.getD path.toString) text
  pure { r with diags := proj.diags ++ r.diags }

private def textDoc (params : Json) : Option (String × Option String) := do
  let td ← (params.getObjVal? "textDocument").toOption
  let uri ← (td.getObjValAs? String "uri").toOption
  pure (uri, (td.getObjValAs? String "text").toOption)

/-- Serves LSP over stdin and stdout until `exit`. -/
partial def serve : IO Unit := do
  let inp ← IO.getStdin
  let out ← IO.getStdout
  let rec loop (docs : List (String × FileResult)) : IO Unit := do
    let some msg ← readMessage inp | return
    let method := (msg.getObjValAs? String "method").toOption.getD ""
    let params := (msg.getObjVal? "params").toOption.getD Json.null
    let id := (msg.getObjVal? "id").toOption
    let reply (result : J) : IO Unit := match id with
      | some i => send out (.obj [("jsonrpc", .str "2.0"), ("id", idJ i), ("result", result)])
      | none => pure ()
    let publish (uri : String) (r : FileResult) : IO Unit :=
      send out (.obj [("jsonrpc", .str "2.0"), ("method", .str "textDocument/publishDiagnostics"),
                      ("params", lspDiagnostics uri r)])
    match method with
    | "initialize" => reply capabilities; loop docs
    | "shutdown" => reply .null; loop docs
    | "exit" => return
    | "textDocument/didOpen" =>
      match textDoc params with
      | some (uri, some text) =>
        let r ← analyse uri text
        publish uri r
        loop ((uri, r) :: docs.filter (·.1 != uri))
      | _ => loop docs
    | "textDocument/didChange" =>
      let text := (params.getObjValAs? (List Json) "contentChanges").toOption.bind fun cs =>
        cs.getLast?.bind fun c => (c.getObjValAs? String "text").toOption
      match textDoc params, text with
      | some (uri, _), some t =>
        let r ← analyse uri t
        publish uri r
        loop ((uri, r) :: docs.filter (·.1 != uri))
      | _, _ => loop docs
    | "textDocument/didClose" =>
      match textDoc params with
      | some (uri, _) => loop (docs.filter (·.1 != uri))
      | none => loop docs
    | "textDocument/hover" =>
      let line := ((params.getObjVal? "position").toOption.bind fun p => (p.getObjValAs? Nat "line").toOption).getD 0
      let col := ((params.getObjVal? "position").toOption.bind fun p => (p.getObjValAs? Nat "character").toOption).getD 0
      match textDoc params with
      | some (uri, _) =>
        reply (match docs.lookup uri with | some r => hoverJ r (line + 1) (col + 1) | none => .null)
      | none => reply .null
      loop docs
    | "textDocument/semanticTokens/full" =>
      match textDoc params with
      | some (uri, _) =>
        reply (match docs.lookup uri with
          | some r => .obj [("data", .arr ((semanticData r).map .num))]
          | none => .obj [("data", .arr [])])
      | none => reply (.obj [("data", .arr [])])
      loop docs
    | "textDocument/codeLens" =>
      match textDoc params with
      | some (uri, _) => reply (match docs.lookup uri with | some r => lensesJ r | none => .arr [])
      | none => reply (.arr [])
      loop docs
    | _ =>
      if let some i := id then
        send out (.obj [("jsonrpc", .str "2.0"), ("id", idJ i),
                        ("error", .obj [("code", .raw "-32601"), ("message", .str s!"method not found: {method}")])])
      loop docs
  loop []

end Lrep
