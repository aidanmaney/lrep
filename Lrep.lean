/-
The checker pipeline: read, tokenize, parse, elaborate, infer and check, for one file.
-/
import Lrep.Effects
import Lrep.Residue
import Lrep.Grammar

namespace Lrep

structure SectionResult where
  name : String
  effects : List Effect
  verdicts : List Verdict

structure FileResult where
  file : String
  lines : Array String
  diags : List Diagnostic
  sections : List SectionResult
  tsections : List TSection
  /-- What each reference refers to, for hover. -/
  refs : List (Span × String) := []
  /-- Each section's core AST, for the dataflow view and the runtime. -/
  cores : List CSection := []

private def isRelativeText (t : String) : Bool :=
  !(t.startsWith "\"/") && !hasScheme t

private def witnessMessage (w : Witness) : String :=
  let what := match w.res with
    | .path segs true => s!"something under \"{pathString segs}\""
    | r => r.show
  let base := match w.text with
    | some "" => w.verb
    | some t => if w.res == .top && isRelativeText t then s!"{w.verb} {t}, a relative path" else s!"{w.verb} {what}"
    | none => s!"{w.verb} {what}"
  -- The caret points at the value; name the step's line when it's elsewhere.
  match w.origin with
  | some o => if o.line != w.site.line then s!"{base} (on line {w.site.line})" else base
  | none => base

private def unquote (t : String) : String :=
  if t.startsWith "\"" && t.endsWith "\"" && t.length ≥ 2 then String.ofList (t.toList.drop 1).dropLast else t

/-- E040 for a failing claim, pointing at up to five witnesses. -/
def claimDiag (v : Verdict) : Option Diagnostic :=
  if v.holds then none
  else
    let keyed := v.witnesses.map fun w => (w.origin.getD w.site, w)
    let uniq := keyed.foldl (init := ([] : List (Span × Witness))) fun acc (sp, w) =>
      if acc.any (·.1 == sp) then acc else acc ++ [(sp, w)]
    let related := (uniq.take 5).map fun (sp, w) => ({ span := sp, message := witnessMessage w } : Related)
    let fix : Option Fix :=
      if v.claim.word != "only" then none
      else
        let prefix_ := v.claimRes.findSome? fun | .path segs true => some segs | _ => none
        let rel := uniq.findSome? fun (_, w) =>
          match w.text, w.origin with
          | some t, some sp => if w.res == .top && isRelativeText t && t != "" then some (t, sp) else none
          | _, _ => none
        match prefix_, rel with
        | some segs, some (t, sp) =>
          match normSegs (segs ++ (unquote t).splitOn "/") with
          | .ok joined =>
            let rep := s!"\"{pathString joined}\""
            some { label := s!"write {rep}", edit := some (sp, rep) }
          | .error _ => none
        | _, _ => none
    some { code := "E040", span := v.claim.span, message := s!"claim not satisfied: {v.claim.text}",
           related, fix }

/-- Effects for display: one per kind, resource and line, in first-seen order. -/
def dedupEffects (es : List Effect) : List Effect :=
  es.foldl (init := []) fun acc e =>
    if acc.any fun f => f.kind == e.kind && f.res == e.res && f.site.line == e.site.line then acc else acc ++ [e]

def checkSource (lex : Lexicon) (file : String) (src : String) : FileResult :=
  let doc := readDoc src
  let (tsecs, tds) := tokenizeDoc lex doc
  let built := lex.ops.filterMap fun o => o.body.map fun b => (o.base, buildTemplate lex o b)
  let templates := built.filterMap fun (n, r) => match r with | .ok t => some (n, t) | .error _ => none
  let templateDiags : List Diagnostic := built.filterMap fun (n, r) => match r with
    | .error e => some { code := "E050", span := Span.none, message := s!"composite op {n}: {e}" }
    | .ok _ => none
  let results := tsecs.map fun ts =>
    let (ss, pds) := parseSection ts
    let (cs, eds, refs) := elabSection lex ts.name ss templates
    let (inf, env) := infer lex cs
    let verdicts := cs.claims.map (checkClaim lex env inf cs.stmts)
    ((⟨ts.name, dedupEffects inf.effects, verdicts⟩ : SectionResult), pds ++ eds ++ checkQuals lex cs ++ verdicts.filterMap claimDiag, refs, cs)
  let lines := (src.splitOn "\n").toArray
  { file, lines, diags := sortDiags (templateDiags ++ doc.diags ++ tds ++ results.flatMap (·.2.1)),
    sections := results.map (·.1), tsections := tsecs,
    refs := results.flatMap (·.2.2.1) ++ (results.map (·.2.2.2)).flatMap (qualHovers lex),
    cores := results.map (·.2.2.2) }

def FileResult.hasErrors (r : FileResult) : Bool := r.diags.any Diagnostic.isError

/-- Whether the residue view may render: only E040 errors are allowed. -/
def FileResult.residueOk (r : FileResult) : Bool :=
  r.diags.all fun d => !d.isError || d.code == "E040"

def FileResult.residue (r : FileResult) : String :=
  let headings := r.tsections.map fun s => r.lines.getD (s.span.line - 1) s.name
  Lrep.residue r.tsections headings

def FileResult.toJ (r : FileResult) : J :=
  .obj [("file", .str r.file),
        ("diagnostics", .arr (r.diags.map Diagnostic.toJ)),
        ("sections", .arr (r.sections.map fun s =>
          .obj [("name", .str s.name),
                ("effects", .arr (s.effects.map fun e =>
                  .obj [("kind", .str e.kind.name), ("resource", .str e.res.key), ("line", .num e.site.line)])),
                ("claims", .arr (s.verdicts.map fun v =>
                  .obj [("text", .str v.claim.text), ("holds", .bool v.holds)]))]))]

def FileResult.text (r : FileResult) : String :=
  let ds := r.diags.map (·.render r.file r.lines)
  let claims := r.sections.flatMap fun s => s.verdicts.map fun v =>
    s!"{if v.holds then "✓" else "✗"} {s.name}: {v.claim.text}"
  "\n".intercalate (ds ++ (if claims.isEmpty then [] else ["\n".intercalate claims ++ "\n"]))

def FileResult.effectsText (r : FileResult) : String :=
  "\n".intercalate (r.sections.map fun s =>
    "\n".intercalate (s.name :: s.effects.map fun e =>
      s!"  {e.kind.name}  {e.res.key}  (line {e.site.line})")) ++ "\n"

/-! ## Tokens view -/

def Cls.show : Cls → String
  | .str _ => "string" | .int _ => "integer" | .comma | .dot | .colon => "punct"
  | .struct _ => "structure" | .label _ => "label" | .claim _ => "claim"
  | .op o f => s!"op {o.base} ({f})" | .pred _ => "predicate"
  | .sort s pl => s!"sort {s.name}{if pl then " (plural)" else ""}"
  | .unit u => s!"unit {u.sort}" | .const c => s!"constant {c.sort}"
  | .qual q => s!"qualifier {q.forms.headD ""}"
  | .article => "gloss (article)" | .name => "name" | .gloss => "gloss" | .aside => "aside"

mutual
def tokLines : TSent → List String
  | .mk toks _ _ _ sub =>
    toks.map (fun t => s!"{t.span.line}:{t.span.col}\t{Cls.show t.cls}\t{t.text}") ++ tokItemLines sub
def tokItemLines : List (List TSent) → List String
  | [] => []
  | it :: rest => tokSentLines it ++ tokItemLines rest
def tokSentLines : List TSent → List String
  | [] => []
  | s :: rest => tokLines s ++ tokSentLines rest
end

def FileResult.tokensText (r : FileResult) : String :=
  "\n".intercalate (r.tsections.flatMap fun s => s!"# {s.name}" :: tokSentLines s.sents) ++ "\n"

/-! ## Loading the project -/

structure Project where
  lex : Lexicon
  diags : List Diagnostic

/-- Loads vocabularies from (path, source) pairs, reporting each problem as E050. -/
def loadLexicon (srcs : List (String × String)) (lang : Words.Language := Words.english) : Project :=
  let (vs, ds) := srcs.foldl (init := (([] : List Vocab), ([] : List Diagnostic))) fun (vs, ds) (path, src) =>
    match loadVocab src with
    | .ok v => (vs ++ [{ v with path }], ds)
    | .error e => (vs, ds ++ [{ code := "E050", span := Span.none, message := s!"bad vocabulary {path}: {e}" }])
  let cs := (conflicts vs lang).map fun m => ({ code := "E050", span := Span.none, message := m } : Diagnostic)
  ⟨{ vocabs := vs, lang }, ds ++ cs⟩

/-! ## Files on disk -/

open Lean (Json) in
/-- Finds `lrep.json` by walking up from `dir`. -/
def findProject (dir : System.FilePath) : Nat → IO (Option System.FilePath)
  | 0 => pure none
  | n + 1 => do
    let p := dir / "lrep.json"
    if ← p.pathExists then return some p
    match dir.parent with
    | some up => if up == dir then pure none else findProject up n
    | none => pure none

open Lean (Json) in
/-- Loads the vocabularies for a file: those `lrep.json` lists, or the four core ones. -/
def loadProject (start : System.FilePath) : IO Project := do
  let dir ← IO.FS.realPath (if start.toString.isEmpty then "." else start)
  match ← findProject dir 64 with
  | none => pure (loadLexicon coreSources)
  | some cfg =>
    let src ← IO.FS.readFile cfg
    let bad (m : String) : Project := ⟨{}, [{ code := "E050", span := Span.none, message := s!"{cfg}: {m}" }]⟩
    match Json.parse src with
    | .error e => pure (bad s!"invalid JSON: {e}")
    | .ok j =>
      match j with
      | .obj kvs =>
        if let some (k, _) := kvs.toList.find? (fun (k, _) => !["vocabularies", "language", "gloss"].contains k) then
          return bad s!"unknown key \"{k}\""
      | _ => return bad "lrep.json must be an object"
      match j.getObjValAs? (List String) "vocabularies" with
      | .error _ => pure (bad "\"vocabularies\" must be a list of paths")
      | .ok paths =>
        let base := cfg.parent.getD "."
        -- A project may name the natural language its source is written in.
        let lang ← match j.getObjValAs? String "language" with
          | .ok p =>
            let path := base / p
            if !(← path.pathExists) then return bad s!"language {p} not found"
            match loadLanguage (← IO.FS.readFile path) with
            | .ok l => pure l
            | .error e => return bad s!"bad language {p}: {e}"
          | .error _ => pure Words.english
        let strict ← match j.getObjValAs? String "gloss" with
          | .ok "strict" => pure true
          | .ok "loose" => pure false
          | .ok g => return bad s!"\"gloss\" is \"strict\" or \"loose\", not \"{g}\""
          | .error _ => pure false
        let mut srcs := []
        for p in paths do
          let path := base / p
          if ← path.pathExists then srcs := srcs ++ [(p, ← IO.FS.readFile path)]
          else return bad s!"vocabulary {p} not found"
        let proj := loadLexicon srcs lang
        -- Read each composite op's body, relative to its vocabulary file.
        let mut vocabs := []
        let mut ds := proj.diags
        for v in proj.lex.vocabs do
          let vdir := (base / v.path).parent.getD base
          let mut ops := []
          for o in v.ops do
            match o.body with
            | some b =>
              let f := vdir / b.file
              if ← f.pathExists then ops := ops ++ [{ o with body := some { b with source := ← IO.FS.readFile f } }]
              else
                ds := ds ++ [{ code := "E050", span := Span.none, message := s!"op {o.base}: body file {b.file} not found" }]
                ops := ops ++ [o]
            | none => ops := ops ++ [o]
          vocabs := vocabs ++ [{ v with ops }]
        pure ⟨{ vocabs, lang, strictGloss := strict }, ds⟩

def checkFile (path : String) : IO FileResult := do
  let fp : System.FilePath := path
  let proj ← loadProject (fp.parent.getD ".")
  let src ← IO.FS.readFile fp
  let r := checkSource proj.lex path src
  pure { r with diags := proj.diags ++ r.diags }

end Lrep
