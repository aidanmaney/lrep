/-
Vocabularies: the JSON lexicon format, its loader and conflict checks, and the
literal validation each sort's `literal` kind calls for.
-/
import Lean.Data.Json
import Lrep.Diag
import Lrep.Words

namespace Lrep
open Lean (Json)

inductive LitKind where
  | path | url | string | int | none
  deriving Repr, BEq, Inhabited

inductive ResKind where
  | pathExact | pathPrefix | url | host | port | command | none
  deriving Repr, BEq, Inhabited

structure SortDef where
  name : String
  forms : List String
  literal : LitKind
  resource : ResKind
  deriving Repr, Inhabited

instance : BEq SortDef := ⟨fun a b => a.name == b.name⟩

structure UnitDef where
  forms : List String
  sort : String
  /-- Base units (seconds, bytes) in one of this unit, for the runtime. -/
  scale : Nat := 1
  deriving Repr, Inhabited

/-- A constant's fixed resource, given in the lexicon as `{"path": …}` and so on. -/
inductive ConstRes where
  | path (p : String) | url (u : String) | host (h : String) | port (n : Nat) | none
  deriving Repr, Inhabited

/-- A qualifier: a descriptive word with a checked meaning. `within` lists the regions a
described value's resources must lie in; `origins` the regions its contents must come
from. Both are path or URL prefixes; an empty list means no constraint. -/
structure QualDef where
  forms : List String
  within : List String := []
  origins : List String := []
  deriving Repr, Inhabited

instance : BEq QualDef := ⟨fun a b => a.forms == b.forms⟩

structure ConstDef where
  forms : List String
  sort : String
  resource : ConstRes
  deriving Repr, Inhabited

/-- What an effect applies to. -/
inductive Target where
  | object | subject | label (l : String) | top
  deriving Repr, BEq, Inhabited

structure EffDecl where
  kind : String
  on : Target
  deriving Repr, Inhabited

inductive RetRes where
  | sameObject | sameLabel (l : String) | none | top
  deriving Repr, Inhabited

structure Returns where
  sort : String
  list : Bool
  resource : RetRes
  deriving Repr, Inhabited

structure PredDef where
  forms : List String
  subject : List String
  labels : List (String × List String)
  required : List String
  effects : List EffDecl
  deriving Repr, Inhabited

/-- A user-defined op: its body is a section of an lrep file, with the op's parameters
bound as names there. Its effects are inferred from the body, not declared. -/
structure CompositeBody where
  file : String
  sectionName : String
  /-- Parameter label (`object` for the object) and the name the body uses for it. -/
  params : List (String × String)
  /-- The body file's text, read when the project loads. -/
  source : String := ""
  deriving Repr, Inhabited

structure OpDef where
  /-- Inflections, keyed `base`, `s`, `past`, `ing`, `pp`. -/
  forms : List (String × String)
  object : List String
  labels : List (String × List String)
  required : List String
  returns : Option Returns
  effects : List EffDecl
  /-- The effect kind a primitive op stands for in claims. -/
  names : Option String
  claimLabels : List String
  body : Option CompositeBody := none
  deriving Repr, Inhabited

def OpDef.base (o : OpDef) : String := (o.forms.lookup "base").getD ""
def OpDef.form (o : OpDef) (k : String) : String := (o.forms.lookup k).getD o.base
def OpDef.isPrimitive (o : OpDef) : Bool := o.names.isSome
def OpDef.takesObject (o : OpDef) : Bool := !o.object.isEmpty

instance : BEq OpDef := ⟨fun a b => a.base == b.base⟩

structure Vocab where
  name : String
  /-- Where the vocabulary was loaded from, for resolving composite bodies. -/
  path : String := ""
  sorts : List SortDef := []
  units : List UnitDef := []
  constants : List ConstDef := []
  predicates : List PredDef := []
  ops : List OpDef := []
  qualifiers : List QualDef := []
  /-- Pairs of qualifier forms that no value may have both of. -/
  disjoint : List (String × String) := []
  deriving Inhabited

/-- The merged vocabularies a file is checked against. -/
structure Lexicon where
  vocabs : List Vocab := []
  lang : Words.Language := Words.english
  /-- Strict gloss: a main clause may hold no gloss but articles and fillers. -/
  strictGloss : Bool := false
  deriving Inhabited

namespace Lexicon
def sorts (l : Lexicon) := l.vocabs.flatMap (·.sorts)
def units (l : Lexicon) := l.vocabs.flatMap (·.units)
def constants (l : Lexicon) := l.vocabs.flatMap (·.constants)
def qualifiers (l : Lexicon) := l.vocabs.flatMap (·.qualifiers)
def disjoint (l : Lexicon) := l.vocabs.flatMap (·.disjoint)
def qual? (l : Lexicon) (form : String) : Option QualDef :=
  l.qualifiers.find? (·.forms.any (·.toLower == form.toLower))
def predicates (l : Lexicon) := l.vocabs.flatMap (·.predicates)
def ops (l : Lexicon) := l.vocabs.flatMap (·.ops)

def sort? (l : Lexicon) (name : String) : Option SortDef := l.sorts.find? (·.name == name)

/-- Resolves a parameter's sort word: a sort's name means one value, its plural form
a list. -/
def paramSort? (l : Lexicon) (w : String) : Option (SortDef × Bool) :=
  match l.sort? w with
  | some s => some (s, false)
  | none => (l.sorts.find? fun s => s.forms.length > 1 && s.forms[1]? == some w).map (·, true)
end Lexicon

/-! ## Literals -/

/-- Normalises an absolute path into segments: repeated slashes collapse, `.` drops,
`..` pops, and a trailing slash is ignored. Going above `/` is an error. -/
def normSegs (raw : List String) : Except String (List String) :=
  raw.foldlM (init := []) fun acc s =>
    if s == "" || s == "." then pure acc
    else if s == ".." then
      match acc with
      | [] => throw "the path goes above \"/\""
      | _ => pure acc.dropLast
    else pure (acc ++ [s])

def isAbsolute (p : String) : Bool := p.startsWith "/"

def normPath (p : String) : Except String (List String) := normSegs (p.splitOn "/")

def pathString (segs : List String) : String := "/" ++ "/".intercalate segs

structure Url where
  scheme : String
  host : String
  segs : List String
  deriving Repr, BEq, Inhabited

/-- Splits `scheme://host/path`; the scheme is required. -/
def parseUrl (s : String) : Except String Url :=
  match s.splitOn "://" with
  | [scheme, rest] =>
    if scheme.isEmpty || !scheme.toList.all (fun c => c.isAlphanum || c == '+' || c == '-' || c == '.') then
      throw "the URL's scheme is invalid"
    else
      match rest.splitOn "/" with
      | [] => throw "the URL has no host"
      | host :: path =>
        if host.isEmpty then throw "the URL has no host"
        else do
          let segs ← normSegs path
          pure ⟨scheme, host, segs⟩
  | _ => throw "a URL needs a scheme, as in \"https://\""

def hasScheme (s : String) : Bool := (s.splitOn "://").length == 2

/-- Checks a literal against a sort, returning an error message if it doesn't fit. -/
def validateLit (s : SortDef) (str? : Option String) (int? : Option Nat) : Option String :=
  match s.literal, str?, int? with
  | .path, some p, _ =>
    if isAbsolute p then
      match normPath p with | .ok _ => none | .error e => some e
    else none
  | .url, some u, _ => match parseUrl u with | .ok _ => none | .error e => some e
  | .string, some _, _ => none
  | .int, _, some n =>
    if s.resource == .port && (n < 1 || n > 65535) then some s!"port {n} is outside 1–65535"
    else none
  | .none, _, _ => some s!"a {s.name} has no literal form"
  | _, some _, _ => some s!"a {s.name} is not written as a string"
  | _, _, _ => some s!"a {s.name} is not written as a number"

/-! ## JSON loading -/

abbrev LoadM := Except String

private def objKeys (j : Json) : List String :=
  match j with
  | .obj kvs => kvs.toList.map (·.1)
  | _ => []

private def onlyKeys (what : String) (j : Json) (allowed : List String) : LoadM Unit := do
  match j with
  | .obj _ => pure ()
  | _ => throw s!"{what} must be an object"
  for k in objKeys j do
    unless allowed.contains k do throw s!"unknown key \"{k}\" in {what}"

private def field (j : Json) (k : String) : Option Json :=
  match j.getObjVal? k with
  | .ok .null => none
  | .ok v => some v
  | .error _ => none

private def str (what : String) (j : Json) : LoadM String :=
  match j.getStr? with
  | .ok s => pure s
  | .error _ => throw s!"{what} must be a string"

private def strField (what : String) (j : Json) (k : String) : LoadM String :=
  match field j k with
  | some v => str s!"{what}.{k}" v
  | none => throw s!"{what} is missing \"{k}\""

private def arr (what : String) (j : Json) : LoadM (List Json) :=
  match j.getArr? with
  | .ok a => pure a.toList
  | .error _ => throw s!"{what} must be an array"

private def strList (what : String) (j : Option Json) : LoadM (List String) :=
  match j with
  | none => pure []
  | some j => do (← arr what j).mapM (str what)

private def litKind (s : String) : LoadM LitKind :=
  match s with
  | "path" => pure .path | "url" => pure .url | "string" => pure .string
  | "int" => pure .int | "none" => pure .none
  | _ => throw s!"unknown literal kind \"{s}\""

private def resKind (s : String) : LoadM ResKind :=
  match s with
  | "path-exact" => pure .pathExact | "path-prefix" => pure .pathPrefix | "url" => pure .url
  | "host" => pure .host | "port" => pure .port | "command" => pure .command | "none" => pure .none
  | _ => throw s!"unknown resource kind \"{s}\""

private def target (s : String) : LoadM Target :=
  if s == "object" then pure .object
  else if s == "subject" then pure .subject
  else if s == "top" then pure .top
  else if s.startsWith "label:" then pure (.label (String.ofList (s.toList.drop 6)))
  else throw s!"unknown effect target \"{s}\""

private def kinds : List String := ["read", "write", "delete", "listen", "connect", "spawn"]

private def effects (what : String) (j : Option Json) : LoadM (List EffDecl) := do
  let es ← match j with | none => pure [] | some j => arr what j
  es.mapM fun e => do
    onlyKeys "an effect" e ["kind", "on"]
    let k ← strField "effect" e "kind"
    unless kinds.contains k do throw s!"unknown effect kind \"{k}\""
    pure ⟨k, ← target (← strField "effect" e "on")⟩

private def labelMap (what : String) (j : Option Json) : LoadM (List (String × List String)) :=
  match j with
  | none => pure []
  | some (.obj kvs) => kvs.toList.mapM fun (k, v) => do pure (k, ← strList s!"{what}.{k}" (some v))
  | some _ => throw s!"{what} must be an object"

private def loadSort (j : Json) : LoadM SortDef := do
  onlyKeys "a sort" j ["name", "forms", "literal", "resource"]
  pure { name := ← strField "sort" j "name", forms := ← strList "sort forms" (field j "forms"),
         literal := ← litKind (← strField "sort" j "literal"),
         resource := ← resKind (← strField "sort" j "resource") }

private def loadUnit (j : Json) : LoadM UnitDef := do
  onlyKeys "a unit" j ["forms", "sort", "scale"]
  let scale ← match field j "scale" with
    | some s => match s.getNat? with | .ok n => pure n | .error _ => throw "a unit's scale must be a number"
    | none => pure 1
  pure { forms := ← strList "unit forms" (field j "forms"), sort := ← strField "unit" j "sort", scale }

private def loadConst (j : Json) : LoadM ConstDef := do
  onlyKeys "a constant" j ["forms", "sort", "resource"]
  let res ← match field j "resource" with
    | none => pure ConstRes.none
    | some r => do
      onlyKeys "a constant's resource" r ["path", "url", "host", "port"]
      if let some p := field r "path" then pure (.path (← str "path" p))
      else if let some u := field r "url" then pure (.url (← str "url" u))
      else if let some h := field r "host" then pure (.host (← str "host" h))
      else if let some p := field r "port" then
        match p.getNat? with
        | .ok n => pure (.port n)
        | .error _ => throw "port must be a number"
      else pure .none
  pure { forms := ← strList "constant forms" (field j "forms"), sort := ← strField "constant" j "sort",
         resource := res }

private def loadPred (j : Json) : LoadM PredDef := do
  onlyKeys "a predicate" j ["forms", "subject", "labels", "required", "effects"]
  pure { forms := ← strList "predicate forms" (field j "forms"),
         subject := ← strList "predicate subject" (field j "subject"),
         labels := ← labelMap "predicate labels" (field j "labels"),
         required := ← strList "predicate required" (field j "required"),
         effects := ← effects "predicate effects" (field j "effects") }

private def retRes (s : String) : LoadM RetRes :=
  if s == "same(object)" then pure .sameObject
  else if s == "none" then pure .none
  else if s == "top" then pure .top
  else if s.startsWith "same(label:" && s.endsWith ")" then
    pure (.sameLabel (String.ofList (s.toList.drop 11).dropLast))
  else throw s!"unknown returns.resource \"{s}\""

private def loadOp (j : Json) : LoadM OpDef := do
  onlyKeys "an op" j ["forms", "object", "labels", "required", "returns", "effects", "names", "claimLabels", "body"]
  let forms ← match field j "forms" with
    | some (.obj kvs) => kvs.toList.mapM fun (k, v) => do
        unless ["base", "s", "past", "ing", "pp"].contains k do throw s!"unknown op form \"{k}\""
        pure (k, ← str "op form" v)
    | _ => throw "an op's forms must be an object"
  unless (forms.lookup "base").isSome do throw "an op needs a base form"
  let returns ← match field j "returns" with
    | none => pure none
    | some r => do
      onlyKeys "returns" r ["sort", "list", "resource"]
      let list := match r.getObjValAs? Bool "list" with | .ok b => b | .error _ => false
      let res ← match field r "resource" with
        | some s => retRes (← str "returns.resource" s)
        | none => pure .none
      pure (some { sort := ← strField "returns" r "sort", list, resource := res : Returns })
  let names ← match field j "names" with
    | none => pure none
    | some n => do
      let k ← str "names" n
      unless kinds.contains k do throw s!"unknown effect kind \"{k}\""
      pure (some k)
  let body ← match field j "body" with
    | none => pure none
    | some b => do
      onlyKeys "a body" b ["file", "section", "params"]
      let params ← match field b "params" with
        | some (.obj kvs) => kvs.toList.mapM fun (k, v) => do pure (k, ← str "a body parameter" v)
        | some _ => throw "a body's params must be an object"
        | none => pure []
      if (field j "effects").isSome || (field j "names").isSome then
        throw "a composite op's effects come from its body, so it declares no effects or names"
      if returns.isSome then throw "a composite op returns nothing"
      pure (some { file := ← strField "body" b "file", sectionName := ← strField "body" b "section", params })
  pure { forms, body, object := ← strList "op object" (field j "object"),
         labels := ← labelMap "op labels" (field j "labels"),
         required := ← strList "op required" (field j "required"), returns,
         effects := ← effects "op effects" (field j "effects"), names,
         claimLabels := ← strList "claimLabels" (field j "claimLabels") }

def loadVocab (src : String) : LoadM Vocab := do
  let j ← match Json.parse src with
    | .ok j => pure j
    | .error e => throw s!"invalid JSON: {e}"
  onlyKeys "a vocabulary" j ["vocabulary", "version", "sorts", "units", "constants", "predicates", "ops",
    "qualifiers", "disjoint"]
  let list (k : String) := match field j k with | some v => arr k v | none => pure []
  let qualifiers ← (← list "qualifiers").mapM fun q => do
    onlyKeys "a qualifier" q ["forms", "within", "from"]
    let regions (k : String) : LoadM (List String) := do
      let rs ← strList s!"qualifier {k}" (field q k)
      for r in rs do
        unless hasScheme r || isAbsolute r do throw s!"qualifier region \"{r}\" must be an absolute path or a URL"
      pure rs
    pure ({ forms := ← strList "qualifier forms" (field q "forms"),
            within := ← regions "within", origins := ← regions "from" } : QualDef)
  let disjoint ← (← list "disjoint").mapM fun p => do
    match ← strList "a disjoint pair" (some p) with
    | [a, b] => pure (a, b)
    | _ => throw "a disjoint entry is a pair of qualifier forms"
  pure { name := ← strField "vocabulary" j "vocabulary",
         sorts := ← (← list "sorts").mapM loadSort,
         units := ← (← list "units").mapM loadUnit,
         constants := ← (← list "constants").mapM loadConst,
         predicates := ← (← list "predicates").mapM loadPred,
         ops := ← (← list "ops").mapM loadOp, qualifiers, disjoint }

/-- Every form a vocabulary reserves, lower-cased. -/
private def dedup (xs : List String) : List String :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- Every form a vocabulary reserves, lower-cased; an entry's repeated forms
(such as `read` as both base and past) count once. -/
def Vocab.allForms (v : Vocab) : List String :=
  let entries : List (List String) :=
    v.sorts.map (·.forms) ++ v.units.map (·.forms) ++ v.constants.map (·.forms) ++ v.qualifiers.map (·.forms) ++
    v.predicates.map (·.forms) ++ v.ops.map (·.forms.map (·.2))
  entries.flatMap fun fs => dedup (fs.map String.toLower)

/-- Conflict checks across the loaded vocabularies: a word defined twice, or a
language word defined at all. Each problem is one E050 message. -/
def conflicts (vs : List Vocab) (lang : Words.Language := Words.english) : List String :=
  let tagged := vs.flatMap fun v => v.allForms.map (·, v.name)
  let lang := tagged.filterMap fun (w, n) =>
    if lang.words.contains w || (lang.forbiddenFix w).isSome then
      some s!"vocabulary {n} defines \"{w}\", which is a language word"
    else none
  let dups := (dedup (tagged.map (·.1))).filterMap fun w =>
    let owners := tagged.filter (·.1 == w) |>.map (·.2)
    if owners.length > 1 then some s!"\"{w}\" is defined by more than one vocabulary ({", ".intercalate owners})"
    else none
  lang ++ dups

/-- Loads a language's word tables. Canonical words must be the language's own: the
English structure, claim and phrase words. -/
def loadLanguage (src : String) : LoadM Words.Language := do
  let j ← match Json.parse src with
    | .ok j => pure j
    | .error e => throw s!"invalid JSON: {e}"
  onlyKeys "a language" j ["language", "phrases", "structure", "claims", "labels", "articles", "forbidden", "numbers", "fillers"]
  let strMap (k : String) : LoadM (List (String × String)) :=
    match field j k with
    | some (.obj kvs) => kvs.toList.mapM fun (a, v) => do pure (a.toLower, ← str k v)
    | some _ => throw s!"\"{k}\" must be an object"
    | none => pure []
  let structureMap ← strMap "structure"
  for (w, c) in structureMap do
    unless Words.structureWords.contains c do throw s!"\"{w}\" maps to \"{c}\", which is not a structure word"
  let claimMap ← strMap "claims"
  for (w, c) in claimMap do
    unless Words.claimWords.contains c do throw s!"\"{w}\" maps to \"{c}\", which is not a claim word"
  let phrases ← (← strMap "phrases").mapM fun (p, c) => do
    unless ["for each", "at most", "this section"].contains c do throw s!"\"{p}\" maps to \"{c}\", which is not a phrase"
    match p.splitOn " " with
    | [a, b] => pure ((a, b), c)
    | _ => throw s!"the phrase \"{p}\" must be two words"
  pure { name := ← strField "language" j "language", phrases, structureMap, claimMap,
         labels := (← strList "labels" (field j "labels")).map String.toLower,
         articles := (← strList "articles" (field j "articles")).map String.toLower,
         forbidden := ← strMap "forbidden", numbers := ← strMap "numbers", contractions := false,
         fillers := (← strList "fillers" (field j "fillers")).map String.toLower }

/-! ## Core vocabularies, embedded so a file with no `lrep.json` still checks. -/

def coreFiles : String := include_str "../vocab/core/files.json"
def coreUnits : String := include_str "../vocab/core/units.json"
def coreNet : String := include_str "../vocab/core/net.json"
def coreProc : String := include_str "../vocab/core/proc.json"

def coreSources : List (String × String) :=
  [("vocab/core/files.json", coreFiles), ("vocab/core/units.json", coreUnits),
   ("vocab/core/net.json", coreNet), ("vocab/core/proc.json", coreProc)]

end Lrep
