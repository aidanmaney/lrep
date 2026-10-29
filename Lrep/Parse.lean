/-
The parser: residue tokens to the surface AST, with the clause rules.

Each sentence reports at most one parse error, the lowest code among the rules that
apply. A sentence that fails to parse becomes `SSent.skip`, which the elaborator treats
as a wildcard so that no follow-on errors cascade from it.
-/
import Lrep.Token

namespace Lrep

inductive Lit where
  | str (s : String)
  | int (n : Nat)
  deriving Inhabited

inductive Atom where
  /-- A literal, with the sort written before it if any. -/
  | lit (sort : Option SortDef) (l : Lit) (text : String) (span : Span)
  | qty (n : Nat) (u : UnitDef) (text : String) (span : Span)
  /-- A bare sort: a definite description. -/
  | desc (s : SortDef) (plural : Bool) (text : String) (span : Span)
  | it (span : Span)
  | them (span : Span)
  | name (n : String) (span : Span)
  | const (c : ConstDef) (text : String) (span : Span)
  /-- A qualifier describing the atom after it, as in `the backup file "/backup/a"`. -/
  | qual (q : QualDef) (span : Span) (a : Atom)
  deriving Inhabited

def Atom.span : Atom → Span
  | .lit _ _ _ s | .qty _ _ _ s | .desc _ _ _ s | .it s | .them s | .name _ s | .const _ _ s => s
  | .qual _ _ a => a.span

structure Value where
  atoms : List Atom
  span : Span
  deriving Inhabited

structure Arg where
  label : String
  labelSpan : Span
  value : Value
  deriving Inhabited

structure Stmt where
  op : OpDef
  opTok : Tok
  obj : Option Value
  args : List Arg
  asName : Option (String × Span)
  span : Span
  deriving Inhabited

structure Test where
  subj : Atom
  are : Bool
  verbSpan : Span
  neg : Bool
  pred : PredDef
  args : List Arg
  span : Span
  deriving Inhabited

structure Claim where
  word : String
  op : OpDef
  obj : Option Value
  args : List Arg
  span : Span
  text : String
  /-- The bound of an `at most` claim. -/
  count : Nat := 0
  deriving Inhabited

/-- A parsed sentence. Bodies are inline statements (`inl`) or a list (`items`). -/
inductive SSent where
  | stmts (ss : List Stmt) (span : Span)
  | cond (all : Bool) (tests : List Test) (inl : List Stmt) (items : List (List SSent)) (span : Span)
  | other (inl : List Stmt) (items : List (List SSent)) (span : Span)
  | handler (inl : List Stmt) (items : List (List SSent)) (span : Span)
  | each (s : SortDef) (coll : Value) (inl : List Stmt) (items : List (List SSent)) (span : Span)
  | claims (cs : List Claim) (span : Span)
  /-- A sentence starting with a capitalised gloss word, which is an error if that word is
  a declared name. -/
  | lead (word : String) (span : Span) (inner : SSent)
  /-- A sentence that had errors; it still declares the names it tried to declare. -/
  | skip (names : List String)
  /-- A sentence that failed to parse. The elaborator reports `err`, unless the sentence
  starts with a declared name, which is E013 and the lower code. -/
  | failed (err : Diagnostic) (names : List String)
  deriving Inhabited

/-! ## Helpers -/

abbrev P := Except Diagnostic

private def err (code : String) (sp : Span) (m : String) (fix : Option Fix := none) : P α :=
  throw { code, span := sp, message := m, fix }

/-- E020 as a fallback for a sentence shape the code table doesn't name. -/
private def shape (sp : Span) (m : String) : P α :=
  throw { code := "E020", span := sp, message := m, weak := true }

private def spanOfToks (ts : List Tok) : Span :=
  match ts.head?, ts.getLast? with
  | some a, some b => a.span.join b.span
  | _, _ => Span.none

/-- A token that can start an atom. -/
def startsAtom (t : Tok) : Bool :=
  match t.cls with
  | .str _ | .int _ | .sort _ _ | .const _ | .name | .qual _ => true
  | .struct w => w == "it" || w == "them"
  | _ => false

def Tok.isQual (t : Tok) : Bool := match t.cls with | .qual _ => true | _ => false

/-- Parses one unqualified atom from the front of `ts`. -/
def atomBase? : List Tok → Option (Atom × List Tok)
  | t :: u :: rest =>
    match t.cls, u.cls with
    | .sort s _, .str v => some (.lit (some s) (.str v) u.text u.span, rest)
    | .sort s _, .int n => some (.lit (some s) (.int n) u.text u.span, rest)
    | .int n, .unit un => some (.qty n un (t.text ++ " " ++ u.text) (t.span.join u.span), rest)
    | _, _ => atom1? t (u :: rest)
  | [t] => atom1? t []
  | [] => none
where
  atom1? (t : Tok) (rest : List Tok) : Option (Atom × List Tok) :=
    match t.cls with
    | .str v => some (.lit none (.str v) t.text t.span, rest)
    | .int n => some (.lit none (.int n) t.text t.span, rest)
    | .sort s pl => some (.desc s pl t.text t.span, rest)
    | .const c => some (.const c t.text t.span, rest)
    | .name => some (.name t.text t.span, rest)
    | .struct "it" => some (.it t.span, rest)
    | .struct "them" => some (.them t.span, rest)
    | _ => none

/-- Parses one atom, with any qualifiers before it. -/
def atom? : List Tok → Option (Atom × List Tok)
  | t :: rest =>
    match t.cls with
    | .qual q => (atom? rest).map fun (a, r) => (.qual q t.span a, r)
    | _ => atomBase? (t :: rest)
  | [] => none

/-- `value ::= atom ( "and" atom )*`; an `and` continues the value only when an atom follows. -/
def value? (ts : List Tok) : Option (Value × List Tok) :=
  match atom? ts with
  | none => none
  | some (a, rest) =>
    let rec more (fuel : Nat) (acc : List Atom) (ts : List Tok) : List Atom × List Tok :=
      match fuel, ts with
      | fuel + 1, t :: rest' =>
        if t.isStruct "and" then
          match atom? rest' with
          | some (b, rest'') => more fuel (acc ++ [b]) rest''
          | none => (acc, ts)
        else (acc, ts)
      | _, _ => (acc, ts)
    let (atoms, rest') := more (ts.length + 1) [a] rest
    some (⟨atoms, (atoms.head?.map Atom.span).getD Span.none |>.join ((atoms.getLast?.map Atom.span).getD Span.none)⟩, rest')

/-- The words a clause dropped as gloss, for E020's message. -/
private def glossWords (ts : List Tok) : List String :=
  ts.filter (fun t => match t.cls with | .gloss | .name => true | _ => false) |>.map (·.text)

private def quoteList (ws : List String) : String := ", ".intercalate (ws.map fun w => s!"\"{w}\"")

private def withCase (like : String) (w : String) : String :=
  if (like.toList.head?.map Char.isUpper).getD false then
    match w.toList with | c :: cs => String.ofList (c.toUpper :: cs) | [] => w
  else w

/-- Parses labelled arguments, given the labels the op or predicate declares. Returns the
arguments and the unconsumed tokens. -/
def labelled (fuel : Nat) (declared : List String) (what : String) (ts : List Tok) :
    P (List Arg × List Tok) :=
  match fuel with
  | 0 => pure ([], ts)
  | fuel + 1 =>
    match ts with
    | t :: rest =>
      match t.cls with
      | .label l =>
        if !declared.contains l then
          err "E025" t.span s!"{what} takes no \"{l}\" argument"
            (some { label := if declared.isEmpty then s!"{what} declares no labels"
                             else s!"declared labels: {", ".intercalate declared}" })
        else match rest.head? with
          | some u => if u.isOp then err "E011" u.span s!"\"{u.text}\" is an op word where a value belongs"
              (some { label := "rephrase without the op word, or move it into an aside" })
            else match value? rest with
              | some (v, rest') => do
                let (more, rest'') ← labelled fuel declared what rest'
                if more.any (·.label == l) then
                  err "E026" t.span s!"second \"{l}\" argument"
                else pure (⟨l, t.span, v⟩ :: more, rest'')
              | none => err "E027" t.span s!"\"{l}\" has no value"
          | none => err "E027" t.span s!"\"{l}\" has no value"
      | _ => pure ([], ts)
    | [] => pure ([], ts)

/-- An error for a token that doesn't fit, given the token after it. `and` is E022 only
when a statement follows it. -/
private def unexpected (t : Tok) (next : Option Tok) (where_ : String) : P α :=
  if t.isOp then err "E011" t.span s!"\"{t.text}\" is an op word where a value belongs"
    (some { label := "rephrase without the op word, or move it into an aside" })
  else if t.isStruct "and" && (next.map Tok.isOp).getD false then err "E022" t.span "`and` between statements"
    (some { label := "replace `and` with `then`", edit := some (t.span, "then") })
  else shape t.span s!"\"{t.text}\" cannot appear {where_}"

/-! ## Statements -/

def checkRequired (required : List String) (hasObj : Bool) (args : List Arg) (sp : Span) (what : String) : P Unit := do
  for r in required do
    if r == "object" then
      unless hasObj do err "E027" sp s!"{what} needs an object"
    else unless args.any (·.label == r) do err "E027" sp s!"{what} needs a \"{r}\" argument"

/-- `stmt ::= OP value? labelled* ( "as" NAME )?`, over a clause's residue. -/
def parseStmt (all : List Tok) (res : List Tok) : P Stmt := do
  match res with
  | [] => err "E020" (spanOfToks all) "a clause needs an op"
  | t :: rest =>
    let glosses := glossWords all
    let noOp := err "E020" (spanOfToks all) s!"clause has no op{if glosses.isEmpty then "" else s!"; dropped as gloss: {quoteList glosses}"}"
      (some { label := if glosses.isEmpty then "add an op" else s!"{quoteList glosses} is not an op in the loaded vocabularies" })
    match t.cls with
    | .op o form =>
      if form != "base" then
        err "E024" t.span s!"\"{t.text}\" is not the base form of {o.base}"
          (some { label := s!"write \"{withCase t.text o.base}\", or rewrite the sentence as a claim",
                  edit := some (t.span, withCase t.text o.base) })
      else
      let what := s!"\"{o.base}\""
      let (obj, rest) := match rest.head? with
        | some u => if startsAtom u then (match value? rest with | some (v, r) => (some v, r) | none => (none, rest)) else (none, rest)
        | none => (none, rest)
      let (args, rest) ← labelled (rest.length + 1) (o.labels.map (·.1)) what rest
      if obj.isSome && !o.takesObject then
        err "E026" (obj.map (·.span)).get! s!"{what} takes no object"
      else
      let (asName, rest) ← match rest with
        | a :: n :: rest' =>
          if a.isStruct "as" then
            match n.cls with
            | .name => pure (some (n.text, n.span), rest')
            | _ => err "E013" n.span "`as` must be followed by a capitalised name"
          else pure (none, rest)
        | [a] => if a.isStruct "as" then err "E013" a.span "`as` must be followed by a capitalised name" else pure (none, rest)
        | [] => pure (none, rest)
      match rest with
      | u :: more =>
        if startsAtom u then err "E026" u.span "second unlabelled argument"
        else unexpected u more.head? "here"
      | [] =>
        checkRequired o.required obj.isSome args t.span what
        pure { op := o, opTok := t, obj, args, asName, span := t.span }
    | _ =>
      if res.any Tok.isOp then
        shape t.span s!"a clause starts with its op, not \"{t.text}\""
      else noOp

structure Clause where
  thenTok : Option Tok
  toks : List Tok

/-- Splits at commas and `then`. Commas always end a clause. -/
def splitClauses (ts : List Tok) : List Clause :=
  let step (acc : List Clause × Clause × Bool) (t : Tok) : List Clause × Clause × Bool :=
    let (done, cur, _) := acc
    if t.isComma then (done ++ [cur], ⟨none, []⟩, true)
    else if t.isStruct "then" then
      if cur.toks.any Tok.isProgram then (done ++ [cur], ⟨some t, []⟩, false)
      else (done, { cur with thenTok := some t }, false)
    else (done, { cur with toks := cur.toks ++ [t] }, false)
  let (done, cur, _) := ts.foldl step ([], ⟨none, []⟩, false)
  done ++ [cur]

/-- `statements ::= stmt ( ","? "then" stmt )*`. -/
def parseStmts (ts : List Tok) : P (List Stmt) := do
  let clauses := splitClauses ts
  let results := clauses.zipIdx.map fun (c, i) =>
    let res := c.toks.filter Tok.isProgram
    let seqErr : List Diagnostic :=
      if i > 0 && c.thenTok.isNone then
        match c.toks.head? with
        | some t => [{ code := "E021", span := t.span, message := "every clause after the first starts with `then`",
                       fix := some { label := "insert `then`", edit := some (⟨t.span.line, t.span.col, t.span.col⟩, "then ") } }]
        | none => []
      else []
    match parseStmt c.toks res with
    | .ok s => (seqErr, some s)
    | .error e => (seqErr ++ [e], none)
  match lowest (results.flatMap (·.1)) with
  | some e => throw e
  | none => pure (results.filterMap (·.2))

/-! ## Conditions -/

private def startsSubject (ts : List Tok) : Bool :=
  match ts.dropWhile Tok.isQual with
  | t :: u :: _ =>
    let subj := match t.cls with
      | .struct "it" | .struct "them" | .name | .sort _ _ => true
      | _ => false
    subj && (u.isStruct "is" || u.isStruct "are")
  | _ => false

/-- Splits a condition into tests at `and`/`or` followed by a new subject. -/
def splitTests (ts : List Tok) : List (List Tok) × List Tok :=
  let rec go (fuel : Nat) (cur : List Tok) (ts : List Tok) : List (List Tok) × List Tok :=
    match fuel, ts with
    | fuel + 1, t :: rest =>
      if (t.isStruct "and" || t.isStruct "or") && startsSubject rest then
        let (more, conns) := go fuel [] rest
        (cur :: more, t :: conns)
      else go fuel (cur ++ [t]) rest
    | _, _ => ([cur], [])
  go (ts.length + 1) [] ts

def parseTest (ts0 : List Tok) : P Test := do
  let quals := ts0.takeWhile Tok.isQual
  let ts := ts0.drop quals.length
  match ts with
  | s :: v :: rest =>
    let subj0 ← match atomBase?.atom1? s [] with
      | some (a@(.it _), _) | some (a@(.them _), _) | some (a@(.name _ _), _) | some (a@(.desc ..), _) => pure a
      | _ => shape s.span "a condition starts with it, them, a name or a sort"
    let subj := quals.foldr (fun q a => match q.cls with | .qual qd => Atom.qual qd q.span a | _ => a) subj0
    unless v.isStruct "is" || v.isStruct "are" do shape v.span "a condition applies a predicate with is or are"
    let (neg, rest) := match rest with
      | n :: r => if n.isStruct "not" then (true, r) else (false, rest)
      | [] => (false, rest)
    match rest with
    | p :: rest =>
      match p.cls with
      | .pred pd =>
        let what := s!"\"{p.text}\""
        let (args, rest) ← labelled (rest.length + 1) (pd.labels.map (·.1)) what rest
        match rest with
        | u :: more => unexpected u more.head? "in a condition"
        | [] =>
          checkRequired pd.required true args p.span what
          pure { subj, are := v.isStruct "are", verbSpan := v.span, neg, pred := pd, args,
                 span := s.span.join p.span }
      | _ => if p.isOp then unexpected p none "" else shape p.span s!"\"{p.text}\" is not a predicate"
    | [] => shape v.span "a predicate must follow is or are"
  | _ => shape (spanOfToks ts) "a condition is a subject, is or are, and a predicate"

/-- `cond ::= test ( "and" test )* | test ( "or" test )+`. -/
def parseCond (ts : List Tok) : P (Bool × List Test) := do
  let (parts, conns) := splitTests ts
  let ands := conns.filter (·.isStruct "and")
  let ors := conns.filter (·.isStruct "or")
  if !ands.isEmpty && !ors.isEmpty then
    err "E029" (ors.head!.span) "a condition may not mix `and` and `or`"
      (some { label := "split the condition into separate sentences" })
  else
    let tests ← parts.mapM parseTest
    pure (ors.isEmpty, tests)

/-! ## Claims -/

/-- Splits claims at `and` (optionally after a comma) followed by a claim word, or by an op
followed by `at most`. -/
def splitClaims (ts : List Tok) : List (List Tok) :=
  let startsClaim (rest : List Tok) : Bool :=
    match rest with
    | t :: u :: _ => t.isClaim || (t.isOp && u.isClaim)
    | [t] => t.isClaim
    | [] => false
  let rec go (fuel : Nat) (cur : List Tok) (ts : List Tok) : List (List Tok) :=
    match fuel, ts with
    | fuel + 1, t :: rest =>
      if t.isStruct "and" && startsClaim rest then cur :: go fuel [] rest
      else if t.isComma && (match rest with | a :: r => a.isStruct "and" && startsClaim r | [] => false) then go fuel cur rest
      else go fuel (cur ++ [t]) rest
    | _, _ => [cur]
  go (ts.length + 1) [] ts

private def claimText (ts : List Tok) : String := " ".intercalate (ts.map (·.text))

private def claimBody (w : Tok) (word : String) (od : OpDef) (ts rest : List Tok) : P Claim := do
  let declared := (if od.isPrimitive then od.claimLabels else od.labels.map (·.1)) ++ od.contentsLabel.toList
  let (obj, rest) := match rest.head? with
    | some u => if startsAtom u then (match value? rest with | some (v, r) => (some v, r) | none => (none, rest)) else (none, rest)
    | none => (none, rest)
  let what := if od.isPrimitive then s!"a claim on \"{od.base}\"" else s!"\"{od.base}\""
  let (args, rest) ← labelled (rest.length + 1) declared what rest
  match rest with
  | u :: more => unexpected u more.head? "in a claim"
  | [] =>
    let sp := w.span.join ((ts.getLast?.map (·.span)).getD w.span)
    if word == "only" && obj.isNone && args.isEmpty then
      err "E027" sp "`only` needs at least one resource"
    else pure { word, op := od, obj, args, span := sp, text := claimText ts }

def parseClaim (ts : List Tok) : P Claim := do
  let whole := (ts.head?.map (·.span)).getD Span.none |>.join ((ts.getLast?.map (·.span)).getD Span.none)
  match ts with
  | w :: o :: rest =>
    match w.cls, o.cls with
    | .claim word, .op od _ =>
      if word == "at most" then shape w.span "`at most` follows its op"
      else claimBody w word od ts rest
    | .op od _, .claim word =>
      if word == "at most" then
        match rest with
        | [n] =>
          match n.cls with
          | .int k => pure { word, op := od, obj := none, args := [], span := whole, text := claimText ts, count := k }
          | _ => shape n.span "`at most` is followed by a numeral"
        | [] => shape o.span "`at most` is followed by a numeral"
        | _ :: u :: _ => shape u.span "`at most` claims take no arguments"
      else shape w.span "a claim starts with never, only or always"
    | .claim _, _ =>
      if o.isGloss then shape o.span s!"\"{o.text}\" is not an op in the loaded vocabularies"
      else shape o.span "a claim word is followed by an op"
    | _, _ => shape w.span "a claim starts with never, only or always"
  | [w] => shape w.span "a claim word is followed by an op"
  | [] => shape Span.none "empty claim"

def parseClaims (ts : List Tok) : P (List Claim) := do
  let res := ts.filter Tok.isProgram
  -- A comma not followed by `and` doesn't join claims.
  let parts := splitClaims res
  for p in parts do
    if let some c := p.find? Tok.isComma then
      shape c.span "claims are joined with `and`"
  parts.mapM parseClaim

/-! ## Sentences -/

/-- Names a sentence declares, so a skipped sentence still binds them. -/
private def declaredNames : List Tok → List String
  | a :: n :: rest =>
    if a.isStruct "as" then (match n.cls with | .name => [n.text] | _ => []) ++ declaredNames rest
    else declaredNames (n :: rest)
  | _ => []

private def firstComma (ts : List Tok) : Option (List Tok × List Tok) :=
  match ts.findIdx? Tok.isComma with
  | some i => some (ts.take i, ts.drop (i + 1))
  | none => none

/-- An inline body: `","` statements `"."`. A `then` right after the comma is E023. -/
def parseInline (afterComma : List Tok) : P (List Stmt) := do
  match afterComma.filter Tok.isProgram |>.head? with
  | some t =>
    if t.isStruct "then" then
      err "E023" t.span "`then` after a condition"
        (some { label := "delete `then`", edit := some (⟨t.span.line, t.span.col, t.span.endCol + 1⟩, "") })
    else parseStmts afterComma
  | none => shape (spanOfToks afterComma) "the body has no statement"

/-- The E042 a sentence earns: a claim word, or "this section", outside a claim sentence. -/
def claimPlacement (toks : List Tok) : Option Diagnostic :=
  let res := toks.filter Tok.isProgram
  let isClaimSentence := (res.head?.map (·.isStruct "this section")).getD false
  let misplaced : Option Diagnostic :=
    if isClaimSentence then none
    else (res.find? Tok.isClaim).map fun c =>
      { code := "E042", span := c.span, message := s!"claim word \"{c.text}\" outside a sentence starting \"This section\"",
        fix := some { label := "state the claim in its own sentence: This section …" } }
  misplaced <|> ((res.drop 1).find? (·.isStruct "this section")).map fun t =>
    { code := "E042", span := t.span, message := "\"this section\" starts a claim sentence" }

/-- Parses one sentence's shape, given its already-parsed list items. -/
def dispatchShape (toks : List Tok) (term : Char) (sp : Span) (items : List (List SSent)) : P SSent := do
  let res := toks.filter Tok.isProgram
  let first := res.head?
  -- A body is either inline after a comma, or a list after a colon.
  let body (rest : List Tok) (what : String) : P (List Stmt × List (List SSent)) := do
    match firstComma rest with
    | some (_, after) =>
      if term == ':' then err "E001" sp s!"{what} with an inline body ends in `.`"
      else pure (← parseInline after, [])
    | none =>
      if term == ':' then pure ([], items)
      else shape sp s!"{what} needs a body: a comma and statements, or a colon and a list"
  match first with
  | none => shape sp "sentence has no program words"
  | some f =>
    let rest := (toks.dropWhile (fun t => !(t.span == f.span))).drop 1
    if f.isStruct "this section" then
      if term == ':' then err "E001" sp "a claim sentence ends in `.`"
      else return .claims (← parseClaims rest) sp
    else if f.isStruct "if" then
      let r := rest.filter Tok.isProgram
      match r with
      | a :: b :: _ =>
        if a.isStruct "it" && b.isStruct "fails" then
          let rest' := (rest.dropWhile (fun t => !(t.span == b.span))).drop 1
          let (inl, its) ← body rest' "If it fails"
          return .handler inl its sp
        else pure ()
      | _ => pure ()
      let condToks := match firstComma rest with | some (c, _) => c | none => rest
      let (all, tests) ← parseCond (condToks.filter Tok.isProgram)
      let (inl, its) ← body rest "a conditional"
      return .cond all tests inl its sp
    else if f.isStruct "otherwise" then
      let (inl, its) ← body rest "otherwise"
      return .other inl its sp
    else if f.isStruct "for each" then
      let r := rest.filter Tok.isProgram
      match r with
      | s :: i :: _ =>
        match s.cls with
        | .sort sd false =>
          unless i.isLabel do shape i.span "for each <sort> is followed by in"
          let collToks := ((match firstComma rest with | some (c, _) => c | none => rest).filter Tok.isProgram).drop 2
          match value? collToks with
          | some (v, []) =>
            let (inl, its) ← body rest "for each"
            return .each sd v inl its sp
          | some (_, u :: more) => unexpected u more.head? "in a loop header"
          | none => err "E027" i.span "for each needs a collection after in"
        | .sort _ true => err "E030" s.span "for each takes the singular sort"
        | _ => shape s.span "for each is followed by a sort"
      | _ => shape f.span "for each <sort> in <collection>"
    else
      if term == ':' then err "E001" sp "only if, otherwise, If it fails and for each take a list"
      else return .stmts (← parseStmts toks) sp


/-- Parses one sentence. E042 competes with the parse errors, and the lower code wins. -/
def dispatch (toks : List Tok) (term : Char) (sp : Span) (items : List (List SSent)) : P SSent :=
  let placement := claimPlacement toks
  match dispatchShape toks term sp items, placement with
  | .ok s, none => .ok s
  | .ok _, some e => .error e
  | .error e, some p => .error (if e.weak then p else (lowest [e, p]).getD e)
  | .error e, none => .error e

mutual
def parseSent : TSent → SSent × List Diagnostic
  | .mk toks term termSpan bad sub =>
    if bad then (.skip (declaredNames toks), [])
    else
      let sp := (TSent.mk toks term termSpan bad sub).span
      let (items, ds) := parseItems sub
      let r := dispatch toks term sp items
      let lead := match toks.head? with
        | some t => if t.isGloss && (t.text.toList.head?.map Char.isUpper).getD false then some (t.text, t.span) else none
        | none => none
      let s := match r with
        | .ok s => s
        | .error e => .failed e (declaredNames toks)
      (match lead with | some (w, s') => .lead w s' s | none => s, ds)

def parseItems : List (List TSent) → List (List SSent) × List Diagnostic
  | [] => ([], [])
  | it :: rest =>
    let (a, ds1) := parseSents it
    let (b, ds2) := parseItems rest
    (a :: b, ds1 ++ ds2)

def parseSents : List TSent → List SSent × List Diagnostic
  | [] => ([], [])
  | s :: rest =>
    let (a, ds1) := parseSent s
    let (b, ds2) := parseSents rest
    (a :: b, ds1 ++ ds2)
end

def parseSection (s : TSection) : List SSent × List Diagnostic := parseSents s.sents

end Lrep
