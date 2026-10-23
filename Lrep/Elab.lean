/-
Elaboration: resolves `it`, `them`, names and descriptions, checks sorts, and produces
the core AST.

Each sentence reports at most one elaboration error. A sentence with an error, like a
skipped one, leaves wildcard bindings (sort `?`) behind so later sentences don't cascade.
-/
import Lrep.Parse

namespace Lrep

/-! ## Core AST -/

inductive CVal where
  /-- A literal, typed at the sort of the parameter it fills. -/
  | lit (s : SortDef) (l : Lit) (text : String) (span : Span)
  /-- A quantity: `n` units of `scale` base units (seconds, bytes) each. -/
  | qty (n : Nat) (sort : String) (scale : Nat) (unit : String) (span : Span)
  | const (c : ConstDef) (span : Span)
  /-- A statement result or loop element, by binding id. -/
  | ref (id : Nat) (span : Span)
  | list (vs : List CVal)
  /-- A value from a sentence that had errors. -/
  | unknown
  deriving Inhabited

/-- An argument; label `""` is the op's object or the predicate's subject. -/
structure CArg where
  label : String
  val : CVal
  deriving Inhabited

structure CTest where
  pred : PredDef
  args : List CArg
  neg : Bool
  site : Span
  deriving Inhabited

inductive CStmt where
  | call (id : Nat) (op : OpDef) (args : List CArg) (site : Span)
  | ite (all : Bool) (tests : List CTest) (thn els : List CStmt)
  | loop (elem : Nat) (coll : CVal) (body : List CStmt)
  | try (body handler : List CStmt)
  deriving Inhabited

structure CClaim where
  word : String
  op : OpDef
  args : List CArg
  span : Span
  text : String
  count : Nat := 0
  deriving Inhabited

/-- A qualifier applied to a value, checked once the section's resources are known. -/
structure CQual where
  q : QualDef
  val : CVal
  span : Span
  deriving Inhabited

structure CSection where
  name : String
  stmts : List CStmt
  claims : List CClaim
  quals : List CQual := []
  deriving Inhabited

/-! ## Environment -/

/-- A type: a sort name, and whether it is a list. Sort `?` fits anything. -/
structure Ty where
  sort : String
  list : Bool
  deriving BEq, Inhabited

def Ty.show (t : Ty) : String :=
  if t.sort == "?" then "an unknown value" else if t.list then s!"a list of {t.sort}" else s!"a {t.sort}"

structure Bind where
  name : String
  id : Nat
  ty : Ty
  /-- What the binding is, for hover: "the result of `list` on line 3, a list of file". -/
  about : String
  deriving Inhabited

/-- A composite op's body, elaborated once with placeholder ids for its parameters. -/
structure Template where
  /-- Argument label (`""` for the object) and the placeholder id standing for it. -/
  params : List (String × Nat)
  stmts : List CStmt
  /-- How many ids the body uses, placeholders included. -/
  size : Nat
  deriving Inhabited

structure Env where
  names : List Bind := []
  elems : List Bind := []
  topic : Option Bind := none
  /-- Composite ops' bodies, by base form. Empty inside a body, so bodies can't nest. -/
  templates : List (String × Template) := []
  deriving Inhabited

structure St where
  next : Nat := 0
  diags : List Diagnostic := []
  /-- What each `it`, `them`, name and description refers to, for hover. -/
  refs : List (Span × String) := []
  /-- Qualifiers applied to values, for checking after inference. -/
  quals : List CQual := []

abbrev EM := StateM St
abbrev EE := ExceptT Diagnostic EM

private def fresh : EE Nat := do
  let s ← get
  set { s with next := s.next + 1 }
  pure s.next

private def err (code : String) (sp : Span) (m : String) (fix : Option Fix := none) : EE α :=
  throw { code, span := sp, message := m, fix }

def wildcard : Ty := ⟨"?", false⟩

/-! ## Values -/

/-- An atom resolved: either a typed value, or a literal whose sort comes from the parameter. -/
inductive RAtom where
  | typed (v : CVal) (t : Ty)
  | lit (l : Lit) (text : String) (span : Span)

private def swapFix (sp : Span) (to : String) : Fix := { label := s!"use `{to}`", edit := some (sp, to) }

/-- Records what a reference resolved to, then returns it. -/
private def refer (sp : Span) (what : String) (b : Bind) : EE RAtom := do
  modify fun s => { s with refs := s.refs ++ [(sp, s!"{what} refers to {b.about}")] }
  pure (.typed (.ref b.id sp) b.ty)

/-- An atom's qualifiers and the atom they describe. -/
def stripQuals : Atom → List (QualDef × Span) × Atom
  | .qual q sp a => let (qs, b) := stripQuals a; ((q, sp) :: qs, b)
  | a => ([], a)

private def recordQuals (qs : List (QualDef × Span)) (v : CVal) : EE Unit :=
  modify fun s => { s with quals := s.quals ++ qs.map fun (q, sp) => ⟨q, v, sp⟩ }

def resolveAtom (_lex : Lexicon) (env : Env) : Atom → EE RAtom
  | .qual _ _ a => resolveAtom _lex env a
  | .it sp =>
    match env.topic with
    | none => err "E031" sp "`it` has no topic here"
    | some b =>
      if b.ty.list then err "E031" sp s!"`it` refers to {b.ty.show}" (some (swapFix sp "them"))
      else refer sp "`it`" b
  | .them sp =>
    match env.topic with
    | none => err "E031" sp "`them` has no topic here"
    | some b =>
      if !b.ty.list && b.ty.sort != "?" then err "E031" sp s!"`them` refers to {b.ty.show}" (some (swapFix sp "it"))
      else refer sp "`them`" b
  | .name n sp =>
    match env.names.find? (·.name == n) with
    | some b => refer sp s!"`{n}`" b
    | none => err "E013" sp s!"\"{n}\" is not a declared name" (some { label := s!"declare it with `as {n}`" })
  | .desc s pl text sp => do
    let want : Ty := ⟨s.name, pl⟩
    let cands := (env.names ++ env.elems).filter (·.ty == want)
    match cands with
    | [b] => refer sp s!"\"{text}\"" b
    | [] =>
      if (env.names ++ env.elems).any (·.ty.sort == "?") then
        pure (RAtom.typed CVal.unknown wildcard)
      else
        err "E032" sp s!"no {text} in scope for \"{text}\" to refer to"
          (some { label := s!"name a {s.name} with `as` and refer to it by name" })
    | bs =>
      let names := bs.map fun b => if b.name.isEmpty then s!"the current {s.name}" else b.name
      err "E032" sp s!"\"{text}\" could refer to {" or ".intercalate names}"
        (some { label := s!"use one of: {", ".intercalate names}" })
  | .const c _ sp => pure (.typed (.const c sp) ⟨c.sort, false⟩)
  | .qty n u text sp => pure (.typed (.qty n u.sort u.scale ((text.splitOn " ").getLast?.getD "") sp) ⟨u.sort, false⟩)
  | .lit none l text sp => pure (.lit l text sp)
  | .lit (some s) l text sp =>
    let (str?, int?) := match l with | .str v => (some v, none) | .int n => (none, some n)
    match validateLit s str? int? with
    | some m => err "E030" sp s!"{text} is not a valid {s.name}: {m}"
    | none => pure (.typed (.lit s l text sp) ⟨s.name, false⟩)

private def litOk (s : SortDef) (l : Lit) : Option String :=
  match l with
  | .str v => validateLit s (some v) none
  | .int n => validateLit s none (some n)

/-- Fits a value to a parameter declared as one or more sorts; the first sort that accepts
the argument wins. -/
def fitValue (lex : Lexicon) (env : Env) (params : List String) (v : Value) (what : String) : EE (CVal × Ty) := do
  let parts := v.atoms.map stripQuals
  let r ← fitAtoms (← parts.mapM fun p => resolveAtom lex env p.2)
  -- Each qualifier describes its own atom's value.
  for (p, i) in parts.zipIdx do
    let vi := match r.1 with | .list vs => vs[i]?.getD r.1 | c => c
    recordQuals p.1 vi
  pure r
where
  fitAtoms (atoms : List RAtom) : EE (CVal × Ty) := do
    let ps := params.filterMap lex.paramSort?
    let fitOne (s : SortDef) (pl : Bool) : Option (CVal × Ty) :=
      match atoms with
      | [.typed cv t] => if t.sort == "?" || (t.sort == s.name && t.list == pl) then some (cv, ⟨s.name, pl⟩) else none
      | [.lit l text sp] => if !pl && (litOk s l).isNone then some (.lit s l text sp, ⟨s.name, false⟩) else none
      | as =>
        if !pl then none
        else
          let vs := as.filterMap fun
            | .typed cv t => if t.sort == "?" || (t.sort == s.name && !t.list) then some cv else none
            | .lit l text sp => if (litOk s l).isNone then some (.lit s l text sp) else none
          if vs.length == as.length then some (.list vs, ⟨s.name, true⟩) else none
    match ps.findSome? fun (s, pl) => fitOne s pl with
    | some r => pure r
    | none =>
      -- Prefer the literal's own validation message, such as a port out of range.
      let litMsg := match atoms with
        | [.lit l text _] => ps.findSome? fun ((s, _) : SortDef × Bool) =>
            let kindFits : Bool := match s.literal, l with
              | LitKind.int, Lit.int _ => true
              | LitKind.path, Lit.str _ | LitKind.url, Lit.str _ | LitKind.string, Lit.str _ => true
              | _, _ => false
            if kindFits then (litOk s l).map fun m => s!"{text} is not a valid {s.name}: {m}" else none
        | _ => none
      let got := match atoms with
        | [.typed _ t] => t.show
        | [.lit _ text _] => text
        | _ => "a list"
      err "E030" v.span (litMsg.getD s!"{what} takes {" or ".intercalate (params.map fun p => s!"a {p}")}, not {got}")

/-! ## Statements -/

mutual
/-- Instantiates a template value: placeholders become arguments; other ids move by `base`. -/
def substVal (base : Nat) (ps : List (Nat × CVal)) : CVal → CVal
  | .ref id sp => match ps.lookup id with | some v => v | none => .ref (base + id) sp
  | .list vs => .list (substVals base ps vs)
  | v => v
def substVals (base : Nat) (ps : List (Nat × CVal)) : List CVal → List CVal
  | [] => []
  | v :: vs => substVal base ps v :: substVals base ps vs
end

def substArgs (base : Nat) (ps : List (Nat × CVal)) (as : List CArg) : List CArg :=
  as.map fun a => { a with val := substVal base ps a.val }

mutual
def substStmt (base : Nat) (ps : List (Nat × CVal)) : CStmt → CStmt
  | .call id op args site => .call (base + id) op (substArgs base ps args) site
  | .ite all tests thn els =>
    .ite all (tests.map fun t => { t with args := substArgs base ps t.args })
      (substStmts base ps thn) (substStmts base ps els)
  | .loop elem coll body => .loop (base + elem) (substVal base ps coll) (substStmts base ps body)
  | .try body h => .try (substStmts base ps body) (substStmts base ps h)
def substStmts (base : Nat) (ps : List (Nat × CVal)) : List CStmt → List CStmt
  | [] => []
  | s :: rest => substStmt base ps s :: substStmts base ps rest
end

/-- Elaborates one statement, returning its core statements and the binding of its result.
A composite op's call is followed by its body, instantiated with the call's arguments. -/
def elabStmt (lex : Lexicon) (env : Env) (s : Stmt) : EE (List CStmt × Env) := do
  let what := s!"\"{s.op.base}\""
  let obj ← match s.obj with
    | some v => do let (cv, _) ← fitValue lex env s.op.object v what; pure [⟨"", cv⟩]
    | none => pure []
  let args ← s.args.mapM fun a => do
    let (cv, _) ← fitValue lex env ((s.op.labels.lookup a.label).getD []) a.value s!"\"{a.label}\""
    pure (⟨a.label, cv⟩ : CArg)
  let id ← fresh
  let env' ← match s.op.returns with
    | some r =>
      let ty : Ty := ⟨r.sort, r.list⟩
      let b : Bind := ⟨"", id, ty, s!"the result of `{s.op.base}` on line {s.span.line}, {ty.show}"⟩
      match s.asName with
      | some (n, sp) =>
        if env.names.any (·.name == n) then err "E033" sp s!"\"{n}\" is already declared"
        else pure { env with topic := some b, names := env.names ++ [{ b with name := n }] }
      | none => pure { env with topic := some b }
    | none =>
      match s.asName with
      | some (n, sp) => err "E030" sp s!"{what} returns nothing for \"{n}\" to name"
      | none => pure { env with topic := none }
  let call := CStmt.call id s.op (obj ++ args) s.span
  match s.op.body with
  | none => pure ([call], env')
  | some _ =>
    match env.templates.lookup s.op.base with
    | none => err "E050" s.span s!"{what} is a composite op, which a composite op's body may not call"
    | some tpl =>
      let st ← get
      set { st with next := st.next + tpl.size }
      let ps := tpl.params.filterMap fun (l, pid) => ((obj ++ args).find? (·.label == l)).map (pid, ·.val)
      pure (call :: substStmts st.next ps tpl.stmts, env')

def elabStmts (lex : Lexicon) (env : Env) : List Stmt → EE (List CStmt × Env)
  | [] => pure ([], env)
  | s :: rest => do
    let (c, env') ← elabStmt lex env s
    let (cs, env'') ← elabStmts lex env' rest
    pure (c ++ cs, env'')

def elabTest (lex : Lexicon) (env : Env) (t : Test) : EE CTest := do
  let (subjQuals, subjAtom) := stripQuals t.subj
  let subj ← resolveAtom lex env subjAtom
  let (cv, ty) ← match subj with
    | .typed cv ty => pure (cv, ty)
    | .lit _ _ sp => err "E030" sp "a condition's subject is it, them, a name or a sort"
  recordQuals subjQuals cv
  if ty.sort != "?" then
    if t.are && !ty.list then err "E031" t.verbSpan s!"`are` needs a list, but the subject is {ty.show}" (some (swapFix t.verbSpan "is"))
    if !t.are && ty.list then err "E031" t.verbSpan s!"`is` needs one value, but the subject is {ty.show}" (some (swapFix t.verbSpan "are"))
    unless t.pred.subject.contains ty.sort do
      err "E030" t.subj.span s!"\"{t.pred.forms.headD ""}\" applies to {" or ".intercalate t.pred.subject}, not {ty.show}"
  let args ← t.args.mapM fun a => do
    let (v, _) ← fitValue lex env ((t.pred.labels.lookup a.label).getD []) a.value s!"\"{a.label}\""
    pure (⟨a.label, v⟩ : CArg)
  pure { pred := t.pred, args := ⟨"", cv⟩ :: args, neg := t.neg, site := t.span }

/-! ## Claims -/

/-- The pseudo-sorts claim literals are read at: a string with a scheme is a URL, any other
string an absolute path prefix, and a number a port. -/
def claimUrl : SortDef := ⟨"url", [], .url, .url⟩
def claimPath : SortDef := ⟨"path", [], .path, .pathPrefix⟩
def claimPort : SortDef := ⟨"port", [], .int, .port⟩

def elabClaimValue (lex : Lexicon) (env : Env) (v : Value) : EE CVal := do
  let vs ← v.atoms.mapM fun a0 => do
    let (qs, a) := stripQuals a0
    let cv ← (do match ← resolveAtom lex env a with
    | .typed cv _ => pure cv
    | .lit (.str s) text sp =>
      if hasScheme s then
        match parseUrl s with
        | .ok _ => pure (.lit claimUrl (.str s) text sp)
        | .error m => err "E030" sp s!"{text} is not a valid URL: {m}"
      else if !isAbsolute s then
        err "E030" sp s!"{text} is a relative path; a claim names absolute paths"
          (some { label := s!"write \"/{s}\"", edit := some (sp, s!"\"/{s}\"") })
      else match normPath s with
        | .ok _ => pure (.lit claimPath (.str s) text sp)
        | .error m => err "E030" sp s!"{text} is not a valid path: {m}"
    | .lit (.int n) text sp =>
      match validateLit claimPort none (some n) with
      | some m => err "E030" sp s!"{text} is not a valid port: {m}"
      | none => pure (.lit claimPort (.int n) text sp) : EE CVal)
    recordQuals qs cv
    pure cv
  pure (match vs with | [x] => x | xs => .list xs)

def elabClaim (lex : Lexicon) (env : Env) (c : Claim) : EE CClaim := do
  let obj ← match c.obj with
    | some v => do pure [⟨"", ← elabClaimValue lex env v⟩]
    | none => pure []
  let args ← c.args.mapM fun a => do pure (⟨a.label, ← elabClaimValue lex env a.value⟩ : CArg)
  pure { word := c.word, op := c.op, args := obj ++ args, span := c.span, text := c.text, count := c.count }

/-! ## Sentences and bodies -/

/-- What the previous sentence in a body was, for placement checks. -/
inductive Prev where
  | none
  /-- A conditional, with the topic its body started with. -/
  | cond (topic : Option Bind)
  /-- A statement sentence, with the number of core statements it produced. -/
  | stmts (n : Nat)
  /-- A sentence with errors: anything may follow it. -/
  | skipped
  | other

structure Out where
  stmts : List CStmt := []
  claims : List CClaim := []

private def record (d : Diagnostic) : EM Unit := modify fun s => { s with diags := s.diags ++ [d] }

/-- Binds a skipped sentence's names as wildcards and leaves an unknown topic. -/
private def skipEnv (env : Env) (names : List String) : EM Env := do
  let mut env := env
  for n in names do
    let s ← get
    set { s with next := s.next + 1 }
    unless env.names.any (·.name == n) do
      env := { env with names := env.names ++ [⟨n, s.next, wildcard, "a value from a sentence with errors"⟩] }
  let s ← get
  set { s with next := s.next + 1 }
  pure { env with topic := some ⟨"", s.next, wildcard, "a value from a sentence with errors"⟩ }

/-- Attaches an `otherwise` body to the last conditional in `out`. -/
private def attachElse (out : List CStmt) (els : List CStmt) : List CStmt :=
  match out.getLast? with
  | some (.ite a ts thn []) => out.dropLast ++ [.ite a ts thn els]
  | _ => out ++ els

/-- Wraps the last `n` statements in a failure handler. -/
private def attachHandler (out : List CStmt) (n : Nat) (h : List CStmt) : List CStmt :=
  out.take (out.length - n) ++ [.try (out.drop (out.length - n)) h]

/-- An inline body. -/
def inlineBody (lex : Lexicon) (env : Env) (inl : List Stmt) : EM (Except Diagnostic Out) := do
  match ← (elabStmts lex env inl).run with
  | .ok (cs, _) => pure (.ok { stmts := cs })
  | .error e => pure (.error e)

mutual
/-- Elaborates a body: its sentences in order, threading the environment. Returns the core
statements, the claims found, and the environment after the last sentence. -/
def elabSents (lex : Lexicon) (env : Env) (prev : Prev) (out : Out) : List SSent → EM (Out × Env)
  | [] => pure (out, env)
  | s :: rest => do
    let (out', env', prev') ← elabSent lex env prev out s
    elabSents lex env' prev' out' rest

/-- List items: each starts with the body's topic (the loop element, in a loop), and
names declared in one item stay visible in the items after it. -/
def elabItems (lex : Lexicon) (env : Env) : List (List SSent) → EM (Out × Env)
  | [] => pure ({}, env)
  | it :: rest => do
    let (o1, env1) ← elabSents lex env .none {} it
    let (o2, env2) ← elabItems lex { env1 with topic := env.topic } rest
    pure ({ stmts := o1.stmts ++ o2.stmts, claims := o1.claims ++ o2.claims }, env2)

def elabSent (lex : Lexicon) (env : Env) (prev : Prev) (out : Out) : SSent → EM (Out × Env × Prev)
  | .skip names => do pure (out, ← skipEnv env names, .skipped)
  | .failed e names => do record e; pure (out, ← skipEnv env names, .skipped)
  | .lead w sp inner =>
    if env.names.any (·.name == w) then do
      record { code := "E013", span := sp, message := s!"a sentence may not start with the name \"{w}\"",
               fix := some { label := "start the sentence with its op or structure word" } }
      pure (out, ← skipEnv env [], .skipped)
    else elabSent lex env prev out inner
  | .stmts ss _ => do
    match ← (elabStmts lex env ss).run with
    | .ok (cs, env') => pure ({ out with stmts := out.stmts ++ cs }, env', .stmts cs.length)
    | .error e => do record e; pure (out, ← skipEnv env [], .skipped)
  | .claims cs _ => do
    match ← (cs.mapM (elabClaim lex env)).run with
    | .ok ccs => pure ({ out with claims := out.claims ++ ccs }, env, prev)
    | .error e => do record e; pure (out, env, prev)
  | .cond all tests inl items _ => do
    match ← (tests.mapM (elabTest lex env)).run with
    | .error e => do record e; pure (out, ← skipEnv { env with topic := none } [], .skipped)
    | .ok cts =>
      match ← (if items.isEmpty then inlineBody lex env inl else do let (o, _) ← elabItems lex env items; pure (.ok o)) with
      | .error e => do record e; pure (out, { env with topic := none }, .skipped)
      | .ok o =>
        pure ({ stmts := out.stmts ++ [.ite all cts o.stmts []], claims := out.claims ++ o.claims },
              { env with topic := none }, .cond env.topic)
  | .other inl items sp => do
    match prev with
    | .cond topic =>
      match ← (if items.isEmpty then inlineBody lex { env with topic } inl else do let (o, _) ← elabItems lex { env with topic } items; pure (.ok o)) with
      | .error e => do record e; pure (out, { env with topic := none }, .other)
      | .ok o => pure ({ stmts := attachElse out.stmts o.stmts, claims := out.claims ++ o.claims },
                       { env with topic := none }, .other)
    | .skipped => do
      let _ ← (if items.isEmpty then inlineBody lex env inl else do let (o, _) ← elabItems lex env items; pure (.ok o))
      pure (out, { env with topic := none }, .other)
    | _ => do
      record { code := "E028", span := sp, message := "`otherwise` must directly follow a conditional" }
      pure (out, { env with topic := none }, .skipped)
  | .handler inl items sp => do
    match prev with
    | .stmts n =>
      match ← (if items.isEmpty then inlineBody lex { env with topic := none } inl else do let (o, _) ← elabItems lex { env with topic := none } items; pure (.ok o)) with
      | .error e => do record e; pure (out, { env with topic := none }, .other)
      | .ok o => pure ({ stmts := attachHandler out.stmts n o.stmts, claims := out.claims ++ o.claims },
                       { env with topic := none }, .other)
    | .skipped => do
      let _ ← (if items.isEmpty then inlineBody lex { env with topic := none } inl else do let (o, _) ← elabItems lex { env with topic := none } items; pure (.ok o))
      pure (out, { env with topic := none }, .other)
    | _ => do
      record { code := "E028", span := sp, message := "`If it fails` must directly follow a statement sentence" }
      pure (out, { env with topic := none }, .skipped)
  | .each s coll inl items sp => do
    let r ← (do
      let parts := coll.atoms.map stripQuals
      let atoms ← parts.mapM fun p => resolveAtom lex env p.2
      match atoms with
      | [.typed cv t] =>
        recordQuals (parts.flatMap (·.1)) cv
        if t.sort == "?" || (t.sort == s.name && t.list) then pure cv
        else err "E030" coll.span s!"for each {s.name} needs a list of {s.name}, not {t.show}"
      | _ => err "E030" coll.span s!"for each {s.name} needs a list of {s.name}" : EE CVal).run
    match r with
    | .error e => do record e; pure (out, ← skipEnv { env with topic := none } [], .skipped)
    | .ok cv => do
      let st ← get
      set { st with next := st.next + 1 }
      let elem : Bind := ⟨"", st.next, ⟨s.name, false⟩, s!"the current {s.name} of the loop on line {sp.line}"⟩
      match ← (if items.isEmpty then inlineBody lex { env with elems := env.elems ++ [elem], topic := some elem } inl else do let (o, _) ← elabItems lex { env with elems := env.elems ++ [elem], topic := some elem } items; pure (.ok o)) with
      | .error e => do record e; pure (out, { env with topic := none }, .other)
      | .ok o => pure ({ stmts := out.stmts ++ [.loop elem.id cv o.stmts], claims := out.claims ++ o.claims },
                       { env with topic := none }, .other)
end

def elabSection (lex : Lexicon) (name : String) (ss : List SSent)
    (templates : List (String × Template) := []) :
    CSection × List Diagnostic × List (Span × String) :=
  let ((out, _), st) := (elabSents lex { templates } .none {} ss).run {}
  ({ name, stmts := out.stmts, claims := out.claims, quals := st.quals }, st.diags, st.refs)

/-- Elaborates a composite op's body section once, its parameters bound as names to
placeholder ids `0, 1, …`. -/
def buildTemplate (lex : Lexicon) (o : OpDef) (b : CompositeBody) : Except String Template := do
  let doc := readDoc b.source
  let some sec := doc.sections.find? (·.name == b.sectionName)
    | throw s!"no section \"{b.sectionName}\" in {b.file}"
  let (tsents, tds) := tokSents lex sec.sents
  let firstErr (ds : List Diagnostic) : Except String Unit :=
    match ds.find? Diagnostic.isError with
    | some d => throw s!"{b.file}:{d.span.line}: {d.code} {d.message}"
    | none => pure ()
  firstErr (doc.diags ++ tds)
  let (ss, pds) := parseSents tsents
  firstErr pds
  let params := b.params.zipIdx.map fun ((label, nm), i) =>
    let sorts := if label == "object" then o.object else (o.labels.lookup label).getD []
    let ty := match sorts.findSome? lex.paramSort? with
      | some (s, pl) => (⟨s.name, pl⟩ : Ty)
      | none => wildcard
    (if label == "object" then "" else label, (⟨nm, i, ty, s!"the {nm} parameter of `{o.base}`"⟩ : Bind))
  let ((out, _), st) := (elabSents lex { names := params.map (·.2) } .none {} ss).run { next := params.length }
  firstErr st.diags
  pure ⟨params.map fun (l, bd) => (l, bd.id), out.stmts, st.next⟩

end Lrep
