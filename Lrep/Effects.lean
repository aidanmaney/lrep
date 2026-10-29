/-
Effect inference and claim checking. Both are pure and total, and `Lrep/Sound.lean` proves
that if `check` accepts a claim, no execution of the core semantics performs an effect the
claim rules out.
-/
import Lrep.Elab

namespace Lrep

inductive Kind where
  | read | write | delete | listen | connect | spawn
  deriving DecidableEq, Repr, Inhabited

def Kind.ofString? : String → Option Kind
  | "read" => some .read | "write" => some .write | "delete" => some .delete
  | "listen" => some .listen | "connect" => some .connect | "spawn" => some .spawn
  | _ => none

def Kind.name : Kind → String
  | .read => "read" | .write => "write" | .delete => "delete"
  | .listen => "listen" | .connect => "connect" | .spawn => "spawn"

/-- How a witness message phrases the effect. -/
def Kind.verb : Kind → String
  | .read => "reads" | .write => "writes to" | .delete => "deletes"
  | .listen => "listens on" | .connect => "connects to" | .spawn => "runs"

inductive Res where
  /-- One file, or a directory and everything below it. -/
  | path (segs : List String) (isPrefix : Bool)
  /-- Always a prefix. -/
  | url (scheme host : String) (segs : List String)
  | host (scheme host : String)
  | port (n : Nat)
  | cmd (c : String)
  /-- Unknown: may be anything. -/
  | top
  deriving DecidableEq, Repr, Inhabited

/-- A resource with where it came from: the literal that named it, if any. -/
structure RVal where
  res : Res
  origin : Option Span := none
  text : Option String := none
  deriving Inhabited

structure Effect where
  kind : Kind
  res : Res
  /-- The statement or test that caused it. -/
  site : Span
  origin : Option Span := none
  text : Option String := none
  deriving Inhabited

/-- A call of a non-primitive op, for claims that name their calls. -/
structure Call where
  op : OpDef
  site : Span
  args : List (String × List RVal)
  deriving Inhabited

/-! ## Resources -/

def segPrefix : List String → List String → Bool
  | [], _ => true
  | a :: as, b :: bs => a == b && segPrefix as bs
  | _ :: _, [] => false

/-- `covers r s`: claim resource `r` contains effect resource `s`. Paths and URLs compare by
whole segments; `top` is covered by nothing. A URL with no path covers a host with the same
scheme and host. -/
def covers : Res → Res → Bool
  | .path a pa, .path b pb => if pa then segPrefix a b else (!pb && a == b)
  | .url sc h a, .url sc' h' b => sc == sc' && h == h' && segPrefix a b
  | .url sc h [], .host sc' h' => sc == sc' && h == h'
  | .host sc h, .host sc' h' => sc == sc' && h == h'
  | .port a, .port b => a == b
  | .cmd a, .cmd b => a == b
  | _, _ => false

/-- `overlaps r s`: some concrete resource may be described by both. Either side being `top`
overlaps everything: a claim naming an unknown value must not pass by accident, which the
soundness proof requires. -/
def overlaps (r s : Res) : Bool :=
  match r, s with
  | .top, _ | _, .top => true
  | _, _ => covers r s || covers s r

def Res.show : Res → String
  | .path segs _ => s!"\"{pathString segs}\""
  | .url sc h segs => s!"\"{sc}://{h}{if segs.isEmpty then "" else pathString segs}\""
  | .host sc h => if sc.isEmpty then s!"\"{h}\"" else s!"\"{sc}://{h}\""
  | .port n => s!"port {n}"
  | .cmd c => s!"\"{c}\""
  | .top => "an unknown resource"

/-- The JSON form: `top`, `port:443`, `path:/tmp/a.txt`, `path:/var/log/app/*` and so on. -/
def Res.key : Res → String
  | .path segs p => s!"path:{pathString segs}{if p then (if segs.isEmpty then "*" else "/*") else ""}"
  | .url sc h segs => s!"url:{sc}://{h}{pathString segs}{if segs.isEmpty then "*" else "/*"}"
  | .host sc h => if sc.isEmpty then s!"host:{h}" else s!"host:{sc}://{h}"
  | .port n => s!"port:{n}"
  | .cmd c => s!"command:{c}"
  | .top => "top"

def litRes (s : SortDef) (l : Lit) (text : String) (sp : Span) : List RVal :=
  let mk (r : Res) : List RVal := [{ res := r, origin := some sp, text := some text }]
  match s.resource, l with
  | .pathExact, .str p | .pathPrefix, .str p =>
    if isAbsolute p then
      match normPath p with
      | .ok segs => mk (.path segs (s.resource == .pathPrefix))
      | .error _ => mk .top
    else mk .top
  | .url, .str u =>
    match parseUrl u with
    | .ok ⟨sc, h, segs⟩ => mk (.url sc h segs)
    | .error _ => mk .top
  | .host, .str h =>
    match parseUrl h with
    | .ok ⟨sc, host, _⟩ => mk (.host sc host)
    | .error _ => mk (.host "" h)
  | .port, .int n => mk (.port n)
  | .command, .str c => mk (.cmd c)
  | .none, _ => []
  | _, _ => mk .top

def constRes (c : ConstDef) (sp : Span) : List RVal :=
  match c.resource with
  | .path p => match normPath p with
    | .ok segs => [{ res := .path segs true, origin := some sp }]
    | .error _ => [{ res := .top, origin := some sp }]
  | .url u => match parseUrl u with
    | .ok ⟨sc, h, segs⟩ => [{ res := .url sc h segs, origin := some sp }]
    | .error _ => [{ res := .top, origin := some sp }]
  | .host h => [{ res := .host "" h, origin := some sp }]
  | .port n => [{ res := .port n, origin := some sp }]
  | .none => []

abbrev REnv := List (Nat × List RVal)

/-- Every resource bound to `id`. Bodies bind each id once, so this is one binding's
resources; taking the union keeps inference sound without that assumption. -/
def lookupAll (env : REnv) (id : Nat) : List RVal :=
  env.flatMap fun (k, rs) => if k == id then rs else []

def valRes (env : REnv) : CVal → List RVal
  | .lit s l text sp => litRes s l text sp
  | .qty .. => []
  | .const c sp => constRes c sp
  | .ref id _ => lookupAll env id
  | .list vs => vs.attach.flatMap fun ⟨v, _⟩ => valRes env v
  | .unknown => [{ res := .top }]

/-! ## Inference -/

structure Inferred where
  effects : List Effect := []
  calls : List Call := []
  deriving Inhabited

def Inferred.append (a b : Inferred) : Inferred := ⟨a.effects ++ b.effects, a.calls ++ b.calls⟩

def argRes (env : REnv) (args : List CArg) (l : String) : List RVal :=
  args.filter (·.label == l) |>.flatMap fun a => valRes env a.val

/-- A connect effect on a URL uses its scheme and host. -/
def forKind (k : Kind) (r : RVal) : RVal :=
  match k, r.res with
  | .connect, .url sc h _ => { r with res := .host sc h }
  | _, _ => r

def declEffects (env : REnv) (decls : List EffDecl) (args : List CArg) (site : Span) : List Effect :=
  decls.flatMap fun d =>
    match Kind.ofString? d.kind with
    | none => []
    | some k =>
      let rs : List RVal := match d.on with
        | .object | .subject => argRes env args ""
        | .label l => argRes env args l
        | .top => [{ res := .top }]
      rs.map fun r =>
        let r := forKind k r
        { kind := k, res := r.res, site, origin := r.origin, text := r.text }

/-- The resources an op's result may touch, by its declared return resource. A result of an
in-memory sort touches nothing. -/
def hasResource (lex : Lexicon) (r : Returns) : Bool :=
  match lex.sort? r.sort with
  | some s => s.resource != .none
  | none => true

def resultRes (lex : Lexicon) (env : REnv) (op : OpDef) (args : List CArg) : List RVal :=
  match op.returns with
  | none => []
  | some r =>
    if hasResource lex r then
      match r.resource with
      | .sameObject => argRes env args ""
      | .sameLabel l => argRes env args l
      | .none => []
      | .top => [{ res := .top }]
    else []

mutual
def inferStmt (lex : Lexicon) (env : REnv) : CStmt → Inferred × REnv
  | .call id op args site =>
    let effs := declEffects env op.effects args site
    let result := resultRes lex env op args
    let call : List Call := if op.isPrimitive then [] else
      [⟨op, site, args.map fun a => (a.label, argRes env args a.label)⟩]
    (⟨effs, call⟩, (id, result) :: env)
  -- Bindings made inside a branch or loop body don't escape it.
  | .ite _ tests thn els =>
    let te : List Effect := tests.flatMap fun t => declEffects env t.pred.effects t.args t.site
    let a := (inferStmts lex env thn).1
    let b := (inferStmts lex env els).1
    (Inferred.append ⟨te, []⟩ (a.append b), env)
  | .loop elem coll body =>
    ((inferStmts lex ((elem, valRes env coll) :: env) body).1, env)
  | .try body h =>
    let (a, env1) := inferStmts lex env body
    let (b, env2) := inferStmts lex env1 h
    (a.append b, env2)

def inferStmts (lex : Lexicon) (env : REnv) : List CStmt → Inferred × REnv
  | [] => ({}, env)
  | s :: rest =>
    let (a, env1) := inferStmt lex env s
    let (b, env2) := inferStmts lex env1 rest
    (a.append b, env2)
end

/-- Every effect a section may perform, every branch and loop body included. -/
def infer (lex : Lexicon) (s : CSection) : Inferred × REnv := inferStmts lex [] s.stmts

/-! ## Claims -/

/-- Something a claim was checked against: an effect, or a call of the op it names. -/
structure Witness where
  site : Span
  res : Res
  origin : Option Span
  text : Option String
  verb : String
  deriving Inhabited

structure Verdict where
  claim : CClaim
  holds : Bool
  witnesses : List Witness
  /-- The resources the claim names, for fixes. -/
  claimRes : List Res
  deriving Inhabited

def claimArgRes (env : REnv) (c : CClaim) : List (String × List Res) :=
  c.args.map fun a => (a.label, (argRes env c.args a.label).map (·.res))

/-- Checks one claim against a section's inferred effects and calls. -/
def check (env : REnv) (inf : Inferred) (c : CClaim) : Verdict :=
  let rs := claimArgRes env c
  let allR := rs.flatMap (·.2)
  match c.op.names.bind Kind.ofString? with
  | some k =>
    let targets := inf.effects.filter (·.kind == k)
    let bad := targets.filter fun e =>
      if c.word == "never" then allR.isEmpty || allR.any (overlaps · e.res)
      else !allR.any (covers · e.res)
    ⟨c, bad.isEmpty, bad.map (fun e => ⟨e.site, e.res, e.origin, e.text, k.verb⟩), allR⟩
  | none =>
    let targets := inf.calls.filter (·.op.base == c.op.base)
    let verbFor (l : String) := c.op.form "s" ++ (if l.isEmpty then "" else " " ++ l)
    let bad : List Witness := targets.flatMap fun t =>
      if c.word == "never" && rs.isEmpty then
        [⟨t.site, .top, none, some "", c.op.form "s"⟩]
      else
        rs.flatMap fun (l, claimRs) =>
          let callRs := (t.args.lookup l).getD []
          (callRs.filter fun r =>
            if c.word == "never" then claimRs.any (overlaps · r.res)
            else !claimRs.any (covers · r.res)).map fun r => ⟨t.site, r.res, r.origin, r.text, verbFor l⟩
    ⟨c, bad.isEmpty, bad, allR⟩

/-! ## Path claims: `always` and `at most`

`always` holds when every complete path (one where no op fails) surely performs the target;
`at most n` holds when no path may perform it more than `n` times. Both walk the finite
control-flow graph. A loop's collection may have any size, so a loop that may perform the
target makes `at most` unbounded, and a loop never guarantees `always`.
-/

/-- One statement's match against a claim: whether it may perform the target (counted by
`at most`) and whether it surely does when it succeeds (needed by `always`). -/
structure Match where
  may : Bool
  sure : Bool

private def effMatch (k : Kind) (allR : List Res) (effs : List Effect) : Match :=
  let es := effs.filter (·.kind == k)
  { may := if allR.isEmpty then !es.isEmpty else es.any fun e => allR.any (overlaps · e.res)
    sure := !es.isEmpty && (allR.isEmpty || es.all fun e => allR.any (covers · e.res)) }

private def callMatch (c : CClaim) (claimRs : List (String × List Res)) (op : OpDef)
    (argRs : String → List RVal) : Match :=
  if op.isPrimitive || op.base != c.op.base then ⟨false, false⟩
  else
    { may := claimRs.all fun (l, rs) => rs.isEmpty || (argRs l).any fun r => rs.any (overlaps · r.res)
      sure := claimRs.all fun (l, rs) => !(argRs l).isEmpty && (argRs l).all fun r => rs.any (covers · r.res) }

/-- The most times a path may perform the target (`none`: unbounded), whether every
complete path surely performs it, and the statements that may. -/
structure PathInfo where
  most : Option Nat := some 0
  must : Bool := false
  sites : List Span := []

private def addMost : Option Nat → Option Nat → Option Nat
  | some a, some b => some (a + b)
  | _, _ => none

private def maxMost : Option Nat → Option Nat → Option Nat
  | some a, some b => some (max a b)
  | _, _ => none

def PathInfo.seq (a b : PathInfo) : PathInfo :=
  ⟨addMost a.most b.most, a.must || b.must, a.sites ++ b.sites⟩

mutual
def pathStmt (lex : Lexicon) (c : CClaim) (claimRs : List (String × List Res)) (env : REnv) :
    CStmt → PathInfo × REnv
  | .call id op args site =>
    let m := match c.op.names.bind Kind.ofString? with
      | some k => effMatch k (claimRs.flatMap Prod.snd) (declEffects env op.effects args site)
      | none => callMatch c claimRs op (argRes env args)
    (⟨some (if m.may then 1 else 0), m.sure, if m.may then [site] else []⟩,
     (id, resultRes lex env op args) :: env)
  | .ite _ tests thn els =>
    let testMay : List Span := match c.op.names.bind Kind.ofString? with
      | some k => tests.filterMap fun t =>
          if (effMatch k (claimRs.flatMap Prod.snd) (declEffects env t.pred.effects t.args t.site)).may
          then some t.site else none
      | none => []
    let a := (pathStmts lex c claimRs env thn).1
    let b := (pathStmts lex c claimRs env els).1
    (⟨addMost (some testMay.length) (maxMost a.most b.most), a.must && b.must,
      testMay ++ a.sites ++ b.sites⟩, env)
  | .loop elem coll body =>
    let a := (pathStmts lex c claimRs ((elem, valRes env coll) :: env) body).1
    (⟨if a.most == some 0 then some 0 else none, false, a.sites⟩, env)
  | .try body h =>
    let (a, env1) := pathStmts lex c claimRs env body
    let (b, env2) := pathStmts lex c claimRs env1 h
    -- The success path skips the handler; a failure path runs part of the body, then it.
    (⟨addMost a.most b.most, a.must && b.must, a.sites ++ b.sites⟩, env2)

def pathStmts (lex : Lexicon) (c : CClaim) (claimRs : List (String × List Res)) (env : REnv) :
    List CStmt → PathInfo × REnv
  | [] => ({}, env)
  | s :: rest =>
    let (a, env1) := pathStmt lex c claimRs env s
    let (b, env2) := pathStmts lex c claimRs env1 rest
    (a.seq b, env2)
end

/-- Checks an `always` or `at most` claim against a section's statements. -/
def checkPath (lex : Lexicon) (env : REnv) (stmts : List CStmt) (c : CClaim) : Verdict :=
  let rs := claimArgRes env c
  let info := (pathStmts lex c rs [] stmts).1
  let verb := c.op.form "s"
  let wit (sp : Span) : Witness := ⟨sp, .top, none, some "", verb⟩
  if c.word == "always" then
    ⟨c, info.must, if info.must then [] else info.sites.map wit, rs.flatMap (·.2)⟩
  else
    let ok := match info.most with | some n => n ≤ c.count | none => false
    ⟨c, ok, if ok then [] else info.sites.map wit, rs.flatMap (·.2)⟩

/-! ## Qualifiers

A qualifier is a descriptive word with a checked meaning: where a value lies (`within`),
where its contents came from (`from`), and which other qualifiers it excludes (`disjoint`).
Checking one is a `covers` test, the same as an `only` claim's.
-/

/-- A qualifier region: a URL prefix when it has a scheme, else an absolute path prefix. -/
def regionRes (r : String) : Option Res :=
  if hasScheme r then (parseUrl r).toOption.map fun u => .url u.scheme u.host u.segs
  else (normPath r).toOption.map (.path · true)

/-- Where a value's contents came from: a literal or constant's own resource, a binding's
recorded origins, anything for an unknown value. -/
def originRes (orig : REnv) : CVal → List RVal
  | .lit s l text sp => litRes s l text sp
  | .qty .. => []
  | .const c sp => constRes c sp
  | .ref id _ => lookupAll orig id
  | .list vs => vs.attach.flatMap fun ⟨v, _⟩ => originRes orig v
  | .unknown => [{ res := .top }]

mutual
/-- Every binding a section makes, branch and loop bodies included: each id's location
(as inference computes it) and its origins. A result's contents come from its object,
and from anywhere when its op may touch anything. -/
def bindStmt (lex : Lexicon) (envs : REnv × REnv) : CStmt → REnv × REnv
  | .call id op args _ =>
    let (loc, orig) := envs
    let fromObj := args.filter (·.label == "") |>.flatMap fun a => originRes orig a.val
    let anywhere := if op.effects.any (·.on == .top) then [({ res := .top } : RVal)] else []
    ((id, resultRes lex loc op args) :: loc, (id, fromObj ++ anywhere) :: orig)
  | .ite _ _ thn els => bindStmts lex (bindStmts lex envs thn) els
  | .loop elem coll body =>
    let (loc, orig) := envs
    bindStmts lex ((elem, valRes loc coll) :: loc, (elem, originRes orig coll) :: orig) body
  | .try body h => bindStmts lex (bindStmts lex envs body) h

def bindStmts (lex : Lexicon) (envs : REnv × REnv) : List CStmt → REnv × REnv
  | [] => envs
  | s :: rest => bindStmts lex (bindStmt lex envs s) rest
end

private def regionsText (rs : List String) : String := " or ".intercalate (rs.map fun r => s!"\"{r}\"")

private def describeRes (r : RVal) : String :=
  match r.res, r.text with
  | .top, some t => s!"{t}, a relative path"
  | .top, none => "an unknown resource"
  | res, _ => res.show

/-- Checks a qualifier use; returns the problem, if any. -/
def checkQual (lex : Lexicon) (loc orig : REnv) (cq : CQual) : Option Diagnostic :=
  let q := cq.q
  let word := q.forms.headD ""
  let locs := valRes loc cq.val
  let origs := originRes orig cq.val
  let inside (regions : List String) (r : RVal) : Bool :=
    regions.any fun w => match regionRes w with | some wr => covers wr r.res | none => false
  let err (m : String) : Option Diagnostic :=
    some { code := "E034", span := cq.span, message := m, fix := some { label := "use the qualifier that matches, or drop it" } }
  let location : Option Diagnostic :=
    if q.within.isEmpty then none
    else (locs.find? (!inside q.within ·)).bind fun r =>
      err s!"\"{word}\" describes {describeRes r}, which is not within {regionsText q.within}"
  location
  <|> (if q.origins.isEmpty then none else
    match origs.find? (!inside q.origins ·) with
    | some r => err s!"\"{word}\" describes a value whose contents come from {describeRes r}, not from {regionsText q.origins}"
    | none => none)
  <|> (lex.disjoint.filterMap fun (a, b) =>
      let other := if q.forms.contains a then some b else if q.forms.contains b then some a else none
      other.bind lex.qual?).findSome? fun o =>
    let oword := o.forms.headD ""
    if !o.within.isEmpty && locs.any (inside o.within) then
      err s!"\"{word}\" describes a value within {regionsText o.within}, which is {oword}; the two exclude each other"
    else if !o.origins.isEmpty && origs.any (inside o.origins) then
      err s!"\"{word}\" describes a value whose contents come from {regionsText o.origins}, which is {oword}; the two exclude each other"
    else none

/-- What a qualifier use describes, for hover: where the value lies, where its contents came
from, and whether the check holds. -/
def qualHover (lex : Lexicon) (loc orig : REnv) (cq : CQual) : String :=
  let word := cq.q.forms.headD ""
  -- `at` for a place a value lies; nothing before a source its contents come from.
  let one (lead : String) (r : RVal) : String := match r.res with
    | .path segs true => s!"somewhere under \"{pathString segs}\""
    | .top => describeRes r
    | _ => lead ++ describeRes r
  let fmt (rs : List RVal) : String := ", ".intercalate ((rs.map (one "at ")).eraseDups)
  let fmtFrom (rs : List RVal) : String := ", ".intercalate ((rs.map (one "")).eraseDups)
  let locs := valRes loc cq.val
  let origs := originRes orig cq.val
  let lies := if locs.isEmpty then "it is held in memory" else s!"it is {fmt locs}"
  let same := (origs.map (·.res)).eraseDups == (locs.map (·.res)).eraseDups
  let from_ := if origs.isEmpty || same then "" else s!"; its contents come from {fmtFrom origs}"
  let status := match checkQual lex loc orig cq with
    | none => "✓ the description holds"
    | some d => s!"✗ {d.message}"
  s!"`{word}` describes a value: {lies}{from_}.\n\n{status}"

/-- Hover text for each qualifier use in a section. -/
def qualHovers (lex : Lexicon) (s : CSection) : List (Span × String) :=
  let (loc, orig) := bindStmts lex ([], []) s.stmts
  s.quals.map fun cq => (cq.span, qualHover lex loc orig cq)

def checkQuals (lex : Lexicon) (s : CSection) : List Diagnostic :=
  let (loc, orig) := bindStmts lex ([], []) s.stmts
  s.quals.filterMap (checkQual lex loc orig)

/-! ## Data-flow claims

A claim that uses an op's contents label, as in `never posts from "/Journal"`, is about where
the posted data came from rather than where it goes. It's checked against each call's object
origins, from the same analysis as `from` qualifiers. The soundness proof doesn't cover it yet.
-/

mutual
/-- Every call of the op `base`, with where its object's contents came from. -/
def flowStmt (lex : Lexicon) (base : String) (envs : REnv × REnv) :
    CStmt → List (Span × List RVal) × (REnv × REnv)
  | .call id op args site =>
    let here := if op.base == base then
        [(site, args.filter (·.label == "") |>.flatMap fun a => originRes envs.2 a.val)]
      else []
    (here, bindStmt lex envs (.call id op args site))
  | .ite _ _ thn els =>
    let (a, e1) := flowStmts lex base envs thn
    let (b, e2) := flowStmts lex base e1 els
    (a ++ b, e2)
  | .loop elem coll body =>
    let (loc, orig) := envs
    flowStmts lex base ((elem, valRes loc coll) :: loc, (elem, originRes orig coll) :: orig) body
  | .try body h =>
    let (a, e1) := flowStmts lex base envs body
    let (b, e2) := flowStmts lex base e1 h
    (a ++ b, e2)

def flowStmts (lex : Lexicon) (base : String) (envs : REnv × REnv) :
    List CStmt → List (Span × List RVal) × (REnv × REnv)
  | [] => ([], envs)
  | s :: rest =>
    let (a, e1) := flowStmt lex base envs s
    let (b, e2) := flowStmts lex base e1 rest
    (a ++ b, e2)
end

/-- Checks a data-flow claim: `never` fails if any call's contents may come from a named
place; `only` fails if any may come from elsewhere. -/
def checkFlow (lex : Lexicon) (env : REnv) (stmts : List CStmt) (c : CClaim) (label : String) : Verdict :=
  let claimRs := (argRes env c.args label).map (·.res)
  let calls := (flowStmts lex c.op.base ([], []) stmts).1
  let verb := s!"{c.op.form "s"} {label}"
  let bad : List Witness := calls.flatMap fun (site, origs) =>
    let offending := origs.filter fun r =>
      if c.word == "never" then claimRs.any (overlaps · r.res) else !claimRs.any (covers · r.res)
    offending.map fun r => ⟨site, r.res, r.origin, r.text, verb⟩
  ⟨c, bad.isEmpty, bad, claimRs⟩

/-- Checks any claim: `never` and `only` against the inferred effects, or against data flow
when they use an op's contents label; `always` and `at most` against the paths. -/
def checkClaim (lex : Lexicon) (env : REnv) (inf : Inferred) (stmts : List CStmt) (c : CClaim) : Verdict :=
  match c.op.contentsLabel with
  | some l =>
    if c.args.any (·.label == l) then checkFlow lex env stmts c l
    else if c.word == "always" || c.word == "at most" then checkPath lex env stmts c else check env inf c
  | none =>
    if c.word == "always" || c.word == "at most" then checkPath lex env stmts c else check env inf c

end Lrep
