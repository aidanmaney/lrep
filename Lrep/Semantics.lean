/-
The core semantics, for the soundness proof in `Lrep/Sound.lean`.

Execution is a relation, not a function: ops are host code, so the semantics says only what
an op may do, given its declared effects. A run may take either branch of a conditional,
iterate a loop any number of times over any elements of its collection, and stop at any
point (an op that fails stops its body; a handler may then run). Every run the real runtime
can perform is one of these, so a claim that holds for all of them holds at runtime.
-/
import Lrep.Effects

namespace Lrep

/-- A concrete resource an effect touches at runtime. -/
inductive CRes where
  | path (segs : List String)
  | url (scheme host : String) (segs : List String)
  | host (scheme host : String)
  | port (n : Nat)
  | cmd (c : String)
  deriving DecidableEq, Repr

/-- `approx r c`: abstract resource `r` describes concrete resource `c`. A path prefix
describes everything below it; a URL describes everything below it, and its host when it
has no path; `top` describes anything. -/
def approx : Res → CRes → Prop
  | .top, _ => True
  | .path a true, .path c => segPrefix a c = true
  | .path a false, .path c => a = c
  | .url sc h a, .url sc' h' c => sc = sc' ∧ h = h' ∧ segPrefix a c = true
  | .url sc h a, .host sc' h' => sc = sc' ∧ h = h' ∧ a = []
  | .host sc h, .host sc' h' => sc = sc' ∧ h = h'
  | .port a, .port b => a = b
  | .cmd a, .cmd b => a = b
  | _, _ => False

/-- `approx` as a decision procedure, for the runtime's sandbox. `approxB_iff` proves the two
agree. -/
def approxB : Res → CRes → Bool
  | .top, _ => true
  | .path a true, .path c => segPrefix a c
  | .path a false, .path c => a == c
  | .url sc h a, .url sc' h' c => sc == sc' && h == h' && segPrefix a c
  | .url sc h a, .host sc' h' => sc == sc' && h == h' && a.isEmpty
  | .host sc h, .host sc' h' => sc == sc' && h == h'
  | .port a, .port b => a == b
  | .cmd a, .cmd b => a == b
  | _, _ => false

theorem approxB_iff (r : Res) (c : CRes) : approxB r c = true ↔ approx r c := by
  cases r with
  | path a p => cases p <;> cases c <;> simp [approxB, approx]
  | url sc h a => cases c <;> simp [approxB, approx, List.isEmpty_iff, and_assoc]
  | _ => cases c <;> simp [approxB, approx]

structure CEff where
  kind : Kind
  res : CRes

/-- What a run does: perform an effect, or call an op with these concrete arguments. -/
inductive Event where
  | eff (e : CEff)
  | call (op : OpDef) (args : String → List CRes)

/-- The concrete environment: each binding's concrete resources, newest first. -/
abbrev CEnv := List (Nat × List CRes)

/-- Values: a literal or constant denotes the resources its abstract meaning describes; a
reference denotes its binding; an unknown value may be anything. -/
inductive Eval (ρ : CEnv) : CVal → List CRes → Prop
  | lit {s l text sp cs} : (∀ c ∈ cs, ∃ r ∈ litRes s l text sp, approx r.res c) → Eval ρ (.lit s l text sp) cs
  | qty {n u k t sp} : Eval ρ (.qty n u k t sp) []
  | const {k sp cs} : (∀ c ∈ cs, ∃ r ∈ constRes k sp, approx r.res c) → Eval ρ (.const k sp) cs
  | ref {id sp} : Eval ρ (.ref id sp) ((ρ.lookup id).getD [])
  | list {vs} (f : CVal → List CRes) : (∀ v ∈ vs, Eval ρ v (f v)) → Eval ρ (.list vs) (vs.flatMap f)
  | unknown {cs} : Eval ρ .unknown cs

/-- The concrete resources of the arguments with label `l`. -/
def labelC (args : List CArg) (cargs : CArg → List CRes) (l : String) : List CRes :=
  (args.filter (·.label == l)).flatMap cargs

def targetC (args : String → List CRes) : Target → List CRes
  | .object | .subject => args ""
  | .label l => args l
  | .top => []

/-- A connect effect on a URL connects to its scheme and host. -/
def forKindC : Kind → CRes → CRes
  | .connect, .url sc h _ => .host sc h
  | _, c => c

/-- The assumption: an op performs only its declared effects, each on the resources of its
target argument (or anything, for a `top` target). -/
def Allowed (decls : List EffDecl) (args : String → List CRes) (e : CEff) : Prop :=
  ∃ d ∈ decls, Kind.ofString? d.kind = some e.kind ∧
    (d.on = .top ∨ ∃ c ∈ targetC args d.on, e.res = forKindC e.kind c)

/-- An op's result touches only what its declared return resource says. -/
def ResultOK (lex : Lexicon) (op : OpDef) (args : String → List CRes) (v : CRes) : Prop :=
  match op.returns with
  | none => False
  | some r =>
    hasResource lex r = true ∧
    match r.resource with
    | .sameObject => v ∈ args ""
    | .sameLabel l => v ∈ args l
    | .none => False
    | .top => True

/-- An event a condition's test may cause. -/
def TestEvent (ρ : CEnv) (t : CTest) : Event → Prop
  | .eff e => ∃ cargs : CArg → List CRes, (∀ a ∈ t.args, Eval ρ a.val (cargs a)) ∧
      Allowed t.pred.effects (labelC t.args cargs) e
  | .call _ _ => False

/-- Runs of a statement list: the events performed and the environment after. -/
inductive Run (lex : Lexicon) : CEnv → List CStmt → List Event → CEnv → Prop
  | nil {ρ} : Run lex ρ [] [] ρ
  /-- A run may stop at any point: an op failed. -/
  | stop {ρ ss} : Run lex ρ ss [] ρ
  | call {ρ id op args site rest t ρ'} (cargs : CArg → List CRes) (es : List CEff) (vs : List CRes) :
      (∀ a ∈ args, Eval ρ a.val (cargs a)) →
      (∀ e ∈ es, Allowed op.effects (labelC args cargs) e) →
      (∀ v ∈ vs, ResultOK lex op (labelC args cargs) v) →
      Run lex ((id, vs) :: ρ) rest t ρ' →
      Run lex ρ (.call id op args site :: rest) (es.map .eff ++ [.call op (labelC args cargs)] ++ t) ρ'
  | ite {ρ all tests thn els rest tt tb t ρb ρ'} (branch : List CStmt) :
      (∀ ev ∈ tt, ∃ x ∈ tests, TestEvent ρ x ev) →
      (branch = thn ∨ branch = els) →
      Run lex ρ branch tb ρb →
      Run lex ρ rest t ρ' →
      Run lex ρ (.ite all tests thn els :: rest) (tt ++ tb ++ t) ρ'
  /-- The loop has no iterations left. -/
  | loopDone {ρ elem coll body rest t ρ'} :
      Run lex ρ rest t ρ' →
      Run lex ρ (.loop elem coll body :: rest) t ρ'
  /-- One iteration, on an element whose resources come from the collection. -/
  | loopStep {ρ elem coll body rest cs es t1 ρ1 t2 ρ'} :
      Eval ρ coll cs →
      (∀ c ∈ es, c ∈ cs) →
      Run lex ((elem, es) :: ρ) body t1 ρ1 →
      Run lex ρ (.loop elem coll body :: rest) t2 ρ' →
      Run lex ρ (.loop elem coll body :: rest) (t1 ++ t2) ρ'
  | try {ρ body h rest t1 ρ1 t2 ρ2 t3 ρ'} :
      Run lex ρ body t1 ρ1 →
      Run lex ρ1 h t2 ρ2 →
      Run lex ρ2 rest t3 ρ' →
      Run lex ρ (.try body h :: rest) (t1 ++ t2 ++ t3) ρ'

/-! ## What a claim rules out -/

/-- `Violates env c ev`: event `ev` is one claim `c` rules out. A claim's resources mean
what they describe (`approx`). -/
def Violates (env : REnv) (c : CClaim) : Event → Prop
  | .eff e =>
    match c.op.names.bind Kind.ofString? with
    | some k =>
      let allR := (claimArgRes env c).flatMap (·.2)
      e.kind = k ∧
        if c.word = "never" then allR = [] ∨ ∃ r ∈ allR, approx r e.res
        else ¬ ∃ r ∈ allR, approx r e.res
    | none => False
  | .call op args =>
    match c.op.names.bind Kind.ofString? with
    | some _ => False
    | none =>
      let rs := claimArgRes env c
      op.isPrimitive = false ∧ op.base = c.op.base ∧
        if c.word = "never" then
          rs = [] ∨ ∃ p ∈ rs, ∃ x ∈ args p.1, ∃ r ∈ p.2, approx r x
        else ∃ p ∈ rs, ∃ x ∈ args p.1, ¬ ∃ r ∈ p.2, approx r x

end Lrep
