/-
The core view (`lrep core FILE`): each section as the core program the checker elaborates it
into. Every value is a numbered binding (`v3`), every argument is labelled, conditions are
predicate calls, and a composite op's body appears inlined after its call.
-/
import Lrep
import Lrep.Server

namespace Lrep

/-- Renumbers values `v0, v1, …` in the order the program binds them, so ids an inlined
body skips leave no gaps. -/
abbrev Renum := List (Nat × Nat)

private def vname (rn : Renum) (id : Nat) : String := s!"v{(rn.lookup id).getD id}"

def coreVal (rn : Renum) : CVal → String
  | .lit s _ text _ => if s.name.isEmpty then text else s!"{s.name} {text}"
  | .qty n _ _ u _ => s!"{n} {u}"
  | .const c _ => c.forms.headD c.sort
  | .ref id _ => vname rn id
  | .list vs => "[" ++ ", ".intercalate (vs.attach.map fun ⟨v, _⟩ => coreVal rn v) ++ "]"
  | .unknown => "?"

private def coreArgs (rn : Renum) (args : List CArg) : String :=
  ", ".intercalate (args.map fun a => if a.label.isEmpty then coreVal rn a.val else s!"{a.label}: {coreVal rn a.val}")

private def coreTest (rn : Renum) (t : CTest) : String :=
  s!"{if t.neg then "not " else ""}{t.pred.forms.headD ""}({coreArgs rn t.args})"

mutual
/-- The ids a statement binds, in order. -/
def boundStmt : CStmt → List Nat
  | .call id op _ _ => if op.returns.isSome then [id] else []
  | .ite _ _ thn els => boundStmts thn ++ boundStmts els
  | .loop elem _ body => elem :: boundStmts body
  | .try body h => boundStmts body ++ boundStmts h

def boundStmts : List CStmt → List Nat
  | [] => []
  | s :: rest => boundStmt s ++ boundStmts rest
end

mutual
def coreStmt (bl : List (String × Nat)) (rn : Renum) (ind : String) : CStmt → List String
  | .call id op args _ =>
    let call := s!"{op.base}({coreArgs rn args})"
    let line := if op.returns.isSome then s!"{vname rn id} := {call}" else call
    [ind ++ line ++ (if op.body.isSome then "    -- defined in lrep; its body:" else "")]
  | .ite all tests thn els =>
    let c := (if all then " and " else " or ").intercalate (tests.map (coreTest rn))
    [ind ++ s!"if {c} then"] ++ coreStmts bl rn (ind ++ "  ") 0 thn ++
      (if els.isEmpty then [] else [ind ++ "else"] ++ coreStmts bl rn (ind ++ "  ") 0 els) ++ [ind ++ "end"]
  | .loop elem coll body =>
    [ind ++ s!"for {vname rn elem} in {coreVal rn coll} do"] ++ coreStmts bl rn (ind ++ "  ") 0 body ++ [ind ++ "end"]
  | .try body h =>
    [ind ++ "try"] ++ coreStmts bl rn (ind ++ "  ") 0 body ++ [ind ++ "on failure"] ++
      coreStmts bl rn (ind ++ "  ") 0 h ++ [ind ++ "end"]

/-- `inBody` counts the statements still to come of the composite body being printed:
the elaborator places a body right after its call, so those statements are indented under it. -/
def coreStmts (bl : List (String × Nat)) (rn : Renum) (ind : String) (inBody : Nat) : List CStmt → List String
  | [] => []
  | s :: rest =>
    let here := coreStmt bl rn (if inBody > 0 then ind ++ "  " else ind) s
    let next := match s with
      | .call _ op _ _ => if op.body.isSome then (bl.lookup op.base).getD 0 else inBody - 1
      | _ => inBody - 1
    here ++ coreStmts bl rn ind next rest
end

private def coreClaim (rn : Renum) (c : CClaim) : String :=
  let target := match c.op.names with
    | some k => k
    | none => s!"{c.op.base} calls"
  let args := if c.args.isEmpty then "" else s!" ({coreArgs rn c.args})"
  if c.word == "at most" then s!"claim at most {c.count} {target}"
  else s!"claim {c.word} {target}{args}"

def FileResult.coreText (r : FileResult) : String :=
  "\n\n".intercalate (r.cores.map fun s =>
    let rn := (boundStmts s.stmts).zipIdx
    "\n".intercalate ([s!"section \"{s.name}\""] ++ coreStmts r.bodyLens rn "  " 0 s.stmts ++
      s.quals.map (fun q => s!"  check {q.q.forms.headD ""}({coreVal rn q.val})") ++
      s.claims.map (fun c => "  " ++ coreClaim rn c))) ++ "\n"

/-! ## Permissions

`lrep permissions FILE` is what an install prompt would show: for each section (one command),
the promises it makes and whether each is proved or only checked, everything it may touch, and
the pure ops it computes with.
-/

private def placePhrase (r : Res) : String :=
  match r with
  | .path segs true => s!"anything under {pathString segs}"
  | .url sc h segs => s!"{sc}://{h}{if segs.isEmpty then "" else pathString segs}"
  | .top => "anything at all"
  | _ => plainRes r

private def mayVerb : Kind → String
  | .read => "read" | .write => "write to" | .delete => "delete" | .listen => "listen on"
  | .connect => "connect to" | .spawn => "run"

mutual
private def pureOps : CStmt → List String
  | .call _ op _ _ => if op.effects.isEmpty && op.body.isNone then [op.base] else []
  | .ite _ _ thn els => pureOpsList thn ++ pureOpsList els
  | .loop _ _ body => pureOpsList body
  | .try body h => pureOpsList body ++ pureOpsList h
private def pureOpsList : List CStmt → List String
  | [] => []
  | s :: rest => pureOps s ++ pureOpsList rest
end

def FileResult.permissionsText (r : FileResult) : String :=
  let blocks := (r.sections.zip r.cores).map fun (s, core) =>
    let promises := s.verdicts.map fun v =>
      let flow := (v.claim.op.contentsLabel.map fun l => v.claim.args.any (·.label == l)).getD false
      let proved := (v.claim.word == "never" || v.claim.word == "only") && !flow
      s!"    {if v.holds then "✓" else "✗"} {v.claim.text}  ({if !v.holds then "broken" else if proved then "proved" else "checked"})"
    let kinds := [Kind.read, .write, .delete, .listen, .connect, .spawn]
    let may := kinds.flatMap fun k =>
      ((s.effects.filter (·.kind == k)).map (placePhrase ·.res)).eraseDups.map (s!"    {mayVerb k} " ++ ·)
    let pure := (pureOpsList core.stmts).eraseDups
    let broken := s.verdicts.any (!·.holds)
    [s!"{s.name}"] ++
      (if s.verdicts.isEmpty then ["  Promises: none"] else ["  Promises:"] ++ promises) ++
      (if may.isEmpty then ["  May: nothing"] else ["  May:"] ++ may) ++
      (if pure.isEmpty then [] else [s!"  Computes with (touches nothing): {", ".intercalate pure}"]) ++
      (if broken then ["  ! This command breaks its own promises. Don't install it."] else [])
  "\n\n".intercalate (blocks.map ("\n".intercalate ·)) ++ "\n"

end Lrep
