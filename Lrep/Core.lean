/-
The core view (`lrep core FILE`): each section as the core program the checker elaborates it
into. Every value is a numbered binding (`v3`), every argument is labelled, conditions are
predicate calls, and a composite op's body appears inlined after its call.
-/
import Lrep

namespace Lrep

def coreVal : CVal → String
  | .lit s _ text _ => if s.name.isEmpty then text else s!"{s.name} {text}"
  | .qty n _ _ u _ => s!"{n} {u}"
  | .const c _ => c.forms.headD c.sort
  | .ref id _ => s!"v{id}"
  | .list vs => "[" ++ ", ".intercalate (vs.attach.map fun ⟨v, _⟩ => coreVal v) ++ "]"
  | .unknown => "?"

private def coreArgs (args : List CArg) : String :=
  ", ".intercalate (args.map fun a => if a.label.isEmpty then coreVal a.val else s!"{a.label}: {coreVal a.val}")

private def coreTest (t : CTest) : String :=
  s!"{if t.neg then "not " else ""}{t.pred.forms.headD ""}({coreArgs t.args})"

mutual
def coreStmt (ind : String) : CStmt → List String
  | .call id op args _ =>
    let call := s!"{op.base}({coreArgs args})"
    let line := if op.returns.isSome then s!"v{id} := {call}" else call
    [ind ++ line ++ (if op.body.isSome then "    -- defined in lrep; its body follows" else "")]
  | .ite all tests thn els =>
    let c := (if all then " and " else " or ").intercalate (tests.map coreTest)
    [ind ++ s!"if {c} then"] ++ coreStmts (ind ++ "  ") thn ++
      (if els.isEmpty then [] else [ind ++ "else"] ++ coreStmts (ind ++ "  ") els) ++ [ind ++ "end"]
  | .loop elem coll body =>
    [ind ++ s!"for v{elem} in {coreVal coll} do"] ++ coreStmts (ind ++ "  ") body ++ [ind ++ "end"]
  | .try body h =>
    [ind ++ "try"] ++ coreStmts (ind ++ "  ") body ++ [ind ++ "on failure"] ++ coreStmts (ind ++ "  ") h ++ [ind ++ "end"]

def coreStmts (ind : String) : List CStmt → List String
  | [] => []
  | s :: rest => coreStmt ind s ++ coreStmts ind rest
end

private def coreClaim (c : CClaim) : String :=
  let target := match c.op.names with
    | some k => k
    | none => s!"{c.op.base} calls"
  let args := if c.args.isEmpty then "" else s!" ({coreArgs c.args})"
  if c.word == "at most" then s!"claim at most {c.count} {target}"
  else s!"claim {c.word} {target}{args}"

def FileResult.coreText (r : FileResult) : String :=
  "\n\n".intercalate (r.cores.map fun s =>
    "\n".intercalate ([s!"section \"{s.name}\""] ++ coreStmts "  " s.stmts ++
      s.quals.map (fun q => s!"  check {q.q.forms.headD ""}({coreVal q.val})") ++
      s.claims.map (fun c => "  " ++ coreClaim c))) ++ "\n"

end Lrep
