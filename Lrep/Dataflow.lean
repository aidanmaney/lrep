/-
The dataflow view (`lrep dataflow FILE`): a Graphviz graph of which values feed which
statements. Solid edges carry values, labelled by argument; dashed edges show which
statements a condition or loop controls.
-/
import Lrep

namespace Lrep

private def dotEscape (s : String) : String := (s.replace "\\" "\\\\").replace "\"" "\\\""

structure DotState where
  next : Nat := 0
  lines : List String := []

abbrev DotM := StateM DotState

private def emit (l : String) : DotM Unit := modify fun s => { s with lines := s.lines ++ [l] }

private def freshNode (sec : Nat) : DotM String := do
  let s ← get
  set { s with next := s.next + 1 }
  pure s!"v{sec}_{s.next}"

private def valNode (sec : Nat) (label : String) : DotM String := do
  let n ← freshNode sec
  emit s!"    {n} [label=\"{dotEscape label}\", shape=plaintext];"
  pure n

/-- Edges into `target` from the sources of a value. -/
def valueEdges (sec : Nat) (target : String) (label : String) : CVal → DotM Unit
  | .lit _ _ text _ => do let n ← valNode sec text; emit s!"    {n} -> {target} [label=\"{dotEscape label}\"];"
  | .qty n _ _ u _ => do let v ← valNode sec s!"{n} {u}"; emit s!"    {v} -> {target} [label=\"{dotEscape label}\"];"
  | .const c _ => do let v ← valNode sec (c.forms.headD c.sort); emit s!"    {v} -> {target} [label=\"{dotEscape label}\"];"
  | .ref id _ => emit s!"    b{sec}_{id} -> {target} [label=\"{dotEscape label}\"];"
  | .list vs => vs.attach.forM fun ⟨v, _⟩ => valueEdges sec target label v
  | .unknown => do let v ← valNode sec "?"; emit s!"    {v} -> {target} [label=\"{dotEscape label}\"];"

private def argLabel (l : String) : String := if l.isEmpty then "object" else l

mutual
/-- Emits a statement's node and edges; returns the node names it starts, for control edges. -/
def dotStmt (sec : Nat) : CStmt → DotM (List String)
  | .call id op args site => do
    let n := s!"b{sec}_{id}"
    emit s!"    {n} [label=\"{dotEscape op.base}\\nline {site.line}\", shape=box];"
    for a in args do valueEdges sec n (argLabel a.label) a.val
    pure [n]
  | .ite all tests thn els => do
    let c ← freshNode sec
    let preds := tests.map fun t => s!"{if t.neg then "not " else ""}{t.pred.forms.headD ""}"
    let line := (tests.head?.map (·.site.line)).getD 0
    emit s!"    {c} [label=\"if {dotEscape ((if all then " and " else " or ").intercalate preds)}\\nline {line}\", shape=diamond];"
    for t in tests do
      for a in t.args do valueEdges sec c (if a.label.isEmpty then "subject" else a.label) a.val
    let a ← dotStmts sec thn
    let b ← dotStmts sec els
    for x in a do emit s!"    {c} -> {x} [style=dashed, label=\"then\"];"
    for x in b do emit s!"    {c} -> {x} [style=dashed, label=\"otherwise\"];"
    pure [c]
  | .loop elem coll body => do
    let n := s!"b{sec}_{elem}"
    emit s!"    {n} [label=\"for each\", shape=ellipse];"
    valueEdges sec n "in" coll
    let xs ← dotStmts sec body
    for x in xs do emit s!"    {n} -> {x} [style=dashed, label=\"each\"];"
    pure [n]
  | .try body h => do
    let a ← dotStmts sec body
    let b ← dotStmts sec h
    for x in a do
      for y in b do emit s!"    {x} -> {y} [style=dashed, label=\"if it fails\"];"
    pure a

def dotStmts (sec : Nat) : List CStmt → DotM (List String)
  | [] => pure []
  | s :: rest => do
    let a ← dotStmt sec s
    let b ← dotStmts sec rest
    pure (a ++ b)
end

def FileResult.dataflow (r : FileResult) : String :=
  let body : DotM Unit := do
    for (s, i) in r.cores.zipIdx do
      emit s!"  subgraph cluster_{i} \{"
      emit s!"    label=\"{dotEscape s.name}\";"
      let _ ← dotStmts i s.stmts
      emit "  }"
  let ((), st) := body.run {}
  "\n".intercalate (["digraph lrep {", "  rankdir=LR;", "  node [fontname=\"Helvetica\"];"] ++ st.lines ++ ["}"]) ++ "\n"

end Lrep
