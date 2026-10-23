/-
Claim diffs (`lrep diff OLD NEW`): adding, weakening or removing a claim is its own event in
review. Quietly dropping "never deletes" is exactly what review exists to catch.
-/
import Lrep

namespace Lrep

inductive Change where
  | added (v : Verdict)
  | removed (v : Verdict)
  | weakened (old new : Verdict)
  | strengthened (old new : Verdict)
  /-- The claim is unchanged, but whether it holds changed. -/
  | verdict (old new : Verdict)

/-- Whether every resource in `as` lies within some resource of `bs`. -/
private def within (as bs : List Res) : Bool := as.all fun a => bs.any (covers · a)

/-- Whether `new` says less than `old` about the same op. An empty resource list means
anything. -/
def weaker (old new : Verdict) : Bool :=
  let ro := old.claimRes
  let rn := new.claimRes
  match old.claim.word with
  -- Fewer forbidden resources, or a narrower scope, is weaker.
  | "never" => !rn.isEmpty && (ro.isEmpty || !within ro rn)
  -- More allowed resources is weaker.
  | "only" => !within rn ro
  -- A broader target, or any target at all, is easier to perform.
  | "always" => !ro.isEmpty && (rn.isEmpty || !within rn ro)
  | "at most" => new.claim.count > old.claim.count
  | _ => false

private def key (v : Verdict) : String × String := (v.claim.word, v.claim.op.base)

/-- The changes between two versions of one section's claims. Claims match by text; a
removed and an added claim with the same word and op pair up as weakened or strengthened. -/
def diffClaims (old new : List Verdict) : List Change :=
  let removed := old.filter fun o => !new.any (·.claim.text == o.claim.text)
  let added := new.filter fun n => !old.any (·.claim.text == n.claim.text)
  let same := old.filterMap fun o => (new.find? (·.claim.text == o.claim.text)).map (o, ·)
  let (paired, unpairedOld) := removed.foldl (init := (([] : List (Verdict × Verdict)), ([] : List Verdict)))
    fun (ps, us) o =>
      match added.find? fun n => key n == key o && !ps.any (·.2.claim.text == n.claim.text) with
      | some n => (ps ++ [(o, n)], us)
      | none => (ps, us ++ [o])
  let unpairedNew := added.filter fun n => !paired.any (·.2.claim.text == n.claim.text)
  unpairedOld.map .removed ++
  paired.map (fun (o, n) => if weaker o n then .weakened o n else .strengthened o n) ++
  unpairedNew.map .added ++
  (same.filter fun (o, n) => o.holds != n.holds).map fun (o, n) => .verdict o n

def Change.flagged : Change → Bool
  | .removed _ | .weakened _ _ => true
  | _ => false

private def status (v : Verdict) : String := if v.holds then "holds" else "fails"

def Change.text : Change → String
  | .added v => s!"+ added: {v.claim.text} ({status v})"
  | .removed v => s!"- removed: {v.claim.text}"
  | .weakened o n => s!"~ weakened: {o.claim.text} → {n.claim.text}"
  | .strengthened o n => s!"~ strengthened: {o.claim.text} → {n.claim.text}"
  | .verdict o n => s!"! {n.claim.text}: {status o} → {status n}"

def Change.toJ : Change → J
  | .added v => .obj [("change", .str "added"), ("claim", .str v.claim.text), ("holds", .bool v.holds)]
  | .removed v => .obj [("change", .str "removed"), ("claim", .str v.claim.text)]
  | .weakened o n => .obj [("change", .str "weakened"), ("old", .str o.claim.text), ("new", .str n.claim.text)]
  | .strengthened o n => .obj [("change", .str "strengthened"), ("old", .str o.claim.text), ("new", .str n.claim.text)]
  | .verdict o n => .obj [("change", .str "verdict"), ("claim", .str n.claim.text),
                          ("old", .bool o.holds), ("new", .bool n.holds)]

/-- Changes per section, sections matched by name; a whole section added or removed brings
all its claims with it. -/
def diffFiles (old new : FileResult) : List (String × List Change) :=
  let names := (old.sections.map (·.name) ++ new.sections.map (·.name)).eraseDups
  names.filterMap fun n =>
    let o := ((old.sections.find? (·.name == n)).map (·.verdicts)).getD []
    let nw := ((new.sections.find? (·.name == n)).map (·.verdicts)).getD []
    let cs := diffClaims o nw
    if cs.isEmpty then none else some (n, cs)

/-! ## Vocabulary diffs

Qualifier definitions and op effects are the trust base: changing them changes what every
program's checks mean. `lrep vocab-diff` reports each change, and flags those that weaken a
guarantee, as a weakened claim is flagged.
-/

structure VocabChange where
  /-- Whether the change weakens a guarantee and needs a reviewer's attention. -/
  flagged : Bool
  text : String

private def regionsWithin (as bs : List String) : Bool :=
  as.all fun a => match regionRes a with
    | some ra => bs.any fun b => match regionRes b with | some rb => covers rb ra | none => false
    | none => false

private def regionChanges (word what : String) (old new : List String) : List VocabChange :=
  if old == new then []
  else if old.isEmpty then [⟨false, s!"\"{word}\" now constrains {what}: {new}"⟩]
  else if new.isEmpty then [⟨true, s!"\"{word}\" no longer constrains {what} (was {old})"⟩]
  else
    let widened := !regionsWithin new old
    let narrowed := !regionsWithin old new
    (if widened then [⟨true, s!"\"{word}\" {what} widened: {old} → {new}"⟩] else []) ++
    (if narrowed && !widened then [⟨false, s!"\"{word}\" {what} narrowed: {old} → {new}"⟩] else [])

private def declKey (d : EffDecl) : String :=
  d.kind ++ " " ++ match d.on with
    | .object => "object" | .subject => "subject" | .label l => s!"label:{l}" | .top => "top"

def diffVocabs (old new : Vocab) : List VocabChange :=
  let key (q : QualDef) := q.forms.headD ""
  let quals := old.qualifiers.flatMap fun o =>
    match new.qualifiers.find? (key · == key o) with
    | none => [⟨true, s!"qualifier \"{key o}\" removed: descriptions using it are now unchecked gloss"⟩]
    | some n => regionChanges (key o) "location" o.within n.within ++ regionChanges (key o) "origin" o.origins n.origins
  let addedQuals := new.qualifiers.filter (fun n => !old.qualifiers.any (key · == key n)) |>.map fun n =>
    (⟨false, s!"qualifier \"{key n}\" added"⟩ : VocabChange)
  let sameP (a b : String × String) := a == b || a == (b.2, b.1)
  let disjoint := (old.disjoint.filter fun p => !new.disjoint.any (sameP p)).map (fun (a, b) =>
      (⟨true, s!"\"{a}\" and \"{b}\" no longer exclude each other"⟩ : VocabChange)) ++
    (new.disjoint.filter fun p => !old.disjoint.any (sameP p)).map fun (a, b) =>
      (⟨false, s!"\"{a}\" and \"{b}\" now exclude each other"⟩ : VocabChange)
  let ops := old.ops.flatMap fun o =>
    match new.ops.find? (·.base == o.base) with
    | none => [(⟨false, s!"op \"{o.base}\" removed"⟩ : VocabChange)]
    | some n =>
      let ok := o.effects.map declKey
      let nk := n.effects.map declKey
      (ok.filter (!nk.contains ·)).map (fun k =>
        (⟨true, s!"op \"{o.base}\" no longer declares {k}: claims it used to fail may now pass"⟩ : VocabChange)) ++
      (nk.filter (!ok.contains ·)).map fun k =>
        (⟨false, s!"op \"{o.base}\" now declares {k}: claims that held may now fail"⟩ : VocabChange)
  let addedOps := new.ops.filter (fun n => !old.ops.any (·.base == n.base)) |>.map fun n =>
    (⟨false, s!"op \"{n.base}\" added"⟩ : VocabChange)
  quals ++ addedQuals ++ disjoint ++ ops ++ addedOps

end Lrep
