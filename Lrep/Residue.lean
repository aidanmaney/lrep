/-
The residue view: the program with gloss and asides dropped, rendered canonically.
-/
import Lrep.Token

namespace Lrep

private def capitalise (s : String) : String :=
  match s.toList with
  | c :: cs => String.ofList (c.toUpper :: cs)
  | [] => s

/-- A sentence's program tokens, single-spaced, commas attached to the token before. -/
def residueLine (toks : List Tok) (term : Char) : String :=
  let words := toks.filter Tok.isProgram
  let body := words.zipIdx.foldl (init := "") fun acc (t, i) =>
    let text := if i == 0 then capitalise t.text else t.text
    if t.isComma || acc.isEmpty then acc ++ text else acc ++ " " ++ text
  body.push term

mutual
def residueSent (indent : Nat) (prefix_ : String) : TSent → List String
  | .mk toks term _ _ sub =>
    (spaces indent ++ prefix_ ++ residueLine toks term) :: residueItems indent sub

/-- List items at `indent`; an item's later sentences line up under its first. -/
def residueItems (indent : Nat) : List (List TSent) → List String
  | [] => []
  | item :: rest => residueItem indent true item ++ residueItems indent rest

def residueItem (indent : Nat) (first : Bool) : List TSent → List String
  | [] => []
  | s :: rest =>
    match s with
    | .mk toks term _ _ sub =>
      let line := spaces indent ++ (if first then "- " else "  ") ++ residueLine toks term
      line :: residueItems (indent + 2) sub ++ residueItem indent false rest
end

def residueSents : List TSent → List String
  | [] => []
  | s :: rest => residueSent 0 "" s ++ residueSents rest

/-- Headings stay verbatim, with a blank line between sections. -/
def residue (secs : List TSection) (headingLines : List String) : String :=
  let blocks := (secs.zip headingLines).map fun (s, h) =>
    "\n".intercalate (h :: "" :: residueSents s.sents)
  "\n\n".intercalate blocks ++ "\n"

end Lrep
