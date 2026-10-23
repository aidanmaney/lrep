/-
The TextMate grammar emitter. Every class matches exactly, case-insensitively on word
boundaries, except names, which are approximate: a capitalised word that is not after a
full stop or at a line start.
-/
import Lrep.Lexicon
import Lrep.Words

namespace Lrep

/-- Escapes a word for an Oniguruma regex. -/
private def reEscape (w : String) : String :=
  w.toList.foldl (init := "") fun acc c =>
    if "\\^$.|?*+()[]{}".toList.contains c then acc.push '\\' |>.push c
    else if c == ' ' then acc ++ "\\s+"
    else acc.push c

private def alternation (ws : List String) : String :=
  -- Longer words first, so "opens" isn't cut to "open".
  let sorted := ws.eraseDups.mergeSort fun a b => a.length > b.length || (a.length == b.length && a ≤ b)
  "|".intercalate (sorted.map reEscape)

private def wordRule (scope : String) (ws : List String) : Option J :=
  if ws.isEmpty then none
  else some (.obj [("name", .str scope),
    ("match", .str s!"(?i)(?<![\\w'])(?:{alternation ws})(?![\\w'])")])

/-- The grammar. `calm` keeps only literals, asides, headings, claim words and forbidden
words, for editors where the language server's semantic tokens style the program words. -/
def grammar (lex : Lexicon) (calm : Bool := false) : J :=
  let ops := lex.ops.flatMap (·.forms.map (·.2))
  let preds := lex.predicates.flatMap (·.forms)
  let sorts := lex.sorts.flatMap (·.forms) ++ lex.units.flatMap (·.forms)
  let consts := lex.constants.flatMap (·.forms)
  let quals := lex.qualifiers.flatMap (·.forms)
  let L := lex.lang
  let phraseWords (c : String) := L.phrases.filter (·.2 == c) |>.map fun ((a, b), _) => a ++ " " ++ b
  let structure_ := (L.structureMap.filter (·.2 != "because")).map (·.1) ++ phraseWords "for each" ++
    phraseWords "this section" ++ L.labels
  let claims := L.claimMap.map (·.1) ++ phraseWords "at most"
  let forbidden := L.forbidden.map (·.1)
  let patterns : List J :=
    [.obj [("name", .str "markup.heading"), ("match", .str "^#{1,6} .*$")],
     .obj [("name", .str "comment.block"), ("begin", .str "\\("), ("end", .str "\\)")],
     .obj [("name", .str "comment.block"), ("begin", .str s!"(?i)(?<![\\w'])(?:{alternation L.asideWords})(?![\\w'])"),
           ("end", .str "(?=[.:](?:\\s|$))")],
     .obj [("name", .str "string.quoted.double"), ("match", .str "\"(?:\\\\[\"\\\\]|[^\"\\\\])*\"")],
     .obj [("name", .str "constant.numeric"), ("match", .str "\\b[0-9]+\\b")]] ++
    (if L.contractions then
      [.obj [("name", .str "invalid.illegal"), ("match", .str "(?i)(?<![\\w'])[a-z']*n't(?![\\w'])")]]
    else []) ++
    ((if calm then [wordRule "invalid.illegal" forbidden, wordRule "keyword.other.claim" claims] else
     [wordRule "invalid.illegal" forbidden,
      wordRule "keyword.other.claim" claims,
      wordRule "keyword.control" structure_,
      wordRule "entity.name.function" ops,
      wordRule "support.function" preds,
      wordRule "support.type" sorts,
      wordRule "support.constant" consts,
      wordRule "storage.modifier" quals]).filterMap id) ++
    (if calm then [] else
      [.obj [("name", .str "variable.other"), ("match", .str "(?<![.:]\\s)(?<!^)(?<![\\w'])[A-Z][\\w']*")]])
  .obj [("name", .str "lrep"), ("scopeName", .str "source.lrep"), ("fileTypes", .arr [.str "lrep"]),
        ("patterns", .arr patterns)]

end Lrep
