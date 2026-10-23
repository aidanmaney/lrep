/-
The language's closed word tables: structure words, labels, claim words,
articles and forbidden words.
All entries are lower case; classification ignores case.
-/
namespace Lrep.Words

/-- Two-word phrases, matched before anything else. -/
def phrases : List (String × String) :=
  [("for", "each"), ("at", "most"), ("this", "section")]

def structureWords : List String :=
  ["it", "them", "then", "and", "or", "if", "otherwise", "not", "is", "are", "as",
   "because", "fails"]

/-- Every preposition is an argument label. -/
def labels : List String :=
  ["about", "above", "across", "after", "against", "along", "among", "around", "at",
   "before", "behind", "below", "beneath", "beside", "between", "beyond", "by", "despite",
   "down", "during", "except", "for", "from", "in", "inside", "into", "like", "near", "of",
   "off", "on", "onto", "out", "outside", "over", "past", "per", "since", "than", "through",
   "throughout", "till", "to", "toward", "towards", "under", "until", "up", "upon", "via",
   "with", "within", "without"]

def claimWords : List String := ["never", "only", "always"]

def articles : List String := ["a", "an", "the"]

def numberWords : List (String × String) :=
  [("zero", "0"), ("one", "1"), ("two", "2"), ("three", "3"), ("four", "4"), ("five", "5"),
   ("six", "6"), ("seven", "7"), ("eight", "8"), ("nine", "9"), ("ten", "10"),
   ("eleven", "11"), ("twelve", "12"), ("thirteen", "13"), ("fourteen", "14"),
   ("fifteen", "15"), ("sixteen", "16"), ("seventeen", "17"), ("eighteen", "18"),
   ("nineteen", "19"), ("twenty", "20"), ("hundred", "100"), ("thousand", "1000"),
   ("million", "1000000"), ("billion", "1000000000")]

private def group (fix : String) (ws : List String) : List (String × String) :=
  ws.map (·, fix)

/-- Forbidden words with the fix each one offers. -/
def forbidden : List (String × String) :=
  group "use if … not" ["unless"] ++
  group "use never in claims and not in conditions"
    ["don't", "doesn't", "isn't", "can't", "won't", "aren't", "didn't", "wasn't", "weren't",
     "shouldn't", "couldn't", "wouldn't", "mustn't", "haven't", "hasn't", "hadn't"] ++
  group "drop the modal: statements are commands and claims are checked"
    ["may", "might", "can", "could", "should", "must", "will", "would", "do", "does", "did",
     "shall", "ought"] ++
  group "use the present tense: is, are" ["was", "were", "be", "been", "being", "am"] ++
  group "use the op's base form, or rewrite as a claim" ["have", "has", "had"] ++
  group "use then, a new sentence or an aside"
    ["but", "so", "while", "although", "yet", "though", "whereas", "nor"] ++
  group "use if" ["when", "whenever", "once", "whether"] ++
  group "use a label, a name or an aside" ["where", "wherever"] ++
  group "use it, them or a name"
    ["they", "he", "she", "we", "you", "i", "this", "that", "these", "those", "its", "their",
     "who", "whom", "whose", "which", "what", "whatever", "me", "my", "mine", "myself",
     "your", "yours", "him", "his", "her", "hers", "us", "our", "ours", "itself",
     "themselves", "theirs"] ++
  group "use for each or a claim"
    ["all", "every", "any", "some", "no", "both", "either", "neither", "each", "most", "few",
     "many", "much", "more", "less", "least", "several", "enough", "other", "another",
     "such", "something", "anything", "nothing", "everything", "someone", "anyone",
     "everyone", "none"] ++
  numberWords.map fun (w, n) => (w, s!"write the numeral {n}")

/-- The fix for a forbidden word, or `none` if the word is allowed. Any word containing
`n't` is forbidden. -/
def forbiddenFix (w : String) : Option String :=
  match forbidden.lookup w with
  | some f => some f
  | none => if (w.splitOn "n't").length > 1 then some "use never in claims and not in conditions" else none

/-- Every word the language reserves; a vocabulary may define none of them. -/
def languageWords : List String :=
  structureWords ++ labels ++ claimWords ++ articles ++ forbidden.map (·.1) ++
  ["section"]

/-! ## Languages

The tables above are English. A language maps its own closed words to the canonical ones,
so the parser and everything after it work unchanged; vocabularies supply the open words. -/

structure Language where
  name : String
  /-- Two-word phrases: the pair as written, and the canonical phrase. -/
  phrases : List ((String × String) × String)
  /-- Structure words: as written, and canonical. -/
  structureMap : List (String × String)
  claimMap : List (String × String)
  labels : List String
  articles : List String
  forbidden : List (String × String)
  numbers : List (String × String)
  /-- English forbids any word containing `n't`. -/
  contractions : Bool
  /-- Gloss words strict mode still allows in main clauses, such as "times" after a count. -/
  fillers : List String := []
  deriving Inhabited

def english : Language where
  name := "en"
  phrases := [(("for", "each"), "for each"), (("at", "most"), "at most"), (("this", "section"), "this section")]
  structureMap := structureWords.map fun w => (w, w)
  claimMap := claimWords.map fun w => (w, w)
  labels := labels
  articles := articles
  forbidden := forbidden
  numbers := numberWords
  contractions := true
  fillers := ["times"]

def Language.forbiddenFix (L : Language) (w : String) : Option String :=
  match L.forbidden.lookup w with
  | some f => some f
  | none => if L.contractions && (w.splitOn "n't").length > 1 then some "use never in claims and not in conditions" else none

/-- The words that open an aside to the end of the sentence. -/
def Language.asideWords (L : Language) : List String :=
  L.structureMap.filter (·.2 == "because") |>.map (·.1)

/-- Every word the language reserves; a vocabulary may define none of them. -/
def Language.words (L : Language) : List String :=
  L.structureMap.map (·.1) ++ L.claimMap.map (·.1) ++ L.labels ++ L.articles ++ L.forbidden.map (·.1) ++
    L.phrases.flatMap fun ((a, b), _) => [a, b]

end Lrep.Words
