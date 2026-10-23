/-
The tokenizer and the word classifier. Classification needs no grammar: only the word,
its neighbours for the two-word phrases, its place in the sentence, and the vocabularies.
-/
import Lrep.Markdown
import Lrep.Lexicon
import Lrep.Words

namespace Lrep

inductive Cls where
  | str (v : String)
  | int (n : Nat)
  | comma | dot | colon
  | struct (w : String)
  | label (w : String)
  | claim (w : String)
  /-- An op, with the key of the form written (`base`, `s`, `past`, `ing` or `pp`). -/
  | op (o : OpDef) (form : String)
  | pred (p : PredDef)
  | sort (s : SortDef) (plural : Bool)
  | unit (u : UnitDef)
  | const (c : ConstDef)
  /-- A qualifier: a descriptive word whose meaning is checked. -/
  | qual (q : QualDef)
  | article
  | name
  | gloss
  | aside
  deriving Inhabited

structure Tok where
  cls : Cls
  text : String
  span : Span
  deriving Inhabited

namespace Tok
/-- Program tokens survive into the residue; gloss, articles and asides don't. -/
def isProgram (t : Tok) : Bool :=
  match t.cls with
  | .gloss | .article | .aside => false
  | _ => true
def isStruct (t : Tok) (w : String) : Bool :=
  match t.cls with | .struct v => v == w | _ => false
def isComma (t : Tok) : Bool := match t.cls with | .comma => true | _ => false
def isClaim (t : Tok) : Bool := match t.cls with | .claim _ => true | _ => false
def isOp (t : Tok) : Bool := match t.cls with | .op _ _ => true | _ => false
def isGloss (t : Tok) : Bool := match t.cls with | .gloss => true | _ => false
def isLabel (t : Tok) : Bool := match t.cls with | .label _ => true | _ => false
end Tok

/-- A sentence after tokenizing. `bad` marks lexical or classification errors, which stop
the sentence from being parsed. -/
inductive TSent where
  | mk (toks : List Tok) (term : Char) (termSpan : Span) (bad : Bool) (sub : List (List TSent))
  deriving Inhabited

def TSent.toks : TSent → List Tok | .mk ts .. => ts
def TSent.term : TSent → Char | .mk _ t .. => t
def TSent.termSpan : TSent → Span | .mk _ _ s .. => s
def TSent.bad : TSent → Bool | .mk _ _ _ b _ => b
def TSent.sub : TSent → List (List TSent) | .mk _ _ _ _ s => s

/-- The span from the first token to the terminator. -/
def TSent.span (s : TSent) : Span :=
  match s.toks.head? with
  | some t => if t.span.line == s.termSpan.line then ⟨t.span.line, t.span.col, s.termSpan.endCol⟩ else t.span
  | none => s.termSpan

structure TSection where
  name : String
  span : Span
  sents : List TSent
  deriving Inhabited

/-! ## Raw tokens -/

inductive Raw where
  | word (w : String) (sp : Span)
  | str (v : String) (text : String) (sp : Span)
  | int (n : Nat) (text : String) (sp : Span)
  | punct (c : Char) (sp : Span)
  /-- An aside, with the words inside it. -/
  | aside (sp : Span) (words : List (String × Span))
  deriving Inhabited

private def spanOf (a b : PChar) : Span :=
  if a.line == b.line then ⟨a.line, a.col, b.col + 1⟩ else ⟨a.line, a.col, a.col + 1⟩

/-- Letters: ASCII ones, and any non-ASCII character that isn't a quote, dash or space. -/
def isLetter (c : Char) : Bool :=
  c.isAlpha || (c.toNat > 127 && !"‘’“”–—…  ".toList.contains c)

private def wordChar (c : Char) : Bool := isLetter c || c.isDigit || c == '\'' || c == '’'

private def d (code : String) (sp : Span) (m : String) (fix : Option Fix := none) : Diagnostic :=
  { code, span := sp, message := m, fix }

/-- Words inside an aside: letter-initial runs of letters, digits and apostrophes. -/
def asideWords (cs : List PChar) : List (String × Span) :=
  let rec go (cs : List PChar) (cur : List PChar) : List (List PChar) :=
    match cs with
    | [] => if cur.isEmpty then [] else [cur.reverse]
    | p :: rest =>
      if wordChar p.c && (!cur.isEmpty || isLetter p.c) then go rest (p :: cur)
      else if cur.isEmpty then go rest []
      else cur.reverse :: go rest []
  (go cs []).filterMap fun w =>
    match w.head?, w.getLast? with
    | some a, some b => some (String.ofList (w.map fun p => if p.c == '’' then '\'' else p.c), spanOf a b)
    | _, _ => none

private def mdChars : List Char := ['*', '_', '`', '[', ']', '<', '>', '|', '#', '~']

/-- Splits a sentence's characters into raw tokens. -/
def lexChars (asides : List String) (fuel : Nat) (cs : List PChar) : List Raw × List Diagnostic :=
  match fuel with
  | 0 => ([], [])
  | fuel + 1 =>
    match cs with
    | [] => ([], [])
    | p :: rest =>
      let cont (r : List Raw) (ds : List Diagnostic) (rest : List PChar) :=
        let (rs, ds') := lexChars asides fuel rest
        (r ++ rs, ds ++ ds')
      if p.c == ' ' || p.c == '\t' || p.c == '-' then cont [] [] rest
      else if p.c == '"' || p.c == '“' then
        let close := if p.c == '"' then '"' else '”'
        match lexString close p.line rest [] [] with
        | some (v, endP, ds, rest') =>
          let sp := spanOf p endP
          let text := "\"" ++ v ++ "\""
          let ds := if close == '"' then ds
            else ds ++ [d "E003" sp "typographic quotes are not string delimiters"
              (some { label := s!"use straight quotes: {text}", edit := some (sp, text) })]
          cont [.str v text sp] ds rest'
        | none => ([], [d "E004" p.span "unterminated string (strings end on the line they start)"])
      else if p.c == '(' then
        match rest.findIdx? (·.c == ')') with
        | some i =>
          let inner := rest.take i
          let endP := rest[i]?.getD p
          cont [.aside (spanOf p endP) (asideWords inner)] [] (rest.drop (i + 1))
        | none => ([], [d "E004" p.span "unterminated parenthesis"])
      else if p.c == ')' then cont [] [d "E004" p.span "unmatched `)`"] rest
      else if p.c.isDigit then
        let ds := (p :: rest).takeWhile (·.c.isDigit)
        let text := String.ofList (ds.map (·.c))
        let last := ds.getLast?.getD p
        cont [.int text.toNat! text (spanOf p last)] [] ((p :: rest).drop ds.length)
      else if isLetter p.c then
        let ws := (p :: rest).takeWhile (wordChar ·.c)
        let last := ws.getLast?.getD p
        let w := String.ofList (ws.map fun q => if q.c == '’' then '\'' else q.c)
        let ds := ws.filter (·.c == '’') |>.map fun q =>
          d "E003" q.span "typographic apostrophe" (some { label := "use a straight apostrophe: '", edit := some (q.span, "'") })
        let after := (p :: rest).drop ws.length
        if asides.contains w.toLower then
          -- An aside from `because` to the end of the sentence.
          let endP := ((p :: rest).getLast?).getD p
          ([.aside (spanOf p endP) (asideWords after)], ds)
        else cont [.word w (spanOf p last)] ds after
      else if p.c == ',' || p.c == '.' || p.c == ':' then cont [.punct p.c p.span] [] rest
      else if p.c == '‘' || p.c == '’' || p.c == '”' then
        cont [] [d "E003" p.span "typographic quote" (some { label := "use straight quotes", edit := none })] rest
      else if mdChars.contains p.c then
        cont [] [d "E001" p.span s!"`{p.c}` is Markdown outside the subset"] rest
      else cont [] [d "E003" p.span s!"unsupported character `{p.c}`"] rest
where
  /-- Reads a string body up to `close`, on one line, with escapes `\"` and `\\`. -/
  lexString (close : Char) (line : Nat) : List PChar → List Char → List Diagnostic →
      Option (String × PChar × List Diagnostic × List PChar)
    | [], _, _ => none
    | q :: rest, acc, ds =>
      if q.line != line then none
      else if q.c == close || (close == '”' && q.c == '"') then some (String.ofList acc.reverse, q, ds, rest)
      else if q.c == '\\' && close == '"' then
        match rest with
        | e :: rest' =>
          if e.c == '"' || e.c == '\\' then lexString close line rest' (e.c :: acc) ds
          else lexString close line rest' (e.c :: '\\' :: acc)
            (ds ++ [d "E003" (spanOf q e) "the only escapes are \\\" and \\\\"])
        | [] => none
      else lexString close line rest (q.c :: acc) ds

/-! ## Classification -/

private def lower (s : String) : String := s.toLower

def opForm? (lex : Lexicon) (w : String) : Option (OpDef × String) :=
  lex.ops.findSome? fun o =>
    if lower o.base == w then some (o, "base")
    else (o.forms.find? fun (_, f) => lower f == w).map fun (k, _) => (o, k)

def vocabClass? (lex : Lexicon) (w : String) : Option Cls :=
  match opForm? lex w with
  | some (o, k) => some (.op o k)
  | none =>
  match lex.predicates.find? (·.forms.any (lower · == w)) with
  | some p => some (.pred p)
  | none =>
  match lex.sorts.findSome? fun s =>
      if (s.forms.head?.map lower) == some w then some (s, false)
      else if (s.forms[1]?.map lower) == some w then some (s, true) else none with
  | some (s, pl) => some (.sort s pl)
  | none =>
  match lex.units.find? (·.forms.any (lower · == w)) with
  | some u => some (.unit u)
  | none =>
  match lex.constants.find? (·.forms.any (lower · == w)) with
  | some c => some (.const c)
  | none => (lex.qualifiers.find? (·.forms.any (lower · == w))).map .qual

/-- Whether a word is an op or claim word, which asides may not contain. -/
def reservedInAside (lex : Lexicon) (w : String) : Bool :=
  (lex.lang.claimMap.lookup (lower w)).isSome || (opForm? lex (lower w)).isSome

private def isCap (w : String) : Bool := (w.toList.head?.map Char.isUpper).getD false

/-- E014: gloss in a main clause, which strict mode forbids. -/
def strictGlossDiag (w : String) (sp : Span) : Diagnostic :=
  let fix : Fix := { label := "use a qualifier from the vocabularies, or move the description into an aside" }
  { code := "E014", span := sp, message := s!"\"{w}\" is unchecked gloss, which strict mode allows only in asides", fix }

/-- Classifies a sentence's raw tokens. Returns the tokens and any E010/E012 diagnostics. -/
def classify (lex : Lexicon) (raws : List Raw) : List Tok × List Diagnostic :=
  let rec go (first : Bool) : List Raw → List Tok × List Diagnostic
    | [] => ([], [])
    | .word a sa :: .word b sb :: rest =>
      let pair := (lower a, lower b)
      if let some canon := lex.lang.phrases.lookup pair then
        let cls := if canon == "at most" then Cls.claim canon else Cls.struct canon
        let (ts, ds) := go false rest
        (⟨cls, a ++ " " ++ b, sa.join sb⟩ :: ts, ds)
      else
        let (t, ds1) := one first a sa
        let (ts, ds2) := go false (.word b sb :: rest)
        (t :: ts, ds1 ++ ds2)
    | .word a sa :: rest =>
      let (t, ds1) := one first a sa
      let (ts, ds2) := go false rest
      (t :: ts, ds1 ++ ds2)
    | .str v text sp :: rest =>
      let (ts, ds) := go false rest
      (⟨.str v, text, sp⟩ :: ts, ds)
    | .int n text sp :: rest =>
      let (ts, ds) := go false rest
      (⟨.int n, text, sp⟩ :: ts, ds)
    | .punct c sp :: rest =>
      let cls := if c == ',' then Cls.comma else if c == '.' then Cls.dot else Cls.colon
      let (ts, ds) := go false rest
      (⟨cls, c.toString, sp⟩ :: ts, ds)
    | .aside sp ws :: rest =>
      let bad := asidePhrases ws
      let ds1 := bad.map fun (w, s) =>
        { code := "E012", span := s, message := s!"\"{w}\" is an op or claim word, which an aside may not contain" : Diagnostic }
      let (ts, ds2) := go false rest
      (⟨.aside, "", sp⟩ :: ts, ds1 ++ ds2)
  go true raws
where
  one (first : Bool) (w : String) (sp : Span) : Tok × List Diagnostic :=
    let lw := lower w
    match lex.lang.forbiddenFix lw with
    | some fix =>
      let edit := (lex.lang.numbers.lookup lw).map (sp, ·)
      (⟨.gloss, w, sp⟩, [{ code := "E010", span := sp, message := s!"\"{w}\" is a forbidden word",
                           fix := some { label := fix, edit } }])
    | none =>
    if let some c := lex.lang.structureMap.lookup lw then (⟨.struct c, w, sp⟩, [])
    else if lex.lang.labels.contains lw then (⟨.label lw, w, sp⟩, [])
    else if let some c := lex.lang.claimMap.lookup lw then (⟨.claim c, w, sp⟩, [])
    else match vocabClass? lex lw with
    | some c => (⟨c, w, sp⟩, [])
    | none =>
      if lex.lang.articles.contains lw then (⟨.article, w, sp⟩, [])
      else if isCap w && !first then (⟨.name, w, sp⟩, [])
      else if lex.strictGloss && !lex.lang.fillers.contains lw then (⟨.gloss, w, sp⟩, [strictGlossDiag w sp])
      else (⟨.gloss, w, sp⟩, [])
  /-- Op and claim words inside an aside, including the phrase `at most`. -/
  asidePhrases : List (String × Span) → List (String × Span)
    | [] => []
    | (a, sa) :: (b, sb) :: rest =>
      if lex.lang.phrases.lookup (lower a, lower b) == some "at most" then (a ++ " " ++ b, sa.join sb) :: asidePhrases rest
      else if reservedInAside lex a then (a, sa) :: asidePhrases ((b, sb) :: rest)
      else asidePhrases ((b, sb) :: rest)
    | [(a, sa)] => if reservedInAside lex a then [(a, sa)] else []

/-- Words in a sentence for W001: words outside asides, literals excluded. -/
def wordCount (raws : List Raw) : Nat :=
  raws.foldl (fun n r => match r with | .word .. => n + 1 | _ => n) 0

def tokenizeSentence (lex : Lexicon) (cs : List PChar) : List Tok × List Diagnostic :=
  let (raws, ds1) := lexChars lex.lang.asideWords (cs.length + 1) cs
  let (toks, ds2) := classify lex raws
  let w001 : List Diagnostic :=
    if wordCount raws > 25 then
      match toks.head? with
      | some t => [{ code := "W001", span := t.span, message := s!"sentence has {wordCount raws} words; the limit is 25" }]
      | none => []
    else []
  (toks, ds1 ++ ds2 ++ w001)

mutual
def tokSent (lex : Lexicon) : Sentence → TSent × List Diagnostic
  | .mk cs term sp sub =>
    let (toks, ds) := tokenizeSentence lex cs
    let (sub', ds') := tokItems lex sub
    (.mk toks term sp (ds.any Diagnostic.isError) sub', ds ++ ds')

def tokItems (lex : Lexicon) : List (List Sentence) → List (List TSent) × List Diagnostic
  | [] => ([], [])
  | it :: rest =>
    let (a, ds1) := tokSents lex it
    let (b, ds2) := tokItems lex rest
    (a :: b, ds1 ++ ds2)

def tokSents (lex : Lexicon) : List Sentence → List TSent × List Diagnostic
  | [] => ([], [])
  | s :: rest =>
    let (a, ds1) := tokSent lex s
    let (b, ds2) := tokSents lex rest
    (a :: b, ds1 ++ ds2)
end

def tokenizeDoc (lex : Lexicon) (doc : Doc) : List TSection × List Diagnostic :=
  doc.sections.foldl (init := ([], [])) fun (acc, ds) s =>
    let (ss, ds') := tokSents lex s.sents
    (acc ++ [⟨s.name, s.span, ss⟩], ds ++ ds')

end Lrep
