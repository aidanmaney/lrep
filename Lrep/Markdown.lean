/-
The Markdown subset: headings, paragraphs and `- ` lists that follow a sentence
ending in `:`. Everything else is E001. This layer also splits blocks into sentences.
-/
import Lrep.Diag

namespace Lrep

/-- A source character with its 1-based position. -/
structure PChar where
  c : Char
  line : Nat
  col : Nat
  deriving Inhabited

def PChar.span (p : PChar) : Span := ⟨p.line, p.col, p.col + 1⟩

/-- A sentence: its characters without the terminator, the terminator (`.` or `:`), and,
for a `:` sentence, the list items that follow it. Each item holds one or more sentences. -/
inductive Sentence where
  | mk (chars : List PChar) (term : Char) (termSpan : Span) (sub : List (List Sentence))
  deriving Inhabited

structure Section where
  name : String
  span : Span
  sents : List Sentence
  deriving Inhabited

structure Doc where
  sections : List Section
  diags : List Diagnostic
  deriving Inhabited

/-! ## Lines and blocks -/

inductive Line where
  | blank
  | heading (text : String) (span : Span)
  | item (indent : Nat) (text : List PChar)
  | text (indent : Nat) (chars : List PChar)
  | bad (span : Span) (msg : String)

private def isSpace (c : Char) : Bool := c == ' ' || c == '\t'

private def charsOf (line : Nat) (s : String) : List PChar :=
  (s.toList.zipIdx 1).map fun (c, i) => ⟨c, line, i⟩

private def trimEnd (cs : List PChar) : List PChar :=
  (cs.reverse.dropWhile (isSpace ·.c)).reverse

private def lineOf (cs : List PChar) : Nat := (cs.head?.map (·.line)).getD 0

def trimStr (s : String) : String :=
  let f (l : List Char) := l.dropWhile Char.isWhitespace
  String.ofList (f (f s.toList).reverse).reverse

private def str (cs : List PChar) : String := String.ofList (cs.map (·.c))

private def startsWithAny (s : List Char) (ps : List String) : Bool :=
  ps.any fun p => s.take p.length == p.toList

private def orderedMarker (s : List Char) : Bool :=
  let ds := s.takeWhile Char.isDigit
  !ds.isEmpty && (match s.drop ds.length with
    | '.' :: ' ' :: _ | ')' :: ' ' :: _ => true
    | _ => false)

def classifyLine (n : Nat) (raw : String) : Line :=
  let cs := trimEnd (charsOf n (if raw.endsWith "\r" then String.ofList raw.toList.dropLast else raw))
  if cs.isEmpty then .blank
  else
    let indent := (cs.takeWhile (isSpace ·.c)).length
    let body := cs.drop indent
    let b := body.map (·.c)
    let sp : Span := ⟨n, indent + 1, indent + 2⟩
    if indent == 0 && b.head? == some '#' then
      let hashes := b.takeWhile (· == '#')
      if hashes.length ≤ 6 && (b.drop hashes.length).head? == some ' ' then
        .heading (trimStr (str (body.drop (hashes.length + 1)))) ⟨n, 1, cs.length + 1⟩
      else .bad sp "a heading is one to six `#` and a space"
    else if b.take 2 == ['-', ' '] then
      .item indent ((body.drop 2).dropWhile (isSpace ·.c))
    else if startsWithAny b ["* ", "+ ", ">", "```", "~~~", "|", "<", "---", "===", "\t"] || orderedMarker b then
      .bad sp "only headings, paragraphs and `- ` lists are allowed"
    else .text indent body

private def e001 (sp : Span) (m : String) : Diagnostic := { code := "E001", span := sp, message := m }

inductive Block where
  | heading (name : String) (span : Span)
  | para (chars : List PChar)
  | item (indent : Nat) (chars : List PChar)
  deriving Inhabited

private def joinLine (prev : List PChar) (next : List PChar) : List PChar :=
  match prev.getLast? with
  | some p => prev ++ [⟨' ', p.line, p.col + 1⟩] ++ next
  | none => next

/-- Groups lines into blocks. A paragraph is consecutive unindented lines; an item takes
continuation lines indented two spaces past its `-`. -/
def blocks (lines : List Line) : List Block × List Diagnostic :=
  let close (st : List Block × Option Block × List Diagnostic) : List Block × List Diagnostic :=
    match st.2.1 with
    | some b => (st.1 ++ [b], st.2.2)
    | none => (st.1, st.2.2)
  let step (st : List Block × Option Block × List Diagnostic) (l : Line) :=
    let (bs, ds) := close st
    match l, st.2.1 with
    | .blank, _ => (bs, none, ds)
    | .heading t sp, _ => (bs ++ [.heading t sp], none, ds)
    | .item k cs, _ => (bs, some (.item k cs), ds)
    | .bad sp m, _ => (bs, none, ds ++ [e001 sp m])
    | .text 0 cs, some (.para p) => (st.1, some (.para (joinLine p cs)), st.2.2)
    | .text 0 cs, _ => (bs, some (.para cs), ds)
    | .text k cs, some (.item i p) =>
      if k ≥ i + 2 then (st.1, some (.item i (joinLine p cs)), st.2.2)
      else (bs, none, ds ++ [e001 ⟨lineOf cs, 1, k + 1⟩
        "an item's continuation lines are indented two spaces past its `-`"])
    | .text _ cs, some (.para p) => (st.1, some (.para (joinLine p cs)), st.2.2)
    | .text k cs, _ => (bs, none, ds ++ [e001 ⟨lineOf cs, 1, k + 1⟩
        "indented text (such as a code block) is outside the Markdown subset"])
  close (lines.foldl step ([], none, []))

/-! ## Sentences -/

/-- Splits a block's characters at `.` and `:` outside quotes and parentheses that are
followed by whitespace or the end. Returns each sentence's characters with its terminator. -/
def splitSentences (cs : List PChar) : List (List PChar × Option PChar) :=
  let rec go (cs : List PChar) (cur : List PChar) (quote : Option Char) (paren : Bool) :
      List (List PChar × Option PChar) :=
    match cs with
    | [] =>
      match cur with
      | [] => []
      | last :: before =>
        if cur.all (isSpace ·.c) then []
        -- Still inside a quote or parenthesis: end at a final `.` or `:` anyway, so the
        -- tokenizer reports the unterminated string or parenthesis (E004).
        else if last.c == '.' || last.c == ':' then [(before.reverse, some last)]
        else [(cur.reverse, none)]
    | p :: rest =>
      let atEnd := match rest with | [] => true | q :: _ => isSpace q.c
      match quote with
      | some close =>
        if p.c == '\\' && close == '"' && !rest.isEmpty then
          go rest.tail (rest.headD p :: p :: cur) quote paren
        else if p.c == close then go rest (p :: cur) none paren
        else go rest (p :: cur) quote paren
      | none =>
        if paren then go rest (p :: cur) none (p.c != ')')
        else if p.c == '"' then go rest (p :: cur) (some '"') false
        else if p.c == '“' then go rest (p :: cur) (some '”') false
        else if p.c == '(' then go rest (p :: cur) none true
        else if (p.c == '.' || p.c == ':') && atEnd then
          (cur.reverse.dropWhile (isSpace ·.c), some p) :: go rest [] none false
        else go rest (p :: cur) none false
  termination_by cs.length
  decreasing_by all_goals (simp_all; try omega)
  (go cs [] none false).map fun (s, t) => (s.dropWhile (isSpace ·.c), t)

/-- A block's sentences. Every sentence must end in `.` or `:`, and a `:` must end the block. -/
def blockSentences (cs : List PChar) : List (List PChar × Char × Span) × List Diagnostic :=
  let parts := splitSentences cs
  let n := parts.length
  (parts.zipIdx).foldl (init := ([], [])) fun (acc, ds) ((chars, t), i) =>
    match t with
    | none =>
      let sp := match chars.getLast? with | some p => p.span | none => Span.none
      (acc, ds ++ [e001 sp "a sentence must end with `.` or `:`"])
    | some p =>
      if p.c == ':' && i + 1 < n then
        (acc ++ [(chars, p.c, p.span)], ds ++ [e001 p.span "a `:` must end its paragraph or list item"])
      else (acc ++ [(chars, p.c, p.span)], ds)

/-- Takes the items at `indent` from the front of `bs`, with their nested lists. -/
def takeItems (fuel : Nat) (indent : Nat) (bs : List Block) :
    List (List Sentence) × List Block × List Diagnostic :=
  match fuel with
  | 0 => ([], bs, [])
  | fuel + 1 =>
    match bs with
    | .item k cs :: rest =>
      if k < indent then ([], bs, [])
      else if k > indent then
        let sp : Span := match cs.head? with | some p => ⟨p.line, 1, k + 1⟩ | none => Span.none
        let (more, rest', ds) := takeItems fuel indent rest
        (more, rest', e001 sp "a nested list is indented two spaces more than its parent item" :: ds)
      else
        let (sents, ds1) := blockSentences cs
        let (item, rest1, ds2) := attach fuel (k + 2) sents rest
        let (more, rest2, ds3) := takeItems fuel indent rest1
        (item :: more, rest2, ds1 ++ ds2 ++ ds3)
    | _ => ([], bs, [])
where
  /-- Builds sentences, giving the last one the list that follows when it ends in `:`. -/
  attach (fuel : Nat) (indent : Nat) (sents : List (List PChar × Char × Span)) (rest : List Block) :
      List Sentence × List Block × List Diagnostic :=
    match sents.getLast? with
    | some (cs, ':', sp) =>
      let (sub, rest', ds) := takeItems fuel indent rest
      let init := sents.dropLast.map fun (c, t, s) => Sentence.mk c t s []
      let ds' := if sub.isEmpty then ds ++ [e001 sp "a `:` must be followed by a list"] else ds
      (init ++ [Sentence.mk cs ':' sp sub], rest', ds')
    | _ => (sents.map fun (c, t, s) => Sentence.mk c t s [], rest, [])

/-- A section body: paragraphs, each optionally followed by its list. -/
def body (fuel : Nat) (bs : List Block) : List Sentence × List Diagnostic :=
  match fuel with
  | 0 => ([], [])
  | fuel + 1 =>
    match bs with
    | [] => ([], [])
    | .para cs :: rest =>
      let (sents, ds1) := blockSentences cs
      let (ss, rest', ds2) := takeItems.attach (fuel + 1) 0 sents rest
      let (more, ds3) := body fuel rest'
      (ss ++ more, ds1 ++ ds2 ++ ds3)
    | .item _ cs :: rest =>
      let sp := match cs.head? with | some p => ⟨p.line, 1, p.col⟩ | none => Span.none
      let (more, ds) := body fuel rest
      (more, e001 sp "a list must directly follow a sentence ending in `:`" :: ds)
    | .heading _ _ :: rest => body fuel rest

/-- Reads a whole file into sections. -/
def readDoc (src : String) : Doc :=
  let lines := (src.splitOn "\n").zipIdx 1 |>.map fun (l, n) => classifyLine n l
  let (bs, ds) := blocks lines
  -- Split the blocks at headings.
  let (pre, secs) := bs.foldl (init := (([] : List Block), ([] : List (String × Span × List Block))))
    fun (pre, secs) b =>
      match b, secs with
      | .heading n sp, _ => (pre, secs ++ [(n, sp, [])])
      | b, [] => (pre ++ [b], secs)
      | b, _ => (pre, secs.dropLast ++ (secs.getLast?.map fun (n, sp, xs) => (n, sp, xs ++ [b])).toList)
  let preDiag : List Diagnostic :=
    match pre.head? with
    | some (.para cs) | some (.item _ cs) =>
      let sp := match cs.head? with | some p => ⟨p.line, p.col, p.col + 1⟩ | none => Span.none
      [{ code := "E002", span := sp, message := "text before the first heading" }]
    | _ => []
  let (sections, ds2, _) := secs.foldl (init := (([] : List Section), ([] : List Diagnostic), ([] : List String)))
    fun (acc, ds, names) (n, sp, bs) =>
      let (sents, ds') := body (bs.length + 1) bs
      let dup : List Diagnostic := if names.contains n then
        [{ code := "E002", span := sp, message := s!"duplicate section name \"{n}\"" }] else []
      (acc ++ [⟨n, sp, sents⟩], ds ++ dup ++ ds', names ++ [n])
  ⟨sections, ds ++ preDiag ++ ds2⟩

end Lrep
