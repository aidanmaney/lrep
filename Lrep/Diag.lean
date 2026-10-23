/-
Diagnostics, fixes, and the small JSON writer every output uses.

Columns are 1-based and `endCol` is exclusive. Line 0 means the diagnostic is
about the file as a whole (for example a bad vocabulary).
-/
namespace Lrep

structure Span where
  line : Nat
  col : Nat
  endCol : Nat
  deriving Repr, BEq, Inhabited

def Span.none : Span := ⟨0, 0, 0⟩

/-- The smallest span covering both, assuming `a` starts first and both are on one line;
across lines the result keeps `a`'s line and runs to the end of `a`. -/
def Span.join (a b : Span) : Span :=
  if a.line == b.line then ⟨a.line, a.col, max a.endCol b.endCol⟩ else a

structure Related where
  span : Span
  message : String
  deriving Inhabited

/-- A fix: a hint for the reader, and optionally a machine-applicable edit. -/
structure Fix where
  label : String
  edit : Option (Span × String) := none
  deriving Inhabited

structure Diagnostic where
  code : String
  span : Span
  message : String
  related : List Related := []
  fix : Option Fix := none
  /-- A fallback for a shape no rule in the code table names. A weak error loses to any
  rule that applies to the same sentence, such as a misplaced claim word (E042). -/
  weak : Bool := false
  deriving Inhabited

def Diagnostic.severity (d : Diagnostic) : String :=
  if d.code.startsWith "W" then "warning" else "error"

def Diagnostic.isError (d : Diagnostic) : Bool := d.severity == "error"

/-- Code order: lower codes win when several rules apply to one sentence. -/
def codeRank (c : String) : Nat :=
  let digits := (String.ofList (c.toList.drop 1))
  let n := digits.toNat?.getD 999
  if c.startsWith "W" then 1000 + n else n

/-- The diagnostic with the lowest code, the first of those on a tie. -/
def lowest : List Diagnostic → Option Diagnostic
  | [] => none
  | d :: ds =>
    match lowest ds with
    | none => some d
    | some e => if codeRank e.code < codeRank d.code then some e else some d

def sortDiags (ds : List Diagnostic) : List Diagnostic :=
  ds.mergeSort fun a b =>
    a.span.line < b.span.line || (a.span.line == b.span.line && a.span.col ≤ b.span.col)

/-! ## JSON -/

def spaces (n : Nat) : String := String.ofList (List.replicate n ' ')

inductive J where
  | null
  | bool (b : Bool)
  | num (n : Nat)
  | str (s : String)
  | arr (xs : List J)
  | obj (kvs : List (String × J))
  /-- Already-rendered JSON, such as a negative number. -/
  | raw (s : String)
  deriving Inhabited

def jsonEscape (s : String) : String :=
  s.toList.foldl (init := "") fun acc c =>
    match c with
    | '"' => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | '\t' => acc ++ "\\t"
    | '\r' => acc ++ "\\r"
    | c => if c.toNat < 0x20 then acc ++ "\\u00" ++ (if c.toNat < 16 then "0" else "1") ++
        String.ofList (Nat.toDigits 16 (c.toNat % 16)) else acc.push c

mutual
/-- Compact rendering, used inside one-line arrays and objects. -/
def J.compact : J → String
  | .null => "null"
  | .bool b => if b then "true" else "false"
  | .num n => toString n
  | .str s => "\"" ++ jsonEscape s ++ "\""
  | .arr xs => "[" ++ ", ".intercalate (J.compactItems xs) ++ "]"
  | .obj kvs => "{" ++ ", ".intercalate (J.compactFields kvs) ++ "}"
  | .raw s => s

def J.compactItems : List J → List String
  | [] => []
  | x :: xs => x.compact :: J.compactItems xs

def J.compactFields : List (String × J) → List String
  | [] => []
  | (k, v) :: rest => ("\"" ++ jsonEscape k ++ "\": " ++ v.compact) :: J.compactFields rest
end

mutual
/-- Pretty rendering: objects and arrays of objects break across lines; scalars and
arrays of scalars stay on one line. -/
def J.pretty (indent : Nat) : J → String
  | .arr xs =>
    if xs.isEmpty then "[]"
    else if xs.all (fun | .obj _ => false | .arr _ => false | _ => true) then J.compact (.arr xs)
    else "[\n" ++ ",\n".intercalate (J.prettyItems (indent + 2) xs) ++ "\n" ++ spaces indent ++ "]"
  | .obj kvs =>
    if kvs.isEmpty then "{}"
    else "{\n" ++ ",\n".intercalate (J.prettyFields (indent + 2) kvs) ++ "\n" ++ spaces indent ++ "}"
  | j => j.compact

def J.prettyItems (indent : Nat) : List J → List String
  | [] => []
  | x :: xs => (spaces indent ++ x.pretty indent) :: J.prettyItems indent xs

def J.prettyFields (indent : Nat) : List (String × J) → List String
  | [] => []
  | (k, v) :: rest =>
    (spaces indent ++ "\"" ++ jsonEscape k ++ "\": " ++ v.pretty indent) :: J.prettyFields indent rest
end

def Diagnostic.toJ (d : Diagnostic) : J :=
  let base : List (String × J) :=
    [("code", .str d.code), ("severity", .str d.severity), ("line", .num d.span.line),
     ("col", .num d.span.col), ("endCol", .num d.span.endCol), ("message", .str d.message)]
  let rel : List (String × J) :=
    if d.related.isEmpty then []
    else [("related", .arr (d.related.map fun r =>
      .obj [("line", .num r.span.line), ("col", .num r.span.col), ("message", .str r.message)]))]
  let fix : List (String × J) :=
    match d.fix with
    | none => []
    | some f =>
      match f.edit with
      | some (s, rep) =>
        [("fix", .obj [("line", .num s.line), ("col", .num s.col), ("endCol", .num s.endCol),
          ("replacement", .str rep), ("message", .str f.label)])]
      | none => [("fix", .obj [("message", .str f.label)])]
  .obj (base ++ rel ++ fix)

/-! ## Text rendering -/

def carets (s : Span) : String :=
  spaces (s.col - 1) ++ String.ofList (List.replicate (max 1 (s.endCol - s.col)) '^')

/-- Renders a diagnostic: the message, the source line with carets, related lines and the fix. -/
def Diagnostic.render (file : String) (lines : Array String) (d : Diagnostic) : String :=
  let srcLine (n : Nat) : String := lines.getD (n - 1) ""
  let width := ([d.span.line] ++ d.related.map (·.span.line)).foldl (fun w n => max w (toString n).length) 1
  let gutter := spaces width ++ " |"
  let num (n : Nat) := spaces (width - (toString n).length) ++ toString n ++ " | "
  let head := s!"{d.severity}[{d.code}]: {d.message}\n"
  if d.span.line == 0 then
    head ++ s!"{spaces width}--> {file}\n" ++
      (match d.fix with | some f => s!"{gutter}\n{spaces width} = fix: {f.label}\n" | none => "")
  else
    let loc := s!"{spaces width}--> {file}:{d.span.line}\n"
    let main := s!"{gutter}\n{num d.span.line}{srcLine d.span.line}\n{gutter} {carets d.span}\n"
    let rel := d.related.foldl (init := "") fun acc r =>
      acc ++ s!"{num r.span.line}{srcLine r.span.line}\n{gutter} {carets r.span} {r.message}\n"
    let fix := match d.fix with
      | some f => s!"{gutter}\n{spaces width} = fix: {f.label}\n"
      | none => ""
    head ++ loc ++ main ++ rel ++ fix

end Lrep
