/-
The runtime (`lrep run`): executes a checked program's core AST with the core vocabularies'
ops, under a capability sandbox.

The sandbox is capability-based: an op that performs an effect its section's inferred
effects don't describe fails instead of quietly breaking a claim. Each effect is checked
with `approxB`, which `approxB_iff` proves equal to the semantics' `approx`, so every run
that completes is one the soundness proof covers.

`--root DIR` maps every absolute path into `DIR`, like WASI's preopened directories. A
`run` statement's subprocess is not confined; its effects are `top`, so claims about them
already fail statically.
-/
import Lrep
import Lrep.Semantics
import Std.Time

namespace Lrep

/-- A runtime value. -/
inductive RV where
  | path (segs : List String)
  | url (u : Url)
  | host (scheme host : String)
  | port (n : Nat)
  | text (s : String)
  | archive (entries : List (String × String))
  | service (desc : String)
  /-- A quantity in base units: seconds or bytes. -/
  | qty (n : Nat)
  | transport (t : String)
  | cmd (c : String)
  | list (vs : List RV)
  | none
  deriving Inhabited

structure RtCtx where
  root : Option System.FilePath
  /-- The virtual working directory that relative paths resolve against. -/
  cwd : List String
  /-- The section's inferred effects: the capabilities its ops may use. -/
  caps : List Effect
  log : IO.Ref (List String)

/-- A sandbox violation, which aborts the whole run rather than one section. -/
def sandboxPrefix : String := "sandbox: "

def RtCtx.real (ctx : RtCtx) (segs : List String) : System.FilePath :=
  match ctx.root with
  | some r => segs.foldl (fun (acc : System.FilePath) (s : String) => acc / s) r
  | none => System.FilePath.mk (pathString segs)

def CRes.show : CRes → String
  | .path segs => pathString segs
  | .url sc h segs => s!"{sc}://{h}{if segs.isEmpty then "" else pathString segs}"
  | .host sc h => if sc.isEmpty then h else s!"{sc}://{h}"
  | .port n => s!"port {n}"
  | .cmd c => s!"\"{c}\""

/-- Performs an effect: checks it against the capabilities, then logs it. -/
def perform (ctx : RtCtx) (k : Kind) (c : CRes) : IO Unit := do
  unless ctx.caps.any (fun a => a.kind == k && approxB a.res c) do
    throw (IO.userError s!"{sandboxPrefix}undeclared {k.name} on {c.show}")
  ctx.log.modify (· ++ [s!"{k.name} {c.show}"])

private def fail (m : String) : IO α := throw (IO.userError m)

/-! ## Values -/

def evalLit (ctx : RtCtx) (s : SortDef) (l : Lit) : IO RV :=
  match s.resource, l with
  | .pathExact, .str p | .pathPrefix, .str p =>
    let raw := if isAbsolute p then p.splitOn "/" else ctx.cwd ++ p.splitOn "/"
    match normSegs raw with
    | .ok segs => pure (.path segs)
    | .error e => fail e
  | .url, .str u => match parseUrl u with | .ok v => pure (.url v) | .error e => fail e
  | .host, .str h => match parseUrl h with
    | .ok v => pure (.host v.scheme v.host)
    | .error _ => pure (.host "" h)
  | .port, .int n => pure (.port n)
  | .command, .str c => pure (.cmd c)
  | _, .str v => pure (.text v)
  | _, .int n => pure (.qty n)

def evalConst (c : ConstDef) : RV :=
  match c.resource with
  | .path p => match normPath p with | .ok segs => .path segs | .error _ => .none
  | .url u => match parseUrl u with | .ok v => .url v | .error _ => .none
  | .host h => .host "" h
  | .port n => .port n
  | .none => .transport (c.forms.headD c.sort)

abbrev RtEnv := List (Nat × RV)

def evalVal (ctx : RtCtx) (env : RtEnv) : CVal → IO RV
  | .lit s l _ _ => evalLit ctx s l
  | .qty n _ scale _ _ => pure (.qty (n * scale))
  | .const c _ => pure (evalConst c)
  | .ref id _ => match env.lookup id with
    | some v => pure v
    | none => fail "a value was used before its statement ran"
  | .list vs => do pure (.list (← vs.attach.mapM fun ⟨v, _⟩ => evalVal ctx env v))
  | .unknown => fail "an unknown value"

/-! ## Ops -/

private def arg (args : List (String × RV)) (l : String) : RV := (args.lookup l).getD .none

private def asPath : RV → IO (List String)
  | .path segs => pure segs
  | _ => fail "expected a path"

private def asPaths : RV → IO (List (List String))
  | .path segs => pure [segs]
  | .list vs => vs.mapM asPath
  | _ => fail "expected paths"

private def asUrl : RV → IO Url
  | .url u => pure u
  | _ => fail "expected a URL"

private def urlString (u : Url) : String := s!"{u.scheme}://{u.host}{if u.segs.isEmpty then "" else pathString u.segs}"

/-- An archive's bytes: each entry as a header line and its contents. -/
def serializeArchive (es : List (String × String)) : String :=
  String.join (es.map fun (n, c) => s!"--- {n} {c.utf8ByteSize}\n{c}\n")

private def content (ctx : RtCtx) : RV → IO String
  | .text s => pure s
  | .archive es => pure (serializeArchive es)
  | .path segs => do perform ctx .read (.path segs); IO.FS.readFile (ctx.real segs)
  | _ => fail "expected text, an archive or a file"

private def curl (args : Array String) (stdin : Option String := none) : IO String := do
  let child ← IO.Process.spawn { cmd := "curl", args, stdin := .piped, stdout := .piped, stderr := .piped }
  let (stdinH, child) ← child.takeStdin
  stdinH.putStr (stdin.getD "")
  stdinH.flush
  let out ← child.stdout.readToEnd
  let err ← child.stderr.readToEnd
  let code ← child.wait
  if code != 0 then fail s!"curl failed: {trimStr err}" else pure out

private def httpLike (u : Url) : Bool := u.scheme == "http" || u.scheme == "https"

/-- Runs one op of the core vocabularies. Every external effect goes through `perform`. -/
def callOp (ctx : RtCtx) (op : OpDef) (args : List (String × RV)) : IO RV := do
  match op.base with
  | "open" =>
    let f ← asPath (arg args "")
    perform ctx .read (.path f)
    unless ← (ctx.real f).pathExists do fail s!"no such file: {pathString f}"
    pure (.path f)
  | "read" =>
    let f ← asPath (arg args "")
    perform ctx .read (.path f)
    pure (.text (← IO.FS.readFile (ctx.real f)))
  | "write" =>
    let f ← asPath (arg args "to")
    let c ← content ctx (arg args "")
    perform ctx .write (.path f)
    if let some dir := (ctx.real f).parent then IO.FS.createDirAll dir
    IO.FS.writeFile (ctx.real f) c
    pure .none
  | "copy" | "move" =>
    let f ← asPath (arg args "")
    let d ← asPath (arg args "to")
    let dst := d ++ [f.getLastD ""]
    perform ctx .read (.path f)
    let bytes ← IO.FS.readBinFile (ctx.real f)
    perform ctx .write (.path dst)
    IO.FS.createDirAll (ctx.real d)
    IO.FS.writeBinFile (ctx.real dst) bytes
    if op.base == "move" then
      perform ctx .delete (.path f)
      IO.FS.removeFile (ctx.real f)
    pure (.path dst)
  | "delete" =>
    let f ← asPath (arg args "")
    perform ctx .delete (.path f)
    if ← (ctx.real f).isDir then IO.FS.removeDirAll (ctx.real f) else IO.FS.removeFile (ctx.real f)
    pure .none
  | "list" =>
    let d ← asPath (arg args "")
    perform ctx .read (.path d)
    let entries ← (ctx.real d).readDir
    let mut files : List (List String) := []
    for e in entries do
      if !(← e.path.isDir) then files := files ++ [d ++ [e.fileName]]
    pure (.list ((files.mergeSort fun a b => pathString a ≤ pathString b).map .path))
  | "compress" =>
    let fs ← asPaths (arg args "")
    let es ← fs.mapM fun f => do
      perform ctx .read (.path f)
      pure (f.getLastD "", ← IO.FS.readFile (ctx.real f))
    pure (.archive es)
  | "fetch" =>
    let u ← asUrl (arg args "")
    perform ctx .connect (.host u.scheme u.host)
    unless httpLike u do fail s!"fetch supports http and https, not {u.scheme}"
    pure (.text (← curl #["-fsSL", urlString u]))
  | "connect" =>
    match arg args "to" with
    | .url u =>
      perform ctx .connect (.host u.scheme u.host)
      unless httpLike u do fail s!"connect supports http and https, not {u.scheme}"
      let _ ← curl #["-fsS", "-o", "/dev/null", "--max-time", "10", urlString u]
      pure .none
    | .host sc h =>
      perform ctx .connect (.host sc h)
      -- A host literal written with an http(s) scheme connects like that URL.
      unless sc == "http" || sc == "https" do
        fail s!"connecting to the bare host {h} is not supported by this runtime"
      let _ ← curl #["-fsS", "-o", "/dev/null", "--max-time", "10", s!"{sc}://{h}"]
      pure .none
    | _ => fail "expected a host or URL"
  | "upload" =>
    let c ← content ctx (arg args "")
    let u ← asUrl (arg args "to")
    perform ctx .write (.url u.scheme u.host u.segs)
    perform ctx .connect (.host u.scheme u.host)
    unless httpLike u do fail s!"upload supports http and https, not {u.scheme}"
    let _ ← curl #["-fsS", "-T", "-", urlString u] (some c)
    pure .none
  | "run" =>
    let c ← match arg args "" with | .cmd c => pure c | _ => fail "expected a command"
    perform ctx .spawn (.cmd c)
    let out ← IO.Process.output { cmd := "sh", args := #["-c", c],
                                   cwd := ctx.root.map fun r => ctx.cwd.foldl (fun (acc : System.FilePath) (s : String) => acc / s) r }
    if out.exitCode != 0 then fail s!"command \"{c}\" exited with {out.exitCode}"
    pure (.text out.stdout)
  | "serve" | "listen" =>
    fail s!"`{op.base}` starts a long-running service, which this runtime does not provide yet"
  | b => fail s!"no implementation for op `{b}`"

private def nowSecs : IO Int := do
  pure (← Std.Time.Timestamp.now).toSecondsSinceUnixEpoch.val

/-- Evaluates a predicate test of the core vocabularies. -/
def testPred (ctx : RtCtx) (p : PredDef) (args : List (String × RV)) : IO Bool := do
  let f ← asPath (arg args "")
  perform ctx .read (.path f)
  let real := ctx.real f
  match p.forms.headD "" with
  | "missing" => pure !(← real.pathExists)
  | "empty" =>
    if ← real.isDir then pure (← real.readDir).isEmpty
    else pure ((← real.metadata).byteSize == 0)
  | "older" =>
    let secs ← match arg args "than" with | .qty n => pure n | _ => fail "expected a duration"
    pure ((← real.metadata).modified.sec + secs ≤ (← nowSecs))
  | "larger" =>
    let bytes ← match arg args "than" with | .qty n => pure n | _ => fail "expected a size"
    pure ((← real.metadata).byteSize.toNat > bytes)
  | w => fail s!"no implementation for predicate `{w}`"

/-! ## Statements -/

private def evalArgs (ctx : RtCtx) (env : RtEnv) (args : List CArg) : IO (List (String × RV)) :=
  args.mapM fun a => do pure (a.label, ← evalVal ctx env a.val)

private def isSandbox (e : IO.Error) : Bool := (toString e).startsWith sandboxPrefix

mutual
def execStmt (ctx : RtCtx) (env : RtEnv) : CStmt → IO RtEnv
  | .call id op args _ => do
    -- A composite op does nothing itself; its inlined body follows the call.
    if op.body.isSome then return (id, RV.none) :: env
    let vs ← evalArgs ctx env args
    let r ← callOp ctx op vs
    pure ((id, r) :: env)
  | .ite all tests thn els => do
    let mut result := all
    for t in tests do
      let v := (← testPred ctx t.pred (← evalArgs ctx env t.args)) != t.neg
      if all then
        result := v
        if !v then break
      else
        result := v
        if v then break
    if result then
      let _ ← execStmts ctx env thn
    else
      let _ ← execStmts ctx env els
    pure env
  | .loop elem coll body => do
    let items ← match ← evalVal ctx env coll with
      | .list vs => pure vs
      | v => pure [v]
    for v in items do
      let _ ← execStmts ctx ((elem, v) :: env) body
    pure env
  | .try body h => do
    try execStmts ctx env body
    catch e =>
      if isSandbox e then throw e
      ctx.log.modify (· ++ [s!"failed: {e}; handling it"])
      execStmts ctx env h

def execStmts (ctx : RtCtx) (env : RtEnv) : List CStmt → IO RtEnv
  | [] => pure env
  | s :: rest => do
    let env' ← execStmt ctx env s
    execStmts ctx env' rest
end

structure RunResult where
  /-- Per section: its name, whether it completed, and its log. -/
  sections : List (String × Bool × List String)
  sandboxViolation : Bool

/-- Runs every section of a checked file. An op that fails stops its section; a sandbox
violation stops the run. -/
def runFile (lex : Lexicon) (r : FileResult) (root : Option System.FilePath) : IO RunResult := do
  let mut out := []
  for s in r.cores do
    let log ← IO.mkRef []
    let ctx : RtCtx := { root, cwd := [], caps := (infer lex s).1.effects, log }
    try
      let _ ← execStmts ctx [] s.stmts
      out := out ++ [(s.name, true, ← log.get)]
    catch e =>
      out := out ++ [(s.name, false, (← log.get) ++ [s!"stopped: {e}"])]
      if isSandbox e then return ⟨out, true⟩
  pure ⟨out, false⟩

end Lrep
