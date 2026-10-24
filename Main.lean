import Lrep
import Lrep.Server
import Lrep.Diff
import Lrep.Dataflow
import Lrep.Runtime
import Lrep.Audit
import Lrep.Core

open Lrep

def usage : String :=
  "usage:\n  lrep check [--json] FILE…\n  lrep residue FILE\n  lrep core FILE\n  lrep tokens FILE\n  lrep effects FILE\n  lrep grammar [--calm]\n  lrep lsp\n  lrep diff [--json] OLD NEW\n  lrep vocab-diff OLD.json NEW.json\n  lrep dataflow FILE\n  lrep run [--root DIR] FILE\n  lrep audit [--dry-run] FILE\n"

def withFile (path : String) (k : FileResult → IO UInt32) : IO UInt32 := do
  try
    let r ← checkFile path
    k r
  catch e =>
    IO.eprintln s!"lrep: {e}"
    pure 2

def main (args : List String) : IO UInt32 := do
  match args with
  | "check" :: rest =>
    let json := rest.contains "--json"
    let files := rest.filter (· != "--json")
    if files.isEmpty then IO.eprint usage; return 2
    let mut code : UInt32 := 0
    for f in files do
      let c ← withFile f fun r => do
        if json then IO.println (r.toJ.pretty 0)
        else IO.print r.text
        pure (if r.hasErrors then 1 else 0)
      code := max code c
    pure code
  | ["residue", f] => withFile f fun r => do
    if r.residueOk then IO.print r.residue; pure (if r.hasErrors then 1 else 0)
    else
      IO.print r.text
      IO.eprintln "lrep: the residue view needs a file whose only errors are E040"
      pure 1
  | ["core", f] => withFile f fun r => do
    if r.hasErrors then
      IO.print r.text
      IO.eprintln "lrep: the core view needs a file without errors"
      return 1
    IO.print r.coreText; pure 0
  | ["tokens", f] => withFile f fun r => do IO.print r.tokensText; pure 0
  | ["effects", f] => withFile f fun r => do
    IO.print r.effectsText; pure (if r.hasErrors then 1 else 0)
  | "grammar" :: flags => do
    let calm := flags.contains "--calm"
    let proj ← loadProject "."
    if !proj.diags.isEmpty then
      for d in proj.diags do IO.eprintln s!"error[{d.code}]: {d.message}"
      return 1
    IO.println ((grammar proj.lex calm).pretty 0)
    pure 0
  | ["lsp"] => do serve; pure 0
  | "run" :: rest =>
    let (root, files) := match rest with
      | "--root" :: d :: fs => (some (System.FilePath.mk d), fs)
      | fs => (none, fs)
    match files with
    | [f] => withFile f fun r => do
      if r.hasErrors then
        IO.print r.text
        IO.eprintln "lrep: refusing to run a file with errors"
        return 1
      let fp : System.FilePath := f
      let proj ← loadProject (fp.parent.getD ".")
      let res ← runFile proj.lex r root
      for (name, ok, log) in res.sections do
        IO.println s!"{name}: {if ok then "completed" else "stopped"}"
        for l in log do IO.println s!"  {l}"
      pure (if res.sections.all (·.2.1) then 0 else 1)
    | _ => IO.eprint usage; pure 2
  | "audit" :: rest =>
    let dry := rest.contains "--dry-run"
    match rest.filter (· != "--dry-run") with
    | [f] => withFile f fun r => do
      let body := auditRequest r
      if dry then IO.println (body.pretty 0); return 0
      let some cred ← auditCredential
        | IO.eprintln "lrep: no Claude API credentials; set ANTHROPIC_API_KEY or run `ant auth login`"; return 2
      match parseAudit (← sendAudit cred body) with
      | .error e => IO.eprintln s!"lrep: {e}"; pure 2
      | .ok [] => IO.println "No gloss contradicts the program."; pure 0
      | .ok fs =>
        for x in fs do IO.println s!"{f}:{x.line}: \"{x.gloss}\": {x.concern}"
        -- The audit annotates review; it never fails a build.
        pure 0
    | _ => IO.eprint usage; pure 2
  | ["dataflow", f] => withFile f fun r => do
    IO.print r.dataflow; pure (if r.hasErrors then 1 else 0)
  | ["vocab-diff", a, b] => do
    try
      let va ← IO.ofExcept (loadVocab (← IO.FS.readFile a))
      let vb ← IO.ofExcept (loadVocab (← IO.FS.readFile b))
      let cs := diffVocabs va vb
      for c in cs do IO.println s!"{if c.flagged then "!" else "~"} {c.text}"
      -- A change that weakens a guarantee needs a reviewer's attention.
      pure (if cs.any (·.flagged) then 1 else 0)
    catch e =>
      IO.eprintln s!"lrep: {e}"
      pure 2
  | "diff" :: rest =>
    let json := rest.contains "--json"
    match rest.filter (· != "--json") with
    | [a, b] => withFile a fun ra => withFile b fun rb => do
      let ds := diffFiles ra rb
      if json then
        IO.println ((J.arr (ds.map fun (n, cs) => .obj [("section", .str n), ("changes", .arr (cs.map Change.toJ))])).pretty 0)
      else
        for (n, cs) in ds do
          IO.println s!"{n}:"
          for c in cs do IO.println s!"  {c.text}"
      -- Removing or weakening a claim needs a reviewer's attention.
      pure (if ds.any (·.2.any Change.flagged) then 1 else 0)
    | _ => IO.eprint usage; pure 2
  | _ => IO.eprint usage; pure 2
