# lrep

lrep is a small language for glue code: scripts that move data and trigger actions between files, services and commands, such as backups, syncs, cleanup jobs and deploy steps. Programs are written in a restricted English. A checker verifies claims such as `never deletes from "/etc"` and rejects programs that break them.

lrep isn't for application logic. It has no arithmetic, string handling or open-ended loops, which is what keeps its claims provable; computation belongs in the ops a vocabulary provides.

```text
# Back up the config

Read the config file "/etc/app/config.json" as Settings.
Write Settings to the backup file "/backup/config.json".
If it fails, delete the backup file "/backup/config.json" because a truncated backup misleads whoever restores it.

This section never deletes from "/etc" and only writes to the backup directory "/backup".
```

The last sentence is a claim, and the checker verifies it. Change the failure handler to `If it fails, delete the backup file "/etc/app/config.json".` and checking fails:

```text
error[E034]: "backup" describes "/etc/app/config.json", which is not within "/backup" or "s3://acme-backups"
error[E040]: claim not satisfied: never deletes from "/etc"
```

The first error comes from the word "backup". This program's vocabulary, a JSON file that defines the words a program can use, says that backup files live under `/backup` or `s3://acme-backups`. The second error is the claim.

Glue scripts run with real permissions and get skimmed in review. lrep is designed so that a skim is reliable. A fixed set of words mean something to the checker: ops such as `copy` and `delete`, and words such as `then`, `if` and `for each`. Every other word is description, which the checker ignores, except for descriptive words like "backup" and "log" that a vocabulary defines and the checker verifies. Each sentence that begins "This section" is a claim, and the checker verifies it on every path through the section. `Lrep/Sound.lean` proves in Lean that an accepted `never` or `only` claim holds on every run, provided each op does only what its vocabulary declares. `always` and `at most` claims are checked but not covered by the proof.

lrep is meant to be written by AI models and read by people. The rules are strict because the cost of strictness falls on the writer and the benefit on the reader.

## Try it

Install [elan](https://github.com/leanprover/elan), the Lean version manager. `lake build` then installs the Lean 4 version named in `lean-toolchain` and builds lrep.

```bash
git clone https://github.com/aidanmaney/lrep && cd lrep
lake build
```

Check an example, show only the words the checker reads, and list what each section may touch:

```bash
.lake/build/bin/lrep check examples/nightly/nightly.lrep
.lake/build/bin/lrep residue examples/nightly/nightly.lrep
.lake/build/bin/lrep effects examples/nightly/nightly.lrep
```

| Command | What it does |
| --- | --- |
| `lrep check FILE` | Reports errors and whether each claim holds; `--json` for tools |
| `lrep residue FILE` | Prints the program with the description removed |
| `lrep effects FILE` | Lists what each section may read, write, delete or connect to |
| `lrep dataflow FILE` | Prints a Graphviz graph of which values feed which steps |
| `lrep run --root DIR FILE` | Runs a checked program, with every absolute path mapped inside `DIR` |
| `lrep diff OLD NEW` | Lists claims added, removed, weakened or strengthened between two versions |
| `lrep vocab-diff OLD NEW` | Lists changes to the descriptive words and op effects in a vocabulary |
| `lrep audit FILE` | Asks Claude whether a program's description matches what it does. Needs `ANTHROPIC_API_KEY` or an `ant auth login` profile |
| `lrep lsp` | Runs the language server for editors |
| `lrep grammar` | Prints a TextMate grammar for syntax highlighting |

The [language guide](docs/guide.md) explains how to write lrep. A VS Code extension is in [editors/vscode](editors/vscode/README.md).

## What's here

| Path | Contents |
| --- | --- |
| `Lrep/` | The checker, language server, runtime and proof, in Lean |
| `vocab/` | Vocabularies: the core one (files, units, network, processes), a Spanish demo, and example descriptive words |
| `examples/` | Example programs |
| `docs/` | The language guide |
| `editors/vscode/` | The VS Code extension |
| `tests/` | Test programs with expected results; `lake test` runs them |

## Status

lrep is an experiment. The checker, the proof for `never` and `only` claims, the language server, the VS Code extension and the tests are complete. The runtime is partial: it runs local file operations, commands and HTTP requests, but not S3 uploads or long-running services such as web servers.

## License

[MIT](LICENSE)
