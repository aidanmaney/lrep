# lrep

**Glue code you can read once.** lrep is a small programming language for the scripts that move, copy, back up and delete things, written in plain English. Its checker proves what each program will and won't touch.

```text
# Back up the config

Read the config file "/etc/app/config.json" as Settings.
Write Settings to the backup file "/backup/config.json".
If it fails, delete the backup file "/backup/config.json" because a truncated backup misleads whoever restores it.

This section never deletes from "/etc" and only writes to the backup directory "/backup".
```

That last sentence isn't a comment. It's a **claim**, and the checker proves it. Suppose someone edits the failure handler to delete the wrong file:

```text
error[E034]: "backup" describes "/etc/app/config.json", which is not within "/backup" or "s3://acme-backups"
error[E040]: claim not satisfied: never deletes from "/etc"
```

The program no longer compiles. The English said one thing and the code did another, so the checker refused it.

## Why

Shell scripts and cron jobs are where data goes missing. They're short, they run with real permissions, and reviewers skim them. lrep is built so that a skim is enough:

- **Every word has one job.** A small, fixed set of words do things: ops like `copy` and `delete`, and words like `then`, `if` and `for each`. The rest is description that the checker ignores. There are no hidden meanings to work out.
- **Claims are proved, not hoped.** `never deletes`, `only writes to "/backup"`, `always reads` and `uploads at most 3 times` are checked against every path through the program. If one could be false, the program doesn't compile.
- **Descriptions are checked too.** Calling something "the backup file" is a promise about where it lives; calling it "the log" is a promise about where its contents came from. The checker holds the program to both.
- **The guarantee is proved in Lean.** If the checker accepts a `never` or `only` claim, no run of the program can break it, assuming each operation does only what its definition declares.

lrep is meant to be written by AI models and read by people. Strict rules cost a model a quick fix; they spare the reviewer from guessing.

## Try it

You need [Lean 4](https://lean-lang.org/install/); the right version installs itself from `lean-toolchain`.

```bash
git clone https://github.com/aidanmaney/lrep && cd lrep
```

```bash
lake build
```

Check the example, then see the program with the description stripped out, and what it touches:

```bash
.lake/build/bin/lrep check examples/nightly/nightly.lrep
```

```bash
.lake/build/bin/lrep residue examples/nightly/nightly.lrep
```

```bash
.lake/build/bin/lrep effects examples/nightly/nightly.lrep
```

| Command | What it does |
| --- | --- |
| `lrep check FILE` | Checks a program and reports errors and claims (`--json` for tools) |
| `lrep residue FILE` | Shows just the program: the words the checker reads |
| `lrep effects FILE` | Lists everything each section may read, write, delete or connect to |
| `lrep dataflow FILE` | Draws which values feed which steps, as a Graphviz graph |
| `lrep run --root DIR FILE` | Runs a checked program in a sandbox, with every path kept inside `DIR` |
| `lrep diff OLD NEW` | Shows claims added, removed or weakened between two versions |
| `lrep vocab-diff OLD NEW` | Shows what changed in a vocabulary's definitions |
| `lrep audit FILE` | Asks Claude whether the remaining description matches what the program does |
| `lrep lsp` | Runs the language server for editors |
| `lrep grammar` | Prints a TextMate grammar for highlighting |

The [language guide](docs/guide.md) explains how to write lrep.

## Editor support

`editors/vscode` is a VS Code extension. It highlights what the checker reads in bold and leaves description plain, shows errors as you type, and explains on hover what each `it`, name and description refers to. It also shows each section's claims and effects above its heading. See its [README](editors/vscode/README.md) to install it.

## What's here

| Path | Contents |
| --- | --- |
| `Lrep/` | The checker, language server, runtime and proofs, in Lean |
| `vocab/` | Vocabularies: the core one (files, units, network, processes), a Spanish demo, and example descriptive words |
| `examples/` | Example programs |
| `docs/` | The language guide |
| `editors/vscode/` | The VS Code extension |
| `tests/` | Test programs and their expected results; run them with `lake test` |

## Status

lrep is an experiment. The checker, proofs and editor support work, and `lake test` covers them. The runtime handles local files, commands and HTTP; it can't yet upload to S3 or run long-lived services such as web servers.

## License

[MIT](LICENSE)
