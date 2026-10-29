# The lrep language guide

An lrep program is a Markdown file of English sentences. A fixed set of words mean something to the checker; the rest is description. This guide covers the file format, statements, values, control flow, claims, and project configuration, then lists the word kinds and error codes for reference.

## A first program

```text
# Ship old logs

List the application's log directory "/var/log/app" as Logs.

For each file in Logs:
- If it is older than 7 days, compress it, then upload it to the shared bucket url "s3://acme-logs/app".

This section never deletes and only writes to "s3://acme-logs/app".
```

`lrep residue` prints the program with the description removed:

```text
List directory "/var/log/app" as Logs.
For each file in Logs:
- If it is older than 7 days, compress it, then upload it to url "s3://acme-logs/app".
This section never deletes and only writes to "s3://acme-logs/app".
```

"The application's log" and "the shared bucket" were description. Everything left is what runs, and the last sentence is a claim the checker verifies.

`lrep core` goes one step further and prints the program the checker actually works on. Names and `it` become numbered values, every argument is labelled, and each claim becomes a check on one kind of effect:

```text
section "Ship old logs"
  v0 := list(directory "/var/log/app")
  for v1 in v0 do
    if older(v1, than: 7 days) then
      v2 := compress(v1)
      upload(v2, to: url "s3://acme-logs/app")
    end
  end
  claim never delete
  claim only write (to: url "s3://acme-logs/app")
```

## Files and sections

- A heading (`#` to `######`) starts a section. Each section is checked separately, and its heading is only a name. Text before the first heading is an error.
- A sentence ends with a full stop. A sentence that ends with a colon must be followed by a list; each `- ` item holds one or more sentences, and a nested list is indented two more spaces.
- Other Markdown, such as code blocks, quotes, tables, links and emphasis, is an error.

## Statements

A clause is the part of a sentence between commas, `then` and the full stop. Each clause has exactly one op, written as a command:

```text
Open the file "/tmp/a.txt", then serve it over a websocket on port 8080.
```

- Use the op's base form: "Write", not "Writes". "The job writes to disk" is an error, because a sentence that reads as a description must not perform anything.
- Join steps with `then`. A comma always ends a clause, and `and` never joins steps.
- An op takes at most one argument without a label, its object, and any number of labelled ones, such as `to "/backup"` and `on port 443`.

## Values

- Strings use straight double quotes: `"/var/log/app"`. Curly quotes are an error.
- Numbers are numerals, optionally with a unit: `443`, `7 days`, `2 GB`. Number words such as "seven" are errors.
- A sort word before a value says what the value must be: `the file "/a.txt"`, `port 443`.
- A sort word alone refers to the one value of that sort in scope: `delete the file`. If there is none, or more than one, that's error E032; name the value with `as` instead.
- `as` names a value: `List the directory "/tmp" as Temp.` A name is capitalised and can't start a sentence.
- `it` is the result of the previous step; `them` is the same when the result is a list. After an `if` or a loop ends, there is no `it`.
- `and` makes a list of values: `Compress "/a" and "/b".`

## Control

```text
Open the file "/tmp/report.txt".
If it is empty, delete it.
Otherwise, move it to "/archive".

For each file in Logs:
- Compress it, then upload it to "s3://acme-logs/app".

Copy the file "/a" to "/b".
If it fails, delete the file "/b".
```

- A condition is a subject, `is` or `are`, an optional `not`, and a predicate: `if it is older than 7 days`. Join tests with `and` or with `or`, but not both.
- `Otherwise` must come directly after an `If` sentence.
- `For each` steps through a list that already exists. It is the only loop, so loops always end. A single step, such as an HTTP request, can still take a long time.
- `If it fails` is a fixed phrase. It must come directly after a statement sentence, and it runs if a step in that sentence fails. Without it, a failed step stops the section.

## Claims

A sentence that begins "This section" is a claim about every step the section might take, on every path:

| Claim | Holds when |
| --- | --- |
| `never deletes from "/etc"` | No step can delete anything under `/etc` |
| `only writes to "/backup"` | Every write is under `/backup` |
| `always reads from "/etc/app"` | Every run that finishes reads from `/etc/app` |
| `uploads at most 3 times` | No run uploads more than 3 times |

- A claim names an effect, `reads`, `writes`, `deletes`, `connects`, `listens` or `runs`, or any op, as in `never uploads`.
- A string in a claim is a URL if it has a scheme, and otherwise an absolute path.
- A relative path, or a `run the command …` step, has effects the checker can't determine, so any claim that depends on it fails.
- An op can name a contents label, so claims can say where data came from rather than where it goes. If `post` has the contents label `from`, then `never posts from "/Journal"` fails when any posted text could have come from `/Journal`, even if it went to an allowed server. These are data-flow claims.
- `never` and `only` claims are covered by the proof in `Lrep/Sound.lean`. `always`, `at most` and data-flow claims are checked, but the proof doesn't cover them yet. `lrep permissions` shows which is which.

## Asides and forbidden words

An explanation goes in parentheses, or after "because" to the end of the sentence:

```text
Upload Old to "s3://acme-logs/app" (the bucket keeps 90 days of history).
Delete the file "/tmp/z" because the archive already holds its contents.
```

An aside can't contain ops or claim words, so searching a file for `delete` finds only real deletes.

Some words are errors, each with a suggested fix: modals such as "may" and "should", contractions such as "don't", most pronouns such as "they" and "this", quantifiers such as "all" and "every", and number words. Each either hides what a sentence does or has a more precise replacement.

## Vocabularies and projects

A vocabulary is a JSON file that defines the words a program can use: ops, with their arguments and effects; sorts; predicates; constants; units; and checked descriptive words. Each op declares its effects, such as "reads its object" or "writes to its `to` argument". Claims are checked against those declarations, and the runtime stops an op that does anything else. An op can also be defined by a section of lrep, in which case its effects come from that section.

A vocabulary marked `"pure": true` may contain only ops with no effects: ops that compute, such as rendering or summarizing text. This lets a plugin author ship computation without being able to touch anything; the effectful ops stay with whoever owns the main vocabulary. [`examples/obsidian`](../examples/obsidian/README.md) shows this for app plugins.

A project's `lrep.json`, next to its programs, lists its vocabularies:

```json
{
  "vocabularies": ["vocab/core/files.json", "vocab/core/net.json", "vocab/examples/places.json"],
  "gloss": "strict"
}
```

Without an `lrep.json`, the four core vocabularies (files, units, network, processes) load. Two optional keys:

- `gloss` is `loose` (the default) or `strict`; see the next section.
- `language` names a different natural language's word tables. English is the default; `vocab/es` is a Spanish demo.

### Checked descriptive words

A vocabulary can define descriptive words, called qualifiers, whose meaning the checker verifies:

```json
"qualifiers": [
  {"forms": ["backup"], "within": ["/backup"]},
  {"forms": ["log"], "from": ["/var/log"]}
],
"disjoint": [["production", "temporary"]]
```

- `within` lists where a value must be. `the backup file "/var/db/prod.db"` is an error.
- `from` lists where a value's contents must come from. Calling the contents of the production database "the log" is an error.
- A `disjoint` pair can't describe the same value.

With `"gloss": "strict"`, a sentence may contain only words the checker reads, qualifiers, and "a", "an" and "the". Any other description must go in an aside.

## Reference

### Word kinds

The checker decides each word's kind from the word itself:

| Kind | Examples | Meaning |
| --- | --- | --- |
| Op | `copy`, `delete`, `upload` | Performs an action. Defined in a vocabulary |
| Sort | `file`, `directory`, `url` | A type of value |
| Predicate | `empty`, `older`, `larger` | A test, used in conditions |
| Constant | `disk`, `websocket` | A fixed value |
| Qualifier | `backup`, `log`, `temporary` | A checked descriptive word |
| Structure | `then`, `if`, `for each`, `it`, `as` | Connects the parts of a program |
| Label | `to`, `from`, `on`, `than` | Names an argument. Every preposition is a label |
| Claim | `never`, `only`, `always`, `at most` | Starts a claim |
| Name | `Logs`, `Settings` | A value named with `as` |
| Literal | `"/var/log/app"`, `443` | A string or a number |
| Gloss | `the`, `old`, `job` | Description, which the checker ignores |

A word that a vocabulary defines can't be used as description. If `open` is an op, "the open port" is an error; write "the unblocked port".

### Error codes

Most errors suggest a fix.

| Code | Meaning |
| --- | --- |
| E001 | Markdown that lrep doesn't allow, or a `:` not followed by a list |
| E002 | Text before the first heading, or two sections with the same name |
| E003 | An unsupported character, or curly quotes |
| E004 | An unterminated string or parenthesis |
| E010 | A forbidden word |
| E011 | An op where a value belongs |
| E012 | An op or claim word inside an aside |
| E013 | An undeclared name, or a name starting a sentence |
| E014 | Description outside an aside, in strict mode |
| E020 | A clause with no op |
| E021 | A later clause without `then` |
| E022 | `and` between steps |
| E023 | `then` directly after a condition |
| E024 | An op not in its base form |
| E025 | A label the op doesn't take |
| E026 | A second argument without a label |
| E027 | A missing argument, or `only` without a resource |
| E028 | `Otherwise` or `If it fails` in the wrong place |
| E029 | A condition that mixes `and` and `or` |
| E030 | A value of the wrong sort, or an invalid literal |
| E031 | `it` or `them` with nothing to refer to, or the wrong one of the two |
| E032 | A sort word that matches no value, or several |
| E033 | A name declared twice |
| E034 | A qualifier that doesn't fit its value |
| E040 | A claim that doesn't hold |
| E042 | A claim word outside a "This section" sentence |
| E050 | A broken vocabulary or project file |
| W001 | A warning: a sentence over 25 words |

### The guarantee

`Lrep/Sound.lean` proves in Lean that if the checker accepts a `never` or `only` claim, no run of the section breaks it. That covers every path and any number of loop iterations, including runs that stop part-way. The proof assumes each op does only what its vocabulary declares, and the runtime enforces that assumption by stopping any op that does something else.
