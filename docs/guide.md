# The lrep language guide

lrep programs read like short English instructions. Under the prose is a strict program: a fixed set of words do the work, and everything else is description the checker ignores. This guide shows how to write one.

## A first program

```text
# Ship old logs

List the directory "/var/log/app" as Logs.

For each file in Logs:
- If it is older than 7 days, compress it, then upload it to "s3://acme-logs/app".

This section never deletes and only writes to "s3://acme-logs/app".
```

Running `lrep residue` shows what the checker actually reads, with the description removed:

```text
List directory "/var/log/app" as Logs.
For each file in Logs:
- If it is older than 7 days, compress it, then upload it to "s3://acme-logs/app".
This section never deletes and only writes to "s3://acme-logs/app".
```

## Files, sections and sentences

A program is a Markdown file with a few rules:

- **Headings** (`#` to `######`) start sections. Each section is checked on its own, and its heading is just a name.
- **Sentences** end with a full stop. A sentence that ends with a colon is followed by a list, and each `- ` item holds one or more sentences. Indent a nested list by two more spaces.
- Anything else Markdown offers, such as code blocks, quotes, tables, links and emphasis, is an error. So is text before the first heading.

## Words

Every word belongs to exactly one kind, decided by the word alone:

| Kind | Examples | What it does |
| --- | --- | --- |
| Op | `copy`, `delete`, `upload` | Does something. Comes from a vocabulary |
| Sort | `file`, `directory`, `url` | Names a type of value |
| Predicate | `empty`, `older`, `larger` | Tests something in a condition |
| Constant | `disk`, `websocket` | A fixed value |
| Qualifier | `backup`, `log`, `temporary` | A checked description (see below) |
| Structure | `then`, `if`, `for each`, `it`, `as` | Holds the program together |
| Label | `to`, `from`, `on`, `than` | Names an argument (every preposition) |
| Claim | `never`, `only`, `always`, `at most` | States a guarantee the checker proves |
| Name | `Logs`, `Settings` | A value you named with `as` |
| Literal | `"/var/log/app"`, `443` | A string or a number |
| Gloss | `the`, `old`, `job` | Description. The checker ignores it |

Words reserved by a vocabulary are never gloss, even in passing. If `open` is an op, "the open port" is an error: write "the unblocked port".

## Values

- **Strings** use straight double quotes: `"/var/log/app"`. Curly quotes are an error.
- **Numbers** are numerals: `443`, `7 days`, `2 GB`. Number words like "seven" are errors.
- **A sort before a value** says what it must be: `the file "/a.txt"`, `port 443`.
- **A sort alone** means the one value of that sort in scope: `delete the file`. If there's none, or more than one, the checker asks you to name it.
- **Names** come from `as`: `List the directory "/tmp" as Temp.` A name is capitalised and may not start a sentence.
- **`it`** is the result of the previous step; **`them`** is the same, when the result is a list. After an `if` or a loop ends, `it` is gone.
- **`and`** makes a list of values: `Compress "/a" and "/b".`

## Statements

Each clause has exactly one op, written as a command:

```text
Open the file "/tmp/a.txt", then serve it over a websocket on port 8080.
```

- Use the op's base form: "Write", not "Writes". "The job writes to disk" is an error, because a sentence that sounds like a description must not quietly act.
- Join steps with `then`. A comma always ends a clause, and `and` never joins steps.
- An op takes one unlabelled argument, its object, and labelled ones such as `to "/backup"` and `on port 443`.

## Control

```text
If it is empty, delete it.
Otherwise, move it to "/archive".

For each file in Logs:
- Compress it, then upload it to "s3://acme-logs/app".

Copy the file "/a" to "/b".
If it fails, delete the file "/b".
```

- **Conditions** use `is` or `are`, optionally `not`, and a predicate: `if it is older than 7 days`. Combine tests with `and` or with `or`, never both.
- **`Otherwise`** directly follows an `If` sentence.
- **`For each`** walks a list that already exists. There are no other loops, so every program finishes.
- **`If it fails`** directly follows a statement sentence and handles its failure. Otherwise a failed step stops the section.

## Asides

Explanations go in parentheses, or after "because" to the end of the sentence:

```text
Upload it to "s3://acme-logs/app" (the bucket keeps 90 days of history).
Delete it because the archive already holds its contents.
```

Asides may not contain ops or claim words, so searching a file for `delete` finds only real deletes.

## Forbidden words

Some words are errors, each with a suggested fix: modals ("may", "should"), contractions ("don't"), most pronouns ("they", "this"), quantifiers ("all", "every") and number words. Each one either hides what a sentence does or can be said more precisely another way.

## Claims

A sentence starting "This section" states guarantees about everything the section might do, on every path:

| Claim | Holds when |
| --- | --- |
| `never deletes from "/etc"` | No step can delete anything under `/etc` |
| `only writes to "/backup"` | Every write lands under `/backup` |
| `always reads from "/etc/app"` | Every run that finishes reads from `/etc/app` |
| `uploads at most 3 times` | No run uploads more than 3 times |

- A claim names an effect: `reads`, `writes`, `deletes`, `connects`, `listens` or `runs`. It can also name any op, such as `never uploads`.
- A claim's strings are absolute paths, or URLs when they have a scheme.
- Anything the checker can't pin down, such as a relative path or `run the command …`, could be anything, so claims about it fail rather than pass by accident.

## Checked descriptions

A vocabulary can turn descriptive words into **qualifiers**, whose meaning is checked:

```json
"qualifiers": [
  {"forms": ["backup"], "within": ["/backup"]},
  {"forms": ["log"], "from": ["/var/log"]}
],
"disjoint": [["production", "temporary"]]
```

- `within` is where a value must live, so `the backup file "/var/db/prod.db"` is an error.
- `from` is where its contents must come from, so calling the production database's contents "the log" is an error.
- `disjoint` pairs can't describe the same value.

For even stricter projects, set `"gloss": "strict"` in `lrep.json`. Then a sentence may contain only program words, qualifiers and "a", "an" and "the". Every other description goes in an aside.

## Projects and vocabularies

A project's `lrep.json` sits next to its programs:

```json
{
  "vocabularies": ["vocab/core/files.json", "vocab/core/net.json"],
  "language": "vocab/es/language.json",
  "gloss": "strict"
}
```

- **`vocabularies`** lists the JSON files that define ops, sorts, predicates, constants, units and qualifiers. Without `lrep.json`, the four core vocabularies (files, units, network, processes) load.
- **`language`** names the natural language's word tables; English is the default, and `vocab/es` is a Spanish demo.
- **`gloss`** is `loose` (the default) or `strict`.

Each op in a vocabulary declares its effects, such as "reads its object" or "writes to its `to` argument". Those declarations are what claims are checked against, and the runtime's sandbox enforces them. An op can also be defined by a section of lrep (a `body`), in which case its effects come from that section.

## Errors

Every error has a code, and most suggest a fix.

| Code | Meaning |
| --- | --- |
| E001 | Markdown outside what lrep allows, or a `:` not followed by a list |
| E002 | Text before the first heading, or two sections with one name |
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
| E023 | `then` right after a condition |
| E024 | An op not in its base form |
| E025 | A label the op doesn't take |
| E026 | A second unlabelled argument |
| E027 | A missing argument, or `only` without a resource |
| E028 | `Otherwise` or `If it fails` in the wrong place |
| E029 | A condition mixing `and` and `or` |
| E030 | A value of the wrong sort, or an invalid literal |
| E031 | `it` or `them` with nothing to refer to, or the wrong one |
| E032 | A description that matches no value, or several |
| E033 | A name declared twice |
| E034 | A qualifier that doesn't fit its value |
| E040 | A claim that doesn't hold |
| E042 | A claim word outside a "This section" sentence |
| E050 | A broken vocabulary or project file |
| W001 | A warning: a sentence over 25 words |

## The guarantee

`Lrep/Sound.lean` proves in Lean that if the checker accepts a `never` or `only` claim, no run of the section breaks it, on any path and any number of loop iterations, including runs that stop part-way. The one assumption is that each op does only what its vocabulary declares. The runtime enforces that assumption with a sandbox: an op that tries anything else is stopped.
