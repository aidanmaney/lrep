# Examples

Each program here passes `lrep check`. Run it on any of them to see which claims hold:

```bash
.lake/build/bin/lrep check examples/publish-report.lrep
```

Most examples use `examples/lrep.json`, which loads the core vocabularies and the example descriptive words in `vocab/examples/places.json` (such as `backup`, `log` and `public`).

| Example | What it shows |
| --- | --- |
| [`nightly/nightly.lrep`](nightly/nightly.lrep) | Four sections of nightly maintenance in strict mode: nested lists, a failure handler, asides, and every kind of claim |
| [`publish-report.lrep`](publish-report.lrep) | Uploading a file publicly, with a local backup if the upload fails |
| [`mirror-status.lrep`](mirror-status.lrep) | Fetching a page and uploading it, with an `at most` claim |
| [`deploy-site.lrep`](deploy-site.lrep) | Copying a release into place and serving it on one port |
| [`clean-uploads.lrep`](clean-uploads.lrep) | Deleting files that are empty or older than 2 days, and nothing else |
| [`backup-secrets.lrep`](backup-secrets.lrep) | Backing up a secret, with claims that it never leaves the machine |
| [`health-check.lrep`](health-check.lrep) | Calling an alert command when a check fails. Its only claim is `always connects`, because a `run` step could do anything |
| [`composite/retire-old-logs.lrep`](composite/retire-old-logs.lrep) | An op defined in lrep itself: `retire` compresses, uploads and deletes, and the claims see through it ([`vocab/retire.lrep`](composite/vocab/retire.lrep)) |
| [`es/copiar-registro.lrep`](es/copiar-registro.lrep) | The same language in Spanish |
| [`obsidian/`](obsidian/README.md) | A sketch of safe app plugins: an app-owned vocabulary, pure plugin ops, data-flow claims, an install prompt, and a malicious update that's caught |

## What the checker catches

The programs in [`caught/`](caught) each contain a mistake. `lrep check` rejects all of them.

### A claim the program breaks

[`caught/claims-too-little.lrep`](caught/claims-too-little.lrep) deletes empty files in `/etc/app` while claiming it never deletes from `/etc`:

```text
error[E040]: claim not satisfied: never deletes from "/etc"
 --> caught/claims-too-little.lrep:8
  |
8 | This section never deletes from "/etc".
  |              ^^^^^^^^^^^^^^^^^^^^^^^^^
3 | List the directory "/etc/app" as Settings.
  |                    ^^^^^^^^^^ deletes something under "/etc/app" (on line 6)
```

### Descriptions that don't match

[`caught/misleading-words.lrep`](caught/misleading-words.lrep) calls the production database a backup, deletes it as if it were temporary, and writes its contents out as a log:

```text
error[E034]: "backup" describes "/var/db/production.db", which is not within "/backup" or "s3://acme-backups"
error[E034]: "temporary" describes "/var/db/production.db", which is not within "/tmp" or "/var/tmp"
error[E034]: "log" describes a value whose contents come from "/var/db/production.db", not from "/var/log"
```

### A command that could do anything

[`caught/run-defeats-claims.lrep`](caught/run-defeats-claims.lrep) runs a shell command and claims it only writes to `/srv/site`. The checker can't know what the command does, so the claim fails:

```text
error[E040]: claim not satisfied: only writes to "/srv/site"
 --> caught/run-defeats-claims.lrep:5
  |
5 | This section only writes to "/srv/site".
  |              ^^^^^^^^^^^^^^^^^^^^^^^^^^
3 | Run the command "make site".
  | ^^^ writes to an unknown resource
```

### A verb the language doesn't know

[`caught/unknown-verb.lrep`](caught/unknown-verb.lrep) says "zip it", but no vocabulary defines `zip`. A clause without an op is an error, so the word can't silently do nothing:

```text
error[E020]: clause has no op; dropped as gloss: "zip"
 --> caught/unknown-verb.lrep:3
  |
3 | Open the file "/srv/reports/weekly.txt", zip it, then upload it to "https://cdn.example.com/weekly".
  |                                          ^^^^^^
  |
  = fix: "zip" is not an op in the loaded vocabularies
```
