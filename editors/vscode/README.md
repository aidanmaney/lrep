# lrep for VS Code

This extension supports `.lrep` files using the `lrep lsp` language server.

- Words the checker reads are shown in bold; description is left plain, and asides are italic. Highlighting follows the project's own vocabularies. The bundled grammar is used while the server starts.
- Errors appear as you type, with suggested fixes. A failed claim links to the steps that break it.
- Hovering shows what `it`, a name or a description refers to; an op's arguments and effects; why a qualifier such as `backup` does or doesn't fit its value; and whether a claim holds.
- Above each heading, a line shows whether the section's claims hold and what the section reads, writes, deletes and connects to.

## Install

Build lrep first (`lake build` at the top of the repo). Then, in this folder, package and install the extension:

```bash
npm install && npm run package
code --install-extension lrep-0.2.0.vsix
```

If `lrep` isn't on your `PATH`, set `lrep.serverPath` to the executable, for example `/path/to/lrep/.lake/build/bin/lrep`.

## Test

```bash
npm test
```

This runs the extension in your installed VS Code, with a temporary profile, and checks highlighting, hover, the heading lines and errors.
