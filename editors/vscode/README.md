# lrep for VS Code

Highlighting, diagnostics, hover and claim status for `.lrep` files, from `lrep lsp`.

- **Highlighting** comes from the server's semantic tokens, so it follows each project's vocabularies and language. The bundled TextMate grammar covers the core vocabularies while the server starts.
- **Diagnostics** appear as you type, with fixes, and a failing claim's witnesses as related locations.
- **Hover** shows what `it`, each name and each description refers to; each op's signature and effects; each qualifier's check, with where the value lies and where its contents came from; and each claim's status.
- **Code lenses** on each heading show the section's effects and claims.

## Install

Build lrep, then package and install the extension:

```bash
cd editors/vscode && npm install && npm run package
```

```bash
code --install-extension editors/vscode/lrep-0.1.0.vsix
```

If `lrep` isn't on your `PATH`, set `lrep.serverPath` to the executable, such as `~/src/lrep/.lake/build/bin/lrep`.

## Test

```bash
npm test
```

This runs the extension in your installed VS Code with a throwaway profile, and checks the language, hover, semantic tokens, code lenses and diagnostics.
