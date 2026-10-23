// Starts `lrep lsp` for .lrep files. Highlighting comes from the server's semantic tokens,
// which follow the project's vocabularies; the bundled TextMate grammar covers the core ones
// until the server answers.
const vscode = require("vscode");
const { LanguageClient } = require("vscode-languageclient/node");

let client;

function activate() {
  const command = vscode.workspace.getConfiguration("lrep").get("serverPath") || "lrep";
  client = new LanguageClient(
    "lrep",
    "lrep",
    { command, args: ["lsp"] },
    { documentSelector: [{ scheme: "file", language: "lrep" }] }
  );
  client.start().catch((err) => {
    vscode.window.showErrorMessage(
      `lrep: couldn't start "${command} lsp" (${err.message}). Set lrep.serverPath to the lrep executable.`
    );
  });
}

function deactivate() {
  return client ? client.stop() : undefined;
}

module.exports = { activate, deactivate };
