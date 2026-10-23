// Checks what a user would see: the language, diagnostics, hover, semantic tokens and lenses.
const path = require("path");
const vscode = require("vscode");

const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

async function waitFor(what, fn, ms = 20000) {
  const end = Date.now() + ms;
  for (;;) {
    const v = await fn();
    if (v) return v;
    if (Date.now() > end) throw new Error(`timed out waiting for ${what}`);
    await sleep(250);
  }
}

function hoverText(hovers) {
  return hovers.flatMap((h) => h.contents.map((c) => (typeof c === "string" ? c : c.value))).join("\n");
}

async function run() {
  const ws = process.env.LREP_TEST_WORKSPACE;
  const checks = [];
  const check = (name, ok, detail = "") => checks.push({ name, ok: !!ok, detail });

  const doc = await vscode.workspace.openTextDocument(path.join(ws, "nightly.lrep"));
  await vscode.window.showTextDocument(doc);
  check("language is lrep", doc.languageId === "lrep", doc.languageId);

  const at = (line, word) => new vscode.Position(line - 1, doc.lineAt(line - 1).text.indexOf(word) + 1);
  const settings = await waitFor("hover", async () => {
    const h = await vscode.commands.executeCommand("vscode.executeHoverProvider", doc.uri, at(15, "Settings"));
    return h && h.length ? hoverText(h) : null;
  });
  check("hover on a name", settings.includes("refers to the result of `read` on line 14"), settings);
  const qual = hoverText(await vscode.commands.executeCommand("vscode.executeHoverProvider", doc.uri, at(7, "log")));
  check("hover on a qualifier", qual.includes("somewhere under \"/var/log/app\"") && qual.includes("✓"), qual);

  const legend = await vscode.commands.executeCommand("vscode.provideDocumentSemanticTokensLegend", doc.uri);
  const tokens = await vscode.commands.executeCommand("vscode.provideDocumentSemanticTokens", doc.uri);
  const n = tokens ? tokens.data.length / 5 : 0;
  check("semantic tokens", legend && legend.tokenTypes.includes("lrepProgram") && n > 50, `${n} tokens`);

  const lenses = await vscode.commands.executeCommand("vscode.executeCodeLensProvider", doc.uri);
  const titles = (lenses || []).map((l) => l.command && l.command.title).filter(Boolean);
  check("code lenses", titles.some((t) => /^✓ \d+ claims hold$/.test(t)), titles.slice(0, 2).join(" | "));

  const broken = await vscode.workspace.openTextDocument(path.join(ws, "broken.lrep"));
  await vscode.window.showTextDocument(broken);
  const diags = await waitFor("diagnostics", async () => {
    const d = vscode.languages.getDiagnostics(broken.uri);
    return d.length ? d : null;
  });
  check("diagnostics", diags.some((d) => d.code === "E040"), diags.map((d) => d.code).join(", "));

  for (const c of checks) console.log(`${c.ok ? "ok  " : "FAIL"}  ${c.name}${c.detail ? `: ${c.detail.replace(/\n/g, " ⏎ ").slice(0, 160)}` : ""}`);
  if (checks.some((c) => !c.ok)) throw new Error("extension checks failed");
}

module.exports = { run };
