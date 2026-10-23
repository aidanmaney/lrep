// Runs the extension inside the installed VS Code, with a throwaway profile, against a
// copy of the nightly example and a deliberately broken copy.
const fs = require("fs");
const os = require("os");
const path = require("path");
const { runTests } = require("@vscode/test-electron");

const repo = path.resolve(__dirname, "../../..");

async function main() {
  const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "lrep-vscode-"));
  const ws = path.join(tmp, "workspace");
  fs.mkdirSync(ws);
  const vocabs = ["files", "units", "net", "proc"].map((v) => `${repo}/vocab/core/${v}.json`)
    .concat([`${repo}/vocab/examples/places.json`]);
  fs.writeFileSync(path.join(ws, "lrep.json"), JSON.stringify({ vocabularies: vocabs, gloss: "strict" }));
  const nightly = fs.readFileSync(path.join(repo, "examples/nightly/nightly.lrep"), "utf8");
  fs.writeFileSync(path.join(ws, "nightly.lrep"), nightly);
  fs.writeFileSync(path.join(ws, "broken.lrep"),
    nightly.replace('connect to "https://hooks.example.com/oncall"', 'run the command "page-oncall logs"'));
  const user = path.join(tmp, "user");
  fs.mkdirSync(path.join(user, "User"), { recursive: true });
  fs.writeFileSync(path.join(user, "User", "settings.json"),
    JSON.stringify({ "lrep.serverPath": path.join(repo, ".lake/build/bin/lrep") }));
  process.env.LREP_TEST_WORKSPACE = ws;
  await runTests({
    vscodeExecutablePath: "/Applications/Visual Studio Code.app/Contents/MacOS/Code",
    extensionDevelopmentPath: path.resolve(__dirname, ".."),
    extensionTestsPath: path.join(__dirname, "suite.js"),
    launchArgs: [ws, "--disable-extensions", "--user-data-dir", user,
                 "--extensions-dir", path.join(tmp, "extensions"), "--skip-welcome", "--skip-release-notes"],
  });
}

main().catch((err) => { console.error(err); process.exit(1); });
