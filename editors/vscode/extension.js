const { LanguageClient, TransportKind } = require("vscode-languageclient/node");
const path = require("path");

let client;

function activate(context) {
  // Look for dylang-lsp in PATH, or use a local debug build
  const serverCommand =
    process.env.DYLANG_LSP_PATH ||
    path.join(__dirname, "..", "..", "target", "debug", "dylang-lsp");

  const serverOptions = {
    command: serverCommand,
    transport: TransportKind.stdio,
  };

  const clientOptions = {
    documentSelector: [{ scheme: "file", language: "dylang" }],
  };

  client = new LanguageClient(
    "dylang-lsp",
    "dylang Language Server",
    serverOptions,
    clientOptions,
  );

  client.start();
}

function deactivate() {
  if (client) {
    return client.stop();
  }
}

module.exports = { activate, deactivate };
