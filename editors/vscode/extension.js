const vscode = require("vscode");
const { LanguageClient, TransportKind } = require("vscode-languageclient/node");
const path = require("path");

let client;

function createClient() {
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

  return new LanguageClient(
    "dylang-lsp",
    "dylang Language Server",
    serverOptions,
    clientOptions,
  );
}

function activate(context) {
  client = createClient();
  client.start();

  const restartCommand = vscode.commands.registerCommand(
    "dylang.restartServer",
    async () => {
      if (client) {
        await client.stop();
      }
      client = createClient();
      await client.start();
    },
  );

  context.subscriptions.push(restartCommand);
}

function deactivate() {
  if (client) {
    return client.stop();
  }
}

module.exports = { activate, deactivate };
