const vscode = require("vscode");
const { LanguageClient, TransportKind } = require("vscode-languageclient/node");
const path = require("path");

let client;

function createClient() {
  const serverCommand =
    process.env.DYLANG_LSP_PATH ||
    path.join(__dirname, "..", "..", "target", "debug", "saga-lsp");

  const serverOptions = {
    command: serverCommand,
    transport: TransportKind.stdio,
  };

  const clientOptions = {
    documentSelector: [{ scheme: "file", language: "saga" }],
  };

  return new LanguageClient(
    "saga-lsp",
    "saga Language Server",
    serverOptions,
    clientOptions,
  );
}

function activate(context) {
  client = createClient();
  client.start();

  const restartCommand = vscode.commands.registerCommand(
    "saga.restartServer",
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
