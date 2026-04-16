const vscode = require("vscode");
const path = require("path");
const fs = require("fs");
const os = require("os");
const { LanguageClient, TransportKind } = require("vscode-languageclient/node");

let client;

function findServerCommand() {
  const config = vscode.workspace.getConfiguration("saga");
  const configured = config.get("lsp.path");
  if (configured) return configured;

  // Check ~/.saga/bin/saga-lsp as a fallback since VS Code on macOS
  // may not inherit the user's shell PATH
  const homeBin = path.join(os.homedir(), ".saga", "bin", "saga-lsp");
  if (fs.existsSync(homeBin)) return homeBin;

  return "saga-lsp";
}

function createClient() {
  const serverCommand = findServerCommand();

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
