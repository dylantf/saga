use std::sync::Mutex;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};

use dylang::typechecker;

mod checker;
mod diagnostics;
mod hover;
mod line_index;

use diagnostics::CheckResult;

struct Backend {
    client: Client,
    /// Cached base checker with prelude + module map loaded.
    base_checker: Mutex<Option<typechecker::Checker>>,
    /// Last successful check result per file, for hover queries.
    last_check: Mutex<Option<(Url, CheckResult)>>,
}

impl Backend {
    fn get_checker(&self, uri: &Url) -> typechecker::Checker {
        let mut cached = self.base_checker.lock().unwrap();
        if let Some(base) = &*cached {
            return base.clone();
        }

        let project_root = uri
            .to_file_path()
            .ok()
            .and_then(|p| p.parent().map(|d| d.to_path_buf()))
            .and_then(|d| checker::find_project_root(&d));

        let base = checker::make_checker(project_root);
        *cached = Some(base.clone());
        base
    }

    fn check_file(&self, uri: Url, text: &str) -> Vec<Diagnostic> {
        let checker = self.get_checker(&uri);
        let result = diagnostics::check(checker, text);
        let diagnostics = result.diagnostics.clone();

        let mut last = self.last_check.lock().unwrap();
        *last = Some((uri, result));

        diagnostics
    }
}

#[tower_lsp::async_trait]
impl LanguageServer for Backend {
    async fn initialize(&self, _: InitializeParams) -> Result<InitializeResult> {
        Ok(InitializeResult {
            capabilities: ServerCapabilities {
                text_document_sync: Some(TextDocumentSyncCapability::Kind(
                    TextDocumentSyncKind::FULL,
                )),
                hover_provider: Some(HoverProviderCapability::Simple(true)),
                ..Default::default()
            },
            ..Default::default()
        })
    }

    async fn initialized(&self, _: InitializedParams) {
        self.client
            .log_message(MessageType::INFO, "dylang LSP initialized")
            .await;
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        let uri = params.text_document.uri.clone();
        let diagnostics = self.check_file(uri.clone(), &params.text_document.text);
        self.client
            .publish_diagnostics(uri, diagnostics, None)
            .await;
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        let uri = params.text_document.uri.clone();
        if let Some(change) = params.content_changes.into_iter().last() {
            let diagnostics = self.check_file(uri.clone(), &change.text);
            self.client
                .publish_diagnostics(uri, diagnostics, None)
                .await;
        }
    }

    async fn did_save(&self, params: DidSaveTextDocumentParams) {
        if let Some(text) = &params.text {
            let uri = params.text_document.uri.clone();
            let diagnostics = self.check_file(uri.clone(), text);
            self.client
                .publish_diagnostics(uri, diagnostics, None)
                .await;
        }
    }

    async fn hover(&self, params: HoverParams) -> Result<Option<Hover>> {
        let last = self.last_check.lock().unwrap();
        let Some((ref _uri, ref result)) = *last else {
            return Ok(None);
        };

        let Some(ref program) = result.program else {
            return Ok(None);
        };

        let position = params.text_document_position_params.position;
        let offset = result
            .line_index
            .line_col_to_offset(position.line as usize, position.character as usize);

        let Some(name) = hover::find_name_at_offset(program, offset) else {
            return Ok(None);
        };

        let Some(type_str) = hover::type_at_name(&result.checker, &name, program) else {
            return Ok(None);
        };

        Ok(Some(Hover {
            contents: HoverContents::Markup(MarkupContent {
                kind: MarkupKind::Markdown,
                value: format!("```dylang\n{}: {}\n```", name, type_str),
            }),
            range: None,
        }))
    }
}

#[tokio::main]
async fn main() {
    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    let (service, socket) = LspService::new(|client| Backend {
        client,
        base_checker: Mutex::new(None),
        last_check: Mutex::new(None),
    });
    Server::new(stdin, stdout, socket).serve(service).await;
}
