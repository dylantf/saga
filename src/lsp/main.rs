use std::sync::Mutex;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};

use dylang::typechecker;

mod checker;
mod definition;
mod diagnostics;
mod hover;
mod line_index;

use diagnostics::CheckResult;

struct Backend {
    client: Client,
    /// Cached base checker with prelude + module map loaded.
    base_checker: Mutex<Option<typechecker::Checker>>,
    /// Last check result, for hover/goto queries.
    last_check: Mutex<Option<(Url, CheckResult)>>,
}

impl Backend {
    fn get_checker(&self, uri: &Url) -> typechecker::Checker {
        let mut cached = self.base_checker.lock().unwrap_or_else(|e| e.into_inner());
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
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            diagnostics::check(checker, text)
        }));
        match result {
            Ok(result) => {
                let diagnostics = result.diagnostics.clone();
                let mut last = self.last_check.lock().unwrap_or_else(|e| e.into_inner());
                *last = Some((uri, result));
                diagnostics
            }
            Err(e) => {
                eprintln!("[check_file] panic: {:?}", e);
                vec![]
            }
        }
    }

    /// Clone the last check result out of the lock to avoid holding it
    /// across async boundaries (which would deadlock with did_open).
    fn snapshot(&self) -> Option<(Url, typechecker::Checker, Vec<dylang::ast::Decl>, line_index::LineIndex)> {
        let last = self.last_check.lock().ok()?;
        let (uri, result) = last.as_ref()?;
        Some((
            uri.clone(),
            result.checker.clone(),
            result.program.clone()?,
            result.line_index.clone(),
        ))
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
                definition_provider: Some(OneOf::Left(true)),
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
        let Some((_uri, checker, program, line_index)) = self.snapshot() else {
            return Ok(None);
        };

        let position = params.text_document_position_params.position;
        let offset = line_index.line_col_to_offset(position.line as usize, position.character as usize);

        let Some(name) = hover::find_name_at_offset(&program, offset) else {
            return Ok(None);
        };

        let Some(type_str) = hover::type_at_name(&checker, &name, &program) else {
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

    async fn goto_definition(
        &self,
        params: GotoDefinitionParams,
    ) -> Result<Option<GotoDefinitionResponse>> {
        let Some((uri, checker, program, line_index)) = self.snapshot() else {
            return Ok(None);
        };

        let position = params.text_document_position_params.position;
        let offset =
            line_index.line_col_to_offset(position.line as usize, position.character as usize);

        let Some(name) = hover::find_name_at_offset(&program, offset) else {
            return Ok(None);
        };

        let Some(def_result) = definition::find_definition(&program, &name, &checker) else {
            return Ok(None);
        };

        // For cross-module definitions, build a line index for the target file
        let (target_uri, target_line_index);
        if let Some(ref file_path) = def_result.file_path {
            target_uri = Url::from_file_path(file_path)
                .map_err(|_| tower_lsp::jsonrpc::Error::internal_error())?;
            let source = std::fs::read_to_string(file_path)
                .map_err(|_| tower_lsp::jsonrpc::Error::internal_error())?;
            target_line_index = Some(line_index::LineIndex::new(&source));
        } else {
            target_uri = uri;
            target_line_index = None;
        }

        let li = target_line_index.as_ref().unwrap_or(&line_index);
        let (start_line, start_col) = li.offset_to_line_col(def_result.span.start);
        let (end_line, end_col) = li.offset_to_line_col(def_result.span.end);

        Ok(Some(GotoDefinitionResponse::Scalar(Location {
            uri: target_uri,
            range: Range {
                start: Position::new(start_line as u32, start_col as u32),
                end: Position::new(end_line as u32, end_col as u32),
            },
        })))
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
