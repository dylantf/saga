use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};

use dylang::{lexer, parser, typechecker};

mod line_index;
use line_index::LineIndex;

struct Backend {
    client: Client,
}

impl Backend {
    fn check_and_report(&self, _uri: Url, text: &str) -> Vec<Diagnostic> {
        let line_index = LineIndex::new(text);

        let tokens = match lexer::Lexer::new(text).lex() {
            Ok(tokens) => tokens,
            Err(e) => {
                let (line, col) = line_index.offset_to_line_col(e.pos);
                return vec![Diagnostic {
                    range: Range {
                        start: Position::new(line as u32, col as u32),
                        end: Position::new(line as u32, col as u32 + 1),
                    },
                    severity: Some(DiagnosticSeverity::ERROR),
                    message: e.message,
                    ..Default::default()
                }];
            }
        };

        let mut program = match parser::Parser::new(tokens).parse_program() {
            Ok(program) => program,
            Err(e) => {
                let (line, col) = line_index.offset_to_line_col(e.span.start);
                return vec![Diagnostic {
                    range: Range {
                        start: Position::new(line as u32, col as u32),
                        end: Position::new(line as u32, col as u32 + 1),
                    },
                    severity: Some(DiagnosticSeverity::ERROR),
                    message: e.message,
                    ..Default::default()
                }];
            }
        };

        dylang::derive::expand_derives(&mut program);

        let mut checker = typechecker::Checker::new();
        let prelude_src = include_str!("../stdlib/prelude.dy");
        let prelude_tokens = lexer::Lexer::new(prelude_src).lex().expect("prelude lex");
        let mut prelude_program = parser::Parser::new(prelude_tokens)
            .parse_program()
            .expect("prelude parse");
        dylang::derive::expand_derives(&mut prelude_program);
        if let Err(e) = checker.check_program(&prelude_program) {
            return vec![Diagnostic {
                range: Range::default(),
                severity: Some(DiagnosticSeverity::ERROR),
                message: format!("Prelude error: {}", e),
                ..Default::default()
            }];
        }

        match checker.check_program(&program) {
            Ok(()) => vec![],
            Err(e) => {
                let (start_line, start_col) = if let Some(span) = e.span {
                    line_index.offset_to_line_col(span.start)
                } else {
                    (0, 0)
                };
                let (end_line, end_col) = if let Some(span) = e.span {
                    line_index.offset_to_line_col(span.end)
                } else {
                    (0, 1)
                };
                vec![Diagnostic {
                    range: Range {
                        start: Position::new(start_line as u32, start_col as u32),
                        end: Position::new(end_line as u32, end_col as u32),
                    },
                    severity: Some(DiagnosticSeverity::ERROR),
                    message: e.message,
                    ..Default::default()
                }]
            }
        }
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
        let text = &params.text_document.text;
        let diagnostics = self.check_and_report(uri.clone(), text);
        self.client
            .publish_diagnostics(uri, diagnostics, None)
            .await;
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        let uri = params.text_document.uri.clone();
        if let Some(change) = params.content_changes.into_iter().last() {
            let diagnostics = self.check_and_report(uri.clone(), &change.text);
            self.client
                .publish_diagnostics(uri, diagnostics, None)
                .await;
        }
    }

    async fn did_save(&self, params: DidSaveTextDocumentParams) {
        if let Some(text) = &params.text {
            let uri = params.text_document.uri.clone();
            let diagnostics = self.check_and_report(uri.clone(), text);
            self.client
                .publish_diagnostics(uri, diagnostics, None)
                .await;
        }
    }

    async fn hover(&self, _params: HoverParams) -> Result<Option<Hover>> {
        // TODO: look up type at cursor position
        Ok(None)
    }
}

#[tokio::main]
async fn main() {
    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    let (service, socket) = LspService::new(|client| Backend { client });
    Server::new(stdin, stdout, socket).serve(service).await;
}
