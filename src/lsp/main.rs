use std::sync::Mutex;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};

use dylang::typechecker;

mod checker;
mod completion;
mod definition;
mod diagnostics;
mod document_symbol;
mod hover;
mod line_index;
mod signature_help;

use diagnostics::CheckSnapshot;

struct Backend {
    client: Client,
    /// Cached base checker per project root. Key is the project root path (or empty for no project).
    base_checkers: Mutex<std::collections::HashMap<String, typechecker::Checker>>,
    /// Last check result per file, for hover/goto queries.
    last_check: Mutex<std::collections::HashMap<Url, CheckSnapshot>>,
}

impl Backend {
    fn get_checker(&self, uri: &Url) -> typechecker::Checker {
        let project_root = uri
            .to_file_path()
            .ok()
            .and_then(|p| p.parent().map(|d| d.to_path_buf()))
            .and_then(|d| checker::find_project_root(&d));

        let cache_key = project_root
            .as_ref()
            .map(|p| p.to_string_lossy().to_string())
            .unwrap_or_default();

        let mut cached = self.base_checkers.lock().unwrap_or_else(|e| e.into_inner());
        if let Some(base) = cached.get(&cache_key) {
            return base.clone();
        }

        let base = checker::make_checker(project_root);
        cached.insert(cache_key, base.clone());
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
                last.insert(uri, result);
                diagnostics
            }
            Err(e) => {
                eprintln!("[check_file] panic: {:?}", e);
                vec![]
            }
        }
    }

    /// Clone the check result for a specific URI out of the lock to avoid holding it
    /// across async boundaries (which would deadlock with did_open).
    fn snapshot(&self, uri: &Url) -> Option<(typechecker::CheckResult, Vec<dylang::ast::Decl>, line_index::LineIndex, String)> {
        let last = self.last_check.lock().ok()?;
        let result = last.get(uri)?;
        Some((
            result.tc_result.clone(),
            result.program.clone()?,
            result.line_index.clone(),
            result.source.clone(),
        ))
    }
}

/// Resolve a span's location: returns (URI, LineIndex) for a span that lives in `module_name`
/// (None = same file as `current_uri`).
fn resolve_span_location(
    current_uri: &Url,
    current_li: &line_index::LineIndex,
    module_name: Option<&str>,
    tc_result: &dylang::typechecker::CheckResult,
) -> tower_lsp::jsonrpc::Result<(Url, line_index::LineIndex)> {
    if let Some(module) = module_name
        && let Some(file_path) = tc_result.module_map().and_then(|m| m.get(module))
    {
        let target_uri = Url::from_file_path(file_path)
            .map_err(|_| tower_lsp::jsonrpc::Error::internal_error())?;
        let source = std::fs::read_to_string(file_path)
            .map_err(|_| tower_lsp::jsonrpc::Error::internal_error())?;
        return Ok((target_uri, line_index::LineIndex::new(&source)));
    }
    Ok((current_uri.clone(), current_li.clone()))
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
                completion_provider: Some(CompletionOptions {
                    trigger_characters: Some(vec![".".to_string()]),
                    ..Default::default()
                }),
                references_provider: Some(OneOf::Left(true)),
                document_symbol_provider: Some(OneOf::Left(true)),
                signature_help_provider: Some(SignatureHelpOptions {
                    trigger_characters: Some(vec![" ".to_string()]),
                    retrigger_characters: None,
                    work_done_progress_options: Default::default(),
                }),
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
        eprintln!("[did_open] {}", uri);
        let diagnostics = self.check_file(uri.clone(), &params.text_document.text);
        eprintln!("[did_open] {} diagnostics", diagnostics.len());
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
        let uri = params.text_document_position_params.text_document.uri.clone();
        let Some((tc_result, program, line_index, _source)) = self.snapshot(&uri) else {
            return Ok(None);
        };

        let position = params.text_document_position_params.position;
        let offset = line_index.line_col_to_offset(position.line as usize, position.character as usize);

        let Some((name, span, node_id)) = hover::find_name_at_offset(&program, offset) else {
            return Ok(None);
        };

        let Some(type_str) = hover::type_at_name(&tc_result, &name, Some(&span), node_id.as_ref(), &program) else {
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
        let uri = params.text_document_position_params.text_document.uri.clone();
        let Some((tc_result, program, line_index, _source)) = self.snapshot(&uri) else {
            return Ok(None);
        };

        let position = params.text_document_position_params.position;
        let offset =
            line_index.line_col_to_offset(position.line as usize, position.character as usize);

        let Some((name, span, _node_id)) = hover::find_name_at_offset(&program, offset) else {
            return Ok(None);
        };

        // Level 1: effect call -> handler arm (op! -> the arm that handles it)
        if let Some((arm_span, arm_module)) = tc_result.effect_call_targets.get(&span) {
            let (target_uri, target_li) = resolve_span_location(&uri, &line_index, arm_module.as_deref(), &tc_result)?;
            let (start_line, start_col) = target_li.offset_to_line_col(arm_span.start);
            let (end_line, end_col) = target_li.offset_to_line_col(arm_span.end);
            return Ok(Some(GotoDefinitionResponse::Scalar(Location {
                uri: target_uri,
                range: Range {
                    start: Position::new(start_line as u32, start_col as u32),
                    end: Position::new(end_line as u32, end_col as u32),
                },
            })));
        }

        // Level 2: handler arm -> effect op definition
        if let Some((op_def_span, op_module)) = tc_result.handler_arm_targets.get(&span) {
            let (target_uri, target_li) = resolve_span_location(&uri, &line_index, op_module.as_deref(), &tc_result)?;
            let (start_line, start_col) = target_li.offset_to_line_col(op_def_span.start);
            let (end_line, end_col) = target_li.offset_to_line_col(op_def_span.end);
            return Ok(Some(GotoDefinitionResponse::Scalar(Location {
                uri: target_uri,
                range: Range {
                    start: Position::new(start_line as u32, start_col as u32),
                    end: Position::new(end_line as u32, end_col as u32),
                },
            })));
        }

        // Handler name in `with handler_name`: look it up via the typechecker's handler table,
        // which knows the source module even if the handler isn't in the explicit exposing list.
        if let Some(handler_info) = tc_result.handlers.get(&name) {
            let source_module = handler_info.source_module.as_deref();
            let (target_uri, target_li) = resolve_span_location(&uri, &line_index, source_module, &tc_result)?;
            // Find the HandlerDef span in the target program
            let target_program = if let Some(m) = source_module {
                tc_result.programs().get(m).map(|p| p.as_slice())
            } else {
                Some(program.as_slice())
            };
            if let Some(prog) = target_program
                && let Some(def) = definition::find_definition(prog, &name, &tc_result)
            {
                let (start_line, start_col) = target_li.offset_to_line_col(def.span.start);
                let (end_line, end_col) = target_li.offset_to_line_col(def.span.end);
                return Ok(Some(GotoDefinitionResponse::Scalar(Location {
                    uri: target_uri,
                    range: Range {
                        start: Position::new(start_line as u32, start_col as u32),
                        end: Position::new(end_line as u32, end_col as u32),
                    },
                })));
            }
        }

        let Some(def_result) = definition::find_definition(&program, &name, &tc_result) else {
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

    async fn completion(
        &self,
        params: CompletionParams,
    ) -> Result<Option<CompletionResponse>> {
        let uri = params.text_document_position.text_document.uri.clone();
        let Some((tc_result, program, line_index, source)) = self.snapshot(&uri) else {
            return Ok(None);
        };

        let position = params.text_document_position.position;
        let offset =
            line_index.line_col_to_offset(position.line as usize, position.character as usize);

        let prefix = completion::extract_prefix(&source, offset);
        let items = completion::collect_completions(&tc_result, prefix, &program);

        Ok(Some(CompletionResponse::Array(items)))
    }

    async fn document_symbol(
        &self,
        params: DocumentSymbolParams,
    ) -> Result<Option<DocumentSymbolResponse>> {
        let uri = params.text_document.uri.clone();
        let Some((_tc_result, program, line_index, _source)) = self.snapshot(&uri) else {
            return Ok(None);
        };

        let mut symbols = document_symbol::collect_symbols(&program, &line_index);
        // Fill in the real URI (collect_symbols uses a placeholder)
        for sym in &mut symbols {
            sym.location.uri = uri.clone();
        }

        Ok(Some(DocumentSymbolResponse::Flat(symbols)))
    }

    async fn signature_help(
        &self,
        params: SignatureHelpParams,
    ) -> Result<Option<SignatureHelp>> {
        let uri = params.text_document_position_params.text_document.uri.clone();
        let Some((tc_result, program, line_index, source)) = self.snapshot(&uri) else {
            return Ok(None);
        };

        let position = params.text_document_position_params.position;
        let offset =
            line_index.line_col_to_offset(position.line as usize, position.character as usize);

        // Only proceed if there's an identifier-like token before the cursor.
        // When triggered by space, cursor is after the space, so skip whitespace backwards.
        if offset > 0 {
            let bytes = source.as_bytes();
            let mut check_pos = offset - 1;
            while check_pos > 0 && bytes[check_pos] == b' ' {
                check_pos -= 1;
            }
            let prev = bytes[check_pos];
            if !prev.is_ascii_alphanumeric() && prev != b'_' && prev != b'\'' && prev != b')' {
                return Ok(None);
            }
        }

        let (func_name, active_param) =
            if let Some(found) = signature_help::find_active_call(&program, offset) {
                found
            } else if let Some(found) = signature_help::find_call_near(&program, &source, offset) {
                found
            } else {
                // No App chain found -- check if cursor is after `<name> ` (no arg yet).
                match signature_help::ident_before_spaces(&source, offset) {
                    Some(name) => (name, 0),
                    None => return Ok(None),
                }
            };

        let Some(mut sig_info) = signature_help::build_signature(&func_name, &program, &tc_result)
        else {
            return Ok(None);
        };

        sig_info.active_parameter = Some(active_param as u32);

        Ok(Some(SignatureHelp {
            signatures: vec![sig_info],
            active_signature: Some(0),
            active_parameter: None, // set per-signature above
        }))
    }

    async fn references(
        &self,
        params: ReferenceParams,
    ) -> Result<Option<Vec<Location>>> {
        let uri = params.text_document_position.text_document.uri.clone();
        let Some((tc_result, program, line_index, _source)) = self.snapshot(&uri) else {
            return Ok(None);
        };

        let position = params.text_document_position.position;
        let offset =
            line_index.line_col_to_offset(position.line as usize, position.character as usize);

        let Some((_name, _span, node_id)) = hover::find_name_at_offset(&program, offset) else {
            return Ok(None);
        };

        // Determine the definition NodeId.
        // If cursor is on a usage expression, look up the resolution map.
        // If cursor is on a definition, the node_id itself is the definition.
        let def_id = if let Some(expr_id) = node_id {
            if let Some(&did) = tc_result.references.get(&expr_id) {
                // Cursor is on a usage -> follow to definition
                did
            } else {
                // Cursor might be on a definition itself (e.g., clicking the function name
                // in a FunAnnotation). Check if anything references this node.
                expr_id
            }
        } else {
            // No expr NodeId (Pat binding). Find the definition by looking up the
            // env's def_id for this name.
            if let Some(did) = tc_result.env.def_id(&_name) {
                did
            } else {
                return Ok(None);
            }
        };

        // Collect all usage spans that resolve to this definition.
        let mut locations = Vec::new();
        for (usage_id, &ref_def_id) in &tc_result.references {
            if ref_def_id == def_id {
                if let Some(&usage_span) = tc_result.node_spans.get(usage_id) {
                    let (start_line, start_col) = line_index.offset_to_line_col(usage_span.start);
                    let (end_line, end_col) = line_index.offset_to_line_col(usage_span.end);
                    locations.push(Location {
                        uri: uri.clone(),
                        range: Range {
                            start: Position::new(start_line as u32, start_col as u32),
                            end: Position::new(end_line as u32, end_col as u32),
                        },
                    });
                }
            }
        }

        // Include the definition site itself if requested.
        if params.context.include_declaration {
            if let Some(&def_span) = tc_result.node_spans.get(&def_id) {
                let (start_line, start_col) = line_index.offset_to_line_col(def_span.start);
                let (end_line, end_col) = line_index.offset_to_line_col(def_span.end);
                locations.push(Location {
                    uri: uri.clone(),
                    range: Range {
                        start: Position::new(start_line as u32, start_col as u32),
                        end: Position::new(end_line as u32, end_col as u32),
                    },
                });
            }
        }

        if locations.is_empty() {
            Ok(None)
        } else {
            Ok(Some(locations))
        }
    }
}

#[tokio::main]
async fn main() {
    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    let (service, socket) = LspService::new(|client| Backend {
        client,
        base_checkers: Mutex::new(std::collections::HashMap::new()),
        last_check: Mutex::new(std::collections::HashMap::new()),
    });
    Server::new(stdin, stdout, socket).serve(service).await;
}
