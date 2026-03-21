use std::sync::{Arc, Mutex};
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};

use dylang::typechecker;

mod checker;
mod code_action;
mod completion;
mod definition;
mod diagnostics;
mod document_symbol;
mod hover;
mod line_index;
mod signature_help;
mod symbol_index;

use diagnostics::CheckSnapshot;

struct Backend {
    client: Client,
    /// Cached base checker per project root. Key is the project root path (or empty for no project).
    base_checkers: Mutex<std::collections::HashMap<String, typechecker::Checker>>,
    /// Last check result per file, for hover/goto queries.
    last_check: Mutex<std::collections::HashMap<Url, Arc<CheckSnapshot>>>,
    /// Latest document text per file, updated immediately on did_change/did_open.
    /// Used by completion to see the current editor text, which may be ahead of
    /// the last check snapshot due to async processing.
    document_texts: Mutex<std::collections::HashMap<Url, String>>,
    /// Project-wide symbol reference index for cross-module find-references.
    symbol_index: Mutex<symbol_index::SymbolIndex>,
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
                let snap = Arc::new(result);
                eprintln!("[check_file] program={}", snap.program.is_some());
                // Update the symbol index with references from this file.
                if let Some(ref program) = snap.program {
                    let mut idx = self.symbol_index.lock().unwrap_or_else(|e| e.into_inner());
                    idx.update_file(&uri, &snap.tc_result, program, &snap.line_index, &snap.source);
                }
                let mut last = self.last_check.lock().unwrap_or_else(|e| e.into_inner());
                last.insert(uri, snap);
                diagnostics
            }
            Err(e) => {
                eprintln!("[check_file] panic: {:?}", e);
                vec![]
            }
        }
    }

    /// Get a shared reference to the check result for a specific URI.
    /// Clones the Arc (cheap pointer copy) to avoid holding the lock across async boundaries.
    fn snapshot(&self, uri: &Url) -> Option<Arc<CheckSnapshot>> {
        let last = self.last_check.lock().ok()?;
        let snap = last.get(uri)?;
        snap.program.as_ref()?;
        Some(Arc::clone(snap))
    }

    /// Get the latest editor text for a file (updated immediately in did_change).
    fn document_text(&self, uri: &Url) -> Option<String> {
        let texts = self.document_texts.lock().ok()?;
        texts.get(uri).cloned()
    }
}

/// Resolve a span's location: returns (URI, LineIndex) for a span that lives in `module_name`
/// (None = same file as `current_uri`).
fn resolve_span_location(
    current_uri: &Url,
    current_li: &line_index::LineIndex,
    current_source: &str,
    module_name: Option<&str>,
    tc_result: &dylang::typechecker::CheckResult,
) -> tower_lsp::jsonrpc::Result<(Url, line_index::LineIndex, String)> {
    if let Some(module) = module_name
        && let Some(file_path) = tc_result.module_map().and_then(|m| m.get(module))
    {
        let target_uri = Url::from_file_path(file_path)
            .map_err(|_| tower_lsp::jsonrpc::Error::internal_error())?;
        let source = std::fs::read_to_string(file_path)
            .map_err(|_| tower_lsp::jsonrpc::Error::internal_error())?;
        let li = line_index::LineIndex::new(&source);
        return Ok((target_uri, li, source));
    }
    Ok((current_uri.clone(), current_li.clone(), current_source.to_string()))
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
                code_action_provider: Some(CodeActionProviderCapability::Simple(true)),
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
        self.document_texts
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .insert(uri.clone(), params.text_document.text.clone());
        let diagnostics = self.check_file(uri.clone(), &params.text_document.text);
        self.client
            .publish_diagnostics(uri, diagnostics, None)
            .await;
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        let uri = params.text_document.uri.clone();
        if let Some(change) = params.content_changes.into_iter().last() {
            self.document_texts
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .insert(uri.clone(), change.text.clone());
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
        let uri = params
            .text_document_position_params
            .text_document
            .uri
            .clone();
        let Some(snap) = self.snapshot(&uri) else {
            return Ok(None);
        };
        let tc_result = &snap.tc_result;
        let program = snap.program.as_ref().unwrap();
        let line_index = &snap.line_index;


        let position = params.text_document_position_params.position;
        let offset =
            line_index.line_col_to_offset(position.line as usize, position.character as usize, &snap.source);

        let Some((name, span, node_id)) = hover::find_name_at_offset(program, offset) else {
            return Ok(None);
        };

        // Handlers get special display: "handler name for Effect1, Effect2"
        if let Some(handler_info) = tc_result.handlers.get(&name) {
            let effects = handler_info.effects.join(", ");
            return Ok(Some(Hover {
                contents: HoverContents::Markup(MarkupContent {
                    kind: MarkupKind::Markdown,
                    value: format!("```dylang\nhandler {} for {}\n```", name, effects),
                }),
                range: None,
            }));
        }

        // Effect operation: show signature from the effect definition
        // Check if this name matches an effect op (and cursor is inside a handler)
        for (effect_name, info) in &tc_result.effects {
            for op in &info.ops {
                if op.name == name {
                    let params_display: Vec<String> = op
                        .params
                        .iter()
                        .map(|(label, ty)| {
                            let resolved = tc_result.sub.apply(ty);
                            if label.starts_with('_') {
                                format!("{}", resolved)
                            } else {
                                format!("({}: {})", label, resolved)
                            }
                        })
                        .collect();
                    let ret = tc_result.sub.apply(&op.return_type);
                    let sig = if params_display.is_empty() {
                        format!("{}.{} : () -> {}", effect_name, name, ret)
                    } else {
                        format!(
                            "{}.{} : {} -> {}",
                            effect_name,
                            name,
                            params_display.join(" -> "),
                            ret
                        )
                    };
                    return Ok(Some(Hover {
                        contents: HoverContents::Markup(MarkupContent {
                            kind: MarkupKind::Markdown,
                            value: format!("```dylang\n{}\n```", sig),
                        }),
                        range: None,
                    }));
                }
            }
        }

        // Type/record/effect/trait definition summary.
        // Check this before type_at_name for uppercase names in type position (no node_id),
        // since record names also exist as constructors and type_at_name would show the
        // constructor signature instead of the definition.
        if node_id.is_none()
            && name.starts_with(|c: char| c.is_uppercase())
            && let Some(summary) = hover::type_definition_summary(tc_result, &name, program)
        {
            return Ok(Some(Hover {
                contents: HoverContents::Markup(MarkupContent {
                    kind: MarkupKind::Markdown,
                    value: format!("```dylang\n{}\n```", summary),
                }),
                range: None,
            }));
        }

        if let Some(type_str) =
            hover::type_at_name(tc_result, &name, Some(&span), node_id.as_ref(), program)
        {
            return Ok(Some(Hover {
                contents: HoverContents::Markup(MarkupContent {
                    kind: MarkupKind::Markdown,
                    value: format!("```dylang\n{}: {}\n```", name, type_str),
                }),
                range: None,
            }));
        }

        Ok(None)
    }

    async fn goto_definition(
        &self,
        params: GotoDefinitionParams,
    ) -> Result<Option<GotoDefinitionResponse>> {
        let uri = params
            .text_document_position_params
            .text_document
            .uri
            .clone();
        let Some(snap) = self.snapshot(&uri) else {
            return Ok(None);
        };
        let tc_result = &snap.tc_result;
        let program = snap.program.as_ref().unwrap();
        let line_index = &snap.line_index;


        let position = params.text_document_position_params.position;
        let offset =
            line_index.line_col_to_offset(position.line as usize, position.character as usize, &snap.source);

        let Some((name, span, _node_id)) = hover::find_name_at_offset(program, offset) else {
            return Ok(None);
        };

        // Level 1: effect call -> handler arm (op! -> the arm that handles it)
        if let Some((arm_span, arm_module)) = tc_result.effect_call_targets.get(&span) {
            let (target_uri, target_li, target_source) =
                resolve_span_location(&uri, line_index, &snap.source, arm_module.as_deref(), tc_result)?;
            let (start_line, start_col) = target_li.offset_to_line_col(arm_span.start, &target_source);
            let (end_line, end_col) = target_li.offset_to_line_col(arm_span.end, &target_source);
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
            let (target_uri, target_li, target_source) =
                resolve_span_location(&uri, line_index, &snap.source, op_module.as_deref(), tc_result)?;
            let (start_line, start_col) = target_li.offset_to_line_col(op_def_span.start, &target_source);
            let (end_line, end_col) = target_li.offset_to_line_col(op_def_span.end, &target_source);
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
            let (target_uri, target_li, target_source) =
                resolve_span_location(&uri, line_index, &snap.source, source_module, tc_result)?;
            // Find the HandlerDef span in the target program
            let target_program = if let Some(m) = source_module {
                tc_result.programs().get(m).map(|p| p.as_slice())
            } else {
                Some(program.as_slice())
            };
            if let Some(prog) = target_program
                && let Some(def) = definition::find_definition(prog, &name, tc_result)
            {
                let (start_line, start_col) = target_li.offset_to_line_col(def.span.start, &target_source);
                let (end_line, end_col) = target_li.offset_to_line_col(def.span.end, &target_source);
                return Ok(Some(GotoDefinitionResponse::Scalar(Location {
                    uri: target_uri,
                    range: Range {
                        start: Position::new(start_line as u32, start_col as u32),
                        end: Position::new(end_line as u32, end_col as u32),
                    },
                })));
            }
        }

        let Some(def_result) = definition::find_definition(program, &name, tc_result) else {
            return Ok(None);
        };

        // For cross-module definitions, build a line index for the target file
        let (target_uri, target_line_index, target_source);
        if let Some(ref file_path) = def_result.file_path {
            target_uri = Url::from_file_path(file_path)
                .map_err(|_| tower_lsp::jsonrpc::Error::internal_error())?;
            let src = std::fs::read_to_string(file_path)
                .map_err(|_| tower_lsp::jsonrpc::Error::internal_error())?;
            target_line_index = Some(line_index::LineIndex::new(&src));
            target_source = Some(src);
        } else {
            target_uri = uri;
            target_line_index = None;
            target_source = None;
        }

        let li = target_line_index.as_ref().unwrap_or(line_index);
        let src = target_source.as_deref().unwrap_or(&snap.source);
        let (start_line, start_col) = li.offset_to_line_col(def_result.span.start, src);
        let (end_line, end_col) = li.offset_to_line_col(def_result.span.end, src);

        Ok(Some(GotoDefinitionResponse::Scalar(Location {
            uri: target_uri,
            range: Range {
                start: Position::new(start_line as u32, start_col as u32),
                end: Position::new(end_line as u32, end_col as u32),
            },
        })))
    }

    async fn completion(&self, params: CompletionParams) -> Result<Option<CompletionResponse>> {
        let uri = params.text_document_position.text_document.uri.clone();
        let position = params.text_document_position.position;

        let Some(snap) = self.snapshot(&uri) else {
            return Ok(None);
        };

        // Use the latest editor text for dot-chain detection (may be ahead of
        // the snapshot due to async processing), falling back to the snapshot's
        // source if document_texts hasn't been populated yet.
        let editor_source = self.document_text(&uri);
        let source = editor_source.as_deref().unwrap_or(&snap.source);
        let li = line_index::LineIndex::new(source);
        let offset = li.line_col_to_offset(position.line as usize, position.character as usize, source);
        let prefix = completion::extract_prefix(source, offset);

        // Dot-completion: record field access, supports chaining (e.g. `a.b.c.`).
        // Type resolution uses the snapshot's source (where spans are valid).
        if let Some(chain) = completion::extract_dot_chain(source, offset)
            && let Some(items) = completion::collect_field_completions(
                &snap.tc_result,
                &chain,
                prefix,
                &snap.source,
            )
        {
            return Ok(Some(CompletionResponse::Array(items)));
        }

        // Record construction completion: `House { a|` or `House { address: { n|`
        if let Some(ctx) = completion::extract_record_construction_context(&snap.tc_result, source, offset)
            && let Some(items) = completion::collect_record_construction_completions(
                &snap.tc_result,
                &ctx,
                prefix,
                source,
                offset,
            )
        {
            return Ok(Some(CompletionResponse::Array(items)));
        }

        // General completion.
        let program = snap.program.as_ref().unwrap();
        let items = completion::collect_completions(&snap.tc_result, prefix, program, offset);
        Ok(Some(CompletionResponse::Array(items)))
    }

    async fn code_action(&self, params: CodeActionParams) -> Result<Option<CodeActionResponse>> {
        let uri = params.text_document.uri.clone();
        let Some(snap) = self.snapshot(&uri) else {
            return Ok(None);
        };
        let tc_result = &snap.tc_result;
        let program = snap.program.as_ref().unwrap();
        let line_index = &snap.line_index;

        let actions =
            code_action::collect_code_actions(tc_result, program, line_index, &snap.source, &uri, params.range);

        if actions.is_empty() {
            Ok(None)
        } else {
            Ok(Some(actions))
        }
    }

    async fn document_symbol(
        &self,
        params: DocumentSymbolParams,
    ) -> Result<Option<DocumentSymbolResponse>> {
        let uri = params.text_document.uri.clone();
        let Some(snap) = self.snapshot(&uri) else {
            return Ok(None);
        };

        let program = snap.program.as_ref().unwrap();
        let line_index = &snap.line_index;


        let mut symbols = document_symbol::collect_symbols(program, line_index, &snap.source);
        // Fill in the real URI (collect_symbols uses a placeholder)
        for sym in &mut symbols {
            sym.location.uri = uri.clone();
        }

        Ok(Some(DocumentSymbolResponse::Flat(symbols)))
    }

    async fn signature_help(&self, params: SignatureHelpParams) -> Result<Option<SignatureHelp>> {
        let uri = params
            .text_document_position_params
            .text_document
            .uri
            .clone();
        let Some(snap) = self.snapshot(&uri) else {
            return Ok(None);
        };
        let tc_result = &snap.tc_result;
        let program = snap.program.as_ref().unwrap();
        let line_index = &snap.line_index;
        let source = &snap.source;

        let position = params.text_document_position_params.position;
        let offset =
            line_index.line_col_to_offset(position.line as usize, position.character as usize, source);

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
            if let Some(found) = signature_help::find_active_call(program, offset) {
                found
            } else if let Some(found) = signature_help::find_call_near(program, source, offset) {
                found
            } else {
                // No App chain found -- check if cursor is after `<name> ` (no arg yet).
                match signature_help::ident_before_spaces(source, offset) {
                    Some(name) => (name, 0),
                    None => return Ok(None),
                }
            };

        let Some(mut sig_info) = signature_help::build_signature(&func_name, program, tc_result)
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

    async fn references(&self, params: ReferenceParams) -> Result<Option<Vec<Location>>> {
        let uri = params.text_document_position.text_document.uri.clone();
        let Some(snap) = self.snapshot(&uri) else {
            return Ok(None);
        };
        let tc_result = &snap.tc_result;
        let program = snap.program.as_ref().unwrap();
        let line_index = &snap.line_index;

        let position = params.text_document_position.position;
        let offset =
            line_index.line_col_to_offset(position.line as usize, position.character as usize, &snap.source);

        let Some((name, _span, _node_id)) = hover::find_name_at_offset(program, offset) else {
            return Ok(None);
        };

        // Resolve the symbol key: (module, name).
        // Check both value import_origins and type_import_origins.
        let module = if let Some(origin) = tc_result.import_origins.get(&name)
            .or_else(|| tc_result.type_import_origins.get(&name))
        {
            origin.clone()
        } else {
            // Local definition: use this file's module declaration
            let local_module = program.iter().find_map(|decl| {
                if let dylang::ast::Decl::ModuleDecl { path, .. } = decl {
                    Some(path.join("."))
                } else {
                    None
                }
            });
            local_module.unwrap_or_else(|| "_script".to_string())
        };

        let key = symbol_index::SymbolKey {
            module: module.clone(),
            name: name.clone(),
        };

        // Ensure all project files are indexed before querying.
        if let Some(module_map) = tc_result.module_map() {
            let current_path = uri.to_file_path().ok();
            for file_path in module_map.values() {
                if current_path.as_ref() == Some(file_path) {
                    continue;
                }
                let file_uri = match Url::from_file_path(file_path) {
                    Ok(u) => u,
                    Err(_) => continue,
                };
                let needs_index = {
                    let idx = self.symbol_index.lock().unwrap_or_else(|e| e.into_inner());
                    !idx.has_file(&file_uri)
                };
                if needs_index {
                    let source = match std::fs::read_to_string(file_path) {
                        Ok(s) => s,
                        Err(_) => continue,
                    };
                    // Quick text check: skip files that don't mention the name
                    if !source.contains(&name) {
                        continue;
                    }
                    let checker = self.get_checker(&file_uri);
                    let check_result = std::panic::catch_unwind(
                        std::panic::AssertUnwindSafe(|| diagnostics::check(checker, &source)),
                    );
                    if let Ok(snap) = check_result
                        && let Some(ref prog) = snap.program
                    {
                        let mut idx =
                            self.symbol_index.lock().unwrap_or_else(|e| e.into_inner());
                        idx.update_file(&file_uri, &snap.tc_result, prog, &snap.line_index, &snap.source);
                    }
                }
            }
        }

        // Query the index for all references to this symbol.
        let refs = {
            let idx = self.symbol_index.lock().unwrap_or_else(|e| e.into_inner());
            idx.query(&key)
        };

        let mut locations: Vec<Location> = refs
            .into_iter()
            .map(|r| Location {
                uri: r.uri,
                range: r.range,
            })
            .collect();

        // Include the definition site if requested.
        if params.context.include_declaration {
            // Find the definition span in the current file's check result
            if let Some(did) = tc_result.env.def_id(&name)
                && let Some(&def_span) = tc_result.node_spans.get(&did)
            {
                let (start_line, start_col) = line_index.offset_to_line_col(def_span.start, &snap.source);
                let (end_line, end_col) = line_index.offset_to_line_col(def_span.end, &snap.source);
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
        document_texts: Mutex::new(std::collections::HashMap::new()),
        symbol_index: Mutex::new(symbol_index::SymbolIndex::default()),
    });
    Server::new(stdin, stdout, socket).serve(service).await;
}
