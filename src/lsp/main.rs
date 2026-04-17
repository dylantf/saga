use std::sync::{Arc, Mutex};
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};

use saga::{formatter, lexer, parser, typechecker};

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

/// Shared mutable state accessed by both the LanguageServer methods (queries)
/// and the background debounce task (typechecking).
struct SharedState {
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

struct Backend {
    client: Client,
    shared: Arc<SharedState>,
    check_tx: tokio::sync::mpsc::UnboundedSender<(Url, String)>,
}

impl SharedState {
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
                    idx.update_file(
                        &uri,
                        &snap.tc_result,
                        program,
                        &snap.line_index,
                        &snap.source,
                    );
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

impl Backend {
    /// Ensure all project files are indexed in the symbol index, then collect
    /// all reference + definition locations for a symbol. Shared by references and rename.
    fn collect_all_symbol_locations(
        &self,
        uri: &Url,
        snap: &CheckSnapshot,
        name: &str,
        node_id: Option<saga::ast::NodeId>,
        include_definition: bool,
    ) -> Vec<Location> {
        let tc_result = &snap.tc_result;
        let program = snap.program.as_ref().unwrap();
        let line_index = &snap.line_index;

        // Node-id-based lookup: resolve cursor to a def_id, then find all
        // same-file usages via tc_result.references. This handles local
        // variables, function params, pattern bindings, etc. that aren't
        // tracked in the cross-module symbol index.
        if let Some(nid) = node_id {
            // Resolve to def_id: if this node is a usage, look up its target;
            // otherwise it might be the definition itself.
            let def_id = tc_result.references.get(&nid).copied().unwrap_or(nid);

            // Collect all usages that point to this def_id
            let mut locations: Vec<Location> = Vec::new();
            for (usage_id, &did) in &tc_result.references {
                if did == def_id
                    && let Some(&span) = tc_result.node_spans.get(usage_id)
                {
                    let (sl, sc) = line_index.offset_to_line_col(span.start, &snap.source);
                    let (el, ec) = line_index.offset_to_line_col(span.end, &snap.source);
                    locations.push(Location {
                        uri: uri.clone(),
                        range: Range {
                            start: Position::new(sl as u32, sc as u32),
                            end: Position::new(el as u32, ec as u32),
                        },
                    });
                }
            }

            // Include the definition site itself
            if include_definition && let Some(&def_span) = tc_result.node_spans.get(&def_id) {
                let (sl, sc) = line_index.offset_to_line_col(def_span.start, &snap.source);
                let (el, ec) = line_index.offset_to_line_col(def_span.end, &snap.source);
                let def_loc = Location {
                    uri: uri.clone(),
                    range: Range {
                        start: Position::new(sl as u32, sc as u32),
                        end: Position::new(el as u32, ec as u32),
                    },
                };
                if !locations.iter().any(|l| l.range == def_loc.range) {
                    locations.push(def_loc);
                }
            }

            // If we found usages (not just the definition), return them.
            // Types/records/effects use type_references instead of references,
            // so they won't have usages here -- fall through to symbol index.
            if locations.len() > 1 || (!include_definition && !locations.is_empty()) {
                return locations;
            }
        }

        // Resolve the symbol key: (module, name).
        let module = if let Some(origin) = tc_result.scope_map.origin_of(name) {
            origin.to_string()
        } else {
            let local_module = program.iter().find_map(|decl| {
                if let saga::ast::Decl::ModuleDecl { path, .. } = decl {
                    Some(path.join("."))
                } else {
                    None
                }
            });
            local_module.unwrap_or_else(|| uri.to_string())
        };

        let key = symbol_index::SymbolKey {
            module: module.clone(),
            name: name.to_string(),
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
                    let idx = self
                        .shared
                        .symbol_index
                        .lock()
                        .unwrap_or_else(|e| e.into_inner());
                    !idx.has_file(&file_uri)
                };
                if needs_index {
                    let source = match std::fs::read_to_string(file_path) {
                        Ok(s) => s,
                        Err(_) => continue,
                    };
                    if !source.contains(name) {
                        continue;
                    }
                    let checker = self.shared.get_checker(&file_uri);
                    let check_result =
                        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                            diagnostics::check(checker, &source)
                        }));
                    if let Ok(snap) = check_result
                        && let Some(ref prog) = snap.program
                    {
                        let mut idx = self
                            .shared
                            .symbol_index
                            .lock()
                            .unwrap_or_else(|e| e.into_inner());
                        idx.update_file(
                            &file_uri,
                            &snap.tc_result,
                            prog,
                            &snap.line_index,
                            &snap.source,
                        );
                    }
                }
            }
        }

        // Query the index for all references.
        let refs = {
            let idx = self
                .shared
                .symbol_index
                .lock()
                .unwrap_or_else(|e| e.into_inner());
            idx.query(&key)
        };

        let mut locations: Vec<Location> = refs
            .into_iter()
            .map(|r| Location {
                uri: r.uri,
                range: r.range,
            })
            .collect();

        // Include the definition site.
        if include_definition {
            if let Some(did) = tc_result.env.def_id(name)
                && let Some(&def_span) = tc_result.node_spans.get(&did)
            {
                let line_index = &snap.line_index;
                let (start_line, start_col) =
                    line_index.offset_to_line_col(def_span.start, &snap.source);
                let (end_line, end_col) = line_index.offset_to_line_col(def_span.end, &snap.source);
                locations.push(Location {
                    uri: uri.clone(),
                    range: Range {
                        start: Position::new(start_line as u32, start_col as u32),
                        end: Position::new(end_line as u32, end_col as u32),
                    },
                });
            }
            // For type/effect/record/trait/handler definitions, find via AST
            if let Some(def_result) = definition::find_definition(program, name, tc_result) {
                let (def_uri, def_li, def_source) = if let Some(ref fp) = def_result.file_path {
                    let u = match Url::from_file_path(fp) {
                        Ok(u) => u,
                        Err(_) => return locations,
                    };
                    let s = match std::fs::read_to_string(fp) {
                        Ok(s) => s,
                        Err(_) => return locations,
                    };
                    let li = line_index::LineIndex::new(&s);
                    (u, li, s)
                } else {
                    (uri.clone(), snap.line_index.clone(), snap.source.clone())
                };
                let (sl, sc) = def_li.offset_to_line_col(def_result.span.start, &def_source);
                let (el, ec) = def_li.offset_to_line_col(def_result.span.end, &def_source);
                let def_loc = Location {
                    uri: def_uri,
                    range: Range {
                        start: Position::new(sl as u32, sc as u32),
                        end: Position::new(el as u32, ec as u32),
                    },
                };
                // Avoid duplicates
                if !locations
                    .iter()
                    .any(|l| l.uri == def_loc.uri && l.range == def_loc.range)
                {
                    locations.push(def_loc);
                }
            }
        }

        locations
    }
}

/// Find an effect op signature from the AST (preserves original type param names).
/// Returns (signature, doc_comments) for an effect operation.
fn find_effect_op_signature(
    program: &[saga::ast::Decl],
    op_name: &str,
) -> Option<(String, Vec<String>)> {
    for decl in program {
        if let saga::ast::Decl::EffectDef {
            name: effect_name,
            operations,
            ..
        } = decl
        {
            for op in operations {
                let op = &op.node;
                if op.name == op_name {
                    let sig = hover::format_signature(&op.name, &op.params, &op.return_type);
                    return Some((format!("{}.{}", effect_name, sig), op.doc.clone()));
                }
            }
        }
    }
    None
}

/// Find an effect op signature from CheckResult (for imported effects not in local AST).
fn find_effect_op_signature_from_result(
    tc_result: &saga::typechecker::CheckResult,
    op_name: &str,
) -> Option<String> {
    for (effect_name, info) in &tc_result.effects {
        for (name, params, ret) in tc_result.prettify_effect(info) {
            if name == op_name {
                let display_name = tc_result
                    .scope_map
                    .shortest_alias(effect_name, &tc_result.scope_map.effects)
                    .unwrap_or(effect_name.as_str());
                let param_strs: Vec<String> = params
                    .iter()
                    .map(|(label, ty)| {
                        if label.starts_with('_') {
                            format!("{}", ty)
                        } else {
                            format!("({}: {})", label, ty)
                        }
                    })
                    .collect();
                let sig = if param_strs.is_empty() {
                    format!("{}.{} : Unit -> {}", display_name, op_name, ret)
                } else {
                    format!(
                        "{}.{} : {} -> {}",
                        display_name,
                        op_name,
                        param_strs.join(" -> "),
                        ret
                    )
                };
                return Some(sig);
            }
        }
    }
    None
}

/// Resolve a span's location: returns (URI, LineIndex) for a span that lives in `module_name`
/// (None = same file as `current_uri`).
fn resolve_span_location(
    current_uri: &Url,
    current_li: &line_index::LineIndex,
    current_source: &str,
    module_name: Option<&str>,
    tc_result: &saga::typechecker::CheckResult,
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
    Ok((
        current_uri.clone(),
        current_li.clone(),
        current_source.to_string(),
    ))
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
                rename_provider: Some(OneOf::Right(RenameOptions {
                    prepare_provider: Some(true),
                    work_done_progress_options: Default::default(),
                })),
                document_formatting_provider: Some(OneOf::Left(true)),
                ..Default::default()
            },
            ..Default::default()
        })
    }

    async fn initialized(&self, _: InitializedParams) {
        self.client
            .log_message(MessageType::INFO, "saga LSP initialized")
            .await;
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        let uri = params.text_document.uri.clone();
        let text = params.text_document.text.clone();
        self.shared
            .document_texts
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .insert(uri.clone(), text.clone());
        let _ = self.check_tx.send((uri, text));
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        let uri = params.text_document.uri.clone();
        if let Some(change) = params.content_changes.into_iter().last() {
            self.shared
                .document_texts
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .insert(uri.clone(), change.text.clone());
            let _ = self.check_tx.send((uri, change.text));
        }
    }

    async fn did_save(&self, params: DidSaveTextDocumentParams) {
        if let Some(text) = &params.text {
            let uri = params.text_document.uri.clone();
            let _ = self.check_tx.send((uri, text.clone()));
        }
    }

    async fn hover(&self, params: HoverParams) -> Result<Option<Hover>> {
        let uri = params
            .text_document_position_params
            .text_document
            .uri
            .clone();
        let Some(snap) = self.shared.snapshot(&uri) else {
            return Ok(None);
        };
        let tc_result = &snap.tc_result;
        let program = snap.program.as_ref().unwrap();
        let line_index = &snap.line_index;

        let position = params.text_document_position_params.position;
        let offset = line_index.line_col_to_offset(
            position.line as usize,
            position.character as usize,
            &snap.source,
        );

        let Some((name, span, node_id)) = hover::find_name_at_offset(program, offset) else {
            return Ok(None);
        };

        // Handlers get special display: "handler name for Effect1, Effect2"
        if let Some(handler_info) = tc_result.handlers.get(&name) {
            let effects = handler_info.effects.join(", ");
            let code = format!("handler {} for {}", name, effects);
            let value = match hover::doc_for_name(program, &name, tc_result) {
                Some(doc) => format!("{}\n\n---\n\n```saga\n{}\n```", doc, code),
                None => format!("```saga\n{}\n```", code),
            };
            return Ok(Some(Hover {
                contents: HoverContents::Markup(MarkupContent {
                    kind: MarkupKind::Markdown,
                    value,
                }),
                range: None,
            }));
        }

        // Effect operation: show signature from the effect definition.
        // Prefer AST (has original type param names) over CheckResult (may have raw var IDs).
        if let Some((sig, doc)) = find_effect_op_signature(program, &name) {
            let value = if doc.is_empty() {
                format!("```saga\n{}\n```", sig)
            } else {
                format!("{}\n\n---\n\n```saga\n{}\n```", doc.join("\n"), sig)
            };
            return Ok(Some(Hover {
                contents: HoverContents::Markup(MarkupContent {
                    kind: MarkupKind::Markdown,
                    value,
                }),
                range: None,
            }));
        }
        if let Some(sig) = find_effect_op_signature_from_result(tc_result, &name) {
            return Ok(Some(Hover {
                contents: HoverContents::Markup(MarkupContent {
                    kind: MarkupKind::Markdown,
                    value: format!("```saga\n{}\n```", sig),
                }),
                range: None,
            }));
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
                    value: summary,
                }),
                range: None,
            }));
        }

        if let Some(type_str) =
            hover::type_at_name(tc_result, &name, Some(&span), node_id.as_ref(), program)
        {
            // Use source text for display name (the AST name may be canonical after resolve)
            let display_name = if span.end > span.start
                && span.end <= snap.source.len()
                && snap.source.is_char_boundary(span.start)
                && snap.source.is_char_boundary(span.end)
            {
                &snap.source[span.start..span.end]
            } else {
                &name
            };
            let code = format!("{}: {}", display_name, type_str);
            let value = match hover::doc_for_name(program, &name, tc_result) {
                Some(doc) => format!("{}\n\n---\n\n```saga\n{}\n```", doc, code),
                None => format!("```saga\n{}\n```", code),
            };
            return Ok(Some(Hover {
                contents: HoverContents::Markup(MarkupContent {
                    kind: MarkupKind::Markdown,
                    value,
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
        let Some(snap) = self.shared.snapshot(&uri) else {
            return Ok(None);
        };
        let tc_result = &snap.tc_result;
        let program = snap.program.as_ref().unwrap();
        let line_index = &snap.line_index;

        let position = params.text_document_position_params.position;
        let offset = line_index.line_col_to_offset(
            position.line as usize,
            position.character as usize,
            &snap.source,
        );

        let Some((name, span, _node_id)) = hover::find_name_at_offset(program, offset) else {
            return Ok(None);
        };

        // Level 1: effect call -> handler arm (op! -> the arm that handles it)
        if let Some((arm_span, arm_module)) = tc_result.effect_call_targets.get(&span) {
            let (target_uri, target_li, target_source) = resolve_span_location(
                &uri,
                line_index,
                &snap.source,
                arm_module.as_deref(),
                tc_result,
            )?;
            let (start_line, start_col) =
                target_li.offset_to_line_col(arm_span.start, &target_source);
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
        // handler_arm_targets is keyed by the full arm span, so also check if the cursor's
        // span is contained within any arm span.
        if let Some((op_def_span, op_module)) =
            tc_result.handler_arm_targets.get(&span).or_else(|| {
                tc_result
                    .handler_arm_targets
                    .iter()
                    .find_map(|(arm_span, target)| {
                        (span.start >= arm_span.start && span.end <= arm_span.end).then_some(target)
                    })
            })
        {
            let (target_uri, target_li, target_source) = resolve_span_location(
                &uri,
                line_index,
                &snap.source,
                op_module.as_deref(),
                tc_result,
            )?;
            let (start_line, start_col) =
                target_li.offset_to_line_col(op_def_span.start, &target_source);
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
                let (start_line, start_col) =
                    target_li.offset_to_line_col(def.span.start, &target_source);
                let (end_line, end_col) =
                    target_li.offset_to_line_col(def.span.end, &target_source);
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

        let Some(snap) = self.shared.snapshot(&uri) else {
            return Ok(None);
        };

        // Use the latest editor text for dot-chain detection (may be ahead of
        // the snapshot due to async processing), falling back to the snapshot's
        // source if document_texts hasn't been populated yet.
        let editor_source = self.shared.document_text(&uri);
        let source = editor_source.as_deref().unwrap_or(&snap.source);
        let li = line_index::LineIndex::new(source);
        let offset =
            li.line_col_to_offset(position.line as usize, position.character as usize, source);
        let prefix = completion::extract_prefix(source, offset);

        // Dot-completion: record field access or module-qualified names.
        // Type resolution uses the snapshot's source (where spans are valid).
        if let Some(chain) = completion::extract_dot_chain(source, offset) {
            if let Some(items) =
                completion::collect_field_completions(&snap.tc_result, &chain, prefix, &snap.source)
            {
                return Ok(Some(CompletionResponse::Array(items)));
            }
            if let Some(items) =
                completion::collect_module_completions(&snap.tc_result, &chain, prefix)
            {
                return Ok(Some(CompletionResponse::Array(items)));
            }
        }

        // Record construction completion: `House { a|` or `House { address: { n|`
        if let Some(ctx) =
            completion::extract_record_construction_context(&snap.tc_result, source, offset)
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
        let Some(snap) = self.shared.snapshot(&uri) else {
            return Ok(None);
        };
        let tc_result = &snap.tc_result;
        let program = snap.program.as_ref().unwrap();
        let line_index = &snap.line_index;

        let actions = code_action::collect_code_actions(
            tc_result,
            program,
            line_index,
            &snap.source,
            &uri,
            params.range,
        );

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
        let Some(snap) = self.shared.snapshot(&uri) else {
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
        let Some(snap) = self.shared.snapshot(&uri) else {
            return Ok(None);
        };
        let tc_result = &snap.tc_result;
        let program = snap.program.as_ref().unwrap();
        let line_index = &snap.line_index;
        let source = &snap.source;

        let position = params.text_document_position_params.position;
        let offset = line_index.line_col_to_offset(
            position.line as usize,
            position.character as usize,
            source,
        );

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
        let Some(snap) = self.shared.snapshot(&uri) else {
            return Ok(None);
        };
        let program = snap.program.as_ref().unwrap();
        let line_index = &snap.line_index;

        let position = params.text_document_position.position;
        let offset = line_index.line_col_to_offset(
            position.line as usize,
            position.character as usize,
            &snap.source,
        );

        let Some((name, _span, node_id)) = hover::find_name_at_offset(program, offset) else {
            return Ok(None);
        };

        let locations = self.collect_all_symbol_locations(
            &uri,
            &snap,
            &name,
            node_id,
            params.context.include_declaration,
        );

        if locations.is_empty() {
            Ok(None)
        } else {
            Ok(Some(locations))
        }
    }

    async fn prepare_rename(
        &self,
        params: TextDocumentPositionParams,
    ) -> Result<Option<PrepareRenameResponse>> {
        let uri = params.text_document.uri.clone();
        let Some(snap) = self.shared.snapshot(&uri) else {
            return Ok(None);
        };
        let program = snap.program.as_ref().unwrap();
        let line_index = &snap.line_index;

        let position = params.position;
        let offset = line_index.line_col_to_offset(
            position.line as usize,
            position.character as usize,
            &snap.source,
        );

        let Some((name, span, _node_id)) = hover::find_name_at_offset(program, offset) else {
            return Ok(None);
        };

        // Don't allow renaming module-prefixed names, keywords, or wildcards
        if name.starts_with("module:") || name == "_" {
            return Ok(None);
        }
        // Reject imported symbols that aren't locally redefined
        let tc_result = &snap.tc_result;
        let is_imported = tc_result.scope_map.is_import(&name);
        let is_locally_defined = definition::find_definition(program, &name, tc_result)
            .is_some_and(|d| d.file_path.is_none());
        if is_imported && !is_locally_defined {
            return Ok(None);
        }

        let (start_line, start_col) = line_index.offset_to_line_col(span.start, &snap.source);
        let (end_line, end_col) = line_index.offset_to_line_col(span.end, &snap.source);
        let range = Range {
            start: Position::new(start_line as u32, start_col as u32),
            end: Position::new(end_line as u32, end_col as u32),
        };

        Ok(Some(PrepareRenameResponse::RangeWithPlaceholder {
            range,
            placeholder: name,
        }))
    }

    async fn rename(&self, params: RenameParams) -> Result<Option<WorkspaceEdit>> {
        let uri = params.text_document_position.text_document.uri.clone();
        let Some(snap) = self.shared.snapshot(&uri) else {
            return Ok(None);
        };
        let program = snap.program.as_ref().unwrap();
        let line_index = &snap.line_index;

        let position = params.text_document_position.position;
        let offset = line_index.line_col_to_offset(
            position.line as usize,
            position.character as usize,
            &snap.source,
        );

        let Some((name, _span, node_id)) = hover::find_name_at_offset(program, offset) else {
            return Ok(None);
        };

        if name.starts_with("module:") {
            return Ok(None);
        }

        let new_name = params.new_name;
        // Collect all locations: references + definition
        let locations = self.collect_all_symbol_locations(&uri, &snap, &name, node_id, true);

        if locations.is_empty() {
            return Ok(None);
        }

        // Group edits by URI
        let mut changes: std::collections::HashMap<Url, Vec<TextEdit>> =
            std::collections::HashMap::new();
        for loc in locations {
            changes.entry(loc.uri).or_default().push(TextEdit {
                range: loc.range,
                new_text: new_name.clone(),
            });
        }

        Ok(Some(WorkspaceEdit {
            changes: Some(changes),
            ..Default::default()
        }))
    }

    async fn formatting(&self, params: DocumentFormattingParams) -> Result<Option<Vec<TextEdit>>> {
        let uri = params.text_document.uri;
        // Use the latest editor text (updated immediately on each keystroke),
        // not the snapshot source which may be stale due to debounced checking.
        let Some(source) = self.shared.document_text(&uri) else {
            return Ok(None);
        };

        // Re-parse to get AnnotatedProgram (preserves comments/trivia)
        let tokens = match lexer::Lexer::new(&source).lex() {
            Ok(t) => t,
            Err(_) => return Ok(None),
        };
        let mut p = parser::Parser::new(tokens);
        let annotated = match p.parse_program_annotated() {
            Ok(prog) => prog,
            Err(_) => return Ok(None),
        };

        // Resolve width from project.toml, falling back to default
        let width = uri
            .to_file_path()
            .ok()
            .and_then(|p| p.parent().map(|d| d.to_path_buf()))
            .and_then(|d| checker::find_project_root(&d))
            .map(|root| {
                saga::project_config::ProjectConfig::load(&root)
                    .formatter
                    .width
            })
            .unwrap_or(formatter::DEFAULT_WIDTH);

        let formatted = formatter::format(&annotated, width);

        // Replace the entire document
        let last_line = source.lines().count() as u32;
        let range = Range {
            start: Position::new(0, 0),
            end: Position::new(last_line, 0),
        };

        Ok(Some(vec![TextEdit {
            range,
            new_text: formatted,
        }]))
    }
}

/// Background task that debounces typecheck requests per-URI.
///
/// Each incoming `(Url, String)` resets a 300ms timer for that URI. When the
/// timer fires (no new edits for that file), the check runs on the blocking
/// thread pool so hover/completion remain responsive on the async event loop.
async fn debounce_loop(
    mut rx: tokio::sync::mpsc::UnboundedReceiver<(Url, String)>,
    client: Client,
    shared: Arc<SharedState>,
) {
    use std::collections::HashMap;
    use tokio::time::{Duration, Instant, sleep_until};

    let debounce = Duration::from_millis(300);
    let mut pending: HashMap<Url, (String, Instant)> = HashMap::new();

    loop {
        // If nothing is pending, block until the next request arrives.
        if pending.is_empty() {
            match rx.recv().await {
                Some((uri, text)) => {
                    pending.insert(uri, (text, Instant::now() + debounce));
                }
                None => break,
            }
        }

        // Wait for either the earliest deadline or a new request.
        let next_deadline = pending.values().map(|(_, d)| *d).min().unwrap();

        tokio::select! {
            biased;
            result = rx.recv() => {
                match result {
                    Some((uri, text)) => {
                        pending.insert(uri, (text, Instant::now() + debounce));
                    }
                    None => break,
                }
            }
            _ = sleep_until(next_deadline) => {
                let now = Instant::now();
                let expired: Vec<Url> = pending
                    .iter()
                    .filter(|(_, (_, deadline))| *deadline <= now)
                    .map(|(uri, _)| uri.clone())
                    .collect();

                for uri in expired {
                    let (text, _) = pending.remove(&uri).unwrap();
                    let shared = Arc::clone(&shared);
                    let client = client.clone();
                    tokio::spawn(async move {
                        let uri2 = uri.clone();
                        let result = tokio::task::spawn_blocking(move || {
                            shared.check_file(uri2, &text)
                        })
                        .await;
                        if let Ok(diagnostics) = result {
                            client.publish_diagnostics(uri, diagnostics, None).await;
                        }
                    });
                }
            }
        }
    }
}

#[tokio::main]
async fn main() {
    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    let (check_tx, check_rx) = tokio::sync::mpsc::unbounded_channel();

    let (service, socket) = LspService::new(|client| {
        let shared = Arc::new(SharedState {
            base_checkers: Mutex::new(std::collections::HashMap::new()),
            last_check: Mutex::new(std::collections::HashMap::new()),
            document_texts: Mutex::new(std::collections::HashMap::new()),
            symbol_index: Mutex::new(symbol_index::SymbolIndex::default()),
        });

        tokio::spawn(debounce_loop(check_rx, client.clone(), Arc::clone(&shared)));

        Backend {
            client,
            shared,
            check_tx,
        }
    });
    Server::new(stdin, stdout, socket).serve(service).await;
}
