use std::collections::{HashMap, HashSet};
use std::path::PathBuf;
use std::sync::{Arc, Mutex};

use saga::{ast, formatter, lexer, parser, project_config, typechecker};
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};

mod analysis;
mod analysis_pipeline;
mod code_action;
mod completion;
mod document_symbol;
mod hover;
mod navigation;
mod scheduler;
mod semantic;
mod semantic_builder;
mod semantic_symbols;
mod semantic_values;
mod signature_help;
mod state;
mod text;

use analysis_pipeline::{
    analyze_syntax_document, display_project_root, project_root_for_uri, trace,
};
use code_action::collect_code_actions;
use completion::collect_completion_items;
use document_symbol::collect_document_symbols;
use hover::hover_type_at;
use navigation::{
    RenameTarget, local_definition_at, references_at, rename_target_at, valid_rename_name,
    workspace_edit_from_locations,
};
use scheduler::debounce_loop;
use semantic::{SemanticIndex, SemanticSymbolKey};
use signature_help::signature_help_at;
use state::{
    CachedModuleInterface, ModuleInterfaceUpdate, ProjectSemanticIndexUpdate, ProjectSemanticStore,
};
use text::{LineIndex, full_document_range, sort_and_dedup_locations};

const SEMANTIC_DEBOUNCE_MS: u64 = 100;

#[derive(Clone)]
struct DocumentState {
    version: i32,
    text: String,
    dirty: bool,
    parse: Option<Arc<ParseSnapshot>>,
    semantic: Option<Arc<SemanticSnapshot>>,
    diagnostics: Vec<Diagnostic>,
}

#[derive(Clone)]
struct ParseSnapshot {
    version: i32,
    source: Arc<str>,
    line_index: LineIndex,
    program: ast::Program,
}

struct ParseJobResult {
    version: i32,
    parse: Option<ParseSnapshot>,
    semantic: Option<SemanticSnapshot>,
    diagnostics: Vec<Diagnostic>,
    module_interfaces: Vec<ModuleInterfaceUpdate>,
    semantic_index_update: Option<ProjectSemanticIndexUpdate>,
    force_dependents: bool,
}

struct AppliedParseResult {
    diagnostics: Vec<Diagnostic>,
    dependents: Vec<Url>,
}

#[derive(Clone)]
struct SemanticSnapshot {
    version: i32,
    source: Arc<str>,
    line_index: LineIndex,
    check: typechecker::CheckResult,
    semantic_index: SemanticIndex,
}

#[derive(Default)]
struct SharedState {
    documents: Mutex<HashMap<Url, DocumentState>>,
    projects: Mutex<ProjectSemanticStore>,
}

#[derive(Clone, Copy)]
struct CachedDefinitionSources<'a> {
    projects: &'a ProjectSemanticStore,
    project_root: &'a Option<PathBuf>,
    direct_imports: &'a std::collections::HashSet<String>,
}

struct CheckRequest {
    uri: Url,
    version: i32,
    text: String,
    project_root: Option<PathBuf>,
    is_primary: bool,
}

struct Backend {
    client: Client,
    shared: Arc<SharedState>,
    check_tx: tokio::sync::mpsc::UnboundedSender<CheckRequest>,
}

fn store_document(shared: &SharedState, uri: Url, version: i32, text: String, dirty: bool) {
    let mut documents = shared.documents.lock().unwrap_or_else(|e| e.into_inner());
    let previous_parse = documents.get(&uri).and_then(|doc| doc.parse.clone());
    let previous_semantic = documents.get(&uri).and_then(|doc| doc.semantic.clone());
    documents.insert(
        uri,
        DocumentState {
            version,
            text,
            dirty,
            parse: previous_parse,
            semantic: previous_semantic,
            diagnostics: Vec::new(),
        },
    );
}

fn apply_parse_result(
    shared: &SharedState,
    uri: &Url,
    result: ParseJobResult,
) -> Option<AppliedParseResult> {
    let mut documents = shared.documents.lock().ok()?;
    let document = documents.get_mut(uri)?;
    if document.version != result.version {
        trace(format!(
            "discard stale analysis uri={uri} result_version={} current_version={}",
            result.version, document.version
        ));
        return None;
    }

    let mut parsed_program = None;
    let document_is_dirty = document.dirty;
    let had_semantic = result.semantic.is_some();
    if let Some(parse) = result.parse {
        debug_assert_eq!(parse.version, result.version);
        parsed_program = Some(parse.program.clone());
        document.parse = Some(Arc::new(parse));
    }
    if let Some(semantic) = result.semantic {
        debug_assert_eq!(semantic.version, result.version);
        document.semantic = Some(Arc::new(semantic));
    }
    document.diagnostics = result.diagnostics.clone();
    drop(documents);

    let project_root = project_root_for_uri(uri);
    let interface_apply = {
        let mut projects = shared.projects.lock().ok()?;
        let module_interfaces = if document_is_dirty {
            result
                .module_interfaces
                .into_iter()
                .filter(|update| !update.is_current)
                .collect()
        } else {
            result.module_interfaces
        };
        projects.apply_module_interface_updates(project_root.clone(), module_interfaces)
    };
    if let Some(update) = result.semantic_index_update.filter(|_| !document_is_dirty) {
        let module_name = update.module_name.clone();
        let mut projects = shared.projects.lock().ok()?;
        projects.update_semantic_index(project_root.clone(), update);
        trace(format!(
            "project semantic index updated module={module_name} root={}",
            display_project_root(project_root.as_ref())
        ));
    }
    if interface_apply.updated > 0 {
        trace(format!(
            "cached module interfaces root={} count={} current_changed={} saw_current={}",
            display_project_root(project_root.as_ref()),
            interface_apply.updated,
            interface_apply.current_changed,
            interface_apply.saw_current
        ));
    }

    if let Some(program) = parsed_program.filter(|_| !document_is_dirty) {
        let (module_name, imports) = extract_module_info(&program);
        let generation = {
            let mut projects = shared.projects.lock().ok()?;
            projects.update_file(project_root.clone(), uri, module_name, imports)
        };
        trace(format!(
            "project graph updated uri={uri} root={} generation={generation}",
            display_project_root(project_root.as_ref())
        ));
    }

    let should_recheck_dependents = result.force_dependents
        || (had_semantic && (!interface_apply.saw_current || interface_apply.current_changed));
    let dependents = if should_recheck_dependents {
        let projects = shared.projects.lock().ok()?;
        projects.dependents_of(&project_root, uri)
    } else {
        trace(format!(
            "skip dependents uri={uri} root={} reason=interface-unchanged",
            display_project_root(project_root.as_ref())
        ));
        Vec::new()
    };

    Some(AppliedParseResult {
        diagnostics: result.diagnostics,
        dependents,
    })
}

fn current_document(shared: &SharedState, uri: &Url) -> Option<DocumentState> {
    let documents = shared.documents.lock().ok()?;
    documents.get(uri).cloned()
}

async fn publish_syntax_snapshot(
    client: &Client,
    shared: &SharedState,
    uri: &Url,
    version: i32,
    text: &str,
) {
    let result = analyze_syntax_document(Some(uri), version, text);
    if let Some(applied) = apply_parse_result(shared, uri, result) {
        trace(format!(
            "publish syntax diagnostics uri={uri} version={version} count={}",
            applied.diagnostics.len()
        ));
        client
            .publish_diagnostics(uri.clone(), applied.diagnostics, Some(version))
            .await;
    }
}

fn document_version_is_current(shared: &SharedState, uri: Option<&Url>, version: i32) -> bool {
    let Some(uri) = uri else {
        return true;
    };
    current_document(shared, uri).is_none_or(|document| document.version == version)
}

fn extract_module_info(
    program: &[ast::Decl],
) -> (Option<String>, std::collections::HashSet<String>) {
    let mut module_name = None;
    let mut imports = std::collections::HashSet::new();
    for decl in program {
        match decl {
            ast::Decl::ModuleDecl { path, .. } => {
                module_name = Some(path.join("."));
            }
            ast::Decl::Import { module_path, .. } => {
                imports.insert(module_path.join("."));
            }
            _ => {}
        }
    }
    (module_name, imports)
}

fn formatting_edits(uri: &Url, source: &str) -> Option<Vec<TextEdit>> {
    let tokens = lexer::Lexer::new(source).lex().ok()?;
    let mut parser = parser::Parser::new(tokens);
    let program = parser.parse_program_annotated().ok()?;
    let width = project_root_for_uri(uri)
        .map(|root| project_config::ProjectConfig::load(&root).formatter.width)
        .unwrap_or(formatter::DEFAULT_WIDTH);
    let formatted = formatter::format(&program, width);
    if formatted == source {
        return Some(Vec::new());
    }
    Some(vec![TextEdit {
        range: full_document_range(source),
        new_text: formatted,
    }])
}

fn is_saga_file_uri(uri: &Url) -> bool {
    uri.to_file_path()
        .ok()
        .and_then(|path| path.extension().map(|ext| ext == "saga"))
        .unwrap_or(false)
}

fn recheck_open_documents_in_project(
    shared: &SharedState,
    check_tx: &tokio::sync::mpsc::UnboundedSender<CheckRequest>,
    project_root: Option<PathBuf>,
) {
    let documents = {
        let documents = shared.documents.lock().unwrap_or_else(|e| e.into_inner());
        documents
            .iter()
            .filter_map(|(uri, document)| {
                if project_root_for_uri(uri) != project_root {
                    return None;
                }
                Some((uri.clone(), document.version, document.text.clone()))
            })
            .collect::<Vec<_>>()
    };

    for (uri, version, text) in documents {
        let _ = check_tx.send(CheckRequest {
            uri,
            version,
            text,
            project_root: project_root.clone(),
            is_primary: true,
        });
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
                document_symbol_provider: Some(OneOf::Left(true)),
                completion_provider: Some(CompletionOptions {
                    trigger_characters: Some(vec![
                        ".".into(),
                        "{".into(),
                        ":".into(),
                        "(".into(),
                        ",".into(),
                    ]),
                    ..Default::default()
                }),
                signature_help_provider: Some(SignatureHelpOptions {
                    trigger_characters: Some(vec![" ".into(), "(".into(), ",".into()]),
                    retrigger_characters: None,
                    work_done_progress_options: WorkDoneProgressOptions::default(),
                }),
                hover_provider: Some(HoverProviderCapability::Simple(true)),
                definition_provider: Some(OneOf::Left(true)),
                references_provider: Some(OneOf::Left(true)),
                code_action_provider: Some(CodeActionProviderCapability::Simple(true)),
                document_formatting_provider: Some(OneOf::Left(true)),
                rename_provider: Some(OneOf::Right(RenameOptions {
                    prepare_provider: Some(true),
                    work_done_progress_options: WorkDoneProgressOptions::default(),
                })),
                ..Default::default()
            },
            ..Default::default()
        })
    }

    async fn initialized(&self, _: InitializedParams) {
        let client = self.client.clone();
        tokio::spawn(async move {
            let options = DidChangeWatchedFilesRegistrationOptions {
                watchers: vec![FileSystemWatcher {
                    glob_pattern: GlobPattern::String("**/*.saga".to_string()),
                    kind: Some(WatchKind::Create | WatchKind::Change | WatchKind::Delete),
                }],
            };
            let registration = Registration {
                id: "saga-watch-saga-files".to_string(),
                method: "workspace/didChangeWatchedFiles".to_string(),
                register_options: serde_json::to_value(options).ok(),
            };
            if let Err(err) = client.register_capability(vec![registration]).await {
                client
                    .log_message(
                        MessageType::WARNING,
                        format!("failed to register saga file watcher: {err}"),
                    )
                    .await;
            }
        });
        self.client
            .log_message(MessageType::INFO, "saga LSP next initialized")
            .await;
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        let uri = params.text_document.uri;
        let version = params.text_document.version;
        let text = params.text_document.text;
        let project_root = project_root_for_uri(&uri);
        store_document(&self.shared, uri.clone(), version, text.clone(), false);
        publish_syntax_snapshot(&self.client, &self.shared, &uri, version, &text).await;
        let _ = self.check_tx.send(CheckRequest {
            uri,
            version,
            text,
            project_root,
            is_primary: true,
        });
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        let uri = params.text_document.uri;
        let version = params.text_document.version;
        let project_root = project_root_for_uri(&uri);
        let Some(change) = params.content_changes.into_iter().last() else {
            return;
        };
        let text = change.text;
        store_document(&self.shared, uri.clone(), version, text.clone(), true);
        publish_syntax_snapshot(&self.client, &self.shared, &uri, version, &text).await;
        let _ = self.check_tx.send(CheckRequest {
            uri,
            version,
            text,
            project_root,
            is_primary: true,
        });
    }

    async fn did_save(&self, params: DidSaveTextDocumentParams) {
        let uri = params.text_document.uri;
        let project_root = project_root_for_uri(&uri);
        let Some(doc) = current_document(&self.shared, &uri) else {
            return;
        };
        let text = params.text.unwrap_or(doc.text);
        let version = doc.version;
        store_document(&self.shared, uri.clone(), version, text.clone(), false);
        publish_syntax_snapshot(&self.client, &self.shared, &uri, version, &text).await;
        let _ = self.check_tx.send(CheckRequest {
            uri,
            version,
            text,
            project_root,
            is_primary: true,
        });
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        let uri = params.text_document.uri;
        {
            let mut documents = self
                .shared
                .documents
                .lock()
                .unwrap_or_else(|e| e.into_inner());
            documents.remove(&uri);
        }
        {
            let mut projects = self
                .shared
                .projects
                .lock()
                .unwrap_or_else(|e| e.into_inner());
            projects.remove_file_from_all_projects(&uri);
        }
        self.client.publish_diagnostics(uri, Vec::new(), None).await;
    }

    async fn did_change_watched_files(&self, params: DidChangeWatchedFilesParams) {
        let mut affected_roots = HashSet::new();
        for change in params.changes {
            if !is_saga_file_uri(&change.uri) {
                continue;
            }
            let project_root = project_root_for_uri(&change.uri);
            affected_roots.insert(project_root.clone());
            if change.typ == FileChangeType::DELETED
                && current_document(&self.shared, &change.uri).is_none()
            {
                let mut projects = self
                    .shared
                    .projects
                    .lock()
                    .unwrap_or_else(|e| e.into_inner());
                projects.remove_file_from_all_projects(&change.uri);
            }
        }

        for project_root in affected_roots {
            recheck_open_documents_in_project(&self.shared, &self.check_tx, project_root);
        }
    }

    async fn document_symbol(
        &self,
        params: DocumentSymbolParams,
    ) -> Result<Option<DocumentSymbolResponse>> {
        let uri = params.text_document.uri;
        let Some(document) = current_document(&self.shared, &uri) else {
            return Ok(None);
        };
        let Some(parse) = document.parse else {
            return Ok(None);
        };

        let symbols =
            collect_document_symbols(&uri, &parse.program, &parse.line_index, &parse.source);
        if symbols.is_empty() {
            Ok(None)
        } else {
            Ok(Some(DocumentSymbolResponse::Flat(symbols)))
        }
    }

    async fn formatting(&self, params: DocumentFormattingParams) -> Result<Option<Vec<TextEdit>>> {
        let uri = params.text_document.uri;
        let Some(document) = current_document(&self.shared, &uri) else {
            return Ok(None);
        };

        Ok(formatting_edits(&uri, &document.text))
    }

    async fn code_action(&self, params: CodeActionParams) -> Result<Option<CodeActionResponse>> {
        let uri = params.text_document.uri;
        let Some(document) = current_document(&self.shared, &uri) else {
            return Ok(None);
        };
        let Some(semantic) = &document.semantic else {
            return Ok(None);
        };
        if semantic.version != document.version {
            return Ok(None);
        }

        let project_root = project_root_for_uri(&uri);
        let projects = self
            .shared
            .projects
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let actions = collect_code_actions(
            &uri,
            &document,
            semantic,
            Some((&projects, &project_root)),
            params.range,
            &params.context.diagnostics,
        );
        if actions.is_empty() {
            Ok(None)
        } else {
            Ok(Some(actions))
        }
    }

    async fn completion(&self, params: CompletionParams) -> Result<Option<CompletionResponse>> {
        let uri = params.text_document_position.text_document.uri;
        let position = params.text_document_position.position;
        let Some(document) = current_document(&self.shared, &uri) else {
            return Ok(None);
        };

        let project_root = project_root_for_uri(&uri);
        let projects = self
            .shared
            .projects
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let items = collect_completion_items(&document, position, Some((&projects, &project_root)));
        if items.is_empty() {
            Ok(None)
        } else {
            Ok(Some(CompletionResponse::Array(items)))
        }
    }

    async fn hover(&self, params: HoverParams) -> Result<Option<Hover>> {
        let uri = params.text_document_position_params.text_document.uri;
        let position = params.text_document_position_params.position;
        let Some(document) = current_document(&self.shared, &uri) else {
            return Ok(None);
        };
        let Some(semantic) = document.semantic else {
            return Ok(None);
        };

        if semantic.version != document.version {
            return Ok(None);
        }

        let project_root = project_root_for_uri(&uri);
        let projects = self
            .shared
            .projects
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        Ok(hover_type_at(
            &uri,
            &semantic,
            position,
            Some((&projects, &project_root)),
        ))
    }

    async fn signature_help(&self, params: SignatureHelpParams) -> Result<Option<SignatureHelp>> {
        let uri = params.text_document_position_params.text_document.uri;
        let position = params.text_document_position_params.position;
        let Some(document) = current_document(&self.shared, &uri) else {
            return Ok(None);
        };
        let Some(semantic) = &document.semantic else {
            return Ok(None);
        };
        if semantic.version != document.version {
            return Ok(None);
        }

        let project_root = project_root_for_uri(&uri);
        let projects = self
            .shared
            .projects
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        Ok(signature_help_at(
            &document,
            semantic,
            position,
            Some((&projects, &project_root)),
        ))
    }

    async fn goto_definition(
        &self,
        params: GotoDefinitionParams,
    ) -> Result<Option<GotoDefinitionResponse>> {
        let uri = params.text_document_position_params.text_document.uri;
        let position = params.text_document_position_params.position;
        let Some(document) = current_document(&self.shared, &uri) else {
            return Ok(None);
        };
        let Some(semantic) = document.semantic else {
            return Ok(None);
        };

        if semantic.version != document.version {
            return Ok(None);
        }

        let mut location = local_definition_at(&uri, &semantic, position);
        if location.is_none() {
            let project_root = project_root_for_uri(&uri);
            let projects = self
                .shared
                .projects
                .lock()
                .unwrap_or_else(|e| e.into_inner());
            if let Some(module_name) = semantic
                .semantic_index
                .module_name_at_position(&uri, position)
            {
                location = projects.project_module_definition_location(&project_root, module_name);
            }
            if location.is_none()
                && let Some(type_name) = semantic
                    .semantic_index
                    .type_name_at_position(&uri, position)
            {
                location = projects.project_type_definition_location(&project_root, type_name);
            }
            if location.is_none()
                && let Some(key) = semantic
                    .semantic_index
                    .symbol_key_at_position(&uri, position)
            {
                location = projects.project_symbol_definition_location(&project_root, key);
            }
        }

        Ok(location.map(GotoDefinitionResponse::Scalar))
    }

    async fn references(&self, params: ReferenceParams) -> Result<Option<Vec<Location>>> {
        let uri = params.text_document_position.text_document.uri;
        let position = params.text_document_position.position;
        let Some(document) = current_document(&self.shared, &uri) else {
            return Ok(None);
        };
        let Some(semantic) = document.semantic else {
            return Ok(None);
        };

        if semantic.version != document.version {
            return Ok(None);
        }

        let mut locations = references_at(
            &uri,
            &semantic,
            position,
            params.context.include_declaration,
        );
        if let Some(module_name) = semantic
            .semantic_index
            .module_name_at_position(&uri, position)
        {
            let project_root = project_root_for_uri(&uri);
            let projects = self
                .shared
                .projects
                .lock()
                .unwrap_or_else(|e| e.into_inner());
            locations.extend(projects.project_module_reference_locations(
                &project_root,
                module_name,
                params.context.include_declaration,
            ));
            sort_and_dedup_locations(&mut locations);
        }
        if let Some(type_name) = semantic
            .semantic_index
            .type_name_at_position(&uri, position)
        {
            let project_root = project_root_for_uri(&uri);
            let projects = self
                .shared
                .projects
                .lock()
                .unwrap_or_else(|e| e.into_inner());
            locations.extend(projects.project_type_reference_locations(
                &project_root,
                type_name,
                params.context.include_declaration,
            ));
            sort_and_dedup_locations(&mut locations);
        }
        if let Some(key) = semantic
            .semantic_index
            .symbol_key_at_position(&uri, position)
        {
            let project_root = project_root_for_uri(&uri);
            let projects = self
                .shared
                .projects
                .lock()
                .unwrap_or_else(|e| e.into_inner());
            locations.extend(projects.project_symbol_reference_locations(
                &project_root,
                key,
                params.context.include_declaration,
            ));
            sort_and_dedup_locations(&mut locations);
        }
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
        let uri = params.text_document.uri;
        let position = params.position;
        let Some(document) = current_document(&self.shared, &uri) else {
            return Ok(None);
        };
        let Some(semantic) = document.semantic else {
            return Ok(None);
        };

        if semantic.version != document.version {
            return Ok(None);
        }

        Ok(rename_target_at(&uri, &semantic, position)
            .map(|(_, range)| PrepareRenameResponse::Range(range)))
    }

    async fn rename(&self, params: RenameParams) -> Result<Option<WorkspaceEdit>> {
        let uri = params.text_document_position.text_document.uri;
        let position = params.text_document_position.position;
        let Some(document) = current_document(&self.shared, &uri) else {
            return Ok(None);
        };
        let Some(semantic) = document.semantic else {
            return Ok(None);
        };

        if semantic.version != document.version {
            return Ok(None);
        }

        let Some((target, _)) = rename_target_at(&uri, &semantic, position) else {
            return Ok(None);
        };
        if !valid_rename_name(&params.new_name, &target) {
            return Ok(None);
        }

        let project_root = project_root_for_uri(&uri);
        let mut locations = match &target {
            RenameTarget::Module(module_name) => semantic
                .semantic_index
                .module_reference_locations_for_name(module_name, true),
            RenameTarget::Type(type_name) => semantic
                .semantic_index
                .type_reference_locations_for_name(type_name, true),
            RenameTarget::Symbol(key) => semantic
                .semantic_index
                .symbol_reference_locations_for_key(key, true),
            RenameTarget::Value(definition_id) => semantic
                .semantic_index
                .reference_locations_for_node(*definition_id, true),
        };

        match &target {
            RenameTarget::Module(module_name) => {
                let projects = self
                    .shared
                    .projects
                    .lock()
                    .unwrap_or_else(|e| e.into_inner());
                locations.extend(projects.project_module_reference_locations(
                    &project_root,
                    module_name,
                    true,
                ));
            }
            RenameTarget::Type(type_name) => {
                let projects = self
                    .shared
                    .projects
                    .lock()
                    .unwrap_or_else(|e| e.into_inner());
                locations.extend(projects.project_type_reference_locations(
                    &project_root,
                    type_name,
                    true,
                ));
            }
            RenameTarget::Symbol(key) => {
                let projects = self
                    .shared
                    .projects
                    .lock()
                    .unwrap_or_else(|e| e.into_inner());
                locations.extend(projects.project_symbol_reference_locations(
                    &project_root,
                    key,
                    true,
                ));
            }
            RenameTarget::Value(_) => {}
        }
        sort_and_dedup_locations(&mut locations);

        Ok(workspace_edit_from_locations(locations, params.new_name))
    }
}

#[tokio::main]
async fn main() {
    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    let (check_tx, check_rx) = tokio::sync::mpsc::unbounded_channel();

    let (service, socket) = LspService::new(|client| {
        let shared = Arc::new(SharedState::default());
        tokio::spawn(debounce_loop(
            check_rx,
            check_tx.clone(),
            client.clone(),
            Arc::clone(&shared),
        ));

        Backend {
            client,
            shared,
            check_tx,
        }
    });

    Server::new(stdin, stdout, socket).serve(service).await;
}

#[cfg(test)]
mod tests;
