use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};
use std::time::{Duration as StdDuration, Instant as StdInstant};

use saga::{ast, derive, desugar, lexer, parser, project_config, typechecker};
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};

const SEMANTIC_DEBOUNCE_MS: u64 = 100;

#[derive(Clone)]
struct DocumentState {
    version: i32,
    text: String,
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
    definition_locations: HashMap<ast::NodeId, Location>,
}

#[derive(Default)]
struct SharedState {
    documents: Mutex<HashMap<Url, DocumentState>>,
    projects: Mutex<ProjectSemanticStore>,
}

#[derive(Default)]
struct ProjectSemanticStore {
    projects: HashMap<Option<PathBuf>, ProjectSemanticState>,
}

struct ProjectSemanticState {
    generation: u64,
    dep_graph: DependencyGraph,
    base_checker: Option<typechecker::Checker>,
    module_interfaces: HashMap<String, CachedModuleInterface>,
}

#[derive(Clone)]
struct CachedModuleInterface {
    path: Option<PathBuf>,
    source_fingerprint: u64,
    interface_fingerprint: u64,
    exports: typechecker::ModuleExports,
    codegen_info: Option<typechecker::ModuleCodegenInfo>,
    check_result: Option<typechecker::CheckResult>,
}

struct ModuleInterfaceUpdate {
    module_name: String,
    path: Option<PathBuf>,
    source_fingerprint: u64,
    interface_fingerprint: u64,
    exports: typechecker::ModuleExports,
    codegen_info: Option<typechecker::ModuleCodegenInfo>,
    check_result: Option<typechecker::CheckResult>,
    is_current: bool,
}

impl ProjectSemanticState {
    fn new() -> Self {
        Self {
            generation: 0,
            dep_graph: DependencyGraph::default(),
            base_checker: None,
            module_interfaces: HashMap::new(),
        }
    }
}

impl ProjectSemanticStore {
    fn project_mut(&mut self, project_root: Option<PathBuf>) -> &mut ProjectSemanticState {
        self.projects
            .entry(project_root)
            .or_insert_with(ProjectSemanticState::new)
    }

    fn base_checker(&self, project_root: &Option<PathBuf>) -> Option<typechecker::Checker> {
        self.projects
            .get(project_root)
            .and_then(|project| project.base_checker.clone())
    }

    fn store_base_checker(
        &mut self,
        project_root: Option<PathBuf>,
        checker: typechecker::Checker,
    ) -> typechecker::Checker {
        let project = self.project_mut(project_root);
        project
            .base_checker
            .get_or_insert_with(|| checker.clone())
            .clone()
    }

    fn update_file(
        &mut self,
        project_root: Option<PathBuf>,
        uri: &Url,
        module_name: Option<String>,
        new_imports: std::collections::HashSet<String>,
    ) -> u64 {
        let project = self.project_mut(project_root);
        project.dep_graph.update_file(uri, module_name, new_imports);
        project.generation = project.generation.saturating_add(1);
        project.generation
    }

    fn dependents_of(&self, project_root: &Option<PathBuf>, uri: &Url) -> Vec<Url> {
        self.projects
            .get(project_root)
            .map(|project| project.dep_graph.dependents_of(uri))
            .unwrap_or_default()
    }

    fn remove_file_from_all_projects(&mut self, uri: &Url) {
        for project in self.projects.values_mut() {
            project.dep_graph.remove_file(uri);
            project.generation = project.generation.saturating_add(1);
        }
    }

    fn seed_module_interfaces(
        &self,
        project_root: &Option<PathBuf>,
        checker: &mut typechecker::Checker,
        source_overlay: &HashMap<PathBuf, String>,
        requested_modules: Option<&std::collections::HashSet<String>>,
    ) -> usize {
        let Some(project) = self.projects.get(project_root) else {
            return 0;
        };

        let mut seeded = 0;
        for (module_name, entry) in &project.module_interfaces {
            if requested_modules.is_some_and(|modules| !modules.contains(module_name)) {
                continue;
            }
            let current_fingerprint = match &entry.path {
                Some(path) => source_fingerprint_for_path(path, source_overlay),
                None => builtin_module_source_fingerprint(module_name),
            };
            let Some(current_fingerprint) = current_fingerprint else {
                continue;
            };
            if current_fingerprint != entry.source_fingerprint {
                continue;
            }
            checker.seed_module_cache(
                module_name.clone(),
                entry.exports.clone(),
                entry.codegen_info.clone(),
                None,
                None,
            );
            seeded += 1;
        }
        seeded
    }

    fn apply_module_interface_updates(
        &mut self,
        project_root: Option<PathBuf>,
        updates: Vec<ModuleInterfaceUpdate>,
    ) -> ModuleInterfaceApplyResult {
        let project = self.project_mut(project_root);
        let mut updated = 0;
        let mut current_changed = false;
        let mut saw_current = false;

        for update in updates {
            let previous_fingerprint = project
                .module_interfaces
                .get(&update.module_name)
                .map(|entry| entry.interface_fingerprint);
            if update.is_current {
                saw_current = true;
                current_changed = previous_fingerprint != Some(update.interface_fingerprint);
            }
            let entry = CachedModuleInterface {
                path: update.path,
                source_fingerprint: update.source_fingerprint,
                interface_fingerprint: update.interface_fingerprint,
                exports: update.exports,
                codegen_info: update.codegen_info,
                check_result: update.check_result,
            };
            project.module_interfaces.insert(update.module_name, entry);
            updated += 1;
        }

        ModuleInterfaceApplyResult {
            updated,
            current_changed,
            saw_current,
        }
    }

    fn cached_module_source_fingerprints(
        &self,
        project_root: &Option<PathBuf>,
    ) -> HashMap<String, u64> {
        self.projects
            .get(project_root)
            .map(|project| {
                project
                    .module_interfaces
                    .iter()
                    .map(|(module, entry)| (module.clone(), entry.source_fingerprint))
                    .collect()
            })
            .unwrap_or_default()
    }
}

#[derive(Default)]
struct ModuleInterfaceApplyResult {
    updated: usize,
    current_changed: bool,
    saw_current: bool,
}

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

#[derive(Default)]
struct DependencyGraph {
    dependents: HashMap<String, std::collections::HashSet<Url>>,
    imports: HashMap<Url, std::collections::HashSet<String>>,
    module_of: HashMap<Url, String>,
}

impl DependencyGraph {
    fn update_file(
        &mut self,
        uri: &Url,
        module_name: Option<String>,
        new_imports: std::collections::HashSet<String>,
    ) {
        if let Some(old_imports) = self.imports.remove(uri) {
            for module in old_imports {
                if let Some(dependents) = self.dependents.get_mut(&module) {
                    dependents.remove(uri);
                    if dependents.is_empty() {
                        self.dependents.remove(&module);
                    }
                }
            }
        }

        for module in &new_imports {
            self.dependents
                .entry(module.clone())
                .or_default()
                .insert(uri.clone());
        }
        self.imports.insert(uri.clone(), new_imports);

        match module_name {
            Some(module_name) => {
                self.module_of.insert(uri.clone(), module_name);
            }
            None => {
                self.module_of.remove(uri);
            }
        }
    }

    fn dependents_of(&self, uri: &Url) -> Vec<Url> {
        let Some(module) = self.module_of.get(uri) else {
            return Vec::new();
        };
        self.dependents
            .get(module)
            .map(|uris| uris.iter().cloned().collect())
            .unwrap_or_default()
    }

    fn remove_file(&mut self, uri: &Url) {
        if let Some(old_imports) = self.imports.remove(uri) {
            for module in old_imports {
                if let Some(dependents) = self.dependents.get_mut(&module) {
                    dependents.remove(uri);
                    if dependents.is_empty() {
                        self.dependents.remove(&module);
                    }
                }
            }
        }
        self.module_of.remove(uri);
    }
}

struct Backend {
    client: Client,
    shared: Arc<SharedState>,
    check_tx: tokio::sync::mpsc::UnboundedSender<CheckRequest>,
}

#[derive(Clone)]
struct LineIndex {
    line_starts: Vec<usize>,
}

impl LineIndex {
    fn new(text: &str) -> Self {
        let mut line_starts = vec![0];
        for (i, b) in text.bytes().enumerate() {
            if b == b'\n' {
                line_starts.push(i + 1);
            }
        }
        Self { line_starts }
    }

    fn offset_to_position(&self, offset: usize, source: &str) -> Position {
        let offset = clamp_to_char_boundary(source, offset.min(source.len()));
        let line = self
            .line_starts
            .partition_point(|&start| start <= offset)
            .saturating_sub(1);
        let line_start = self.line_starts.get(line).copied().unwrap_or(0);
        let line_text = &source[line_start..offset];
        let utf16_col: usize = line_text.chars().map(|c| c.len_utf16()).sum();
        Position::new(line as u32, utf16_col as u32)
    }

    fn position_to_offset(&self, position: Position, source: &str) -> usize {
        let line = position.line as usize;
        let Some(&line_start) = self.line_starts.get(line) else {
            return source.len();
        };
        let line_end = self
            .line_starts
            .get(line + 1)
            .copied()
            .unwrap_or(source.len());
        let line_text = &source[line_start..line_end];
        let target_col = position.character as usize;
        let mut utf16_col = 0;

        for (byte_offset, ch) in line_text.char_indices() {
            if utf16_col >= target_col {
                return line_start + byte_offset;
            }
            utf16_col += ch.len_utf16();
        }

        line_end
    }
}

fn clamp_to_char_boundary(source: &str, mut offset: usize) -> usize {
    while offset > 0 && !source.is_char_boundary(offset) {
        offset -= 1;
    }
    offset
}

#[derive(Default)]
struct AnalysisTimings {
    lex: StdDuration,
    parse: StdDuration,
    checker: StdDuration,
    derive_imports: StdDuration,
    derive_expand: StdDuration,
    desugar: StdDuration,
    typecheck: StdDuration,
    cache_update: StdDuration,
    definitions: StdDuration,
    total: StdDuration,
}

fn timed<T>(slot: &mut StdDuration, f: impl FnOnce() -> T) -> T {
    let start = StdInstant::now();
    let result = f();
    *slot = start.elapsed();
    result
}

fn duration_ms(duration: StdDuration) -> String {
    format!("{:.1}ms", duration.as_secs_f64() * 1000.0)
}

fn trace_elapsed(label: impl AsRef<str>, start: StdInstant) {
    trace(format!(
        "{} elapsed={}",
        label.as_ref(),
        duration_ms(start.elapsed())
    ));
}

fn trace(message: impl AsRef<str>) {
    if std::env::var_os("SAGA_LSP_TRACE").is_none() {
        return;
    }

    let line = format!("[saga-lsp] {}", message.as_ref());
    if let Some(path) = std::env::var_os("SAGA_LSP_TRACE_FILE") {
        use std::io::Write;
        if let Ok(mut file) = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(path)
        {
            let _ = writeln!(file, "{line}");
        }
    } else {
        eprintln!("{line}");
    }
}

fn display_project_root(root: Option<&PathBuf>) -> String {
    root.map(|path| path.display().to_string())
        .unwrap_or_else(|| "<loose>".to_string())
}

fn source_fingerprint(source: &str) -> u64 {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    source.hash(&mut hasher);
    hasher.finish()
}

fn module_interface_fingerprint(exports: &typechecker::ModuleExports) -> u64 {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    // This is intentionally conservative for the first LSP slice. Different
    // map iteration orders may over-invalidate, but changed public data should
    // not hash as unchanged.
    format!("{exports:?}").hash(&mut hasher);
    hasher.finish()
}

fn source_fingerprint_for_path(
    path: &Path,
    source_overlay: &HashMap<PathBuf, String>,
) -> Option<u64> {
    if let Some(source) = source_overlay.get(path) {
        return Some(source_fingerprint(source));
    }
    std::fs::read_to_string(path)
        .ok()
        .map(|source| source_fingerprint(&source))
}

fn builtin_module_source_fingerprint(module_name: &str) -> Option<u64> {
    let path: Vec<String> = module_name.split('.').map(str::to_string).collect();
    typechecker::builtin_module_source(&path).map(source_fingerprint)
}

fn collect_module_interface_updates(
    current_uri: Option<&Url>,
    current_program: &ast::Program,
    checker: &typechecker::Checker,
    check: &typechecker::CheckResult,
    source_overlay: &HashMap<PathBuf, String>,
    cached_source_fingerprints: &HashMap<String, u64>,
    include_current: bool,
) -> Vec<ModuleInterfaceUpdate> {
    let mut updates = Vec::new();

    for (module_name, exports) in check.module_exports() {
        let path = check.resolve_module_path(module_name);
        let source_fingerprint = match &path {
            Some(path) => source_fingerprint_for_path(path, source_overlay),
            None => builtin_module_source_fingerprint(module_name),
        };
        let Some(source_fingerprint) = source_fingerprint else {
            continue;
        };
        if cached_source_fingerprints.get(module_name) == Some(&source_fingerprint) {
            continue;
        }
        updates.push(ModuleInterfaceUpdate {
            module_name: module_name.clone(),
            path,
            source_fingerprint,
            interface_fingerprint: module_interface_fingerprint(exports),
            exports: exports.clone(),
            codegen_info: check.codegen_info().get(module_name).cloned(),
            check_result: check.module_check_results().get(module_name).cloned(),
            is_current: false,
        });
    }

    if include_current {
        let (Some(uri), (Some(module_name), _)) =
            (current_uri, extract_module_info(current_program))
        else {
            return updates;
        };
        let Ok(path) = uri.to_file_path() else {
            return updates;
        };
        let Some(source_fingerprint) = source_fingerprint_for_path(&path, source_overlay) else {
            return updates;
        };
        let exports = typechecker::ModuleExports::collect(current_program, checker);
        updates.push(ModuleInterfaceUpdate {
            module_name,
            path: Some(path),
            source_fingerprint,
            interface_fingerprint: module_interface_fingerprint(&exports),
            exports,
            codegen_info: None,
            check_result: Some(check.clone()),
            is_current: true,
        });
    }

    updates
}

fn trace_analysis(
    uri: Option<&Url>,
    version: i32,
    project_root: Option<&PathBuf>,
    stage: &str,
    timings: &AnalysisTimings,
    diagnostics: usize,
) {
    trace(format!(
        "analysis {stage} uri={} version={version} root={} diagnostics={diagnostics} total={} lex={} parse={} checker={} derive_imports={} derive_expand={} desugar={} typecheck={} cache_update={} definitions={}",
        uri.map(ToString::to_string)
            .unwrap_or_else(|| "<unknown>".to_string()),
        display_project_root(project_root),
        duration_ms(timings.total),
        duration_ms(timings.lex),
        duration_ms(timings.parse),
        duration_ms(timings.checker),
        duration_ms(timings.derive_imports),
        duration_ms(timings.derive_expand),
        duration_ms(timings.desugar),
        duration_ms(timings.typecheck),
        duration_ms(timings.cache_update),
        duration_ms(timings.definitions),
    ));
}

fn diagnostic_at(
    line_index: &LineIndex,
    source: &str,
    offset: usize,
    message: String,
) -> Diagnostic {
    let start = line_index.offset_to_position(offset, source);
    let end_offset = (offset.saturating_add(1)).min(source.len());
    let end = line_index.offset_to_position(end_offset, source);
    Diagnostic {
        range: Range { start, end },
        severity: Some(DiagnosticSeverity::ERROR),
        message,
        ..Default::default()
    }
}

fn typechecker_diagnostic_at(
    line_index: &LineIndex,
    source: &str,
    diagnostic: &typechecker::Diagnostic,
) -> Diagnostic {
    let span = diagnostic
        .span
        .unwrap_or(saga::token::Span { start: 0, end: 1 });
    let severity = match diagnostic.severity {
        typechecker::Severity::Error => DiagnosticSeverity::ERROR,
        typechecker::Severity::Warning => DiagnosticSeverity::WARNING,
    };

    Diagnostic {
        range: span_to_range(&span, line_index, source),
        severity: Some(severity),
        message: diagnostic.message.clone(),
        ..Default::default()
    }
}

fn find_project_root(start: &Path) -> Option<PathBuf> {
    let mut dir = start.to_path_buf();
    loop {
        if dir.join("project.toml").exists() {
            return Some(dir);
        }
        if !dir.pop() {
            return None;
        }
    }
}

fn project_root_for_uri(uri: &Url) -> Option<PathBuf> {
    uri.to_file_path()
        .ok()
        .and_then(|path| path.parent().map(Path::to_path_buf))
        .and_then(|dir| find_project_root(&dir))
}

fn checker_for_analysis(
    shared: &SharedState,
    project_root: Option<PathBuf>,
    requested_modules: Option<&std::collections::HashSet<String>>,
) -> std::result::Result<typechecker::Checker, typechecker::Diagnostic> {
    trace(format!(
        "checker prep start root={}",
        display_project_root(project_root.as_ref())
    ));
    let overlay_start = StdInstant::now();
    let source_overlay = open_source_overlay(shared);
    trace_elapsed("checker prep overlay-build", overlay_start);
    trace(format!(
        "checker prep overlay root={} count={}",
        display_project_root(project_root.as_ref()),
        source_overlay.len()
    ));
    let open_modules_start = StdInstant::now();
    let open_modules = open_module_map(shared, project_root.as_deref());
    trace_elapsed("checker prep open-modules-build", open_modules_start);
    trace(format!(
        "checker prep open-modules root={} count={}",
        display_project_root(project_root.as_ref()),
        open_modules.len()
    ));

    let base_lookup_start = StdInstant::now();
    let cached_base = {
        let projects = shared.projects.lock().unwrap_or_else(|e| e.into_inner());
        projects.base_checker(&project_root)
    };
    trace_elapsed("checker prep base-lookup", base_lookup_start);

    if let Some(base) = cached_base {
        trace(format!(
            "checker prep base-cache-hit root={}",
            display_project_root(project_root.as_ref())
        ));
        let prepare_start = StdInstant::now();
        let mut checker = prepare_checker_for_analysis(
            base,
            project_root.clone(),
            source_overlay.clone(),
            open_modules,
        );
        trace_elapsed("checker prep prepare-checker", prepare_start);
        trace(format!(
            "checker prep prepared root={}",
            display_project_root(project_root.as_ref())
        ));
        let seed_start = StdInstant::now();
        let seeded = shared
            .projects
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .seed_module_interfaces(
                &project_root,
                &mut checker,
                &source_overlay,
                requested_modules,
            );
        trace_elapsed("checker prep seed-interfaces", seed_start);
        if seeded > 0 {
            trace(format!(
                "seeded module interfaces root={} count={seeded}",
                display_project_root(project_root.as_ref())
            ));
        }
        trace(format!(
            "checker prep finish root={}",
            display_project_root(project_root.as_ref())
        ));
        return Ok(checker);
    }

    trace(format!(
        "checker prep base-cache-miss root={}",
        display_project_root(project_root.as_ref())
    ));
    let mut built = checker_base_for_project(project_root.clone())?;
    trace(format!(
        "checker prep base-built root={}",
        display_project_root(project_root.as_ref())
    ));
    let warmed_interfaces = collect_module_interface_updates(
        None,
        &Vec::new(),
        &built,
        &built.to_result(),
        &source_overlay,
        &HashMap::new(),
        false,
    );
    if !warmed_interfaces.is_empty() {
        let applied = shared
            .projects
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .apply_module_interface_updates(project_root.clone(), warmed_interfaces);
        trace(format!(
            "checker prep harvested warmed interfaces root={} count={}",
            display_project_root(project_root.as_ref()),
            applied.updated
        ));
    }
    built.clear_module_semantic_caches();
    let base = {
        let mut projects = shared.projects.lock().unwrap_or_else(|e| e.into_inner());
        projects.store_base_checker(project_root.clone(), built)
    };
    trace(format!(
        "checker prep base-stored root={}",
        display_project_root(project_root.as_ref())
    ));
    let mut checker = prepare_checker_for_analysis(
        base,
        project_root.clone(),
        source_overlay.clone(),
        open_modules,
    );
    trace(format!(
        "checker prep prepared root={}",
        display_project_root(project_root.as_ref())
    ));
    let seeded = shared
        .projects
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .seed_module_interfaces(
            &project_root,
            &mut checker,
            &source_overlay,
            requested_modules,
        );
    if seeded > 0 {
        trace(format!(
            "seeded module interfaces root={} count={seeded}",
            display_project_root(project_root.as_ref())
        ));
    }
    trace(format!(
        "checker prep finish root={}",
        display_project_root(project_root.as_ref())
    ));
    Ok(checker)
}

fn checker_base_for_project(
    project_root: Option<PathBuf>,
) -> std::result::Result<typechecker::Checker, typechecker::Diagnostic> {
    let mut checker = typechecker::Checker::with_prelude(project_root.clone())?;
    if let Some(root) = &project_root {
        let config = project_config::ProjectConfig::load(root);
        if let Some(deps) = &config.deps
            && let Err(e) = project_config::resolve_deps(&mut checker, root, deps)
        {
            eprintln!("[LSP] Warning: failed to resolve dependencies: {e}");
        }
        warm_dependency_modules(&mut checker, root);
    }
    Ok(checker)
}

fn warm_dependency_modules(checker: &mut typechecker::Checker, root: &Path) {
    let mut dependency_modules: Vec<String> = checker
        .module_map()
        .into_iter()
        .flat_map(|module_map| module_map.iter())
        .filter(|(_, path)| !is_local_project_module_path(root, path))
        .map(|(module, _)| module.clone())
        .collect();
    dependency_modules.sort();

    for module in dependency_modules {
        if let Err(e) = checker.try_typecheck_import_by_name(&module) {
            eprintln!("[LSP] Warning: failed to warm dependency module '{module}': {e}");
        }
    }
}

fn prepare_checker_for_analysis(
    mut checker: typechecker::Checker,
    project_root: Option<PathBuf>,
    source_overlay: HashMap<PathBuf, String>,
    open_modules: typechecker::ModuleMap,
) -> typechecker::Checker {
    if let Some(root) = project_root
        && let Ok(module_map) = typechecker::scan_project_modules(&root)
    {
        let mut refreshed_map = checker.module_map().cloned().unwrap_or_default();
        refreshed_map.retain(|_, path| !is_local_project_module_path(&root, path));
        for path in open_modules.values() {
            refreshed_map.retain(|_, existing_path| existing_path != path);
        }
        refreshed_map.extend(module_map);
        refreshed_map.extend(open_modules);
        checker.set_module_map(refreshed_map);
    }
    checker.set_source_overlay(source_overlay);
    checker
}

fn is_local_project_module_path(root: &Path, path: &Path) -> bool {
    path.starts_with(root.join("src")) || path.starts_with(root.join("lib"))
}

fn open_source_overlay(shared: &SharedState) -> HashMap<PathBuf, String> {
    let documents = shared.documents.lock().unwrap_or_else(|e| e.into_inner());
    documents
        .iter()
        .filter_map(|(uri, document)| Some((uri.to_file_path().ok()?, document.text.clone())))
        .collect()
}

fn open_module_map(shared: &SharedState, project_root: Option<&Path>) -> typechecker::ModuleMap {
    let documents = shared.documents.lock().unwrap_or_else(|e| e.into_inner());
    documents
        .iter()
        .filter_map(|(uri, document)| {
            let path = uri.to_file_path().ok()?;
            if let Some(root) = project_root
                && !path.starts_with(root)
            {
                return None;
            }
            let parse = document.parse.as_ref()?;
            let (module_name, _) = extract_module_info(&parse.program);
            Some((module_name?, path))
        })
        .collect()
}

fn analyze_document(
    shared: &SharedState,
    uri: Option<&Url>,
    version: i32,
    text: &str,
    project_root: Option<PathBuf>,
) -> ParseJobResult {
    let total_start = StdInstant::now();
    let mut timings = AnalysisTimings::default();
    let line_index = LineIndex::new(text);

    let tokens = match timed(&mut timings.lex, || lexer::Lexer::new(text).lex()) {
        Ok(tokens) => tokens,
        Err(e) => {
            let diagnostics = vec![diagnostic_at(&line_index, text, e.pos, e.message)];
            timings.total = total_start.elapsed();
            trace_analysis(
                uri,
                version,
                project_root.as_ref(),
                "lex-error",
                &timings,
                diagnostics.len(),
            );
            return ParseJobResult {
                version,
                parse: None,
                semantic: None,
                diagnostics,
                module_interfaces: Vec::new(),
                force_dependents: true,
            };
        }
    };
    trace(format!(
        "analysis checkpoint uri={} version={version} stage=lex-ok",
        uri.map(ToString::to_string)
            .unwrap_or_else(|| "<unknown>".to_string())
    ));

    let mut parser = parser::Parser::new(tokens);
    match timed(&mut timings.parse, || parser.parse_program()) {
        Ok(program) => {
            trace(format!(
                "analysis checkpoint uri={} version={version} stage=parse-ok",
                uri.map(ToString::to_string)
                    .unwrap_or_else(|| "<unknown>".to_string())
            ));
            let source: Arc<str> = Arc::from(text);
            let parse = ParseSnapshot {
                version,
                source: Arc::clone(&source),
                line_index: line_index.clone(),
                program: program.clone(),
            };
            let (_, direct_imports) = extract_module_info(&program);

            let mut checker = match timed(&mut timings.checker, || {
                checker_for_analysis(shared, project_root.clone(), Some(&direct_imports))
            }) {
                Ok(checker) => checker,
                Err(e) => {
                    let diagnostics = vec![typechecker_diagnostic_at(&line_index, text, &e)];
                    timings.total = total_start.elapsed();
                    trace_analysis(
                        uri,
                        version,
                        project_root.as_ref(),
                        "checker-error",
                        &timings,
                        diagnostics.len(),
                    );
                    return ParseJobResult {
                        version,
                        parse: Some(parse),
                        semantic: None,
                        diagnostics,
                        module_interfaces: Vec::new(),
                        force_dependents: true,
                    };
                }
            };
            trace(format!(
                "analysis checkpoint uri={} version={version} stage=checker-ok",
                uri.map(ToString::to_string)
                    .unwrap_or_else(|| "<unknown>".to_string())
            ));

            let source_overlay = open_source_overlay(shared);
            if let (Some(current_module), _) = extract_module_info(&program) {
                checker.evict_module(&current_module);
            }
            let imported = timed(&mut timings.derive_imports, || {
                derive::collect_imported_decls_with_sources(
                    &program,
                    checker.module_map(),
                    &source_overlay,
                )
            });
            trace(format!(
                "analysis checkpoint uri={} version={version} stage=derive-imports-ok",
                uri.map(ToString::to_string)
                    .unwrap_or_else(|| "<unknown>".to_string())
            ));
            let mut semantic_program = program;
            let derive_errors = timed(&mut timings.derive_expand, || {
                derive::expand_derives(&mut semantic_program, &imported)
            });
            trace(format!(
                "analysis checkpoint uri={} version={version} stage=derive-expand-ok",
                uri.map(ToString::to_string)
                    .unwrap_or_else(|| "<unknown>".to_string())
            ));
            timed(&mut timings.desugar, || {
                desugar::desugar_program(&mut semantic_program)
            });
            trace(format!(
                "analysis checkpoint uri={} version={version} stage=desugar-ok",
                uri.map(ToString::to_string)
                    .unwrap_or_else(|| "<unknown>".to_string())
            ));
            if !document_version_is_current(shared, uri, version) {
                timings.total = total_start.elapsed();
                trace_analysis(
                    uri,
                    version,
                    project_root.as_ref(),
                    "stale-before-typecheck",
                    &timings,
                    0,
                );
                return ParseJobResult {
                    version,
                    parse: Some(parse),
                    semantic: None,
                    diagnostics: Vec::new(),
                    module_interfaces: Vec::new(),
                    force_dependents: false,
                };
            }
            let check = timed(&mut timings.typecheck, || {
                checker.check_program_lsp(&mut semantic_program)
            });
            trace(format!(
                "analysis checkpoint uri={} version={version} stage=typecheck-ok",
                uri.map(ToString::to_string)
                    .unwrap_or_else(|| "<unknown>".to_string())
            ));
            let include_current_interface = !check.has_errors()
                && derive_errors
                    .iter()
                    .all(|diagnostic| !matches!(diagnostic.severity, typechecker::Severity::Error));
            let cached_source_fingerprints = shared
                .projects
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .cached_module_source_fingerprints(&project_root);
            trace(format!(
                "interface cache snapshot root={} count={}",
                display_project_root(project_root.as_ref()),
                cached_source_fingerprints.len()
            ));
            let module_interfaces = timed(&mut timings.cache_update, || {
                collect_module_interface_updates(
                    uri,
                    &semantic_program,
                    &checker,
                    &check,
                    &source_overlay,
                    &cached_source_fingerprints,
                    include_current_interface,
                )
            });
            if !module_interfaces.is_empty() {
                trace(format!(
                    "prepared module interfaces root={} count={}",
                    display_project_root(project_root.as_ref()),
                    module_interfaces.len()
                ));
            }
            let definition_locations = timed(&mut timings.definitions, || {
                let projects = shared.projects.lock().unwrap_or_else(|e| e.into_inner());
                build_definition_locations(
                    uri,
                    &line_index,
                    text,
                    &check,
                    &source_overlay,
                    CachedDefinitionSources {
                        projects: &projects,
                        project_root: &project_root,
                        direct_imports: &direct_imports,
                    },
                )
            });

            let mut diagnostics: Vec<Diagnostic> = derive_errors
                .iter()
                .map(|d| typechecker_diagnostic_at(&line_index, text, d))
                .collect();
            diagnostics.extend(
                check
                    .diagnostics
                    .iter()
                    .map(|d| typechecker_diagnostic_at(&line_index, text, d)),
            );

            timings.total = total_start.elapsed();
            trace_analysis(
                uri,
                version,
                project_root.as_ref(),
                "ok",
                &timings,
                diagnostics.len(),
            );

            ParseJobResult {
                version,
                parse: Some(parse),
                semantic: Some(SemanticSnapshot {
                    version,
                    source,
                    line_index,
                    check,
                    definition_locations,
                }),
                diagnostics,
                module_interfaces,
                force_dependents: !include_current_interface,
            }
        }
        Err(e) => {
            let diagnostics = vec![diagnostic_at(&line_index, text, e.span.start, e.message)];
            timings.total = total_start.elapsed();
            trace_analysis(
                uri,
                version,
                project_root.as_ref(),
                "parse-error",
                &timings,
                diagnostics.len(),
            );
            ParseJobResult {
                version,
                parse: None,
                semantic: None,
                diagnostics,
                module_interfaces: Vec::new(),
                force_dependents: true,
            }
        }
    }
}

fn build_definition_locations(
    current_uri: Option<&Url>,
    current_line_index: &LineIndex,
    current_source: &str,
    check: &typechecker::CheckResult,
    source_overlay: &HashMap<PathBuf, String>,
    cached: CachedDefinitionSources<'_>,
) -> HashMap<ast::NodeId, Location> {
    let mut locations = HashMap::new();

    if let Some(uri) = current_uri {
        for (node_id, span) in &check.node_spans {
            locations.insert(
                *node_id,
                Location {
                    uri: uri.clone(),
                    range: span_to_range(span, current_line_index, current_source),
                },
            );
        }
    }

    for (module_name, module_result) in check.module_check_results() {
        let Some(path) = check.resolve_module_path(module_name) else {
            continue;
        };
        let Ok(uri) = Url::from_file_path(&path) else {
            continue;
        };
        let source = source_overlay
            .get(&path)
            .cloned()
            .or_else(|| std::fs::read_to_string(&path).ok());
        let Some(source) = source else { continue };
        let line_index = LineIndex::new(&source);
        for (node_id, span) in &module_result.node_spans {
            locations.insert(
                *node_id,
                Location {
                    uri: uri.clone(),
                    range: span_to_range(span, &line_index, &source),
                },
            );
        }
    }

    if let Some(project) = cached.projects.projects.get(cached.project_root) {
        for module_name in cached.direct_imports {
            if check.module_check_results().contains_key(module_name) {
                continue;
            }
            let Some(entry) = project.module_interfaces.get(module_name) else {
                continue;
            };
            let Some(module_result) = entry.check_result.as_ref() else {
                continue;
            };
            let Some(path) = entry.path.as_ref() else {
                continue;
            };
            let Ok(uri) = Url::from_file_path(path) else {
                continue;
            };
            let source = source_overlay
                .get(path)
                .cloned()
                .or_else(|| std::fs::read_to_string(path).ok());
            let Some(source) = source else { continue };
            let line_index = LineIndex::new(&source);
            for (node_id, span) in &module_result.node_spans {
                locations.insert(
                    *node_id,
                    Location {
                        uri: uri.clone(),
                        range: span_to_range(span, &line_index, &source),
                    },
                );
            }
        }
    }

    locations
}

fn store_document(shared: &SharedState, uri: Url, version: i32, text: String) {
    let mut documents = shared.documents.lock().unwrap_or_else(|e| e.into_inner());
    let previous_parse = documents.get(&uri).and_then(|doc| doc.parse.clone());
    let previous_semantic = documents.get(&uri).and_then(|doc| doc.semantic.clone());
    documents.insert(
        uri,
        DocumentState {
            version,
            text,
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
    if let Some(parse) = result.parse {
        debug_assert_eq!(parse.version, result.version);
        debug_assert!(!parse.program.is_empty());
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
        projects.apply_module_interface_updates(project_root.clone(), result.module_interfaces)
    };
    if interface_apply.updated > 0 {
        trace(format!(
            "cached module interfaces root={} count={} current_changed={} saw_current={}",
            display_project_root(project_root.as_ref()),
            interface_apply.updated,
            interface_apply.current_changed,
            interface_apply.saw_current
        ));
    }

    if let Some(program) = parsed_program {
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

    let should_recheck_dependents =
        result.force_dependents || !interface_apply.saw_current || interface_apply.current_changed;
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

fn span_to_range(span: &saga::token::Span, line_index: &LineIndex, source: &str) -> Range {
    Range {
        start: line_index.offset_to_position(span.start, source),
        end: line_index.offset_to_position(span.end, source),
    }
}

#[allow(deprecated)]
fn collect_document_symbols(uri: &Url, parse: &ParseSnapshot) -> Vec<SymbolInformation> {
    let mut symbols = Vec::new();
    let mut annotated = std::collections::HashSet::new();

    for decl in &parse.program {
        if let ast::Decl::FunSignature { name, .. } = decl {
            annotated.insert(name.as_str());
        }
    }

    for decl in &parse.program {
        let symbol = match decl {
            ast::Decl::ModuleDecl { path, span, .. } => Some((
                path.join("."),
                SymbolKind::MODULE,
                span_to_range(span, &parse.line_index, &parse.source),
            )),
            ast::Decl::FunSignature { name, span, .. } => Some((
                name.clone(),
                SymbolKind::FUNCTION,
                span_to_range(span, &parse.line_index, &parse.source),
            )),
            ast::Decl::FunBinding { name, span, .. } if !annotated.contains(name.as_str()) => {
                Some((
                    name.clone(),
                    SymbolKind::FUNCTION,
                    span_to_range(span, &parse.line_index, &parse.source),
                ))
            }
            ast::Decl::Let { name, span, .. } => Some((
                name.clone(),
                SymbolKind::VARIABLE,
                span_to_range(span, &parse.line_index, &parse.source),
            )),
            ast::Decl::TypeDef { name, span, .. } => Some((
                name.clone(),
                SymbolKind::ENUM,
                span_to_range(span, &parse.line_index, &parse.source),
            )),
            ast::Decl::TypeAlias { name, span, .. } => Some((
                name.clone(),
                SymbolKind::TYPE_PARAMETER,
                span_to_range(span, &parse.line_index, &parse.source),
            )),
            ast::Decl::RecordDef { name, span, .. } => Some((
                name.clone(),
                SymbolKind::STRUCT,
                span_to_range(span, &parse.line_index, &parse.source),
            )),
            ast::Decl::EffectDef { name, span, .. } => Some((
                name.clone(),
                SymbolKind::INTERFACE,
                span_to_range(span, &parse.line_index, &parse.source),
            )),
            ast::Decl::HandlerDef { name, span, .. } => Some((
                name.clone(),
                SymbolKind::FUNCTION,
                span_to_range(span, &parse.line_index, &parse.source),
            )),
            ast::Decl::TraitDef { name, span, .. } => Some((
                name.clone(),
                SymbolKind::INTERFACE,
                span_to_range(span, &parse.line_index, &parse.source),
            )),
            ast::Decl::ImplDef {
                trait_name,
                target_type,
                span,
                ..
            } => Some((
                format!("impl {} for {}", trait_name, target_type),
                SymbolKind::CLASS,
                span_to_range(span, &parse.line_index, &parse.source),
            )),
            _ => None,
        };

        if let Some((name, kind, range)) = symbol {
            symbols.push(SymbolInformation {
                name,
                kind,
                location: Location {
                    uri: uri.clone(),
                    range,
                },
                tags: None,
                deprecated: None,
                container_name: None,
            });
        }
    }

    symbols
}

fn extract_prefix(source: &str, offset: usize) -> &str {
    let offset = clamp_to_char_boundary(source, offset.min(source.len()));
    let before = &source[..offset];
    let start = before
        .rfind(|c: char| !c.is_alphanumeric() && c != '_' && c != '\'')
        .map(|i| i + 1)
        .unwrap_or(0);
    &before[start..]
}

fn top_level_completion_names(parse: Option<&ParseSnapshot>) -> Vec<(&str, CompletionItemKind)> {
    let Some(parse) = parse else {
        return Vec::new();
    };

    let mut names = Vec::new();
    let mut annotated = std::collections::HashSet::new();
    for decl in &parse.program {
        if let ast::Decl::FunSignature { name, .. } = decl {
            annotated.insert(name.as_str());
        }
    }

    for decl in &parse.program {
        match decl {
            ast::Decl::FunSignature { name, .. } => {
                names.push((name.as_str(), CompletionItemKind::FUNCTION));
            }
            ast::Decl::FunBinding { name, .. } if !annotated.contains(name.as_str()) => {
                names.push((name.as_str(), CompletionItemKind::FUNCTION));
            }
            ast::Decl::Let { name, .. } => {
                names.push((name.as_str(), CompletionItemKind::VARIABLE));
            }
            ast::Decl::TypeDef { name, .. }
            | ast::Decl::TypeAlias { name, .. }
            | ast::Decl::RecordDef { name, .. } => {
                names.push((name.as_str(), CompletionItemKind::CLASS));
            }
            ast::Decl::EffectDef { name, .. } | ast::Decl::TraitDef { name, .. } => {
                names.push((name.as_str(), CompletionItemKind::INTERFACE));
            }
            ast::Decl::HandlerDef { name, .. } => {
                names.push((name.as_str(), CompletionItemKind::EVENT));
            }
            _ => {}
        }
    }

    names
}

fn collect_completion_items(document: &DocumentState, position: Position) -> Vec<CompletionItem> {
    let line_index = LineIndex::new(&document.text);
    let offset = line_index.position_to_offset(position, &document.text);
    let prefix = extract_prefix(&document.text, offset);
    let prefix_lower = prefix.to_lowercase();
    let mut items = Vec::new();
    let mut seen = std::collections::HashSet::new();

    let keywords = [
        "if", "then", "else", "case", "let", "fun", "type", "record", "effect", "handler", "with",
        "import", "module", "pub", "opaque", "trait", "impl", "where", "needs", "receive", "do",
        "assert",
    ];

    for keyword in keywords {
        if !prefix.is_empty() && !keyword.starts_with(&prefix_lower) {
            continue;
        }
        if seen.insert(keyword.to_string()) {
            items.push(CompletionItem {
                label: keyword.to_string(),
                kind: Some(CompletionItemKind::KEYWORD),
                ..Default::default()
            });
        }
    }

    for (name, kind) in top_level_completion_names(document.parse.as_deref()) {
        if !prefix.is_empty() && !name.to_lowercase().starts_with(&prefix_lower) {
            continue;
        }
        if seen.insert(name.to_string()) {
            items.push(CompletionItem {
                label: name.to_string(),
                kind: Some(kind),
                ..Default::default()
            });
        }
    }

    items.sort_by(|a, b| a.label.cmp(&b.label));
    items
}

fn source_text_at(source: &str, span: saga::token::Span) -> &str {
    if span.start < span.end
        && span.end <= source.len()
        && source.is_char_boundary(span.start)
        && source.is_char_boundary(span.end)
    {
        &source[span.start..span.end]
    } else {
        ""
    }
}

fn hover_type_at(semantic: &SemanticSnapshot, position: Position) -> Option<Hover> {
    let offset = semantic
        .line_index
        .position_to_offset(position, &semantic.source);
    let mut best: Option<(saga::token::Span, String)> = None;

    for span in semantic.check.type_at_span.keys() {
        if offset >= span.start
            && offset <= span.end
            && let Some(type_str) = semantic.check.type_at_span(span)
        {
            let replace = best.as_ref().is_none_or(|(best_span, _)| {
                span.end - span.start < best_span.end - best_span.start
            });
            if replace {
                best = Some((*span, type_str));
            }
        }
    }

    for (node_id, span) in &semantic.check.node_spans {
        if offset >= span.start
            && offset <= span.end
            && let Some(type_str) = semantic.check.type_at_node(node_id)
        {
            let replace = best.as_ref().is_none_or(|(best_span, _)| {
                span.end - span.start < best_span.end - best_span.start
            });
            if replace {
                best = Some((*span, type_str));
            }
        }
    }

    let (span, type_str) = best?;
    let name = source_text_at(&semantic.source, span);
    let code = if name.is_empty() {
        type_str
    } else {
        format!("{name}: {type_str}")
    };

    Some(Hover {
        contents: HoverContents::Markup(MarkupContent {
            kind: MarkupKind::Markdown,
            value: format!("```saga\n{code}\n```"),
        }),
        range: Some(span_to_range(&span, &semantic.line_index, &semantic.source)),
    })
}

fn smallest_node_at_offset(
    node_spans: &HashMap<ast::NodeId, saga::token::Span>,
    offset: usize,
) -> Option<(ast::NodeId, saga::token::Span)> {
    node_spans
        .iter()
        .filter(|(_, span)| offset >= span.start && offset <= span.end)
        .min_by_key(|(_, span)| span.end.saturating_sub(span.start))
        .map(|(id, span)| (*id, *span))
}

fn local_definition_at(
    uri: &Url,
    semantic: &SemanticSnapshot,
    position: Position,
) -> Option<Location> {
    let offset = semantic
        .line_index
        .position_to_offset(position, &semantic.source);
    let (node_id, _) = smallest_node_at_offset(&semantic.check.node_spans, offset)?;
    let def_id = semantic
        .check
        .references
        .get(&node_id)
        .copied()
        .unwrap_or(node_id);
    semantic
        .definition_locations
        .get(&def_id)
        .cloned()
        .or_else(|| {
            let def_span = semantic.check.node_spans.get(&def_id)?;
            Some(Location {
                uri: uri.clone(),
                range: span_to_range(def_span, &semantic.line_index, &semantic.source),
            })
        })
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
                completion_provider: Some(CompletionOptions::default()),
                hover_provider: Some(HoverProviderCapability::Simple(true)),
                definition_provider: Some(OneOf::Left(true)),
                ..Default::default()
            },
            ..Default::default()
        })
    }

    async fn initialized(&self, _: InitializedParams) {
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
        store_document(&self.shared, uri.clone(), version, text.clone());
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
        store_document(&self.shared, uri.clone(), version, text.clone());
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
        store_document(&self.shared, uri.clone(), version, text.clone());
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

        let symbols = collect_document_symbols(&uri, &parse);
        if symbols.is_empty() {
            Ok(None)
        } else {
            Ok(Some(DocumentSymbolResponse::Flat(symbols)))
        }
    }

    async fn completion(&self, params: CompletionParams) -> Result<Option<CompletionResponse>> {
        let uri = params.text_document_position.text_document.uri;
        let position = params.text_document_position.position;
        let Some(document) = current_document(&self.shared, &uri) else {
            return Ok(None);
        };

        let items = collect_completion_items(&document, position);
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

        Ok(hover_type_at(&semantic, position))
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

        Ok(local_definition_at(&uri, &semantic, position).map(GotoDefinitionResponse::Scalar))
    }
}

async fn debounce_loop(
    mut rx: tokio::sync::mpsc::UnboundedReceiver<CheckRequest>,
    tx_for_dependents: tokio::sync::mpsc::UnboundedSender<CheckRequest>,
    client: Client,
    shared: Arc<SharedState>,
) {
    use tokio::time::{Duration, Instant, sleep_until};

    let debounce = Duration::from_millis(SEMANTIC_DEBOUNCE_MS);
    let mut pending: HashMap<Url, (i32, String, Option<PathBuf>, bool, Instant)> = HashMap::new();
    let mut in_flight: std::collections::HashSet<Url> = std::collections::HashSet::new();
    let (done_tx, mut done_rx) = tokio::sync::mpsc::unbounded_channel::<Url>();

    loop {
        if pending.is_empty() && in_flight.is_empty() {
            match rx.recv().await {
                Some(req) => {
                    queue_check_request(&mut pending, req, debounce);
                }
                None => break,
            }
        }

        let next_deadline = pending
            .iter()
            .filter(|(uri, _)| !in_flight.contains(*uri))
            .map(|(_, (_, _, _, _, deadline))| *deadline)
            .min();

        tokio::select! {
            biased;
            result = rx.recv() => {
                match result {
                    Some(req) => {
                        let uri = req.uri.clone();
                        let version = req.version;
                        queue_check_request(&mut pending, req, debounce);
                        if in_flight.contains(&uri) {
                            trace(format!(
                                "coalesce analysis while in-flight uri={uri} latest_version={version}"
                            ));
                        }
                    }
                    None => break,
                }
            }
            done = done_rx.recv() => {
                let Some(uri) = done else {
                    break;
                };
                in_flight.remove(&uri);
                trace(format!("analysis job complete uri={uri}"));
                if let Some((_, _, _, _, deadline)) = pending.get_mut(&uri) {
                    *deadline = Instant::now();
                }
            }
            _ = async {
                if let Some(deadline) = next_deadline {
                    sleep_until(deadline).await;
                } else {
                    std::future::pending::<()>().await;
                }
            } => {
                let now = Instant::now();
                let expired: Vec<Url> = pending
                    .iter()
                    .filter(|(uri, (_, _, _, _, deadline))| *deadline <= now && !in_flight.contains(*uri))
                    .map(|(uri, _)| uri.clone())
                    .collect();

                for uri in expired {
                    let Some((version, text, project_root, is_primary, _)) = pending.remove(&uri) else {
                        continue;
                    };
                    let Some(current) = current_document(&shared, &uri) else {
                        continue;
                    };
                    if current.version != version {
                        trace(format!(
                            "skip stale analysis before start uri={uri} request_version={version} current_version={}",
                            current.version
                        ));
                        continue;
                    }
                    in_flight.insert(uri.clone());
                    let client = client.clone();
                    let shared = Arc::clone(&shared);
                    let analysis_shared = Arc::clone(&shared);
                    let tx = tx_for_dependents.clone();
                    let done = done_tx.clone();
                    let analysis_uri = uri.clone();
                    trace(format!(
                        "analysis job start uri={uri} version={version} primary={is_primary}"
                    ));
                    tokio::spawn(async move {
                        let job_start = StdInstant::now();
                        let join_result = tokio::task::spawn_blocking(move || {
                            analyze_document(
                                &analysis_shared,
                                Some(&analysis_uri),
                                version,
                                &text,
                                project_root,
                            )
                        })
                        .await;
                        let result = match join_result {
                            Ok(result) => result,
                            Err(error) => {
                                trace(format!(
                                    "analysis job failed uri={uri} version={version} error={error}"
                                ));
                                let _ = done.send(uri);
                                return;
                            }
                        };
                        trace(format!(
                            "analysis job finish uri={uri} version={} elapsed={}",
                            result.version,
                            duration_ms(job_start.elapsed())
                        ));

                        if let Some(applied) = apply_parse_result(&shared, &uri, result) {
                            trace(format!(
                                "publish diagnostics uri={uri} version={version} count={}",
                                applied.diagnostics.len()
                            ));
                            client
                                .publish_diagnostics(uri.clone(), applied.diagnostics, Some(version))
                                .await;
                            if is_primary {
                                for dependent_uri in applied.dependents {
                                    if dependent_uri == uri {
                                        continue;
                                    }
                                    let Some(dependent) = current_document(&shared, &dependent_uri) else {
                                        continue;
                                    };
                                    trace(format!(
                                        "enqueue dependent uri={dependent_uri} because={uri} version={}",
                                        dependent.version
                                    ));
                                    let _ = tx.send(CheckRequest {
                                        project_root: project_root_for_uri(&dependent_uri),
                                        uri: dependent_uri,
                                        version: dependent.version,
                                        text: dependent.text,
                                        is_primary: false,
                                    });
                                }
                            }
                        }
                        let _ = done.send(uri);
                    });
                }
            }
        }
    }
}

fn queue_check_request(
    pending: &mut HashMap<Url, (i32, String, Option<PathBuf>, bool, tokio::time::Instant)>,
    req: CheckRequest,
    debounce: tokio::time::Duration,
) {
    let CheckRequest {
        uri,
        version,
        text,
        project_root,
        is_primary,
    } = req;
    pending
        .entry(uri)
        .and_modify(|entry| {
            entry.0 = version;
            entry.1 = text.clone();
            entry.2 = project_root.clone();
            entry.3 |= is_primary;
            entry.4 = tokio::time::Instant::now() + debounce;
        })
        .or_insert_with(|| {
            (
                version,
                text,
                project_root,
                is_primary,
                tokio::time::Instant::now() + debounce,
            )
        });
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
mod tests {
    use super::*;

    fn uri() -> Url {
        Url::parse("file:///tmp/main.saga").unwrap()
    }

    fn valid_source() -> String {
        "module Main\n\nfun main : Unit -> Unit\nmain () = ()\n".to_string()
    }

    fn temp_project(name: &str) -> PathBuf {
        let unique = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("clock before epoch")
            .as_nanos();
        let root = std::env::temp_dir().join(format!(
            "saga-lsp-unit-{name}-{}-{unique}",
            std::process::id()
        ));
        std::fs::create_dir_all(root.join("src")).expect("create temp project src");
        std::fs::write(root.join("project.toml"), "").expect("write project.toml");
        root
    }

    fn interface_update(module_name: &str, interface_fingerprint: u64) -> ModuleInterfaceUpdate {
        ModuleInterfaceUpdate {
            module_name: module_name.to_string(),
            path: Some(PathBuf::from(format!("/tmp/{module_name}.saga"))),
            source_fingerprint: 1,
            interface_fingerprint,
            exports: typechecker::ModuleExports::default(),
            codegen_info: None,
            check_result: None,
            is_current: true,
        }
    }

    #[test]
    fn project_interface_apply_detects_current_interface_changes() {
        let mut store = ProjectSemanticStore::default();
        let root = Some(PathBuf::from("/tmp/project"));

        let first = store
            .apply_module_interface_updates(root.clone(), vec![interface_update("Helper", 10)]);
        assert!(first.saw_current);
        assert!(first.current_changed);

        let unchanged = store
            .apply_module_interface_updates(root.clone(), vec![interface_update("Helper", 10)]);
        assert!(unchanged.saw_current);
        assert!(!unchanged.current_changed);

        let changed =
            store.apply_module_interface_updates(root, vec![interface_update("Helper", 11)]);
        assert!(changed.saw_current);
        assert!(changed.current_changed);
    }

    #[test]
    fn parse_failure_preserves_previous_parse_snapshot() {
        let shared = SharedState::default();
        let uri = uri();

        store_document(&shared, uri.clone(), 1, valid_source());
        let applied = apply_parse_result(
            &shared,
            &uri,
            analyze_document(&shared, Some(&uri), 1, &valid_source(), None),
        )
        .expect("apply valid parse");
        assert!(applied.diagnostics.is_empty());

        store_document(
            &shared,
            uri.clone(),
            2,
            "module Main\n\nfun main : Unit -> Unit\nmain () = ".to_string(),
        );
        let applied = apply_parse_result(
            &shared,
            &uri,
            analyze_document(
                &shared,
                Some(&uri),
                2,
                "module Main\n\nfun main : Unit -> Unit\nmain () = ",
                None,
            ),
        )
        .expect("apply invalid parse");
        assert!(!applied.diagnostics.is_empty());

        let document = current_document(&shared, &uri).expect("document");
        let parse = document.parse.expect("previous parse is preserved");
        assert_eq!(parse.version, 1);
        assert_eq!(document.diagnostics.len(), 1);
    }

    #[test]
    fn stale_parse_result_is_discarded() {
        let shared = SharedState::default();
        let uri = uri();

        store_document(&shared, uri.clone(), 2, valid_source());
        let result = apply_parse_result(
            &shared,
            &uri,
            analyze_document(&shared, Some(&uri), 1, &valid_source(), None),
        );

        assert!(result.is_none());
        let document = current_document(&shared, &uri).expect("document");
        assert!(document.parse.is_none());
        assert!(document.diagnostics.is_empty());
    }

    #[test]
    fn utf16_position_to_offset_handles_multibyte_text() {
        let source = "module Main\n\nlet smile = \"🙂\"\n";
        let index = LineIndex::new(source);
        let offset = index.position_to_offset(Position::new(2, 12), source);

        assert_eq!(&source[offset..offset + 1], "\"");
    }

    #[test]
    fn completion_uses_preserved_parse_snapshot_on_broken_text() {
        let shared = SharedState::default();
        let uri = uri();

        store_document(&shared, uri.clone(), 1, valid_source());
        apply_parse_result(
            &shared,
            &uri,
            analyze_document(&shared, Some(&uri), 1, &valid_source(), None),
        )
        .expect("apply valid parse");
        store_document(&shared, uri.clone(), 2, "module Main\n\nm".to_string());

        let document = current_document(&shared, &uri).expect("document");
        let labels: Vec<_> = collect_completion_items(&document, Position::new(2, 1))
            .into_iter()
            .map(|item| item.label)
            .collect();

        assert!(labels.iter().any(|label| label == "main"));
        assert!(labels.iter().any(|label| label == "module"));
    }

    #[test]
    fn hover_reads_exact_version_semantic_snapshot() {
        let source = "\
module Main

fun id : Unit -> Unit
id x = x

fun main : Unit -> Unit
main () = id ()
";
        let uri = uri();
        let shared = SharedState::default();
        let result = analyze_document(&shared, Some(&uri), 1, source, None);
        let semantic = result.semantic.expect("semantic snapshot");
        let hover = hover_type_at(&semantic, Position::new(6, 10)).expect("hover");
        let HoverContents::Markup(markup) = hover.contents else {
            panic!("expected markup hover");
        };

        assert!(
            markup.value.contains("id: Unit -> Unit"),
            "{}",
            markup.value
        );
    }

    #[test]
    fn local_definition_uses_semantic_references() {
        let uri = uri();
        let source = "\
module Main

fun id : Unit -> Unit
id x = x

fun main : Unit -> Unit
main () = id ()
";
        let shared = SharedState::default();
        let result = analyze_document(&shared, Some(&uri), 1, source, None);
        let semantic = result.semantic.expect("semantic snapshot");
        let location =
            local_definition_at(&uri, &semantic, Position::new(6, 10)).expect("definition");

        assert_eq!(location.uri, uri);
        assert!(
            location.range.start.line == 2 || location.range.start.line == 3,
            "unexpected definition line: {:?}",
            location.range
        );
    }

    #[test]
    fn project_base_checker_warms_dependency_exports() {
        let root = temp_project("dependency-warmup");
        let dep_root = root.join("deps/kraken");
        let dep_src = dep_root.join("src");
        std::fs::create_dir_all(&dep_src).expect("create dependency src");
        std::fs::write(
            root.join("project.toml"),
            "\
[project]
name = \"app\"

[deps]
kraken = { path = \"deps/kraken\" }
",
        )
        .expect("write app project.toml");
        std::fs::write(
            dep_root.join("project.toml"),
            "\
[project]
name = \"kraken\"

[library]
module = \"Kraken\"
expose = [\"Kraken.Core\"]
",
        )
        .expect("write dependency project.toml");
        std::fs::write(
            dep_src.join("Core.saga"),
            "\
module Kraken.Core

pub fun answer : Unit -> Int
answer () = 42
",
        )
        .expect("write dependency module");

        let checker = checker_base_for_project(Some(root.clone())).expect("base checker");
        let result = checker.to_result();
        let _ = std::fs::remove_dir_all(&root);

        assert!(
            result.module_exports().contains_key("Kraken.Core"),
            "dependency exports were not warmed"
        );
    }

    #[test]
    fn interface_updates_cache_builtin_modules_without_paths() {
        let mut checker = typechecker::Checker::with_prelude(None).expect("checker");
        checker
            .try_typecheck_import_by_name("Std.DateTime")
            .expect("typecheck builtin module");
        let result = checker.to_lsp_result();

        let updates = collect_module_interface_updates(
            None,
            &Vec::new(),
            &checker,
            &result,
            &HashMap::new(),
            &HashMap::new(),
            false,
        );
        let date_time = updates
            .iter()
            .find(|update| update.module_name == "Std.DateTime")
            .expect("Std.DateTime interface update");

        assert!(date_time.path.is_none());
        assert!(date_time.source_fingerprint != 0);
    }
}
