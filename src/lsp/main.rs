use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
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

#[derive(Clone, Default)]
struct SemanticIndex {
    definition_locations: HashMap<ast::NodeId, Location>,
    references: HashMap<ast::NodeId, ast::NodeId>,
    references_by_definition: HashMap<ast::NodeId, Vec<SemanticOccurrence>>,
    type_definition_locations: HashMap<String, Location>,
    type_occurrences_by_name: HashMap<String, Vec<SemanticOccurrence>>,
    type_occurrences: Vec<NamedLocation>,
    symbol_definition_locations: HashMap<SemanticSymbolKey, Location>,
    symbol_occurrences_by_key: HashMap<SemanticSymbolKey, Vec<SemanticOccurrence>>,
    symbol_occurrences: Vec<SemanticSymbolLocation>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum SemanticSymbolKind {
    Trait,
    TraitMethod,
    Effect,
    EffectOperation,
    Handler,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct SemanticSymbolKey {
    kind: SemanticSymbolKind,
    name: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum OccurrenceKind {
    Definition,
    Reference,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct SemanticOccurrence {
    kind: OccurrenceKind,
    location: Location,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct NamedLocation {
    name: String,
    location: Location,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct SemanticSymbolLocation {
    key: SemanticSymbolKey,
    location: Location,
}

impl SemanticIndex {
    fn new(definition_locations: HashMap<ast::NodeId, Location>) -> Self {
        Self {
            definition_locations,
            references: HashMap::new(),
            references_by_definition: HashMap::new(),
            type_definition_locations: HashMap::new(),
            type_occurrences_by_name: HashMap::new(),
            type_occurrences: Vec::new(),
            symbol_definition_locations: HashMap::new(),
            symbol_occurrences_by_key: HashMap::new(),
            symbol_occurrences: Vec::new(),
        }
    }

    fn add_references(
        &mut self,
        references: &HashMap<ast::NodeId, ast::NodeId>,
        definition_nodes: &std::collections::HashSet<ast::NodeId>,
    ) {
        for (&usage_id, &definition_id) in references {
            self.references.insert(usage_id, definition_id);
            if let Some(location) = self.definition_locations.get(&usage_id) {
                let kind = if definition_nodes.contains(&usage_id) {
                    OccurrenceKind::Definition
                } else {
                    OccurrenceKind::Reference
                };
                self.references_by_definition
                    .entry(definition_id)
                    .or_default()
                    .push(SemanticOccurrence {
                        kind,
                        location: location.clone(),
                    });
            }
        }
    }

    fn add_type_definition(&mut self, name: String, location: Location) {
        self.type_definition_locations
            .entry(name.clone())
            .or_insert_with(|| location.clone());
        self.type_occurrences_by_name
            .entry(name.clone())
            .or_default()
            .push(SemanticOccurrence {
                kind: OccurrenceKind::Definition,
                location: location.clone(),
            });
        self.type_occurrences.push(NamedLocation { name, location });
    }

    fn add_type_reference(&mut self, name: String, location: Location) {
        self.type_occurrences_by_name
            .entry(name.clone())
            .or_default()
            .push(SemanticOccurrence {
                kind: OccurrenceKind::Reference,
                location: location.clone(),
            });
        self.type_occurrences.push(NamedLocation { name, location });
    }

    fn add_symbol_definition(
        &mut self,
        kind: SemanticSymbolKind,
        name: String,
        location: Location,
    ) {
        let key = SemanticSymbolKey { kind, name };
        self.symbol_definition_locations
            .entry(key.clone())
            .or_insert_with(|| location.clone());
        self.symbol_occurrences_by_key
            .entry(key.clone())
            .or_default()
            .push(SemanticOccurrence {
                kind: OccurrenceKind::Definition,
                location: location.clone(),
            });
        self.symbol_occurrences
            .push(SemanticSymbolLocation { key, location });
    }

    fn add_symbol_reference(&mut self, kind: SemanticSymbolKind, name: String, location: Location) {
        let key = SemanticSymbolKey { kind, name };
        self.symbol_occurrences_by_key
            .entry(key.clone())
            .or_default()
            .push(SemanticOccurrence {
                kind: OccurrenceKind::Reference,
                location: location.clone(),
            });
        self.symbol_occurrences
            .push(SemanticSymbolLocation { key, location });
    }

    fn type_name_at_position(&self, uri: &Url, position: Position) -> Option<&str> {
        self.type_occurrences
            .iter()
            .filter(|occurrence| {
                occurrence.location.uri == *uri
                    && range_contains_position(&occurrence.location.range, position)
            })
            .min_by_key(|occurrence| range_width(&occurrence.location.range))
            .map(|occurrence| occurrence.name.as_str())
    }

    fn type_definition_location_at(&self, uri: &Url, position: Position) -> Option<Location> {
        let name = self.type_name_at_position(uri, position)?;
        self.type_definition_locations.get(name).cloned()
    }

    fn type_reference_locations_at(
        &self,
        uri: &Url,
        position: Position,
        include_declaration: bool,
    ) -> Option<Vec<Location>> {
        let name = self.type_name_at_position(uri, position)?;
        Some(self.type_reference_locations_for_name(name, include_declaration))
    }

    fn type_reference_locations_for_name(
        &self,
        name: &str,
        include_declaration: bool,
    ) -> Vec<Location> {
        let mut locations: Vec<Location> = self
            .type_occurrences_by_name
            .get(name)
            .into_iter()
            .flat_map(|occurrences| occurrences.iter())
            .filter(|occurrence| {
                include_declaration || occurrence.kind == OccurrenceKind::Reference
            })
            .map(|occurrence| occurrence.location.clone())
            .collect();
        sort_and_dedup_locations(&mut locations);
        locations
    }

    fn symbol_key_at_position(&self, uri: &Url, position: Position) -> Option<&SemanticSymbolKey> {
        self.symbol_location_at_position(uri, position)
            .map(|occurrence| &occurrence.key)
    }

    fn symbol_location_at_position(
        &self,
        uri: &Url,
        position: Position,
    ) -> Option<&SemanticSymbolLocation> {
        self.symbol_occurrences
            .iter()
            .filter(|occurrence| {
                occurrence.location.uri == *uri
                    && range_contains_position(&occurrence.location.range, position)
            })
            .min_by_key(|occurrence| range_width(&occurrence.location.range))
    }

    fn symbol_definition_location_at(&self, uri: &Url, position: Position) -> Option<Location> {
        let key = self.symbol_key_at_position(uri, position)?;
        self.symbol_definition_locations.get(key).cloned()
    }

    fn symbol_reference_locations_at(
        &self,
        uri: &Url,
        position: Position,
        include_declaration: bool,
    ) -> Option<Vec<Location>> {
        let key = self.symbol_key_at_position(uri, position)?;
        Some(self.symbol_reference_locations_for_key(key, include_declaration))
    }

    fn symbol_reference_locations_for_key(
        &self,
        key: &SemanticSymbolKey,
        include_declaration: bool,
    ) -> Vec<Location> {
        let mut locations: Vec<Location> = self
            .symbol_occurrences_by_key
            .get(key)
            .into_iter()
            .flat_map(|occurrences| occurrences.iter())
            .filter(|occurrence| {
                include_declaration || occurrence.kind == OccurrenceKind::Reference
            })
            .map(|occurrence| occurrence.location.clone())
            .collect();
        sort_and_dedup_locations(&mut locations);
        locations
    }

    fn identity_for_node(&self, node_id: ast::NodeId) -> ast::NodeId {
        self.references.get(&node_id).copied().unwrap_or(node_id)
    }

    fn definition_location_for_node(&self, node_id: ast::NodeId) -> Option<Location> {
        let definition_id = self.identity_for_node(node_id);
        self.definition_locations.get(&definition_id).cloned()
    }

    fn reference_locations_for_node(
        &self,
        node_id: ast::NodeId,
        include_declaration: bool,
    ) -> Vec<Location> {
        let definition_id = self.identity_for_node(node_id);
        let mut locations: Vec<Location> = self
            .references_by_definition
            .get(&definition_id)
            .into_iter()
            .flat_map(|occurrences| occurrences.iter())
            .filter(|occurrence| {
                include_declaration || occurrence.kind == OccurrenceKind::Reference
            })
            .map(|occurrence| occurrence.location.clone())
            .collect();

        if include_declaration && let Some(location) = self.definition_locations.get(&definition_id)
        {
            locations.push(location.clone());
        }

        sort_and_dedup_locations(&mut locations);
        locations
    }
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
    semantic_indexes: HashMap<String, CachedSemanticIndex>,
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

struct CachedSemanticIndex {
    uri: Url,
    index: SemanticIndex,
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

struct ProjectSemanticIndexUpdate {
    module_name: String,
    uri: Url,
    index: SemanticIndex,
}

impl ProjectSemanticState {
    fn new() -> Self {
        Self {
            generation: 0,
            dep_graph: DependencyGraph::default(),
            base_checker: None,
            module_interfaces: HashMap::new(),
            semantic_indexes: HashMap::new(),
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
            project
                .semantic_indexes
                .retain(|_, cached| cached.uri != *uri);
            project.generation = project.generation.saturating_add(1);
        }
    }

    fn update_semantic_index(
        &mut self,
        project_root: Option<PathBuf>,
        update: ProjectSemanticIndexUpdate,
    ) {
        let project = self.project_mut(project_root);
        project
            .semantic_indexes
            .retain(|_, cached| cached.uri != update.uri);
        project.semantic_indexes.insert(
            update.module_name,
            CachedSemanticIndex {
                uri: update.uri,
                index: update.index,
            },
        );
    }

    fn project_type_reference_locations(
        &self,
        project_root: &Option<PathBuf>,
        type_name: &str,
        include_declaration: bool,
    ) -> Vec<Location> {
        let Some(project) = self.projects.get(project_root) else {
            return Vec::new();
        };
        let mut locations = Vec::new();
        for cached in project.semantic_indexes.values() {
            locations.extend(
                cached
                    .index
                    .type_reference_locations_for_name(type_name, include_declaration),
            );
        }
        sort_and_dedup_locations(&mut locations);
        locations
    }

    fn project_symbol_reference_locations(
        &self,
        project_root: &Option<PathBuf>,
        key: &SemanticSymbolKey,
        include_declaration: bool,
    ) -> Vec<Location> {
        let Some(project) = self.projects.get(project_root) else {
            return Vec::new();
        };
        let mut locations = Vec::new();
        for cached in project.semantic_indexes.values() {
            locations.extend(
                cached
                    .index
                    .symbol_reference_locations_for_key(key, include_declaration),
            );
        }
        sort_and_dedup_locations(&mut locations);
        locations
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
    hash_module_exports(exports, &mut hasher);
    hasher.finish()
}

fn hash_module_exports(exports: &typechecker::ModuleExports, state: &mut impl Hasher) {
    "ModuleExports".hash(state);
    hash_sorted_pairs(&exports.bindings, state, hash_scheme);
    hash_string_map(&exports.binding_origins, state);
    hash_string_vec_map(&exports.type_constructors, state);
    hash_sorted_map(&exports.inlinable_constructors, state, |ctors, state| {
        hash_sorted_pairs(ctors, state, hash_scheme);
    });
    hash_string_map(&exports.type_origins, state);
    hash_sorted_map(&exports.record_defs, state, hash_record_info);
    hash_sorted_map(&exports.traits, state, hash_trait_info);
    hash_string_map(&exports.trait_origins, state);
    hash_sorted_map(&exports.trait_impls, state, hash_impl_info);
    hash_sorted_map(&exports.effects, state, hash_effect_def_info);
    hash_string_map(&exports.effect_origins, state);
    hash_sorted_map(&exports.handlers, state, hash_handler_info);
    hash_string_map(&exports.handler_origins, state);
    hash_sorted_map(&exports.type_arity, state, |arity, state| arity.hash(state));
    hash_sorted_map(&exports.type_param_kinds, state, |kinds, state| {
        hash_vec(kinds, state, |kind, state| kind.hash(state));
    });
    hash_sorted_map(&exports.type_aliases, state, hash_type_alias_info);
    let effectful: BTreeSet<_> = exports.effectful_funs.iter().collect();
    hash_vec(
        &effectful.into_iter().collect::<Vec<_>>(),
        state,
        |name, state| {
            name.hash(state);
        },
    );
}

fn hash_sorted_pairs<T, H: Hasher>(
    values: &[(String, T)],
    state: &mut H,
    hash_value: impl Fn(&T, &mut H),
) {
    let sorted: BTreeMap<_, _> = values.iter().map(|(key, value)| (key, value)).collect();
    hash_vec(
        &sorted.into_iter().collect::<Vec<_>>(),
        state,
        |(key, value), state| {
            key.hash(state);
            hash_value(value, state);
        },
    );
}

fn hash_string_map<H: Hasher>(values: &HashMap<String, String>, state: &mut H) {
    hash_sorted_map(values, state, |value, state| value.hash(state));
}

fn hash_string_vec_map<H: Hasher>(values: &HashMap<String, Vec<String>>, state: &mut H) {
    hash_sorted_map(values, state, |value, state| value.hash(state));
}

fn hash_sorted_map<K, V, H: Hasher>(
    values: &HashMap<K, V>,
    state: &mut H,
    hash_value: impl Fn(&V, &mut H),
) where
    K: Ord + Hash,
{
    let sorted: BTreeMap<_, _> = values.iter().collect();
    hash_vec(
        &sorted.into_iter().collect::<Vec<_>>(),
        state,
        |(key, value), state| {
            key.hash(state);
            hash_value(value, state);
        },
    );
}

fn hash_vec<T, H: Hasher>(values: &[T], state: &mut H, hash_value: impl Fn(&T, &mut H)) {
    values.len().hash(state);
    for value in values {
        hash_value(value, state);
    }
}

fn hash_scheme<H: Hasher>(scheme: &typechecker::Scheme, state: &mut H) {
    scheme.forall.hash(state);
    hash_vec(
        &scheme.constraints,
        state,
        |(trait_name, var_id, extra_args), state| {
            trait_name.hash(state);
            var_id.hash(state);
            hash_vec(extra_args, state, hash_type);
        },
    );
    hash_type(&scheme.ty, state);
}

fn hash_type<H: Hasher>(ty: &typechecker::Type, state: &mut H) {
    match ty {
        typechecker::Type::Var(id) => {
            "Var".hash(state);
            id.hash(state);
        }
        typechecker::Type::Fun(param, ret, effects) => {
            "Fun".hash(state);
            hash_type(param, state);
            hash_type(ret, state);
            hash_effect_row(effects, state);
        }
        typechecker::Type::Con(name, args) => {
            "Con".hash(state);
            name.hash(state);
            hash_vec(args, state, hash_type);
        }
        typechecker::Type::Record(fields) => {
            "Record".hash(state);
            hash_vec(fields, state, |(name, ty), state| {
                name.hash(state);
                hash_type(ty, state);
            });
        }
        typechecker::Type::Symbol(value) => {
            "Symbol".hash(state);
            value.hash(state);
        }
        typechecker::Type::Error => {
            "Error".hash(state);
        }
    }
}

fn hash_effect_row<H: Hasher>(row: &typechecker::EffectRow, state: &mut H) {
    let mut effects = row.effects.clone();
    effects.sort_by(|a, b| {
        a.name
            .cmp(&b.name)
            .then_with(|| format!("{:?}", a.args).cmp(&format!("{:?}", b.args)))
    });
    hash_vec(&effects, state, |entry, state| {
        entry.name.hash(state);
        hash_vec(&entry.args, state, hash_type);
    });
    hash_vec(&row.tails, state, hash_type);
}

fn hash_record_info<H: Hasher>(info: &typechecker::RecordInfo, state: &mut H) {
    info.type_params.hash(state);
    hash_vec(&info.fields, state, |(name, ty), state| {
        name.hash(state);
        hash_type(ty, state);
    });
}

fn hash_trait_info<H: Hasher>(info: &typechecker::TraitInfo, state: &mut H) {
    hash_vec(&info.type_params, state, |(name, kind), state| {
        name.hash(state);
        kind.hash(state);
    });
    info.supertraits.hash(state);
    hash_vec(&info.methods, state, hash_trait_method_info);
    info.is_functional.hash(state);
    match &info.fundep {
        Some(fundep) => {
            true.hash(state);
            fundep.determinant.hash(state);
            fundep.determined.hash(state);
        }
        None => false.hash(state),
    }
}

fn hash_trait_method_info<H: Hasher>(info: &typechecker::TraitMethodInfo, state: &mut H) {
    info.name.hash(state);
    hash_vec(&info.param_types, state, hash_type);
    hash_type(&info.return_type, state);
    info.trait_param_id.hash(state);
    hash_scheme(&info.scheme, state);
    info.effect_sig.effects.hash(state);
    info.effect_sig.is_open_row.hash(state);
    info.effect_sig.user_arity.hash(state);
}

fn hash_impl_info<H: Hasher>(info: &typechecker::ImplInfo, state: &mut H) {
    info.param_constraints.hash(state);
    info.param_constraints_by_var.hash(state);
    hash_vec(
        &info.param_constraints_by_var_with_args,
        state,
        |(trait_name, var_id, extra_args), state| {
            trait_name.hash(state);
            var_id.hash(state);
            hash_vec(extra_args, state, hash_type);
        },
    );
    match &info.target_pattern {
        Some(ty) => {
            true.hash(state);
            hash_type(ty, state);
        }
        None => false.hash(state),
    }
    hash_vec(&info.trait_type_args, state, hash_type);
    info.target_type_param_ids.hash(state);
    hash_string_vec_map(&info.method_effects, state);
    hash_vec(&info.where_app_dict_params, state, |param, state| {
        param.trait_name.hash(state);
        hash_vec(&param.trait_type_args, state, hash_type);
        hash_type(&param.self_type, state);
    });
}

fn hash_effect_def_info<H: Hasher>(info: &typechecker::EffectDefInfo, state: &mut H) {
    info.type_params.hash(state);
    hash_vec(&info.ops, state, |op, state| {
        op.name.hash(state);
        op.effect_name.hash(state);
        hash_vec(&op.params, state, |(label, ty), state| {
            label.hash(state);
            hash_type(ty, state);
        });
        hash_type(&op.return_type, state);
        hash_effect_row(&op.needs, state);
        hash_vec(
            &op.constraints,
            state,
            |(trait_name, var_id, extra_args), state| {
                trait_name.hash(state);
                var_id.hash(state);
                hash_vec(extra_args, state, hash_type);
            },
        );
    });
    info.source_module.hash(state);
}

fn hash_handler_info<H: Hasher>(info: &typechecker::HandlerInfo, state: &mut H) {
    info.effects.hash(state);
    match &info.return_type {
        Some((param, body)) => {
            true.hash(state);
            hash_type(param, state);
            hash_type(body, state);
        }
        None => false.hash(state),
    }
    hash_effect_row(&info.needs_effects, state);
    info.forall.hash(state);
    let where_constraints: BTreeMap<_, _> = info.where_constraints.iter().collect();
    hash_vec(
        &where_constraints.into_iter().collect::<Vec<_>>(),
        state,
        |((effect_name, param_index), constraints), state| {
            effect_name.hash(state);
            param_index.hash(state);
            hash_vec(constraints, state, |(trait_name, vars), state| {
                trait_name.hash(state);
                vars.hash(state);
            });
        },
    );
    info.source_module.hash(state);
}

fn hash_type_alias_info<H: Hasher>(info: &typechecker::TypeAliasInfo, state: &mut H) {
    info.param_vars.hash(state);
    info.param_kinds.hash(state);
    hash_type(&info.body, state);
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
                semantic_index_update: None,
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
                        semantic_index_update: None,
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
                    semantic_index_update: None,
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
            let semantic_index = timed(&mut timings.definitions, || {
                let projects = shared.projects.lock().unwrap_or_else(|e| e.into_inner());
                build_semantic_index(
                    uri,
                    &line_index,
                    text,
                    &semantic_program,
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

            let semantic_index_update = uri.and_then(|uri| {
                let (module_name, _) = extract_module_info(&semantic_program);
                module_name.map(|module_name| ProjectSemanticIndexUpdate {
                    module_name,
                    uri: uri.clone(),
                    index: semantic_index.clone(),
                })
            });

            ParseJobResult {
                version,
                parse: Some(parse),
                semantic: Some(SemanticSnapshot {
                    version,
                    source,
                    line_index,
                    check,
                    semantic_index,
                }),
                diagnostics,
                module_interfaces,
                semantic_index_update,
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
                semantic_index_update: None,
                force_dependents: true,
            }
        }
    }
}

fn analyze_syntax_document(uri: Option<&Url>, version: i32, text: &str) -> ParseJobResult {
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
                None,
                "syntax-lex-error",
                &timings,
                diagnostics.len(),
            );
            return ParseJobResult {
                version,
                parse: None,
                semantic: None,
                diagnostics,
                module_interfaces: Vec::new(),
                semantic_index_update: None,
                force_dependents: false,
            };
        }
    };

    let mut parser = parser::Parser::new(tokens);
    match timed(&mut timings.parse, || parser.parse_program()) {
        Ok(program) => {
            let source: Arc<str> = Arc::from(text);
            let parse = ParseSnapshot {
                version,
                source,
                line_index,
                program,
            };
            timings.total = total_start.elapsed();
            trace_analysis(uri, version, None, "syntax-ok", &timings, 0);
            ParseJobResult {
                version,
                parse: Some(parse),
                semantic: None,
                diagnostics: Vec::new(),
                module_interfaces: Vec::new(),
                semantic_index_update: None,
                force_dependents: false,
            }
        }
        Err(e) => {
            let diagnostics = vec![diagnostic_at(&line_index, text, e.span.start, e.message)];
            timings.total = total_start.elapsed();
            trace_analysis(
                uri,
                version,
                None,
                "syntax-parse-error",
                &timings,
                diagnostics.len(),
            );
            ParseJobResult {
                version,
                parse: None,
                semantic: None,
                diagnostics,
                module_interfaces: Vec::new(),
                semantic_index_update: None,
                force_dependents: false,
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

fn build_semantic_index(
    current_uri: Option<&Url>,
    current_line_index: &LineIndex,
    current_source: &str,
    current_program: &[ast::Decl],
    check: &typechecker::CheckResult,
    source_overlay: &HashMap<PathBuf, String>,
    cached: CachedDefinitionSources<'_>,
) -> SemanticIndex {
    let definition_locations = build_definition_locations(
        current_uri,
        current_line_index,
        current_source,
        check,
        source_overlay,
        cached,
    );
    let mut index = SemanticIndex::new(definition_locations);
    let definition_nodes = collect_value_definition_nodes(current_program);
    let references = semantic_value_references_for_program(check, current_program);
    index.add_references(&references, &definition_nodes);
    if let Some(uri) = current_uri {
        let (module_name, _) = extract_module_info(current_program);
        add_program_type_symbols(
            &mut index,
            uri,
            current_line_index,
            current_source,
            current_program,
            check,
            module_name.as_deref(),
        );
    }

    for (module_name, module_result) in check.module_check_results() {
        let mut module_definition_nodes = HashSet::new();
        let program = check
            .programs()
            .get(module_name)
            .or_else(|| module_result.programs().get(module_name));
        let references = if let Some(program) = program {
            collect_value_definition_nodes_into(program, &mut module_definition_nodes);
            semantic_value_references_for_program(module_result, program)
        } else {
            module_result.references.clone()
        };
        index.add_references(&references, &module_definition_nodes);
        if let Some(program) = program
            && let Some(path) = check.resolve_module_path(module_name)
            && let Ok(uri) = Url::from_file_path(&path)
            && let Some(source) = source_for_path(&path, source_overlay)
        {
            let line_index = LineIndex::new(&source);
            add_program_type_symbols(
                &mut index,
                &uri,
                &line_index,
                &source,
                program,
                module_result,
                Some(module_name),
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
            let mut module_definition_nodes = HashSet::new();
            let program = module_result.programs().get(module_name);
            let references = if let Some(program) = program {
                collect_value_definition_nodes_into(program, &mut module_definition_nodes);
                semantic_value_references_for_program(module_result, program)
            } else {
                module_result.references.clone()
            };
            index.add_references(&references, &module_definition_nodes);
            if let Some(program) = program
                && let Some(path) = entry.path.as_ref()
                && let Ok(uri) = Url::from_file_path(path)
                && let Some(source) = source_for_path(path, source_overlay)
            {
                let line_index = LineIndex::new(&source);
                add_program_type_symbols(
                    &mut index,
                    &uri,
                    &line_index,
                    &source,
                    program,
                    module_result,
                    Some(module_name),
                );
            }
        }
    }

    index
}

fn source_for_path(path: &Path, source_overlay: &HashMap<PathBuf, String>) -> Option<String> {
    source_overlay
        .get(path)
        .cloned()
        .or_else(|| std::fs::read_to_string(path).ok())
}

fn add_program_type_symbols(
    index: &mut SemanticIndex,
    uri: &Url,
    line_index: &LineIndex,
    source: &str,
    program: &[ast::Decl],
    check: &typechecker::CheckResult,
    module_name: Option<&str>,
) {
    for decl in program {
        add_decl_type_symbols(index, uri, line_index, source, decl, check, module_name);
    }
}

fn type_definition_name(module_name: Option<&str>, name: &str) -> String {
    module_name
        .map(|module| format!("{module}.{name}"))
        .unwrap_or_else(|| name.to_string())
}

fn name_range(start: usize, name: &str, line_index: &LineIndex, source: &str) -> Range {
    span_to_range(
        &saga::token::Span {
            start,
            end: start + name.len(),
        },
        line_index,
        source,
    )
}

fn final_segment_name_range(
    span: saga::token::Span,
    name: &str,
    line_index: &LineIndex,
    source: &str,
) -> Range {
    let haystack = source.get(span.start..span.end).unwrap_or_default();
    if let Some(relative_start) = haystack.rfind(name) {
        name_range(span.start + relative_start, name, line_index, source)
    } else {
        name_range(span.start, name, line_index, source)
    }
}

fn add_type_definition_symbol(
    index: &mut SemanticIndex,
    uri: &Url,
    line_index: &LineIndex,
    source: &str,
    module_name: Option<&str>,
    name: &str,
    name_span: saga::token::Span,
) {
    index.add_type_definition(
        type_definition_name(module_name, name),
        Location {
            uri: uri.clone(),
            range: span_to_range(&name_span, line_index, source),
        },
    );
}

fn add_type_reference_symbol(index: &mut SemanticIndex, uri: &Url, name: String, range: Range) {
    index.add_type_reference(
        name,
        Location {
            uri: uri.clone(),
            range,
        },
    );
}

fn add_semantic_symbol_definition(
    index: &mut SemanticIndex,
    uri: &Url,
    line_index: &LineIndex,
    source: &str,
    kind: SemanticSymbolKind,
    name: String,
    name_span: saga::token::Span,
) {
    index.add_symbol_definition(
        kind,
        name,
        Location {
            uri: uri.clone(),
            range: span_to_range(&name_span, line_index, source),
        },
    );
}

fn add_semantic_symbol_reference(
    index: &mut SemanticIndex,
    uri: &Url,
    kind: SemanticSymbolKind,
    name: String,
    range: Range,
) {
    index.add_symbol_reference(
        kind,
        name,
        Location {
            uri: uri.clone(),
            range,
        },
    );
}

fn member_symbol_name(owner: &str, member: &str) -> String {
    format!("{owner}.{member}")
}

fn add_trait_method_definition_symbol(
    index: &mut SemanticIndex,
    uri: &Url,
    line_index: &LineIndex,
    source: &str,
    trait_name: &str,
    method: &ast::TraitMethod,
) {
    index.add_symbol_definition(
        SemanticSymbolKind::TraitMethod,
        member_symbol_name(trait_name, &method.name),
        Location {
            uri: uri.clone(),
            range: final_segment_name_range(method.span, &method.name, line_index, source),
        },
    );
}

fn add_effect_operation_definition_symbol(
    index: &mut SemanticIndex,
    uri: &Url,
    line_index: &LineIndex,
    source: &str,
    effect_name: &str,
    op: &ast::EffectOp,
) {
    index.add_symbol_definition(
        SemanticSymbolKind::EffectOperation,
        member_symbol_name(effect_name, &op.name),
        Location {
            uri: uri.clone(),
            range: final_segment_name_range(op.span, &op.name, line_index, source),
        },
    );
}

fn add_trait_method_reference_symbol(
    index: &mut SemanticIndex,
    uri: &Url,
    trait_name: &str,
    method_name: &str,
    range: Range,
) {
    add_semantic_symbol_reference(
        index,
        uri,
        SemanticSymbolKind::TraitMethod,
        member_symbol_name(trait_name, method_name),
        range,
    );
}

fn add_effect_operation_reference_symbol(
    index: &mut SemanticIndex,
    uri: &Url,
    effect_name: &str,
    op_name: &str,
    range: Range,
) {
    add_semantic_symbol_reference(
        index,
        uri,
        SemanticSymbolKind::EffectOperation,
        member_symbol_name(effect_name, op_name),
        range,
    );
}

fn add_trait_ref_symbol(
    index: &mut SemanticIndex,
    uri: &Url,
    line_index: &LineIndex,
    source: &str,
    trait_ref: &ast::TraitRef,
    check: &typechecker::CheckResult,
) {
    if let Some(resolved) = check.resolved_trait_name_for_node(trait_ref.id) {
        add_semantic_symbol_reference(
            index,
            uri,
            SemanticSymbolKind::Trait,
            resolved.to_string(),
            name_range(trait_ref.span.start, &trait_ref.name, line_index, source),
        );
    }
    for type_expr in &trait_ref.type_args {
        add_type_expr_symbols(index, uri, line_index, source, type_expr, check);
    }
}

fn add_trait_app_symbol(
    index: &mut SemanticIndex,
    uri: &Url,
    line_index: &LineIndex,
    source: &str,
    app: &ast::TraitApp,
    check: &typechecker::CheckResult,
) {
    if let Some(resolved) = check.resolved_trait_name_for_node(app.id) {
        add_semantic_symbol_reference(
            index,
            uri,
            SemanticSymbolKind::Trait,
            resolved.to_string(),
            name_range(app.span.start, &app.trait_name, line_index, source),
        );
    }
    for type_expr in &app.type_args {
        add_type_expr_symbols(index, uri, line_index, source, type_expr, check);
    }
}

fn add_effect_ref_symbol(
    index: &mut SemanticIndex,
    uri: &Url,
    line_index: &LineIndex,
    source: &str,
    effect_ref: &ast::EffectRef,
    check: &typechecker::CheckResult,
) {
    if let Some(resolved) = check.resolved_effect_name_for_node(effect_ref.id) {
        add_semantic_symbol_reference(
            index,
            uri,
            SemanticSymbolKind::Effect,
            resolved.to_string(),
            name_range(effect_ref.span.start, &effect_ref.name, line_index, source),
        );
    }
    for type_expr in &effect_ref.type_args {
        add_type_expr_symbols(index, uri, line_index, source, type_expr, check);
    }
}

fn add_handler_ref_symbol(
    index: &mut SemanticIndex,
    uri: &Url,
    line_index: &LineIndex,
    source: &str,
    handler_ref: &ast::NamedHandlerRef,
    check: &typechecker::CheckResult,
) {
    if let Some(resolved) = check.resolved_handler_name_for_node(handler_ref.id) {
        add_semantic_symbol_reference(
            index,
            uri,
            SemanticSymbolKind::Handler,
            resolved,
            name_range(
                handler_ref.span.start,
                &handler_ref.name,
                line_index,
                source,
            ),
        );
    }
}

fn add_decl_type_symbols(
    index: &mut SemanticIndex,
    uri: &Url,
    line_index: &LineIndex,
    source: &str,
    decl: &ast::Decl,
    check: &typechecker::CheckResult,
    module_name: Option<&str>,
) {
    match decl {
        ast::Decl::FunSignature {
            params,
            return_type,
            effects,
            where_clause,
            ..
        } => {
            for (_, type_expr) in params {
                add_type_expr_symbols(index, uri, line_index, source, type_expr, check);
            }
            add_type_expr_symbols(index, uri, line_index, source, return_type, check);
            for effect_ref in effects {
                add_effect_ref_symbol(index, uri, line_index, source, effect_ref, check);
            }
            add_where_clause_type_symbols(index, uri, line_index, source, where_clause, check);
        }
        ast::Decl::FunBinding {
            params,
            guard,
            body,
            ..
        } => {
            for param in params {
                add_pat_type_symbols(index, uri, line_index, source, param, check);
            }
            if let Some(guard) = guard {
                add_expr_type_symbols(index, uri, line_index, source, guard, check);
            }
            add_expr_type_symbols(index, uri, line_index, source, body, check);
        }
        ast::Decl::Let {
            annotation, value, ..
        } => {
            if let Some(annotation) = annotation {
                add_type_expr_symbols(index, uri, line_index, source, annotation, check);
            }
            add_expr_type_symbols(index, uri, line_index, source, value, check);
        }
        ast::Decl::TypeDef {
            name,
            name_span,
            variants,
            ..
        } => {
            add_type_definition_symbol(
                index,
                uri,
                line_index,
                source,
                module_name,
                name,
                *name_span,
            );
            for variant in variants {
                for (_, type_expr) in &variant.node.fields {
                    add_type_expr_symbols(index, uri, line_index, source, type_expr, check);
                }
            }
        }
        ast::Decl::TypeAlias {
            name,
            name_span,
            body,
            ..
        } => {
            add_type_definition_symbol(
                index,
                uri,
                line_index,
                source,
                module_name,
                name,
                *name_span,
            );
            add_type_expr_symbols(index, uri, line_index, source, body, check);
        }
        ast::Decl::RecordDef {
            name,
            name_span,
            fields,
            ..
        } => {
            add_type_definition_symbol(
                index,
                uri,
                line_index,
                source,
                module_name,
                name,
                *name_span,
            );
            for field in fields {
                add_type_expr_symbols(index, uri, line_index, source, &field.node.1, check);
            }
        }
        ast::Decl::EffectDef {
            name,
            name_span,
            operations,
            ..
        } => {
            let effect_name = type_definition_name(module_name, name);
            add_semantic_symbol_definition(
                index,
                uri,
                line_index,
                source,
                SemanticSymbolKind::Effect,
                effect_name.clone(),
                *name_span,
            );
            for op in operations {
                add_effect_operation_definition_symbol(
                    index,
                    uri,
                    line_index,
                    source,
                    &effect_name,
                    &op.node,
                );
                for (_, type_expr) in &op.node.params {
                    add_type_expr_symbols(index, uri, line_index, source, type_expr, check);
                }
                add_type_expr_symbols(index, uri, line_index, source, &op.node.return_type, check);
                for effect_ref in &op.node.effects {
                    add_effect_ref_symbol(index, uri, line_index, source, effect_ref, check);
                }
                add_where_clause_type_symbols(
                    index,
                    uri,
                    line_index,
                    source,
                    &op.node.where_clause,
                    check,
                );
            }
        }
        ast::Decl::HandlerDef {
            name,
            name_span,
            body,
            ..
        } => {
            add_semantic_symbol_definition(
                index,
                uri,
                line_index,
                source,
                SemanticSymbolKind::Handler,
                type_definition_name(module_name, name),
                *name_span,
            );
            add_handler_body_type_symbols(index, uri, line_index, source, body, check);
        }
        ast::Decl::TraitDef {
            name,
            name_span,
            supertraits,
            methods,
            ..
        } => {
            let trait_name = type_definition_name(module_name, name);
            add_semantic_symbol_definition(
                index,
                uri,
                line_index,
                source,
                SemanticSymbolKind::Trait,
                trait_name.clone(),
                *name_span,
            );
            for trait_ref in supertraits {
                add_trait_ref_symbol(index, uri, line_index, source, trait_ref, check);
            }
            for method in methods {
                add_trait_method_definition_symbol(
                    index,
                    uri,
                    line_index,
                    source,
                    &trait_name,
                    &method.node,
                );
                for (_, type_expr) in &method.node.params {
                    add_type_expr_symbols(index, uri, line_index, source, type_expr, check);
                }
                add_type_expr_symbols(
                    index,
                    uri,
                    line_index,
                    source,
                    &method.node.return_type,
                    check,
                );
                for effect_ref in &method.node.effects {
                    add_effect_ref_symbol(index, uri, line_index, source, effect_ref, check);
                }
            }
        }
        ast::Decl::ImplDef {
            id,
            target_type,
            target_type_span,
            target_type_expr,
            trait_name,
            trait_name_span,
            trait_type_args,
            where_clause,
            where_apps,
            needs,
            methods,
            ..
        } => {
            let resolved_trait = check.resolved_trait_name_for_node(*id);
            if let Some(resolved) = resolved_trait {
                add_semantic_symbol_reference(
                    index,
                    uri,
                    SemanticSymbolKind::Trait,
                    resolved.to_string(),
                    span_to_range(trait_name_span, line_index, source),
                );
            } else {
                let _ = trait_name;
            }
            if let Some(name) = check.resolved_type_name_for_node(*id) {
                add_type_reference_symbol(
                    index,
                    uri,
                    name.to_string(),
                    span_to_range(target_type_span, line_index, source),
                );
            } else {
                let _ = target_type;
            }
            if let Some(target_type_expr) = target_type_expr {
                add_type_expr_symbols(index, uri, line_index, source, target_type_expr, check);
            }
            for type_expr in trait_type_args {
                add_type_expr_symbols(index, uri, line_index, source, type_expr, check);
            }
            add_where_clause_type_symbols(index, uri, line_index, source, where_clause, check);
            for app in where_apps {
                add_trait_app_symbol(index, uri, line_index, source, app, check);
            }
            for effect_ref in needs {
                add_effect_ref_symbol(index, uri, line_index, source, effect_ref, check);
            }
            for method in methods {
                if let Some(resolved_trait) = resolved_trait {
                    add_trait_method_reference_symbol(
                        index,
                        uri,
                        resolved_trait,
                        &method.node.name,
                        span_to_range(&method.node.name_span, line_index, source),
                    );
                }
                for param in &method.node.params {
                    add_pat_type_symbols(index, uri, line_index, source, param, check);
                }
                add_expr_type_symbols(index, uri, line_index, source, &method.node.body, check);
            }
        }
        ast::Decl::DictConstructor { methods, .. } => {
            for method in methods {
                add_expr_type_symbols(index, uri, line_index, source, method, check);
            }
        }
        ast::Decl::Import { .. } | ast::Decl::ModuleDecl { .. } => {}
    }
}

fn add_where_clause_type_symbols(
    index: &mut SemanticIndex,
    uri: &Url,
    line_index: &LineIndex,
    source: &str,
    where_clause: &[ast::TraitBound],
    check: &typechecker::CheckResult,
) {
    for bound in where_clause {
        for trait_ref in &bound.traits {
            add_trait_ref_symbol(index, uri, line_index, source, trait_ref, check);
        }
    }
}

fn add_type_expr_symbols(
    index: &mut SemanticIndex,
    uri: &Url,
    line_index: &LineIndex,
    source: &str,
    type_expr: &ast::TypeExpr,
    check: &typechecker::CheckResult,
) {
    match type_expr {
        ast::TypeExpr::Named { id, name, span } => {
            if let Some(resolved) = check.resolved_type_name_for_node(*id) {
                add_type_reference_symbol(
                    index,
                    uri,
                    resolved.to_string(),
                    span_to_range(span, line_index, source),
                );
            } else {
                let _ = name;
            }
        }
        ast::TypeExpr::App { func, arg, .. } => {
            add_type_expr_symbols(index, uri, line_index, source, func, check);
            add_type_expr_symbols(index, uri, line_index, source, arg, check);
        }
        ast::TypeExpr::Arrow {
            from, to, effects, ..
        } => {
            add_type_expr_symbols(index, uri, line_index, source, from, check);
            add_type_expr_symbols(index, uri, line_index, source, to, check);
            for effect in effects {
                add_effect_ref_symbol(index, uri, line_index, source, effect, check);
            }
        }
        ast::TypeExpr::Record { fields, .. } => {
            for (_, type_expr) in fields {
                add_type_expr_symbols(index, uri, line_index, source, type_expr, check);
            }
        }
        ast::TypeExpr::Labeled { inner, .. } => {
            add_type_expr_symbols(index, uri, line_index, source, inner, check);
        }
        ast::TypeExpr::Var { .. } | ast::TypeExpr::Symbol { .. } => {}
    }
}

fn add_pat_type_symbols(
    index: &mut SemanticIndex,
    uri: &Url,
    line_index: &LineIndex,
    source: &str,
    pat: &ast::Pat,
    check: &typechecker::CheckResult,
) {
    match pat {
        ast::Pat::Constructor { args, .. } | ast::Pat::Tuple { elements: args, .. } => {
            for arg in args {
                add_pat_type_symbols(index, uri, line_index, source, arg, check);
            }
        }
        ast::Pat::Record {
            id, name, fields, ..
        } => {
            if let Some(resolved) = check.resolved_type_name_for_node(*id) {
                add_type_reference_symbol(
                    index,
                    uri,
                    resolved.to_string(),
                    name_range(pat.span().start, name, line_index, source),
                );
            }
            for (_, field_pat) in fields {
                if let Some(field_pat) = field_pat {
                    add_pat_type_symbols(index, uri, line_index, source, field_pat, check);
                }
            }
        }
        ast::Pat::AnonRecord { fields, .. } => {
            for (_, field_pat) in fields {
                if let Some(field_pat) = field_pat {
                    add_pat_type_symbols(index, uri, line_index, source, field_pat, check);
                }
            }
        }
        ast::Pat::StringPrefix { rest, .. } => {
            add_pat_type_symbols(index, uri, line_index, source, rest, check);
        }
        ast::Pat::BitStringPat { segments, .. } => {
            for segment in segments {
                add_pat_type_symbols(index, uri, line_index, source, &segment.value, check);
                if let Some(size) = &segment.size {
                    add_expr_type_symbols(index, uri, line_index, source, size, check);
                }
            }
        }
        ast::Pat::ListPat { elements, .. }
        | ast::Pat::Or {
            patterns: elements, ..
        } => {
            for element in elements {
                add_pat_type_symbols(index, uri, line_index, source, element, check);
            }
        }
        ast::Pat::ConsPat { head, tail, .. } => {
            add_pat_type_symbols(index, uri, line_index, source, head, check);
            add_pat_type_symbols(index, uri, line_index, source, tail, check);
        }
        ast::Pat::Wildcard { .. } | ast::Pat::Var { .. } | ast::Pat::Lit { .. } => {}
    }
}

fn add_stmt_type_symbols(
    index: &mut SemanticIndex,
    uri: &Url,
    line_index: &LineIndex,
    source: &str,
    stmt: &ast::Stmt,
    check: &typechecker::CheckResult,
) {
    match stmt {
        ast::Stmt::Let {
            pattern,
            annotation,
            value,
            ..
        } => {
            add_pat_type_symbols(index, uri, line_index, source, pattern, check);
            if let Some(annotation) = annotation {
                add_type_expr_symbols(index, uri, line_index, source, annotation, check);
            }
            add_expr_type_symbols(index, uri, line_index, source, value, check);
        }
        ast::Stmt::LetFun {
            params,
            guard,
            body,
            ..
        } => {
            for param in params {
                add_pat_type_symbols(index, uri, line_index, source, param, check);
            }
            if let Some(guard) = guard {
                add_expr_type_symbols(index, uri, line_index, source, guard, check);
            }
            add_expr_type_symbols(index, uri, line_index, source, body, check);
        }
        ast::Stmt::Expr(expr) => add_expr_type_symbols(index, uri, line_index, source, expr, check),
    }
}

fn add_expr_type_symbols(
    index: &mut SemanticIndex,
    uri: &Url,
    line_index: &LineIndex,
    source: &str,
    expr: &ast::Expr,
    check: &typechecker::CheckResult,
) {
    match &expr.kind {
        ast::ExprKind::Lit { .. }
        | ast::ExprKind::Constructor { .. }
        | ast::ExprKind::DictRef { .. }
        | ast::ExprKind::SymbolIntrinsic { .. } => {}
        ast::ExprKind::Var { name } => {
            if let Some((trait_name, method_name)) = check.resolved_trait_method_for_node(expr.id) {
                add_trait_method_reference_symbol(
                    index,
                    uri,
                    trait_name,
                    method_name,
                    final_segment_name_range(expr.span, name, line_index, source),
                );
            }
        }
        ast::ExprKind::QualifiedName { name, .. } => {
            if let Some((trait_name, method_name)) = check.resolved_trait_method_for_node(expr.id) {
                add_trait_method_reference_symbol(
                    index,
                    uri,
                    trait_name,
                    method_name,
                    final_segment_name_range(expr.span, name, line_index, source),
                );
            }
        }
        ast::ExprKind::App { func, arg } => {
            add_expr_type_symbols(index, uri, line_index, source, func, check);
            add_expr_type_symbols(index, uri, line_index, source, arg, check);
        }
        ast::ExprKind::BinOp { left, right, .. } => {
            add_expr_type_symbols(index, uri, line_index, source, left, check);
            add_expr_type_symbols(index, uri, line_index, source, right, check);
        }
        ast::ExprKind::UnaryMinus { expr } => {
            add_expr_type_symbols(index, uri, line_index, source, expr, check);
        }
        ast::ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            add_expr_type_symbols(index, uri, line_index, source, cond, check);
            add_expr_type_symbols(index, uri, line_index, source, then_branch, check);
            add_expr_type_symbols(index, uri, line_index, source, else_branch, check);
        }
        ast::ExprKind::Case {
            scrutinee, arms, ..
        } => {
            add_expr_type_symbols(index, uri, line_index, source, scrutinee, check);
            for arm in arms {
                add_pat_type_symbols(index, uri, line_index, source, &arm.node.pattern, check);
                if let Some(guard) = &arm.node.guard {
                    add_expr_type_symbols(index, uri, line_index, source, guard, check);
                }
                add_expr_type_symbols(index, uri, line_index, source, &arm.node.body, check);
            }
        }
        ast::ExprKind::Block { stmts, .. } => {
            for stmt in stmts {
                add_stmt_type_symbols(index, uri, line_index, source, &stmt.node, check);
            }
        }
        ast::ExprKind::Lambda { params, body } => {
            for param in params {
                add_pat_type_symbols(index, uri, line_index, source, param, check);
            }
            add_expr_type_symbols(index, uri, line_index, source, body, check);
        }
        ast::ExprKind::FieldAccess { expr, .. } => {
            add_expr_type_symbols(index, uri, line_index, source, expr, check);
        }
        ast::ExprKind::RecordCreate { name, fields, .. } => {
            if let Some(resolved) = check.resolved_type_name_for_node(expr.id) {
                add_type_reference_symbol(
                    index,
                    uri,
                    resolved.to_string(),
                    name_range(expr.span.start, name, line_index, source),
                );
            }
            for (_, _, value) in fields {
                add_expr_type_symbols(index, uri, line_index, source, value, check);
            }
        }
        ast::ExprKind::AnonRecordCreate { fields } => {
            for (_, _, value) in fields {
                add_expr_type_symbols(index, uri, line_index, source, value, check);
            }
        }
        ast::ExprKind::RecordUpdate { record, fields, .. } => {
            add_expr_type_symbols(index, uri, line_index, source, record, check);
            for (_, _, value) in fields {
                add_expr_type_symbols(index, uri, line_index, source, value, check);
            }
        }
        ast::ExprKind::EffectCall {
            name,
            qualifier,
            args,
        } => {
            if let Some((effect_name, op_name)) =
                check.resolved_effect_operation_for_call_node(expr.id)
            {
                add_effect_operation_reference_symbol(
                    index,
                    uri,
                    effect_name,
                    op_name,
                    final_segment_name_range(expr.span, name, line_index, source),
                );
            }
            if let Some(qualifier) = qualifier
                && let Some(resolved) = check.resolved_effect_call_effect_name_for_node(expr.id)
            {
                add_semantic_symbol_reference(
                    index,
                    uri,
                    SemanticSymbolKind::Effect,
                    resolved.to_string(),
                    name_range(expr.span.start, qualifier, line_index, source),
                );
            }
            for arg in args {
                add_expr_type_symbols(index, uri, line_index, source, arg, check);
            }
        }
        ast::ExprKind::With { expr, handler } => {
            add_expr_type_symbols(index, uri, line_index, source, expr, check);
            add_handler_type_symbols(index, uri, line_index, source, handler, check);
        }
        ast::ExprKind::Resume { value } => {
            add_expr_type_symbols(index, uri, line_index, source, value, check);
        }
        ast::ExprKind::Tuple { elements } | ast::ExprKind::ListLit { elements } => {
            for element in elements {
                add_expr_type_symbols(index, uri, line_index, source, element, check);
            }
        }
        ast::ExprKind::Do {
            bindings,
            success,
            else_arms,
            ..
        } => {
            for (pattern, value) in bindings {
                add_pat_type_symbols(index, uri, line_index, source, pattern, check);
                add_expr_type_symbols(index, uri, line_index, source, value, check);
            }
            add_expr_type_symbols(index, uri, line_index, source, success, check);
            for arm in else_arms {
                add_pat_type_symbols(index, uri, line_index, source, &arm.node.pattern, check);
                if let Some(guard) = &arm.node.guard {
                    add_expr_type_symbols(index, uri, line_index, source, guard, check);
                }
                add_expr_type_symbols(index, uri, line_index, source, &arm.node.body, check);
            }
        }
        ast::ExprKind::Receive {
            arms, after_clause, ..
        } => {
            for arm in arms {
                add_pat_type_symbols(index, uri, line_index, source, &arm.node.pattern, check);
                if let Some(guard) = &arm.node.guard {
                    add_expr_type_symbols(index, uri, line_index, source, guard, check);
                }
                add_expr_type_symbols(index, uri, line_index, source, &arm.node.body, check);
            }
            if let Some((timeout, body)) = after_clause {
                add_expr_type_symbols(index, uri, line_index, source, timeout, check);
                add_expr_type_symbols(index, uri, line_index, source, body, check);
            }
        }
        ast::ExprKind::BitString { segments } => {
            for segment in segments {
                add_expr_type_symbols(index, uri, line_index, source, &segment.value, check);
                if let Some(size) = &segment.size {
                    add_expr_type_symbols(index, uri, line_index, source, size, check);
                }
            }
        }
        ast::ExprKind::Ascription { expr, type_expr } => {
            add_expr_type_symbols(index, uri, line_index, source, expr, check);
            add_type_expr_symbols(index, uri, line_index, source, type_expr, check);
        }
        ast::ExprKind::HandlerExpr { body } => {
            add_handler_body_type_symbols(index, uri, line_index, source, body, check);
        }
        ast::ExprKind::Pipe { segments, .. }
        | ast::ExprKind::BinOpChain { segments, .. }
        | ast::ExprKind::PipeBack { segments }
        | ast::ExprKind::ComposeForward { segments } => {
            for segment in segments {
                add_expr_type_symbols(index, uri, line_index, source, &segment.node, check);
            }
        }
        ast::ExprKind::Cons { head, tail } => {
            add_expr_type_symbols(index, uri, line_index, source, head, check);
            add_expr_type_symbols(index, uri, line_index, source, tail, check);
        }
        ast::ExprKind::StringInterp { parts, .. } => {
            for part in parts {
                if let ast::StringPart::Expr(expr) = part {
                    add_expr_type_symbols(index, uri, line_index, source, expr, check);
                }
            }
        }
        ast::ExprKind::ListComprehension { body, qualifiers } => {
            add_expr_type_symbols(index, uri, line_index, source, body, check);
            for qualifier in qualifiers {
                match qualifier {
                    ast::ComprehensionQualifier::Generator(pattern, value)
                    | ast::ComprehensionQualifier::Let(pattern, value) => {
                        add_pat_type_symbols(index, uri, line_index, source, pattern, check);
                        add_expr_type_symbols(index, uri, line_index, source, value, check);
                    }
                    ast::ComprehensionQualifier::Guard(value) => {
                        add_expr_type_symbols(index, uri, line_index, source, value, check);
                    }
                }
            }
        }
        ast::ExprKind::DictMethodAccess { dict, .. }
        | ast::ExprKind::DictSuperAccess { dict, .. } => {
            add_expr_type_symbols(index, uri, line_index, source, dict, check);
        }
        ast::ExprKind::ForeignCall { args, .. } => {
            for arg in args {
                add_expr_type_symbols(index, uri, line_index, source, arg, check);
            }
        }
    }
}

fn add_handler_body_type_symbols(
    index: &mut SemanticIndex,
    uri: &Url,
    line_index: &LineIndex,
    source: &str,
    body: &ast::HandlerBody,
    check: &typechecker::CheckResult,
) {
    for effect_ref in &body.effects {
        add_effect_ref_symbol(index, uri, line_index, source, effect_ref, check);
    }
    for effect_ref in &body.needs {
        add_effect_ref_symbol(index, uri, line_index, source, effect_ref, check);
    }
    add_where_clause_type_symbols(index, uri, line_index, source, &body.where_clause, check);
    for arm in &body.arms {
        add_handler_arm_type_symbols(index, uri, line_index, source, &arm.node, check);
    }
    if let Some(return_clause) = &body.return_clause {
        add_handler_arm_type_symbols(index, uri, line_index, source, return_clause, check);
    }
}

fn add_handler_type_symbols(
    index: &mut SemanticIndex,
    uri: &Url,
    line_index: &LineIndex,
    source: &str,
    handler: &ast::Handler,
    check: &typechecker::CheckResult,
) {
    match handler {
        ast::Handler::Named(named) => {
            add_handler_ref_symbol(index, uri, line_index, source, named, check);
        }
        ast::Handler::Inline { items, .. } => {
            for item in items {
                match &item.node {
                    ast::HandlerItem::Named(named) => {
                        add_handler_ref_symbol(index, uri, line_index, source, named, check);
                    }
                    ast::HandlerItem::Arm(arm) | ast::HandlerItem::Return(arm) => {
                        add_handler_arm_type_symbols(index, uri, line_index, source, arm, check);
                    }
                }
            }
        }
    }
}

fn add_handler_arm_type_symbols(
    index: &mut SemanticIndex,
    uri: &Url,
    line_index: &LineIndex,
    source: &str,
    arm: &ast::HandlerArm,
    check: &typechecker::CheckResult,
) {
    if let Some(qualifier) = &arm.qualifier
        && let Some(resolved) = check.resolved_handler_arm_effect_name_for_node(arm.id)
    {
        add_semantic_symbol_reference(
            index,
            uri,
            SemanticSymbolKind::Effect,
            resolved.to_string(),
            name_range(arm.span.start, qualifier, line_index, source),
        );
    }
    if let Some((effect_name, op_name)) =
        check.resolved_effect_operation_for_handler_arm_node(arm.id)
    {
        add_effect_operation_reference_symbol(
            index,
            uri,
            effect_name,
            op_name,
            final_segment_name_range(arm.span, &arm.op_name, line_index, source),
        );
    }
    for param in &arm.params {
        add_pat_type_symbols(index, uri, line_index, source, param, check);
    }
    add_expr_type_symbols(index, uri, line_index, source, &arm.body, check);
    if let Some(finally_block) = &arm.finally_block {
        add_expr_type_symbols(index, uri, line_index, source, finally_block, check);
    }
}

fn semantic_value_references_for_program(
    check: &typechecker::CheckResult,
    program: &[ast::Decl],
) -> HashMap<ast::NodeId, ast::NodeId> {
    let local_definitions = collect_local_value_binding_definitions(program);
    let mut references = check.references.clone();
    for (usage_id, binding_id) in check.local_value_references() {
        if let Some(definition_id) = local_definitions.get(&binding_id) {
            references.insert(usage_id, *definition_id);
        }
    }
    references
}

fn collect_local_value_binding_definitions(program: &[ast::Decl]) -> HashMap<u32, ast::NodeId> {
    let mut collector = LocalBindingDefinitionCollector::default();
    collector.collect_program(program);
    collector.definitions
}

#[derive(Default)]
struct LocalBindingDefinitionCollector {
    next_binding_id: u32,
    definitions: HashMap<u32, ast::NodeId>,
}

impl LocalBindingDefinitionCollector {
    fn collect_program(&mut self, program: &[ast::Decl]) {
        for decl in program {
            self.collect_decl(decl);
        }
    }

    fn bind_node(&mut self, node_id: ast::NodeId) {
        self.definitions.insert(self.next_binding_id, node_id);
        self.next_binding_id += 1;
    }

    fn collect_decl(&mut self, decl: &ast::Decl) {
        match decl {
            ast::Decl::FunSignature {
                params,
                return_type,
                effects,
                where_clause,
                ..
            } => {
                let _ = (params, return_type, effects, where_clause);
            }
            ast::Decl::FunBinding {
                params,
                body,
                guard,
                ..
            } => {
                for param in params {
                    self.bind_pattern(param);
                }
                self.collect_expr(body);
                if let Some(guard) = guard {
                    self.collect_expr(guard);
                }
            }
            ast::Decl::Let { value, .. } => self.collect_expr(value),
            ast::Decl::HandlerDef { body, .. } => self.collect_handler_body(body),
            ast::Decl::ImplDef { methods, .. } => {
                for method in methods {
                    for param in &method.node.params {
                        self.bind_pattern(param);
                    }
                    self.collect_expr(&method.node.body);
                }
            }
            ast::Decl::DictConstructor { methods, .. } => {
                for method in methods {
                    self.collect_expr(method);
                }
            }
            _ => {}
        }
    }

    fn bind_pattern(&mut self, pat: &ast::Pat) {
        match pat {
            ast::Pat::Var { id, .. } => self.bind_node(*id),
            ast::Pat::Constructor { args, .. } => {
                for arg in args {
                    self.bind_pattern(arg);
                }
            }
            ast::Pat::Record {
                fields, as_name, ..
            } => {
                for (_, alias) in fields {
                    if let Some(alias) = alias {
                        self.bind_pattern(alias);
                    } else {
                        self.bind_node(pat.id());
                    }
                }
                if as_name.is_some() {
                    self.bind_node(pat.id());
                }
            }
            ast::Pat::AnonRecord { fields, .. } => {
                for (_, alias) in fields {
                    if let Some(alias) = alias {
                        self.bind_pattern(alias);
                    } else {
                        self.bind_node(pat.id());
                    }
                }
            }
            ast::Pat::Tuple { elements, .. } | ast::Pat::ListPat { elements, .. } => {
                for element in elements {
                    self.bind_pattern(element);
                }
            }
            ast::Pat::StringPrefix { rest, .. } => self.bind_pattern(rest),
            ast::Pat::BitStringPat { segments, .. } => {
                for segment in segments {
                    self.bind_pattern(&segment.value);
                }
            }
            ast::Pat::ConsPat { head, tail, .. } => {
                self.bind_pattern(head);
                self.bind_pattern(tail);
            }
            ast::Pat::Or { patterns, .. } => {
                if let Some(first) = patterns.first() {
                    self.bind_pattern(first);
                }
            }
            ast::Pat::Wildcard { .. } | ast::Pat::Lit { .. } => {}
        }
    }

    fn collect_stmt(&mut self, stmt: &ast::Stmt) {
        match stmt {
            ast::Stmt::Expr(expr) => self.collect_expr(expr),
            ast::Stmt::Let { pattern, value, .. } => {
                self.collect_expr(value);
                self.bind_pattern(pattern);
            }
            ast::Stmt::LetFun {
                id,
                params,
                guard,
                body,
                ..
            } => {
                self.bind_node(*id);
                for param in params {
                    self.bind_pattern(param);
                }
                if let Some(guard) = guard {
                    self.collect_expr(guard);
                }
                self.collect_expr(body);
            }
        }
    }

    fn collect_expr(&mut self, expr: &ast::Expr) {
        match &expr.kind {
            ast::ExprKind::Lit { .. }
            | ast::ExprKind::Var { .. }
            | ast::ExprKind::Constructor { .. }
            | ast::ExprKind::QualifiedName { .. }
            | ast::ExprKind::DictRef { .. }
            | ast::ExprKind::SymbolIntrinsic { .. } => {}
            ast::ExprKind::App { func, arg } => {
                self.collect_expr(func);
                self.collect_expr(arg);
            }
            ast::ExprKind::BinOp { left, right, .. } => {
                self.collect_expr(left);
                self.collect_expr(right);
            }
            ast::ExprKind::UnaryMinus { expr } => self.collect_expr(expr),
            ast::ExprKind::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                self.collect_expr(cond);
                self.collect_expr(then_branch);
                self.collect_expr(else_branch);
            }
            ast::ExprKind::Case {
                scrutinee, arms, ..
            } => {
                self.collect_expr(scrutinee);
                for arm in arms {
                    self.bind_pattern(&arm.node.pattern);
                    if let Some(guard) = &arm.node.guard {
                        self.collect_expr(guard);
                    }
                    self.collect_expr(&arm.node.body);
                }
            }
            ast::ExprKind::Block { stmts, .. } => {
                for stmt in stmts {
                    self.collect_stmt(&stmt.node);
                }
            }
            ast::ExprKind::Lambda { params, body } => {
                for param in params {
                    self.bind_pattern(param);
                }
                self.collect_expr(body);
            }
            ast::ExprKind::FieldAccess { expr, .. } => self.collect_expr(expr),
            ast::ExprKind::RecordCreate { fields, .. }
            | ast::ExprKind::AnonRecordCreate { fields, .. } => {
                for (_, _, value) in fields {
                    self.collect_expr(value);
                }
            }
            ast::ExprKind::RecordUpdate { record, fields, .. } => {
                self.collect_expr(record);
                for (_, _, value) in fields {
                    self.collect_expr(value);
                }
            }
            ast::ExprKind::EffectCall { args, .. } => {
                for arg in args {
                    self.collect_expr(arg);
                }
            }
            ast::ExprKind::With { expr, handler } => {
                self.collect_expr(expr);
                self.collect_handler(handler);
            }
            ast::ExprKind::Resume { value } => self.collect_expr(value),
            ast::ExprKind::Tuple { elements } | ast::ExprKind::ListLit { elements } => {
                for element in elements {
                    self.collect_expr(element);
                }
            }
            ast::ExprKind::Do {
                bindings,
                success,
                else_arms,
                ..
            } => {
                for (pattern, value) in bindings {
                    self.collect_expr(value);
                    self.bind_pattern(pattern);
                }
                self.collect_expr(success);
                for arm in else_arms {
                    self.bind_pattern(&arm.node.pattern);
                    if let Some(guard) = &arm.node.guard {
                        self.collect_expr(guard);
                    }
                    self.collect_expr(&arm.node.body);
                }
            }
            ast::ExprKind::Receive {
                arms, after_clause, ..
            } => {
                for arm in arms {
                    self.bind_pattern(&arm.node.pattern);
                    if let Some(guard) = &arm.node.guard {
                        self.collect_expr(guard);
                    }
                    self.collect_expr(&arm.node.body);
                }
                if let Some((timeout, body)) = after_clause {
                    self.collect_expr(timeout);
                    self.collect_expr(body);
                }
            }
            ast::ExprKind::BitString { segments } => {
                for segment in segments {
                    self.collect_expr(&segment.value);
                    if let Some(size) = &segment.size {
                        self.collect_expr(size);
                    }
                }
            }
            ast::ExprKind::Ascription { expr, .. } => self.collect_expr(expr),
            ast::ExprKind::HandlerExpr { body } => self.collect_handler_body(body),
            ast::ExprKind::Pipe { segments, .. }
            | ast::ExprKind::BinOpChain { segments, .. }
            | ast::ExprKind::PipeBack { segments }
            | ast::ExprKind::ComposeForward { segments } => {
                for segment in segments {
                    self.collect_expr(&segment.node);
                }
            }
            ast::ExprKind::Cons { head, tail } => {
                self.collect_expr(head);
                self.collect_expr(tail);
            }
            ast::ExprKind::StringInterp { parts, .. } => {
                for part in parts {
                    if let ast::StringPart::Expr(expr) = part {
                        self.collect_expr(expr);
                    }
                }
            }
            ast::ExprKind::ListComprehension { body, qualifiers } => {
                self.collect_expr(body);
                for qualifier in qualifiers {
                    match qualifier {
                        ast::ComprehensionQualifier::Generator(pattern, value)
                        | ast::ComprehensionQualifier::Let(pattern, value) => {
                            self.collect_expr(value);
                            self.bind_pattern(pattern);
                        }
                        ast::ComprehensionQualifier::Guard(value) => self.collect_expr(value),
                    }
                }
            }
            ast::ExprKind::DictMethodAccess { dict, .. }
            | ast::ExprKind::DictSuperAccess { dict, .. } => self.collect_expr(dict),
            ast::ExprKind::ForeignCall { args, .. } => {
                for arg in args {
                    self.collect_expr(arg);
                }
            }
        }
    }

    fn collect_handler_body(&mut self, body: &ast::HandlerBody) {
        for arm in &body.arms {
            self.collect_handler_arm(&arm.node);
        }
        if let Some(return_clause) = &body.return_clause {
            for param in &return_clause.params {
                self.bind_pattern(param);
            }
            self.collect_expr(&return_clause.body);
        }
    }

    fn collect_handler(&mut self, handler: &ast::Handler) {
        match handler {
            ast::Handler::Named(_) => {}
            ast::Handler::Inline { items, .. } => {
                for item in items {
                    match &item.node {
                        ast::HandlerItem::Named(_) => {}
                        ast::HandlerItem::Arm(arm) | ast::HandlerItem::Return(arm) => {
                            self.collect_handler_arm(arm);
                        }
                    }
                }
            }
        }
    }

    fn collect_handler_arm(&mut self, arm: &ast::HandlerArm) {
        for param in &arm.params {
            self.bind_pattern(param);
        }
        self.collect_expr(&arm.body);
        if let Some(finally_block) = &arm.finally_block {
            self.collect_expr(finally_block);
        }
    }
}

fn collect_value_definition_nodes(program: &[ast::Decl]) -> HashSet<ast::NodeId> {
    let mut definition_nodes = HashSet::new();
    collect_value_definition_nodes_into(program, &mut definition_nodes);
    definition_nodes
}

fn collect_value_definition_nodes_into(program: &[ast::Decl], out: &mut HashSet<ast::NodeId>) {
    for decl in program {
        collect_decl_value_definition_nodes(decl, out);
    }
}

fn collect_decl_value_definition_nodes(decl: &ast::Decl, out: &mut HashSet<ast::NodeId>) {
    match decl {
        ast::Decl::FunSignature { id, .. }
        | ast::Decl::FunBinding { id, .. }
        | ast::Decl::Let { id, .. }
        | ast::Decl::HandlerDef { id, .. }
        | ast::Decl::DictConstructor { id, .. } => {
            out.insert(*id);
        }
        _ => {}
    }

    match decl {
        ast::Decl::FunBinding {
            params,
            guard,
            body,
            ..
        } => {
            for param in params {
                collect_pat_value_definition_nodes(param, out);
            }
            if let Some(guard) = guard {
                collect_expr_value_definition_nodes(guard, out);
            }
            collect_expr_value_definition_nodes(body, out);
        }
        ast::Decl::Let { value, .. } => collect_expr_value_definition_nodes(value, out),
        ast::Decl::HandlerDef { body, .. } => {
            collect_handler_body_value_definition_nodes(body, out);
        }
        ast::Decl::ImplDef { methods, .. } => {
            for method in methods {
                for param in &method.node.params {
                    collect_pat_value_definition_nodes(param, out);
                }
                collect_expr_value_definition_nodes(&method.node.body, out);
            }
        }
        ast::Decl::DictConstructor { methods, .. } => {
            for method in methods {
                collect_expr_value_definition_nodes(method, out);
            }
        }
        _ => {}
    }
}

fn collect_pat_value_definition_nodes(pat: &ast::Pat, out: &mut HashSet<ast::NodeId>) {
    match pat {
        ast::Pat::Var { id, .. } => {
            out.insert(*id);
        }
        ast::Pat::Constructor { args, .. } | ast::Pat::Tuple { elements: args, .. } => {
            for arg in args {
                collect_pat_value_definition_nodes(arg, out);
            }
        }
        ast::Pat::Record {
            fields, as_name, ..
        } => {
            for (_, field_pat) in fields {
                if let Some(field_pat) = field_pat {
                    collect_pat_value_definition_nodes(field_pat, out);
                }
            }
            if as_name.is_some() {
                out.insert(pat.id());
            }
        }
        ast::Pat::AnonRecord { fields, .. } => {
            for (_, field_pat) in fields {
                if let Some(field_pat) = field_pat {
                    collect_pat_value_definition_nodes(field_pat, out);
                }
            }
        }
        ast::Pat::StringPrefix { rest, .. } => collect_pat_value_definition_nodes(rest, out),
        ast::Pat::BitStringPat { segments, .. } => {
            for segment in segments {
                collect_pat_value_definition_nodes(&segment.value, out);
            }
        }
        ast::Pat::ListPat { elements, .. }
        | ast::Pat::Or {
            patterns: elements, ..
        } => {
            for element in elements {
                collect_pat_value_definition_nodes(element, out);
            }
        }
        ast::Pat::ConsPat { head, tail, .. } => {
            collect_pat_value_definition_nodes(head, out);
            collect_pat_value_definition_nodes(tail, out);
        }
        ast::Pat::Wildcard { .. } | ast::Pat::Lit { .. } => {}
    }
}

fn collect_stmt_value_definition_nodes(stmt: &ast::Stmt, out: &mut HashSet<ast::NodeId>) {
    match stmt {
        ast::Stmt::Let { pattern, value, .. } => {
            collect_pat_value_definition_nodes(pattern, out);
            collect_expr_value_definition_nodes(value, out);
        }
        ast::Stmt::LetFun {
            id,
            params,
            guard,
            body,
            ..
        } => {
            out.insert(*id);
            for param in params {
                collect_pat_value_definition_nodes(param, out);
            }
            if let Some(guard) = guard {
                collect_expr_value_definition_nodes(guard, out);
            }
            collect_expr_value_definition_nodes(body, out);
        }
        ast::Stmt::Expr(expr) => collect_expr_value_definition_nodes(expr, out),
    }
}

fn collect_expr_value_definition_nodes(expr: &ast::Expr, out: &mut HashSet<ast::NodeId>) {
    match &expr.kind {
        ast::ExprKind::Lit { .. }
        | ast::ExprKind::Var { .. }
        | ast::ExprKind::Constructor { .. }
        | ast::ExprKind::QualifiedName { .. }
        | ast::ExprKind::DictRef { .. }
        | ast::ExprKind::SymbolIntrinsic { .. } => {}
        ast::ExprKind::App { func, arg } => {
            collect_expr_value_definition_nodes(func, out);
            collect_expr_value_definition_nodes(arg, out);
        }
        ast::ExprKind::BinOp { left, right, .. } => {
            collect_expr_value_definition_nodes(left, out);
            collect_expr_value_definition_nodes(right, out);
        }
        ast::ExprKind::UnaryMinus { expr } => collect_expr_value_definition_nodes(expr, out),
        ast::ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_expr_value_definition_nodes(cond, out);
            collect_expr_value_definition_nodes(then_branch, out);
            collect_expr_value_definition_nodes(else_branch, out);
        }
        ast::ExprKind::Case {
            scrutinee, arms, ..
        } => {
            collect_expr_value_definition_nodes(scrutinee, out);
            for arm in arms {
                collect_pat_value_definition_nodes(&arm.node.pattern, out);
                if let Some(guard) = &arm.node.guard {
                    collect_expr_value_definition_nodes(guard, out);
                }
                collect_expr_value_definition_nodes(&arm.node.body, out);
            }
        }
        ast::ExprKind::Block { stmts, .. } => {
            for stmt in stmts {
                collect_stmt_value_definition_nodes(&stmt.node, out);
            }
        }
        ast::ExprKind::Lambda { params, body } => {
            for param in params {
                collect_pat_value_definition_nodes(param, out);
            }
            collect_expr_value_definition_nodes(body, out);
        }
        ast::ExprKind::FieldAccess { expr, .. } => {
            collect_expr_value_definition_nodes(expr, out);
        }
        ast::ExprKind::RecordCreate { fields, .. }
        | ast::ExprKind::AnonRecordCreate { fields, .. } => {
            for (_, _, value) in fields {
                collect_expr_value_definition_nodes(value, out);
            }
        }
        ast::ExprKind::RecordUpdate { record, fields, .. } => {
            collect_expr_value_definition_nodes(record, out);
            for (_, _, value) in fields {
                collect_expr_value_definition_nodes(value, out);
            }
        }
        ast::ExprKind::EffectCall { args, .. } => {
            for arg in args {
                collect_expr_value_definition_nodes(arg, out);
            }
        }
        ast::ExprKind::With { expr, handler } => {
            collect_expr_value_definition_nodes(expr, out);
            collect_handler_value_definition_nodes(handler, out);
        }
        ast::ExprKind::Resume { value } => collect_expr_value_definition_nodes(value, out),
        ast::ExprKind::Tuple { elements } | ast::ExprKind::ListLit { elements } => {
            for element in elements {
                collect_expr_value_definition_nodes(element, out);
            }
        }
        ast::ExprKind::Do {
            bindings,
            success,
            else_arms,
            ..
        } => {
            for (pattern, value) in bindings {
                collect_pat_value_definition_nodes(pattern, out);
                collect_expr_value_definition_nodes(value, out);
            }
            collect_expr_value_definition_nodes(success, out);
            for arm in else_arms {
                collect_pat_value_definition_nodes(&arm.node.pattern, out);
                if let Some(guard) = &arm.node.guard {
                    collect_expr_value_definition_nodes(guard, out);
                }
                collect_expr_value_definition_nodes(&arm.node.body, out);
            }
        }
        ast::ExprKind::Receive {
            arms, after_clause, ..
        } => {
            for arm in arms {
                collect_pat_value_definition_nodes(&arm.node.pattern, out);
                if let Some(guard) = &arm.node.guard {
                    collect_expr_value_definition_nodes(guard, out);
                }
                collect_expr_value_definition_nodes(&arm.node.body, out);
            }
            if let Some((timeout, body)) = after_clause {
                collect_expr_value_definition_nodes(timeout, out);
                collect_expr_value_definition_nodes(body, out);
            }
        }
        ast::ExprKind::BitString { segments } => {
            for segment in segments {
                collect_expr_value_definition_nodes(&segment.value, out);
                if let Some(size) = &segment.size {
                    collect_expr_value_definition_nodes(size, out);
                }
            }
        }
        ast::ExprKind::Ascription { expr, .. } => {
            collect_expr_value_definition_nodes(expr, out);
        }
        ast::ExprKind::HandlerExpr { body } => {
            collect_handler_body_value_definition_nodes(body, out);
        }
        ast::ExprKind::Pipe { segments, .. }
        | ast::ExprKind::BinOpChain { segments, .. }
        | ast::ExprKind::PipeBack { segments }
        | ast::ExprKind::ComposeForward { segments } => {
            for segment in segments {
                collect_expr_value_definition_nodes(&segment.node, out);
            }
        }
        ast::ExprKind::Cons { head, tail } => {
            collect_expr_value_definition_nodes(head, out);
            collect_expr_value_definition_nodes(tail, out);
        }
        ast::ExprKind::StringInterp { parts, .. } => {
            for part in parts {
                if let ast::StringPart::Expr(expr) = part {
                    collect_expr_value_definition_nodes(expr, out);
                }
            }
        }
        ast::ExprKind::ListComprehension { body, qualifiers } => {
            collect_expr_value_definition_nodes(body, out);
            for qualifier in qualifiers {
                match qualifier {
                    ast::ComprehensionQualifier::Generator(pattern, value)
                    | ast::ComprehensionQualifier::Let(pattern, value) => {
                        collect_pat_value_definition_nodes(pattern, out);
                        collect_expr_value_definition_nodes(value, out);
                    }
                    ast::ComprehensionQualifier::Guard(value) => {
                        collect_expr_value_definition_nodes(value, out);
                    }
                }
            }
        }
        ast::ExprKind::DictMethodAccess { dict, .. }
        | ast::ExprKind::DictSuperAccess { dict, .. } => {
            collect_expr_value_definition_nodes(dict, out);
        }
        ast::ExprKind::ForeignCall { args, .. } => {
            for arg in args {
                collect_expr_value_definition_nodes(arg, out);
            }
        }
    }
}

fn collect_handler_body_value_definition_nodes(
    body: &ast::HandlerBody,
    out: &mut HashSet<ast::NodeId>,
) {
    for arm in &body.arms {
        collect_handler_arm_value_definition_nodes(&arm.node, out);
    }
    if let Some(return_clause) = &body.return_clause {
        collect_handler_arm_value_definition_nodes(return_clause, out);
    }
}

fn collect_handler_value_definition_nodes(handler: &ast::Handler, out: &mut HashSet<ast::NodeId>) {
    match handler {
        ast::Handler::Named(_) => {}
        ast::Handler::Inline { items, .. } => {
            for item in items {
                match &item.node {
                    ast::HandlerItem::Named(_) => {}
                    ast::HandlerItem::Arm(arm) | ast::HandlerItem::Return(arm) => {
                        collect_handler_arm_value_definition_nodes(arm, out);
                    }
                }
            }
        }
    }
}

fn collect_handler_arm_value_definition_nodes(
    arm: &ast::HandlerArm,
    out: &mut HashSet<ast::NodeId>,
) {
    for param in &arm.params {
        collect_pat_value_definition_nodes(param, out);
    }
    collect_expr_value_definition_nodes(&arm.body, out);
    if let Some(finally_block) = &arm.finally_block {
        collect_expr_value_definition_nodes(finally_block, out);
    }
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
    let had_semantic = result.semantic.is_some();
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
    if let Some(update) = result.semantic_index_update {
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

fn span_to_range(span: &saga::token::Span, line_index: &LineIndex, source: &str) -> Range {
    Range {
        start: line_index.offset_to_position(span.start, source),
        end: line_index.offset_to_position(span.end, source),
    }
}

fn position_leq(a: Position, b: Position) -> bool {
    a.line < b.line || (a.line == b.line && a.character <= b.character)
}

fn range_contains_position(range: &Range, position: Position) -> bool {
    position_leq(range.start, position) && position_leq(position, range.end)
}

fn range_width(range: &Range) -> u32 {
    range
        .end
        .line
        .saturating_sub(range.start.line)
        .saturating_mul(u32::MAX / 2)
        .saturating_add(range.end.character.saturating_sub(range.start.character))
}

fn sort_and_dedup_locations(locations: &mut Vec<Location>) {
    locations.sort_by(|a, b| {
        a.uri
            .as_str()
            .cmp(b.uri.as_str())
            .then(a.range.start.line.cmp(&b.range.start.line))
            .then(a.range.start.character.cmp(&b.range.start.character))
            .then(a.range.end.line.cmp(&b.range.end.line))
            .then(a.range.end.character.cmp(&b.range.end.character))
    });
    locations.dedup_by(|a, b| {
        a.uri == b.uri && a.range.start == b.range.start && a.range.end == b.range.end
    });
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

fn hover_type_at(uri: &Url, semantic: &SemanticSnapshot, position: Position) -> Option<Hover> {
    if let Some(hover) = hover_semantic_symbol_at(uri, semantic, position) {
        return Some(hover);
    }

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

fn hover_semantic_symbol_at(
    uri: &Url,
    semantic: &SemanticSnapshot,
    position: Position,
) -> Option<Hover> {
    let occurrence = semantic
        .semantic_index
        .symbol_location_at_position(uri, position)?;
    let (owner, member) = occurrence.key.name.rsplit_once('.')?;
    let signature = match occurrence.key.kind {
        SemanticSymbolKind::TraitMethod => semantic.check.trait_method_signature(owner, member),
        SemanticSymbolKind::EffectOperation => {
            semantic.check.effect_operation_signature(owner, member)
        }
        SemanticSymbolKind::Trait | SemanticSymbolKind::Effect | SemanticSymbolKind::Handler => {
            None
        }
    }?;

    Some(Hover {
        contents: HoverContents::Markup(MarkupContent {
            kind: MarkupKind::Markdown,
            value: format!("```saga\n{signature}\n```"),
        }),
        range: Some(occurrence.location.range),
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
    if let Some(location) = semantic
        .semantic_index
        .type_definition_location_at(uri, position)
    {
        return Some(location);
    }
    if let Some(location) = semantic
        .semantic_index
        .symbol_definition_location_at(uri, position)
    {
        return Some(location);
    }

    let offset = semantic
        .line_index
        .position_to_offset(position, &semantic.source);
    let (node_id, _) = smallest_node_at_offset(&semantic.check.node_spans, offset)?;
    semantic
        .semantic_index
        .definition_location_for_node(node_id)
        .or_else(|| {
            let def_id = semantic.semantic_index.identity_for_node(node_id);
            let def_span = semantic.check.node_spans.get(&def_id)?;
            Some(Location {
                uri: uri.clone(),
                range: span_to_range(def_span, &semantic.line_index, &semantic.source),
            })
        })
}

fn references_at(
    uri: &Url,
    semantic: &SemanticSnapshot,
    position: Position,
    include_declaration: bool,
) -> Vec<Location> {
    if let Some(locations) =
        semantic
            .semantic_index
            .type_reference_locations_at(uri, position, include_declaration)
    {
        return locations;
    }
    if let Some(locations) =
        semantic
            .semantic_index
            .symbol_reference_locations_at(uri, position, include_declaration)
    {
        return locations;
    }

    let offset = semantic
        .line_index
        .position_to_offset(position, &semantic.source);
    let Some((node_id, _)) = smallest_node_at_offset(&semantic.check.node_spans, offset) else {
        return Vec::new();
    };
    semantic
        .semantic_index
        .reference_locations_for_node(node_id, include_declaration)
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
                references_provider: Some(OneOf::Left(true)),
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
        store_document(&self.shared, uri.clone(), version, text.clone());
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
        store_document(&self.shared, uri.clone(), version, text.clone());
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

        Ok(hover_type_at(&uri, &semantic, position))
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
        let hover = hover_type_at(&uri, &semantic, Position::new(6, 10)).expect("hover");
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
    fn semantic_index_groups_references_by_definition_identity() {
        let uri = uri();
        let source = "\
module Main

fun id : Unit -> Unit
id x = x

fun main : Unit -> Unit
main () = id (id ())
";
        let shared = SharedState::default();
        let result = analyze_document(&shared, Some(&uri), 1, source, None);
        let semantic = result.semantic.expect("semantic snapshot");

        let outer_offset = source.find("id (").expect("outer id") + 1;
        let inner_offset = source.rfind("id ()").expect("inner id") + 1;
        let outer_position = semantic.line_index.offset_to_position(outer_offset, source);
        let inner_position = semantic.line_index.offset_to_position(inner_offset, source);

        let outer_refs = references_at(&uri, &semantic, outer_position, true);
        let inner_refs = references_at(&uri, &semantic, inner_position, true);

        assert_eq!(outer_refs, inner_refs);
        assert!(
            outer_refs.len() >= 3,
            "expected declaration and both call sites, got {outer_refs:?}"
        );
        assert!(
            outer_refs
                .iter()
                .any(|location| location.range.start.line == 2 || location.range.start.line == 3),
            "expected declaration location, got {outer_refs:?}"
        );
        assert!(
            outer_refs
                .iter()
                .filter(|location| location.range.start.line == 6)
                .count()
                >= 2,
            "expected both call sites, got {outer_refs:?}"
        );

        let usage_refs = references_at(&uri, &semantic, outer_position, false);
        assert!(
            usage_refs
                .iter()
                .filter(|location| location.range.start.line == 6)
                .count()
                >= 2,
            "expected both call sites without requiring declarations: {usage_refs:?}"
        );
        assert!(
            usage_refs
                .iter()
                .all(|location| location.range.start.line != 2 && location.range.start.line != 3),
            "declarations should be omitted when include_declaration is false: {usage_refs:?}"
        );
    }

    #[test]
    fn semantic_index_keeps_shadowed_local_references_separate() {
        let uri = uri();
        let source = "\
module Main

fun main : Unit -> Int
main () = {
  let x = 1
  let y = {
    let x = 2
    x
  }
  x
}
";
        let shared = SharedState::default();
        let result = analyze_document(&shared, Some(&uri), 1, source, None);
        let semantic = result.semantic.expect("semantic snapshot");

        let inner_offset = source.find("    x\n").expect("inner x") + 4;
        let outer_offset = source.rfind("  x\n").expect("outer x") + 2;
        let inner_position = semantic.line_index.offset_to_position(inner_offset, source);
        let outer_position = semantic.line_index.offset_to_position(outer_offset, source);

        let inner_refs = references_at(&uri, &semantic, inner_position, false);
        let outer_refs = references_at(&uri, &semantic, outer_position, false);

        assert_ne!(inner_refs, outer_refs);
        assert_eq!(inner_refs.len(), 1, "inner references: {inner_refs:?}");
        assert_eq!(outer_refs.len(), 1, "outer references: {outer_refs:?}");
        assert_eq!(inner_refs[0].range.start.line, 7);
        assert_eq!(outer_refs[0].range.start.line, 9);
    }

    #[test]
    fn semantic_index_resolves_type_names_before_value_fallback() {
        let uri = uri();
        let source = "\
module Main

type SeshType =
  | Spot
  | Downwinder

type BoardType =
  | Twintip
  | Hydrofoil

record Normalized {
  sesh_type: SeshType,
  board_type: BoardType,
}

fun parse_board_type : String -> BoardType
parse_board_type s = Twintip

fun from_row : Unit -> Normalized
from_row () = Normalized {
  sesh_type: Downwinder,
  board_type: Twintip,
}
";
        let shared = SharedState::default();
        let result = analyze_document(&shared, Some(&uri), 1, source, None);
        let semantic = result.semantic.expect("semantic snapshot");

        let sesh_usage = source
            .find("sesh_type: SeshType")
            .expect("SeshType field usage")
            + "sesh_type: ".len();
        let sesh_location = local_definition_at(
            &uri,
            &semantic,
            semantic.line_index.offset_to_position(sesh_usage, source),
        )
        .expect("SeshType definition");
        assert_eq!(sesh_location.range.start.line, 2);

        let board_usage = source
            .find("board_type: BoardType")
            .expect("BoardType field usage")
            + "board_type: ".len();
        let board_location = local_definition_at(
            &uri,
            &semantic,
            semantic.line_index.offset_to_position(board_usage, source),
        )
        .expect("BoardType definition");
        assert_eq!(board_location.range.start.line, 6);

        let normalized_constructor = source
            .rfind("Normalized {")
            .expect("Normalized constructor");
        let normalized_location = local_definition_at(
            &uri,
            &semantic,
            semantic
                .line_index
                .offset_to_position(normalized_constructor, source),
        )
        .expect("Normalized definition");
        assert_eq!(normalized_location.range.start.line, 10);

        let board_definition = source.find("BoardType\n").expect("BoardType definition");
        let board_refs = references_at(
            &uri,
            &semantic,
            semantic
                .line_index
                .offset_to_position(board_definition, source),
            false,
        );
        assert!(
            board_refs
                .iter()
                .all(|location| location.range.start.line != 6),
            "definition should be omitted: {board_refs:?}"
        );
        assert!(
            board_refs
                .iter()
                .any(|location| location.range.start.line == 12),
            "expected record field type reference: {board_refs:?}"
        );
        assert!(
            board_refs
                .iter()
                .any(|location| location.range.start.line == 15),
            "expected function return type reference: {board_refs:?}"
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

    #[test]
    fn module_interface_fingerprint_uses_stable_projection() {
        let int_scheme = typechecker::Scheme {
            forall: Vec::new(),
            constraints: Vec::new(),
            ty: typechecker::Type::Con("Int".to_string(), Vec::new()),
        };
        let bool_scheme = typechecker::Scheme {
            forall: Vec::new(),
            constraints: Vec::new(),
            ty: typechecker::Type::Con("Bool".to_string(), Vec::new()),
        };

        let mut left = typechecker::ModuleExports {
            bindings: vec![
                ("two".to_string(), int_scheme.clone()),
                ("one".to_string(), int_scheme.clone()),
            ],
            ..Default::default()
        };
        left.binding_origins
            .insert("one".to_string(), "Example.one".to_string());
        left.binding_origins
            .insert("two".to_string(), "Example.two".to_string());
        left.type_arity.insert("Pair".to_string(), 2);
        left.type_arity.insert("Box".to_string(), 1);
        left.doc_comments.insert(
            "one".to_string(),
            vec!["docs do not force recheck".to_string()],
        );

        let mut right = typechecker::ModuleExports {
            bindings: vec![
                ("one".to_string(), int_scheme.clone()),
                ("two".to_string(), int_scheme),
            ],
            ..Default::default()
        };
        right
            .binding_origins
            .insert("two".to_string(), "Example.two".to_string());
        right
            .binding_origins
            .insert("one".to_string(), "Example.one".to_string());
        right.type_arity.insert("Box".to_string(), 1);
        right.type_arity.insert("Pair".to_string(), 2);
        right
            .doc_comments
            .insert("one".to_string(), vec!["different docs".to_string()]);

        assert_eq!(
            module_interface_fingerprint(&left),
            module_interface_fingerprint(&right)
        );

        right.bindings[0].1 = bool_scheme;
        assert_ne!(
            module_interface_fingerprint(&left),
            module_interface_fingerprint(&right)
        );
    }
}
