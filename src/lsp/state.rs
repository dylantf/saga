use std::collections::{BTreeSet, HashMap, HashSet};
use std::path::PathBuf;

use saga::typechecker;
use tower_lsp::lsp_types::{Location, Url};

use super::analysis::{builtin_module_source_fingerprint, source_fingerprint_for_path};
use super::hover::{
    effect_operation_signature_in_check, effect_operation_signature_in_exports,
    trait_method_signature_in_check, trait_method_signature_in_exports,
};
use super::semantic::{SemanticIndex, SemanticSymbolKey};
use super::text::sort_and_dedup_locations;

#[derive(Default)]
pub(super) struct DependencyGraph {
    dependents: HashMap<String, HashSet<Url>>,
    imports: HashMap<Url, HashSet<String>>,
    module_of: HashMap<Url, String>,
}

impl DependencyGraph {
    pub(super) fn update_file(
        &mut self,
        uri: &Url,
        module_name: Option<String>,
        new_imports: HashSet<String>,
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

    pub(super) fn dependents_of(&self, uri: &Url) -> Vec<Url> {
        let Some(module) = self.module_of.get(uri) else {
            return Vec::new();
        };
        self.dependents
            .get(module)
            .map(|uris| uris.iter().cloned().collect())
            .unwrap_or_default()
    }

    pub(super) fn remove_file(&mut self, uri: &Url) -> Option<String> {
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
        self.module_of.remove(uri)
    }
}

#[derive(Default)]
pub(super) struct ProjectSemanticStore {
    pub(super) projects: HashMap<Option<PathBuf>, ProjectSemanticState>,
}

pub(super) struct ProjectSemanticState {
    pub(super) generation: u64,
    pub(super) dep_graph: DependencyGraph,
    pub(super) base_checker: Option<typechecker::Checker>,
    pub(super) module_names: BTreeSet<String>,
    pub(super) module_interfaces: HashMap<String, CachedModuleInterface>,
    pub(super) semantic_indexes: HashMap<String, CachedSemanticIndex>,
}

#[derive(Clone)]
pub(super) struct CachedModuleInterface {
    pub(super) path: Option<PathBuf>,
    pub(super) source_fingerprint: u64,
    pub(super) interface_fingerprint: u64,
    pub(super) exports: typechecker::ModuleExports,
    pub(super) codegen_info: Option<typechecker::ModuleCodegenInfo>,
    pub(super) check_result: Option<typechecker::CheckResult>,
}

pub(super) struct CachedSemanticIndex {
    pub(super) uri: Url,
    pub(super) index: SemanticIndex,
}

pub(super) struct ModuleInterfaceUpdate {
    pub(super) module_name: String,
    pub(super) path: Option<PathBuf>,
    pub(super) source_fingerprint: u64,
    pub(super) interface_fingerprint: u64,
    pub(super) exports: typechecker::ModuleExports,
    pub(super) codegen_info: Option<typechecker::ModuleCodegenInfo>,
    pub(super) check_result: Option<typechecker::CheckResult>,
    pub(super) is_current: bool,
}

pub(super) struct ProjectSemanticIndexUpdate {
    pub(super) module_name: String,
    pub(super) uri: Url,
    pub(super) index: SemanticIndex,
}

impl ProjectSemanticState {
    fn new() -> Self {
        Self {
            generation: 0,
            dep_graph: DependencyGraph::default(),
            base_checker: None,
            module_names: BTreeSet::new(),
            module_interfaces: HashMap::new(),
            semantic_indexes: HashMap::new(),
        }
    }
}

impl ProjectSemanticStore {
    pub(super) fn project_mut(
        &mut self,
        project_root: Option<PathBuf>,
    ) -> &mut ProjectSemanticState {
        self.projects
            .entry(project_root)
            .or_insert_with(ProjectSemanticState::new)
    }

    pub(super) fn base_checker(
        &self,
        project_root: &Option<PathBuf>,
    ) -> Option<typechecker::Checker> {
        self.projects
            .get(project_root)
            .and_then(|project| project.base_checker.clone())
    }

    pub(super) fn store_base_checker(
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

    pub(super) fn update_file(
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

    pub(super) fn dependents_of(&self, project_root: &Option<PathBuf>, uri: &Url) -> Vec<Url> {
        self.projects
            .get(project_root)
            .map(|project| project.dep_graph.dependents_of(uri))
            .unwrap_or_default()
    }

    pub(super) fn remove_file_from_all_projects(&mut self, uri: &Url) {
        let path = uri.to_file_path().ok();
        for project in self.projects.values_mut() {
            if let Some(module_name) = project.dep_graph.remove_file(uri) {
                project.module_names.remove(&module_name);
                project.module_interfaces.remove(&module_name);
                project.semantic_indexes.remove(&module_name);
            }
            project
                .semantic_indexes
                .retain(|_, cached| cached.uri != *uri);
            if let Some(path) = &path {
                project
                    .module_interfaces
                    .retain(|_, cached| cached.path.as_deref() != Some(path.as_path()));
            }
            project.generation = project.generation.saturating_add(1);
        }
    }

    pub(super) fn update_semantic_index(
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

    pub(super) fn replace_module_names(
        &mut self,
        project_root: Option<PathBuf>,
        module_names: impl IntoIterator<Item = String>,
    ) {
        let project = self.project_mut(project_root);
        project.module_names = module_names.into_iter().collect();
    }

    pub(super) fn project_type_reference_locations(
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

    pub(super) fn project_type_definition_location(
        &self,
        project_root: &Option<PathBuf>,
        type_name: &str,
    ) -> Option<Location> {
        let project = self.projects.get(project_root)?;
        project.semantic_indexes.values().find_map(|cached| {
            cached
                .index
                .type_definition_locations
                .get(type_name)
                .cloned()
        })
    }

    pub(super) fn project_symbol_reference_locations(
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

    pub(super) fn project_symbol_definition_location(
        &self,
        project_root: &Option<PathBuf>,
        key: &SemanticSymbolKey,
    ) -> Option<Location> {
        let project = self.projects.get(project_root)?;
        project
            .semantic_indexes
            .values()
            .find_map(|cached| cached.index.symbol_definition_locations.get(key).cloned())
    }

    pub(super) fn project_trait_method_signature(
        &self,
        project_root: &Option<PathBuf>,
        trait_name: &str,
        method_name: &str,
    ) -> Option<String> {
        let project = self.projects.get(project_root)?;
        project
            .module_interfaces
            .values()
            .filter_map(|entry| entry.check_result.as_ref())
            .find_map(|check| trait_method_signature_in_check(check, trait_name, method_name))
            .or_else(|| {
                project.module_interfaces.values().find_map(|entry| {
                    trait_method_signature_in_exports(&entry.exports, trait_name, method_name)
                })
            })
    }

    pub(super) fn project_effect_operation_signature(
        &self,
        project_root: &Option<PathBuf>,
        effect_name: &str,
        op_name: &str,
    ) -> Option<String> {
        let project = self.projects.get(project_root)?;
        project
            .module_interfaces
            .values()
            .filter_map(|entry| entry.check_result.as_ref())
            .find_map(|check| effect_operation_signature_in_check(check, effect_name, op_name))
            .or_else(|| {
                project.module_interfaces.values().find_map(|entry| {
                    effect_operation_signature_in_exports(&entry.exports, effect_name, op_name)
                })
            })
    }

    pub(super) fn project_module_reference_locations(
        &self,
        project_root: &Option<PathBuf>,
        module_name: &str,
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
                    .module_reference_locations_for_name(module_name, include_declaration),
            );
        }
        sort_and_dedup_locations(&mut locations);
        locations
    }

    pub(super) fn project_module_definition_location(
        &self,
        project_root: &Option<PathBuf>,
        module_name: &str,
    ) -> Option<Location> {
        let project = self.projects.get(project_root)?;
        project.semantic_indexes.values().find_map(|cached| {
            cached
                .index
                .module_definition_locations
                .get(module_name)
                .cloned()
        })
    }

    pub(super) fn seed_module_interfaces(
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
                entry.check_result.clone(),
            );
            seeded += 1;
        }
        seeded
    }

    pub(super) fn apply_module_interface_updates(
        &mut self,
        project_root: Option<PathBuf>,
        updates: Vec<ModuleInterfaceUpdate>,
    ) -> ModuleInterfaceApplyResult {
        let project = self.project_mut(project_root);
        let mut updated = 0;
        let mut current_changed = false;
        let mut saw_current = false;

        for update in updates {
            if let Some(path) = &update.path {
                let stale_modules = project
                    .module_interfaces
                    .iter()
                    .filter(|(module_name, entry)| {
                        *module_name != &update.module_name
                            && entry.path.as_deref() == Some(path.as_path())
                    })
                    .map(|(module_name, _)| module_name.clone())
                    .collect::<Vec<_>>();
                for module_name in stale_modules {
                    project.module_names.remove(&module_name);
                    project.module_interfaces.remove(&module_name);
                    project.semantic_indexes.remove(&module_name);
                }
            }
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

    pub(super) fn cached_module_source_fingerprints(
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
pub(super) struct ModuleInterfaceApplyResult {
    pub(super) updated: usize,
    pub(super) current_changed: bool,
    pub(super) saw_current: bool,
}
