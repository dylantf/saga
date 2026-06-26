use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use saga::{ast, typechecker};
use tower_lsp::lsp_types::*;

use super::semantic::SemanticIndex;
use super::semantic_symbols::add_program_type_symbols;
use super::semantic_values::{
    collect_value_definition_nodes, collect_value_definition_nodes_into,
    semantic_value_references_for_program,
};
use super::text::{LineIndex, span_to_range};
use super::{CachedDefinitionSources, extract_module_info};

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

pub(super) fn build_semantic_index(
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
