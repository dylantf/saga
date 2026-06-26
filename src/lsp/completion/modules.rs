use std::collections::HashSet;
use std::path::PathBuf;

use saga::typechecker;
use tower_lsp::lsp_types::*;

use super::super::{CachedModuleInterface, ProjectSemanticStore, SemanticSnapshot};
use super::push_completion;

pub(super) fn collect_module_name_completions(
    items: &mut Vec<CompletionItem>,
    seen: &mut HashSet<String>,
    prefix: &str,
    semantic: Option<&SemanticSnapshot>,
    projects: Option<(&ProjectSemanticStore, &Option<PathBuf>)>,
    excluded_module: Option<&str>,
) {
    if let Some(semantic) = semantic {
        for module in semantic.check.module_exports().keys() {
            if excluded_module == Some(module.as_str()) {
                continue;
            }
            push_completion(
                items,
                seen,
                module,
                CompletionItemKind::MODULE,
                Some("module".to_string()),
                prefix,
            );
        }
        for name in semantic
            .check
            .scope_map
            .values
            .keys()
            .chain(semantic.check.scope_map.types.keys())
            .chain(semantic.check.scope_map.constructors.keys())
            .chain(semantic.check.scope_map.traits.keys())
            .chain(semantic.check.scope_map.effects.keys())
            .chain(semantic.check.scope_map.handlers.keys())
        {
            if let Some(module) = name.split('.').next()
                && module != name
            {
                if excluded_module == Some(module) {
                    continue;
                }
                push_completion(
                    items,
                    seen,
                    module,
                    CompletionItemKind::MODULE,
                    Some("module".to_string()),
                    prefix,
                );
            }
        }
    }
    if let Some((projects, project_root)) = projects
        && let Some(project) = projects.projects.get(project_root)
    {
        for module in project.module_names.iter() {
            if excluded_module == Some(module.as_str()) {
                continue;
            }
            push_completion(
                items,
                seen,
                module,
                CompletionItemKind::MODULE,
                Some("module".to_string()),
                prefix,
            );
        }
        for module in project
            .module_interfaces
            .keys()
            .chain(project.semantic_indexes.keys())
        {
            if excluded_module == Some(module.as_str()) {
                continue;
            }
            push_completion(
                items,
                seen,
                module,
                CompletionItemKind::MODULE,
                Some("module".to_string()),
                prefix,
            );
        }
    }
}

pub(super) fn push_module_export_completions(
    items: &mut Vec<CompletionItem>,
    seen: &mut HashSet<String>,
    prefix: &str,
    entry: &CachedModuleInterface,
    label_prefix: Option<&str>,
) {
    let fallback_sub = typechecker::Substitution::new();
    let sub = entry
        .check_result
        .as_ref()
        .map(|check| &check.sub)
        .unwrap_or(&fallback_sub);
    push_exports_completion_items(
        items,
        seen,
        prefix,
        &entry.exports,
        Some((sub, label_prefix)),
    );
}

pub(super) fn push_exports_completion_items(
    items: &mut Vec<CompletionItem>,
    seen: &mut HashSet<String>,
    prefix: &str,
    exports: &typechecker::ModuleExports,
    detail_context: Option<(&typechecker::Substitution, Option<&str>)>,
) {
    let constructor_names: HashSet<&str> = exports
        .type_constructors
        .values()
        .flat_map(|ctors| ctors.iter().map(String::as_str))
        .collect();
    for name in exports.binding_origins.keys() {
        let is_constructor = constructor_names.contains(name.as_str());
        let is_handler = exports.handler_origins.contains_key(name);
        let detail = detail_context
            .and_then(|(sub, _)| {
                exports
                    .bindings
                    .iter()
                    .find(|(binding_name, _)| binding_name == name)
                    .map(|(_, scheme)| scheme.display_with_constraints(sub))
            })
            .or_else(|| {
                Some(
                    if is_constructor {
                        "constructor"
                    } else if is_handler {
                        "handler"
                    } else {
                        "function"
                    }
                    .to_string(),
                )
            });
        push_completion(
            items,
            seen,
            completion_export_label(name, detail_context.and_then(|(_, prefix)| prefix)),
            if is_constructor {
                CompletionItemKind::CONSTRUCTOR
            } else if is_handler {
                CompletionItemKind::EVENT
            } else {
                CompletionItemKind::FUNCTION
            },
            detail,
            prefix,
        );
    }
    for name in exports.type_origins.keys() {
        push_completion(
            items,
            seen,
            completion_export_label(name, detail_context.and_then(|(_, prefix)| prefix)),
            CompletionItemKind::CLASS,
            Some("type".to_string()),
            prefix,
        );
    }
    for name in exports.trait_origins.keys() {
        push_completion(
            items,
            seen,
            completion_export_label(name, detail_context.and_then(|(_, prefix)| prefix)),
            CompletionItemKind::INTERFACE,
            Some("trait".to_string()),
            prefix,
        );
    }
    for name in exports.effect_origins.keys() {
        push_completion(
            items,
            seen,
            completion_export_label(name, detail_context.and_then(|(_, prefix)| prefix)),
            CompletionItemKind::INTERFACE,
            Some("effect".to_string()),
            prefix,
        );
    }
    for name in exports.handler_origins.keys() {
        push_completion(
            items,
            seen,
            completion_export_label(name, detail_context.and_then(|(_, prefix)| prefix)),
            CompletionItemKind::EVENT,
            Some("handler".to_string()),
            prefix,
        );
    }
}

fn completion_export_label(name: &str, label_prefix: Option<&str>) -> String {
    label_prefix
        .map(|prefix| format!("{prefix}{name}"))
        .unwrap_or_else(|| name.to_string())
}

pub(super) fn collect_qualified_completions(
    items: &mut Vec<CompletionItem>,
    seen: &mut HashSet<String>,
    prefix: &str,
    chain: &[String],
    semantic: Option<&SemanticSnapshot>,
    projects: Option<(&ProjectSemanticStore, &Option<PathBuf>)>,
) {
    let qualifier = chain.join(".");
    let qualified_prefix = format!("{qualifier}.");
    if let Some(semantic) = semantic {
        for (name, scheme) in semantic.check.env.iter() {
            if let Some(remainder) = name.strip_prefix(&qualified_prefix) {
                let next = remainder.split('.').next().unwrap_or(remainder);
                let is_module = remainder.contains('.');
                let value_kind = if semantic.check.scope_map.constructors.contains_key(name)
                    || semantic.check.constructors.contains_key(name)
                {
                    CompletionItemKind::CONSTRUCTOR
                } else if semantic.check.scope_map.handlers.contains_key(name) {
                    CompletionItemKind::EVENT
                } else {
                    CompletionItemKind::FUNCTION
                };
                push_completion(
                    items,
                    seen,
                    next,
                    if is_module {
                        CompletionItemKind::MODULE
                    } else {
                        value_kind
                    },
                    if is_module {
                        Some("module".to_string())
                    } else {
                        Some(scheme.display_with_constraints(&semantic.check.sub))
                    },
                    prefix,
                );
            }
        }
        for (visible, canonical) in semantic
            .check
            .scope_map
            .values
            .iter()
            .chain(semantic.check.scope_map.constructors.iter())
            .chain(semantic.check.scope_map.types.iter())
            .chain(semantic.check.scope_map.traits.iter())
            .chain(semantic.check.scope_map.effects.iter())
            .chain(semantic.check.scope_map.handlers.iter())
        {
            if let Some(remainder) = visible.strip_prefix(&qualified_prefix) {
                let next = remainder.split('.').next().unwrap_or(remainder);
                let is_module = remainder.contains('.');
                let kind = if is_module {
                    CompletionItemKind::MODULE
                } else if semantic.check.scope_map.types.contains_key(visible) {
                    CompletionItemKind::CLASS
                } else if semantic.check.scope_map.constructors.contains_key(visible) {
                    CompletionItemKind::CONSTRUCTOR
                } else if semantic.check.scope_map.traits.contains_key(visible)
                    || semantic.check.scope_map.effects.contains_key(visible)
                {
                    CompletionItemKind::INTERFACE
                } else if semantic.check.scope_map.handlers.contains_key(visible) {
                    CompletionItemKind::EVENT
                } else {
                    CompletionItemKind::FUNCTION
                };
                push_completion(items, seen, next, kind, Some(canonical.clone()), prefix);
            }
        }
        if let Some(effect_name) = semantic.check.scope_map.resolve_effect(&qualifier)
            && let Some(effect) = semantic.check.effects.get(effect_name)
        {
            for op in &effect.ops {
                push_completion(
                    items,
                    seen,
                    &op.name,
                    CompletionItemKind::METHOD,
                    typechecker::effect_operation_signature_from_info(
                        effect_name,
                        effect,
                        &op.name,
                    ),
                    prefix,
                );
            }
        }
    }
    if let Some((projects, project_root)) = projects
        && let Some(project) = projects.projects.get(project_root)
    {
        for (module, entry) in &project.module_interfaces {
            if let Some(remainder) = module.strip_prefix(&qualified_prefix) {
                let next = remainder.split('.').next().unwrap_or(remainder);
                push_completion(
                    items,
                    seen,
                    next,
                    CompletionItemKind::MODULE,
                    Some("module".to_string()),
                    prefix,
                );
            }
            if module == &qualifier {
                push_module_export_completions(items, seen, prefix, entry, None);
            }
        }
    }
}
