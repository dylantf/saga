use std::path::PathBuf;

use saga::{ast, typechecker};
use tower_lsp::lsp_types::*;

use super::navigation::smallest_node_at_offset;
use super::semantic::{SemanticDocKey, SemanticSymbolKind, member_symbol_name};
use super::text::{source_text_at, span_to_range};
use super::{ProjectSemanticStore, SemanticSnapshot, SemanticSymbolKey};

fn docs_markdown(docs: &[String]) -> String {
    docs.join("\n")
}

fn hover_markdown(docs: Option<&[String]>, code: Option<String>) -> String {
    match (docs, code) {
        (Some(docs), Some(code)) if !docs.is_empty() => {
            format!("{}\n\n```saga\n{code}\n```", docs_markdown(docs))
        }
        (_, Some(code)) => format!("```saga\n{code}\n```"),
        (Some(docs), None) => docs_markdown(docs),
        (None, None) => String::new(),
    }
}

pub(super) fn trait_method_signature_in_check(
    check: &typechecker::CheckResult,
    trait_name: &str,
    method_name: &str,
) -> Option<String> {
    check
        .trait_method_signature(trait_name, method_name)
        .or_else(|| {
            check
                .module_check_results()
                .values()
                .find_map(|module_result| {
                    trait_method_signature_in_check(module_result, trait_name, method_name)
                })
        })
}

pub(super) fn trait_method_signature_in_exports(
    exports: &typechecker::ModuleExports,
    trait_name: &str,
    method_name: &str,
) -> Option<String> {
    exports.traits.iter().find_map(|(surface_name, info)| {
        let origin = exports
            .trait_origins
            .get(surface_name)
            .map(String::as_str)
            .unwrap_or(surface_name);
        (origin == trait_name || surface_name == trait_name)
            .then(|| typechecker::trait_method_signature_from_info(origin, info, method_name))
            .flatten()
    })
}

pub(super) fn effect_operation_signature_in_check(
    check: &typechecker::CheckResult,
    effect_name: &str,
    op_name: &str,
) -> Option<String> {
    check
        .effect_operation_signature(effect_name, op_name)
        .or_else(|| {
            check
                .module_check_results()
                .values()
                .find_map(|module_result| {
                    effect_operation_signature_in_check(module_result, effect_name, op_name)
                })
        })
}

pub(super) fn effect_operation_signature_in_exports(
    exports: &typechecker::ModuleExports,
    effect_name: &str,
    op_name: &str,
) -> Option<String> {
    exports.effects.iter().find_map(|(surface_name, info)| {
        let origin = exports
            .effect_origins
            .get(surface_name)
            .map(String::as_str)
            .unwrap_or(surface_name);
        (origin == effect_name || surface_name == effect_name)
            .then(|| typechecker::effect_operation_signature_from_info(origin, info, op_name))
            .flatten()
    })
}

pub(super) fn hover_type_at(
    uri: &Url,
    semantic: &SemanticSnapshot,
    position: Position,
    project_signatures: Option<(&ProjectSemanticStore, &Option<PathBuf>)>,
) -> Option<Hover> {
    if let Some(hover) = hover_semantic_symbol_at(uri, semantic, position, project_signatures) {
        return Some(hover);
    }
    if let Some(docs) = semantic.semantic_index.type_doc_at_position(uri, position) {
        return Some(Hover {
            contents: HoverContents::Markup(MarkupContent {
                kind: MarkupKind::Markdown,
                value: hover_markdown(Some(docs), None),
            }),
            range: None,
        });
    }

    let offset = semantic
        .line_index
        .position_to_offset(position, &semantic.source);
    let mut best: Option<(saga::token::Span, String, Option<ast::NodeId>)> = None;

    for span in semantic.check.type_at_span.keys() {
        if offset >= span.start
            && offset <= span.end
            && let Some(type_str) = semantic.check.type_at_span(span)
        {
            let replace = best.as_ref().is_none_or(|(best_span, _, _)| {
                span.end - span.start < best_span.end - best_span.start
            });
            if replace {
                best = Some((*span, type_str, None));
            }
        }
    }

    for (node_id, span) in &semantic.check.node_spans {
        if offset >= span.start
            && offset <= span.end
            && let Some(type_str) = semantic.check.type_at_node(node_id)
        {
            let replace = best.as_ref().is_none_or(|(best_span, _, _)| {
                span.end - span.start < best_span.end - best_span.start
            });
            if replace {
                best = Some((*span, type_str, Some(*node_id)));
            }
        }
    }

    let (span, type_str, node_id) = best?;
    let name = source_text_at(&semantic.source, span);
    let code = if name.is_empty() {
        type_str
    } else {
        format!("{name}: {type_str}")
    };
    let docs = node_id.and_then(|node_id| semantic.semantic_index.value_doc_for_node(node_id));

    Some(Hover {
        contents: HoverContents::Markup(MarkupContent {
            kind: MarkupKind::Markdown,
            value: hover_markdown(docs, Some(code)),
        }),
        range: Some(span_to_range(&span, &semantic.line_index, &semantic.source)),
    })
}

fn hover_semantic_symbol_at(
    uri: &Url,
    semantic: &SemanticSnapshot,
    position: Position,
    project_signatures: Option<(&ProjectSemanticStore, &Option<PathBuf>)>,
) -> Option<Hover> {
    let (key, range) = if let Some(occurrence) = semantic
        .semantic_index
        .symbol_location_at_position(uri, position)
    {
        (occurrence.key.clone(), occurrence.location.range)
    } else {
        let offset = semantic
            .line_index
            .position_to_offset(position, &semantic.source);
        let (node_id, span) = smallest_node_at_offset(&semantic.check.node_spans, offset)?;
        let (trait_name, method_name) = semantic.check.resolved_trait_method_for_node(node_id)?;
        (
            SemanticSymbolKey {
                kind: SemanticSymbolKind::TraitMethod,
                name: member_symbol_name(trait_name, method_name),
            },
            span_to_range(&span, &semantic.line_index, &semantic.source),
        )
    };
    let docs = semantic
        .semantic_index
        .docs_by_key
        .get(&SemanticDocKey::Symbol(key.clone()))
        .map(Vec::as_slice);
    let signature = match key.kind {
        SemanticSymbolKind::TraitMethod => key.name.rsplit_once('.').and_then(|(owner, member)| {
            trait_method_signature_in_check(&semantic.check, owner, member).or_else(|| {
                project_signatures.and_then(|(projects, project_root)| {
                    projects.project_trait_method_signature(project_root, owner, member)
                })
            })
        }),
        SemanticSymbolKind::EffectOperation => {
            key.name.rsplit_once('.').and_then(|(owner, member)| {
                effect_operation_signature_in_check(&semantic.check, owner, member).or_else(|| {
                    project_signatures.and_then(|(projects, project_root)| {
                        projects.project_effect_operation_signature(project_root, owner, member)
                    })
                })
            })
        }
        SemanticSymbolKind::Module
        | SemanticSymbolKind::Trait
        | SemanticSymbolKind::Effect
        | SemanticSymbolKind::Handler => None,
    };
    let value = hover_markdown(docs, signature);
    if value.is_empty() {
        return None;
    }

    Some(Hover {
        contents: HoverContents::Markup(MarkupContent {
            kind: MarkupKind::Markdown,
            value,
        }),
        range: Some(range),
    })
}
