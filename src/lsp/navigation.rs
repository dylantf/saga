use std::collections::HashMap;

use saga::ast;
use tower_lsp::lsp_types::*;

use super::text::span_to_range;
use super::{SemanticSnapshot, SemanticSymbolKey};

pub(super) fn smallest_node_at_offset(
    node_spans: &HashMap<ast::NodeId, saga::token::Span>,
    offset: usize,
) -> Option<(ast::NodeId, saga::token::Span)> {
    node_spans
        .iter()
        .filter(|(_, span)| offset >= span.start && offset <= span.end)
        .min_by_key(|(_, span)| span.end.saturating_sub(span.start))
        .map(|(id, span)| (*id, *span))
}

pub(super) fn local_definition_at(
    uri: &Url,
    semantic: &SemanticSnapshot,
    position: Position,
) -> Option<Location> {
    if let Some(location) = semantic
        .semantic_index
        .module_definition_location_at(uri, position)
    {
        return Some(location);
    }
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

pub(super) fn references_at(
    uri: &Url,
    semantic: &SemanticSnapshot,
    position: Position,
    include_declaration: bool,
) -> Vec<Location> {
    if let Some(locations) =
        semantic
            .semantic_index
            .module_reference_locations_at(uri, position, include_declaration)
    {
        return locations;
    }
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

#[derive(Clone)]
pub(super) enum RenameTarget {
    Module(String),
    Type(String),
    Symbol(SemanticSymbolKey),
    Value(ast::NodeId),
}

pub(super) fn rename_target_at(
    uri: &Url,
    semantic: &SemanticSnapshot,
    position: Position,
) -> Option<(RenameTarget, Range)> {
    if let Some(occurrence) = semantic
        .semantic_index
        .module_occurrence_at_position(uri, position)
    {
        return Some((
            RenameTarget::Module(occurrence.name.clone()),
            occurrence.location.range,
        ));
    }
    if let Some(occurrence) = semantic
        .semantic_index
        .type_occurrence_at_position(uri, position)
    {
        return Some((
            RenameTarget::Type(occurrence.name.clone()),
            occurrence.location.range,
        ));
    }
    if let Some(occurrence) = semantic
        .semantic_index
        .symbol_location_at_position(uri, position)
    {
        return Some((
            RenameTarget::Symbol(occurrence.key.clone()),
            occurrence.location.range,
        ));
    }

    let offset = semantic
        .line_index
        .position_to_offset(position, &semantic.source);
    let (node_id, span) = smallest_node_at_offset(&semantic.check.node_spans, offset)?;
    let definition_id = semantic.semantic_index.identity_for_node(node_id);
    Some((
        RenameTarget::Value(definition_id),
        span_to_range(&span, &semantic.line_index, &semantic.source),
    ))
}

pub(super) fn valid_rename_name(new_name: &str, target: &RenameTarget) -> bool {
    match target {
        RenameTarget::Module(_) => new_name
            .split('.')
            .all(|segment| !segment.is_empty() && valid_identifier(segment)),
        RenameTarget::Type(_) | RenameTarget::Symbol(_) | RenameTarget::Value(_) => {
            valid_identifier(new_name)
        }
    }
}

fn valid_identifier(name: &str) -> bool {
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    (first.is_ascii_alphabetic() || first == '_')
        && chars.all(|ch| ch.is_ascii_alphanumeric() || ch == '_')
}

pub(super) fn workspace_edit_from_locations(
    locations: Vec<Location>,
    new_name: String,
) -> Option<WorkspaceEdit> {
    if locations.is_empty() {
        return None;
    }
    let mut changes: HashMap<Url, Vec<TextEdit>> = HashMap::new();
    for location in locations {
        changes
            .entry(location.uri)
            .or_default()
            .push(TextEdit::new(location.range, new_name.clone()));
    }
    for edits in changes.values_mut() {
        edits.sort_by(|a, b| {
            a.range
                .start
                .line
                .cmp(&b.range.start.line)
                .then_with(|| a.range.start.character.cmp(&b.range.start.character))
                .then_with(|| a.range.end.line.cmp(&b.range.end.line))
                .then_with(|| a.range.end.character.cmp(&b.range.end.character))
        });
    }
    Some(WorkspaceEdit::new(changes))
}
