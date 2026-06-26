use std::collections::HashSet;
use std::path::PathBuf;

use saga::{ast, typechecker};
use tower_lsp::lsp_types::*;

use super::text::{LineIndex, clamp_to_char_boundary, extract_prefix, source_text_at};
use super::{
    DocumentState, ParseSnapshot, ProjectSemanticStore, SemanticSnapshot, extract_module_info,
};

mod modules;
mod records;

use modules::{
    collect_module_name_completions, collect_qualified_completions, push_exports_completion_items,
    push_module_export_completions,
};
use records::{push_record_field_completions, record_fields_for_chain, record_fields_for_name};
#[derive(Clone, Debug, PartialEq, Eq)]
enum CompletionContext {
    ImportModule,
    ImportExposing { module_name: String },
    DotAccess { chain: Vec<String>, prefix: String },
    RecordFields { record_name: String },
    Type,
    Trait,
    Effect,
    Handler,
    Expression,
}

fn completion_context(source: &str, offset: usize) -> CompletionContext {
    let line_start = source[..offset].rfind('\n').map(|i| i + 1).unwrap_or(0);
    let line_before = &source[line_start..offset];
    let trimmed = line_before.trim_start();

    if trimmed.starts_with("import ") {
        if let Some(module_name) = import_exposing_context(line_before) {
            return CompletionContext::ImportExposing { module_name };
        }
        return CompletionContext::ImportModule;
    }
    if let Some((chain, prefix)) = dot_completion_context(source, offset) {
        return CompletionContext::DotAccess { chain, prefix };
    }
    if let Some(record_name) = record_field_completion_context(source, offset) {
        return CompletionContext::RecordFields { record_name };
    }
    if recently_opened_row(line_before, "needs") {
        return CompletionContext::Effect;
    }
    if recently_opened_row(line_before, "with") || trimmed.starts_with("with ") {
        return CompletionContext::Handler;
    }
    if trimmed.starts_with("impl ")
        || line_before.rsplit_once(':').is_some_and(|(left, _)| {
            left.rsplit_once('{').is_some_and(|(_, row)| {
                row.contains("where")
                    || row
                        .chars()
                        .all(|c| c.is_alphanumeric() || c.is_whitespace())
            })
        })
    {
        return CompletionContext::Trait;
    }
    if line_before.contains(':') || line_before.contains("->") {
        return CompletionContext::Type;
    }

    CompletionContext::Expression
}

fn recently_opened_row(line_before: &str, keyword: &str) -> bool {
    let Some(keyword_pos) = line_before.rfind(keyword) else {
        return false;
    };
    let after_keyword = &line_before[keyword_pos + keyword.len()..];
    after_keyword.contains('{') && !after_keyword.contains('}')
}

fn dot_completion_context(source: &str, offset: usize) -> Option<(Vec<String>, String)> {
    let before = &source[..offset];
    let start = before
        .rfind(|c: char| !c.is_alphanumeric() && c != '_' && c != '\'' && c != '.')
        .map(|i| i + 1)
        .unwrap_or(0);
    let token = &before[start..];
    let dot = token.rfind('.')?;
    let chain: Vec<String> = token[..dot]
        .split('.')
        .filter(|part| !part.is_empty())
        .map(ToString::to_string)
        .collect();
    if chain.is_empty() {
        return None;
    }
    Some((chain, token[dot + 1..].to_string()))
}

fn record_field_completion_context(source: &str, offset: usize) -> Option<String> {
    let prefix = extract_prefix(source, offset);
    let mut depth = 0usize;
    let mut brace_pos = None;
    for (idx, ch) in source[..offset - prefix.len()].char_indices().rev() {
        match ch {
            '}' => depth = depth.saturating_add(1),
            '{' if depth == 0 => {
                brace_pos = Some(idx);
                break;
            }
            '{' => depth = depth.saturating_sub(1),
            _ => {}
        }
    }
    let brace_pos = brace_pos?;
    let before_brace = source[..brace_pos].trim_end();
    let name_end = before_brace.len();
    let name_start = before_brace
        .rfind(|c: char| !c.is_alphanumeric() && c != '_' && c != '.')
        .map(|i| i + 1)
        .unwrap_or(0);
    let name = &before_brace[name_start..name_end];
    name.chars()
        .next()
        .is_some_and(|c| c.is_uppercase())
        .then(|| name.to_string())
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

fn completion_prefix_for_context<'a>(
    source: &'a str,
    offset: usize,
    context: &'a CompletionContext,
) -> &'a str {
    match context {
        CompletionContext::DotAccess { prefix, .. } => prefix.as_str(),
        CompletionContext::ImportModule => import_completion_prefix(source, offset),
        CompletionContext::ImportExposing { .. } => extract_prefix(source, offset),
        _ => extract_prefix(source, offset),
    }
}

fn import_exposing_context(line_before: &str) -> Option<String> {
    let trimmed = line_before.trim_start();
    let rest = trimmed.strip_prefix("import ")?;
    let lparen = rest.rfind('(')?;
    let after_lparen = &rest[lparen + 1..];
    if after_lparen.contains(')') {
        return None;
    }
    let before_lparen = rest[..lparen].trim_end();
    let module_name = before_lparen.split_whitespace().next()?;
    (!module_name.is_empty()).then(|| module_name.to_string())
}

fn import_completion_prefix(source: &str, offset: usize) -> &str {
    let offset = clamp_to_char_boundary(source, offset.min(source.len()));
    let line_start = source[..offset].rfind('\n').map(|i| i + 1).unwrap_or(0);
    let line_before = &source[line_start..offset];
    let trimmed_start_len = line_before.len() - line_before.trim_start().len();
    let trimmed = &line_before[trimmed_start_len..];
    let Some(rest) = trimmed.strip_prefix("import ") else {
        return extract_prefix(source, offset);
    };
    rest.trim_start()
}

fn import_completion_replacement_range(
    source: &str,
    offset: usize,
    line_index: &LineIndex,
) -> Range {
    let offset = clamp_to_char_boundary(source, offset.min(source.len()));
    let line_start = source[..offset].rfind('\n').map(|i| i + 1).unwrap_or(0);
    let line_before = &source[line_start..offset];
    let trimmed_start_len = line_before.len() - line_before.trim_start().len();
    let trimmed = &line_before[trimmed_start_len..];
    let prefix_start = trimmed
        .strip_prefix("import ")
        .map(|rest| {
            line_start
                + trimmed_start_len
                + "import ".len()
                + (rest.len() - rest.trim_start().len())
        })
        .unwrap_or_else(|| offset.saturating_sub(extract_prefix(source, offset).len()));
    Range {
        start: line_index.offset_to_position(prefix_start, source),
        end: line_index.offset_to_position(offset, source),
    }
}

fn push_completion(
    items: &mut Vec<CompletionItem>,
    seen: &mut HashSet<String>,
    label: impl Into<String>,
    kind: CompletionItemKind,
    detail: Option<String>,
    prefix: &str,
) {
    let label = label.into();
    if !prefix.is_empty() && !label.to_lowercase().starts_with(&prefix.to_lowercase()) {
        return;
    }
    if seen.insert(label.clone()) {
        items.push(CompletionItem {
            label,
            kind: Some(kind),
            detail,
            ..Default::default()
        });
    }
}

fn apply_completion_text_edit(items: &mut [CompletionItem], range: Range) {
    for item in items {
        item.text_edit = Some(CompletionTextEdit::Edit(TextEdit {
            range,
            new_text: item.label.clone(),
        }));
    }
}

pub(super) fn collect_completion_items(
    document: &DocumentState,
    position: Position,
    projects: Option<(&ProjectSemanticStore, &Option<PathBuf>)>,
) -> Vec<CompletionItem> {
    let line_index = LineIndex::new(&document.text);
    let offset = line_index.position_to_offset(position, &document.text);
    let context = completion_context(&document.text, offset);
    let prefix = completion_prefix_for_context(&document.text, offset, &context);
    let current_module = document
        .parse
        .as_deref()
        .and_then(|parse| extract_module_info(&parse.program).0);
    let mut items = Vec::new();
    let mut seen = HashSet::new();

    let semantic = document
        .semantic
        .as_deref()
        .filter(|semantic| semantic.version == document.version);

    match &context {
        CompletionContext::ImportModule => {
            collect_module_name_completions(
                &mut items,
                &mut seen,
                prefix,
                semantic,
                projects,
                current_module.as_deref(),
            );
            let replace_range =
                import_completion_replacement_range(&document.text, offset, &line_index);
            apply_completion_text_edit(&mut items, replace_range);
        }
        CompletionContext::ImportExposing { module_name } => {
            collect_import_exposing_completions(
                &mut items,
                &mut seen,
                prefix,
                module_name,
                semantic,
                projects,
            );
        }
        CompletionContext::DotAccess { chain, .. } => {
            if let Some(semantic) = semantic
                && let Some(fields) =
                    record_fields_for_chain(&semantic.check, chain, &semantic.source)
            {
                push_record_field_completions(&mut items, &mut seen, prefix, fields);
            }
            collect_qualified_completions(&mut items, &mut seen, prefix, chain, semantic, projects);
        }
        CompletionContext::RecordFields { record_name } => {
            if let Some(semantic) = semantic
                && let Some(fields) = record_fields_for_name(&semantic.check, record_name)
            {
                push_record_field_completions(&mut items, &mut seen, prefix, fields);
            }
        }
        CompletionContext::Type => {
            collect_type_completions(&mut items, &mut seen, prefix, semantic, projects);
        }
        CompletionContext::Trait => {
            collect_trait_completions(&mut items, &mut seen, prefix, semantic, projects);
        }
        CompletionContext::Effect => {
            collect_effect_completions(&mut items, &mut seen, prefix, semantic, projects);
        }
        CompletionContext::Handler => {
            collect_handler_completions(&mut items, &mut seen, prefix, semantic, projects);
        }
        CompletionContext::Expression => {
            collect_keyword_completions(&mut items, &mut seen, prefix);
            collect_syntax_completion_items(&mut items, &mut seen, prefix, document);
            if let Some(semantic) = semantic {
                if let Some(parse) = document
                    .parse
                    .as_deref()
                    .filter(|parse| parse.version == document.version)
                {
                    collect_local_semantic_completions(
                        &mut items, &mut seen, prefix, parse, semantic, offset,
                    );
                }
                collect_expression_semantic_completions(
                    &mut items, &mut seen, prefix, semantic, projects,
                );
            }
        }
    }

    items.sort_by(|a, b| a.label.cmp(&b.label));
    items
}

fn collect_import_exposing_completions(
    items: &mut Vec<CompletionItem>,
    seen: &mut HashSet<String>,
    prefix: &str,
    module_name: &str,
    semantic: Option<&SemanticSnapshot>,
    projects: Option<(&ProjectSemanticStore, &Option<PathBuf>)>,
) {
    if let Some((projects, project_root)) = projects
        && let Some(project) = projects.projects.get(project_root)
        && let Some(entry) = project.module_interfaces.get(module_name)
    {
        push_module_export_completions(items, seen, prefix, entry, None);
        return;
    }
    if let Some(semantic) = semantic
        && let Some(exports) = semantic.check.module_exports().get(module_name)
    {
        push_exports_completion_items(
            items,
            seen,
            prefix,
            exports,
            Some((&semantic.check.sub, None)),
        );
    }
}

fn collect_local_semantic_completions(
    items: &mut Vec<CompletionItem>,
    seen: &mut HashSet<String>,
    prefix: &str,
    parse: &ParseSnapshot,
    semantic: &SemanticSnapshot,
    offset: usize,
) {
    let Some((decl_span, excluded_name_span)) = containing_value_decl(&parse.program, offset)
    else {
        return;
    };
    for node_id in semantic.semantic_index.definition_locations.keys() {
        let Some(span) = semantic.check.node_spans.get(node_id) else {
            continue;
        };
        if span.start < decl_span.start
            || span.end > decl_span.end
            || span.start >= offset
            || excluded_name_span
                .as_ref()
                .is_some_and(|excluded| excluded.start == span.start && excluded.end == span.end)
        {
            continue;
        }
        let name = source_text_at(&semantic.source, *span);
        if name.is_empty()
            || name.contains('.')
            || name
                .chars()
                .next()
                .is_some_and(|ch| ch.is_uppercase() || ch == '_')
        {
            continue;
        }
        push_completion(
            items,
            seen,
            name,
            CompletionItemKind::VARIABLE,
            semantic.check.type_at_node(node_id),
            prefix,
        );
    }
}

fn containing_value_decl(
    program: &ast::Program,
    offset: usize,
) -> Option<(saga::token::Span, Option<saga::token::Span>)> {
    program.iter().find_map(|decl| match decl {
        ast::Decl::FunBinding {
            name_span, span, ..
        }
        | ast::Decl::Let {
            name_span, span, ..
        } if span.start <= offset && offset <= span.end => Some((*span, Some(*name_span))),
        _ => None,
    })
}

fn collect_keyword_completions(
    items: &mut Vec<CompletionItem>,
    seen: &mut HashSet<String>,
    prefix: &str,
) {
    let keywords = [
        "if", "then", "else", "case", "let", "fun", "type", "record", "effect", "handler", "with",
        "import", "module", "pub", "opaque", "trait", "impl", "where", "needs", "receive", "do",
        "assert",
    ];
    for keyword in keywords {
        push_completion(
            items,
            seen,
            keyword,
            CompletionItemKind::KEYWORD,
            None,
            prefix,
        );
    }
}

fn collect_syntax_completion_items(
    items: &mut Vec<CompletionItem>,
    seen: &mut HashSet<String>,
    prefix: &str,
    document: &DocumentState,
) {
    for (name, kind) in top_level_completion_names(document.parse.as_deref()) {
        push_completion(items, seen, name, kind, None, prefix);
    }
}

fn collect_expression_semantic_completions(
    items: &mut Vec<CompletionItem>,
    seen: &mut HashSet<String>,
    prefix: &str,
    semantic: &SemanticSnapshot,
    projects: Option<(&ProjectSemanticStore, &Option<PathBuf>)>,
) {
    for (name, scheme) in semantic.check.env.iter() {
        if name.starts_with("__") || name.contains('.') {
            continue;
        }
        push_completion(
            items,
            seen,
            name,
            CompletionItemKind::FUNCTION,
            Some(scheme.display_with_constraints(&semantic.check.sub)),
            prefix,
        );
    }
    for (name, scheme) in &semantic.check.constructors {
        if name.contains('.') || matches!(name.as_str(), "Cons" | "Nil") {
            continue;
        }
        push_completion(
            items,
            seen,
            name,
            CompletionItemKind::CONSTRUCTOR,
            Some(scheme.display_with_constraints(&semantic.check.sub)),
            prefix,
        );
    }
    collect_handler_completions(items, seen, prefix, Some(semantic), projects);
    collect_module_name_completions(items, seen, prefix, Some(semantic), projects, None);
}

fn collect_type_completions(
    items: &mut Vec<CompletionItem>,
    seen: &mut HashSet<String>,
    prefix: &str,
    semantic: Option<&SemanticSnapshot>,
    projects: Option<(&ProjectSemanticStore, &Option<PathBuf>)>,
) {
    for builtin in [
        "Int",
        "Float",
        "String",
        "Bool",
        "Unit",
        "List",
        "Maybe",
        "Result",
        "Tuple",
        "Pid",
        "Dict",
        "Set",
        "BitString",
    ] {
        push_completion(
            items,
            seen,
            builtin,
            CompletionItemKind::CLASS,
            Some("type".to_string()),
            prefix,
        );
    }
    if let Some(semantic) = semantic {
        for name in semantic.check.scope_map.types.keys() {
            if name.contains('.') {
                continue;
            }
            push_completion(
                items,
                seen,
                name,
                CompletionItemKind::CLASS,
                Some("type".to_string()),
                prefix,
            );
        }
        for name in semantic.check.records.keys() {
            push_completion(
                items,
                seen,
                typechecker::bare_type_name(name),
                CompletionItemKind::CLASS,
                Some("record".to_string()),
                prefix,
            );
        }
    }
    if let Some((projects, project_root)) = projects
        && let Some(project) = projects.projects.get(project_root)
    {
        for entry in project.module_interfaces.values() {
            for name in entry.exports.type_origins.keys() {
                push_completion(
                    items,
                    seen,
                    name,
                    CompletionItemKind::CLASS,
                    Some("type".to_string()),
                    prefix,
                );
            }
        }
    }
}

fn collect_trait_completions(
    items: &mut Vec<CompletionItem>,
    seen: &mut HashSet<String>,
    prefix: &str,
    semantic: Option<&SemanticSnapshot>,
    projects: Option<(&ProjectSemanticStore, &Option<PathBuf>)>,
) {
    if let Some(semantic) = semantic {
        for name in semantic.check.scope_map.traits.keys() {
            if name.contains('.') {
                continue;
            }
            push_completion(
                items,
                seen,
                name,
                CompletionItemKind::INTERFACE,
                Some("trait".to_string()),
                prefix,
            );
        }
    }
    if let Some((projects, project_root)) = projects
        && let Some(project) = projects.projects.get(project_root)
    {
        for entry in project.module_interfaces.values() {
            for name in entry.exports.trait_origins.keys() {
                push_completion(
                    items,
                    seen,
                    name,
                    CompletionItemKind::INTERFACE,
                    Some("trait".to_string()),
                    prefix,
                );
            }
        }
    }
}

fn collect_effect_completions(
    items: &mut Vec<CompletionItem>,
    seen: &mut HashSet<String>,
    prefix: &str,
    semantic: Option<&SemanticSnapshot>,
    projects: Option<(&ProjectSemanticStore, &Option<PathBuf>)>,
) {
    if let Some(semantic) = semantic {
        for name in semantic.check.scope_map.effects.keys() {
            if name.contains('.') {
                continue;
            }
            push_completion(
                items,
                seen,
                name,
                CompletionItemKind::INTERFACE,
                Some("effect".to_string()),
                prefix,
            );
        }
    }
    if let Some((projects, project_root)) = projects
        && let Some(project) = projects.projects.get(project_root)
    {
        for entry in project.module_interfaces.values() {
            for name in entry.exports.effect_origins.keys() {
                push_completion(
                    items,
                    seen,
                    name,
                    CompletionItemKind::INTERFACE,
                    Some("effect".to_string()),
                    prefix,
                );
            }
        }
    }
}

fn collect_handler_completions(
    items: &mut Vec<CompletionItem>,
    seen: &mut HashSet<String>,
    prefix: &str,
    semantic: Option<&SemanticSnapshot>,
    projects: Option<(&ProjectSemanticStore, &Option<PathBuf>)>,
) {
    if let Some(semantic) = semantic {
        for name in semantic.check.scope_map.handlers.keys() {
            if name.contains('.') {
                continue;
            }
            push_completion(
                items,
                seen,
                name,
                CompletionItemKind::EVENT,
                Some("handler".to_string()),
                prefix,
            );
        }
    }
    if let Some((projects, project_root)) = projects
        && let Some(project) = projects.projects.get(project_root)
    {
        for entry in project.module_interfaces.values() {
            for name in entry.exports.handler_origins.keys() {
                push_completion(
                    items,
                    seen,
                    name,
                    CompletionItemKind::EVENT,
                    Some("handler".to_string()),
                    prefix,
                );
            }
        }
    }
}
