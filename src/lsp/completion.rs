use std::collections::HashSet;

use tower_lsp::lsp_types::*;

use dylang::ast::Decl;
use dylang::typechecker::{CheckResult, Type};

/// Extract the identifier prefix at the cursor position by scanning backwards.
pub fn extract_prefix(source: &str, offset: usize) -> &str {
    let before = &source[..offset.min(source.len())];
    let start = before
        .rfind(|c: char| !c.is_alphanumeric() && c != '_' && c != '\'')
        .map(|i| i + 1)
        .unwrap_or(0);
    &before[start..]
}

/// Extract the full dot-access chain before the cursor.
/// e.g. for `house.address.` returns `["house", "address"]`
/// e.g. for `house.address.str` returns `["house", "address"]` (prefix "str" is excluded)
/// e.g. for `house.` returns `["house"]`
pub fn extract_dot_chain(source: &str, offset: usize) -> Option<Vec<String>> {
    let prefix = extract_prefix(source, offset);
    let mut pos = offset - prefix.len();

    // Must have at least one dot
    if pos == 0 || !source[..pos].ends_with('.') {
        return None;
    }

    let mut chain = Vec::new();
    loop {
        if pos == 0 || !source[..pos].ends_with('.') {
            break;
        }
        // Skip the dot
        pos -= 1;
        // Extract the identifier before this dot
        let before = &source[..pos];
        let start = before
            .rfind(|c: char| !c.is_alphanumeric() && c != '_' && c != '\'')
            .map(|i| i + 1)
            .unwrap_or(0);
        let ident = &before[start..];
        if ident.is_empty() {
            break;
        }
        chain.push(ident.to_string());
        pos = start;
    }

    if chain.is_empty() {
        return None;
    }
    chain.reverse();
    Some(chain)
}

/// Extract record fields from a type, supporting both named records (via `records` map)
/// and anonymous/inline records (`Type::Record`).
fn extract_record_fields(result: &CheckResult, ty: &Type) -> Option<Vec<(String, Type)>> {
    match ty {
        Type::Con(name, _) => {
            let info = result.records.get(name.as_str())?;
            Some(info.fields.clone())
        }
        Type::Record(fields) => Some(fields.clone()),
        _ => None,
    }
}

/// Resolve a receiver name to its record fields, checking multiple type sources.
fn resolve_record_fields(
    result: &CheckResult,
    receiver: &str,
    source: &str,
) -> Option<Vec<(String, Type)>> {
    // 1. Check top-level env (top-level let bindings, functions)
    if let Some(scheme) = result.env.get(receiver) {
        let ty = result.sub.apply(&scheme.ty);
        if let Some(fields) = extract_record_fields(result, &ty) {
            return Some(fields);
        }
    }

    // 2. Check per-span types (local let bindings, pattern bindings, params).
    for (span, ty) in &result.type_at_span {
        if span.end <= source.len() && &source[span.start..span.end] == receiver {
            let resolved = result.sub.apply(ty);
            if let Some(fields) = extract_record_fields(result, &resolved) {
                return Some(fields);
            }
        }
    }

    // 3. Check per-node types (expression nodes, e.g. Var references).
    for (node_id, ty) in &result.type_at_node {
        if let Some(span) = result.node_spans.get(node_id)
            && span.end <= source.len()
            && &source[span.start..span.end] == receiver
        {
            let resolved = result.sub.apply(ty);
            if let Some(fields) = extract_record_fields(result, &resolved) {
                return Some(fields);
            }
        }
    }

    None
}

/// Collect field completion items for a record receiver.
/// Supports chained access (e.g. `house.address.`).
/// `chain` is the list of identifiers before the final dot (e.g. `["house", "address"]`).
/// Returns None if the receiver's type is not a record.
pub fn collect_field_completions(
    result: &CheckResult,
    chain: &[String],
    prefix: &str,
    source: &str,
) -> Option<Vec<CompletionItem>> {
    if chain.is_empty() {
        return None;
    }

    // Resolve the root variable to its fields.
    let mut fields = resolve_record_fields(result, &chain[0], source)?;

    // Walk the chain: for each subsequent segment, find the field and resolve its type.
    for segment in &chain[1..] {
        let (_, field_ty) = fields.iter().find(|(name, _)| name == segment)?;
        let resolved = result.sub.apply(field_ty);
        fields = extract_record_fields(result, &resolved)?;
    }

    let prefix_lower = prefix.to_lowercase();
    let mut items = Vec::new();
    for (field_name, field_type) in &fields {
        if !prefix.is_empty() && !field_name.to_lowercase().starts_with(&prefix_lower) {
            continue;
        }
        let resolved_type = result.sub.apply(field_type);
        items.push(CompletionItem {
            label: field_name.clone(),
            kind: Some(CompletionItemKind::FIELD),
            detail: Some(format!("{}", resolved_type)),
            sort_text: Some(format!("!{}", field_name)), // sort fields to top
            ..Default::default()
        });
    }

    Some(items)
}

/// Result of detecting a record construction context around the cursor.
pub struct RecordConstructionContext {
    /// The fields available for this record (from RecordInfo or anonymous Type::Record).
    pub fields: Vec<(String, Type)>,
    /// Byte offset of the innermost opening `{`.
    pub brace_offset: usize,
}

/// Detect whether the cursor is inside a record construction expression.
///
/// Scans backwards from the cursor to find an unmatched `{`, then checks if it's
/// preceded by an uppercase identifier (named record) or a `fieldname:` pattern
/// (anonymous nested record inside a named record).
///
/// Examples:
/// - `House { a|` → fields of House
/// - `House { year_built: 2005, a|` → fields of House
/// - `House { address: { n|` → fields of House.address (anonymous record)
pub fn extract_record_construction_context(
    result: &CheckResult,
    source: &str,
    offset: usize,
) -> Option<RecordConstructionContext> {
    let prefix = extract_prefix(source, offset);
    let cursor_before_prefix = offset - prefix.len();

    // Iteratively scan backwards through nested `fieldname: {` layers,
    // collecting the field path until we find a named record (uppercase ident before `{`).
    let mut field_path: Vec<String> = Vec::new();
    let mut search_from = cursor_before_prefix;
    let mut innermost_brace = 0;

    loop {
        let brace_pos = find_unmatched_open_brace(source, search_from)?;

        if field_path.is_empty() {
            innermost_brace = brace_pos;
        }

        // Check what precedes the `{`: skip whitespace, then look for either
        // an uppercase ident (named record) or `fieldname:` (anonymous nested record).
        let before_brace = source[..brace_pos].trim_end();
        if before_brace.is_empty() {
            return None;
        }

        // Check if the thing right before `{` is `:` (i.e., `fieldname: {`).
        if let Some(before_colon) = before_brace.strip_suffix(':') {
            let before_colon = before_colon.trim_end();
            let field_start = before_colon
                .rfind(|c: char| !c.is_alphanumeric() && c != '_')
                .map(|i| i + 1)
                .unwrap_or(0);
            let field_name = &before_colon[field_start..];
            if field_name.is_empty() {
                return None;
            }
            field_path.push(field_name.to_string());
            search_from = field_start;
            continue;
        }

        // Extract the identifier just before the `{`.
        let ident_end = before_brace.len();
        let ident_start = before_brace
            .rfind(|c: char| !c.is_alphanumeric() && c != '_')
            .map(|i| i + 1)
            .unwrap_or(0);
        let ident = &before_brace[ident_start..ident_end];

        if ident.is_empty() {
            return None;
        }

        if ident.starts_with(|c: char| c.is_uppercase()) {
            let info = result.records.get(ident)?;
            let mut fields = info.fields.clone();

            // Walk the field path to resolve nested anonymous records.
            for field_name in &field_path {
                let (_, field_ty) = fields.iter().find(|(n, _)| n == field_name)?;
                let resolved = result.sub.apply(field_ty);
                fields = extract_record_fields(result, &resolved)?;
            }

            return Some(RecordConstructionContext {
                fields,
                brace_offset: innermost_brace,
            });
        }

        // Neither uppercase ident nor `fieldname:` pattern.
        return None;
    }
}

/// Scan backwards from `from` to find the nearest unmatched `{`.
/// Tracks brace depth so that matched `{ }` pairs are skipped.
fn find_unmatched_open_brace(source: &str, from: usize) -> Option<usize> {
    let bytes = source.as_bytes();
    let mut depth: i32 = 0;
    let mut pos = from;

    while pos > 0 {
        pos -= 1;
        match bytes[pos] {
            b'}' => depth += 1,
            b'{' => {
                if depth == 0 {
                    return Some(pos);
                }
                depth -= 1;
            }
            _ => {}
        }
    }
    None
}

/// Scan the text between the opening `{` and the cursor to find field names
/// that have already been provided. Respects brace depth so that fields
/// inside nested `{ }` are not counted.
fn find_used_fields(source: &str, brace_offset: usize, cursor_offset: usize) -> HashSet<String> {
    let mut used = HashSet::new();
    let region = &source[brace_offset + 1..cursor_offset];
    let bytes = region.as_bytes();
    let mut depth: i32 = 0;
    let mut i = 0;

    while i < bytes.len() {
        match bytes[i] {
            b'{' => depth += 1,
            b'}' => depth -= 1,
            b':' if depth == 0 => {
                // Check this isn't `::` (cons operator).
                if i + 1 < bytes.len() && bytes[i + 1] == b':' {
                    i += 2;
                    continue;
                }
                // Extract the identifier before this colon.
                let before = &region[..i];
                let trimmed = before.trim_end();
                let start = trimmed
                    .rfind(|c: char| !c.is_alphanumeric() && c != '_')
                    .map(|j| j + 1)
                    .unwrap_or(0);
                let field_name = &trimmed[start..];
                if !field_name.is_empty()
                    && field_name
                        .chars()
                        .next()
                        .is_some_and(|c| c.is_lowercase() || c == '_')
                {
                    used.insert(field_name.to_string());
                }
            }
            _ => {}
        }
        i += 1;
    }
    used
}

/// Collect completion items for record construction.
/// Returns field names (with snippet `: $0`) for the record being constructed,
/// filtering out fields that have already been provided.
pub fn collect_record_construction_completions(
    result: &CheckResult,
    ctx: &RecordConstructionContext,
    prefix: &str,
    source: &str,
    cursor_offset: usize,
) -> Option<Vec<CompletionItem>> {
    let used = find_used_fields(source, ctx.brace_offset, cursor_offset);
    let prefix_lower = prefix.to_lowercase();
    let mut items = Vec::new();

    for (field_name, field_type) in &ctx.fields {
        if used.contains(field_name) {
            continue;
        }
        if !prefix.is_empty() && !field_name.to_lowercase().starts_with(&prefix_lower) {
            continue;
        }
        let resolved_type = result.sub.apply(field_type);
        items.push(CompletionItem {
            label: field_name.clone(),
            kind: Some(CompletionItemKind::FIELD),
            detail: Some(format!("{}", resolved_type)),
            insert_text: Some(format!("{}: $0", field_name)),
            insert_text_format: Some(InsertTextFormat::SNIPPET),
            sort_text: Some(format!("!{}", field_name)), // sort fields to top
            ..Default::default()
        });
    }

    if items.is_empty() {
        return None;
    }
    Some(items)
}

/// Collect completion items for module-qualified access (e.g. `List.` or `Std.`).
/// `chain` is the dot-chain before the cursor (e.g. `["List"]` or `["Std"]`).
///
/// Completes the *next* path segment only:
/// - `List.` → `map`, `reverse`, ... (leaf names)
/// - `Std.` → `List`, `Dict`, `Time`, ... (sub-modules)
/// - `Std.List.` → `map`, `reverse`, ... (leaf names via canonical path)
pub fn collect_module_completions(
    result: &CheckResult,
    chain: &[String],
    prefix: &str,
) -> Option<Vec<CompletionItem>> {
    if chain.is_empty() {
        return None;
    }
    // Build the dot-prefixes to match against. Try both the full chain
    // ("Std.List.") and the short form ("List.") since the env uses short prefixes.
    let full_prefix = chain.join(".");
    let dot_full = format!("{}.", full_prefix);
    let mut dot_prefixes = vec![dot_full.clone()];
    if chain.len() > 1 {
        let short = format!("{}.", chain[chain.len() - 1]);
        dot_prefixes.push(short);
    }

    let prefix_lower = prefix.to_lowercase();
    let mut items = Vec::new();
    let mut seen = HashSet::new();

    // Scan env for qualified names matching our prefix, extracting only the next segment.
    for (name, scheme) in result.env.iter() {
        let remainder = dot_prefixes
            .iter()
            .find_map(|p| name.strip_prefix(p.as_str()));
        let Some(remainder) = remainder else {
            continue;
        };
        // Take only the first segment (before any further dots)
        let next_segment = remainder.split('.').next().unwrap_or(remainder);
        if next_segment.is_empty() {
            continue;
        }
        if !prefix.is_empty() && !next_segment.to_lowercase().starts_with(&prefix_lower) {
            continue;
        }
        if !seen.insert(next_segment.to_string()) {
            continue;
        }
        // If remainder has more dots, this is a sub-module; otherwise it's a leaf name
        let is_leaf = !remainder.contains('.');
        if is_leaf {
            let detail = scheme.display_with_constraints(&result.sub);
            items.push(CompletionItem {
                label: next_segment.to_string(),
                kind: Some(CompletionItemKind::FUNCTION),
                detail: Some(detail),
                ..Default::default()
            });
        } else {
            items.push(CompletionItem {
                label: next_segment.to_string(),
                kind: Some(CompletionItemKind::MODULE),
                detail: Some("module".to_string()),
                ..Default::default()
            });
        }
    }

    // Also scan constructors
    for (name, scheme) in &result.constructors {
        let remainder = dot_prefixes
            .iter()
            .find_map(|p| name.strip_prefix(p.as_str()));
        let Some(remainder) = remainder else {
            continue;
        };
        let next_segment = remainder.split('.').next().unwrap_or(remainder);
        if next_segment.is_empty() || remainder.contains('.') {
            continue; // constructors are always leaf names
        }
        if !prefix.is_empty() && !next_segment.to_lowercase().starts_with(&prefix_lower) {
            continue;
        }
        if !seen.insert(next_segment.to_string()) {
            continue;
        }
        let detail = scheme.display_with_constraints(&result.sub);
        items.push(CompletionItem {
            label: next_segment.to_string(),
            kind: Some(CompletionItemKind::CONSTRUCTOR),
            detail: Some(detail),
            ..Default::default()
        });
    }

    if items.is_empty() {
        return None;
    }
    items.sort_by(|a, b| a.label.cmp(&b.label));
    Some(items)
}

/// Collect completion items from the checker's environment.
pub fn collect_completions(
    result: &CheckResult,
    prefix: &str,
    program: &[Decl],
    offset: usize,
) -> Vec<CompletionItem> {
    let mut items = Vec::new();
    let prefix_lower = prefix.to_lowercase();

    // Functions and variables from env
    for (name, scheme) in result.env.iter() {
        if name.starts_with("__") || name.contains('.') {
            continue; // skip internal dict constructors and qualified names
        }
        if !prefix.is_empty() && !name.to_lowercase().starts_with(&prefix_lower) {
            continue;
        }
        let detail = scheme.display_with_constraints(&result.sub);
        items.push(CompletionItem {
            label: name.to_string(),
            kind: Some(CompletionItemKind::FUNCTION),
            detail: Some(detail),
            ..Default::default()
        });
    }

    // Type constructors
    for (name, scheme) in &result.constructors {
        if name.contains('.') {
            continue; // skip qualified constructors (e.g. Std.Maybe.Just)
        }
        if !prefix.is_empty() && !name.to_lowercase().starts_with(&prefix_lower) {
            continue;
        }
        // Skip internal constructors
        if name == "Cons" || name == "Nil" || name == "True" || name == "False" {
            continue;
        }
        let detail = scheme.display_with_constraints(&result.sub);
        items.push(CompletionItem {
            label: name.to_string(),
            kind: Some(CompletionItemKind::CONSTRUCTOR),
            detail: Some(detail),
            ..Default::default()
        });
    }

    // Module namespace prefixes (e.g. "List", "Dict", "Std") from qualified env names
    {
        let mut module_prefixes = HashSet::new();
        for (name, _) in result.env.iter() {
            if let Some(dot) = name.find('.') {
                module_prefixes.insert(&name[..dot]);
            }
        }
        for (name, _) in &result.constructors {
            if let Some(dot) = name.find('.') {
                module_prefixes.insert(&name[..dot]);
            }
        }
        for module_prefix in module_prefixes {
            if !prefix.is_empty() && !module_prefix.to_lowercase().starts_with(&prefix_lower) {
                continue;
            }
            items.push(CompletionItem {
                label: module_prefix.to_string(),
                kind: Some(CompletionItemKind::MODULE),
                detail: Some("module".to_string()),
                ..Default::default()
            });
        }
    }

    // Effect names
    for name in result.effect_names() {
        if !prefix.is_empty() && !name.to_lowercase().starts_with(&prefix_lower) {
            continue;
        }
        items.push(CompletionItem {
            label: name,
            kind: Some(CompletionItemKind::INTERFACE),
            detail: Some("effect".to_string()),
            ..Default::default()
        });
    }

    // Handler names
    for name in result.handler_names() {
        if !prefix.is_empty() && !name.to_lowercase().starts_with(&prefix_lower) {
            continue;
        }
        items.push(CompletionItem {
            label: name,
            kind: Some(CompletionItemKind::EVENT),
            detail: Some("handler".to_string()),
            ..Default::default()
        });
    }

    // Built-in type names
    let type_names = [
        "Int", "Float", "String", "Bool", "Unit", "List", "Maybe", "Result", "Tuple", "Pid", "Dict", "Set",
    ];
    for type_name in type_names {
        if !prefix.is_empty() && !type_name.to_lowercase().starts_with(&prefix_lower) {
            continue;
        }
        items.push(CompletionItem {
            label: type_name.to_string(),
            kind: Some(CompletionItemKind::CLASS),
            detail: Some("type".to_string()),
            ..Default::default()
        });
    }

    // User-defined type and record names from the current file
    for decl in program {
        let type_name = match decl {
            Decl::TypeDef { name, .. } => Some(name.as_str()),
            Decl::RecordDef { name, .. } => Some(name.as_str()),
            _ => None,
        };
        if let Some(type_name) = type_name {
            if !prefix.is_empty() && !type_name.to_lowercase().starts_with(&prefix_lower) {
                continue;
            }
            items.push(CompletionItem {
                label: type_name.to_string(),
                kind: Some(CompletionItemKind::CLASS),
                detail: Some("type".to_string()),
                ..Default::default()
            });
        }
    }

    // Keywords
    let keywords = [
        "if", "then", "else", "case", "let", "fun", "type", "record", "effect", "handler", "with",
        "import", "module", "pub", "opaque", "trait", "impl", "where", "needs", "receive", "do",
        "assert",
    ];
    for kw in keywords {
        if !prefix.is_empty() && !kw.starts_with(&prefix_lower) {
            continue;
        }
        items.push(CompletionItem {
            label: kw.to_string(),
            kind: Some(CompletionItemKind::KEYWORD),
            ..Default::default()
        });
    }

    // Missing handler operations: if cursor is inside a handler body, suggest unimplemented ops
    for decl in program {
        if let Decl::HandlerDef {
            effects,
            arms,
            recovered_arms,
            span,
            ..
        } = decl
            && offset >= span.start
            && offset <= span.end
        {
            let handled: HashSet<&str> = arms
                .iter()
                .chain(recovered_arms.iter())
                .map(|a| a.node.op_name.as_str())
                .collect();
            for effect_ref in effects {
                if let Some(info) = result.effects.get(&effect_ref.name) {
                    for op in &info.ops {
                        if handled.contains(op.name.as_str()) {
                            continue;
                        }
                        if !prefix.is_empty() && !op.name.to_lowercase().starts_with(&prefix_lower)
                        {
                            continue;
                        }
                        let ret = format!("{}", result.sub.apply(&op.return_type));
                        let snippet = if op.params.is_empty() {
                            format!("{} () = $0", op.name)
                        } else {
                            let tab_stops: Vec<String> = op
                                .params
                                .iter()
                                .enumerate()
                                .map(|(i, (label, _))| {
                                    let name = if label.starts_with('_') {
                                        format!("arg{}", i + 1)
                                    } else {
                                        label.clone()
                                    };
                                    format!("${{{}:{}}}", i + 1, name)
                                })
                                .collect();
                            format!("{} {} = $0", op.name, tab_stops.join(" "))
                        };

                        let param_types: Vec<String> = op
                            .params
                            .iter()
                            .map(|(_, t)| format!("{}", result.sub.apply(t)))
                            .collect();

                        let detail = if param_types.is_empty() {
                            format!("-> {} ({})", ret, effect_ref.name)
                        } else {
                            format!(
                                "{} -> {} ({})",
                                param_types.join(" -> "),
                                ret,
                                effect_ref.name
                            )
                        };
                        items.push(CompletionItem {
                            label: op.name.clone(),
                            kind: Some(CompletionItemKind::METHOD),
                            detail: Some(detail),
                            insert_text: Some(snippet),
                            insert_text_format: Some(InsertTextFormat::SNIPPET),
                            sort_text: Some(format!("!{}", op.name)), // sort to top
                            ..Default::default()
                        });
                    }
                }
            }
        }
    }

    // Sort: exact prefix matches first, then alphabetical
    items.sort_by(|a, b| a.label.cmp(&b.label));

    items
}
