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
    eprintln!("[resolve] looking for receiver={:?} in {} type_at_span entries, source_len={}", receiver, result.type_at_span.len(), source.len());
    for (span, ty) in &result.type_at_span {
        if span.end <= source.len() {
            let text = &source[span.start..span.end];
            if text.contains(receiver) || receiver.contains(text.trim()) {
                eprintln!("[resolve] near-match span={:?} text={:?} ty={:?}", span, text, ty);
            }
        } else {
            eprintln!("[resolve] span {:?} OUT OF BOUNDS (source_len={})", span, source.len());
        }
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
        "Int", "Float", "String", "Bool", "Unit", "List", "Maybe", "Result", "Tuple", "Pid", "Dict",
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
            let handled: HashSet<&str> = arms.iter().chain(recovered_arms.iter()).map(|a| a.op_name.as_str()).collect();
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
