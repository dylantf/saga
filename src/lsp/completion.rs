use std::collections::HashSet;

use tower_lsp::lsp_types::*;

use dylang::ast::Decl;
use dylang::typechecker::CheckResult;

/// Extract the identifier prefix at the cursor position by scanning backwards.
pub fn extract_prefix(source: &str, offset: usize) -> &str {
    let before = &source[..offset.min(source.len())];
    let start = before
        .rfind(|c: char| !c.is_alphanumeric() && c != '_' && c != '\'')
        .map(|i| i + 1)
        .unwrap_or(0);
    &before[start..]
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
