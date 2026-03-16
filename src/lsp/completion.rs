use tower_lsp::lsp_types::*;

use dylang::ast::Decl;
use dylang::typechecker::Checker;

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
pub fn collect_completions(checker: &Checker, prefix: &str, program: &[Decl]) -> Vec<CompletionItem> {
    let mut items = Vec::new();
    let prefix_lower = prefix.to_lowercase();

    // Functions and variables from env
    for (name, scheme) in checker.env.iter() {
        if name.starts_with("__") || name.contains('.') {
            continue; // skip internal dict constructors and qualified names
        }
        if !prefix.is_empty() && !name.to_lowercase().starts_with(&prefix_lower) {
            continue;
        }
        let detail = scheme.display_with_constraints(&checker.sub);
        items.push(CompletionItem {
            label: name.to_string(),
            kind: Some(CompletionItemKind::FUNCTION),
            detail: Some(detail),
            ..Default::default()
        });
    }

    // Type constructors
    for (name, scheme) in &checker.constructors {
        if !prefix.is_empty() && !name.to_lowercase().starts_with(&prefix_lower) {
            continue;
        }
        // Skip internal constructors
        if name == "Cons" || name == "Nil" || name == "True" || name == "False" {
            continue;
        }
        let detail = scheme.display_with_constraints(&checker.sub);
        items.push(CompletionItem {
            label: name.to_string(),
            kind: Some(CompletionItemKind::CONSTRUCTOR),
            detail: Some(detail),
            ..Default::default()
        });
    }

    // Effect names
    for name in checker.effect_names() {
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
    for name in checker.handler_names() {
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
        "Int", "Float", "String", "Bool", "Unit", "List", "Maybe", "Result",
        "Tuple", "Pid", "Dict",
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
        "if", "then", "else", "case", "let", "fun", "type", "record",
        "effect", "handler", "with", "import", "module", "pub", "opaque",
        "trait", "impl", "where", "needs", "receive", "do", "assert",
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

    // Sort: exact prefix matches first, then alphabetical
    items.sort_by(|a, b| a.label.cmp(&b.label));

    items
}
