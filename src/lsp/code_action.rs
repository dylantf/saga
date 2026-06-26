use std::collections::{HashMap, HashSet};

use saga::ast::{self, Exposing};
use saga::typechecker::{self, ModuleExports};
use tower_lsp::lsp_types::*;

use super::state::ProjectSemanticStore;
use super::text::LineIndex;
use super::{DocumentState, SemanticSnapshot};

pub(super) fn collect_code_actions(
    uri: &Url,
    document: &DocumentState,
    semantic: &SemanticSnapshot,
    project: Option<(&ProjectSemanticStore, &Option<std::path::PathBuf>)>,
    request_range: Range,
    diagnostics: &[Diagnostic],
) -> Vec<CodeActionOrCommand> {
    let Some(parse) = &document.parse else {
        return Vec::new();
    };
    let mut module_exports = semantic.check.module_exports().clone();
    if let Some((projects, project_root)) = project {
        for (module, exports) in projects.module_exports_for_project(project_root) {
            module_exports.entry(module).or_insert(exports);
        }
    }
    if module_exports.is_empty() {
        return Vec::new();
    }

    let current_module = current_module_name(&parse.program);
    let symbol_index = build_symbol_index(&module_exports);
    let module_prefix_index =
        build_module_prefix_index(&module_exports, semantic.check.module_map());
    let (existing_imports, insert_pos, insert_context) =
        analyze_imports(&parse.program, &parse.line_index, &parse.source);
    let explicit_imports: HashSet<String> = existing_imports
        .iter()
        .map(|import| import.module_name.clone())
        .collect();
    let implicit_imports = semantic
        .check
        .prelude_imports
        .iter()
        .filter_map(|decl| match decl {
            ast::Decl::Import { module_path, .. } => Some(module_path.join(".")),
            _ => None,
        })
        .collect::<HashSet<_>>();

    let mut actions = Vec::new();
    let mut suggested = HashSet::new();
    for diagnostic in diagnostics {
        if !ranges_overlap(&request_range, &diagnostic.range) {
            continue;
        }
        let Some(unresolved) = parse_unresolved_name(&diagnostic.message) else {
            continue;
        };
        match unresolved {
            UnresolvedName::Bare(name) => collect_bare_import_actions(
                BareImportActionInput {
                    name: &name,
                    diagnostic_range: diagnostic.range,
                    current_module: current_module.as_deref(),
                    uri,
                    source: &parse.source,
                    line_index: &parse.line_index,
                    symbol_index: &symbol_index,
                    existing_imports: &existing_imports,
                    explicit_imports: &explicit_imports,
                    implicit_imports: &implicit_imports,
                    insert_pos,
                    insert_context,
                },
                &mut suggested,
                &mut actions,
            ),
            UnresolvedName::Qualified { module, name } => collect_qualified_import_actions(
                QualifiedImportActionInput {
                    module: &module,
                    name: &name,
                    current_module: current_module.as_deref(),
                    uri,
                    module_exports: &module_exports,
                    module_prefix_index: &module_prefix_index,
                    explicit_imports: &explicit_imports,
                    implicit_imports: &implicit_imports,
                    insert_pos,
                    insert_context,
                },
                &mut suggested,
                &mut actions,
            ),
        }
    }
    actions
}

struct BareImportActionInput<'a> {
    name: &'a str,
    diagnostic_range: Range,
    current_module: Option<&'a str>,
    uri: &'a Url,
    source: &'a str,
    line_index: &'a LineIndex,
    symbol_index: &'a HashMap<String, Vec<SymbolSource>>,
    existing_imports: &'a [ExistingImport],
    explicit_imports: &'a HashSet<String>,
    implicit_imports: &'a HashSet<String>,
    insert_pos: Position,
    insert_context: InsertContext,
}

fn collect_bare_import_actions(
    input: BareImportActionInput<'_>,
    suggested: &mut HashSet<String>,
    actions: &mut Vec<CodeActionOrCommand>,
) {
    let Some(sources) = input.symbol_index.get(input.name) else {
        return;
    };
    for source in sources {
        if input.current_module == Some(source.module_name.as_str()) {
            continue;
        }
        let already_imported = input.explicit_imports.contains(&source.module_name);
        let implicitly_imported = input.implicit_imports.contains(&source.module_name);
        if let Some(existing) = input
            .existing_imports
            .iter()
            .find(|import| import.module_name == source.module_name)
        {
            match &existing.exposing {
                Some(Exposing::All { .. }) => {}
                Some(Exposing::Items(items)) => {
                    if !items.iter().any(|item| {
                        item.name == source.import_item || item.surface_name() == input.name
                    }) {
                        add_to_exposing_action(
                            existing,
                            &source.import_item,
                            input.source,
                            input.line_index,
                            input.uri,
                            suggested,
                            actions,
                        );
                    }
                }
                None => add_expose_to_existing_action(
                    existing,
                    &source.import_item,
                    input.source,
                    input.line_index,
                    input.uri,
                    suggested,
                    actions,
                ),
            }
            qualify_name_action(
                input.name,
                existing.qualifier(),
                input.diagnostic_range,
                input.uri,
                suggested,
                actions,
            );
        } else {
            add_new_import_action(
                &source.module_name,
                Some(&source.import_item),
                input.insert_pos,
                input.insert_context,
                input.uri,
                suggested,
                actions,
            );
            if implicitly_imported && !already_imported {
                qualify_name_action(
                    input.name,
                    module_qualifier(&source.module_name),
                    input.diagnostic_range,
                    input.uri,
                    suggested,
                    actions,
                );
            }
        }
    }
}

struct QualifiedImportActionInput<'a> {
    module: &'a str,
    name: &'a str,
    current_module: Option<&'a str>,
    uri: &'a Url,
    module_exports: &'a HashMap<String, ModuleExports>,
    module_prefix_index: &'a HashMap<String, Vec<String>>,
    explicit_imports: &'a HashSet<String>,
    implicit_imports: &'a HashSet<String>,
    insert_pos: Position,
    insert_context: InsertContext,
}

fn collect_qualified_import_actions(
    input: QualifiedImportActionInput<'_>,
    suggested: &mut HashSet<String>,
    actions: &mut Vec<CodeActionOrCommand>,
) {
    let Some(candidate_modules) = input.module_prefix_index.get(input.module) else {
        return;
    };
    for module_name in candidate_modules {
        if input.current_module == Some(module_name.as_str())
            || input.explicit_imports.contains(module_name)
            || input.implicit_imports.contains(module_name)
        {
            continue;
        }
        let Some(exports) = input.module_exports.get(module_name) else {
            continue;
        };
        if !exports_name(exports, input.name) {
            continue;
        }
        add_new_import_action(
            module_name,
            None,
            input.insert_pos,
            input.insert_context,
            input.uri,
            suggested,
            actions,
        );
    }
}

#[derive(Clone)]
struct SymbolSource {
    module_name: String,
    import_item: String,
}

fn build_symbol_index(
    module_exports: &HashMap<String, ModuleExports>,
) -> HashMap<String, Vec<SymbolSource>> {
    let mut index: HashMap<String, Vec<SymbolSource>> = HashMap::new();
    for (module_name, exports) in module_exports {
        let mut add = |symbol: &str, import_item: &str| {
            let source = SymbolSource {
                module_name: module_name.clone(),
                import_item: import_item.to_string(),
            };
            let entry = index.entry(symbol.to_string()).or_default();
            if !entry.iter().any(|existing: &SymbolSource| {
                existing.module_name == source.module_name
                    && existing.import_item == source.import_item
            }) {
                entry.push(source);
            }
        };

        for (name, _) in &exports.bindings {
            add(name, name);
        }
        for (type_name, constructors) in &exports.type_constructors {
            add(type_name, type_name);
            for constructor in constructors {
                add(constructor, type_name);
            }
        }
        for name in exports.type_aliases.keys() {
            add(name, name);
        }
        for (trait_name, info) in &exports.traits {
            add(trait_name, trait_name);
            for method in &info.methods {
                add(&method.name, trait_name);
            }
        }
        for (effect_name, info) in &exports.effects {
            add(effect_name, effect_name);
            for op in &info.ops {
                add(&op.name, effect_name);
            }
        }
        for name in exports.handlers.keys() {
            add(name, name);
        }
    }
    index
}

fn build_module_prefix_index(
    module_exports: &HashMap<String, ModuleExports>,
    module_map: Option<&typechecker::ModuleMap>,
) -> HashMap<String, Vec<String>> {
    let mut index: HashMap<String, Vec<String>> = HashMap::new();
    let mut add = |key: &str, module_name: &str| {
        let entry = index.entry(key.to_string()).or_default();
        if !entry.iter().any(|existing| existing == module_name) {
            entry.push(module_name.to_string());
        }
    };
    for module_name in module_exports.keys() {
        add(module_name, module_name);
        if let Some(last) = module_name.rsplit('.').next() {
            add(last, module_name);
        }
    }
    if let Some(module_map) = module_map {
        for module_name in module_map.keys() {
            add(module_name, module_name);
            if let Some(last) = module_name.rsplit('.').next() {
                add(last, module_name);
            }
        }
    }
    for &(module_name, _) in typechecker::BUILTIN_MODULES {
        add(module_name, module_name);
        if let Some(last) = module_name.rsplit('.').next() {
            add(last, module_name);
        }
    }
    index
}

fn exports_name(exports: &ModuleExports, name: &str) -> bool {
    exports.bindings.iter().any(|(binding, _)| binding == name)
        || exports
            .type_constructors
            .values()
            .any(|constructors| constructors.iter().any(|ctor| ctor == name))
        || exports.type_constructors.contains_key(name)
        || exports.type_aliases.contains_key(name)
        || exports.traits.contains_key(name)
        || exports
            .traits
            .values()
            .any(|info| info.methods.iter().any(|method| method.name == name))
        || exports.effects.contains_key(name)
        || exports
            .effects
            .values()
            .any(|info| info.ops.iter().any(|op| op.name == name))
        || exports.handlers.contains_key(name)
}

struct ExistingImport {
    module_name: String,
    alias: Option<String>,
    exposing: Option<Exposing>,
    span_end: usize,
}

impl ExistingImport {
    fn qualifier(&self) -> &str {
        self.alias
            .as_deref()
            .unwrap_or_else(|| module_qualifier(&self.module_name))
    }
}

#[derive(Clone, Copy)]
enum InsertContext {
    AfterImports,
    AfterModuleDecl,
    TopOfFile,
}

fn analyze_imports(
    program: &[ast::Decl],
    line_index: &LineIndex,
    source: &str,
) -> (Vec<ExistingImport>, Position, InsertContext) {
    let mut imports = Vec::new();
    let mut last_import_end = None;
    let mut module_decl_end = None;
    for decl in program {
        match decl {
            ast::Decl::Import {
                module_path,
                alias,
                exposing,
                span,
                ..
            } => {
                imports.push(ExistingImport {
                    module_name: module_path.join("."),
                    alias: alias.clone(),
                    exposing: exposing.clone(),
                    span_end: span.end,
                });
                last_import_end = Some(span.end);
            }
            ast::Decl::ModuleDecl { span, .. } => {
                module_decl_end = Some(span.end);
            }
            _ => {}
        }
    }

    if let Some(offset) = last_import_end {
        let mut pos = line_index.offset_to_position(offset, source);
        pos.line += 1;
        pos.character = 0;
        (imports, pos, InsertContext::AfterImports)
    } else if let Some(offset) = module_decl_end {
        let mut pos = line_index.offset_to_position(offset, source);
        pos.line += 1;
        pos.character = 0;
        (imports, pos, InsertContext::AfterModuleDecl)
    } else {
        (imports, Position::new(0, 0), InsertContext::TopOfFile)
    }
}

fn current_module_name(program: &[ast::Decl]) -> Option<String> {
    program.iter().find_map(|decl| match decl {
        ast::Decl::ModuleDecl { path, .. } => Some(path.join(".")),
        _ => None,
    })
}

enum UnresolvedName {
    Bare(String),
    Qualified { module: String, name: String },
}

fn parse_unresolved_name(message: &str) -> Option<UnresolvedName> {
    if let Some(name) = suffix_after(message, "undefined variable: ") {
        Some(UnresolvedName::Bare(name))
    } else if let Some(name) = suffix_after(message, "undefined constructor: ") {
        Some(UnresolvedName::Bare(name))
    } else if let Some(name) = suffix_after(message, "undefined constructor in pattern: ") {
        Some(UnresolvedName::Bare(name))
    } else if let Some(name) = suffix_after(message, "undefined effect operation: ") {
        Some(UnresolvedName::Bare(name))
    } else if let Some(rest) = quoted_after(message, "unknown qualified name '") {
        let dot = rest.rfind('.')?;
        Some(UnresolvedName::Qualified {
            module: rest[..dot].to_string(),
            name: rest[dot + 1..].to_string(),
        })
    } else {
        None
    }
}

fn suffix_after(message: &str, prefix: &str) -> Option<String> {
    let start = message.find(prefix)? + prefix.len();
    let rest = &message[start..];
    let end = rest
        .find(|c: char| c.is_whitespace() || matches!(c, ',' | ')' | '}'))
        .unwrap_or(rest.len());
    Some(rest[..end].trim_matches('`').to_string())
}

fn quoted_after(message: &str, prefix: &str) -> Option<String> {
    let start = message.find(prefix)? + prefix.len();
    let rest = &message[start..];
    let end = rest.find('\'')?;
    Some(rest[..end].to_string())
}

fn add_new_import_action(
    module_name: &str,
    expose_name: Option<&str>,
    insert_pos: Position,
    insert_context: InsertContext,
    uri: &Url,
    suggested: &mut HashSet<String>,
    actions: &mut Vec<CodeActionOrCommand>,
) {
    let key = format!("new:{module_name}:{expose_name:?}");
    if !suggested.insert(key) {
        return;
    }
    let import_stmt = match expose_name {
        Some(name) => format!("import {module_name} ({name})"),
        None => format!("import {module_name}"),
    };
    let new_text = match insert_context {
        InsertContext::AfterImports => format!("{import_stmt}\n"),
        InsertContext::AfterModuleDecl => format!("\n{import_stmt}\n\n"),
        InsertContext::TopOfFile => format!("{import_stmt}\n\n"),
    };
    let title = match expose_name {
        Some(name) => format!("Add `import {module_name} ({name})`"),
        None => format!("Add `import {module_name}`"),
    };
    push_edit_action(title, uri, insert_pos..insert_pos, new_text, actions);
}

fn add_to_exposing_action(
    existing: &ExistingImport,
    name: &str,
    source: &str,
    line_index: &LineIndex,
    uri: &Url,
    suggested: &mut HashSet<String>,
    actions: &mut Vec<CodeActionOrCommand>,
) {
    let key = format!("expose-item:{}:{name}", existing.module_name);
    if !suggested.insert(key) {
        return;
    }
    let before_end = &source[..existing.span_end.min(source.len())];
    let Some(close_paren) = before_end.rfind(')') else {
        return;
    };
    let pos = line_index.offset_to_position(close_paren, source);
    push_edit_action(
        format!("Add `{name}` to import {}", existing.module_name),
        uri,
        pos..pos,
        format!(", {name}"),
        actions,
    );
}

fn add_expose_to_existing_action(
    existing: &ExistingImport,
    name: &str,
    source: &str,
    line_index: &LineIndex,
    uri: &Url,
    suggested: &mut HashSet<String>,
    actions: &mut Vec<CodeActionOrCommand>,
) {
    let key = format!("expose-clause:{}:{name}", existing.module_name);
    if !suggested.insert(key) {
        return;
    }
    let pos = line_index.offset_to_position(existing.span_end, source);
    push_edit_action(
        format!("Expose `{name}` from import {}", existing.module_name),
        uri,
        pos..pos,
        format!(" ({name})"),
        actions,
    );
}

fn qualify_name_action(
    name: &str,
    prefix: &str,
    range: Range,
    uri: &Url,
    suggested: &mut HashSet<String>,
    actions: &mut Vec<CodeActionOrCommand>,
) {
    let key = format!(
        "qualify:{prefix}:{name}:{}:{}",
        range.start.line, range.start.character
    );
    if !suggested.insert(key) {
        return;
    }
    push_edit_action(
        format!("Use `{prefix}.{name}`"),
        uri,
        range.start..range.end,
        format!("{prefix}.{name}"),
        actions,
    );
}

fn push_edit_action(
    title: String,
    uri: &Url,
    range: std::ops::Range<Position>,
    new_text: String,
    actions: &mut Vec<CodeActionOrCommand>,
) {
    actions.push(CodeActionOrCommand::CodeAction(CodeAction {
        title,
        kind: Some(CodeActionKind::QUICKFIX),
        edit: Some(WorkspaceEdit {
            changes: Some(
                [(
                    uri.clone(),
                    vec![TextEdit {
                        range: Range {
                            start: range.start,
                            end: range.end,
                        },
                        new_text,
                    }],
                )]
                .into_iter()
                .collect(),
            ),
            ..Default::default()
        }),
        diagnostics: None,
        is_preferred: Some(false),
        ..Default::default()
    }));
}

fn module_qualifier(module_name: &str) -> &str {
    module_name.rsplit('.').next().unwrap_or(module_name)
}

fn ranges_overlap(a: &Range, b: &Range) -> bool {
    a.start <= b.end && b.start <= a.end
}
