use std::collections::{HashMap, HashSet};

use tower_lsp::lsp_types::*;

use dylang::ast::Decl;
use dylang::typechecker::{CheckResult, ModuleExports};

use crate::line_index::LineIndex;

/// Generate code actions for the given diagnostics range.
/// Handles: adding missing handler arms, adding missing imports.
pub fn collect_code_actions(
    tc_result: &CheckResult,
    program: &[Decl],
    line_index: &LineIndex,
    source: &str,
    uri: &Url,
    range: Range,
) -> Vec<CodeActionOrCommand> {
    let mut actions = Vec::new();

    collect_missing_handler_arms(
        tc_result,
        program,
        line_index,
        source,
        uri,
        range,
        &mut actions,
    );
    collect_missing_import_actions(tc_result, program, line_index, source, uri, &mut actions);

    actions
}

// ---------------------------------------------------------------------------
// Missing handler arms
// ---------------------------------------------------------------------------

fn collect_missing_handler_arms(
    tc_result: &CheckResult,
    program: &[Decl],
    line_index: &LineIndex,
    source: &str,
    uri: &Url,
    range: Range,
    actions: &mut Vec<CodeActionOrCommand>,
) {
    for decl in program {
        if let Decl::HandlerDef {
            name,
            effects,
            arms,
            recovered_arms,
            span,
            ..
        } = decl
        {
            let handler_start = line_index.offset_to_line_col(span.start, source);
            let handler_end = line_index.offset_to_line_col(span.end, source);
            let handler_range = Range {
                start: Position::new(handler_start.0 as u32, handler_start.1 as u32),
                end: Position::new(handler_end.0 as u32, handler_end.1 as u32),
            };

            if !ranges_overlap(&range, &handler_range) {
                continue;
            }

            let handled: HashSet<&str> = arms
                .iter()
                .chain(recovered_arms.iter())
                .map(|a| a.node.op_name.as_str())
                .collect();

            let mut all_missing: Vec<(String, String)> = Vec::new();
            for effect_ref in effects {
                if let Some(info) = tc_result.effects.get(&effect_ref.name) {
                    for op in &info.ops {
                        if handled.contains(op.name.as_str()) {
                            continue;
                        }
                        let arm_text = format_arm(op);
                        all_missing.push((effect_ref.name.clone(), arm_text));
                    }
                }
            }

            if all_missing.is_empty() {
                continue;
            }

            let insert_offset = span.end;
            let (insert_line, _) = line_index.offset_to_line_col(insert_offset, source);
            let insert_pos = Position::new(insert_line as u32, 0);

            let indent = if let Some(first_arm) = arms.first() {
                let (_, col) = line_index.offset_to_line_col(first_arm.node.span.start, source);
                " ".repeat(col)
            } else {
                "  ".to_string()
            };

            if all_missing.len() > 1 {
                let all_text: String = all_missing
                    .iter()
                    .map(|(_, arm)| format!("{}{}\n", indent, arm))
                    .collect();

                let edit = TextEdit {
                    range: Range {
                        start: insert_pos,
                        end: insert_pos,
                    },
                    new_text: all_text,
                };

                actions.push(CodeActionOrCommand::CodeAction(CodeAction {
                    title: format!("Add all missing arms to '{}'", name),
                    kind: Some(CodeActionKind::QUICKFIX),
                    edit: Some(WorkspaceEdit {
                        changes: Some([(uri.clone(), vec![edit])].into_iter().collect()),
                        ..Default::default()
                    }),
                    diagnostics: None,
                    is_preferred: Some(true),
                    ..Default::default()
                }));
            }

            for (effect_name, arm_text) in &all_missing {
                let op_name = arm_text.split_whitespace().next().unwrap_or("?");
                let text = format!("{}{}\n", indent, arm_text);

                let edit = TextEdit {
                    range: Range {
                        start: insert_pos,
                        end: insert_pos,
                    },
                    new_text: text,
                };

                actions.push(CodeActionOrCommand::CodeAction(CodeAction {
                    title: format!("Add missing arm: {} ({})", op_name, effect_name),
                    kind: Some(CodeActionKind::QUICKFIX),
                    edit: Some(WorkspaceEdit {
                        changes: Some([(uri.clone(), vec![edit])].into_iter().collect()),
                        ..Default::default()
                    }),
                    diagnostics: None,
                    is_preferred: Some(false),
                    ..Default::default()
                }));
            }
        }
    }
}

/// Format a handler arm from an effect op signature.
/// Produces: `op_name arg1 arg2 = todo`
fn format_arm(op: &dylang::typechecker::EffectOpSig) -> String {
    if op.params.is_empty() {
        format!("{} () = todo", op.name)
    } else {
        let params: Vec<String> = op
            .params
            .iter()
            .enumerate()
            .map(|(i, (label, _))| {
                if label.starts_with('_') {
                    format!("arg{}", i + 1)
                } else {
                    label.clone()
                }
            })
            .collect();
        format!("{} {} = todo", op.name, params.join(" "))
    }
}

fn ranges_overlap(a: &Range, b: &Range) -> bool {
    a.start <= b.end && b.start <= a.end
}

// ---------------------------------------------------------------------------
// Missing import code actions
// ---------------------------------------------------------------------------

/// What kind of unresolved name did the diagnostic report?
enum UnresolvedName {
    /// `undefined variable: foo` or `undefined constructor: Foo`
    Bare(String),
    /// `unknown qualified name 'Module.name'`
    Qualified { module: String, name: String },
}

/// Try to extract an unresolved name from a typechecker diagnostic message.
fn parse_unresolved_name(message: &str) -> Option<UnresolvedName> {
    if let Some(name) = message.strip_prefix("undefined variable: ") {
        Some(UnresolvedName::Bare(name.to_string()))
    } else if let Some(name) = message.strip_prefix("undefined constructor: ") {
        Some(UnresolvedName::Bare(name.to_string()))
    } else if let Some(name) = message.strip_prefix("undefined constructor in pattern: ") {
        Some(UnresolvedName::Bare(name.to_string()))
    } else if let Some(rest) = message.strip_prefix("unknown qualified name '") {
        let rest = rest.strip_suffix('\'')?;
        let dot = rest.rfind('.')?;
        Some(UnresolvedName::Qualified {
            module: rest[..dot].to_string(),
            name: rest[dot + 1..].to_string(),
        })
    } else {
        None
    }
}

/// Whether a symbol needs an explicit `exposing` clause or is auto-exposed by `import Module`.
#[derive(Clone, PartialEq)]
enum ExposureKind {
    /// Needs `import Module (name)` to use as a bare name.
    NeedsExposing,
    /// Auto-exposed by `import Module` (handlers, effects, trait methods).
    AutoExposed,
}

/// An entry in the symbol index: which module, and how it's exposed.
#[derive(Clone)]
struct SymbolSource {
    module_name: String,
    exposure: ExposureKind,
}

/// Build a reverse index: name -> list of (module, exposure kind).
/// Searches bindings, constructors, effects, and handlers.
fn build_symbol_index(
    module_exports: &HashMap<String, ModuleExports>,
) -> HashMap<String, Vec<SymbolSource>> {
    let mut index: HashMap<String, Vec<SymbolSource>> = HashMap::new();
    for (module_name, exports) in module_exports {
        // Function/value bindings — need exposing
        for (name, _) in &exports.bindings {
            index.entry(name.clone()).or_default().push(SymbolSource {
                module_name: module_name.clone(),
                exposure: ExposureKind::NeedsExposing,
            });
        }
        // Type constructors — need exposing
        for ctors in exports.type_constructors.values() {
            for ctor in ctors {
                index.entry(ctor.clone()).or_default().push(SymbolSource {
                    module_name: module_name.clone(),
                    exposure: ExposureKind::NeedsExposing,
                });
            }
        }
        // Effects — auto-exposed
        for name in exports.effects.keys() {
            index.entry(name.clone()).or_default().push(SymbolSource {
                module_name: module_name.clone(),
                exposure: ExposureKind::AutoExposed,
            });
        }
        // Handlers — auto-exposed
        for name in exports.handlers.keys() {
            index.entry(name.clone()).or_default().push(SymbolSource {
                module_name: module_name.clone(),
                exposure: ExposureKind::AutoExposed,
            });
        }
    }
    index
}

/// Build an index from short module prefix (last segment) to full module names.
/// e.g. "Time" -> ["Std.Time"], "List" -> ["Std.List"]
/// Combines the module map (all discoverable modules) with already-cached exports.
fn build_module_prefix_index(
    module_exports: &HashMap<String, ModuleExports>,
    module_map: Option<&dylang::typechecker::ModuleMap>,
) -> HashMap<String, Vec<String>> {
    let mut index: HashMap<String, Vec<String>> = HashMap::new();
    let mut add = |module_name: &str| {
        if let Some(last) = module_name.rsplit('.').next() {
            let entry = index.entry(last.to_string()).or_default();
            if !entry.contains(&module_name.to_string()) {
                entry.push(module_name.to_string());
            }
        }
    };
    for module_name in module_exports.keys() {
        add(module_name);
    }
    if let Some(map) = module_map {
        for module_name in map.keys() {
            add(module_name);
        }
    }
    // Include all builtin stdlib modules (may not be in exports cache or module map)
    for &(module_name, _) in dylang::typechecker::BUILTIN_MODULES {
        add(module_name);
    }
    index
}

/// Information about an existing import in the source file.
struct ExistingImport {
    /// The full module name, e.g. "Std.List"
    module_name: String,
    /// The alias, if any
    _alias: Option<String>,
    /// Names in the exposing list (None = no exposing clause)
    exposing: Option<Vec<String>>,
    /// Span end offset (for finding insertion position)
    span_end: usize,
}

/// Where in the file the new import will be inserted, relative to existing structure.
#[derive(Clone, Copy)]
enum InsertContext {
    /// After existing imports — just a newline.
    AfterImports,
    /// After module decl, no existing imports — needs blank line before and after.
    AfterModuleDecl,
    /// Top of file, nothing above — needs blank line after.
    TopOfFile,
}

/// Gather info about existing imports and find the insertion line.
fn analyze_imports(
    program: &[Decl],
    line_index: &LineIndex,
    source: &str,
) -> (Vec<ExistingImport>, Position, InsertContext) {
    let mut imports = Vec::new();
    let mut last_import_end: Option<usize> = None;
    let mut module_decl_end: Option<usize> = None;

    for decl in program {
        match decl {
            Decl::Import {
                module_path,
                alias,
                exposing,
                span,
                ..
            } => {
                let module_name = module_path.join(".");
                imports.push(ExistingImport {
                    module_name,
                    _alias: alias.clone(),
                    exposing: exposing.clone(),
                    span_end: span.end,
                });
                last_import_end = Some(span.end);
            }
            Decl::ModuleDecl { span, .. } => {
                module_decl_end = Some(span.end);
            }
            _ => {}
        }
    }

    let (insert_pos, ctx) = if let Some(offset) = last_import_end {
        let (line, _) = line_index.offset_to_line_col(offset, source);
        (
            Position::new(line as u32 + 1, 0),
            InsertContext::AfterImports,
        )
    } else if let Some(offset) = module_decl_end {
        let (line, _) = line_index.offset_to_line_col(offset, source);
        (
            Position::new(line as u32 + 1, 0),
            InsertContext::AfterModuleDecl,
        )
    } else {
        (Position::new(0, 0), InsertContext::TopOfFile)
    };

    (imports, insert_pos, ctx)
}

/// Generate "add missing import" code actions for all unresolved-name diagnostics.
fn collect_missing_import_actions(
    tc_result: &CheckResult,
    program: &[Decl],
    line_index: &LineIndex,
    source: &str,
    uri: &Url,
    actions: &mut Vec<CodeActionOrCommand>,
) {
    let module_exports = tc_result.module_exports();
    if module_exports.is_empty() {
        return;
    }

    let symbol_index = build_symbol_index(module_exports);
    let prefix_index = build_module_prefix_index(module_exports, tc_result.module_map());
    let (existing_imports, insert_pos, insert_ctx) = analyze_imports(program, line_index, source);

    // Set of already-imported module names: explicit user imports + prelude imports
    let mut imported_modules: HashSet<String> = existing_imports
        .iter()
        .map(|i| i.module_name.clone())
        .collect();
    for prelude_import in &tc_result.prelude_imports {
        if let Decl::Import { module_path, .. } = prelude_import {
            imported_modules.insert(module_path.join("."));
        }
    }

    // Track suggested imports to avoid duplicates across diagnostics
    let mut suggested: HashSet<String> = HashSet::new();

    for diag in &tc_result.diagnostics {
        let unresolved = match parse_unresolved_name(&diag.message) {
            Some(u) => u,
            None => continue,
        };

        match unresolved {
            UnresolvedName::Bare(name) => {
                // Find which modules export this name
                let Some(sources) = symbol_index.get(&name) else {
                    continue;
                };
                for source_info in sources {
                    let module_name = &source_info.module_name;
                    let auto = source_info.exposure == ExposureKind::AutoExposed;

                    if auto {
                        // Handlers/effects/traits: just `import Module` is enough
                        if imported_modules.contains(module_name) {
                            continue;
                        }
                        let key = format!("import:{}", module_name);
                        if !suggested.insert(key) {
                            continue;
                        }
                        new_import_action(module_name, None, insert_pos, insert_ctx, uri, actions);
                    } else if let Some(existing) = existing_imports
                        .iter()
                        .find(|i| i.module_name == *module_name)
                    {
                        // Module explicitly imported by user — suggest adding to exposing
                        // list AND qualifying the name inline
                        let key = format!("expose:{}:{}", module_name, name);
                        if !suggested.insert(key) {
                            continue;
                        }
                        if let Some(ref exposed) = existing.exposing {
                            if !exposed.contains(&name) {
                                add_to_exposing_action(
                                    existing, &name, source, line_index, uri, actions,
                                );
                            }
                        } else {
                            add_expose_to_existing_action(
                                existing, &name, source, line_index, uri, actions,
                            );
                        }
                        if let Some(span) = diag.span {
                            let prefix = module_name.rsplit('.').next().unwrap_or(module_name);
                            qualify_name_action(
                                &name, prefix, span, source, line_index, uri, actions,
                            );
                        }
                    } else if imported_modules.contains(module_name) {
                        // Module imported via prelude (no explicit import to modify) —
                        // offer two choices:
                        // 1. Add an explicit `import Module (name)` to expose it
                        // 2. Replace bare `name` with `Module.name` (qualified use)
                        let key = format!("import:{}:{}", module_name, name);
                        if !suggested.insert(key) {
                            continue;
                        }
                        new_import_action(
                            module_name,
                            Some(&name),
                            insert_pos,
                            insert_ctx,
                            uri,
                            actions,
                        );
                        if let Some(span) = diag.span {
                            let prefix = module_name.rsplit('.').next().unwrap_or(module_name);
                            qualify_name_action(
                                &name, prefix, span, source, line_index, uri, actions,
                            );
                        }
                    } else {
                        // Module not imported at all — suggest new import with exposing
                        let key = format!("import:{}:{}", module_name, name);
                        if !suggested.insert(key) {
                            continue;
                        }
                        new_import_action(
                            module_name,
                            Some(&name),
                            insert_pos,
                            insert_ctx,
                            uri,
                            actions,
                        );
                    }
                }
            }
            UnresolvedName::Qualified { module, name } => {
                // "Module.name" failed — the module prefix isn't imported.
                // Find full module names whose last segment matches the prefix.
                let Some(candidate_modules) = prefix_index.get(&module) else {
                    continue;
                };
                for module_name in candidate_modules {
                    if imported_modules.contains(module_name) {
                        // Already imported (the name just doesn't exist in it) — skip
                        continue;
                    }
                    // Verify the module actually exports this name (if we have its exports)
                    if let Some(exports) = module_exports.get(module_name) {
                        let has_name = exports.bindings.iter().any(|(n, _)| n == &name)
                            || exports
                                .type_constructors
                                .values()
                                .any(|ctors| ctors.contains(&name))
                            || exports.effects.contains_key(&name)
                            || exports.handlers.contains_key(&name);
                        if !has_name {
                            continue;
                        }
                    }
                    let key = format!("import:{}", module_name);
                    if !suggested.insert(key) {
                        continue;
                    }
                    // Suggest `import Std.Time` (no exposing — qualified use is intended)
                    new_import_action(module_name, None, insert_pos, insert_ctx, uri, actions);
                }
            }
        }
    }
}

/// Create a code action to add a brand new import line.
fn new_import_action(
    module_name: &str,
    expose_name: Option<&str>,
    insert_pos: Position,
    insert_ctx: InsertContext,
    uri: &Url,
    actions: &mut Vec<CodeActionOrCommand>,
) {
    let import_stmt = match expose_name {
        Some(name) => format!("import {} ({})", module_name, name),
        None => format!("import {}", module_name),
    };
    // Wrap with blank lines based on where we're inserting:
    // - AfterImports: just append a newline
    // - AfterModuleDecl: blank line before (to separate from module decl) + blank line after (to separate from code)
    // - TopOfFile: blank line after (to separate from code)
    let import_text = match insert_ctx {
        InsertContext::AfterImports => format!("{}\n", import_stmt),
        InsertContext::AfterModuleDecl => format!("\n{}\n\n", import_stmt),
        InsertContext::TopOfFile => format!("{}\n\n", import_stmt),
    };
    let title = match expose_name {
        Some(name) => format!("Add `import {} ({})`", module_name, name),
        None => format!("Add `import {}`", module_name),
    };

    let edit = TextEdit {
        range: Range {
            start: insert_pos,
            end: insert_pos,
        },
        new_text: import_text,
    };

    actions.push(CodeActionOrCommand::CodeAction(CodeAction {
        title,
        kind: Some(CodeActionKind::QUICKFIX),
        edit: Some(WorkspaceEdit {
            changes: Some([(uri.clone(), vec![edit])].into_iter().collect()),
            ..Default::default()
        }),
        diagnostics: None,
        is_preferred: Some(false),
        ..Default::default()
    }));
}

/// Create a code action to add a name to an existing import's exposing list.
/// e.g. `import Std.List (map)` -> `import Std.List (map, reverse)`
fn add_to_exposing_action(
    existing: &ExistingImport,
    name: &str,
    source: &str,
    line_index: &LineIndex,
    uri: &Url,
    actions: &mut Vec<CodeActionOrCommand>,
) {
    // Find the closing `)` of the exposing list by scanning backwards from span end
    let before_end = &source[..existing.span_end];
    let Some(close_paren) = before_end.rfind(')') else {
        return;
    };

    let (line, col) = line_index.offset_to_line_col(close_paren, source);
    let insert_pos = Position::new(line as u32, col as u32);

    let new_text = format!(", {}", name);
    let title = format!("Add `{}` to import {}", name, existing.module_name);

    let edit = TextEdit {
        range: Range {
            start: insert_pos,
            end: insert_pos,
        },
        new_text,
    };

    actions.push(CodeActionOrCommand::CodeAction(CodeAction {
        title,
        kind: Some(CodeActionKind::QUICKFIX),
        edit: Some(WorkspaceEdit {
            changes: Some([(uri.clone(), vec![edit])].into_iter().collect()),
            ..Default::default()
        }),
        diagnostics: None,
        is_preferred: Some(false),
        ..Default::default()
    }));
}

/// Create a code action to add an exposing clause to an import that has none.
/// e.g. `import Std.List` -> `import Std.List (reverse)`
fn add_expose_to_existing_action(
    existing: &ExistingImport,
    name: &str,
    source: &str,
    line_index: &LineIndex,
    uri: &Url,
    actions: &mut Vec<CodeActionOrCommand>,
) {
    // Insert ` (name)` at the end of the import line (at span_end)
    let (line, col) = line_index.offset_to_line_col(existing.span_end, source);
    let insert_pos = Position::new(line as u32, col as u32);

    let new_text = format!(" ({})", name);
    let title = format!("Expose `{}` from import {}", name, existing.module_name);

    let edit = TextEdit {
        range: Range {
            start: insert_pos,
            end: insert_pos,
        },
        new_text,
    };

    actions.push(CodeActionOrCommand::CodeAction(CodeAction {
        title,
        kind: Some(CodeActionKind::QUICKFIX),
        edit: Some(WorkspaceEdit {
            changes: Some([(uri.clone(), vec![edit])].into_iter().collect()),
            ..Default::default()
        }),
        diagnostics: None,
        is_preferred: Some(false),
        ..Default::default()
    }));
}

/// Create a code action to replace a bare name with its qualified form.
/// e.g. `reverse` -> `List.reverse`
fn qualify_name_action(
    name: &str,
    prefix: &str,
    span: dylang::token::Span,
    source: &str,
    line_index: &LineIndex,
    uri: &Url,
    actions: &mut Vec<CodeActionOrCommand>,
) {
    let (start_line, start_col) = line_index.offset_to_line_col(span.start, source);
    let (end_line, end_col) = line_index.offset_to_line_col(span.end, source);

    let edit = TextEdit {
        range: Range {
            start: Position::new(start_line as u32, start_col as u32),
            end: Position::new(end_line as u32, end_col as u32),
        },
        new_text: format!("{}.{}", prefix, name),
    };

    actions.push(CodeActionOrCommand::CodeAction(CodeAction {
        title: format!("Use `{}.{}`", prefix, name),
        kind: Some(CodeActionKind::QUICKFIX),
        edit: Some(WorkspaceEdit {
            changes: Some([(uri.clone(), vec![edit])].into_iter().collect()),
            ..Default::default()
        }),
        diagnostics: None,
        is_preferred: Some(false),
        ..Default::default()
    }));
}
