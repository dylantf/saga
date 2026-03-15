use std::path::PathBuf;

use dylang::ast::{Decl, Expr, Pat, Stmt};
use dylang::token::Span;
use dylang::typechecker::Checker;

pub struct DefinitionResult {
    pub span: Span,
    /// None means same file, Some means a different file
    pub file_path: Option<PathBuf>,
}

/// Find the definition of a name, searching local then imported modules.
/// If name starts with "module:", jump to the module file itself.
pub fn find_definition(
    program: &[Decl],
    name: &str,
    checker: &Checker,
) -> Option<DefinitionResult> {
    // Module name click: jump to the module file
    if let Some(module_name) = name.strip_prefix("module:") {
        return find_module_file(program, module_name, checker);
    }

    // Try local first
    if let Some(span) = find_local(program, name) {
        return Some(DefinitionResult {
            span,
            file_path: None,
        });
    }

    // Try cross-module: find which module imported this name
    find_cross_module(program, name, checker)
}

fn find_local(program: &[Decl], name: &str) -> Option<Span> {
    for decl in program {
        if let Some(span) = find_in_decl(decl, name) {
            return Some(span);
        }
    }
    None
}

fn find_in_decl(decl: &Decl, name: &str) -> Option<Span> {
    match decl {
        Decl::FunAnnotation {
            name: fn_name,
            span,
            ..
        } if fn_name == name => Some(*span),

        Decl::FunBinding {
            name: fn_name,
            span,
            ..
        } if fn_name == name => Some(*span),

        Decl::Let {
            name: let_name,
            span,
            ..
        } if let_name == name => Some(*span),

        Decl::TypeDef {
            name: type_name,
            variants,
            span,
            ..
        } => {
            if type_name == name {
                return Some(*span);
            }
            for variant in variants {
                if variant.name == name {
                    return Some(variant.span);
                }
            }
            None
        }

        Decl::RecordDef {
            name: rec_name,
            span,
            ..
        } if rec_name == name => Some(*span),

        Decl::EffectDef {
            name: eff_name,
            operations,
            span,
            ..
        } => {
            if eff_name == name {
                return Some(*span);
            }
            for op in operations {
                if op.name == name {
                    return Some(op.span);
                }
            }
            None
        }

        Decl::HandlerDef {
            name: h_name, span, ..
        } if h_name == name => Some(*span),

        Decl::TraitDef {
            name: t_name, span, ..
        } if t_name == name => Some(*span),

        // Search inside function bodies for local let bindings
        Decl::FunBinding { body, .. } => find_local_def(body, name),

        _ => None,
    }
}

fn find_local_def(expr: &Expr, name: &str) -> Option<Span> {
    match expr {
        Expr::Block { stmts, .. } => {
            for stmt in stmts {
                if let Some(span) = find_def_in_stmt(stmt, name) {
                    return Some(span);
                }
            }
            None
        }
        Expr::Case { arms, .. } => {
            for arm in arms {
                if let Some(span) = find_def_in_pat(&arm.pattern, name) {
                    return Some(span);
                }
                if let Some(span) = find_local_def(&arm.body, name) {
                    return Some(span);
                }
            }
            None
        }
        Expr::Lambda { params, body, .. } => {
            for pat in params {
                if let Some(span) = find_def_in_pat(pat, name) {
                    return Some(span);
                }
            }
            find_local_def(body, name)
        }
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => find_local_def(then_branch, name).or_else(|| find_local_def(else_branch, name)),
        _ => None,
    }
}

fn find_def_in_stmt(stmt: &Stmt, name: &str) -> Option<Span> {
    match stmt {
        Stmt::Let { pattern, span, .. } => {
            if pat_defines(pattern, name) {
                return Some(*span);
            }
            None
        }
        Stmt::LetFun {
            name: fn_name,
            span,
            ..
        } if fn_name == name => Some(*span),
        _ => None,
    }
}

fn pat_defines(pat: &Pat, name: &str) -> bool {
    match pat {
        Pat::Var { name: v, .. } => v == name,
        Pat::Constructor { args, .. } => args.iter().any(|a| pat_defines(a, name)),
        Pat::Tuple { elements, .. } => elements.iter().any(|e| pat_defines(e, name)),
        Pat::Record { fields, .. } => fields.iter().any(|(field_name, alias)| {
            if let Some(pat) = alias {
                pat_defines(pat, name)
            } else {
                field_name == name
            }
        }),
        Pat::StringPrefix { rest, .. } => pat_defines(rest, name),
        _ => false,
    }
}

fn find_def_in_pat(pat: &Pat, name: &str) -> Option<Span> {
    match pat {
        Pat::Var { name: v, span, .. } if v == name => Some(*span),
        Pat::Constructor { args, .. } => {
            for a in args {
                if let Some(s) = find_def_in_pat(a, name) {
                    return Some(s);
                }
            }
            None
        }
        Pat::Tuple { elements, .. } => {
            for e in elements {
                if let Some(s) = find_def_in_pat(e, name) {
                    return Some(s);
                }
            }
            None
        }
        _ => None,
    }
}

/// Jump to a module file by module name (e.g. "MathLib").
fn find_module_file(
    program: &[Decl],
    module_name: &str,
    checker: &Checker,
) -> Option<DefinitionResult> {
    // Find the import that matches this module name
    for decl in program {
        if let Decl::Import { module_path, .. } = decl {
            let last = module_path.last()?;
            if last == module_name {
                let full_name = module_path.join(".");
                let file_path = checker
                    .module_map
                    .as_ref()
                    .and_then(|m| m.get(&full_name))
                    .cloned()?;
                // Jump to the top of the file
                return Some(DefinitionResult {
                    span: Span { start: 0, end: 0 },
                    file_path: Some(file_path),
                });
            }
        }
    }
    None
}

/// Find a name's definition in an imported module.
fn find_cross_module(program: &[Decl], name: &str, checker: &Checker) -> Option<DefinitionResult> {
    // Collect all imports that could have brought this name into scope
    for decl in program {
        if let Decl::Import {
            module_path,
            exposing,
            ..
        } = decl
        {
            let module_name = module_path.join(".");

            // Skip stdlib builtins (no file to jump to)
            if module_name.starts_with("Std.") {
                continue;
            }

            // Check if this import could expose the name
            let exposes_name = match exposing {
                Some(items) => items.iter().any(|item| item == name),
                None => true, // No exposing list means wildcard import
            };

            if !exposes_name {
                continue;
            }

            // Look up the module's AST and file path
            let Some(file_path) = checker
                .module_map
                .as_ref()
                .and_then(|m| m.get(&module_name))
                .cloned()
            else {
                continue;
            };

            let Some(module_program) = checker.tc_programs.get(&module_name) else {
                continue;
            };

            // Search for the definition in that module
            if let Some(span) = find_local(module_program, name) {
                return Some(DefinitionResult {
                    span,
                    file_path: Some(file_path),
                });
            }
        }
    }
    None
}
