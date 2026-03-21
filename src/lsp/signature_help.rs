use tower_lsp::lsp_types::*;

use dylang::ast::{Decl, Expr, ExprKind, Pat, Stmt};
use dylang::typechecker::CheckResult;

use super::hover::format_type_expr;

/// Extract an identifier that appears before trailing spaces at the given offset.
/// E.g., for source `foo ` with offset=4, returns Some("foo").
pub fn ident_before_spaces(source: &str, offset: usize) -> Option<String> {
    let bytes = source.as_bytes();
    if offset == 0 {
        return None;
    }
    let mut pos = offset - 1;
    // Skip spaces
    while pos > 0 && bytes[pos] == b' ' {
        pos -= 1;
    }
    if bytes[pos] == b' ' {
        return None;
    }
    // Now pos is at the last char of the identifier
    let end = pos + 1;
    while pos > 0
        && (bytes[pos - 1].is_ascii_alphanumeric()
            || bytes[pos - 1] == b'_'
            || bytes[pos - 1] == b'\'')
    {
        pos -= 1;
    }
    let name = &source[pos..end];
    if name.is_empty() || !name.as_bytes()[0].is_ascii_alphabetic() {
        return None;
    }
    Some(name.to_string())
}

/// Like `find_active_call`, but handles the case where the cursor is just past
/// an App expression (user typed a space to start the next argument).
/// Skips back past whitespace, finds the App chain, and increments the param index.
pub fn find_call_near(program: &[Decl], source: &str, offset: usize) -> Option<(String, usize)> {
    let bytes = source.as_bytes();
    let mut pos = offset;
    while pos > 0 && bytes[pos - 1] == b' ' {
        pos -= 1;
    }
    if pos == offset || pos == 0 {
        return None;
    }
    // pos is now right after the last non-space char; use pos-1 to be inside the expression
    find_active_call(program, pos - 1).map(|(name, active)| (name, active + 1))
}

/// Find the function being called at the cursor and which argument is active.
/// Returns (function_name, active_parameter_index).
pub fn find_active_call(program: &[Decl], offset: usize) -> Option<(String, usize)> {
    for decl in program {
        if let Some(result) = find_call_in_decl(decl, offset) {
            return Some(result);
        }
    }
    None
}

fn contains(span: &dylang::token::Span, offset: usize) -> bool {
    // End-inclusive: cursor right after the last char of an expression
    // is still "in" that call context (user may still be typing the arg).
    offset >= span.start && offset <= span.end
}

fn find_call_in_decl(decl: &Decl, offset: usize) -> Option<(String, usize)> {
    match decl {
        Decl::FunBinding {
            params, body, span, ..
        } => {
            if !contains(span, offset) {
                return None;
            }
            for pat in params {
                if let Some(r) = find_call_in_pat(pat, offset) {
                    return Some(r);
                }
            }
            find_call_in_expr(body, offset)
        }
        Decl::ImplDef { methods, span, .. } => {
            if !contains(span, offset) {
                return None;
            }
            for (_, _, params, body) in methods {
                for pat in params {
                    if let Some(r) = find_call_in_pat(pat, offset) {
                        return Some(r);
                    }
                }
                if let Some(r) = find_call_in_expr(body, offset) {
                    return Some(r);
                }
            }
            None
        }
        Decl::Let { value, span, .. } => {
            if !contains(span, offset) {
                return None;
            }
            find_call_in_expr(value, offset)
        }
        _ => None,
    }
}

fn find_call_in_pat(_pat: &Pat, _offset: usize) -> Option<(String, usize)> {
    // Patterns don't contain function calls
    None
}

fn find_call_in_stmt(stmt: &Stmt, offset: usize) -> Option<(String, usize)> {
    match stmt {
        Stmt::Let { value, .. } => find_call_in_expr(value, offset),
        Stmt::LetFun { body, .. } => find_call_in_expr(body, offset),
        Stmt::Expr(expr) => find_call_in_expr(expr, offset),
    }
}

/// Walk the expression tree looking for App chains that contain the cursor.
/// We want the outermost App chain to count all arguments correctly.
fn find_call_in_expr(expr: &Expr, offset: usize) -> Option<(String, usize)> {
    if !contains(&expr.span, offset) {
        return None;
    }

    match &expr.kind {
        ExprKind::App { .. } => {
            // First try to find a call deeper in the arg (nested call takes priority)
            // e.g., in `foo (bar 1) 2` with cursor on `1`, we want `bar` not `foo`
            let (func_name, args) = unwrap_app_chain(expr);
            for arg in &args {
                if contains(&arg.span, offset)
                    && let Some(inner) = find_call_in_expr(arg, offset)
                {
                    return Some(inner);
                }
            }

            // Cursor is in this App chain but not in a nested call.
            // Determine which argument is active.
            let name = match &func_name.kind {
                ExprKind::Var { name } => name.clone(),
                ExprKind::QualifiedName { module, name } => format!("{}.{}", module, name),
                _ => return None,
            };

            // Find which argument the cursor is in or after
            let active = active_param_index(&args, offset);
            Some((name, active))
        }
        // Recurse into subexpressions
        ExprKind::Block { stmts, .. } => {
            for stmt in stmts {
                if let Some(r) = find_call_in_stmt(stmt, offset) {
                    return Some(r);
                }
            }
            None
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => find_call_in_expr(cond, offset)
            .or_else(|| find_call_in_expr(then_branch, offset))
            .or_else(|| find_call_in_expr(else_branch, offset)),
        ExprKind::Case {
            scrutinee, arms, ..
        } => {
            if let Some(r) = find_call_in_expr(scrutinee, offset) {
                return Some(r);
            }
            for arm in arms {
                if let Some(guard) = &arm.guard
                    && let Some(r) = find_call_in_expr(guard, offset)
                {
                    return Some(r);
                }
                if let Some(r) = find_call_in_expr(&arm.body, offset) {
                    return Some(r);
                }
            }
            None
        }
        ExprKind::Lambda { body, .. } => find_call_in_expr(body, offset),
        ExprKind::Tuple { elements, .. } => {
            for e in elements {
                if let Some(r) = find_call_in_expr(e, offset) {
                    return Some(r);
                }
            }
            None
        }
        ExprKind::BinOp { left, right, .. } => {
            find_call_in_expr(left, offset).or_else(|| find_call_in_expr(right, offset))
        }
        ExprKind::With { expr, .. } => find_call_in_expr(expr, offset),
        ExprKind::RecordCreate { fields, .. } => {
            for (_, _, e) in fields {
                if let Some(r) = find_call_in_expr(e, offset) {
                    return Some(r);
                }
            }
            None
        }
        ExprKind::RecordUpdate { record, fields, .. } => {
            if let Some(r) = find_call_in_expr(record, offset) {
                return Some(r);
            }
            for (_, _, e) in fields {
                if let Some(r) = find_call_in_expr(e, offset) {
                    return Some(r);
                }
            }
            None
        }
        ExprKind::FieldAccess { expr, .. } => find_call_in_expr(expr, offset),
        ExprKind::Do {
            bindings, success, ..
        } => {
            for (_, expr) in bindings {
                if let Some(r) = find_call_in_expr(expr, offset) {
                    return Some(r);
                }
            }
            find_call_in_expr(success, offset)
        }
        ExprKind::Resume { value, .. } => find_call_in_expr(value, offset),
        ExprKind::UnaryMinus { expr, .. } => find_call_in_expr(expr, offset),
        _ => None,
    }
}

/// Unwrap a left-nested App chain into the root function and a list of arguments.
/// `App(App(f, a0), a1)` -> (f, [a0, a1])
fn unwrap_app_chain(expr: &Expr) -> (&Expr, Vec<&Expr>) {
    let mut args = Vec::new();
    let mut current = expr;
    while let ExprKind::App { func, arg, .. } = &current.kind {
        args.push(arg.as_ref());
        current = func.as_ref();
    }
    args.reverse();
    (current, args)
}

/// Determine which parameter is active based on cursor offset and argument spans.
fn active_param_index(args: &[&Expr], offset: usize) -> usize {
    for (i, arg) in args.iter().enumerate() {
        if offset <= arg.span.end {
            return i;
        }
    }
    // Cursor is past all existing args -- next parameter
    args.len()
}

/// Build a SignatureInformation for a function, using its annotation if available.
pub fn build_signature(
    name: &str,
    program: &[Decl],
    result: &CheckResult,
) -> Option<SignatureInformation> {
    // Try annotation first (has labels)
    if let Some(sig) = build_from_annotation(name, program) {
        return Some(sig);
    }

    // Fall back to env type
    build_from_env(name, result)
}

fn build_from_annotation(name: &str, program: &[Decl]) -> Option<SignatureInformation> {
    for decl in program {
        if let Decl::FunAnnotation {
            name: fn_name,
            params,
            return_type,
            effects,
            ..
        } = decl
        {
            if fn_name != name {
                continue;
            }

            let param_infos: Vec<ParameterInformation> = params
                .iter()
                .map(|(label, ty)| {
                    let label_str = if label.starts_with('_') {
                        format_type_expr(ty)
                    } else {
                        format!("{}: {}", label, format_type_expr(ty))
                    };
                    ParameterInformation {
                        label: ParameterLabel::Simple(label_str),
                        documentation: None,
                    }
                })
                .collect();

            let params_display: Vec<String> = params
                .iter()
                .map(|(label, ty)| {
                    if label.starts_with('_') {
                        format_type_expr(ty)
                    } else {
                        format!("({}: {})", label, format_type_expr(ty))
                    }
                })
                .collect();
            let mut sig_label = if params_display.is_empty() {
                format_type_expr(return_type)
            } else {
                format!(
                    "{} -> {}",
                    params_display.join(" -> "),
                    format_type_expr(return_type)
                )
            };
            if !effects.is_empty() {
                let effs: Vec<String> = effects
                    .iter()
                    .map(|e| {
                        if e.type_args.is_empty() {
                            e.name.clone()
                        } else {
                            let args: Vec<String> =
                                e.type_args.iter().map(format_type_expr).collect();
                            format!("{} {}", e.name, args.join(" "))
                        }
                    })
                    .collect();
                sig_label.push_str(&format!(" needs {{{}}}", effs.join(", ")));
            }

            return Some(SignatureInformation {
                label: sig_label,
                documentation: None,
                parameters: Some(param_infos),
                active_parameter: None,
            });
        }
    }
    None
}

fn build_from_env(name: &str, result: &CheckResult) -> Option<SignatureInformation> {
    let scheme = result.env.get(name)?;
    let ty = scheme.display_with_constraints(&result.sub);

    // Split arrow type into parameter strings: "Int -> String -> Bool" -> ["Int", "String"] + "Bool"
    let parts: Vec<&str> = ty.split(" -> ").collect();
    if parts.len() < 2 {
        return None;
    }

    let param_infos: Vec<ParameterInformation> = parts[..parts.len() - 1]
        .iter()
        .map(|p| ParameterInformation {
            label: ParameterLabel::Simple(p.to_string()),
            documentation: None,
        })
        .collect();

    Some(SignatureInformation {
        label: ty,
        documentation: None,
        parameters: Some(param_infos),
        active_parameter: None,
    })
}
