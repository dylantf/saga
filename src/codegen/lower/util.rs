use crate::ast::{BinOp, Expr, Lit, Pat};
use crate::codegen::cerl::{CExpr, CLit};

pub(super) fn lower_lit(lit: &Lit) -> CLit {
    match lit {
        Lit::Int(n) => CLit::Int(*n),
        Lit::Float(f) => CLit::Float(*f),
        Lit::Bool(true) => CLit::Atom("true".to_string()),
        Lit::Bool(false) => CLit::Atom("false".to_string()),
        Lit::Unit => CLit::Atom("unit".to_string()),
        Lit::String(s) => CLit::Str(s.clone()),
    }
}

/// Mangle a dylang variable name to a valid Core Erlang variable (uppercase start).
pub(super) fn core_var(name: &str) -> String {
    let mut chars = name.chars();
    match chars.next() {
        None => "_".to_string(),
        Some(first) => {
            let mut result = String::new();
            if first.is_lowercase() {
                result.push(first.to_ascii_uppercase());
            } else {
                result.push('_');
                result.push(first);
            }
            result.extend(chars);
            result
        }
    }
}

pub(super) fn cerl_call(module: &str, func: &str, args: Vec<CExpr>) -> CExpr {
    CExpr::Call(module.to_string(), func.to_string(), args)
}

/// Map a dylang BinOp + two already-bound var names to a CExpr.
pub(super) fn binop_call(op: &BinOp, left: &str, right: &str) -> CExpr {
    let l = CExpr::Var(left.to_string());
    let r = CExpr::Var(right.to_string());
    match op {
        BinOp::Add => cerl_call("erlang", "+", vec![l, r]),
        BinOp::Sub => cerl_call("erlang", "-", vec![l, r]),
        BinOp::Mul => cerl_call("erlang", "*", vec![l, r]),
        BinOp::Div => cerl_call("erlang", "/", vec![l, r]),
        BinOp::Mod => cerl_call("erlang", "rem", vec![l, r]),
        BinOp::Eq => cerl_call("erlang", "=:=", vec![l, r]),
        BinOp::NotEq => cerl_call("erlang", "=/=", vec![l, r]),
        BinOp::Lt => cerl_call("erlang", "<", vec![l, r]),
        BinOp::Gt => cerl_call("erlang", ">", vec![l, r]),
        BinOp::LtEq => cerl_call("erlang", "=<", vec![l, r]),
        BinOp::GtEq => cerl_call("erlang", ">=", vec![l, r]),
        BinOp::Concat => cerl_call("erlang", "++", vec![l, r]),
        BinOp::And | BinOp::Or => unreachable!(),
    }
}

/// Map a simple single-binding pattern to a variable name, if possible.
pub(super) fn pat_binding_var(pat: &Pat) -> Option<String> {
    match pat {
        Pat::Var { name, .. } => Some(core_var(name)),
        _ => None,
    }
}

/// Peel a chain of App nodes to find a named-function head (Var) and its arguments.
/// Returns `Some((func_name, args))` if the head is a Var, `None` otherwise.
pub(super) fn collect_fun_call(expr: &Expr) -> Option<(&str, Vec<&Expr>)> {
    let mut args: Vec<&Expr> = Vec::new();
    let mut current = expr;
    loop {
        match current {
            Expr::App { func, arg, .. } => {
                args.push(arg);
                current = func;
            }
            Expr::Var { name, .. } => {
                args.reverse();
                return Some((name.as_str(), args));
            }
            _ => return None,
        }
    }
}

/// Peel a chain of App nodes to find a Constructor head and its arguments.
pub(super) fn collect_ctor_call(expr: &Expr) -> Option<(&str, Vec<&Expr>)> {
    let mut args: Vec<&Expr> = Vec::new();
    let mut current = expr;
    loop {
        match current {
            Expr::App { func, arg, .. } => {
                args.push(arg);
                current = func;
            }
            Expr::Constructor { name, .. } => {
                args.reverse();
                return Some((name.as_str(), args));
            }
            _ => return None,
        }
    }
}

/// Peel a chain of App nodes to find an EffectCall head and its arguments.
/// Returns `Some((op_name, qualifier, args))` if found.
pub(super) fn collect_effect_call(expr: &Expr) -> Option<(&str, Option<&str>, Vec<&Expr>)> {
    let mut args: Vec<&Expr> = Vec::new();
    let mut current = expr;
    loop {
        match current {
            Expr::App { func, arg, .. } => {
                args.push(arg);
                current = func;
            }
            Expr::EffectCall {
                name, qualifier, ..
            } => {
                args.reverse();
                return Some((name.as_str(), qualifier.as_deref(), args));
            }
            _ => return None,
        }
    }
}

/// Best-effort: return the record type name from an expression, for use when
/// resolving field positions. Only works when the expression is a literal
/// RecordCreate; otherwise the typechecker would need to be consulted.
pub(super) fn field_access_record_name(expr: &Expr) -> Option<&str> {
    if let Expr::RecordCreate { name, .. } = expr {
        return Some(name.as_str());
    }
    None
}
