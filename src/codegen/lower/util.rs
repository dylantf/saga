use crate::ast::{BinOp, Expr, Lit, Pat, Stmt, TypeExpr};
use crate::codegen::cerl::{CExpr, CLit};
use crate::typechecker::Type;
use std::collections::{BTreeSet, HashMap};

/// Map a constructor name to its Erlang atom, applying BEAM convention
/// overrides for Result/Maybe and module-prefix mangling for user types.
///
/// Result: Ok -> "ok", Err -> "error"
/// Maybe:  Nothing -> "undefined" (Just is special-cased structurally, not here)
/// Module types: Circle -> "shapes_Circle"
/// Prelude builtins: True -> "True", False -> "False"
pub(super) fn mangle_ctor_atom(name: &str, constructor_modules: &HashMap<String, String>) -> String {
    // BEAM convention overrides for Result, Maybe, Bool, and ExitReason
    match name {
        "Ok" => return "ok".to_string(),
        "Err" => return "error".to_string(),
        "Nothing" => return "undefined".to_string(),
        "True" => return "true".to_string(),
        "False" => return "false".to_string(),
        // Just is handled structurally (bare value, no tag) -- not here
        // ExitReason constructors map to Erlang exit reason atoms
        "Normal" => return "normal".to_string(),
        "Shutdown" => return "shutdown".to_string(),
        "Killed" => return "killed".to_string(),
        "Noproc" => return "noproc".to_string(),
        // Other(String) stays as-is (tuple form)
        _ => {}
    }
    if let Some(module) = constructor_modules.get(name) {
        format!("{}_{}", module, name)
    } else {
        name.to_string()
    }
}

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
        BinOp::FloatDiv => cerl_call("erlang", "/", vec![l, r]),
        BinOp::IntDiv => cerl_call("erlang", "div", vec![l, r]),
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

/// Like `collect_fun_call`, but for qualified names (`Module.func arg1 arg2`).
/// Returns `Some((module, func_name, args))` if the head is a QualifiedName.
pub(super) fn collect_qualified_call(expr: &Expr) -> Option<(&str, &str, Vec<&Expr>)> {
    let mut args: Vec<&Expr> = Vec::new();
    let mut current = expr;
    loop {
        match current {
            Expr::App { func, arg, .. } => {
                args.push(arg);
                current = func;
            }
            Expr::QualifiedName { module, name, .. } => {
                args.reverse();
                return Some((module.as_str(), name.as_str(), args));
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
                name,
                qualifier,
                args: direct_args,
                ..
            } => {
                debug_assert!(
                    direct_args.is_empty(),
                    "EffectCall.args should be empty (args are wrapped via App nodes)"
                );
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

/// Check if an expression contains effect calls nested inside if/case/block
/// branches. These aren't detected by `collect_effect_call` (which only finds
/// direct effect calls at the expression root) and need special CPS handling
/// so that abort-style handlers can skip the outer continuation.
pub(super) fn has_nested_effect_call(expr: &Expr) -> bool {
    match expr {
        Expr::If {
            then_branch,
            else_branch,
            ..
        } => branch_has_effect(then_branch) || branch_has_effect(else_branch),
        Expr::Case { arms, .. } => arms.iter().any(|arm| branch_has_effect(&arm.body)),
        Expr::Block { stmts, .. } => stmts.iter().any(|s| match s {
            Stmt::Expr(e) => branch_has_effect(e),
            Stmt::Let { value, .. } => branch_has_effect(value),
            Stmt::LetFun { body, .. } => branch_has_effect(body),
        }),
        _ => false,
    }
}

/// Check if an expression is or contains an effect call (direct or nested).
fn branch_has_effect(expr: &Expr) -> bool {
    collect_effect_call(expr).is_some() || has_nested_effect_call(expr)
}

/// Recursively collect all effect names from `needs` clauses in a TypeExpr.
pub(super) fn collect_type_effects(ty: &TypeExpr) -> BTreeSet<String> {
    match ty {
        TypeExpr::Arrow(from, to, needs) => {
            let mut effects: BTreeSet<String> = needs.iter().map(|e| e.name.clone()).collect();
            effects.extend(collect_type_effects(from));
            effects.extend(collect_type_effects(to));
            effects
        }
        TypeExpr::App(a, b) => {
            let mut effects = collect_type_effects(a);
            effects.extend(collect_type_effects(b));
            effects
        }
        TypeExpr::Named(_) | TypeExpr::Var(_) => BTreeSet::new(),
    }
}

/// Convert a module path like `["Foo", "Bar", "Baz"]` to an Erlang module atom
/// name like `"foo_bar_baz"`.
pub(super) fn module_name_to_erlang(path: &[String]) -> String {
    path.iter()
        .map(|s| s.to_lowercase())
        .collect::<Vec<_>>()
        .join("_")
}

/// Derive base arity and effect names from a typechecker `Type`.
/// Returns `(base_param_count, sorted_effect_names)`.
/// The expanded arity (for codegen) is: base + effects.len() + if effects is non-empty { 1 } else { 0 }.
pub(super) fn arity_and_effects_from_type(ty: &Type) -> (usize, Vec<String>) {
    let mut arity = 0;
    let mut effects = BTreeSet::new();
    let mut current = ty;
    loop {
        match current {
            Type::Arrow(_, ret) => {
                arity += 1;
                current = ret;
            }
            Type::EffArrow(_, ret, effs) => {
                arity += 1;
                for (eff, _) in effs {
                    effects.insert(eff.clone());
                }
                current = ret;
            }
            _ => break,
        }
    }
    (arity, effects.into_iter().collect())
}

/// Extract per-parameter absorbed effects from a function type.
/// Returns a map of param_index -> sorted effect names for parameters
/// that have EffArrow types (i.e., callbacks that carry effects).
pub(super) fn param_absorbed_effects_from_type(
    ty: &Type,
) -> HashMap<usize, Vec<String>> {
    let mut result = HashMap::new();
    let mut current = ty;
    let mut param_index = 0;
    loop {
        match current {
            Type::Arrow(param, ret) => {
                // Check if the parameter itself is an EffArrow
                let effs = collect_effarrow_effects(param);
                if !effs.is_empty() {
                    result.insert(param_index, effs);
                }
                param_index += 1;
                current = ret;
            }
            Type::EffArrow(param, ret, _) => {
                let effs = collect_effarrow_effects(param);
                if !effs.is_empty() {
                    result.insert(param_index, effs);
                }
                param_index += 1;
                current = ret;
            }
            _ => break,
        }
    }
    result
}

/// Collect effect names from an EffArrow type (used for parameter types).
fn collect_effarrow_effects(ty: &Type) -> Vec<String> {
    let mut effects = BTreeSet::new();
    let mut current = ty;
    loop {
        match current {
            Type::EffArrow(_, ret, effs) => {
                for (eff, _) in effs {
                    effects.insert(eff.clone());
                }
                current = ret;
            }
            Type::Arrow(_, ret) => {
                current = ret;
            }
            _ => break,
        }
    }
    effects.into_iter().collect()
}
