use crate::ast::{BinOp, BitSegSpec, Expr, ExprKind, Lit, Pat, Stmt};
use crate::codegen::cerl::{BinSegFlags, BinSegSize, BinSegType, CBinSeg, CExpr, CLit, Endianness};
use crate::typechecker::Type;
use std::collections::{BTreeSet, HashMap};

/// Look up a constructor's mangled Erlang atom from the pre-computed table.
/// Falls back to the bare name if not found.
pub(super) fn mangle_ctor_atom(name: &str, constructor_atoms: &HashMap<String, String>) -> String {
    if let Some(atom) = constructor_atoms.get(name) {
        return atom.clone();
    }
    // For qualified names not in the table, try the bare name
    if let Some(bare) = name.rsplit('.').next()
        && bare != name
        && let Some(atom) = constructor_atoms.get(bare)
    {
        return atom.clone();
    }
    name.to_string()
}

pub(super) fn lower_lit(lit: &Lit) -> CLit {
    match lit {
        Lit::Int(_, n) => CLit::Int(*n),
        Lit::Float(_, f) => CLit::Float(*f),
        Lit::Bool(true) => CLit::Atom("true".to_string()),
        Lit::Bool(false) => CLit::Atom("false".to_string()),
        Lit::Unit => CLit::Atom("unit".to_string()),
        Lit::String(s, kind) => {
            if kind.is_multiline() {
                // Multiline strings store raw source - process escapes at emit time
                CLit::Str(process_string_escapes(s))
            } else {
                CLit::Str(s.clone())
            }
        }
    }
}

/// Lower a string value to a binary expression.
pub(super) fn lower_string_to_binary(s: &str) -> CExpr {
    CExpr::Binary(s.as_bytes().iter().map(|&b| CBinSeg::Byte(b)).collect())
}

/// Process escape sequences in a raw string (multiline strings store raw source).
pub(super) fn process_string_escapes(s: &str) -> String {
    let mut out = String::new();
    let mut chars = s.chars();
    while let Some(ch) = chars.next() {
        if ch == '\\' {
            match chars.next() {
                Some('n') => out.push('\n'),
                Some('r') => out.push('\r'),
                Some('t') => out.push('\t'),
                Some('0') => out.push('\0'),
                Some('\\') => out.push('\\'),
                Some('"') => out.push('"'),
                Some('x') => {
                    let hi = chars.next().and_then(|c| c.to_digit(16));
                    let lo = chars.next().and_then(|c| c.to_digit(16));
                    if let (Some(h), Some(l)) = (hi, lo) {
                        out.push((h * 16 + l) as u8 as char);
                    }
                }
                Some(ch) => out.push(ch),
                None => {}
            }
        } else {
            out.push(ch);
        }
    }
    out
}

/// Mangle a saga variable name to a valid Core Erlang variable (uppercase start).
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

/// Map a saga BinOp + two already-bound var names to a CExpr.
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
        BinOp::FloatMod => cerl_call("math", "fmod", vec![l, r]),
        BinOp::Eq => cerl_call("erlang", "=:=", vec![l, r]),
        BinOp::NotEq => cerl_call("erlang", "=/=", vec![l, r]),
        BinOp::Lt => cerl_call("erlang", "<", vec![l, r]),
        BinOp::Gt => cerl_call("erlang", ">", vec![l, r]),
        BinOp::LtEq => cerl_call("erlang", "=<", vec![l, r]),
        BinOp::GtEq => cerl_call("erlang", ">=", vec![l, r]),
        BinOp::Concat => CExpr::Binary(vec![CBinSeg::BinaryAll(l), CBinSeg::BinaryAll(r)]),
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
/// Returns `Some((func_name, head_expr, args))` if the head is a Var, `None` otherwise.
/// The head_expr is the Var node itself (for NodeId-based resolution lookup).
pub(super) fn collect_fun_call(expr: &Expr) -> Option<(&str, &Expr, Vec<&Expr>)> {
    let mut args: Vec<&Expr> = Vec::new();
    let mut current = expr;
    loop {
        match &current.kind {
            ExprKind::App { func, arg, .. } => {
                args.push(arg);
                current = func;
            }
            ExprKind::Var { name, .. } => {
                args.reverse();
                return Some((name.as_str(), current, args));
            }
            _ => return None,
        }
    }
}

/// Like `collect_fun_call`, but for qualified names (`Module.func arg1 arg2`).
/// Returns `Some((module, func_name, head_expr, args))` if the head is a QualifiedName.
pub(super) fn collect_qualified_call(expr: &Expr) -> Option<(&str, &str, &Expr, Vec<&Expr>)> {
    let mut args: Vec<&Expr> = Vec::new();
    let mut current = expr;
    loop {
        match &current.kind {
            ExprKind::App { func, arg, .. } => {
                args.push(arg);
                current = func;
            }
            ExprKind::QualifiedName { module, name, .. } => {
                args.reverse();
                return Some((module.as_str(), name.as_str(), current, args));
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
        match &current.kind {
            ExprKind::App { func, arg, .. } => {
                args.push(arg);
                current = func;
            }
            ExprKind::Constructor { name, .. } => {
                args.reverse();
                return Some((name.as_str(), args));
            }
            _ => return None,
        }
    }
}

/// Peel a chain of App nodes to find an EffectCall head and its arguments.
/// Returns `Some((op_name, qualifier, args))` if found.
pub(super) fn collect_effect_call_expr(
    expr: &Expr,
) -> Option<(&Expr, &str, Option<&str>, Vec<&Expr>)> {
    let mut args: Vec<&Expr> = Vec::new();
    let mut current = expr;
    loop {
        match &current.kind {
            ExprKind::App { func, arg, .. } => {
                args.push(arg);
                current = func;
            }
            ExprKind::EffectCall {
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
                if args.is_empty() {
                    return None;
                }
                return Some((current, name.as_str(), qualifier.as_deref(), args));
            }
            _ => return None,
        }
    }
}

pub(super) fn collect_effect_call(expr: &Expr) -> Option<(&str, Option<&str>, Vec<&Expr>)> {
    collect_effect_call_expr(expr).map(|(_, name, qualifier, args)| (name, qualifier, args))
}

/// Check if an expression contains effect calls nested inside if/case/block
/// branches. These aren't detected by `collect_effect_call` (which only finds
/// direct effect calls at the expression root) and need special CPS handling
/// so that abort-style handlers can skip the outer continuation.
pub(super) fn has_nested_effect_call(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::If {
            then_branch,
            else_branch,
            ..
        } => branch_has_effect(then_branch) || branch_has_effect(else_branch),
        ExprKind::Case { arms, .. } => arms.iter().any(|arm| branch_has_effect(&arm.node.body)),
        ExprKind::Block { stmts, .. } => stmts.iter().any(|s| match &s.node {
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

/// Convert a module path like `["Foo", "Bar", "Baz"]` to an Erlang module atom
/// name like `"foo_bar_baz"`.
pub(super) fn module_name_to_erlang(path: &[String]) -> String {
    path.iter()
        .map(|s| s.to_lowercase())
        .collect::<Vec<_>>()
        .join("_")
}

/// Count dictionary parameters from trait constraints.
/// Excludes operator-dispatched traits (Num, Eq) which use BIF dispatch instead.
pub fn dict_param_count(constraints: &[(String, u32, Vec<crate::typechecker::Type>)]) -> usize {
    constraints
        .iter()
        .filter(|(trait_name, _, _)| trait_name != "Num" && trait_name != "Eq")
        .count()
}

/// Derive base arity and effect names from a typechecker `Type`.
/// Returns `(base_param_count, sorted_effect_names)`.
/// The expanded arity (for codegen) is: base + effects.len() + if effects is non-empty { 1 } else { 0 }.
pub fn arity_and_effects_from_type(ty: &Type) -> (usize, Vec<String>) {
    let mut arity = 0;
    let mut effects = BTreeSet::new();
    let mut current = ty;
    while let Type::Fun(_param, ret, row) = current {
        arity += 1;
        for entry in &row.effects {
            effects.insert(entry.name.clone());
        }
        current = ret;
    }
    (arity, effects.into_iter().collect())
}

/// Extract per-parameter absorbed effects from a function type.
/// Returns a map of param_index -> sorted effect names for parameters
/// that have EffArrow types (i.e., callbacks that carry effects).
pub(super) fn param_absorbed_effects_from_type(ty: &Type) -> HashMap<usize, Vec<String>> {
    let mut result = HashMap::new();
    let mut current = ty;
    let mut param_index = 0;
    while let Type::Fun(param, ret, _) = current {
        let effs = collect_effarrow_effects(param);
        if !effs.is_empty() {
            result.insert(param_index, effs);
        }
        param_index += 1;
        current = ret;
    }
    result
}

/// Collect effect names from a Fun type (used for parameter types).
fn collect_effarrow_effects(ty: &Type) -> Vec<String> {
    let mut effects = BTreeSet::new();
    let mut current = ty;
    while let Type::Fun(_, ret, row) = current {
        for entry in &row.effects {
            effects.insert(entry.name.clone());
        }
        current = ret;
    }
    effects.into_iter().collect()
}

/// Shared segment metadata resolution for bitstring expressions and patterns.
/// Given a set of specifiers, returns (type, default_size, unit).
pub(super) fn resolve_bit_segment_meta(specs: &[BitSegSpec]) -> (BinSegType, i64, u8) {
    let has = |s: &BitSegSpec| specs.contains(s);
    if has(&BitSegSpec::Float) {
        (BinSegType::Float, 64, 1)
    } else if has(&BitSegSpec::Binary) {
        (BinSegType::Binary, 8, 8)
    } else if has(&BitSegSpec::Utf8) {
        (BinSegType::Utf8, 0, 0)
    } else {
        (BinSegType::Integer, 8, 1)
    }
}

/// Build flags from specifiers.
pub(super) fn resolve_bit_segment_flags(specs: &[BitSegSpec]) -> BinSegFlags {
    let has = |s: &BitSegSpec| specs.contains(s);
    BinSegFlags {
        signed: has(&BitSegSpec::Signed),
        endianness: if has(&BitSegSpec::Little) {
            Endianness::Little
        } else if has(&BitSegSpec::Native) {
            Endianness::Native
        } else {
            Endianness::Big
        },
    }
}

/// Build the size expression for a segment, given the lowered size (if any)
/// and the resolved metadata.
pub(super) fn resolve_bit_segment_size(
    size: Option<CExpr>,
    type_name: &BinSegType,
    default_size: i64,
) -> BinSegSize {
    if matches!(type_name, BinSegType::Utf8) {
        BinSegSize::Utf8
    } else {
        match size {
            Some(s) => BinSegSize::Expr(s),
            None => BinSegSize::Expr(CExpr::Lit(CLit::Int(default_size))),
        }
    }
}
