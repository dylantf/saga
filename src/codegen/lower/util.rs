use crate::ast::{BinOp, BitSegSpec, Expr, ExprKind, Lit, Pat};
use crate::codegen::cerl::{BinSegFlags, BinSegSize, BinSegType, CBinSeg, CExpr, CLit, Endianness};
use crate::typechecker::Type;
use std::collections::{BTreeSet, HashMap};

/// Look up a constructor's mangled Erlang atom from the pre-computed table.
/// Constructor names should already be resolved to the exact atom-table key.
///
/// When `origin_module` is set (e.g. lowering an imported handler body),
/// the lookup tries the source module's qualified entry first, then falls
/// through to the normal bare-name path. Only constructors that actually
/// belong to the origin module will have a qualified entry in the table;
/// prelude constructors (Ok, Err, etc.) with BEAM overrides will not, so
/// they correctly fall through to their override atoms.
pub(super) fn mangle_ctor_atom(
    name: &str,
    constructor_atoms: &HashMap<String, String>,
    origin_module: Option<&str>,
) -> String {
    if let Some(origin) = origin_module {
        let qualified = format!("{}.{}", origin, name);
        if let Some(atom) = constructor_atoms.get(&qualified) {
            return atom.clone();
        }
    }
    if let Some(atom) = constructor_atoms.get(name) {
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

/// Peel a chain of App nodes to find a `DictMethodAccess` head and its arguments.
/// Returns `Some((dict_expr, method_index, args))` if the head is a `DictMethodAccess`,
/// `None` otherwise. Used to recognize trait method calls (post-elaboration shape)
/// for evidence-threaded emission.
pub(super) fn collect_dict_method_call(expr: &Expr) -> Option<(&Expr, usize, Vec<&Expr>)> {
    let mut args: Vec<&Expr> = Vec::new();
    let mut current = expr;
    loop {
        match &current.kind {
            ExprKind::App { func, arg, .. } => {
                args.push(arg);
                current = func;
            }
            ExprKind::DictMethodAccess {
                dict, method_index, ..
            } => {
                args.reverse();
                return Some((dict.as_ref(), *method_index, args));
            }
            _ => return None,
        }
    }
}

/// Like `collect_fun_call`, but for an `App` chain whose ultimate head is a
/// `Lambda` literal — `(fun x -> ...) y z`. Returns `Some((lambda, args))`
/// where `lambda` is the head Lambda expr and `args` are the supplied
/// arguments in order.
pub(super) fn collect_lambda_head_call(expr: &Expr) -> Option<(&Expr, Vec<&Expr>)> {
    let mut args: Vec<&Expr> = Vec::new();
    let mut current = expr;
    loop {
        match &current.kind {
            ExprKind::App { func, arg, .. } => {
                args.push(arg);
                current = func;
            }
            ExprKind::Lambda { .. } => {
                if args.is_empty() {
                    return None;
                }
                args.reverse();
                return Some((current, args));
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

/// True if any effect row along the function arrow has an open tail
/// (`needs {Foo, ..e}`). Used by the call-effects pre-pass to distinguish
/// `StaticOps` (closed-row callees, project at the call boundary) from
/// `RowForwarded` (open-row callees, forward full evidence).
pub fn has_open_effect_row(ty: &Type) -> bool {
    let mut current = ty;
    while let Type::Fun(_, ret, row) = current {
        if !row.tails.is_empty() {
            return true;
        }
        current = ret;
    }
    false
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

/// Phase-3 variant of [`arity_and_effects_from_type`] that also reports
/// whether any effect row along the arrow has an open tail. Returns
/// `(user_arity, sorted_effect_names, has_open_row)`.
///
/// Under the evidence-passing convention, `user_arity` is the logical
/// parameter count seen by source code: it does not include the
/// `_Evidence` or `_ReturnK` parameters appended at lowering. The
/// `has_open_row` flag chooses between `StaticOps` (closed-row, project at
/// call sites against a known `EvidenceLayout`) and `RowForwarded`
/// (open-row, forward full ambient evidence).
pub fn arity_and_evidence_from_type(ty: &Type) -> (usize, Vec<String>, bool) {
    let (user_arity, effects) = arity_and_effects_from_type(ty);
    let is_open_row = has_open_effect_row(ty);
    (user_arity, effects, is_open_row)
}

/// Extract per-parameter absorbed effects from a function type.
/// Returns a map of param_index -> sorted effect names for parameters
/// that have EffArrow types (i.e., callbacks that carry effects).
pub(crate) fn param_absorbed_effects_from_type(ty: &Type) -> HashMap<usize, Vec<String>> {
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

/// Extract the source-level parameter types from a function type.
pub(crate) fn param_types_from_type(ty: &Type) -> Vec<Type> {
    let mut params = Vec::new();
    let mut current = ty;
    while let Type::Fun(param, ret, _) = current {
        params.push((**param).clone());
        current = ret;
    }
    params
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
