//! Local utilities for the monadic lowerer

use std::collections::HashMap;

use crate::ast::{BitSegSpec, Lit, TypeExpr};
use crate::codegen::cerl::{
    BinSegFlags, BinSegSize, BinSegType, CArm, CBinSeg, CExpr, CLit, CPat, Endianness,
};
use crate::codegen::monadic::ir::MExpr;
use crate::typechecker::Type;

use super::{LowerCtx, Lowerer};

pub(super) const ABORT_TAG: &str = "__saga_handler_abort";
pub(super) const VALUE_RESULT_TAG: &str = "__saga_value_result";

/// Map a Saga identifier to a Core Erlang variable name.
///
/// Core Erlang variables must start with an uppercase letter or underscore.
/// Source-lowercase names get capitalized; anything else (already-uppercase,
/// digits, symbols) is prefixed with `_`.
pub(crate) fn core_var(name: &str) -> String {
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

/// Build `{Tag, Marker, Value}` for routed handler-control results.
pub(super) fn marked_control_tuple(tag: &str, marker: CExpr, value: CExpr) -> CExpr {
    CExpr::Tuple(vec![CExpr::Lit(CLit::Atom(tag.to_string())), marker, value])
}

/// Match `{Tag, Marker, Value}` for routed handler-control results.
pub(super) fn marked_control_pattern(tag: &str, marker: CPat, value_var: String) -> CPat {
    CPat::Tuple(vec![
        CPat::Lit(CLit::Atom(tag.to_string())),
        marker,
        CPat::Var(value_var),
    ])
}

/// Match `{Tag, MarkerVar, ValueVar}` and bind both routed fields.
pub(super) fn marked_control_var_pattern(tag: &str, marker_var: String, value_var: String) -> CPat {
    marked_control_pattern(tag, CPat::Var(marker_var), value_var)
}

/// `fun(V) -> V`: the local return continuation used at synchronous
/// Saga/native boundaries where a uniform-CPS Saga callback must produce a
/// direct Erlang value.
pub(super) fn identity_k(value_param: impl Into<String>) -> CExpr {
    let value_param = value_param.into();
    CExpr::Fun(vec![value_param.clone()], Box::new(CExpr::Var(value_param)))
}

/// Case arm that propagates a foreign routed control result unchanged.
pub(super) fn propagate_marked_control_arm(
    tag: &str,
    marker_var: String,
    value_var: String,
) -> CArm {
    CArm {
        pat: marked_control_var_pattern(tag, marker_var.clone(), value_var.clone()),
        guard: None,
        body: marked_control_tuple(tag, CExpr::Var(marker_var), CExpr::Var(value_var)),
    }
}

fn apply_marked_control_arm_to_k(
    tag: &str,
    marker_var: String,
    value_var: String,
    return_k: &str,
) -> CArm {
    CArm {
        pat: marked_control_var_pattern(tag, marker_var.clone(), value_var.clone()),
        guard: None,
        body: CExpr::Apply(
            Box::new(CExpr::Var(return_k.to_string())),
            vec![marked_control_tuple(
                tag,
                CExpr::Var(marker_var),
                CExpr::Var(value_var),
            )],
        ),
    }
}

impl<'ctx> Lowerer<'ctx> {
    /// Arms that bubble a routed handler-control result unchanged until the
    /// owning result delimiter catches it.
    pub(super) fn propagate_marked_control_arms(&mut self) -> Vec<CArm> {
        let other_value_marker = self.fresh_helper_name();
        let other_value = self.fresh_helper_name();
        let other_abort_marker = self.fresh_helper_name();
        let other_abort_value = self.fresh_helper_name();
        vec![
            propagate_marked_control_arm(VALUE_RESULT_TAG, other_value_marker, other_value),
            propagate_marked_control_arm(ABORT_TAG, other_abort_marker, other_abort_value),
        ]
    }

    /// Arms that forward a foreign routed handler-control result through the
    /// current continuation rather than unwrapping it at the wrong delimiter.
    pub(super) fn apply_marked_control_arms_to_k(&mut self, return_k: &str) -> Vec<CArm> {
        let other_value_marker = self.fresh_helper_name();
        let other_value = self.fresh_helper_name();
        let other_abort_marker = self.fresh_helper_name();
        let other_abort_value = self.fresh_helper_name();
        vec![
            apply_marked_control_arm_to_k(
                VALUE_RESULT_TAG,
                other_value_marker,
                other_value,
                return_k,
            ),
            apply_marked_control_arm_to_k(
                ABORT_TAG,
                other_abort_marker,
                other_abort_value,
                return_k,
            ),
        ]
    }

    /// Run a handler `finally` block with a local dummy return continuation,
    /// then evaluate `next`. The cleanup result is discarded; routed control
    /// tuples inside `next` are deliberately untouched.
    pub(super) fn sequence_finally_then(
        &mut self,
        finally_expr: &MExpr,
        ctx: &LowerCtx,
        next: CExpr,
    ) -> CExpr {
        let cleanup_k = self.fresh_helper_name();
        let cleanup_ctx = ctx.without_finally().with_return_k(cleanup_k.clone());
        let cleanup_ce = self.lower_expr(finally_expr, &cleanup_ctx);
        CExpr::Let(
            cleanup_k,
            Box::new(identity_k("_")),
            Box::new(CExpr::Let(
                "_".to_string(),
                Box::new(cleanup_ce),
                Box::new(next),
            )),
        )
    }
}

/// Lower a literal to its `CLit` representation for use in a `CExpr::Lit`.
///
/// Strings are NOT handled here — the old lowerer routes string-as-value
/// through a binary expression (`lower_string_to_binary`). Callers that may
/// see a `Lit::String` should use [`lower_lit_atom`] instead.
pub(super) fn lower_lit(lit: &Lit) -> CLit {
    match lit {
        Lit::Int(_, n) => CLit::Int(*n),
        Lit::Float(_, f) => CLit::Float(*f),
        Lit::Bool(true) => CLit::Atom("true".to_string()),
        Lit::Bool(false) => CLit::Atom("false".to_string()),
        Lit::Unit => CLit::Atom("unit".to_string()),
        Lit::String(s, _) => CLit::Str(s.clone()),
    }
}

/// Lower a Saga `Lit` as a value-producing `CExpr`.
///
/// Mirrors the old lowerer's `ExprKind::Lit` arm: numeric / bool / unit
/// become bare `CExpr::Lit`s; strings expand to a `CExpr::Binary` (Saga
/// strings are byte-binary at runtime, not Erlang list-of-codepoints).
/// Multiline strings get escape-processed before expansion.
pub(crate) fn lower_lit_atom(lit: &Lit) -> CExpr {
    match lit {
        Lit::String(s, kind) => {
            let resolved = if kind.is_multiline() {
                process_string_escapes(s)
            } else {
                s.clone()
            };
            lower_string_to_binary(&resolved)
        }
        _ => CExpr::Lit(lower_lit(lit)),
    }
}

/// Lower a string value to a `CExpr::Binary` of per-byte segments.
pub(crate) fn lower_string_to_binary(s: &str) -> CExpr {
    CExpr::Binary(s.as_bytes().iter().map(|&b| CBinSeg::Byte(b)).collect())
}

/// Process Saga escape sequences in a raw multiline-string source.
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

/// Shared segment metadata resolution for bitstring expressions.
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

/// Resolve a constructor name to its mangled Erlang atom via the
/// pre-computed table. Falls back to the source name when no entry exists.
///
/// The new path does not yet thread an "origin module" (the old lowerer
/// needs it for imported-handler bodies); when a sub-step requires that
/// behavior, extend this helper rather than reaching into the old code.
pub(crate) fn mangle_ctor_atom(name: &str, ctors: &HashMap<String, String>) -> String {
    if matches!(name, "Ok" | "Err")
        && let Some(atom) = beam_ctor_override(name)
    {
        return atom.to_string();
    }
    if name.ends_with(".Ok") {
        return "ok".to_string();
    }
    if name.ends_with(".Err") {
        return "error".to_string();
    }
    if let Some(atom) = ctors.get(name) {
        return atom.clone();
    }
    if name.contains('.') {
        let mut parts: Vec<&str> = name.split('.').collect();
        if let Some(ctor) = parts.pop() {
            if matches!(ctor, "Just" | "Nothing") {
                let module = parts.join("_").to_lowercase();
                if module == "std_maybe" || module == "maybe" {
                    return format!("std_maybe_{}", ctor);
                }
            }
            if let Some(atom) = beam_ctor_override(ctor) {
                return atom.to_string();
            }
            let module = parts.join("_").to_lowercase();
            return format!("{}_{}", module, ctor);
        }
    }
    if !name.contains('.') {
        let mut matches = ctors.iter().filter_map(|(key, atom)| {
            key.rsplit('.')
                .next()
                .filter(|bare| *bare == name)
                .map(|_| atom.clone())
        });
        if let Some(first) = matches.next()
            && matches.next().is_none()
        {
            return first;
        }
    }
    name.to_string()
}

fn beam_ctor_override(name: &str) -> Option<&'static str> {
    match name {
        "Ok" => Some("ok"),
        "Err" => Some("error"),
        "True" => Some("true"),
        "False" => Some("false"),
        "Normal" => Some("normal"),
        "Shutdown" => Some("shutdown"),
        "Killed" => Some("killed"),
        "Noproc" => Some("noproc"),
        _ => None,
    }
}

/// Build a native Erlang external call from source-indexed user arguments.
///
/// Both saturated external applications and first-class external wrappers use
/// this helper so the direct-call and wrapper paths preserve the same raw
/// Erlang argument ordering and Unit filtering behavior.
pub(super) fn lower_external_native_call(
    module: &str,
    function: &str,
    indexed_args: Vec<(usize, CExpr)>,
) -> CExpr {
    // Callback adaptation (wrapping Saga uniform-CPS lambdas as native funs)
    // is the wrapper's responsibility — see `lower_external_wrapper` in
    // `decls.rs`. Direct saturated call sites bail and route through the
    // wrapper when any arg is function-typed (see `lower_saturated_external_app`
    // in `app.rs`), so by the time we reach here, indexed_args are
    // call-ready: lambdas have already been replaced with adapters at the
    // wrapper level, or the position simply has no callback.
    let call_args: Vec<CExpr> = indexed_args.into_iter().map(|(_, arg)| arg).collect();
    CExpr::Call(module.to_string(), function.to_string(), call_args)
}

/// True when a fully inferred function type has any function-typed parameter.
///
/// Direct saturated `@external` applications use this to decide whether they
/// must route through the generated wrapper so callback params are adapted
/// from Saga's uniform-CPS shape to native Erlang arity.
pub(super) fn type_has_function_param(ty: &Type) -> bool {
    let mut cur = ty;
    while let Type::Fun(param, ret, _) = cur {
        if matches!(param.as_ref(), Type::Fun(_, _, _)) {
            return true;
        }
        cur = ret;
    }
    false
}

/// Count arrows in a function-type `TypeExpr`. Returns `None` for non-function
/// types. `(a -> b)` -> `Some(1)`; `(a -> b -> c)` -> `Some(2)`;
/// `Int` -> `None`.
///
/// External wrappers use this to size the native-arity adapter wrapping a
/// function-typed callback param.
pub(super) fn type_expr_function_arity(ty: &TypeExpr) -> Option<usize> {
    fn count(ty: &TypeExpr) -> usize {
        match ty {
            TypeExpr::Arrow { to, .. } => 1 + count(to),
            TypeExpr::Labeled { inner, .. } => count(inner),
            _ => 0,
        }
    }
    let arity = count(ty);
    if arity == 0 { None } else { Some(arity) }
}
