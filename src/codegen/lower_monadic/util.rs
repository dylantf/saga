//! Local utilities for the monadic lowerer

use std::collections::HashMap;

use crate::ast::{BitSegSpec, Lit};
use crate::codegen::cerl::{
    BinSegFlags, BinSegSize, BinSegType, CArm, CBinSeg, CExpr, CLit, CPat, Endianness,
};

/// Map a Saga identifier to a Core Erlang variable name.
///
/// Core Erlang variables must start with an uppercase letter or underscore.
/// Source-lowercase names get capitalized; anything else (already-uppercase,
/// digits, symbols) is prefixed with `_`.
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

/// Build `{Tag, Marker, Value}` for routed handler-control results.
pub(super) fn marked_control_tuple(tag: &str, marker: CExpr, value: CExpr) -> CExpr {
    CExpr::Tuple(vec![CExpr::Lit(CLit::Atom(tag.to_string())), marker, value])
}

/// Case arm that propagates a foreign routed control result unchanged.
pub(super) fn propagate_marked_control_arm(
    tag: &str,
    marker_var: String,
    value_var: String,
) -> CArm {
    CArm {
        pat: CPat::Tuple(vec![
            CPat::Lit(CLit::Atom(tag.to_string())),
            CPat::Var(marker_var.clone()),
            CPat::Var(value_var.clone()),
        ]),
        guard: None,
        body: marked_control_tuple(tag, CExpr::Var(marker_var), CExpr::Var(value_var)),
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
pub(super) fn lower_lit_atom(lit: &Lit) -> CExpr {
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
pub(super) fn lower_string_to_binary(s: &str) -> CExpr {
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
pub(super) fn mangle_ctor_atom(name: &str, ctors: &HashMap<String, String>) -> String {
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
            // Maybe's constructors are ordinary stdlib ADT tags in the new
            // path. Keep the historical bare-name overrides below for legacy
            // runtime bridge values, but do not apply them to qualified
            // references such as `Std.Maybe.Nothing`.
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
        "Just" => Some("just"),
        "Nothing" => Some("nothing"),
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
/// this helper so bridge callbacks and legacy-Maybe normalization cannot drift
/// between the direct-call and wrapper paths.
pub(super) fn lower_external_native_call(
    module: &str,
    function: &str,
    indexed_args: Vec<(usize, CExpr)>,
    evidence_var: &str,
) -> CExpr {
    let callback_shape = external_callback_arg(module, function);
    let call_args: Vec<CExpr> = indexed_args
        .into_iter()
        .map(|(idx, arg)| {
            if let Some((callback_idx, callback_arity)) = callback_shape
                && idx == callback_idx
            {
                external_callback_adapter_expr(arg, callback_arity, evidence_var)
            } else {
                arg
            }
        })
        .collect();
    let call = CExpr::Call(module.to_string(), function.to_string(), call_args);
    if external_returns_legacy_maybe(module, function) {
        normalize_legacy_maybe(call)
    } else {
        call
    }
}

fn external_callback_adapter_expr(
    callback_ce: CExpr,
    callback_arity: usize,
    evidence_var: &str,
) -> CExpr {
    let params: Vec<String> = (0..callback_arity)
        .map(|i| format!("_ExtCb{}", i))
        .collect();
    let k_var = "_ExtCbK".to_string();
    let v_var = "_ExtCbV".to_string();
    let id_k = CExpr::Fun(vec![v_var.clone()], Box::new(CExpr::Var(v_var)));
    let mut apply_args: Vec<CExpr> = params.iter().cloned().map(CExpr::Var).collect();
    apply_args.push(CExpr::Var(evidence_var.to_string()));
    apply_args.push(CExpr::Var(k_var.clone()));
    let apply_callback = CExpr::Apply(Box::new(callback_ce), apply_args);
    CExpr::Fun(
        params,
        Box::new(CExpr::Let(k_var, Box::new(id_k), Box::new(apply_callback))),
    )
}

fn external_callback_arg(module: &str, function: &str) -> Option<(usize, usize)> {
    match (module, function) {
        ("std_array_bridge", "map") => Some((0, 1)),
        ("std_array_bridge", "foldl") => Some((0, 2)),
        ("std_dict_bridge", "map_values") => Some((0, 1)),
        ("std_dict_bridge", "filter_entries") => Some((0, 2)),
        ("std_dict_bridge", "fold_entries") => Some((0, 3)),
        ("std_dict_bridge", "update") => Some((1, 1)),
        ("std_list_bridge", "sort_with") => Some((0, 2)),
        ("std_list_bridge", "sort_by") => Some((0, 1)),
        ("std_set_bridge", "map") | ("std_set_bridge", "filter") => Some((0, 1)),
        ("std_set_bridge", "fold") => Some((0, 2)),
        _ => None,
    }
}

fn external_returns_legacy_maybe(module: &str, function: &str) -> bool {
    matches!(
        (module, function),
        ("std_array_bridge", "get")
            | ("std_dict_bridge", "get")
            | ("std_env_bridge", "get")
            | ("std_float_bridge", "parse")
            | ("std_int_bridge", "parse")
            | ("std_int_bridge", "parse_hex")
            | ("std_list_bridge", "nth")
            | ("std_regex_bridge", "match")
            | ("std_regex_bridge", "find")
            | ("std_string_bridge", "find")
            | ("std_string_bridge", "strip_prefix")
            | ("std_bitstring_bridge", "at")
    )
}

fn normalize_legacy_maybe(call: CExpr) -> CExpr {
    let value_var = "_MaybeValue".to_string();
    CExpr::Case(
        Box::new(call),
        vec![
            CArm {
                pat: CPat::Tuple(vec![
                    CPat::Lit(CLit::Atom("just".to_string())),
                    CPat::Var(value_var.clone()),
                ]),
                guard: None,
                body: CExpr::Tuple(vec![
                    CExpr::Lit(CLit::Atom("std_maybe_Just".to_string())),
                    CExpr::Var(value_var),
                ]),
            },
            CArm {
                pat: CPat::Tuple(vec![CPat::Lit(CLit::Atom("nothing".to_string()))]),
                guard: None,
                body: CExpr::Tuple(vec![CExpr::Lit(CLit::Atom(
                    "std_maybe_Nothing".to_string(),
                ))]),
            },
            CArm {
                pat: CPat::Var("_MaybeOther".to_string()),
                guard: None,
                body: CExpr::Var("_MaybeOther".to_string()),
            },
        ],
    )
}
