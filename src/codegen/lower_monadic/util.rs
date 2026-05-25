//! Local utilities for the new lowerer.
//!
//! Copied (not imported) from the old lowerer per the agent-guide's
//! "no imports from frozen files" rule. Each helper here mirrors the
//! corresponding one in `src/codegen/lower/util.rs` so emitted Core Erlang
//! matches the old path's identifier conventions.

use std::collections::HashMap;

use crate::ast::Lit;
use crate::codegen::cerl::{CBinSeg, CExpr, CLit};

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
fn process_string_escapes(s: &str) -> String {
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

/// Resolve a constructor name to its mangled Erlang atom via the
/// pre-computed table. Falls back to the source name when no entry exists.
///
/// The new path does not yet thread an "origin module" (the old lowerer
/// needs it for imported-handler bodies); when a sub-step requires that
/// behavior, extend this helper rather than reaching into the old code.
pub(super) fn mangle_ctor_atom(name: &str, ctors: &HashMap<String, String>) -> String {
    ctors.get(name).cloned().unwrap_or_else(|| name.to_string())
}
