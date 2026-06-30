//! Declaration checking and multi-pass registration.
//!
//! The large `impl Checker` is split across submodules by concern:
//! - `program`     — top-level driver, multi-pass registration, imports/externals
//! - `functions`   — `fun` clause checking, scheme building, exhaustiveness
//! - `types`       — type/alias/record definition registration
//! - `handlers`    — effect stub/op registration and handler checking
//! - `constraints` — pending-constraint and supertrait solving
//!
//! Shared free helpers and `FunctionAnnotation` live here and are re-exported to
//! the submodules via `use super::*`.

pub(crate) use std::collections::HashMap;

pub(crate) use crate::ast::{self, Decl, TypeParam};
pub(crate) use crate::token::Span;

pub(crate) use crate::typechecker::result::CheckResult;
pub(crate) use crate::typechecker::{
    Checker, Diagnostic, EffectDefInfo, EffectEntry, EffectOpSig, EffectRow, HandlerInfo,
    RecordInfo, Scheme, Type,
};

mod constraints;
mod functions;
mod handlers;
mod program;
mod types;

/// Walk an arrow chain and return the EffectRow from the innermost Fun.
pub(crate) fn innermost_effect_row(ty: &Type) -> Option<EffectRow> {
    match ty {
        Type::Fun(_, ret, row) => innermost_effect_row(ret).or_else(|| Some(row.clone())),
        _ => None,
    }
}

/// Effect names appearing on every arrow of a (possibly curried) type. Used to
/// tell whether a function FORWARDS a declared effect via a value of effectful
/// function type (e.g. point-free `greet = emit` where `emit`'s type carries
/// {Log}) versus genuinely never using it. Forwarding != performing, but it still
/// discharges the declaration, so it must not count as "unused".
pub(crate) fn collect_arrow_effects(ty: &Type, out: &mut std::collections::HashSet<String>) {
    if let Type::Fun(_, ret, row) = ty {
        for e in &row.effects {
            out.insert(e.name.clone());
        }
        collect_arrow_effects(ret, out);
    }
}

/// Annotations collected from FunAnnotation declarations:
/// (name -> (type, span)) and (name -> where clause constraints).
pub(crate) type Annotations = (
    HashMap<String, (Type, Span, EffectRow)>,
    HashMap<String, Vec<(String, u32, Vec<Type>)>>,
);

pub(crate) struct FunctionAnnotation<'a> {
    pub(crate) ty: Option<&'a Type>,
    pub(crate) span: Option<Span>,
    pub(crate) effect_row: Option<&'a EffectRow>,
}
