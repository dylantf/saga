//! Declaration checking and multi-pass registration.
//!
//! The large `impl Checker` is split across submodules by concern:
//! - `program`     — top-level driver, multi-pass registration, imports/externals
//! - `functions`   — `fun` clause checking, scheme building, exhaustiveness
//! - `types`       — type/alias/record definition registration
//! - `handlers`    — effect stub/op registration and handler checking
//! - `constraints` — fundep improvement, pending-constraint and supertrait solving
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

pub(crate) fn is_generic_trait_name(name: &str) -> bool {
    matches!(name, "Generic" | "Std.Generic.Generic")
}

pub(crate) fn generic_type(name: &str, args: Vec<Type>) -> Type {
    Type::Con(format!("Std.Generic.{name}"), args)
}

pub(crate) fn anon_record_generic_rep(fields: &[(String, Type)]) -> Type {
    generic_type("Record", vec![anon_record_generic_inner(fields)])
}

pub(crate) fn is_generic_type(ty: &Type, name: &str) -> bool {
    match ty {
        Type::Con(type_name, _) => type_name == name || type_name == &format!("Std.Generic.{name}"),
        _ => false,
    }
}

pub(crate) fn anon_record_from_generic_rep(rep: &Type) -> Option<Type> {
    let Type::Con(name, args) = rep else {
        return None;
    };
    if name != "Record" && name != "Std.Generic.Record" {
        return None;
    }
    let [inner] = args.as_slice() else {
        return None;
    };
    let fields = anon_record_fields_from_generic_inner(inner)?;
    Some(Type::Record(fields))
}

pub(crate) fn anon_record_fields_from_generic_inner(inner: &Type) -> Option<Vec<(String, Type)>> {
    if is_generic_type(inner, "U1") {
        return Some(vec![]);
    }
    match inner {
        Type::Con(name, args) if name == "Labeled" || name == "Std.Generic.Labeled" => {
            let [Type::Symbol(label), leaf] = args.as_slice() else {
                return None;
            };
            let Type::Con(leaf_name, leaf_args) = leaf else {
                return None;
            };
            if leaf_name != "Leaf" && leaf_name != "Std.Generic.Leaf" {
                return None;
            }
            let [field_ty] = leaf_args.as_slice() else {
                return None;
            };
            Some(vec![(label.clone(), field_ty.clone())])
        }
        Type::Con(name, args) if name == "And" || name == "Std.Generic.And" => {
            let [left, right] = args.as_slice() else {
                return None;
            };
            let mut fields = anon_record_fields_from_generic_inner(left)?;
            fields.extend(anon_record_fields_from_generic_inner(right)?);
            Some(fields)
        }
        _ => None,
    }
}

pub(crate) fn anon_record_generic_inner(fields: &[(String, Type)]) -> Type {
    if fields.is_empty() {
        return generic_type("U1", vec![]);
    }
    let mut iter = fields.iter().rev();
    let (last_name, last_ty) = iter.next().expect("non-empty fields");
    let mut acc = anon_record_field_rep(last_name, last_ty);
    for (name, ty) in iter {
        acc = generic_type("And", vec![anon_record_field_rep(name, ty), acc]);
    }
    acc
}

pub(crate) fn anon_record_field_rep(name: &str, ty: &Type) -> Type {
    generic_type(
        "Labeled",
        vec![
            Type::Symbol(name.to_string()),
            generic_type("Leaf", vec![ty.clone()]),
        ],
    )
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
