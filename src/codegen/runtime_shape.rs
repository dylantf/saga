use crate::codegen::resolve::{ResolvedCodegenKind, ResolvedSymbol};
use crate::codegen::type_shape;
use crate::typechecker::Type;

/// Runtime CPS convention for a Saga function value.
///
/// `static_effects` is the canonical, statically-known prefix of the effect
/// row. `is_open_row` means callers must forward their ambient evidence tail
/// in addition to that prefix.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpsShape {
    pub static_effects: Vec<String>,
    pub is_open_row: bool,
}

/// Runtime calling shape for a function value or resolved callable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RuntimeFunctionShape {
    Pure,
    Cps(CpsShape),
    Intrinsic,
    InlineVal,
}

impl RuntimeFunctionShape {
    pub fn from_type(
        ty: &Type,
        mut canonicalize_effects: impl FnMut(Vec<String>) -> Vec<String>,
    ) -> Self {
        if !matches!(ty, Type::Fun(..)) {
            return RuntimeFunctionShape::Pure;
        }
        let (_, effects) = type_shape::arity_and_effects_from_type(ty);
        let static_effects = canonicalize_effects(effects);
        let is_open_row = type_shape::has_open_effect_row(ty);
        if static_effects.is_empty() && !is_open_row {
            RuntimeFunctionShape::Pure
        } else {
            RuntimeFunctionShape::Cps(CpsShape {
                static_effects,
                is_open_row,
            })
        }
    }

    pub fn from_resolved_symbol(
        resolved: &ResolvedSymbol,
        fallback_ty: Option<&Type>,
        mut canonicalize_effects: impl FnMut(Vec<String>) -> Vec<String>,
    ) -> Self {
        match &resolved.kind {
            ResolvedCodegenKind::Intrinsic { .. } => RuntimeFunctionShape::Intrinsic,
            ResolvedCodegenKind::InlineVal => RuntimeFunctionShape::InlineVal,
            ResolvedCodegenKind::BeamFunction { effects, .. }
            | ResolvedCodegenKind::ExternalFunction { effects, .. } => {
                let fallback = fallback_ty
                    .map(|ty| RuntimeFunctionShape::from_type(ty, &mut canonicalize_effects));
                let fallback_shape = fallback.and_then(|shape| shape.cps_shape());
                let mut static_effects = canonicalize_effects(effects.clone());
                if static_effects.is_empty()
                    && let Some(shape) = &fallback_shape
                {
                    static_effects = shape.static_effects.clone();
                }
                let is_open_row = fallback_shape.is_some_and(|shape| shape.is_open_row);
                if static_effects.is_empty() && !is_open_row {
                    RuntimeFunctionShape::Pure
                } else {
                    RuntimeFunctionShape::Cps(CpsShape {
                        static_effects,
                        is_open_row,
                    })
                }
            }
        }
    }

    pub fn cps_shape(&self) -> Option<CpsShape> {
        match self {
            RuntimeFunctionShape::Cps(shape) => Some(shape.clone()),
            RuntimeFunctionShape::Pure
            | RuntimeFunctionShape::Intrinsic
            | RuntimeFunctionShape::InlineVal => None,
        }
    }

    pub fn expanded_arity(&self, base_arity: usize) -> usize {
        match self {
            RuntimeFunctionShape::Cps(_) => base_arity + 2,
            RuntimeFunctionShape::Pure
            | RuntimeFunctionShape::Intrinsic
            | RuntimeFunctionShape::InlineVal => base_arity,
        }
    }
}
