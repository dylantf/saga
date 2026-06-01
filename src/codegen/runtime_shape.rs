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
            RuntimeFunctionShape::Pure | RuntimeFunctionShape::Intrinsic => None,
        }
    }

    pub fn expanded_arity(&self, base_arity: usize) -> usize {
        match self {
            RuntimeFunctionShape::Cps(_) => base_arity + 2,
            RuntimeFunctionShape::Pure | RuntimeFunctionShape::Intrinsic => base_arity,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::codegen::resolve::ResolvedCodegenKind;
    use crate::intrinsics::IntrinsicId;
    use crate::typechecker::{EffectEntry, EffectRow};

    fn int_ty() -> Type {
        Type::Con("Int".to_string(), vec![])
    }

    fn fun_with_row(row: EffectRow) -> Type {
        Type::Fun(Box::new(int_ty()), Box::new(int_ty()), row)
    }

    fn id_effects(effects: Vec<String>) -> Vec<String> {
        effects
    }

    #[test]
    fn closed_empty_function_type_is_pure() {
        let shape =
            RuntimeFunctionShape::from_type(&fun_with_row(EffectRow::closed(vec![])), id_effects);

        assert_eq!(shape, RuntimeFunctionShape::Pure);
        assert_eq!(shape.expanded_arity(2), 2);
    }

    #[test]
    fn closed_effectful_function_type_is_cps() {
        let shape = RuntimeFunctionShape::from_type(
            &fun_with_row(EffectRow::closed(vec![EffectEntry::unnamed(
                "Log".to_string(),
                vec![],
            )])),
            id_effects,
        );

        assert_eq!(
            shape,
            RuntimeFunctionShape::Cps(CpsShape {
                static_effects: vec!["Log".to_string()],
                is_open_row: false,
            })
        );
        assert_eq!(shape.expanded_arity(2), 4);
    }

    #[test]
    fn open_empty_function_type_is_cps() {
        let shape = RuntimeFunctionShape::from_type(
            &fun_with_row(EffectRow {
                effects: vec![],
                tail: Some(Box::new(Type::Var(1))),
            }),
            id_effects,
        );

        assert_eq!(
            shape,
            RuntimeFunctionShape::Cps(CpsShape {
                static_effects: vec![],
                is_open_row: true,
            })
        );
    }

    #[test]
    fn resolved_intrinsic_has_intrinsic_shape() {
        let resolved = ResolvedSymbol {
            name: "add".to_string(),
            source_module: None,
            canonical_name: "add".to_string(),
            kind: ResolvedCodegenKind::Intrinsic {
                id: IntrinsicId::Dbg,
                arity: 2,
            },
        };

        assert_eq!(
            RuntimeFunctionShape::from_resolved_symbol(&resolved, None, id_effects),
            RuntimeFunctionShape::Intrinsic
        );
    }
}
