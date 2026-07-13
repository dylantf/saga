use crate::codegen::lower::util;
use crate::codegen::resolve::{ResolvedCodegenKind, ResolvedSymbol};
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

impl CpsShape {
    /// Derive the runtime shape of a lambda placed into an expected callback
    /// slot. The expected type defines the positional ABI; the inferred type
    /// contributes effects absorbed by an open tail.
    pub fn for_lambda_boundary(expected: &Self, inferred: &Self) -> Self {
        let mut static_effects = expected.static_effects.clone();
        for inferred_effect in &inferred.static_effects {
            if static_effects
                .iter()
                .any(|effect| effect == inferred_effect)
            {
                continue;
            }
            let family = crate::typechecker::applied_effect_family(inferred_effect);
            let same_family = static_effects
                .iter()
                .enumerate()
                .filter(|(_, effect)| crate::typechecker::applied_effect_family(effect) == family)
                .map(|(idx, _)| idx)
                .collect::<Vec<_>>();
            if same_family.len() == 1
                && (static_effects[same_family[0]].contains('$') || inferred_effect.contains('$'))
            {
                // A generic and concrete spelling of the same applied effect
                // describe one positional slot. Prefer the concrete spelling
                // when available, but never mint a second slot for the type
                // variable spelling.
                if !inferred_effect.contains('$') {
                    static_effects[same_family[0]] = inferred_effect.clone();
                }
            } else {
                // Distinct concrete applications of one effect family are
                // independent slots and must coexist.
                static_effects.push(inferred_effect.clone());
            }
        }
        static_effects.sort();
        static_effects.dedup();
        Self {
            static_effects,
            is_open_row: expected.is_open_row || inferred.is_open_row,
        }
    }
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
        let (_, effects) = util::arity_and_effects_from_type(ty);
        let static_effects = canonicalize_effects(effects);
        let is_open_row = util::has_open_effect_row(ty);
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
                // The occurrence type carries the caller's instantiation of
                // parameterized effects; exported symbol metadata only carries
                // the generic declaration. Prefer the occurrence whenever it
                // is available so caller-side evidence projection selects the
                // concrete applied slots.
                let static_effects = fallback_shape
                    .as_ref()
                    .map(|shape| shape.static_effects.clone())
                    .unwrap_or_else(|| canonicalize_effects(effects.clone()));
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
    use super::CpsShape;

    #[test]
    fn lambda_boundary_keeps_unused_expected_slots() {
        let expected = CpsShape {
            static_effects: vec![
                "Main.Repo".into(),
                "Main.Rollback<Std.String.String>".into(),
            ],
            is_open_row: true,
        };
        let inferred = CpsShape {
            static_effects: vec!["Main.Rollback<Std.String.String>".into()],
            is_open_row: false,
        };

        assert_eq!(
            CpsShape::for_lambda_boundary(&expected, &inferred),
            expected
        );
    }

    #[test]
    fn lambda_boundary_keeps_distinct_concrete_family_slots() {
        let expected = CpsShape {
            static_effects: vec!["Main.Fail<Std.Int.Int>".into()],
            is_open_row: true,
        };
        let inferred = CpsShape {
            static_effects: vec!["Main.Fail<Std.String.String>".into()],
            is_open_row: false,
        };

        assert_eq!(
            CpsShape::for_lambda_boundary(&expected, &inferred).static_effects,
            vec!["Main.Fail<Std.Int.Int>", "Main.Fail<Std.String.String>"]
        );
    }

    #[test]
    fn lambda_boundary_collapses_generic_and_concrete_family_slot() {
        let expected = CpsShape {
            static_effects: vec!["Main.Rollback<$1>".into()],
            is_open_row: false,
        };
        let inferred = CpsShape {
            static_effects: vec!["Main.Rollback<Std.String.String>".into()],
            is_open_row: false,
        };

        assert_eq!(
            CpsShape::for_lambda_boundary(&expected, &inferred).static_effects,
            vec!["Main.Rollback<Std.String.String>"]
        );
    }
}
