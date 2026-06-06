use std::collections::BTreeSet;

use crate::typechecker::Type;

/// Count dictionary parameters from trait constraints.
/// Excludes operator-dispatched traits (Num, Eq) which use BIF dispatch instead.
pub fn dict_param_count(constraints: &[(String, u32, Vec<crate::typechecker::Type>)]) -> usize {
    constraints
        .iter()
        .filter(|(trait_name, _, _)| trait_name != "Num" && trait_name != "Eq")
        .count()
}

/// True if any effect row along the function arrow has an open tail
/// (`needs {Foo, ..e}`).
pub fn has_open_effect_row(ty: &Type) -> bool {
    let mut current = ty;
    while let Type::Fun(_, ret, row) = current {
        if row.tail.is_some() {
            return true;
        }
        current = ret;
    }
    false
}

/// Derive source arity and sorted effect names from a typechecker `Type`.
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

/// Evidence-passing view of a function type:
/// `(source_arity, sorted_static_effect_names, has_open_row)`.
pub fn arity_and_evidence_from_type(ty: &Type) -> (usize, Vec<String>, bool) {
    let (user_arity, effects) = arity_and_effects_from_type(ty);
    let is_open_row = has_open_effect_row(ty);
    (user_arity, effects, is_open_row)
}
