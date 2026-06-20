use crate::ast::*;
use crate::token::Span;
use std::collections::HashMap;

pub(crate) fn te_head(te: &TypeExpr) -> Option<String> {
    match te {
        TypeExpr::Named { name, .. } => Some(name.rsplit('.').next().unwrap_or(name).to_string()),
        TypeExpr::App { func, .. } => te_head(func),
        TypeExpr::Labeled { inner, .. } => te_head(inner),
        _ => None,
    }
}


/// Prefix every type variable's name so two type expressions can be unified in a
/// shared substitution without their variables colliding.
pub(crate) fn te_rename_vars(te: &TypeExpr, prefix: &str) -> TypeExpr {
    match te {
        TypeExpr::Var { id, name, span } => TypeExpr::Var {
            id: *id,
            name: format!("{prefix}{name}"),
            span: *span,
        },
        TypeExpr::App {
            id,
            func,
            arg,
            span,
        } => TypeExpr::App {
            id: *id,
            func: Box::new(te_rename_vars(func, prefix)),
            arg: Box::new(te_rename_vars(arg, prefix)),
            span: *span,
        },
        TypeExpr::Labeled { inner, .. } => te_rename_vars(inner, prefix),
        other => other.clone(),
    }
}


pub(crate) fn te_resolve(te: &TypeExpr, subst: &HashMap<String, TypeExpr>) -> TypeExpr {
    match te {
        TypeExpr::Var { name, .. } => match subst.get(name) {
            Some(bound) => te_resolve(bound, subst),
            None => te.clone(),
        },
        _ => te.clone(),
    }
}


pub(crate) fn te_unify(a: &TypeExpr, b: &TypeExpr, subst: &mut HashMap<String, TypeExpr>) -> bool {
    let a = te_resolve(a, subst);
    let b = te_resolve(b, subst);
    match (&a, &b) {
        (TypeExpr::Var { name: na, .. }, TypeExpr::Var { name: nb, .. }) if na == nb => true,
        (TypeExpr::Var { name, .. }, _) => {
            subst.insert(name.clone(), b.clone());
            true
        }
        (_, TypeExpr::Var { name, .. }) => {
            subst.insert(name.clone(), a.clone());
            true
        }
        (TypeExpr::Named { name: na, .. }, TypeExpr::Named { name: nb, .. }) => {
            na.rsplit('.').next() == nb.rsplit('.').next()
        }
        (TypeExpr::Symbol { name: na, .. }, TypeExpr::Symbol { name: nb, .. }) => na == nb,
        (
            TypeExpr::App {
                func: fa, arg: aa, ..
            },
            TypeExpr::App {
                func: fb, arg: ab, ..
            },
        ) => te_unify(fa, fb, subst) && te_unify(aa, ab, subst),
        (TypeExpr::Labeled { inner, .. }, _) => te_unify(inner, &b, subst),
        (_, TypeExpr::Labeled { inner, .. }) => te_unify(&a, inner, subst),
        _ => false,
    }
}


pub(crate) fn te_apply(te: &TypeExpr, subst: &HashMap<String, TypeExpr>) -> TypeExpr {
    match te {
        TypeExpr::Var { name, .. } => match subst.get(name) {
            Some(bound) => te_apply(bound, subst),
            None => te.clone(),
        },
        TypeExpr::App {
            id,
            func,
            arg,
            span,
        } => TypeExpr::App {
            id: *id,
            func: Box::new(te_apply(func, subst)),
            arg: Box::new(te_apply(arg, subst)),
            span: *span,
        },
        TypeExpr::Labeled { inner, .. } => te_apply(inner, subst),
        other => other.clone(),
    }
}


pub(crate) fn te_is_concrete(te: &TypeExpr) -> bool {
    match te {
        TypeExpr::Var { .. } => false,
        TypeExpr::App { func, arg, .. } => te_is_concrete(func) && te_is_concrete(arg),
        TypeExpr::Labeled { inner, .. } => te_is_concrete(inner),
        _ => true,
    }
}


pub(crate) fn te_structural_eq(a: &TypeExpr, b: &TypeExpr) -> bool {
    match (a, b) {
        (TypeExpr::Named { name: na, .. }, TypeExpr::Named { name: nb, .. }) => {
            na.rsplit('.').next() == nb.rsplit('.').next()
        }
        (TypeExpr::Var { name: na, .. }, TypeExpr::Var { name: nb, .. }) => na == nb,
        (TypeExpr::Symbol { name: na, .. }, TypeExpr::Symbol { name: nb, .. }) => na == nb,
        (
            TypeExpr::App {
                func: fa, arg: aa, ..
            },
            TypeExpr::App {
                func: fb, arg: ab, ..
            },
        ) => te_structural_eq(fa, fb) && te_structural_eq(aa, ab),
        _ => false,
    }
}


pub(crate) fn is_type_param_ref(ty: &TypeExpr, param_name: &str) -> bool {
    matches!(ty, TypeExpr::Var { name, .. } if name == param_name)
}


pub(crate) fn is_supported_applied_row_type(ty: &TypeExpr) -> bool {
    if ty.head_name().is_some_and(|head| head == "Tuple") {
        return false;
    }
    match ty {
        TypeExpr::Named { .. } => true,
        TypeExpr::App { func, arg, .. } => {
            is_supported_applied_row_type(func) && is_supported_applied_row_type(arg)
        }
        _ => false,
    }
}


pub(crate) fn rep_type_for_named_type(ty: &TypeExpr) -> Option<TypeExpr> {
    let zero_span = Span { start: 0, end: 0 };
    match ty {
        TypeExpr::Named { name, .. } => Some(TypeExpr::Named {
            id: NodeId::fresh(),
            name: rep_name_for_type_head(name),
            span: zero_span,
        }),
        TypeExpr::App { func, arg, .. } => Some(TypeExpr::App {
            id: NodeId::fresh(),
            func: Box::new(rep_type_for_named_type(func)?),
            arg: Box::new((**arg).clone()),
            span: zero_span,
        }),
        _ => None,
    }
}


pub(crate) fn rep_name_for_type_head(head: &str) -> String {
    if let Some((module, name)) = head.rsplit_once('.') {
        format!("{module}.Rep__{name}")
    } else {
        format!("Rep__{head}")
    }
}


/// Extract the bare head name and left-to-right type arguments from a
/// possibly-applied TypeExpr. Returns None if the TypeExpr isn't a named
/// type or a chain of applications headed by one.
pub(crate) fn extract_head_and_args(te: &TypeExpr) -> Option<(String, Vec<TypeExpr>)> {
    match te {
        TypeExpr::Named { name, .. } => Some((name.clone(), vec![])),
        TypeExpr::App { func, arg, .. } => {
            let (head, mut args) = extract_head_and_args(func)?;
            args.push(arg.as_ref().clone());
            Some((head, args))
        }
        _ => None,
    }
}


pub(crate) fn is_self_var(te: &TypeExpr, self_var: &str) -> bool {
    matches!(te, TypeExpr::Var { name, .. } if name == self_var)
}


/// Build a `[(param_name, call_arg)]` substitution pairing a wrapper's declared
/// type parameters with the type arguments it's applied to at the call site.
pub(crate) fn param_subst(type_params: &[TypeParam], call_args: &[TypeExpr]) -> Vec<(String, TypeExpr)> {
    type_params
        .iter()
        .map(|p| p.name.clone())
        .zip(call_args.iter().cloned())
        .collect()
}


/// Substitute type-parameter variables in `te` according to `subst`. Used to
/// resolve a wrapper's declared field types against the call-site type
/// arguments before locating the trait's self type within them. The cloned
/// TypeExpr is only ever inspected (never spliced into the AST), so reusing the
/// original NodeIds is harmless.
pub(crate) fn subst_type_params(te: &TypeExpr, subst: &[(String, TypeExpr)]) -> TypeExpr {
    match te {
        TypeExpr::Var { name, .. } => subst
            .iter()
            .find(|(p, _)| p == name)
            .map(|(_, replacement)| replacement.clone())
            .unwrap_or_else(|| te.clone()),
        TypeExpr::Named { .. } | TypeExpr::Symbol { .. } => te.clone(),
        TypeExpr::App {
            id,
            func,
            arg,
            span,
        } => TypeExpr::App {
            id: *id,
            func: Box::new(subst_type_params(func, subst)),
            arg: Box::new(subst_type_params(arg, subst)),
            span: *span,
        },
        TypeExpr::Arrow {
            id,
            from,
            to,
            effects,
            effect_row_var,
            span,
        } => TypeExpr::Arrow {
            id: *id,
            from: Box::new(subst_type_params(from, subst)),
            to: Box::new(subst_type_params(to, subst)),
            effects: effects.clone(),
            effect_row_var: effect_row_var.clone(),
            span: *span,
        },
        TypeExpr::Record {
            id,
            fields,
            multiline,
            span,
        } => TypeExpr::Record {
            id: *id,
            fields: fields
                .iter()
                .map(|(l, t)| (l.clone(), subst_type_params(t, subst)))
                .collect(),
            multiline: *multiline,
            span: *span,
        },
        TypeExpr::Labeled {
            id,
            label,
            inner,
            span,
        } => TypeExpr::Labeled {
            id: *id,
            label: label.clone(),
            inner: Box::new(subst_type_params(inner, subst)),
            span: *span,
        },
    }
}


pub(crate) fn type_expr_contains_var(te: &TypeExpr, name: &str) -> bool {
    match te {
        TypeExpr::Var { name: n, .. } => n == name,
        TypeExpr::Named { .. } | TypeExpr::Symbol { .. } => false,
        TypeExpr::App { func, arg, .. } => {
            type_expr_contains_var(func, name) || type_expr_contains_var(arg, name)
        }
        TypeExpr::Arrow { from, to, .. } => {
            type_expr_contains_var(from, name) || type_expr_contains_var(to, name)
        }
        TypeExpr::Record { fields, .. } => {
            fields.iter().any(|(_, t)| type_expr_contains_var(t, name))
        }
        TypeExpr::Labeled { inner, .. } => type_expr_contains_var(inner, name),
    }
}


/// Build a TypeExpr that applies `name` to each of `type_params` as a Var.
/// e.g. (`Rep__Box`, `["a"]`) -> `App(Named(Rep__Box), Var(a))`.
pub(crate) fn apply_type_params(name: &str, type_params: &[TypeParam]) -> TypeExpr {
    apply_type_params_specialized(name, type_params, &HashMap::new())
}


/// Like `apply_type_params`, but substitutes any parameter present in
/// `bindings` with its concrete type (used to pin a parameterized record's
/// scope variable, e.g. `Users source meta` -> `Users source Required`).
pub(crate) fn apply_type_params_specialized(
    name: &str,
    type_params: &[TypeParam],
    bindings: &HashMap<String, TypeExpr>,
) -> TypeExpr {
    let mut acc = TypeExpr::Named {
        id: NodeId::fresh(),
        name: name.into(),
        span: Span { start: 0, end: 0 },
    };
    for tp in type_params {
        let arg = bindings.get(&tp.name).cloned().unwrap_or(TypeExpr::Var {
            id: NodeId::fresh(),
            name: tp.name.clone(),
            span: Span { start: 0, end: 0 },
        });
        acc = TypeExpr::App {
            id: NodeId::fresh(),
            func: Box::new(acc),
            arg: Box::new(arg),
            span: Span { start: 0, end: 0 },
        };
    }
    acc
}

