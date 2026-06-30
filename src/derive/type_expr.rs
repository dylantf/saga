use crate::ast::*;

/// Whether the type variable `name` appears anywhere inside `te`. Used by the
/// built-in record/ADT derives to decide which type parameters a generated impl
/// must carry a `where` bound for.
pub(crate) fn type_expr_contains_var(te: &TypeExpr, name: &str) -> bool {
    match te {
        TypeExpr::Var { name: n, .. } => n == name,
        TypeExpr::Named { .. } => false,
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
