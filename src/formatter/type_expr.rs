use crate::ast::*;
use crate::token::Span;
use crate::docs;
use super::Doc;

/// If `ty` is `Tuple` applied to 2+ args, return those args.
/// The parser desugars `(A, B)` into `App(App(Named("Tuple"), A), B)`.
fn collect_tuple_args(ty: &TypeExpr) -> Option<Vec<&TypeExpr>> {
    let mut args = Vec::new();
    let mut cur = ty;
    loop {
        match cur {
            TypeExpr::App { func, arg, .. } => {
                args.push(arg.as_ref());
                cur = func.as_ref();
            }
            TypeExpr::Named { name, .. } if name == "Tuple" && args.len() >= 2 => {
                args.reverse();
                return Some(args);
            }
            _ => return None,
        }
    }
}

pub fn format_type_expr(ty: &TypeExpr) -> Doc {
    // Tuple sugar: Tuple applied to args → (A, B, ...)
    if let Some(args) = collect_tuple_args(ty) {
        let inner: Vec<Doc> = args.iter().map(|a| format_type_expr(a)).collect();
        return docs![Doc::text("("), Doc::join(Doc::text(", "), inner), Doc::text(")")];
    }
    match ty {
        TypeExpr::Named { name, .. } => Doc::text(name),
        TypeExpr::Var { name, .. } => Doc::text(name),
        TypeExpr::App { func, arg, .. } => {
            let arg_doc = match arg.as_ref() {
                // Paren-wrap App args to disambiguate, but not tuples — they
                // already produce (a, b) which is self-wrapping.
                TypeExpr::App { .. } if collect_tuple_args(arg).is_none() => {
                    docs![Doc::text("("), format_type_expr(arg), Doc::text(")")]
                }
                _ => format_type_expr(arg),
            };
            docs![format_type_expr(func), Doc::text(" "), arg_doc]
        }
        TypeExpr::Arrow { from, to, effects, effect_row_var, .. } => {
            let from_doc = match from.as_ref() {
                TypeExpr::Arrow { .. } => docs![Doc::text("("), format_type_expr(from), Doc::text(")")],
                _ => format_type_expr(from),
            };
            let mut d = docs![from_doc, Doc::text(" -> "), format_type_expr(to)];
            if !effects.is_empty() || effect_row_var.is_some() {
                d = d.append(Doc::text(" needs {"));
                let mut eff_parts: Vec<String> = effects.iter().map(format_effect_ref_str).collect();
                if let Some((var, _)) = effect_row_var {
                    eff_parts.push(format!("..{}", var));
                }
                d = d.append(Doc::text(eff_parts.join(", "))).append(Doc::text("}"));
            }
            d
        }
        TypeExpr::Record { fields, .. } => {
            let field_docs: Vec<Doc> = fields.iter().map(|(name, ty)| {
                docs![Doc::text(format!("{}: ", name)), format_type_expr(ty)]
            }).collect();
            docs![Doc::text("{ "), Doc::join(Doc::text(", "), field_docs), Doc::text(" }")]
        }
    }
}

/// Format a function type signature: params -> return_type [needs {...}]
/// Used for effect ops and trait methods where needs/where always inline.
pub fn format_fun_type(
    params: &[(String, TypeExpr)], return_type: &TypeExpr,
    effects: &[EffectRef], effect_row_var: &Option<(String, Span)>,
) -> Doc {
    let type_doc = format_arrow_chain(params, return_type);
    if effects.is_empty() && effect_row_var.is_none() {
        type_doc
    } else {
        docs![type_doc, Doc::text(" "), format_needs(effects, effect_row_var)]
    }
}

/// Format just the arrow chain: A -> B -> C
pub fn format_arrow_chain(params: &[(String, TypeExpr)], return_type: &TypeExpr) -> Doc {
    let mut parts: Vec<Doc> = params.iter().map(|(label, ty)| {
        if label.starts_with('_') {
            format_type_expr(ty)
        } else {
            docs![Doc::text(format!("({}: ", label)), format_type_expr(ty), Doc::text(")")]
        }
    }).collect();
    parts.push(format_type_expr(return_type));
    Doc::join(Doc::text(" -> "), parts)
}

/// Format `needs {Effect1, Effect2}` if non-empty.
pub fn format_needs(effects: &[EffectRef], effect_row_var: &Option<(String, Span)>) -> Doc {
    if effects.is_empty() && effect_row_var.is_none() {
        return Doc::Nil;
    }
    let mut eff_parts: Vec<String> = effects.iter().map(format_effect_ref_str).collect();
    if let Some((var, _)) = effect_row_var {
        eff_parts.push(format!("..{}", var));
    }
    Doc::text(format!("needs {{{}}}", eff_parts.join(", ")))
}

pub fn format_effect_ref_str(e: &EffectRef) -> String {
    if e.type_args.is_empty() {
        e.name.clone()
    } else {
        let args: Vec<String> = e.type_args.iter().map(format_type_expr_str).collect();
        format!("{} {}", e.name, args.join(" "))
    }
}

/// Simple string-based type formatting (for contexts where we need a String, not a Doc).
pub fn format_type_expr_str(ty: &TypeExpr) -> String {
    if let Some(args) = collect_tuple_args(ty) {
        let inner: Vec<String> = args.iter().map(|a| format_type_expr_str(a)).collect();
        return format!("({})", inner.join(", "));
    }
    match ty {
        TypeExpr::Named { name, .. } | TypeExpr::Var { name, .. } => name.clone(),
        TypeExpr::App { func, arg, .. } => {
            let arg_str = match arg.as_ref() {
                TypeExpr::App { .. } if collect_tuple_args(arg).is_none() => {
                    format!("({})", format_type_expr_str(arg))
                }
                TypeExpr::Arrow { .. } => format!("({})", format_type_expr_str(arg)),
                _ => format_type_expr_str(arg),
            };
            format!("{} {}", format_type_expr_str(func), arg_str)
        }
        TypeExpr::Arrow { from, to, .. } => {
            format!("{} -> {}", format_type_expr_str(from), format_type_expr_str(to))
        }
        TypeExpr::Record { fields, .. } => {
            let fs: Vec<String> = fields.iter()
                .map(|(n, t)| format!("{}: {}", n, format_type_expr_str(t)))
                .collect();
            format!("{{ {} }}", fs.join(", "))
        }
    }
}

pub fn format_where_clause(bounds: &[TraitBound]) -> Doc {
    let bound_strs: Vec<String> = bounds.iter().map(|b| {
        let traits: Vec<&str> = b.traits.iter().map(|(n, _)| n.as_str()).collect();
        format!("{}: {}", b.type_var, traits.join(" + "))
    }).collect();
    Doc::text(format!("where {{{}}}", bound_strs.join(", ")))
}
