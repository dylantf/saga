use super::Doc;
use crate::ast::*;
use crate::docs;
use crate::token::Span;

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

/// Whether an `impl ... for <target>` target must be parenthesized to round-trip.
///
/// The non-parenthesized impl-target grammar only accepts type *variables* as
/// application arguments (`impl Show for Box a b`). When an argument is a
/// concrete type — a named type, a nested application, etc. — the user had to
/// write parens (`impl S for (Users source Db.Required)`), and dropping them
/// changes how the target reparses. Tuples carry their own parens already.
pub fn impl_target_needs_parens(ty: &TypeExpr) -> bool {
    if collect_tuple_args(ty).is_some() {
        return false;
    }
    let mut cur = ty;
    let mut has_non_var_arg = false;
    while let TypeExpr::App { func, arg, .. } = cur {
        if !matches!(arg.as_ref(), TypeExpr::Var { .. }) {
            has_non_var_arg = true;
        }
        cur = func.as_ref();
    }
    has_non_var_arg
}

pub fn format_type_expr(ty: &TypeExpr) -> Doc {
    // Tuple sugar: Tuple applied to args -> (A, B, ...)
    if let Some(args) = collect_tuple_args(ty) {
        let inner: Vec<Doc> = args.iter().map(|a| format_type_expr(a)).collect();
        return docs![
            Doc::text("("),
            Doc::join(Doc::text(", "), inner),
            Doc::text(")")
        ];
    }
    match ty {
        TypeExpr::Named { name, .. } => Doc::text(name),
        TypeExpr::Var { name, .. } => Doc::text(name),
        TypeExpr::App { func, arg, .. } => {
            let arg_doc = match arg.as_ref() {
                // Paren-wrap App args to disambiguate, but not tuples - they
                // already produce (a, b) which is self-wrapping.
                TypeExpr::App { .. } if collect_tuple_args(arg).is_none() => {
                    docs![Doc::text("("), format_type_expr(arg), Doc::text(")")]
                }
                // Arrow args need parens too — `List (a -> b)` vs `List a -> b`
                TypeExpr::Arrow { .. } => {
                    docs![Doc::text("("), format_type_expr(arg), Doc::text(")")]
                }
                _ => format_type_expr(arg),
            };
            docs![format_type_expr(func), Doc::text(" "), arg_doc]
        }
        TypeExpr::Arrow {
            from,
            to,
            effects,
            effect_row_var,
            ..
        } => {
            let from_doc = match from.as_ref() {
                TypeExpr::Arrow { .. } => {
                    docs![Doc::text("("), format_type_expr(from), Doc::text(")")]
                }
                _ => format_type_expr(from),
            };
            let mut d = docs![from_doc, Doc::text(" -> "), format_type_expr(to)];
            if !effects.is_empty() || !effect_row_var.is_empty() {
                d = docs![
                    d,
                    Doc::text(" "),
                    format_needs_inner(effects, effect_row_var)
                ];
            }
            d
        }
        TypeExpr::Labeled { label, inner, .. } => {
            docs![
                Doc::text(format!("({}: ", label)),
                format_type_expr(inner),
                Doc::text(")")
            ]
        }
        TypeExpr::Record {
            fields, multiline, ..
        } => {
            let field_docs: Vec<Doc> = fields
                .iter()
                .map(|(name, ty)| docs![Doc::text(format!("{}: ", name)), format_type_expr(ty)])
                .collect();
            if *multiline {
                let fields_joined = Doc::join(docs![Doc::text(","), Doc::hardline()], field_docs);
                docs![
                    Doc::text("{"),
                    Doc::nest(2, docs![Doc::hardline(), fields_joined, Doc::text(",")]),
                    Doc::hardline(),
                    Doc::text("}")
                ]
            } else {
                let fields_joined = Doc::join(docs![Doc::text(","), Doc::line()], field_docs);
                let trailing_comma = Doc::if_break(Doc::text(","), Doc::Nil);
                Doc::group(docs![
                    Doc::text("{"),
                    Doc::nest(2, docs![Doc::line(), fields_joined, trailing_comma]),
                    Doc::line(),
                    Doc::text("}")
                ])
            }
        }
    }
}

/// Format a type in "atom" position — wraps App and Arrow in parens since they
/// contain spaces and would be ambiguous in space-separated contexts.
/// Named, Var, Labeled, Record, and Tuple types are already self-delimiting.
pub fn format_type_expr_atom(ty: &TypeExpr) -> Doc {
    if collect_tuple_args(ty).is_some() {
        // Tuples are (A, B) — already parenthesized
        return format_type_expr(ty);
    }
    match ty {
        TypeExpr::Named { .. }
        | TypeExpr::Var { .. }
        | TypeExpr::Labeled { .. }
        | TypeExpr::Record { .. } => format_type_expr(ty),
        // App and Arrow need wrapping
        _ => docs![Doc::text("("), format_type_expr(ty), Doc::text(")")],
    }
}

/// Format a function type signature: params -> return_type [needs {...}]
/// Used for effect ops and trait methods where needs/where always inline.
pub fn format_fun_type(
    params: &[(String, TypeExpr)],
    return_type: &TypeExpr,
    effects: &[EffectRef],
    effect_row_var: &[(String, Span)],
) -> Doc {
    let type_doc = format_arrow_chain(params, return_type);
    if effects.is_empty() && effect_row_var.is_empty() {
        type_doc
    } else {
        docs![
            type_doc,
            Doc::text(" "),
            format_needs(effects, effect_row_var)
        ]
    }
}

/// Format just the arrow chain: A -> B -> C
pub fn format_arrow_chain(params: &[(String, TypeExpr)], return_type: &TypeExpr) -> Doc {
    format_arrow_chain_with_tail_indent(params, return_type, 2)
}

/// Format a top-level signature arrow chain whose first item should align with
/// the type text after later arrows:
///
/// This is used by top-level function signatures so a long name can break after
/// the colon without hiding the first parameter:
///
/// ```text
/// fun f :
///      A
///   -> B
/// ```
///
/// If the arrow chain still fits by itself, it keeps the normal two-space
/// continuation indent:
///
/// ```text
/// fun f :
///   A -> B
/// ```
pub fn format_arrow_chain_signature_continuation(
    params: &[(String, TypeExpr)],
    return_type: &TypeExpr,
) -> Doc {
    let mut iter = arrow_chain_parts(params, return_type).into_iter();
    let Some(first) = iter.next() else {
        return Doc::Nil;
    };
    let tail = iter.fold(Doc::Nil, |acc, part| {
        docs![acc, Doc::line(), Doc::text("-> "), part]
    });
    Doc::nest(
        2,
        docs![
            Doc::line(),
            Doc::group(docs![
                Doc::if_break(Doc::text("   "), Doc::Nil),
                first,
                tail
            ])
        ],
    )
}

fn format_arrow_chain_with_tail_indent(
    params: &[(String, TypeExpr)],
    return_type: &TypeExpr,
    tail_indent: usize,
) -> Doc {
    let mut iter = arrow_chain_parts(params, return_type).into_iter();
    let Some(first) = iter.next() else {
        return Doc::Nil;
    };
    let tail = iter.fold(Doc::Nil, |acc, part| {
        docs![acc, Doc::line(), Doc::text("-> "), part]
    });
    Doc::group(docs![first, Doc::nest(tail_indent, tail)])
}

fn arrow_chain_parts(params: &[(String, TypeExpr)], return_type: &TypeExpr) -> Vec<Doc> {
    let mut parts: Vec<Doc> = params
        .iter()
        .map(|(label, ty)| {
            if label.starts_with('_') {
                match ty {
                    TypeExpr::Arrow { .. } => {
                        docs![Doc::text("("), format_type_expr(ty), Doc::text(")")]
                    }
                    _ => format_type_expr(ty),
                }
            } else {
                docs![
                    Doc::text(format!("({}: ", label)),
                    format_type_expr(ty),
                    Doc::text(")")
                ]
            }
        })
        .collect();
    // If the return type is an arrow with effects, wrap in parens to preserve
    // the scoping of `needs` — otherwise `A -> B -> C needs {E}` re-parses
    // with `needs {E}` on the whole signature instead of just the inner arrow.
    let ret_doc = match return_type {
        TypeExpr::Arrow {
            effects,
            effect_row_var,
            ..
        } if !effects.is_empty() || !effect_row_var.is_empty() => {
            docs![
                Doc::text("("),
                format_type_expr(return_type),
                Doc::text(")")
            ]
        }
        _ => format_type_expr(return_type),
    };
    parts.push(ret_doc);
    parts
}

/// Format `needs {Effect1, Effect2}` if non-empty.
pub fn format_needs(effects: &[EffectRef], effect_row_var: &[(String, Span)]) -> Doc {
    if effects.is_empty() && effect_row_var.is_empty() {
        return Doc::Nil;
    }
    format_needs_inner(effects, effect_row_var)
}

/// Format `needs {Effect1, Effect2}` unconditionally.
fn format_needs_inner(effects: &[EffectRef], effect_row_var: &[(String, Span)]) -> Doc {
    let mut parts: Vec<Doc> = effects.iter().map(format_effect_ref).collect();
    for (var, _) in effect_row_var {
        parts.push(Doc::text(format!("..{}", var)));
    }
    docs![
        Doc::text("needs {"),
        Doc::join(Doc::text(", "), parts),
        Doc::text("}")
    ]
}

pub fn format_effect_ref(e: &EffectRef) -> Doc {
    if e.type_args.is_empty() {
        Doc::text(&e.name)
    } else {
        let args: Vec<Doc> = e.type_args.iter().map(format_type_expr).collect();
        docs![
            Doc::text(&e.name),
            Doc::text(" "),
            Doc::join(Doc::text(" "), args)
        ]
    }
}

pub fn format_where_clause(bounds: &[TraitBound]) -> Doc {
    let bound_docs: Vec<Doc> = bounds
        .iter()
        .map(|b| {
            let trait_docs: Vec<Doc> = b
                .traits
                .iter()
                .map(|tr| {
                    if tr.type_args.is_empty() {
                        Doc::text(tr.name.clone())
                    } else {
                        let args: Vec<Doc> = tr.type_args.iter().map(format_type_expr).collect();
                        docs![
                            Doc::text(format!("{} ", tr.name)),
                            Doc::join(Doc::text(" "), args)
                        ]
                    }
                })
                .collect();
            docs![
                Doc::text(format!("{}: ", b.type_var)),
                Doc::join(Doc::text(" + "), trait_docs)
            ]
        })
        .collect();
    docs![
        Doc::text("where {"),
        Doc::join(Doc::text(", "), bound_docs),
        Doc::text("}")
    ]
}

pub fn format_trait_app(app: &TraitApp) -> Doc {
    if app.type_args.is_empty() {
        Doc::text(app.trait_name.clone())
    } else {
        let args: Vec<Doc> = app.type_args.iter().map(format_type_expr).collect();
        docs![
            Doc::text(format!("{} ", app.trait_name)),
            Doc::join(Doc::text(" "), args)
        ]
    }
}

pub fn format_impl_where_clause(bounds: &[TraitBound], apps: &[TraitApp]) -> Doc {
    let mut items: Vec<Doc> = Vec::new();
    for bound in bounds {
        let trait_docs: Vec<Doc> = bound
            .traits
            .iter()
            .map(|tr| {
                if tr.type_args.is_empty() {
                    Doc::text(tr.name.clone())
                } else {
                    let args: Vec<Doc> = tr.type_args.iter().map(format_type_expr).collect();
                    docs![
                        Doc::text(format!("{} ", tr.name)),
                        Doc::join(Doc::text(" "), args)
                    ]
                }
            })
            .collect();
        items.push(docs![
            Doc::text(format!("{}: ", bound.type_var)),
            Doc::join(Doc::text(" + "), trait_docs)
        ]);
    }
    items.extend(apps.iter().map(format_trait_app));
    docs![
        Doc::text("where {"),
        Doc::join(Doc::text(", "), items),
        Doc::text("}")
    ]
}
