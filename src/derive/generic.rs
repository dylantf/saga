use super::*;
use crate::ast::*;
use crate::token::Span;
use crate::typechecker::{Diagnostic, Severity};

/// Returns the decls to splice into the program, or:
///   - `Err(None)` for "unsupported trait, use the default cannot-derive error"
///   - `Err(Some(diag))` for a specific diagnostic
pub(crate) fn generate_record_derive(
    public: bool,
    trait_name: &str,
    record_name: &str,
    type_params: &[TypeParam],
    fields: &[Annotated<(String, TypeExpr)>],
    span: Span,
) -> Result<Vec<Decl>, Option<Diagnostic>> {
    let bare = trait_name.rsplit('.').next().unwrap_or(trait_name);
    match bare {
        "Show" | "Debug" => Ok(vec![derive_record_stringify(
            bare,
            if bare == "Show" { "show" } else { "debug" },
            record_name,
            type_params,
            fields,
            span,
        )]),
        "Eq" => Ok(vec![derive_marker_trait(
            "Eq",
            record_name,
            type_params,
            span,
        )]),
        "Default" => Ok(vec![derive_record_default(
            record_name,
            type_params,
            fields,
            span,
        )]),
        "Generic" => derive_record_generic(public, record_name, type_params, fields, span),
        _ => Err(None),
    }
}


/// Build `type Rep__R = Rep__R <inner-rep>` + `impl Generic R (Rep__R) { to, from }`.
/// Handles parameterized and recursive records: the Rep type carries the same
/// type parameters as the user record, and field types referencing the user
/// type round-trip naturally through the runtime dictionary (no special
/// recursion handling in the Rep shape).
pub(crate) fn derive_record_generic(
    public: bool,
    record_name: &str,
    type_params: &[TypeParam],
    fields: &[Annotated<(String, TypeExpr)>],
    span: Span,
) -> Result<Vec<Decl>, Option<Diagnostic>> {
    // Naming: use a leading uppercase letter so the lexer classifies the
    // name as an UpperIdent (type/constructor). The planning doc proposed
    // `__Rep_<R>` but a leading `_` lexes as lowercase, which would break
    // user-written ascriptions like `(to p : __Rep_Person)`.
    let rep_name = format!("Rep__{record_name}");
    let plain_fields: Vec<(String, TypeExpr)> = fields.iter().map(|a| a.node.clone()).collect();

    // 1. Synthetic TypeDef: `type Rep__R <params> = Rep__R (Record <inner>)`.
    // The Record wrapper carries the runtime type name and gives library
    // codecs a hook for outer record framing (e.g. JSON `{}`).
    let inner_type = type_app(type_named("Record"), build_rep_type_inner(&plain_fields));
    let ctor_field_type = inner_type.clone();
    let rep_typedef = Decl::TypeDef {
        id: NodeId::fresh(),
        doc: vec![],
        public,
        opaque: false,
        name: rep_name.clone(),
        name_span: Span { start: 0, end: 0 },
        type_params: type_params.to_vec(),
        variants: vec![Annotated::bare(TypeConstructor {
            id: NodeId::fresh(),
            name: rep_name.clone(),
            fields: vec![(None, ctor_field_type)],
            span,
        })],
        deriving: vec![],
        multiline: false,
        span,
    };

    // 2. `to p = __Rep_R (And (Labeled "name" (Leaf p.name)) ...)`
    let param_name = "__val".to_string();
    let param_var = Expr::synth(
        span,
        ExprKind::Var {
            name: param_name.clone(),
        },
    );
    let inner_expr = build_rep_to_expr(&plain_fields, &param_var, span);
    let record_wrapped = apply2(
        &generic_name("Record"),
        string_lit(record_name, span),
        inner_expr,
        span,
    );
    let to_body = apply_ctor(&rep_name, record_wrapped, span);
    let to_method = Annotated::bare(ImplMethod {
        name: "to".into(),
        name_span: Span { start: 0, end: 0 },
        params: vec![Pat::Var {
            id: NodeId::fresh(),
            name: param_name,
            span,
        }],
        body: to_body,
    });

    // 3. `from (__Rep_R (And (Labeled _ (Leaf n)) ...)) = R { name: n, ... }`
    let field_var_names: Vec<String> = (0..plain_fields.len()).map(|i| format!("__f{i}")).collect();
    let inner_pat = build_rep_from_pattern(&field_var_names, span);
    let record_pat = Pat::Constructor {
        id: NodeId::fresh(),
        name: generic_name("Record"),
        args: vec![
            Pat::Wildcard {
                id: NodeId::fresh(),
                span,
            },
            inner_pat,
        ],
        span,
    };
    let from_param = Pat::Constructor {
        id: NodeId::fresh(),
        name: rep_name.clone(),
        args: vec![record_pat],
        span,
    };
    let record_fields: Vec<(String, Span, Expr)> = plain_fields
        .iter()
        .zip(field_var_names.iter())
        .map(|((fname, _), vname)| {
            (
                fname.clone(),
                Span { start: 0, end: 0 },
                Expr::synth(
                    span,
                    ExprKind::Var {
                        name: vname.clone(),
                    },
                ),
            )
        })
        .collect();
    let from_body = if plain_fields.is_empty() {
        // Zero-field record: just construct the record with no fields.
        Expr::synth(
            span,
            ExprKind::RecordCreate {
                name: record_name.into(),
                fields: vec![],
                record_name: None,
            },
        )
    } else {
        Expr::synth(
            span,
            ExprKind::RecordCreate {
                name: record_name.into(),
                fields: record_fields,
                record_name: None,
            },
        )
    };
    let from_method = Annotated::bare(ImplMethod {
        name: "from".into(),
        name_span: Span { start: 0, end: 0 },
        params: vec![from_param],
        body: from_body,
    });

    let rep_with_params = apply_type_params(&rep_name, type_params);
    let impl_def = Decl::ImplDef {
        trait_name_span: Span { start: 0, end: 0 },
        target_type_span: Span { start: 0, end: 0 },
        target_type_expr: None,
        id: NodeId::fresh(),
        doc: vec![],
        trait_name: "Generic".into(),
        trait_type_args: vec![rep_with_params],
        target_type: record_name.into(),
        type_params: type_params.to_vec(),
        where_clause: vec![],
        where_apps: vec![],
        needs: vec![],
        methods: vec![to_method, from_method],
        routed_derive_info: None,
        span,
        dangling_trivia: vec![],
    };

    Ok(vec![rep_typedef, impl_def])
}


/// Build `type Rep__T = Rep__T <inner>` + `impl Generic Rep__T for T { to, from }`
/// for an ADT (`Decl::TypeDef`). Mirrors `derive_record_generic`'s shape but
/// the inner Rep is a right-leaning Or chain over `Labeled "Variant" <shape>`.
///
/// Direct self-reference detection only — indirect recursion via other types
/// is rare and deferred to Phase 2d alongside true recursive support.
pub(crate) fn derive_adt_generic(
    public: bool,
    type_name: &str,
    type_params: &[TypeParam],
    variants: &[Annotated<TypeConstructor>],
    span: Span,
) -> Result<Vec<Decl>, Option<Diagnostic>> {
    if variants.is_empty() {
        return Err(Some(Diagnostic {
            severity: Severity::Error,
            message: format!("cannot derive (Generic) for `{type_name}`: no variants"),
            span: Some(span),
        }));
    }

    let rep_name = format!("Rep__{type_name}");

    // 1. Inner Rep type = `Adt <Or-tree>` where the Or-tree is a right-leaning
    // chain of `Variant <variant_shape_type>`. `Adt` carries the runtime type
    // name; `Variant` replaces `Labeled` for constructor-name layers so library
    // codecs can distinguish constructor names from record-field names.
    let inner_type = type_app(type_named("Adt"), build_adt_rep_inner_type(variants));
    let rep_typedef = Decl::TypeDef {
        id: NodeId::fresh(),
        doc: vec![],
        public,
        opaque: false,
        name: rep_name.clone(),
        name_span: Span { start: 0, end: 0 },
        type_params: type_params.to_vec(),
        variants: vec![Annotated::bare(TypeConstructor {
            id: NodeId::fresh(),
            name: rep_name.clone(),
            fields: vec![(None, inner_type)],
            span,
        })],
        deriving: vec![],
        multiline: false,
        span,
    };

    // 2. `to __val = case __val { V0 a b -> Rep__T (Or_Left (Labeled "V0" ...)); ... }`
    let param_name = "__val".to_string();
    let n = variants.len();
    let to_arms: Vec<Annotated<CaseArm>> = variants
        .iter()
        .enumerate()
        .map(|(i, ann_v)| {
            let v = &ann_v.node;
            let field_vars: Vec<String> = (0..v.fields.len()).map(|j| format!("__x{j}")).collect();
            let pattern = Pat::Constructor {
                id: NodeId::fresh(),
                name: v.name.clone(),
                args: field_vars
                    .iter()
                    .map(|name| Pat::Var {
                        id: NodeId::fresh(),
                        name: name.clone(),
                        span,
                    })
                    .collect(),
                span,
            };
            let shape_expr = build_variant_shape_expr(&v.fields, &field_vars, span);
            // Variant <shape> — constructor name lives in the type.
            let variant = apply_ctor(&generic_name("Variant"), shape_expr, span);
            let or_wrapped = or_wrap_expr(variant, i, n, span);
            let adt_wrapped = apply2(
                &generic_name("Adt"),
                string_lit(type_name, span),
                or_wrapped,
                span,
            );
            let body = apply_ctor(&rep_name, adt_wrapped, span);
            Annotated::bare(CaseArm {
                pattern,
                guard: None,
                body,
                span,
            })
        })
        .collect();
    let to_body = Expr::synth(
        span,
        ExprKind::Case {
            scrutinee: Box::new(Expr::synth(
                span,
                ExprKind::Var {
                    name: param_name.clone(),
                },
            )),
            arms: to_arms,
            dangling_trivia: vec![],
        },
    );
    let to_method = Annotated::bare(ImplMethod {
        name: "to".into(),
        name_span: Span { start: 0, end: 0 },
        params: vec![Pat::Var {
            id: NodeId::fresh(),
            name: param_name.clone(),
            span,
        }],
        body: to_body,
    });

    // 3. `from __val = case __val { Rep__T (or-pat (Labeled _ shape-pat)) -> Ctor args; ... }`
    let from_param = "__rep".to_string();
    let from_arms: Vec<Annotated<CaseArm>> = variants
        .iter()
        .enumerate()
        .map(|(i, ann_v)| {
            let v = &ann_v.node;
            let field_vars: Vec<String> = (0..v.fields.len()).map(|j| format!("__y{j}")).collect();
            let shape_pat = build_variant_shape_pat(&v.fields, &field_vars, span);
            let variant_pat = Pat::Constructor {
                id: NodeId::fresh(),
                name: generic_name("Variant"),
                args: vec![shape_pat],
                span,
            };
            let or_wrapped_pat = or_wrap_pat(variant_pat, i, n, span);
            let adt_pat = Pat::Constructor {
                id: NodeId::fresh(),
                name: generic_name("Adt"),
                args: vec![
                    Pat::Wildcard {
                        id: NodeId::fresh(),
                        span,
                    },
                    or_wrapped_pat,
                ],
                span,
            };
            let outer_pat = Pat::Constructor {
                id: NodeId::fresh(),
                name: rep_name.clone(),
                args: vec![adt_pat],
                span,
            };
            let body = build_ctor_application(&v.name, &field_vars, span);
            Annotated::bare(CaseArm {
                pattern: outer_pat,
                guard: None,
                body,
                span,
            })
        })
        .collect();
    let from_body = Expr::synth(
        span,
        ExprKind::Case {
            scrutinee: Box::new(Expr::synth(
                span,
                ExprKind::Var {
                    name: from_param.clone(),
                },
            )),
            arms: from_arms,
            dangling_trivia: vec![],
        },
    );
    let from_method = Annotated::bare(ImplMethod {
        name: "from".into(),
        name_span: Span { start: 0, end: 0 },
        params: vec![Pat::Var {
            id: NodeId::fresh(),
            name: from_param,
            span,
        }],
        body: from_body,
    });

    let rep_with_params = apply_type_params(&rep_name, type_params);
    let impl_def = Decl::ImplDef {
        trait_name_span: Span { start: 0, end: 0 },
        target_type_span: Span { start: 0, end: 0 },
        target_type_expr: None,
        id: NodeId::fresh(),
        doc: vec![],
        trait_name: "Generic".into(),
        trait_type_args: vec![rep_with_params],
        target_type: type_name.into(),
        type_params: type_params.to_vec(),
        where_clause: vec![],
        where_apps: vec![],
        needs: vec![],
        methods: vec![to_method, from_method],
        routed_derive_info: None,
        span,
        dangling_trivia: vec![],
    };

    Ok(vec![rep_typedef, impl_def])
}


/// Build the inner Rep type for an ADT: right-leaning `Or` chain wrapping
/// `Labeled <variant_shape>` for each variant.
pub(crate) fn build_adt_rep_inner_type(variants: &[Annotated<TypeConstructor>]) -> TypeExpr {
    let variant_shapes: Vec<TypeExpr> = variants
        .iter()
        .map(|v| {
            // Variant 'CtorName <shape> — constructor name lives in the type.
            type_app(
                type_app(type_named("Variant"), type_symbol(&v.node.name)),
                build_variant_shape_type(&v.node.fields),
            )
        })
        .collect();
    let mut iter = variant_shapes.into_iter().rev();
    let mut acc = iter.next().unwrap();
    for prev in iter {
        acc = type_app(type_app(type_named("Or"), prev), acc);
    }
    acc
}


/// Variant shape type: U1 for 0 fields, single field rep for 1, right-leaning
/// And chain for >=2.
pub(crate) fn build_variant_shape_type(fields: &[(Option<String>, TypeExpr)]) -> TypeExpr {
    if fields.is_empty() {
        return type_named("U1");
    }
    let n = fields.len();
    let mut acc = field_rep_type_adt(&fields[n - 1].0, &fields[n - 1].1);
    for i in (0..n - 1).rev() {
        acc = type_app(
            type_app(
                type_named("And"),
                field_rep_type_adt(&fields[i].0, &fields[i].1),
            ),
            acc,
        );
    }
    acc
}


/// For a single ADT constructor field: `Labeled 'lbl (Leaf T)` if labeled,
/// else `Leaf T`.
pub(crate) fn field_rep_type_adt(label: &Option<String>, ty: &TypeExpr) -> TypeExpr {
    let leaf = type_app(type_named("Leaf"), ty.clone());
    match label {
        Some(lbl) => type_app(type_app(type_named("Labeled"), type_symbol(lbl)), leaf),
        None => leaf,
    }
}


/// Expression form of `build_variant_shape_type`: builds the And/Labeled/Leaf
/// expression tree from already-bound field variables.
pub(crate) fn build_variant_shape_expr(
    fields: &[(Option<String>, TypeExpr)],
    field_vars: &[String],
    span: Span,
) -> Expr {
    if fields.is_empty() {
        return Expr::synth(
            span,
            ExprKind::Constructor {
                name: generic_name("U1"),
            },
        );
    }
    let leaf_for = |label: &Option<String>, var: &str| -> Expr {
        let leaf = apply_ctor(
            &generic_name("Leaf"),
            Expr::synth(span, ExprKind::Var { name: var.into() }),
            span,
        );
        match label {
            // Labeled (Leaf var) — name lives in the type now.
            Some(_) => apply_ctor(&generic_name("Labeled"), leaf, span),
            None => leaf,
        }
    };
    let n = fields.len();
    let mut acc = leaf_for(&fields[n - 1].0, &field_vars[n - 1]);
    for i in (0..n - 1).rev() {
        let cur = leaf_for(&fields[i].0, &field_vars[i]);
        acc = apply2(&generic_name("And"), cur, acc, span);
    }
    acc
}


/// Pattern form of the variant shape, binding each field to the matching name
/// in `field_vars`.
pub(crate) fn build_variant_shape_pat(
    fields: &[(Option<String>, TypeExpr)],
    field_vars: &[String],
    span: Span,
) -> Pat {
    if fields.is_empty() {
        return Pat::Constructor {
            id: NodeId::fresh(),
            name: generic_name("U1"),
            args: vec![],
            span,
        };
    }
    let leaf_pat_for = |label: &Option<String>, var: &str| -> Pat {
        let leaf = Pat::Constructor {
            id: NodeId::fresh(),
            name: generic_name("Leaf"),
            args: vec![Pat::Var {
                id: NodeId::fresh(),
                name: var.into(),
                span,
            }],
            span,
        };
        match label {
            // Labeled (Leaf var) — name lives in the type now.
            Some(_) => Pat::Constructor {
                id: NodeId::fresh(),
                name: generic_name("Labeled"),
                args: vec![leaf],
                span,
            },
            None => leaf,
        }
    };
    let n = fields.len();
    let mut acc = leaf_pat_for(&fields[n - 1].0, &field_vars[n - 1]);
    for i in (0..n - 1).rev() {
        let cur = leaf_pat_for(&fields[i].0, &field_vars[i]);
        acc = Pat::Constructor {
            id: NodeId::fresh(),
            name: generic_name("And"),
            args: vec![cur, acc],
            span,
        };
    }
    acc
}


/// `Or_Right^i (Or_Left inner)` for i < total-1; `Or_Right^(total-1) inner`
/// for the last variant; bare `inner` if there's only one variant.
pub(crate) fn or_wrap_expr(inner: Expr, index: usize, total: usize, span: Span) -> Expr {
    if total == 1 {
        return inner;
    }
    let mut e = if index == total - 1 {
        inner
    } else {
        apply_ctor(&generic_name("Or_Left"), inner, span)
    };
    for _ in 0..index {
        e = apply_ctor(&generic_name("Or_Right"), e, span);
    }
    e
}


/// Pattern counterpart to `or_wrap_expr`.
pub(crate) fn or_wrap_pat(inner: Pat, index: usize, total: usize, span: Span) -> Pat {
    if total == 1 {
        return inner;
    }
    let mut p = if index == total - 1 {
        inner
    } else {
        Pat::Constructor {
            id: NodeId::fresh(),
            name: generic_name("Or_Left"),
            args: vec![inner],
            span,
        }
    };
    for _ in 0..index {
        p = Pat::Constructor {
            id: NodeId::fresh(),
            name: generic_name("Or_Right"),
            args: vec![p],
            span,
        };
    }
    p
}


/// Build a curried application of `ctor` to each `field_var`. For nullary
/// constructors, returns just `Ctor`.
pub(crate) fn build_ctor_application(ctor: &str, field_vars: &[String], span: Span) -> Expr {
    let mut e = Expr::synth(span, ExprKind::Constructor { name: ctor.into() });
    for v in field_vars {
        e = Expr::synth(
            span,
            ExprKind::App {
                func: Box::new(e),
                arg: Box::new(Expr::synth(span, ExprKind::Var { name: v.clone() })),
            },
        );
    }
    e
}


/// Build the inner Rep type (without the outer newtype wrapping). Right-leaning
/// And chain for >=2 fields; `Labeled 'name (Leaf T)` for 1 field; U1 for 0.
pub(crate) fn build_rep_type_inner(fields: &[(String, TypeExpr)]) -> TypeExpr {
    if fields.is_empty() {
        return type_named("U1");
    }
    let mut iter = fields.iter().rev();
    let (last_name, last_ty) = iter.next().unwrap();
    let mut acc = field_rep_type(last_name, last_ty);
    for (fname, ty) in iter {
        acc = type_app(type_app(type_named("And"), field_rep_type(fname, ty)), acc);
    }
    acc
}


/// Record field rep type: `Labeled 'fieldname (Leaf T)`. The field name is
/// carried as a type-level symbol; library codecs recover the string via
/// `KnownSymbol`.
pub(crate) fn field_rep_type(name: &str, ty: &TypeExpr) -> TypeExpr {
    type_app(
        type_app(type_named("Labeled"), type_symbol(name)),
        type_app(type_named("Leaf"), ty.clone()),
    )
}


/// Build the `to` body's inner expression (everything inside the __Rep_R newtype wrap).
pub(crate) fn build_rep_to_expr(fields: &[(String, TypeExpr)], record_var: &Expr, span: Span) -> Expr {
    if fields.is_empty() {
        return Expr::synth(
            span,
            ExprKind::Constructor {
                name: generic_name("U1"),
            },
        );
    }
    let labeled_for = |fname: &str| -> Expr {
        // Labeled (Leaf record_var.fname) — name lives in the type now.
        let field_access = Expr::synth(
            span,
            ExprKind::FieldAccess {
                expr: Box::new(record_var.clone()),
                field: fname.into(),
                record_name: None,
            },
        );
        let leaf = apply_ctor(&generic_name("Leaf"), field_access, span);
        apply_ctor(&generic_name("Labeled"), leaf, span)
    };

    let mut iter = fields.iter().rev();
    let (last_name, _) = iter.next().unwrap();
    let mut acc = labeled_for(last_name);
    for (fname, _) in iter {
        acc = apply2(&generic_name("And"), labeled_for(fname), acc, span);
    }
    acc
}


/// Build the inner pattern matched by `from`: matches the And/Labeled/Leaf tree
/// and binds each field's value to the corresponding variable in `field_vars`.
pub(crate) fn build_rep_from_pattern(field_vars: &[String], span: Span) -> Pat {
    if field_vars.is_empty() {
        return Pat::Constructor {
            id: NodeId::fresh(),
            name: generic_name("U1"),
            args: vec![],
            span,
        };
    }
    let labeled_pat = |var: &str| -> Pat {
        // Labeled (Leaf var) — name is at the type level, no wildcard needed.
        Pat::Constructor {
            id: NodeId::fresh(),
            name: generic_name("Labeled"),
            args: vec![Pat::Constructor {
                id: NodeId::fresh(),
                name: generic_name("Leaf"),
                args: vec![Pat::Var {
                    id: NodeId::fresh(),
                    name: var.into(),
                    span,
                }],
                span,
            }],
            span,
        }
    };

    let mut iter = field_vars.iter().rev();
    let last = iter.next().unwrap();
    let mut acc = labeled_pat(last);
    for v in iter {
        acc = Pat::Constructor {
            id: NodeId::fresh(),
            name: generic_name("And"),
            args: vec![labeled_pat(v), acc],
            span,
        };
    }
    acc
}

