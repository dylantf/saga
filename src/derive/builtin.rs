use super::*;
use crate::ast::*;
use crate::token::Span;
use crate::token::StringKind;

/// Generate `impl Show/Debug for R { show/debug r = "R { field: " <> show/debug r.field <> ... <> "}" }`
pub(crate) fn derive_record_stringify(
    trait_name: &str,
    method_name: &str,
    record_name: &str,
    type_params: &[TypeParam],
    fields: &[Annotated<(String, TypeExpr)>],
    span: Span,
) -> Decl {
    let param_name = "__val".to_string();
    let param_var = Expr::synth(
        span,
        ExprKind::Var {
            name: param_name.clone(),
        },
    );

    let plain_fields: Vec<(String, TypeExpr)> = fields.iter().map(|a| a.node.clone()).collect();
    let body = build_record_debug_expr(method_name, record_name, &plain_fields, &param_var, span);

    // Each type param needs the same trait (same as ADT derive)
    let where_clause: Vec<TraitBound> = type_params
        .iter()
        .map(|tp| TraitBound {
            type_var: tp.name.clone(),
            traits: vec![TraitRef {
                id: NodeId::fresh(),
                name: trait_name.into(),
                type_args: vec![],
                span: Span { start: 0, end: 0 },
            }],
        })
        .collect();

    Decl::ImplDef {
        trait_name_span: crate::token::Span { start: 0, end: 0 },
        target_type_span: crate::token::Span { start: 0, end: 0 },
        target_type_expr: None,
        id: NodeId::fresh(),
        doc: vec![],
        trait_name: trait_name.into(),
        trait_type_args: vec![],
        target_type: record_name.into(),
        type_params: type_params.to_vec(),
        where_clause,
        where_apps: vec![],
        needs: vec![],
        methods: vec![Annotated::bare(ImplMethod {
            name: method_name.into(),
            name_span: Span { start: 0, end: 0 },
            params: vec![Pat::Var {
                id: NodeId::fresh(),
                name: param_name,
                span,
            }],
            body,
        })],
        routed_derive_info: None,
        span,
        dangling_trivia: vec![],
    }
}

/// Generate `impl Default for R { default = R { field: default, ... } }`.
pub(crate) fn derive_record_default(
    record_name: &str,
    type_params: &[TypeParam],
    fields: &[Annotated<(String, TypeExpr)>],
    span: Span,
) -> Decl {
    let plain_fields: Vec<(String, TypeExpr)> = fields.iter().map(|a| a.node.clone()).collect();
    let body_fields: Vec<(String, Span, Expr)> = plain_fields
        .iter()
        .map(|(field_name, _)| {
            (
                field_name.clone(),
                Span { start: 0, end: 0 },
                Expr::synth(
                    span,
                    ExprKind::Var {
                        name: "default".into(),
                    },
                ),
            )
        })
        .collect();
    let body = Expr::synth(
        span,
        ExprKind::RecordCreate {
            name: record_name.into(),
            fields: body_fields,
            record_name: None,
        },
    );

    let where_clause: Vec<TraitBound> = type_params
        .iter()
        .filter(|tp| {
            plain_fields
                .iter()
                .any(|(_, ty)| type_expr_contains_var(ty, &tp.name))
        })
        .map(|tp| TraitBound {
            type_var: tp.name.clone(),
            traits: vec![TraitRef {
                id: NodeId::fresh(),
                name: "Default".into(),
                type_args: vec![],
                span: Span { start: 0, end: 0 },
            }],
        })
        .collect();

    Decl::ImplDef {
        trait_name_span: crate::token::Span { start: 0, end: 0 },
        target_type_span: crate::token::Span { start: 0, end: 0 },
        target_type_expr: None,
        id: NodeId::fresh(),
        doc: vec![],
        trait_name: "Default".into(),
        trait_type_args: vec![],
        target_type: record_name.into(),
        type_params: type_params.to_vec(),
        where_clause,
        where_apps: vec![],
        needs: vec![],
        methods: vec![Annotated::bare(ImplMethod {
            name: "default".into(),
            name_span: Span { start: 0, end: 0 },
            params: vec![],
            body,
        })],
        routed_derive_info: None,
        span,
        dangling_trivia: vec![],
    }
}

/// Build the debug string expression for a record. For fields with anonymous
/// record types, generates inline formatting instead of calling `debug`.
pub(crate) fn build_record_debug_expr(
    method_name: &str,
    label: &str,
    fields: &[(String, TypeExpr)],
    base_expr: &Expr,
    span: Span,
) -> Expr {
    let mut parts: Vec<Expr> = Vec::new();
    let mut prefix = if label.is_empty() {
        "{ ".to_string()
    } else {
        format!("{label} {{ ")
    };

    for (i, (field_name, ty)) in fields.iter().enumerate() {
        if i > 0 {
            prefix.push_str(", ");
        }
        prefix.push_str(field_name);
        prefix.push_str(": ");
        parts.push(Expr::synth(
            span,
            ExprKind::Lit {
                value: Lit::String(prefix.clone(), StringKind::Normal),
            },
        ));
        prefix.clear();

        let field_access = Expr::synth(
            span,
            ExprKind::FieldAccess {
                expr: Box::new(base_expr.clone()),
                field: field_name.clone(),
                record_name: None,
            },
        );

        match ty {
            TypeExpr::Record {
                fields: inner_fields,
                ..
            } => {
                // Inline the anonymous record's debug output
                parts.push(build_record_debug_expr(
                    method_name,
                    "",
                    inner_fields,
                    &field_access,
                    span,
                ));
            }
            _ => {
                // Call debug/show on the field value
                parts.push(Expr::synth(
                    span,
                    ExprKind::App {
                        func: Box::new(Expr::synth(
                            span,
                            ExprKind::Var {
                                name: method_name.into(),
                            },
                        )),
                        arg: Box::new(field_access),
                    },
                ));
            }
        }
    }

    parts.push(Expr::synth(
        span,
        ExprKind::Lit {
            value: Lit::String(" }".into(), StringKind::Normal),
        },
    ));

    parts
        .into_iter()
        .reduce(|acc, part| {
            Expr::synth(
                span,
                ExprKind::BinOp {
                    op: BinOp::Concat,
                    left: Box::new(acc),
                    right: Box::new(part),
                },
            )
        })
        .unwrap()
}

pub(crate) fn generate_derive(
    trait_name: &str,
    type_name: &str,
    type_params: &[TypeParam],
    variants: &[Annotated<TypeConstructor>],
    span: Span,
) -> Option<Decl> {
    // Use bare trait name — deriving works with well-known traits only.
    // The parser may produce qualified names (e.g. "Std.Base.Show") if written that way.
    let bare = trait_name.rsplit('.').next().unwrap_or(trait_name);
    match bare {
        "Show" => Some(derive_stringify(
            "Show",
            "show",
            type_name,
            type_params,
            variants,
            span,
        )),
        "Debug" => Some(derive_stringify(
            "Debug",
            "debug",
            type_name,
            type_params,
            variants,
            span,
        )),
        "Eq" => Some(derive_marker_trait("Eq", type_name, type_params, span)),
        "Ord" => Some(derive_ord(type_name, type_params, variants, span)),
        "Enum" => Some(derive_enum(type_name, variants, span)),
        // "Generic" is handled by `expand_derives` via `derive_adt_generic`
        // because it emits multiple decls (TypeDef + ImplDef).
        _ => None,
    }
}

/// Generate `impl Show/Debug for T { show/debug x = case x { ... } }`
pub(crate) fn derive_stringify(
    trait_name: &str,
    method_name: &str,
    type_name: &str,
    type_params: &[TypeParam],
    variants: &[Annotated<TypeConstructor>],
    span: Span,
) -> Decl {
    let arms: Vec<Annotated<CaseArm>> = variants
        .iter()
        .map(|ann_variant| {
            let variant = &ann_variant.node;
            let ctor_name = &variant.name;

            if variant.fields.is_empty() {
                // `Ctor -> "Ctor"`
                Annotated::bare(CaseArm {
                    pattern: Pat::Constructor {
                        id: NodeId::fresh(),
                        name: ctor_name.clone(),
                        args: vec![],
                        span,
                    },
                    guard: None,
                    body: Expr::synth(
                        span,
                        ExprKind::Lit {
                            value: Lit::String(ctor_name.clone(), StringKind::Normal),
                        },
                    ),
                    span,
                })
            } else {
                // Generate field variable names
                let field_vars: Vec<String> = (0..variant.fields.len())
                    .map(|i| format!("__x{}", i))
                    .collect();

                let pattern = Pat::Constructor {
                    id: NodeId::fresh(),
                    name: ctor_name.clone(),
                    args: field_vars
                        .iter()
                        .map(|v| Pat::Var {
                            id: NodeId::fresh(),
                            name: v.clone(),
                            span,
                        })
                        .collect(),
                    span,
                };

                // Build: "Ctor(" <> show/debug __x0 <> ", " <> show/debug __x1 <> ")"
                // With labels: "Ctor(label: " <> show/debug __x0 <> ... <> ")"
                let mut parts: Vec<Expr> = Vec::new();
                let mut prefix = format!("{ctor_name}(");

                for (i, (label, _ty)) in variant.fields.iter().enumerate() {
                    if i > 0 {
                        prefix.push_str(", ");
                    }
                    if let Some(lbl) = label {
                        prefix.push_str(lbl);
                        prefix.push_str(": ");
                    }
                    parts.push(Expr::synth(
                        span,
                        ExprKind::Lit {
                            value: Lit::String(prefix.clone(), StringKind::Normal),
                        },
                    ));
                    prefix.clear();

                    // `show/debug __xi`
                    parts.push(Expr::synth(
                        span,
                        ExprKind::App {
                            func: Box::new(Expr::synth(
                                span,
                                ExprKind::Var {
                                    name: method_name.into(),
                                },
                            )),
                            arg: Box::new(Expr::synth(
                                span,
                                ExprKind::Var {
                                    name: field_vars[i].clone(),
                                },
                            )),
                        },
                    ));
                }

                parts.push(Expr::synth(
                    span,
                    ExprKind::Lit {
                        value: Lit::String(")".into(), StringKind::Normal),
                    },
                ));

                let body = parts
                    .into_iter()
                    .reduce(|acc, part| {
                        Expr::synth(
                            span,
                            ExprKind::BinOp {
                                op: BinOp::Concat,
                                left: Box::new(acc),
                                right: Box::new(part),
                            },
                        )
                    })
                    .unwrap();

                Annotated::bare(CaseArm {
                    pattern,
                    guard: None,
                    body,
                    span,
                })
            }
        })
        .collect();

    let scrutinee_name = "__val".to_string();
    let body = Expr::synth(
        span,
        ExprKind::Case {
            scrutinee: Box::new(Expr::synth(
                span,
                ExprKind::Var {
                    name: scrutinee_name.clone(),
                },
            )),
            arms,
            dangling_trivia: vec![],
        },
    );

    // Each type param needs the same trait
    let where_clause: Vec<TraitBound> = type_params
        .iter()
        .map(|tp| TraitBound {
            type_var: tp.name.clone(),
            traits: vec![TraitRef {
                id: NodeId::fresh(),
                name: trait_name.into(),
                type_args: vec![],
                span: Span { start: 0, end: 0 },
            }],
        })
        .collect();

    Decl::ImplDef {
        trait_name_span: crate::token::Span { start: 0, end: 0 },
        target_type_span: crate::token::Span { start: 0, end: 0 },
        target_type_expr: None,
        id: NodeId::fresh(),
        doc: vec![],
        trait_name: trait_name.into(),
        trait_type_args: vec![],
        target_type: type_name.into(),
        type_params: type_params.to_vec(),
        where_clause,
        where_apps: vec![],
        needs: vec![],
        methods: vec![Annotated::bare(ImplMethod {
            name: method_name.into(),
            name_span: Span { start: 0, end: 0 },
            params: vec![Pat::Var {
                id: NodeId::fresh(),
                name: scrutinee_name,
                span,
            }],
            body,
        })],
        routed_derive_info: None,
        span,
        dangling_trivia: vec![],
    }
}

/// Generate `impl Ord for T { compare x y = ... }` using declaration-order
/// constructor indexing and left-to-right field comparison.
pub(crate) fn derive_ord(
    type_name: &str,
    type_params: &[TypeParam],
    variants: &[Annotated<TypeConstructor>],
    span: Span,
) -> Decl {
    let x = "__x".to_string();
    let y = "__y".to_string();

    // Build same-constructor arms: (A(a0,a1), A(b0,b1)) -> field-by-field compare
    let mut arms: Vec<Annotated<CaseArm>> = variants
        .iter()
        .map(|ann_variant| {
            let variant = &ann_variant.node;
            let ctor = &variant.name;
            let arity = variant.fields.len();

            let a_vars: Vec<String> = (0..arity).map(|i| format!("__a{i}")).collect();
            let b_vars: Vec<String> = (0..arity).map(|i| format!("__b{i}")).collect();

            let pat_a = Pat::Constructor {
                id: NodeId::fresh(),
                name: ctor.clone(),
                args: a_vars
                    .iter()
                    .map(|v| Pat::Var {
                        id: NodeId::fresh(),
                        name: v.clone(),
                        span,
                    })
                    .collect(),
                span,
            };
            let pat_b = Pat::Constructor {
                id: NodeId::fresh(),
                name: ctor.clone(),
                args: b_vars
                    .iter()
                    .map(|v| Pat::Var {
                        id: NodeId::fresh(),
                        name: v.clone(),
                        span,
                    })
                    .collect(),
                span,
            };
            let pattern = Pat::Tuple {
                id: NodeId::fresh(),
                elements: vec![pat_a, pat_b],
                span,
            };

            let body = if arity == 0 {
                // Same nullary constructor: always Eq
                Expr::synth(span, ExprKind::Constructor { name: "Eq".into() })
            } else {
                // Compare fields left-to-right, short-circuit on non-Eq
                build_field_compare(&a_vars, &b_vars, span)
            };

            Annotated::bare(CaseArm {
                pattern,
                guard: None,
                body,
                span,
            })
        })
        .collect();

    // Wildcard arm for different constructors: compare by index.
    if variants.len() > 1 {
        let index_case = |var: &str| -> Expr {
            Expr::synth(
                span,
                ExprKind::Case {
                    scrutinee: Box::new(Expr::synth(span, ExprKind::Var { name: var.into() })),
                    arms: variants
                        .iter()
                        .enumerate()
                        .map(|(i, ann_v)| {
                            let v = &ann_v.node;
                            let wildcards: Vec<Pat> = (0..v.fields.len())
                                .map(|_| Pat::Wildcard {
                                    id: NodeId::fresh(),
                                    span,
                                })
                                .collect();
                            Annotated::bare(CaseArm {
                                pattern: Pat::Constructor {
                                    id: NodeId::fresh(),
                                    name: v.name.clone(),
                                    args: wildcards,
                                    span,
                                },
                                guard: None,
                                body: Expr::synth(
                                    span,
                                    ExprKind::Lit {
                                        value: Lit::Int((i as i64).to_string(), i as i64),
                                    },
                                ),
                                span,
                            })
                        })
                        .collect(),
                    dangling_trivia: vec![],
                },
            )
        };

        // compare (case __x { ... -> 0, ... -> 1 }) (case __y { ... })
        let compare_indices = Expr::synth(
            span,
            ExprKind::App {
                func: Box::new(Expr::synth(
                    span,
                    ExprKind::App {
                        func: Box::new(Expr::synth(
                            span,
                            ExprKind::Var {
                                name: "compare".into(),
                            },
                        )),
                        arg: Box::new(index_case(&x)),
                    },
                )),
                arg: Box::new(index_case(&y)),
            },
        );

        arms.push(Annotated::bare(CaseArm {
            pattern: Pat::Wildcard {
                id: NodeId::fresh(),
                span,
            },
            guard: None,
            body: compare_indices,
            span,
        }));
    }

    let body = Expr::synth(
        span,
        ExprKind::Case {
            scrutinee: Box::new(Expr::synth(
                span,
                ExprKind::Tuple {
                    elements: vec![
                        Expr::synth(span, ExprKind::Var { name: x.clone() }),
                        Expr::synth(span, ExprKind::Var { name: y.clone() }),
                    ],
                },
            )),
            arms,
            dangling_trivia: vec![],
        },
    );

    // Ord requires Eq, but Eq is BIF-dispatched (no dict), so only Ord
    // needs to be in the where clause for dictionary passing purposes.
    // The Eq supertrait constraint is still checked by the typechecker.
    let where_clause: Vec<TraitBound> = type_params
        .iter()
        .map(|tp| TraitBound {
            type_var: tp.name.clone(),
            traits: vec![TraitRef {
                id: NodeId::fresh(),
                name: "Ord".into(),
                type_args: vec![],
                span: Span { start: 0, end: 0 },
            }],
        })
        .collect();

    Decl::ImplDef {
        trait_name_span: crate::token::Span { start: 0, end: 0 },
        target_type_span: crate::token::Span { start: 0, end: 0 },
        target_type_expr: None,
        id: NodeId::fresh(),
        doc: vec![],
        trait_name: "Ord".into(),
        trait_type_args: vec![],
        target_type: type_name.into(),
        type_params: type_params.to_vec(),
        where_clause,
        where_apps: vec![],
        needs: vec![],
        methods: vec![Annotated::bare(ImplMethod {
            name: "compare".into(),
            name_span: Span { start: 0, end: 0 },
            params: vec![
                Pat::Var {
                    id: NodeId::fresh(),
                    name: x,
                    span,
                },
                Pat::Var {
                    id: NodeId::fresh(),
                    name: y,
                    span,
                },
            ],
            body,
        })],
        routed_derive_info: None,
        span,
        dangling_trivia: vec![],
    }
}

/// Build a left-to-right field comparison chain:
/// `case compare a0 b0 { Eq -> case compare a1 b1 { Eq -> ... Eq; o -> o }; o -> o }`
pub(crate) fn build_field_compare(a_vars: &[String], b_vars: &[String], span: Span) -> Expr {
    assert!(!a_vars.is_empty());

    // Start from the last field and build inward
    let mut result = Expr::synth(span, ExprKind::Constructor { name: "Eq".into() });

    for i in (0..a_vars.len()).rev() {
        let cmp_call = Expr::synth(
            span,
            ExprKind::App {
                func: Box::new(Expr::synth(
                    span,
                    ExprKind::App {
                        func: Box::new(Expr::synth(
                            span,
                            ExprKind::Var {
                                name: "compare".into(),
                            },
                        )),
                        arg: Box::new(Expr::synth(
                            span,
                            ExprKind::Var {
                                name: a_vars[i].clone(),
                            },
                        )),
                    },
                )),
                arg: Box::new(Expr::synth(
                    span,
                    ExprKind::Var {
                        name: b_vars[i].clone(),
                    },
                )),
            },
        );

        if i == a_vars.len() - 1 && a_vars.len() == 1 {
            // Single field: just return the compare result directly
            result = cmp_call;
        } else {
            // Wrap in: case compare ai bi { Eq -> <inner>; __other -> __other }
            let other_var = format!("__ord{i}");
            result = Expr::synth(
                span,
                ExprKind::Case {
                    scrutinee: Box::new(cmp_call),
                    arms: vec![
                        Annotated::bare(CaseArm {
                            pattern: Pat::Constructor {
                                id: NodeId::fresh(),
                                name: "Eq".into(),
                                args: vec![],
                                span,
                            },
                            guard: None,
                            body: result,
                            span,
                        }),
                        Annotated::bare(CaseArm {
                            pattern: Pat::Var {
                                id: NodeId::fresh(),
                                name: other_var.clone(),
                                span,
                            },
                            guard: None,
                            body: Expr::synth(span, ExprKind::Var { name: other_var }),
                            span,
                        }),
                    ],
                    dangling_trivia: vec![],
                },
            );
        }
    }

    result
}

/// Generate a method-less impl for an operator trait (e.g. Eq).
/// The trait is dispatched via BEAM BIFs, so no methods are needed --
/// we just register the impl so the typechecker accepts the constraint.
pub(crate) fn derive_marker_trait(
    trait_name: &str,
    type_name: &str,
    type_params: &[TypeParam],
    span: Span,
) -> Decl {
    let where_clause: Vec<TraitBound> = type_params
        .iter()
        .map(|tp| TraitBound {
            type_var: tp.name.clone(),
            traits: vec![TraitRef {
                id: NodeId::fresh(),
                name: trait_name.into(),
                type_args: vec![],
                span: Span { start: 0, end: 0 },
            }],
        })
        .collect();

    Decl::ImplDef {
        trait_name_span: crate::token::Span { start: 0, end: 0 },
        target_type_span: crate::token::Span { start: 0, end: 0 },
        target_type_expr: None,
        id: NodeId::fresh(),
        doc: vec![],
        trait_name: trait_name.into(),
        trait_type_args: vec![],
        target_type: type_name.into(),
        type_params: type_params.to_vec(),
        where_clause,
        where_apps: vec![],
        needs: vec![],
        methods: vec![],
        routed_derive_info: None,
        span,
        dangling_trivia: vec![],
    }
}

/// Generate `impl Enum for T { to_enum x = case x { ... }; from_enum n = case n { ... } }`
/// Only valid for types with all nullary constructors.
pub(crate) fn derive_enum(
    type_name: &str,
    variants: &[Annotated<TypeConstructor>],
    span: Span,
) -> Decl {
    for ann_v in variants {
        let v = &ann_v.node;
        if !v.fields.is_empty() {
            panic!(
                "cannot derive Enum for `{}`: constructor `{}` has fields (Enum requires all nullary constructors)",
                type_name, v.name
            );
        }
    }

    // to_enum x = case x { Red -> 0 | Green -> 1 | Blue -> 2 }
    let to_enum_param = "__val".to_string();
    let to_enum_body = Expr::synth(
        span,
        ExprKind::Case {
            scrutinee: Box::new(Expr::synth(
                span,
                ExprKind::Var {
                    name: to_enum_param.clone(),
                },
            )),
            arms: variants
                .iter()
                .enumerate()
                .map(|(i, ann_v)| {
                    Annotated::bare(CaseArm {
                        pattern: Pat::Constructor {
                            id: NodeId::fresh(),
                            name: ann_v.node.name.clone(),
                            args: vec![],
                            span,
                        },
                        guard: None,
                        body: Expr::synth(
                            span,
                            ExprKind::Lit {
                                value: Lit::Int((i as i64).to_string(), i as i64),
                            },
                        ),
                        span,
                    })
                })
                .collect(),
            dangling_trivia: vec![],
        },
    );

    // from_enum n = case n { 0 -> Red | 1 -> Green | 2 -> Blue | _ -> panic "invalid enum index" }
    let from_enum_param = "__n".to_string();
    let mut from_enum_arms: Vec<Annotated<CaseArm>> = variants
        .iter()
        .enumerate()
        .map(|(i, ann_v)| {
            Annotated::bare(CaseArm {
                pattern: Pat::Lit {
                    id: NodeId::fresh(),
                    value: Lit::Int((i as i64).to_string(), i as i64),
                    span,
                },
                guard: None,
                body: Expr::synth(
                    span,
                    ExprKind::Constructor {
                        name: ann_v.node.name.clone(),
                    },
                ),
                span,
            })
        })
        .collect();
    // Wildcard arm: panic on invalid index
    from_enum_arms.push(Annotated::bare(CaseArm {
        pattern: Pat::Wildcard {
            id: NodeId::fresh(),
            span,
        },
        guard: None,
        body: Expr::synth(
            span,
            ExprKind::App {
                func: Box::new(Expr::synth(
                    span,
                    ExprKind::Var {
                        name: "panic".into(),
                    },
                )),
                arg: Box::new(Expr::synth(
                    span,
                    ExprKind::Lit {
                        value: Lit::String(
                            format!("invalid enum index for {}", type_name),
                            StringKind::Normal,
                        ),
                    },
                )),
            },
        ),
        span,
    }));
    let from_enum_body = Expr::synth(
        span,
        ExprKind::Case {
            scrutinee: Box::new(Expr::synth(
                span,
                ExprKind::Var {
                    name: from_enum_param.clone(),
                },
            )),
            arms: from_enum_arms,
            dangling_trivia: vec![],
        },
    );

    Decl::ImplDef {
        trait_name_span: crate::token::Span { start: 0, end: 0 },
        target_type_span: crate::token::Span { start: 0, end: 0 },
        target_type_expr: None,
        id: NodeId::fresh(),
        doc: vec![],
        trait_name: "Enum".into(),
        trait_type_args: vec![],
        target_type: type_name.into(),
        type_params: vec![],
        where_clause: vec![],
        where_apps: vec![],
        needs: vec![],
        methods: vec![
            Annotated::bare(ImplMethod {
                name: "to_enum".into(),
                name_span: Span { start: 0, end: 0 },
                params: vec![Pat::Var {
                    id: NodeId::fresh(),
                    name: to_enum_param,
                    span,
                }],
                body: to_enum_body,
            }),
            Annotated::bare(ImplMethod {
                name: "from_enum".into(),
                name_span: Span { start: 0, end: 0 },
                params: vec![Pat::Var {
                    id: NodeId::fresh(),
                    name: from_enum_param,
                    span,
                }],
                body: from_enum_body,
            }),
        ],
        routed_derive_info: None,
        span,
        dangling_trivia: vec![],
    }
}
