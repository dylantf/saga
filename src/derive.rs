//! Deriving pass: expands `deriving (Show, ...)` clauses on type definitions
//! into synthetic `ImplDef` nodes. Runs before typechecking so the generated
//! impls are validated like any hand-written impl.

use crate::ast::*;
use crate::token::Span;

/// Expand all `deriving` clauses in a program, appending synthetic `ImplDef`
/// nodes after each `TypeDef` that has them.
pub fn expand_derives(program: &mut Vec<Decl>) {
    let mut extra = Vec::new();
    for decl in program.iter() {
        match decl {
            Decl::TypeDef {
                name,
                type_params,
                variants,
                deriving,
                span,
                ..
            } => {
                // Ord requires Eq (supertrait). Automatically derive Eq if Ord
                // is requested but Eq isn't explicitly listed.
                let needs_eq =
                    deriving.iter().any(|t| t == "Ord") && !deriving.iter().any(|t| t == "Eq");

                if needs_eq
                    && let Some(impl_def) =
                        generate_derive("Eq", name, type_params, variants, *span)
                {
                    extra.push(impl_def);
                }

                for trait_name in deriving {
                    if let Some(impl_def) =
                        generate_derive(trait_name, name, type_params, variants, *span)
                    {
                        extra.push(impl_def);
                    }
                }
            }
            Decl::RecordDef {
                name,
                type_params,
                fields,
                deriving,
                span,
                ..
            } => {
                for trait_name in deriving {
                    extra.push(generate_record_derive(trait_name, name, type_params, fields, *span));
                }
            }
            _ => {}
        }
    }
    program.extend(extra);
}

fn generate_record_derive(
    trait_name: &str,
    record_name: &str,
    type_params: &[String],
    fields: &[(String, TypeExpr)],
    span: Span,
) -> Decl {
    match trait_name {
        "Show" | "Debug" => derive_record_stringify(trait_name, if trait_name == "Show" { "show" } else { "debug" }, record_name, type_params, fields, span),
        other => panic!("cannot derive `{other}` for record `{record_name}` (only Show and Debug are supported for records)"),
    }
}

/// Generate `impl Show/Debug for R { show/debug r = "R { field: " <> show/debug r.field <> ... <> "}" }`
fn derive_record_stringify(
    trait_name: &str,
    method_name: &str,
    record_name: &str,
    type_params: &[String],
    fields: &[(String, TypeExpr)],
    span: Span,
) -> Decl {
    let param_name = "__val".to_string();
    let param_var = Expr::synth(span, ExprKind::Var { name: param_name.clone() });

    let body = build_record_debug_expr(method_name, record_name, fields, &param_var, span);

    // Each type param needs the same trait (same as ADT derive)
    let where_clause: Vec<TraitBound> = type_params
        .iter()
        .map(|tp| TraitBound {
            type_var: tp.clone(),
            traits: vec![(trait_name.into(), Span { start: 0, end: 0 })],
        })
        .collect();

    Decl::ImplDef { trait_name_span: crate::token::Span { start: 0, end: 0 }, target_type_span: crate::token::Span { start: 0, end: 0 },
        id: NodeId::fresh(),
        doc: vec![],
        trait_name: trait_name.into(),
        target_type: record_name.into(),
        type_params: type_params.to_vec(),
        where_clause,
        needs: vec![],
        methods: vec![(
            method_name.into(),
            Span { start: 0, end: 0 },
            vec![Pat::Var { id: NodeId::fresh(), name: param_name, span }],
            body,
        )],
        span,
    }
}

/// Build the debug string expression for a record. For fields with anonymous
/// record types, generates inline formatting instead of calling `debug`.
fn build_record_debug_expr(
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
        parts.push(Expr::synth(span, ExprKind::Lit { value: Lit::String(prefix.clone()) }));
        prefix.clear();

        let field_access = Expr::synth(span, ExprKind::FieldAccess {
            expr: Box::new(base_expr.clone()),
            field: field_name.clone(),
        });

        match ty {
            TypeExpr::Record { fields: inner_fields, .. } => {
                // Inline the anonymous record's debug output
                parts.push(build_record_debug_expr(method_name, "", inner_fields, &field_access, span));
            }
            _ => {
                // Call debug/show on the field value
                parts.push(Expr::synth(span, ExprKind::App {
                    func: Box::new(Expr::synth(span, ExprKind::Var { name: method_name.into() })),
                    arg: Box::new(field_access),
                }));
            }
        }
    }

    parts.push(Expr::synth(span, ExprKind::Lit { value: Lit::String(" }".into()) }));

    parts
        .into_iter()
        .reduce(|acc, part| {
            Expr::synth(span, ExprKind::BinOp {
                op: BinOp::Concat,
                left: Box::new(acc),
                right: Box::new(part),
            })
        })
        .unwrap()
}

fn generate_derive(
    trait_name: &str,
    type_name: &str,
    type_params: &[String],
    variants: &[TypeConstructor],
    span: Span,
) -> Option<Decl> {
    match trait_name {
        "Show" => Some(derive_stringify("Show", "show", type_name, type_params, variants, span)),
        "Debug" => Some(derive_stringify("Debug", "debug", type_name, type_params, variants, span)),
        "Eq" => Some(derive_marker_trait("Eq", type_name, type_params, span)),
        "Ord" => Some(derive_ord(type_name, type_params, variants, span)),
        "Enum" => Some(derive_enum(type_name, variants, span)),
        other => panic!("cannot derive `{other}` (only Show, Debug, Eq, Ord, and Enum are supported)"),
    }
}

/// Generate `impl Show/Debug for T { show/debug x = case x { ... } }`
fn derive_stringify(
    trait_name: &str,
    method_name: &str,
    type_name: &str,
    type_params: &[String],
    variants: &[TypeConstructor],
    span: Span,
) -> Decl {
    let arms: Vec<CaseArm> = variants
        .iter()
        .map(|variant| {
            let ctor_name = &variant.name;

            if variant.fields.is_empty() {
                // `Ctor -> "Ctor"`
                CaseArm {
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
                            value: Lit::String(ctor_name.clone()),
                        },
                    ),
                    span,
                }
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
                            value: Lit::String(prefix.clone()),
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
                        value: Lit::String(")".into()),
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

                CaseArm {
                    pattern,
                    guard: None,
                    body,
                    span,
                }
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
        },
    );

    // Each type param needs the same trait
    let where_clause: Vec<TraitBound> = type_params
        .iter()
        .map(|tp| TraitBound {
            type_var: tp.clone(),
            traits: vec![(trait_name.into(), Span { start: 0, end: 0 })],
        })
        .collect();

    Decl::ImplDef { trait_name_span: crate::token::Span { start: 0, end: 0 }, target_type_span: crate::token::Span { start: 0, end: 0 },
        id: NodeId::fresh(),
        doc: vec![],
        trait_name: trait_name.into(),
        target_type: type_name.into(),
        type_params: type_params.to_vec(),
        where_clause,
        needs: vec![],
        methods: vec![(
            method_name.into(),
            Span { start: 0, end: 0 },
            vec![Pat::Var {
                id: NodeId::fresh(),
                name: scrutinee_name,
                span,
            }],
            body,
        )],
        span,
    }
}

/// Generate `impl Ord for T { compare x y = ... }` using declaration-order
/// constructor indexing and left-to-right field comparison.
fn derive_ord(
    type_name: &str,
    type_params: &[String],
    variants: &[TypeConstructor],
    span: Span,
) -> Decl {
    let x = "__x".to_string();
    let y = "__y".to_string();

    // Build same-constructor arms: (A(a0,a1), A(b0,b1)) -> field-by-field compare
    let mut arms: Vec<CaseArm> = variants
        .iter()
        .map(|variant| {
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

            CaseArm {
                pattern,
                guard: None,
                body,
                span,
            }
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
                        .map(|(i, v)| {
                            let wildcards: Vec<Pat> = (0..v.fields.len())
                                .map(|_| Pat::Wildcard { id: NodeId::fresh(), span })
                                .collect();
                            CaseArm {
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
                                        value: Lit::Int(i as i64),
                                    },
                                ),
                                span,
                            }
                        })
                        .collect(),
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

        arms.push(CaseArm {
            pattern: Pat::Wildcard { id: NodeId::fresh(), span },
            guard: None,
            body: compare_indices,
            span,
        });
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
        },
    );

    // Ord requires Eq, but Eq is BIF-dispatched (no dict), so only Ord
    // needs to be in the where clause for dictionary passing purposes.
    // The Eq supertrait constraint is still checked by the typechecker.
    let where_clause: Vec<TraitBound> = type_params
        .iter()
        .map(|tp| TraitBound {
            type_var: tp.clone(),
            traits: vec![("Ord".into(), Span { start: 0, end: 0 })],
        })
        .collect();

    Decl::ImplDef { trait_name_span: crate::token::Span { start: 0, end: 0 }, target_type_span: crate::token::Span { start: 0, end: 0 },
        id: NodeId::fresh(),
        doc: vec![],
        trait_name: "Ord".into(),
        target_type: type_name.into(),
        type_params: type_params.to_vec(),
        where_clause,
        needs: vec![],
        methods: vec![(
            "compare".into(),
            Span { start: 0, end: 0 },
            vec![Pat::Var { id: NodeId::fresh(), name: x, span }, Pat::Var { id: NodeId::fresh(), name: y, span }],
            body,
        )],
        span,
    }
}

/// Build a left-to-right field comparison chain:
/// `case compare a0 b0 { Eq -> case compare a1 b1 { Eq -> ... Eq; o -> o }; o -> o }`
fn build_field_compare(a_vars: &[String], b_vars: &[String], span: Span) -> Expr {
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
                        CaseArm {
                            pattern: Pat::Constructor {
                                id: NodeId::fresh(),
                                name: "Eq".into(),
                                args: vec![],
                                span,
                            },
                            guard: None,
                            body: result,
                            span,
                        },
                        CaseArm {
                            pattern: Pat::Var {
                                id: NodeId::fresh(),
                                name: other_var.clone(),
                                span,
                            },
                            guard: None,
                            body: Expr::synth(span, ExprKind::Var { name: other_var }),
                            span,
                        },
                    ],
                },
            );
        }
    }

    result
}

/// Generate a method-less impl for an operator trait (e.g. Eq).
/// The trait is dispatched via BEAM BIFs, so no methods are needed --
/// we just register the impl so the typechecker accepts the constraint.
fn derive_marker_trait(
    trait_name: &str,
    type_name: &str,
    type_params: &[String],
    span: Span,
) -> Decl {
    let where_clause: Vec<TraitBound> = type_params
        .iter()
        .map(|tp| TraitBound {
            type_var: tp.clone(),
            traits: vec![(trait_name.into(), Span { start: 0, end: 0 })],
        })
        .collect();

    Decl::ImplDef { trait_name_span: crate::token::Span { start: 0, end: 0 }, target_type_span: crate::token::Span { start: 0, end: 0 },
        id: NodeId::fresh(),
        doc: vec![],
        trait_name: trait_name.into(),
        target_type: type_name.into(),
        type_params: type_params.to_vec(),
        where_clause,
        needs: vec![],
        methods: vec![],
        span,
    }
}

/// Generate `impl Enum for T { to_enum x = case x { ... }; from_enum n = case n { ... } }`
/// Only valid for types with all nullary constructors.
fn derive_enum(
    type_name: &str,
    variants: &[TypeConstructor],
    span: Span,
) -> Decl {
    for v in variants {
        if !v.fields.is_empty() {
            panic!(
                "cannot derive Enum for `{}`: constructor `{}` has fields (Enum requires all nullary constructors)",
                type_name, v.name
            );
        }
    }

    // to_enum x = case x { Red -> 0 | Green -> 1 | Blue -> 2 }
    let to_enum_param = "__val".to_string();
    let to_enum_body = Expr::synth(span, ExprKind::Case {
        scrutinee: Box::new(Expr::synth(span, ExprKind::Var { name: to_enum_param.clone() })),
        arms: variants.iter().enumerate().map(|(i, v)| {
            CaseArm {
                pattern: Pat::Constructor { id: NodeId::fresh(), name: v.name.clone(), args: vec![], span },
                guard: None,
                body: Expr::synth(span, ExprKind::Lit { value: Lit::Int(i as i64) }),
                span,
            }
        }).collect(),
    });

    // from_enum n = case n { 0 -> Red | 1 -> Green | 2 -> Blue | _ -> panic "invalid enum index" }
    let from_enum_param = "__n".to_string();
    let mut from_enum_arms: Vec<CaseArm> = variants.iter().enumerate().map(|(i, v)| {
        CaseArm {
            pattern: Pat::Lit { id: NodeId::fresh(), value: Lit::Int(i as i64), span },
            guard: None,
            body: Expr::synth(span, ExprKind::Constructor { name: v.name.clone() }),
            span,
        }
    }).collect();
    // Wildcard arm: panic on invalid index
    from_enum_arms.push(CaseArm {
        pattern: Pat::Wildcard { id: NodeId::fresh(), span },
        guard: None,
        body: Expr::synth(span, ExprKind::App {
            func: Box::new(Expr::synth(span, ExprKind::Var { name: "panic".into() })),
            arg: Box::new(Expr::synth(span, ExprKind::Lit {
                value: Lit::String(format!("invalid enum index for {}", type_name)),
            })),
        }),
        span,
    });
    let from_enum_body = Expr::synth(span, ExprKind::Case {
        scrutinee: Box::new(Expr::synth(span, ExprKind::Var { name: from_enum_param.clone() })),
        arms: from_enum_arms,
    });

    Decl::ImplDef { trait_name_span: crate::token::Span { start: 0, end: 0 }, target_type_span: crate::token::Span { start: 0, end: 0 },
        id: NodeId::fresh(),
        doc: vec![],
        trait_name: "Enum".into(),
        target_type: type_name.into(),
        type_params: vec![],
        where_clause: vec![],
        needs: vec![],
        methods: vec![
            (
                "to_enum".into(),
                Span { start: 0, end: 0 },
                vec![Pat::Var { id: NodeId::fresh(), name: to_enum_param, span }],
                to_enum_body,
            ),
            (
                "from_enum".into(),
                Span { start: 0, end: 0 },
                vec![Pat::Var { id: NodeId::fresh(), name: from_enum_param, span }],
                from_enum_body,
            ),
        ],
        span,
    }
}
