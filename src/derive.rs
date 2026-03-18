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
        if let Decl::TypeDef {
            name,
            type_params,
            variants,
            deriving,
            span,
            ..
        } = decl
        {
            for trait_name in deriving {
                if let Some(impl_def) =
                    generate_derive(trait_name, name, type_params, variants, *span)
                {
                    extra.push(impl_def);
                }
            }
        }
    }
    program.extend(extra);
}

fn generate_derive(
    trait_name: &str,
    type_name: &str,
    type_params: &[String],
    variants: &[TypeConstructor],
    span: Span,
) -> Option<Decl> {
    match trait_name {
        "Show" => Some(derive_show(type_name, type_params, variants, span)),
        "Eq" => Some(derive_marker_trait("Eq", type_name, type_params, span)),
        "Ord" => Some(derive_ord(type_name, type_params, variants, span)),
        other => panic!("cannot derive `{other}` (only Show, Eq, and Ord are supported)"),
    }
}

/// Generate `impl Show for T { show x = case x { ... } }`
fn derive_show(
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
                        name: ctor_name.clone(),
                        args: vec![],
                        span,
                    },
                    guard: None,
                    body: Expr::Lit {
                        value: Lit::String(ctor_name.clone()),
                        span,
                    },
                    span,
                }
            } else {
                // Generate field variable names
                let field_vars: Vec<String> = (0..variant.fields.len())
                    .map(|i| format!("__x{}", i))
                    .collect();

                let pattern = Pat::Constructor {
                    name: ctor_name.clone(),
                    args: field_vars
                        .iter()
                        .map(|v| Pat::Var {
                            name: v.clone(),
                            span,
                        })
                        .collect(),
                    span,
                };

                // Build: "Ctor(" <> show __x0 <> ", " <> show __x1 <> ")"
                // With labels: "Ctor(label: " <> show __x0 <> ", label2: " <> show __x1 <> ")"
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
                    parts.push(Expr::Lit {
                        value: Lit::String(prefix.clone()),
                        span,
                    });
                    prefix.clear();

                    // `show __xi`
                    parts.push(Expr::App {
                        func: Box::new(Expr::Var {
                            name: "show".into(),
                            span,
                        }),
                        arg: Box::new(Expr::Var {
                            name: field_vars[i].clone(),
                            span,
                        }),
                        span,
                    });
                }

                parts.push(Expr::Lit {
                    value: Lit::String(")".into()),
                    span,
                });

                let body = parts
                    .into_iter()
                    .reduce(|acc, part| Expr::BinOp {
                        op: BinOp::Concat,
                        left: Box::new(acc),
                        right: Box::new(part),
                        span,
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
    let body = Expr::Case {
        scrutinee: Box::new(Expr::Var {
            name: scrutinee_name.clone(),
            span,
        }),
        arms,
        span,
    };

    // Each type param needs Show
    let where_clause: Vec<TraitBound> = type_params
        .iter()
        .map(|tp| TraitBound {
            type_var: tp.clone(),
            traits: vec!["Show".into()],
        })
        .collect();

    Decl::ImplDef {
        trait_name: "Show".into(),
        target_type: type_name.into(),
        type_params: type_params.to_vec(),
        where_clause,
        needs: vec![],
        methods: vec![(
            "show".into(),
            vec![Pat::Var {
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
                name: ctor.clone(),
                args: a_vars.iter().map(|v| Pat::Var { name: v.clone(), span }).collect(),
                span,
            };
            let pat_b = Pat::Constructor {
                name: ctor.clone(),
                args: b_vars.iter().map(|v| Pat::Var { name: v.clone(), span }).collect(),
                span,
            };
            let pattern = Pat::Tuple {
                elements: vec![pat_a, pat_b],
                span,
            };

            let body = if arity == 0 {
                // Same nullary constructor: always Eq
                Expr::Constructor { name: "Eq".into(), span }
            } else {
                // Compare fields left-to-right, short-circuit on non-Eq
                build_field_compare(&a_vars, &b_vars, span)
            };

            CaseArm { pattern, guard: None, body, span }
        })
        .collect();

    // Wildcard arm for different constructors: compare by index.
    // Use a distinct span so the elaborator's evidence lookup resolves
    // the inner `compare` call to Int's Ord, not the outer type's Ord.
    if variants.len() > 1 {
        let inner_span = Span { start: span.start + 1, end: span.end + 1 };
        let index_case = |var: &str| -> Expr {
            Expr::Case {
                scrutinee: Box::new(Expr::Var { name: var.into(), span }),
                arms: variants
                    .iter()
                    .enumerate()
                    .map(|(i, v)| {
                        let wildcards: Vec<Pat> =
                            (0..v.fields.len()).map(|_| Pat::Wildcard { span }).collect();
                        CaseArm {
                            pattern: Pat::Constructor {
                                name: v.name.clone(),
                                args: wildcards,
                                span,
                            },
                            guard: None,
                            body: Expr::Lit { value: Lit::Int(i as i64), span },
                            span,
                        }
                    })
                    .collect(),
                span,
            }
        };

        // compare (case __x { ... -> 0, ... -> 1 }) (case __y { ... })
        let compare_indices = Expr::App {
            func: Box::new(Expr::App {
                func: Box::new(Expr::Var { name: "compare".into(), span: inner_span }),
                arg: Box::new(index_case(&x)),
                span: inner_span,
            }),
            arg: Box::new(index_case(&y)),
            span: inner_span,
        };

        arms.push(CaseArm {
            pattern: Pat::Wildcard { span },
            guard: None,
            body: compare_indices,
            span,
        });
    }

    let body = Expr::Case {
        scrutinee: Box::new(Expr::Tuple {
            elements: vec![
                Expr::Var { name: x.clone(), span },
                Expr::Var { name: y.clone(), span },
            ],
            span,
        }),
        arms,
        span,
    };

    // Ord requires Eq, and both need to be propagated to type params
    let where_clause: Vec<TraitBound> = type_params
        .iter()
        .map(|tp| TraitBound {
            type_var: tp.clone(),
            traits: vec!["Ord".into(), "Eq".into()],
        })
        .collect();

    Decl::ImplDef {
        trait_name: "Ord".into(),
        target_type: type_name.into(),
        type_params: type_params.to_vec(),
        where_clause,
        needs: vec![],
        methods: vec![(
            "compare".into(),
            vec![
                Pat::Var { name: x, span },
                Pat::Var { name: y, span },
            ],
            body,
        )],
        span,
    }
}

/// Build a left-to-right field comparison chain:
/// `case compare a0 b0 { Eq -> case compare a1 b1 { Eq -> ... Eq; o -> o }; o -> o }`
fn build_field_compare(a_vars: &[String], b_vars: &[String], span: Span) -> Expr {
    assert!(!a_vars.is_empty());
    // Use a distinct span so elaborator evidence doesn't collide with the outer type's Ord
    let inner_span = Span { start: span.start + 2, end: span.end + 2 };

    // Start from the last field and build inward
    let mut result = Expr::Constructor { name: "Eq".into(), span };

    for i in (0..a_vars.len()).rev() {
        let cmp_call = Expr::App {
            func: Box::new(Expr::App {
                func: Box::new(Expr::Var { name: "compare".into(), span: inner_span }),
                arg: Box::new(Expr::Var { name: a_vars[i].clone(), span: inner_span }),
                span: inner_span,
            }),
            arg: Box::new(Expr::Var { name: b_vars[i].clone(), span: inner_span }),
            span: inner_span,
        };

        if i == a_vars.len() - 1 && a_vars.len() == 1 {
            // Single field: just return the compare result directly
            result = cmp_call;
        } else {
            // Wrap in: case compare ai bi { Eq -> <inner>; __other -> __other }
            let other_var = format!("__ord{i}");
            result = Expr::Case {
                scrutinee: Box::new(cmp_call),
                arms: vec![
                    CaseArm {
                        pattern: Pat::Constructor {
                            name: "Eq".into(),
                            args: vec![],
                            span,
                        },
                        guard: None,
                        body: result,
                        span,
                    },
                    CaseArm {
                        pattern: Pat::Var { name: other_var.clone(), span },
                        guard: None,
                        body: Expr::Var { name: other_var, span },
                        span,
                    },
                ],
                span,
            };
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
            traits: vec![trait_name.into()],
        })
        .collect();

    Decl::ImplDef {
        trait_name: trait_name.into(),
        target_type: type_name.into(),
        type_params: type_params.to_vec(),
        where_clause,
        needs: vec![],
        methods: vec![],
        span,
    }
}
