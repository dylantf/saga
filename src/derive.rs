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
        other => panic!("cannot derive `{other}` (only Show and Eq are supported)"),
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
