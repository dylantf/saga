//! Deriving pass: expands `deriving (Show, ...)` clauses on type definitions
//! into synthetic `ImplDef` nodes. Runs before typechecking so the generated
//! impls are validated like any hand-written impl.

use crate::ast::*;
use crate::token::Span;
use crate::token::StringKind;
use crate::typechecker::{Diagnostic, Severity};

/// Expand all `deriving` clauses in a program, appending synthetic `ImplDef`
/// nodes after each `TypeDef` that has them. Returns diagnostics for
/// unsupported derive requests.
pub fn expand_derives(program: &mut Vec<Decl>) -> Vec<Diagnostic> {
    let mut errors = Vec::new();
    // Build a fresh program, splicing each decl's derived siblings in directly
    // after it. Generic-derived `Rep__T` typedefs and their impls must be
    // visible before any later user impl whose where-app form mentions
    // `Generic T r`, otherwise the where-app's coherence lookup fires before
    // the impl is registered.
    let original = std::mem::take(program);
    let mut rebuilt: Vec<Decl> = Vec::with_capacity(original.len());
    for decl in &original {
        let mut extra: Vec<Decl> = Vec::new();
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
                    let bare = trait_name.rsplit('.').next().unwrap_or(trait_name);
                    if bare == "Generic" {
                        match derive_adt_generic(name, type_params, variants, *span) {
                            Ok(decls) => extra.extend(decls),
                            Err(Some(diag)) => errors.push(diag),
                            Err(None) => errors.push(Diagnostic {
                                severity: Severity::Error,
                                message: format!(
                                    "cannot derive `{trait_name}` for type `{name}`"
                                ),
                                span: Some(*span),
                            }),
                        }
                        continue;
                    }
                    match generate_derive(trait_name, name, type_params, variants, *span) {
                        Some(impl_def) => extra.push(impl_def),
                        None => errors.push(Diagnostic {
                            severity: Severity::Error,
                            message: format!("cannot derive `{trait_name}` for type `{name}`"),
                            span: Some(*span),
                        }),
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
                    match generate_record_derive(trait_name, name, type_params, fields, *span) {
                        Ok(decls) => extra.extend(decls),
                        Err(Some(diag)) => errors.push(diag),
                        Err(None) => errors.push(Diagnostic {
                            severity: Severity::Error,
                            message: format!("cannot derive `{trait_name}` for record `{name}`"),
                            span: Some(*span),
                        }),
                    }
                }
            }
            _ => {}
        }
        rebuilt.push(decl.clone());
        rebuilt.extend(extra);
    }
    *program = rebuilt;
    errors
}

/// Returns the decls to splice into the program, or:
///   - `Err(None)` for "unsupported trait, use the default cannot-derive error"
///   - `Err(Some(diag))` for a specific diagnostic
fn generate_record_derive(
    trait_name: &str,
    record_name: &str,
    type_params: &[String],
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
        "Generic" => derive_record_generic(record_name, type_params, fields, span),
        _ => Err(None),
    }
}

/// Build `type __Rep_R = __Rep_R <inner-rep>` + `impl Generic __Rep_R for R { to, from }`.
/// Only handles records with no type parameters (Phase 2b scope).
/// TODO(Phase 2e): handle parameterized records.
fn derive_record_generic(
    record_name: &str,
    type_params: &[String],
    fields: &[Annotated<(String, TypeExpr)>],
    span: Span,
) -> Result<Vec<Decl>, Option<Diagnostic>> {
    if !type_params.is_empty() {
        return Err(Some(Diagnostic {
            severity: Severity::Error,
            message:
                "deriving (Generic) for parameterized records is not yet supported"
                    .to_string(),
            span: Some(span),
        }));
    }

    // Naming: use a leading uppercase letter so the lexer classifies the
    // name as an UpperIdent (type/constructor). The planning doc proposed
    // `__Rep_<R>` but a leading `_` lexes as lowercase, which would break
    // user-written ascriptions like `(to p : __Rep_Person)`.
    let rep_name = format!("Rep__{record_name}");
    let plain_fields: Vec<(String, TypeExpr)> = fields.iter().map(|a| a.node.clone()).collect();

    // 1. Synthetic TypeDef: `type __Rep_R = __Rep_R <inner>`
    let inner_type = build_rep_type_inner(&plain_fields);
    let ctor_field_type = inner_type.clone();
    let rep_typedef = Decl::TypeDef {
        id: NodeId::fresh(),
        doc: vec![],
        public: false,
        opaque: false,
        name: rep_name.clone(),
        name_span: Span { start: 0, end: 0 },
        type_params: vec![],
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
    let to_body = apply_ctor(&rep_name, inner_expr, span);
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
    let field_var_names: Vec<String> = (0..plain_fields.len())
        .map(|i| format!("__f{i}"))
        .collect();
    let inner_pat = build_rep_from_pattern(&field_var_names, span);
    let from_param = Pat::Constructor {
        id: NodeId::fresh(),
        name: rep_name.clone(),
        args: vec![inner_pat],
        span,
    };
    let record_fields: Vec<(String, Span, Expr)> = plain_fields
        .iter()
        .zip(field_var_names.iter())
        .map(|((fname, _), vname)| {
            (
                fname.clone(),
                Span { start: 0, end: 0 },
                Expr::synth(span, ExprKind::Var { name: vname.clone() }),
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
            },
        )
    } else {
        Expr::synth(
            span,
            ExprKind::RecordCreate {
                name: record_name.into(),
                fields: record_fields,
            },
        )
    };
    let from_method = Annotated::bare(ImplMethod {
        name: "from".into(),
        name_span: Span { start: 0, end: 0 },
        params: vec![from_param],
        body: from_body,
    });

    let impl_def = Decl::ImplDef {
        trait_name_span: Span { start: 0, end: 0 },
        target_type_span: Span { start: 0, end: 0 },
        id: NodeId::fresh(),
        doc: vec![],
        trait_name: "Generic".into(),
        trait_type_args: vec![TypeExpr::Named {
            id: NodeId::fresh(),
            name: rep_name.clone(),
            span: Span { start: 0, end: 0 },
        }],
        target_type: record_name.into(),
        type_params: vec![],
        where_clause: vec![],
        where_apps: vec![],
        needs: vec![],
        methods: vec![to_method, from_method],
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
fn derive_adt_generic(
    type_name: &str,
    type_params: &[String],
    variants: &[Annotated<TypeConstructor>],
    span: Span,
) -> Result<Vec<Decl>, Option<Diagnostic>> {
    if !type_params.is_empty() {
        return Err(Some(Diagnostic {
            severity: Severity::Error,
            message: "deriving (Generic) for parameterized types is not yet supported"
                .to_string(),
            span: Some(span),
        }));
    }
    if variants.is_empty() {
        return Err(Some(Diagnostic {
            severity: Severity::Error,
            message: format!("cannot derive (Generic) for `{type_name}`: no variants"),
            span: Some(span),
        }));
    }
    for v in variants {
        for (_, ty) in &v.node.fields {
            if type_expr_refs(ty, type_name) {
                return Err(Some(Diagnostic {
                    severity: Severity::Error,
                    message:
                        "deriving (Generic) for recursive types is not yet supported"
                            .to_string(),
                    span: Some(span),
                }));
            }
        }
    }

    let rep_name = format!("Rep__{type_name}");

    // 1. Inner Rep type = right-leaning Or of `Labeled <variant_shape_type>`.
    let inner_type = build_adt_rep_inner_type(variants);
    let rep_typedef = Decl::TypeDef {
        id: NodeId::fresh(),
        doc: vec![],
        public: false,
        opaque: false,
        name: rep_name.clone(),
        name_span: Span { start: 0, end: 0 },
        type_params: vec![],
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
            let shape_expr =
                build_variant_shape_expr(&v.fields, &field_vars, span);
            let labeled = apply2("Labeled", string_lit(&v.name, span), shape_expr, span);
            let or_wrapped = or_wrap_expr(labeled, i, n, span);
            let body = apply_ctor(&rep_name, or_wrapped, span);
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
            let labeled_pat = Pat::Constructor {
                id: NodeId::fresh(),
                name: "Labeled".into(),
                args: vec![
                    Pat::Wildcard {
                        id: NodeId::fresh(),
                        span,
                    },
                    shape_pat,
                ],
                span,
            };
            let or_wrapped_pat = or_wrap_pat(labeled_pat, i, n, span);
            let outer_pat = Pat::Constructor {
                id: NodeId::fresh(),
                name: rep_name.clone(),
                args: vec![or_wrapped_pat],
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

    let impl_def = Decl::ImplDef {
        trait_name_span: Span { start: 0, end: 0 },
        target_type_span: Span { start: 0, end: 0 },
        id: NodeId::fresh(),
        doc: vec![],
        trait_name: "Generic".into(),
        trait_type_args: vec![TypeExpr::Named {
            id: NodeId::fresh(),
            name: rep_name.clone(),
            span: Span { start: 0, end: 0 },
        }],
        target_type: type_name.into(),
        type_params: vec![],
        where_clause: vec![],
        where_apps: vec![],
        needs: vec![],
        methods: vec![to_method, from_method],
        span,
        dangling_trivia: vec![],
    };

    Ok(vec![rep_typedef, impl_def])
}

/// Direct self-reference detector: scans a TypeExpr for any `Named { name }`
/// matching `target`. Does not chase through other typedefs (indirect cycles
/// fall through and will produce a normal type error at typecheck time).
fn type_expr_refs(ty: &TypeExpr, target: &str) -> bool {
    match ty {
        TypeExpr::Named { name, .. } => name == target,
        TypeExpr::App { func, arg, .. } => {
            type_expr_refs(func, target) || type_expr_refs(arg, target)
        }
        TypeExpr::Arrow { from, to, .. } => {
            type_expr_refs(from, target) || type_expr_refs(to, target)
        }
        TypeExpr::Record { fields, .. } => {
            fields.iter().any(|(_, t)| type_expr_refs(t, target))
        }
        TypeExpr::Labeled { inner, .. } => type_expr_refs(inner, target),
        TypeExpr::Var { .. } => false,
    }
}

/// Build the inner Rep type for an ADT: right-leaning `Or` chain wrapping
/// `Labeled <variant_shape>` for each variant.
fn build_adt_rep_inner_type(variants: &[Annotated<TypeConstructor>]) -> TypeExpr {
    let labeled_shapes: Vec<TypeExpr> = variants
        .iter()
        .map(|v| type_app(type_named("Labeled"), build_variant_shape_type(&v.node.fields)))
        .collect();
    let mut iter = labeled_shapes.into_iter().rev();
    let mut acc = iter.next().unwrap();
    for prev in iter {
        acc = type_app(type_app(type_named("Or"), prev), acc);
    }
    acc
}

/// Variant shape type: U1 for 0 fields, single field rep for 1, right-leaning
/// And chain for >=2.
fn build_variant_shape_type(fields: &[(Option<String>, TypeExpr)]) -> TypeExpr {
    if fields.is_empty() {
        return type_named("U1");
    }
    let n = fields.len();
    let mut acc = field_rep_type_adt(&fields[n - 1].0, &fields[n - 1].1);
    for i in (0..n - 1).rev() {
        acc = type_app(
            type_app(type_named("And"), field_rep_type_adt(&fields[i].0, &fields[i].1)),
            acc,
        );
    }
    acc
}

/// For a single ADT constructor field: `Labeled (Leaf T)` if labeled, else
/// `Leaf T`.
fn field_rep_type_adt(label: &Option<String>, ty: &TypeExpr) -> TypeExpr {
    let leaf = type_app(type_named("Leaf"), ty.clone());
    if label.is_some() {
        type_app(type_named("Labeled"), leaf)
    } else {
        leaf
    }
}

/// Expression form of `build_variant_shape_type`: builds the And/Labeled/Leaf
/// expression tree from already-bound field variables.
fn build_variant_shape_expr(
    fields: &[(Option<String>, TypeExpr)],
    field_vars: &[String],
    span: Span,
) -> Expr {
    if fields.is_empty() {
        return Expr::synth(span, ExprKind::Constructor { name: "U1".into() });
    }
    let leaf_for = |label: &Option<String>, var: &str| -> Expr {
        let leaf = apply_ctor(
            "Leaf",
            Expr::synth(span, ExprKind::Var { name: var.into() }),
            span,
        );
        match label {
            Some(lbl) => apply2("Labeled", string_lit(lbl, span), leaf, span),
            None => leaf,
        }
    };
    let n = fields.len();
    let mut acc = leaf_for(&fields[n - 1].0, &field_vars[n - 1]);
    for i in (0..n - 1).rev() {
        let cur = leaf_for(&fields[i].0, &field_vars[i]);
        acc = apply2("And", cur, acc, span);
    }
    acc
}

/// Pattern form of the variant shape, binding each field to the matching name
/// in `field_vars`.
fn build_variant_shape_pat(
    fields: &[(Option<String>, TypeExpr)],
    field_vars: &[String],
    span: Span,
) -> Pat {
    if fields.is_empty() {
        return Pat::Constructor {
            id: NodeId::fresh(),
            name: "U1".into(),
            args: vec![],
            span,
        };
    }
    let leaf_pat_for = |label: &Option<String>, var: &str| -> Pat {
        let leaf = Pat::Constructor {
            id: NodeId::fresh(),
            name: "Leaf".into(),
            args: vec![Pat::Var {
                id: NodeId::fresh(),
                name: var.into(),
                span,
            }],
            span,
        };
        match label {
            Some(_) => Pat::Constructor {
                id: NodeId::fresh(),
                name: "Labeled".into(),
                args: vec![
                    Pat::Wildcard {
                        id: NodeId::fresh(),
                        span,
                    },
                    leaf,
                ],
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
            name: "And".into(),
            args: vec![cur, acc],
            span,
        };
    }
    acc
}

/// `Or_Right^i (Or_Left inner)` for i < total-1; `Or_Right^(total-1) inner`
/// for the last variant; bare `inner` if there's only one variant.
fn or_wrap_expr(inner: Expr, index: usize, total: usize, span: Span) -> Expr {
    if total == 1 {
        return inner;
    }
    let mut e = if index == total - 1 {
        inner
    } else {
        apply_ctor("Or_Left", inner, span)
    };
    for _ in 0..index {
        e = apply_ctor("Or_Right", e, span);
    }
    e
}

/// Pattern counterpart to `or_wrap_expr`.
fn or_wrap_pat(inner: Pat, index: usize, total: usize, span: Span) -> Pat {
    if total == 1 {
        return inner;
    }
    let mut p = if index == total - 1 {
        inner
    } else {
        Pat::Constructor {
            id: NodeId::fresh(),
            name: "Or_Left".into(),
            args: vec![inner],
            span,
        }
    };
    for _ in 0..index {
        p = Pat::Constructor {
            id: NodeId::fresh(),
            name: "Or_Right".into(),
            args: vec![p],
            span,
        };
    }
    p
}

/// Build a curried application of `ctor` to each `field_var`. For nullary
/// constructors, returns just `Ctor`.
fn build_ctor_application(ctor: &str, field_vars: &[String], span: Span) -> Expr {
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

fn type_named(name: &str) -> TypeExpr {
    TypeExpr::Named {
        id: NodeId::fresh(),
        name: name.into(),
        span: Span { start: 0, end: 0 },
    }
}

fn type_app(func: TypeExpr, arg: TypeExpr) -> TypeExpr {
    TypeExpr::App {
        id: NodeId::fresh(),
        func: Box::new(func),
        arg: Box::new(arg),
        span: Span { start: 0, end: 0 },
    }
}

/// Build the inner Rep type (without the outer newtype wrapping). Right-leaning
/// And chain for >=2 fields; Labeled (Leaf T) for 1 field; U1 for 0.
fn build_rep_type_inner(fields: &[(String, TypeExpr)]) -> TypeExpr {
    if fields.is_empty() {
        return type_named("U1");
    }
    let mut iter = fields.iter().rev();
    let (_, last_ty) = iter.next().unwrap();
    let mut acc = field_rep_type(last_ty);
    for (_, ty) in iter {
        acc = type_app(type_app(type_named("And"), field_rep_type(ty)), acc);
    }
    acc
}

fn field_rep_type(ty: &TypeExpr) -> TypeExpr {
    type_app(type_named("Labeled"), type_app(type_named("Leaf"), ty.clone()))
}

fn apply_ctor(name: &str, arg: Expr, span: Span) -> Expr {
    Expr::synth(
        span,
        ExprKind::App {
            func: Box::new(Expr::synth(
                span,
                ExprKind::Constructor { name: name.into() },
            )),
            arg: Box::new(arg),
        },
    )
}

fn apply2(func: &str, a: Expr, b: Expr, span: Span) -> Expr {
    Expr::synth(
        span,
        ExprKind::App {
            func: Box::new(Expr::synth(
                span,
                ExprKind::App {
                    func: Box::new(Expr::synth(
                        span,
                        ExprKind::Constructor { name: func.into() },
                    )),
                    arg: Box::new(a),
                },
            )),
            arg: Box::new(b),
        },
    )
}

fn string_lit(s: &str, span: Span) -> Expr {
    Expr::synth(
        span,
        ExprKind::Lit {
            value: Lit::String(s.into(), StringKind::Normal),
        },
    )
}

/// Build the `to` body's inner expression (everything inside the __Rep_R newtype wrap).
fn build_rep_to_expr(fields: &[(String, TypeExpr)], record_var: &Expr, span: Span) -> Expr {
    if fields.is_empty() {
        return Expr::synth(span, ExprKind::Constructor { name: "U1".into() });
    }
    let labeled_for = |fname: &str| -> Expr {
        // Labeled "fname" (Leaf record_var.fname)
        let field_access = Expr::synth(
            span,
            ExprKind::FieldAccess {
                expr: Box::new(record_var.clone()),
                field: fname.into(),
                record_name: None,
            },
        );
        let leaf = apply_ctor("Leaf", field_access, span);
        apply2("Labeled", string_lit(fname, span), leaf, span)
    };

    let mut iter = fields.iter().rev();
    let (last_name, _) = iter.next().unwrap();
    let mut acc = labeled_for(last_name);
    for (fname, _) in iter {
        acc = apply2("And", labeled_for(fname), acc, span);
    }
    acc
}

/// Build the inner pattern matched by `from`: matches the And/Labeled/Leaf tree
/// and binds each field's value to the corresponding variable in `field_vars`.
fn build_rep_from_pattern(field_vars: &[String], span: Span) -> Pat {
    if field_vars.is_empty() {
        return Pat::Constructor {
            id: NodeId::fresh(),
            name: "U1".into(),
            args: vec![],
            span,
        };
    }
    let labeled_pat = |var: &str| -> Pat {
        // Labeled _ (Leaf var)
        Pat::Constructor {
            id: NodeId::fresh(),
            name: "Labeled".into(),
            args: vec![
                Pat::Wildcard {
                    id: NodeId::fresh(),
                    span,
                },
                Pat::Constructor {
                    id: NodeId::fresh(),
                    name: "Leaf".into(),
                    args: vec![Pat::Var {
                        id: NodeId::fresh(),
                        name: var.into(),
                        span,
                    }],
                    span,
                },
            ],
            span,
        }
    };

    let mut iter = field_vars.iter().rev();
    let last = iter.next().unwrap();
    let mut acc = labeled_pat(last);
    for v in iter {
        acc = Pat::Constructor {
            id: NodeId::fresh(),
            name: "And".into(),
            args: vec![labeled_pat(v), acc],
            span,
        };
    }
    acc
}

/// Generate `impl Show/Debug for R { show/debug r = "R { field: " <> show/debug r.field <> ... <> "}" }`
fn derive_record_stringify(
    trait_name: &str,
    method_name: &str,
    record_name: &str,
    type_params: &[String],
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
            type_var: tp.clone(),
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
        span,
        dangling_trivia: vec![],
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

fn generate_derive(
    trait_name: &str,
    type_name: &str,
    type_params: &[String],
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
fn derive_stringify(
    trait_name: &str,
    method_name: &str,
    type_name: &str,
    type_params: &[String],
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
            type_var: tp.clone(),
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
        span,
        dangling_trivia: vec![],
    }
}

/// Generate `impl Ord for T { compare x y = ... }` using declaration-order
/// constructor indexing and left-to-right field comparison.
fn derive_ord(
    type_name: &str,
    type_params: &[String],
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
            type_var: tp.clone(),
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
        span,
        dangling_trivia: vec![],
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
        span,
        dangling_trivia: vec![],
    }
}

/// Generate `impl Enum for T { to_enum x = case x { ... }; from_enum n = case n { ... } }`
/// Only valid for types with all nullary constructors.
fn derive_enum(type_name: &str, variants: &[Annotated<TypeConstructor>], span: Span) -> Decl {
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
        span,
        dangling_trivia: vec![],
    }
}
