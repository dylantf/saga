use super::*;
use crate::ast::*;
use crate::token::Span;
use crate::typechecker::{Diagnostic, Severity};
use std::collections::HashMap;

pub(crate) fn derive_applied_functional_bridge(
    spec: &DeriveSpec,
    type_name: &str,
    type_params: &[TypeParam],
    span: Span,
    scope: &DeriveScope<'_>,
) -> Result<Vec<Decl>, Diagnostic> {
    let trait_entry = match scope.trait_entry(&spec.trait_name) {
        Ok(Some(entry)) => entry,
        Ok(None) => {
            return Err(Diagnostic {
                severity: Severity::Error,
                message: format!("cannot derive `{}`: trait is not in scope", spec.trait_name),
                span: Some(spec.span),
            });
        }
        Err(reason) => {
            return Err(Diagnostic {
                severity: Severity::Error,
                message: format!("cannot derive `{}`: {reason}", spec.trait_name),
                span: Some(spec.span),
            });
        }
    };
    let trait_info = &trait_entry.info;
    let trait_syntax = trait_entry.canonical.clone();
    let trait_display = spec
        .trait_name
        .rsplit('.')
        .next()
        .unwrap_or(&spec.trait_name);

    if spec.type_args.len() != 1 {
        return Err(Diagnostic {
            severity: Severity::Error,
            message: format!(
                "cannot derive `{trait_display}` with {} type arguments; applied derives support exactly one row type",
                spec.type_args.len()
            ),
            span: Some(spec.span),
        });
    }
    let row_type = &spec.type_args[0];
    if !is_supported_applied_row_type(row_type) {
        return Err(Diagnostic {
            severity: Severity::Error,
            message: format!(
                "cannot derive `{trait_display}`: row argument must be a named type or named type application"
            ),
            span: Some(row_type.span()),
        });
    }
    let row_type = canonicalize_applied_row_type(row_type, scope);
    ensure_row_generic_available(trait_display, &row_type, spec.span, scope)?;
    // A parameterized record (e.g. `Users source meta`) may only be `Selectable`
    // at a specific scope: each column field's impl pins which scope makes its
    // selected type equal the requested row's field. Resolve those bindings so
    // the generated impls target `Users source Required` rather than leaving the
    // scope polymorphic (which can't be proven for every scope).
    let scope_bindings =
        determine_scope_specialization(trait_display, type_name, type_params, &row_type, scope);
    let specialized_params: Vec<TypeParam> = type_params
        .iter()
        .filter(|tp| !scope_bindings.contains_key(&tp.name))
        .cloned()
        .collect();
    if trait_info.type_params.len() != 2 || !trait_info.is_functional {
        return Err(Diagnostic {
            severity: Severity::Error,
            message: format!(
                "cannot derive `{trait_display}` with a row argument: trait must be a functional two-parameter trait"
            ),
            span: Some(spec.span),
        });
    }

    let self_var = &trait_info.type_params[0].name;
    let row_var = &trait_info.type_params[1].name;
    let mut methods = Vec::new();
    for method in &trait_info.methods {
        if method.default_body.is_some() {
            continue;
        }
        let return_shape = match classify_applied_bridge_return(&method.return_type, row_var, scope)
        {
            Ok(shape) if is_applied_bridge_method(method, self_var) => shape,
            Ok(_) | Err(_) => {
                return Err(Diagnostic {
                    severity: Severity::Error,
                    message: format!(
                        "cannot derive `{trait_display}` for `{type_name}`: method `{}` must have shape `{self_var} -> {row_var}` or `{self_var} -> Wrapper {row_var}` with no effects",
                        method.name
                    ),
                    span: Some(method.span),
                });
            }
        };
        methods.push((method.clone(), return_shape));
    }
    if methods.is_empty() {
        return Err(Diagnostic {
            severity: Severity::Error,
            message: format!(
                "cannot derive `{trait_display}` for `{type_name}`: every method has a default body, so there is nothing to synthesize"
            ),
            span: Some(spec.span),
        });
    }

    let zero_span = Span { start: 0, end: 0 };
    let source_rep_name = format!("Rep__{type_name}");
    let row_rep_type = rep_type_for_named_type(&row_type).expect("validated row type");
    let row_rep_ctor = row_type
        .head_name()
        .map(rep_name_for_type_head)
        .expect("validated row type");

    let routed_info = RoutedDeriveInfo {
        trait_name: trait_display.to_string(),
        target_type: type_name.to_string(),
        deriving_span: spec.span,
    };

    let bridge_methods = methods
        .iter()
        .map(|(method, return_shape)| {
            Annotated::bare(synth_applied_bridge_method(
                method,
                return_shape,
                &source_rep_name,
                &row_rep_ctor,
                span,
            ))
        })
        .collect();
    // When the record's scope is pinned, target the specialized rep
    // (`Rep__Users source Required`) so the bridge body's column constraints
    // resolve against a concrete scope.
    let bridge_target_expr = (!scope_bindings.is_empty())
        .then(|| apply_type_params_specialized(&source_rep_name, type_params, &scope_bindings));
    let bridge_impl = Decl::ImplDef {
        id: NodeId::fresh(),
        doc: vec![],
        trait_name: trait_syntax.clone(),
        trait_name_span: zero_span,
        trait_type_args: vec![row_rep_type.clone()],
        target_type: source_rep_name,
        target_type_span: zero_span,
        target_type_expr: bridge_target_expr,
        type_params: specialized_params.clone(),
        where_clause: vec![],
        where_apps: vec![],
        needs: vec![],
        methods: bridge_methods,
        routed_derive_info: Some(routed_info.clone()),
        span,
        dangling_trivia: vec![],
    };

    let source_rep_var = "__selection_rep".to_string();
    let row_rep_var = "__row_rep".to_string();
    let source_applied = apply_type_params_specialized(type_name, type_params, &scope_bindings);
    let where_apps = vec![
        TraitApp {
            id: NodeId::fresh(),
            trait_name: "Std.Generic.Generic".into(),
            type_args: vec![
                source_applied,
                TypeExpr::Var {
                    id: NodeId::fresh(),
                    name: source_rep_var.clone(),
                    span: zero_span,
                },
            ],
            span: zero_span,
        },
        TraitApp {
            id: NodeId::fresh(),
            trait_name: "Std.Generic.Generic".into(),
            type_args: vec![
                row_type.clone(),
                TypeExpr::Var {
                    id: NodeId::fresh(),
                    name: row_rep_var.clone(),
                    span: zero_span,
                },
            ],
            span: zero_span,
        },
        TraitApp {
            id: NodeId::fresh(),
            trait_name: trait_syntax.clone(),
            type_args: vec![
                TypeExpr::Var {
                    id: NodeId::fresh(),
                    name: source_rep_var,
                    span: zero_span,
                },
                TypeExpr::Var {
                    id: NodeId::fresh(),
                    name: row_rep_var,
                    span: zero_span,
                },
            ],
            span: zero_span,
        },
    ];
    let delegating_methods = methods
        .iter()
        .map(|(method, return_shape)| {
            Annotated::bare(synth_applied_delegating_method(method, return_shape, span))
        })
        .collect();
    let delegating_target_expr = (!scope_bindings.is_empty())
        .then(|| apply_type_params_specialized(type_name, type_params, &scope_bindings));
    let delegating_impl = Decl::ImplDef {
        id: NodeId::fresh(),
        doc: vec![],
        trait_name: trait_syntax,
        trait_name_span: zero_span,
        trait_type_args: vec![row_type.clone()],
        target_type: type_name.into(),
        target_type_span: zero_span,
        target_type_expr: delegating_target_expr,
        type_params: specialized_params,
        where_clause: vec![],
        where_apps,
        needs: vec![],
        methods: delegating_methods,
        routed_derive_info: Some(routed_info),
        span,
        dangling_trivia: vec![],
    };

    Ok(vec![bridge_impl, delegating_impl])
}

/// A record-synthesizing derive: `deriving (Trait NewName)` on a carrier record,
/// where `Trait` carries a `synthesizes via <Map> deriving (...)` clause. Unlike
/// the applied functional bridge above, the argument names a type that does
/// **not** exist yet — this derive *synthesizes* it. Nothing here is specific to
/// any library: the field transform, the encoder to attach, and the link trait
/// all come from the trait's declared metadata and the map trait's impls.
///
/// Given a carrier like
///
/// ```text
/// record Users {
///   id: Generated Int,
///   name: Col String,
///   age: Col Int,
/// } deriving (Insertable UsersInsert)
/// ```
///
/// where the library declares
///
/// ```text
/// trait InsertField col ins | col -> ins
/// impl InsertField a            for (Col a)        {}
/// impl InsertField (Writable a) for (Generated a)  {}
/// trait Insertable cols ins | cols -> ins
///   synthesizes via InsertField deriving (InsertRow)
/// ```
///
/// it emits, spliced after the carrier:
///
/// 1. A synthetic `record UsersInsert { id: Writable Int, name: String, age: Int }`
///    — each field type is rewritten by matching it against the `via` map trait's
///    impls (`Col a -> a`, `Generated a -> Writable a`), preserving field names
///    and order, inheriting the carrier's visibility.
/// 2. That record's `Generic`/`Rep__` (via `derive_record_generic`).
/// 3. The `synthesizes … deriving (…)` derives (e.g. `InsertRow`) routed onto the
///    new record, so it folds through the library's encoder — the user can't
///    attach those derives to a type they never see, so the derive does it.
/// 4. A method-less functional-dependency link `impl Insertable UsersInsert for
///    Users`, so a caller constrained `where {cols: Insertable ins}` recovers the
///    synthesized type from the carrier alone (`cols -> ins`).
///
/// Carrier vs. synthesized roles are read from the trait's functional dependency
/// (determinant = carrier, determined = synthesized).
#[allow(clippy::too_many_arguments)]
pub(crate) fn derive_synthesize(
    spec: &DeriveSpec,
    carrier_name: &str,
    carrier_params: &[TypeParam],
    carrier_fields: &[Annotated<(String, TypeExpr)>],
    public: bool,
    span: Span,
    trait_info: &RoutedTraitInfo,
    trait_syntax: &str,
    scope: &DeriveScope<'_>,
) -> Result<Vec<Decl>, Diagnostic> {
    let zero_span = Span { start: 0, end: 0 };
    let trait_display = spec.bare_name();
    let synth = trait_info
        .synthesis
        .as_ref()
        .expect("derive_synthesize called only when synthesis metadata is present");

    // Roles come from the functional dependency: determinant = carrier (the
    // record the derive sits on), determined = the synthesized type.
    let Some(fundep) = &trait_info.fundep else {
        return Err(Diagnostic {
            severity: Severity::Error,
            message: format!(
                "cannot derive `{trait_display}`: a record-synthesizing trait must declare a \
                 functional dependency (`carrier synthesized | carrier -> synthesized`)"
            ),
            span: Some(spec.span),
        });
    };
    if trait_info.type_params.len() != 2 {
        return Err(Diagnostic {
            severity: Severity::Error,
            message: format!(
                "cannot derive `{trait_display}`: record synthesis requires a two-parameter trait"
            ),
            span: Some(spec.span),
        });
    }
    let carrier_param = &trait_info.type_params[0].name;
    let synth_param = &trait_info.type_params[1].name;
    if !fundep.determinant.contains(carrier_param) || !fundep.determined.contains(synth_param) {
        return Err(Diagnostic {
            severity: Severity::Error,
            message: format!(
                "cannot derive `{trait_display}`: the functional dependency must determine the \
                 second parameter from the first (`{carrier_param} -> {synth_param}`)"
            ),
            span: Some(spec.span),
        });
    }

    // The single argument names the record to create; it must be a bare name.
    if spec.type_args.len() != 1 {
        return Err(Diagnostic {
            severity: Severity::Error,
            message: format!(
                "cannot derive `{trait_display}`: expected exactly one type argument naming the \
                 record to synthesize"
            ),
            span: Some(spec.span),
        });
    }
    let new_name = match &spec.type_args[0] {
        TypeExpr::Named { name, .. } => name.rsplit('.').next().unwrap_or(name).to_string(),
        other => {
            return Err(Diagnostic {
                severity: Severity::Error,
                message: format!(
                    "cannot derive `{trait_display}`: the argument must be a bare type name to \
                     generate, not a compound type"
                ),
                span: Some(other.span()),
            });
        }
    };

    // A parameterized carrier needs scope specialization the syntactic field map
    // below cannot express; reject it rather than miscompile.
    if !carrier_params.is_empty() {
        return Err(Diagnostic {
            severity: Severity::Error,
            message: format!(
                "cannot derive `{trait_display}` for parameterized record `{carrier_name}`: record \
                 synthesis currently supports non-parameterized carriers"
            ),
            span: Some(spec.span),
        });
    }

    // Map each carrier field through the `via` trait's impls (read syntactically).
    let via_bare = synth
        .via_trait
        .rsplit('.')
        .next()
        .unwrap_or(&synth.via_trait);
    let mut new_fields: Vec<Annotated<(String, TypeExpr)>> =
        Vec::with_capacity(carrier_fields.len());
    for field in carrier_fields {
        let (fname, fty) = &field.node;
        let mapped = map_field_via_trait(fty, via_bare, scope).map_err(|reason| Diagnostic {
            severity: Severity::Error,
            message: format!(
                "cannot synthesize `{new_name}` for `{carrier_name}`: field `{fname}` {reason}"
            ),
            span: Some(fty.span()),
        })?;
        new_fields.push(Annotated::bare((fname.clone(), mapped)));
    }

    // 1. The synthesized record.
    let record_def = Decl::RecordDef {
        id: NodeId::fresh(),
        doc: vec![],
        public,
        name: new_name.clone(),
        name_span: zero_span,
        type_params: vec![],
        fields: new_fields.clone(),
        deriving: vec![],
        multiline: true,
        dangling_trivia: vec![],
        span,
    };
    let mut decls = vec![record_def];

    // 2. Its Generic / Rep__.
    match derive_record_generic(public, &new_name, &[], &new_fields, span) {
        Ok(generic_decls) => decls.extend(generic_decls),
        Err(Some(diag)) => return Err(diag),
        Err(None) => {
            return Err(Diagnostic {
                severity: Severity::Error,
                message: format!(
                    "cannot derive `{trait_display}` for `{carrier_name}`: failed to derive \
                     `Generic` for the generated record `{new_name}`"
                ),
                span: Some(spec.span),
            });
        }
    }

    // 3. The `synthesizes … deriving (…)` derives, routed onto the new record the
    // same way `deriving (…)` on a hand-written record would. Must follow Generic.
    for d in &synth.attach_derives {
        let bare = d.bare_name();
        if bare == "Generic" {
            continue; // already derived above
        }
        if !d.type_args.is_empty() {
            return Err(Diagnostic {
                severity: Severity::Error,
                message: format!(
                    "cannot derive `{trait_display}`: `synthesizes … deriving (…)` entries must be \
                     plain derives; `{}` has type arguments",
                    d.trait_name
                ),
                span: Some(d.span),
            });
        }
        if is_hardcoded_derive(bare) {
            match generate_record_derive(public, &d.trait_name, &new_name, &[], &new_fields, span) {
                Ok(extra) => decls.extend(extra),
                Err(Some(diag)) => return Err(diag),
                Err(None) => {
                    return Err(Diagnostic {
                        severity: Severity::Error,
                        message: format!(
                            "cannot attach `deriving ({})` to synthesized record `{new_name}`",
                            d.trait_name
                        ),
                        span: Some(d.span),
                    });
                }
            }
        } else {
            match derive_routed(&d.trait_name, &new_name, &[], span, scope) {
                Ok(routed) => decls.extend(routed),
                Err(diag) => return Err(diag),
            }
        }
    }

    // 4. The functional-dependency link `impl Trait <synthesized> for <carrier>`.
    // The determinant (carrier) is the impl target; the determined parameter (the
    // synthesized type) is the single extra trait argument. Method-less: the link
    // exists only so `where {carrier: Trait synthesized}` recovers the type.
    let new_type = TypeExpr::Named {
        id: NodeId::fresh(),
        name: new_name,
        span: zero_span,
    };
    let link_impl = Decl::ImplDef {
        id: NodeId::fresh(),
        doc: vec![],
        trait_name: trait_syntax.to_string(),
        trait_name_span: zero_span,
        trait_type_args: vec![new_type],
        target_type: carrier_name.into(),
        target_type_span: zero_span,
        target_type_expr: None,
        type_params: vec![],
        where_clause: vec![],
        where_apps: vec![],
        needs: vec![],
        methods: vec![],
        routed_derive_info: None,
        span,
        dangling_trivia: vec![],
    };
    decls.push(link_impl);

    Ok(decls)
}

/// Rewrite one field type through a field-map trait's impls, read syntactically:
/// find the impl whose target pattern (the `for` type) unifies with the field
/// type and return its substituted row (the other trait argument). E.g. with
/// `impl InsertField (Writable a) for (Generated a)`, `Generated Int` maps to
/// `Writable Int`. Errors if no impl matches or more than one does.
pub(crate) fn map_field_via_trait(
    fty: &TypeExpr,
    via_bare: &str,
    scope: &DeriveScope<'_>,
) -> Result<TypeExpr, String> {
    let field_head = te_head(fty);
    let mut result: Option<TypeExpr> = None;
    for imp in scope.local_impls.iter().chain(scope.imported.impls.iter()) {
        if imp.trait_bare != via_bare {
            continue;
        }
        if field_head.is_some() && te_head(&imp.target) != field_head {
            continue;
        }
        // The field is concrete (non-parameterized carrier), so only the impl's
        // own variables are unification holes; rename them to avoid any collision.
        let target_renamed = te_rename_vars(&imp.target, "i$");
        let row_renamed = te_rename_vars(&imp.row, "i$");
        let mut subst = HashMap::new();
        if !te_unify(fty, &target_renamed, &mut subst) {
            continue;
        }
        if result.is_some() {
            return Err(format!(
                "matches more than one `{via_bare}` impl (overlapping field map)"
            ));
        }
        result = Some(te_apply(&row_renamed, &subst));
    }
    result.ok_or_else(|| {
        format!("has no `{via_bare}` mapping (no impl's `for` type matches its column type)")
    })
}

pub(crate) fn ensure_row_generic_available(
    trait_display: &str,
    row_type: &TypeExpr,
    derive_span: Span,
    scope: &DeriveScope<'_>,
) -> Result<(), Diagnostic> {
    let Some(row_head) = row_type.head_name() else {
        return Ok(());
    };
    let rep_head = rep_name_for_type_head(row_head);
    let has_explicit_rep = matches!(scope.type_entry(&rep_head), Ok(Some(_)))
        || matches!(scope.record_entry(&rep_head), Ok(Some(_)));

    match scope.record_entry(row_head) {
        Ok(Some(entry)) if entry.info.derives_generic || has_explicit_rep => return Ok(()),
        Ok(Some(_)) => {
            return Err(Diagnostic {
                severity: Severity::Error,
                message: format!(
                    "cannot derive `{trait_display}`: row type `{row_head}` must derive `Generic`"
                ),
                span: Some(derive_span),
            });
        }
        Err(reason) => {
            return Err(Diagnostic {
                severity: Severity::Error,
                message: format!("cannot derive `{trait_display}`: {reason}"),
                span: Some(derive_span),
            });
        }
        Ok(None) => {}
    }

    match scope.type_entry(row_head) {
        Ok(Some(entry)) if entry.info.derives_generic || has_explicit_rep => Ok(()),
        Ok(Some(_)) => Err(Diagnostic {
            severity: Severity::Error,
            message: format!(
                "cannot derive `{trait_display}`: row type `{row_head}` must derive `Generic`"
            ),
            span: Some(derive_span),
        }),
        Err(reason) => Err(Diagnostic {
            severity: Severity::Error,
            message: format!("cannot derive `{trait_display}`: {reason}"),
            span: Some(derive_span),
        }),
        Ok(None) => Ok(()),
    }
}

pub(crate) fn canonicalize_applied_row_type(ty: &TypeExpr, scope: &DeriveScope<'_>) -> TypeExpr {
    match ty {
        TypeExpr::Named { id, name, span } => {
            let canonical = scope
                .record_entry(name)
                .ok()
                .flatten()
                .map(|entry| entry.canonical.clone())
                .or_else(|| {
                    scope
                        .type_entry(name)
                        .ok()
                        .flatten()
                        .map(|entry| entry.canonical.clone())
                })
                .unwrap_or_else(|| name.clone());
            TypeExpr::Named {
                id: *id,
                name: canonical,
                span: *span,
            }
        }
        TypeExpr::App {
            id,
            func,
            arg,
            span,
        } => TypeExpr::App {
            id: *id,
            func: Box::new(canonicalize_applied_row_type(func, scope)),
            arg: Box::new(canonicalize_applied_row_type(arg, scope)),
            span: *span,
        },
        other => other.clone(),
    }
}

#[derive(Clone)]
pub(crate) enum AppliedBridgeReturn {
    Bare,
    TransparentUnaryWrapper { ctor_name: String },
    MappedWrapper { map_name: String },
}

pub(crate) enum AppliedRowWrap {
    Constructor(String),
    Function(String),
}

pub(crate) fn classify_applied_bridge_return(
    return_type: &TypeExpr,
    row_var: &str,
    scope: &DeriveScope<'_>,
) -> Result<AppliedBridgeReturn, String> {
    if matches!(return_type, TypeExpr::Var { name, .. } if name == row_var) {
        return Ok(AppliedBridgeReturn::Bare);
    }

    let (head, args) = extract_head_and_args(return_type).ok_or_else(|| {
        "return type must be the row variable or a named unary wrapper applied to the row variable"
            .to_string()
    })?;
    if args.len() != 1 || !matches!(&args[0], TypeExpr::Var { name, .. } if name == row_var) {
        return Err("return type wrapper must be applied directly to the row variable".to_string());
    }
    if let Some(ctor_name) = transparent_unary_wrapper_ctor(&head, scope)? {
        return Ok(AppliedBridgeReturn::TransparentUnaryWrapper { ctor_name });
    }
    Ok(AppliedBridgeReturn::MappedWrapper {
        map_name: map_name_for_wrapper_head(&head),
    })
}

pub(crate) fn transparent_unary_wrapper_ctor(
    head: &str,
    scope: &DeriveScope<'_>,
) -> Result<Option<String>, String> {
    if let Some(entry) = scope.type_entry(head)? {
        if entry.info.opaque || entry.info.type_params.len() != 1 || entry.info.variants.len() != 1
        {
            return Ok(None);
        }
        let variant = &entry.info.variants[0];
        if variant.fields.len() != 1
            || !is_type_param_ref(&variant.fields[0].1, &entry.info.type_params[0].name)
        {
            return Ok(None);
        }
        return Ok(Some(qualify_ctor_like(&entry.canonical, &variant.name)));
    }

    if let Some(entry) = scope.record_entry(head)? {
        if entry.info.type_params.len() != 1
            || entry.info.fields.len() != 1
            || !is_type_param_ref(&entry.info.fields[0].1, &entry.info.type_params[0].name)
        {
            return Ok(None);
        }
        return Ok(Some(entry.canonical.clone()));
    }

    Err(format!("return wrapper `{head}` is not in scope"))
}

pub(crate) fn map_name_for_wrapper_head(head: &str) -> String {
    head.rsplit_once('.')
        .map(|(module, _)| format!("{module}.map"))
        .unwrap_or_else(|| "map".to_string())
}

pub(crate) fn qualify_ctor_like(type_canonical: &str, ctor_name: &str) -> String {
    if ctor_name.contains('.') {
        ctor_name.to_string()
    } else if let Some((module, _)) = type_canonical.rsplit_once('.') {
        format!("{module}.{ctor_name}")
    } else {
        ctor_name.to_string()
    }
}

pub(crate) fn is_applied_bridge_method(method: &TraitMethod, self_var: &str) -> bool {
    method.params.len() == 1
        && method.effects.is_empty()
        && method.effect_row_var.is_empty()
        && matches!(&method.params[0].1, TypeExpr::Var { name, .. } if name == self_var)
}

pub(crate) fn synth_applied_bridge_method(
    method: &TraitMethod,
    return_shape: &AppliedBridgeReturn,
    source_rep_name: &str,
    row_rep_ctor: &str,
    span: Span,
) -> ImplMethod {
    let inner = "__inner".to_string();
    let method_call = app_expr(var_expr(&method.name, span), var_expr(&inner, span), span);
    let body = synth_applied_return_wrap(
        return_shape,
        method_call,
        AppliedRowWrap::Constructor(row_rep_ctor.to_string()),
        span,
    );
    ImplMethod {
        name: method.name.clone(),
        name_span: Span { start: 0, end: 0 },
        params: vec![Pat::Constructor {
            id: NodeId::fresh(),
            name: source_rep_name.to_string(),
            args: vec![Pat::Var {
                id: NodeId::fresh(),
                name: inner,
                span,
            }],
            span,
        }],
        body,
    }
}

pub(crate) fn synth_applied_delegating_method(
    method: &TraitMethod,
    return_shape: &AppliedBridgeReturn,
    span: Span,
) -> ImplMethod {
    let value = "__val".to_string();
    let to_call = app_expr(var_expr("to", span), var_expr(&value, span), span);
    let method_call = app_expr(var_expr(&method.name, span), to_call, span);
    let body = synth_applied_return_wrap(
        return_shape,
        method_call,
        AppliedRowWrap::Function("from".to_string()),
        span,
    );
    ImplMethod {
        name: method.name.clone(),
        name_span: Span { start: 0, end: 0 },
        params: vec![Pat::Var {
            id: NodeId::fresh(),
            name: value,
            span,
        }],
        body,
    }
}

pub(crate) fn synth_applied_return_wrap(
    return_shape: &AppliedBridgeReturn,
    method_call: Expr,
    row_wrap: AppliedRowWrap,
    span: Span,
) -> Expr {
    match return_shape {
        AppliedBridgeReturn::Bare => apply_applied_row_wrap(&row_wrap, method_call, span),
        AppliedBridgeReturn::MappedWrapper { map_name } => app_expr(
            app_expr(value_expr(map_name, span), row_wrap.into_expr(span), span),
            method_call,
            span,
        ),
        AppliedBridgeReturn::TransparentUnaryWrapper { ctor_name } => {
            let out = "__applied_row_out".to_string();
            let wrapped = apply_applied_row_wrap(&row_wrap, var_expr(&out, span), span);
            Expr::synth(
                span,
                ExprKind::Case {
                    scrutinee: Box::new(method_call),
                    arms: vec![Annotated::bare(CaseArm {
                        pattern: Pat::Constructor {
                            id: NodeId::fresh(),
                            name: ctor_name.clone(),
                            args: vec![Pat::Var {
                                id: NodeId::fresh(),
                                name: out,
                                span,
                            }],
                            span,
                        },
                        guard: None,
                        body: apply_ctor(ctor_name, wrapped, span),
                        span,
                    })],
                    dangling_trivia: vec![],
                },
            )
        }
    }
}

pub(crate) fn apply_applied_row_wrap(wrap: &AppliedRowWrap, value: Expr, span: Span) -> Expr {
    match wrap {
        AppliedRowWrap::Constructor(name) => apply_ctor(name, value, span),
        AppliedRowWrap::Function(name) => app_expr(value_expr(name, span), value, span),
    }
}

impl AppliedRowWrap {
    fn into_expr(self, span: Span) -> Expr {
        match self {
            AppliedRowWrap::Constructor(name) => ctor_expr(&name, span),
            AppliedRowWrap::Function(name) => value_expr(&name, span),
        }
    }
}
