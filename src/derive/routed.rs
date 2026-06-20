use super::*;
use crate::ast::*;
use crate::token::Span;
use crate::typechecker::{Diagnostic, Severity};

/// Synthesize the delegating impl for a user-defined derivable trait.
/// Shape (per Phase 2d+2e carry-forward, recommendation b):
///
/// ```text
/// impl <Trait> for <T> [where {a: <Trait>, ...}]
///   where {Generic <T-applied> r, <Trait> r}
/// {
///   <method_name> __val = case to __val { Rep__<T> __inner -> <method_name> __inner }
/// }
/// ```
///
/// The `where_apps` form makes the dependency on `Generic` and the routed
/// trait explicit (better diagnostics at registration). The per-tparam old-form
/// `where_clause` entries are required so the impl-body inference can satisfy
/// `<Trait> a` constraints that bubble up from the Rep__T building-block
/// instances at use time.
pub(crate) fn derive_routed(
    trait_name: &str,
    type_name: &str,
    type_params: &[TypeParam],
    span: Span,
    scope: &DeriveScope<'_>,
) -> Result<Vec<Decl>, Diagnostic> {
    let trait_entry = match scope.trait_entry(trait_name) {
        Ok(Some(entry)) => entry,
        Ok(None) => {
            return Err(Diagnostic {
                severity: Severity::Error,
                message: format!("cannot derive `{trait_name}`: trait is not in scope"),
                span: Some(span),
            });
        }
        Err(reason) => {
            return Err(Diagnostic {
                severity: Severity::Error,
                message: format!("cannot derive `{trait_name}`: {reason}"),
                span: Some(span),
            });
        }
    };
    let trait_info = &trait_entry.info;
    let trait_syntax = trait_entry.canonical.clone();
    let trait_display = trait_name.rsplit('.').next().unwrap_or(trait_name);

    if trait_info.methods.is_empty() {
        return Err(Diagnostic {
            severity: Severity::Error,
            message: format!(
                "cannot derive `{trait_display}` for `{type_name}`: trait `{trait_display}` has no methods to route"
            ),
            span: Some(span),
        });
    }
    let self_var: String = trait_info
        .type_params
        .first()
        .map(|tp| tp.name.clone())
        .unwrap_or_default();

    // Classify each method's direction up-front so any bad method kills the
    // whole derive before we synthesize anything partial. Methods that carry
    // a default body in the trait declaration are skipped here — impl-checking
    // will splice in the cloned default, which lets library authors mark a
    // method as "convenience wrapper over the routed one" without forcing the
    // synthesizer to invent a body for it.
    let mut classified: Vec<(TraitMethod, MethodDirection)> =
        Vec::with_capacity(trait_info.methods.len());
    for method in &trait_info.methods {
        if method.default_body.is_some() {
            continue;
        }
        match classify_method_direction(method, &self_var, scope) {
            Ok(dir) => classified.push((method.clone(), dir)),
            Err(reason) => {
                return Err(Diagnostic {
                    severity: Severity::Error,
                    message: format!("cannot derive `{trait_display}` for `{type_name}`: {reason}"),
                    span: Some(span),
                });
            }
        }
    }
    if classified.is_empty() {
        return Err(Diagnostic {
            severity: Severity::Error,
            message: format!(
                "cannot derive `{trait_display}` for `{type_name}`: every method in trait \
                 `{trait_display}` has a default body, so there is nothing to synthesize"
            ),
            span: Some(span),
        });
    }

    let rep_name = format!("Rep__{type_name}");
    let zero_span = Span { start: 0, end: 0 };

    // Per-tparam old-form bounds: `where {a: <Trait>, ...}`. Required so the
    // bridge impl's body and the delegating impl's body can satisfy the
    // `<Trait> a` constraints that bubble up from the Rep building-block
    // impls (e.g. `Leaf a where {a: <Trait>}`).
    let per_tparam_where: Vec<TraitBound> = type_params
        .iter()
        .map(|tp| TraitBound {
            type_var: tp.name.clone(),
            traits: vec![TraitRef {
                id: NodeId::fresh(),
                name: trait_syntax.clone(),
                type_args: vec![],
                span: zero_span,
            }],
        })
        .collect();

    // Per-method bodies for the bridge impl (target = Rep__T). Each method is
    // synthesized independently; a single impl carries one ImplMethod entry
    // per trait method.
    let mut bridge_methods: Vec<Annotated<ImplMethod>> = Vec::with_capacity(classified.len());
    let mut delegating_methods: Vec<Annotated<ImplMethod>> = Vec::with_capacity(classified.len());
    for (method, dir) in &classified {
        let (bridge_m, deleg_m) = synth_method_pair(method, dir, &rep_name, span);
        bridge_methods.push(Annotated::bare(bridge_m));
        delegating_methods.push(Annotated::bare(deleg_m));
    }

    let routed_info = RoutedDeriveInfo {
        trait_name: trait_display.to_string(),
        target_type: type_name.to_string(),
        deriving_span: span,
    };
    let bridge_impl = Decl::ImplDef {
        id: NodeId::fresh(),
        doc: vec![],
        trait_name: trait_syntax.clone(),
        trait_name_span: zero_span,
        trait_type_args: vec![],
        target_type: rep_name.clone(),
        target_type_span: zero_span,
        target_type_expr: None,
        type_params: type_params.to_vec(),
        where_clause: per_tparam_where.clone(),
        where_apps: vec![],
        needs: vec![],
        methods: bridge_methods,
        routed_derive_info: Some(routed_info.clone()),
        span,
        dangling_trivia: vec![],
    };

    let fresh_r = "__r".to_string();
    let target_applied = apply_type_params(type_name, type_params);
    let where_apps = vec![
        TraitApp {
            id: NodeId::fresh(),
            trait_name: "Std.Generic.Generic".into(),
            type_args: vec![
                target_applied,
                TypeExpr::Var {
                    id: NodeId::fresh(),
                    name: fresh_r.clone(),
                    span: zero_span,
                },
            ],
            span: zero_span,
        },
        TraitApp {
            id: NodeId::fresh(),
            trait_name: trait_syntax.clone(),
            type_args: vec![TypeExpr::Var {
                id: NodeId::fresh(),
                name: fresh_r,
                span: zero_span,
            }],
            span: zero_span,
        },
    ];
    let delegating_impl = Decl::ImplDef {
        id: NodeId::fresh(),
        doc: vec![],
        trait_name: trait_syntax,
        trait_name_span: zero_span,
        trait_type_args: vec![],
        target_type: type_name.into(),
        target_type_span: zero_span,
        target_type_expr: None,
        type_params: type_params.to_vec(),
        where_clause: per_tparam_where,
        where_apps,
        needs: vec![],
        methods: delegating_methods,
        routed_derive_info: Some(routed_info),
        span,
        dangling_trivia: vec![],
    };

    Ok(vec![bridge_impl, delegating_impl])
}


/// Direction of a single routed-derive method. `To` carries a per-parameter
/// flag vector identifying which params are `a`-typed (need `to`/Rep__T
/// wrapping) vs. passthrough. `From` carries a `FromShape` describing the
/// wrapper structurally.
#[derive(Clone)]
pub(crate) enum MethodDirection {
    To { a_params: Vec<Option<SplicePath>> },
    From(FromShape),
}


/// Validate a method's shape for routed deriving and decide which direction it
/// runs. Returns a human-readable reason on failure for use in the surrounding
/// diagnostic.
///
/// To-direction supports any number of parameters: each parameter must either
/// be exactly the trait's self variable (an `a`-param — wrapped via `to` /
/// destructured from `Rep__T`) or contain no occurrence of the self variable
/// at all (a passthrough param). Nested self (e.g. `List a`) is rejected.
pub(crate) fn classify_method_direction(
    method: &TraitMethod,
    self_var: &str,
    scope: &DeriveScope<'_>,
) -> Result<MethodDirection, String> {
    let return_has_self = type_expr_contains_var(&method.return_type, self_var);

    let mut a_params: Vec<Option<SplicePath>> = Vec::with_capacity(method.params.len());
    let mut any_param_has_self = false;
    for (_label, ty) in &method.params {
        let mut visiting = Vec::new();
        match classify_splice_path(ty, self_var, scope, &mut visiting) {
            Ok(path) => {
                if path.is_some() {
                    any_param_has_self = true;
                }
                a_params.push(path);
            }
            Err(reason) => {
                return Err(format!("method `{}` parameter: {}", method.name, reason));
            }
        }
    }

    match (any_param_has_self, return_has_self) {
        (true, false) => Ok(MethodDirection::To { a_params }),
        (false, true) => match classify_from_return(&method.return_type, self_var, scope) {
            Ok(shape) => Ok(MethodDirection::From(shape)),
            Err(reason) => Err(format!("method `{}`: {}", method.name, reason)),
        },
        (true, true) => Err(format!(
            "method `{}` has the self type on both sides; \
             routed deriving cannot infer a direction (consider splitting the trait)",
            method.name
        )),
        (false, false) => Err(format!(
            "method `{}` does not consume or produce a value of the self type",
            method.name
        )),
    }
}


/// Build the bridge-impl ImplMethod and delegating-impl ImplMethod for a
/// single trait method.
pub(crate) fn synth_method_pair(
    method: &TraitMethod,
    dir: &MethodDirection,
    rep_name: &str,
    span: Span,
) -> (ImplMethod, ImplMethod) {
    let zero_span = Span { start: 0, end: 0 };
    let method_name = method.name.clone();
    match dir {
        MethodDirection::To { a_params } => {
            // Bridge:    method (Rep__T i0) (Rep__T i1) p2 = method i0 i1 p2
            // Delegate:  method p0 p1 p2                   = method (to p0) (to p1) p2
            // For each param:
            //   - splice param (path is Some): the bridge destructures `Rep__T`
            //     at every a-leaf (via `build_splice_pattern`) and forwards the
            //     rebuilt product; the delegate binds the whole param and threads
            //     `to` into each a-leaf (via `apply_splice_path`). A bare-`a` param
            //     is the `Leaf` case of both — `(Rep__T __i)` / `to __p`.
            //   - passthrough (path is None): bridge & delegate both bind __p<k>
            //     and forward it unchanged.
            let n = a_params.len();
            let mut bridge_params: Vec<Pat> = Vec::with_capacity(n);
            let mut bridge_args: Vec<Expr> = Vec::with_capacity(n);
            let mut deleg_params: Vec<Pat> = Vec::with_capacity(n);
            let mut deleg_args: Vec<Expr> = Vec::with_capacity(n);
            let to_op = |e: Expr, s: Span| -> Expr {
                Expr::synth(
                    s,
                    ExprKind::App {
                        func: Box::new(Expr::synth(s, ExprKind::Var { name: "to".into() })),
                        arg: Box::new(e),
                    },
                )
            };
            let mut bridge_counter = 0usize;
            for (i, path) in a_params.iter().enumerate() {
                let param_var = format!("__p{i}");
                match path {
                    Some(p) => {
                        let (bpat, barg) =
                            build_splice_pattern(p, rep_name, &mut bridge_counter, span);
                        bridge_params.push(bpat);
                        bridge_args.push(barg);
                        deleg_params.push(Pat::Var {
                            id: NodeId::fresh(),
                            name: param_var.clone(),
                            span,
                        });
                        let arg = Expr::synth(span, ExprKind::Var { name: param_var });
                        deleg_args.push(apply_splice_path(p, arg, &to_op, span));
                    }
                    None => {
                        bridge_params.push(Pat::Var {
                            id: NodeId::fresh(),
                            name: param_var.clone(),
                            span,
                        });
                        bridge_args.push(Expr::synth(
                            span,
                            ExprKind::Var {
                                name: param_var.clone(),
                            },
                        ));
                        deleg_params.push(Pat::Var {
                            id: NodeId::fresh(),
                            name: param_var.clone(),
                            span,
                        });
                        deleg_args.push(Expr::synth(span, ExprKind::Var { name: param_var }));
                    }
                }
            }
            let method_name_for_call = method_name.clone();
            let build_call = |args: Vec<Expr>| -> Expr {
                let mut acc = Expr::synth(
                    span,
                    ExprKind::Var {
                        name: method_name_for_call.clone(),
                    },
                );
                for arg in args {
                    acc = Expr::synth(
                        span,
                        ExprKind::App {
                            func: Box::new(acc),
                            arg: Box::new(arg),
                        },
                    );
                }
                acc
            };
            let bridge = ImplMethod {
                name: method_name.clone(),
                name_span: zero_span,
                params: bridge_params,
                body: build_call(bridge_args),
            };
            let deleg = ImplMethod {
                name: method_name,
                name_span: zero_span,
                params: deleg_params,
                body: build_call(deleg_args),
            };
            (bridge, deleg)
        }
        MethodDirection::From(shape) => {
            // All params are passthrough in from-direction (the a appears only
            // in the return). Bind each as `__p<i>` and forward all of them to
            // the recursive method call inside the case scrutinee.
            let input_vars: Vec<String> = (0..method.params.len())
                .map(|i| format!("__p{i}"))
                .collect();
            let build_params = || -> Vec<Pat> {
                input_vars
                    .iter()
                    .map(|n| Pat::Var {
                        id: NodeId::fresh(),
                        name: n.clone(),
                        span,
                    })
                    .collect()
            };

            let rep_name_owned = rep_name.to_string();
            let bridge_wrap = |inner: Expr, s: Span| apply_ctor(&rep_name_owned, inner, s);
            let bridge_body = build_from_body(&method_name, &input_vars, &bridge_wrap, shape, span);
            let bridge = ImplMethod {
                name: method_name.clone(),
                name_span: zero_span,
                params: build_params(),
                body: bridge_body,
            };

            let deleg_wrap = |inner: Expr, s: Span| {
                Expr::synth(
                    s,
                    ExprKind::App {
                        func: Box::new(Expr::synth(
                            s,
                            ExprKind::Var {
                                name: "from".into(),
                            },
                        )),
                        arg: Box::new(inner),
                    },
                )
            };
            let deleg_body = build_from_body(&method_name, &input_vars, &deleg_wrap, shape, span);
            let deleg = ImplMethod {
                name: method_name,
                name_span: zero_span,
                params: build_params(),
                body: deleg_body,
            };
            (bridge, deleg)
        }
    }
}


/// Structural description of a from-direction method's return wrapper. The
/// general shape is: either bare `a`, or a sum/record wrapper where every
/// `a` position has been located by walking the wrapper's variants/fields
/// against the trait's self type variable. Per-variant a-position bits drive
/// codegen — `build_from_body` reads this and threads `wrap` through each
/// marked position while passing other positions through unchanged.
#[derive(Clone)]
pub(crate) enum FromShape {
    Bare,
    Sum {
        variants: Vec<VariantShape>,
    },
    Record {
        wrapper_name: String,
        fields: Vec<FieldShape>,
    },
}


#[derive(Clone)]
pub(crate) struct VariantShape {
    ctor_name: String,
    /// One entry per field; `None` = no `a` (passthrough), `Some(path)` =
    /// the field's type carries `a` at the leaves the path locates; apply
    /// `wrap` there (under wrapper-self-param substitution).
    field_a_positions: Vec<Option<SplicePath>>,
}


#[derive(Clone)]
pub(crate) struct FieldShape {
    label: String,
    /// `None` = passthrough, `Some(path)` = splice `a` at the path's leaves.
    path: Option<SplicePath>,
}


/// A lens locating every occurrence of the trait's self type `a` inside a
/// (possibly nested) product type, so codegen can splice the `Generic` iso
/// (`to`/`from`/`Rep__T`) at each `a`-leaf rather than around the whole value.
///
/// `Leaf` is the base case (the value *is* `a`); `Tuple`/`Record` recurse into
/// product positions. `a` nested under a sum or a parametric/recursive
/// container (`List a`, custom sums, self-referential records) is *not*
/// representable here — `classify_splice_path` rejects those with a diagnostic.
#[derive(Clone)]
pub(crate) enum SplicePath {
    /// The value at this position is exactly `a`.
    Leaf,
    /// `(T0, T1, ...)` — per-element path (`None` = element has no `a`).
    Tuple(Vec<Option<SplicePath>>),
    /// A named record `Name { f0: .., f1: .. }` — per-field path.
    Record {
        name: String,
        fields: Vec<(String, Option<SplicePath>)>,
    },
}


/// Classify a from-direction method's return type by structural inspection.
/// Walks the trait method's return TypeExpr to find the wrapper head and its
/// type args, looks the wrapper up in the merged local+imported decl tables,
/// then walks the wrapper's variants/fields to mark which positions carry the
/// trait's self type variable. Returns `Err(reason)` for the various cases
/// the synthesizer can't handle: opaque wrapper, no `a`-position anywhere,
/// or nested `a` (e.g. `Yep (List a)` — would require recursing through the
/// `List` Generic representation, deferred).
pub(crate) fn classify_from_return(
    te: &TypeExpr,
    self_var: &str,
    scope: &DeriveScope<'_>,
) -> Result<FromShape, String> {
    // Bare `a`: the trait's self type variable as the entire return.
    if let TypeExpr::Var { name, .. } = te
        && name == self_var
    {
        return Ok(FromShape::Bare);
    }

    // Otherwise expect a (possibly multi-arg) type application headed by a
    // Named wrapper. Extract head name and the left-to-right args.
    let (head, args) = extract_head_and_args(te).ok_or_else(|| {
        "return type must be either the trait's self variable or a named wrapper applied \
             to type arguments"
            .to_string()
    })?;

    // The wrapper's call-site args may now nest `a` inside a product (e.g.
    // `Result (a, Int) String`). The per-field substitution in
    // `classify_sum_wrapper`/`classify_record_wrapper` feeds each such arg
    // through `classify_splice_path`, which rejects non-product nesting
    // (`Result (List a) String`) with a diagnostic. So no up-front arg check
    // is needed here.

    // Look up the wrapper. Sum (TypeDef) first, then record (RecordDef).
    match scope.type_entry(&head) {
        Ok(Some(td)) => {
            return classify_sum_wrapper(&head, &td.info, &args, self_var, scope);
        }
        Ok(None) => {}
        Err(reason) => return Err(reason),
    }
    match scope.record_entry(&head) {
        Ok(Some(rd)) => {
            return classify_record_wrapper(&head, &rd.info, &args, self_var, scope);
        }
        Ok(None) => {}
        Err(reason) => return Err(reason),
    }
    Err(format!(
        "wrapper type `{}` is not defined in the current module or any imported module; \
         routed from-derives need the wrapper's TypeDef in scope so they can inspect its \
         variants",
        head
    ))
}


/// Walk a sum wrapper's declared variants and identify a-positions. The
/// wrapper's local type params that bind to the trait's self at the call
/// site form `wrapper_self_params`; any variant field whose TypeExpr is
/// exactly `Var(p)` for some `p` in that set is an a-position. A field that
/// CONTAINS such a `p` but isn't directly that `Var` (e.g. `List a`,
/// `Foo a Int`) is the nested-a case and we reject.
pub(crate) fn classify_sum_wrapper(
    name: &str,
    td: &WrapperTypeInfo,
    call_args: &[TypeExpr],
    self_var: &str,
    scope: &DeriveScope<'_>,
) -> Result<FromShape, String> {
    if call_args.len() != td.type_params.len() {
        return Err(format!(
            "wrapper `{}` declares {} type parameter(s) but is applied to {}",
            name,
            td.type_params.len(),
            call_args.len()
        ));
    }
    if !call_args
        .iter()
        .any(|a| type_expr_contains_var(a, self_var))
    {
        return Err(format!(
            "wrapper `{}` doesn't carry the trait's self type at any type-argument position",
            name
        ));
    }
    let subst = param_subst(&td.type_params, call_args);

    let mut variants = Vec::with_capacity(td.variants.len());
    let mut any_a_position = false;
    let ctor_prefix = name.rsplit_once('.').map(|(module, _)| module.to_string());
    for variant in &td.variants {
        let mut field_a_positions = Vec::with_capacity(variant.fields.len());
        for (_label, fty) in &variant.fields {
            let resolved = subst_type_params(fty, &subst);
            let mut visiting = Vec::new();
            let path = classify_splice_path(&resolved, self_var, scope, &mut visiting).map_err(
                |reason| format!("wrapper `{}` variant `{}`: {}", name, variant.name, reason),
            )?;
            if path.is_some() {
                any_a_position = true;
            }
            field_a_positions.push(path);
        }
        variants.push(VariantShape {
            ctor_name: ctor_prefix
                .as_ref()
                .map(|prefix| format!("{prefix}.{}", variant.name))
                .unwrap_or_else(|| variant.name.clone()),
            field_a_positions,
        });
    }
    if !any_a_position {
        return Err(format!(
            "wrapper `{}` has no variant field carrying the trait's self type — nothing for \
             `from` to thread through",
            name
        ));
    }
    Ok(FromShape::Sum { variants })
}


pub(crate) fn classify_record_wrapper(
    name: &str,
    rd: &WrapperRecordInfo,
    call_args: &[TypeExpr],
    self_var: &str,
    scope: &DeriveScope<'_>,
) -> Result<FromShape, String> {
    if call_args.len() != rd.type_params.len() {
        return Err(format!(
            "wrapper `{}` declares {} type parameter(s) but is applied to {}",
            name,
            rd.type_params.len(),
            call_args.len()
        ));
    }
    if !call_args
        .iter()
        .any(|a| type_expr_contains_var(a, self_var))
    {
        return Err(format!(
            "wrapper record `{}` doesn't carry the trait's self type at any type-argument \
             position",
            name
        ));
    }
    let subst = param_subst(&rd.type_params, call_args);
    let mut fields = Vec::with_capacity(rd.fields.len());
    let mut any_a_position = false;
    for (label, fty) in &rd.fields {
        let resolved = subst_type_params(fty, &subst);
        let mut visiting = Vec::new();
        let path = classify_splice_path(&resolved, self_var, scope, &mut visiting)
            .map_err(|reason| format!("wrapper record `{}` field `{}`: {}", name, label, reason))?;
        if path.is_some() {
            any_a_position = true;
        }
        fields.push(FieldShape {
            label: label.clone(),
            path,
        });
    }
    if !any_a_position {
        return Err(format!(
            "wrapper record `{}` has no field carrying the trait's self type — nothing for \
             `from` to thread through",
            name
        ));
    }
    Ok(FromShape::Record {
        wrapper_name: name.to_string(),
        fields,
    })
}


/// Locate every occurrence of the trait's self type `a` inside `te` as a
/// `SplicePath`, or return:
/// - `Ok(None)` — `te` doesn't mention `a` (a passthrough position)
/// - `Ok(Some(path))` — `a` sits at the leaves the path locates (products only)
/// - `Err(reason)` — `a` is nested under a non-product (sum / `List a` / arrow /
///   anonymous record) or a recursive type
///
/// `visiting` carries the canonical names of named records currently being
/// expanded, so a self-referential record is rejected rather than looped.
pub(crate) fn classify_splice_path(
    te: &TypeExpr,
    self_var: &str,
    scope: &DeriveScope<'_>,
    visiting: &mut Vec<String>,
) -> Result<Option<SplicePath>, String> {
    // Bare `a`.
    if is_self_var(te, self_var) {
        return Ok(Some(SplicePath::Leaf));
    }
    // No occurrence anywhere — passthrough.
    if !type_expr_contains_var(te, self_var) {
        return Ok(None);
    }

    // `a` occurs nested. Only products (tuples / named records) are spliceable.
    let (head, args) = extract_head_and_args(te).ok_or_else(|| {
        "the trait's self type is nested in a non-leaf position that routed deriving cannot \
         splice through; only `a` inside tuples and records is supported"
            .to_string()
    })?;

    // Tuple `(T0, T1, ...)` — recurse per element.
    if head == "Tuple" {
        let mut elems = Vec::with_capacity(args.len());
        for arg in &args {
            elems.push(classify_splice_path(arg, self_var, scope, visiting)?);
        }
        return Ok(Some(SplicePath::Tuple(elems)));
    }

    // Named record — recurse into its fields, guarding against recursion.
    if let Some(rd) = scope.record_entry(&head)? {
        let canonical = rd.canonical.clone();
        if visiting.contains(&canonical) {
            return Err(format!(
                "the trait's self type is nested in a non-leaf position inside recursive record \
                 `{}`; routed deriving cannot splice through a recursive type",
                head
            ));
        }
        let info = &rd.info;
        if args.len() != info.type_params.len() {
            return Err(format!(
                "record `{}` declares {} type parameter(s) but is applied to {}",
                head,
                info.type_params.len(),
                args.len()
            ));
        }
        let subst = param_subst(&info.type_params, &args);
        visiting.push(canonical);
        let mut fields = Vec::with_capacity(info.fields.len());
        for (label, fty) in &info.fields {
            let resolved = subst_type_params(fty, &subst);
            let sub = classify_splice_path(&resolved, self_var, scope, visiting)?;
            fields.push((label.clone(), sub));
        }
        visiting.pop();
        return Ok(Some(SplicePath::Record {
            name: head.clone(),
            fields,
        }));
    }

    // Sum types, `List a`, arrows, anonymous records: not a product we can
    // structurally rebuild. The phrasing keeps "nested in a non-leaf" so callers
    // (and the existing diagnostics/tests) read consistently.
    Err(format!(
        "the trait's self type is nested in a non-leaf position under `{}`, which is not a \
         product type; routed deriving can only splice through tuples and records",
        head
    ))
}


/// Transform a value expression by applying `leaf_op` (the `Generic` iso —
/// `to`/`from`/`Rep__T`) at every `a`-leaf the path locates. Products are
/// destructured with a single-arm `case` and rebuilt, threading `leaf_op` into
/// marked positions and passing the rest through unchanged.
pub(crate) fn apply_splice_path(
    path: &SplicePath,
    value: Expr,
    leaf_op: &dyn Fn(Expr, Span) -> Expr,
    span: Span,
) -> Expr {
    match path {
        SplicePath::Leaf => leaf_op(value, span),
        SplicePath::Tuple(elems) => {
            let vars: Vec<String> = (0..elems.len()).map(|i| format!("__t{i}")).collect();
            let pat = Pat::Tuple {
                id: NodeId::fresh(),
                elements: vars
                    .iter()
                    .map(|n| Pat::Var {
                        id: NodeId::fresh(),
                        name: n.clone(),
                        span,
                    })
                    .collect(),
                span,
            };
            let rebuilt: Vec<Expr> = elems
                .iter()
                .enumerate()
                .map(|(i, sub)| {
                    let v = Expr::synth(
                        span,
                        ExprKind::Var {
                            name: vars[i].clone(),
                        },
                    );
                    match sub {
                        Some(p) => apply_splice_path(p, v, leaf_op, span),
                        None => v,
                    }
                })
                .collect();
            let body = Expr::synth(span, ExprKind::Tuple { elements: rebuilt });
            single_arm_case(value, pat, body, span)
        }
        SplicePath::Record { name, fields } => {
            let zero_span = Span { start: 0, end: 0 };
            let pat = Pat::Record {
                id: NodeId::fresh(),
                name: name.clone(),
                fields: fields.iter().map(|(l, _)| (l.clone(), None)).collect(),
                rest: false,
                as_name: None,
                span,
            };
            let body_fields: Vec<(String, Span, Expr)> = fields
                .iter()
                .map(|(label, sub)| {
                    let v = Expr::synth(
                        span,
                        ExprKind::Var {
                            name: label.clone(),
                        },
                    );
                    let value = match sub {
                        Some(p) => apply_splice_path(p, v, leaf_op, span),
                        None => v,
                    };
                    (label.clone(), zero_span, value)
                })
                .collect();
            let body = Expr::synth(
                span,
                ExprKind::RecordCreate {
                    name: name.clone(),
                    fields: body_fields,
                },
            );
            single_arm_case(value, pat, body, span)
        }
    }
}


pub(crate) fn single_arm_case(scrutinee: Expr, pattern: Pat, body: Expr, span: Span) -> Expr {
    Expr::synth(
        span,
        ExprKind::Case {
            scrutinee: Box::new(scrutinee),
            arms: vec![Annotated::bare(CaseArm {
                pattern,
                guard: None,
                body,
                span,
            })],
            dangling_trivia: vec![],
        },
    )
}


/// Build a destructuring pattern + matching rebuild expression for the
/// To-direction *bridge*, which unwraps `Rep__T` at each `a`-leaf in the
/// pattern (rather than via an expression). The bridge binds inner structural
/// values at the leaves and passthrough vars elsewhere, then reassembles the
/// product to forward to the recursive method call. `counter` makes every bound
/// variable unique across the whole parameter list.
pub(crate) fn build_splice_pattern(
    path: &SplicePath,
    rep_name: &str,
    counter: &mut usize,
    span: Span,
) -> (Pat, Expr) {
    match path {
        SplicePath::Leaf => {
            let inner = format!("__i{}", *counter);
            *counter += 1;
            let pat = Pat::Constructor {
                id: NodeId::fresh(),
                name: rep_name.to_string(),
                args: vec![Pat::Var {
                    id: NodeId::fresh(),
                    name: inner.clone(),
                    span,
                }],
                span,
            };
            (pat, Expr::synth(span, ExprKind::Var { name: inner }))
        }
        SplicePath::Tuple(elems) => {
            let mut pats = Vec::with_capacity(elems.len());
            let mut exprs = Vec::with_capacity(elems.len());
            for sub in elems {
                let (p, e) = build_splice_pattern_field(sub, rep_name, counter, span);
                pats.push(p);
                exprs.push(e);
            }
            (
                Pat::Tuple {
                    id: NodeId::fresh(),
                    elements: pats,
                    span,
                },
                Expr::synth(span, ExprKind::Tuple { elements: exprs }),
            )
        }
        SplicePath::Record { name, fields } => {
            let zero_span = Span { start: 0, end: 0 };
            let mut pat_fields = Vec::with_capacity(fields.len());
            let mut expr_fields = Vec::with_capacity(fields.len());
            for (label, sub) in fields {
                match sub {
                    Some(p) => {
                        let (pp, ee) = build_splice_pattern(p, rep_name, counter, span);
                        pat_fields.push((label.clone(), Some(pp)));
                        expr_fields.push((label.clone(), zero_span, ee));
                    }
                    None => {
                        pat_fields.push((label.clone(), None));
                        expr_fields.push((
                            label.clone(),
                            zero_span,
                            Expr::synth(
                                span,
                                ExprKind::Var {
                                    name: label.clone(),
                                },
                            ),
                        ));
                    }
                }
            }
            (
                Pat::Record {
                    id: NodeId::fresh(),
                    name: name.clone(),
                    fields: pat_fields,
                    rest: false,
                    as_name: None,
                    span,
                },
                Expr::synth(
                    span,
                    ExprKind::RecordCreate {
                        name: name.clone(),
                        fields: expr_fields,
                    },
                ),
            )
        }
    }
}


/// A single product element/field for the To-bridge: either recurse (it carries
/// `a`) or bind a fresh passthrough var.
pub(crate) fn build_splice_pattern_field(
    sub: &Option<SplicePath>,
    rep_name: &str,
    counter: &mut usize,
    span: Span,
) -> (Pat, Expr) {
    match sub {
        Some(p) => build_splice_pattern(p, rep_name, counter, span),
        None => {
            let v = format!("__p{}", *counter);
            *counter += 1;
            (
                Pat::Var {
                    id: NodeId::fresh(),
                    name: v.clone(),
                    span,
                },
                Expr::synth(span, ExprKind::Var { name: v }),
            )
        }
    }
}


/// Build the body of a from-direction method. The body has the shape
/// `case method input { <reconstruction arms> }` where each arm matches one
/// wrapper variant (or destructures the single record), rebinds its fields,
/// and reconstructs the wrapper applying `wrap` at each a-position.
pub(crate) fn build_from_body(
    method_name: &str,
    input_vars: &[String],
    wrap: &dyn Fn(Expr, Span) -> Expr,
    shape: &FromShape,
    span: Span,
) -> Expr {
    // `method __p0 __p1 ...` — recursive call forwards every input through
    // the dictionary to the next instance in the chain.
    let mut inner_call = Expr::synth(
        span,
        ExprKind::Var {
            name: method_name.into(),
        },
    );
    for iv in input_vars {
        inner_call = Expr::synth(
            span,
            ExprKind::App {
                func: Box::new(inner_call),
                arg: Box::new(Expr::synth(span, ExprKind::Var { name: iv.clone() })),
            },
        );
    }
    match shape {
        FromShape::Bare => wrap(inner_call, span),
        FromShape::Sum { variants, .. } => {
            let arms: Vec<Annotated<CaseArm>> = variants
                .iter()
                .map(|v| Annotated::bare(build_variant_arm(v, wrap, span)))
                .collect();
            Expr::synth(
                span,
                ExprKind::Case {
                    scrutinee: Box::new(inner_call),
                    arms,
                    dangling_trivia: vec![],
                },
            )
        }
        FromShape::Record {
            wrapper_name,
            fields,
        } => {
            let arm = build_record_arm(wrapper_name, fields, wrap, span);
            Expr::synth(
                span,
                ExprKind::Case {
                    scrutinee: Box::new(inner_call),
                    arms: vec![Annotated::bare(arm)],
                    dangling_trivia: vec![],
                },
            )
        }
    }
}


/// One case arm reconstructing a single variant. Zero-field variants
/// destructure-and-reconstruct trivially; multi-field variants bind each
/// field to `__f<i>` and rebuild via positional constructor application,
/// applying `wrap` at marked a-positions.
pub(crate) fn build_variant_arm(v: &VariantShape, wrap: &dyn Fn(Expr, Span) -> Expr, span: Span) -> CaseArm {
    let field_vars: Vec<String> = (0..v.field_a_positions.len())
        .map(|i| format!("__f{i}"))
        .collect();
    let pat = Pat::Constructor {
        id: NodeId::fresh(),
        name: v.ctor_name.clone(),
        args: field_vars
            .iter()
            .map(|n| Pat::Var {
                id: NodeId::fresh(),
                name: n.clone(),
                span,
            })
            .collect(),
        span,
    };
    let mut body = Expr::synth(
        span,
        ExprKind::Constructor {
            name: v.ctor_name.clone(),
        },
    );
    for (i, path) in v.field_a_positions.iter().enumerate() {
        let arg = Expr::synth(
            span,
            ExprKind::Var {
                name: field_vars[i].clone(),
            },
        );
        let arg = match path {
            Some(p) => apply_splice_path(p, arg, wrap, span),
            None => arg,
        };
        body = Expr::synth(
            span,
            ExprKind::App {
                func: Box::new(body),
                arg: Box::new(arg),
            },
        );
    }
    CaseArm {
        pattern: pat,
        guard: None,
        body,
        span,
    }
}


/// One case arm destructuring a record wrapper. Pattern is
/// `Wrap { f1, f2, ... }`, body reconstructs via `Wrap { f1: wrap?(f1), ... }`.
pub(crate) fn build_record_arm(
    wrapper_name: &str,
    fields: &[FieldShape],
    wrap: &dyn Fn(Expr, Span) -> Expr,
    span: Span,
) -> CaseArm {
    let zero_span = Span { start: 0, end: 0 };
    let pat = Pat::Record {
        id: NodeId::fresh(),
        name: wrapper_name.to_string(),
        fields: fields.iter().map(|f| (f.label.clone(), None)).collect(),
        rest: false,
        as_name: None,
        span,
    };
    let body_fields: Vec<(String, Span, Expr)> = fields
        .iter()
        .map(|f| {
            let var_expr = Expr::synth(
                span,
                ExprKind::Var {
                    name: f.label.clone(),
                },
            );
            let value = match &f.path {
                Some(p) => apply_splice_path(p, var_expr, wrap, span),
                None => var_expr,
            };
            (f.label.clone(), zero_span, value)
        })
        .collect();
    let body = Expr::synth(
        span,
        ExprKind::RecordCreate {
            name: wrapper_name.to_string(),
            fields: body_fields,
        },
    );
    CaseArm {
        pattern: pat,
        guard: None,
        body,
        span,
    }
}

