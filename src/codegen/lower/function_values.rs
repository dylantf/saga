use std::collections::HashMap;

use crate::ast::{self, Expr, ExprKind, Pat};
use crate::codegen::cerl::{CArm, CExpr, CLit, CPat};
use crate::codegen::runtime_shape::{CpsShape, RuntimeFunctionShape};

use super::evidence;
use super::util::{self, collect_ctor_call_with_head};
use super::{EvidenceCtx, Lowerer};

impl<'a> Lowerer<'a> {
    fn direct_lambda_arity(expr: &Expr) -> Option<usize> {
        let ExprKind::Lambda { params, body } = &expr.kind else {
            return None;
        };
        let mut arity = params.len();
        let mut current = body.as_ref();
        while let ExprKind::Lambda {
            params,
            body: nested_body,
        } = &current.kind
        {
            arity += params.len();
            current = nested_body.as_ref();
        }
        Some(arity)
    }

    fn lower_curried_lambda_for_expected_arity(
        &mut self,
        expr: &Expr,
        expected_ty: &crate::typechecker::Type,
    ) -> Option<CExpr> {
        let (expected_arity, effects) = util::arity_and_effects_from_type(expected_ty);
        if expected_arity == 0 || !effects.is_empty() {
            return None;
        }
        let actual_arity = Self::direct_lambda_arity(expr)?;
        if expected_arity >= actual_arity {
            return None;
        }

        let ExprKind::Lambda { params, body } = &expr.kind else {
            return None;
        };
        if params.len() != expected_arity
            || !params.iter().all(|p| {
                matches!(
                    p,
                    Pat::Var { .. }
                        | Pat::Wildcard { .. }
                        | Pat::Lit {
                            value: ast::Lit::Unit,
                            ..
                        }
                )
            })
        {
            return None;
        }

        let param_vars = super::pats::lower_params(params);
        Some(CExpr::Fun(
            param_vars,
            Box::new(self.lower_expr_value(body)),
        ))
    }

    fn lower_constructor_function_value(
        &mut self,
        name: &str,
        expected_ty: &crate::typechecker::Type,
    ) -> Option<CExpr> {
        let mut params = Vec::new();
        let mut current = expected_ty;
        while let crate::typechecker::Type::Fun(_, ret, _) = current {
            params.push(self.fresh());
            current = ret;
        }
        if params.is_empty() {
            return None;
        }

        let bare = name.rsplit('.').next().unwrap_or(name);
        let atom =
            util::mangle_ctor_atom(name, &self.constructor_atoms, self.handler_origin_module());
        let value = if bare == "Cons" && params.len() == 2 {
            CExpr::Cons(
                Box::new(CExpr::Var(params[0].clone())),
                Box::new(CExpr::Var(params[1].clone())),
            )
        } else {
            let mut elems = vec![CExpr::Lit(CLit::Atom(atom))];
            elems.extend(params.iter().map(|param| CExpr::Var(param.clone())));
            CExpr::Tuple(elems)
        };

        Some(
            params
                .into_iter()
                .rev()
                .fold(value, |body, param| CExpr::Fun(vec![param], Box::new(body))),
        )
    }

    pub(super) fn cps_function_shape_from_type(
        &self,
        ty: &crate::typechecker::Type,
    ) -> Option<CpsShape> {
        RuntimeFunctionShape::from_type(ty, |effects| self.canonicalize_effects(effects))
            .cps_shape()
    }

    pub(super) fn expr_cps_function_shape(&self, expr: &Expr) -> Option<CpsShape> {
        self.check_result
            .resolved_type_for_node(expr.id)
            .and_then(|ty| self.cps_function_shape_from_type(&ty))
    }

    /// If `expr` is a partial application of a CPS-shaped function (effects
    /// or open row), returns the resulting closure's runtime CPS shape.
    /// Used to bridge the gap between a value's static type — which may
    /// have been narrowed to pure via row-variable substitution at the
    /// application site — and its actual runtime convention, which is
    /// fixed by the head function's compiled signature.
    ///
    /// Example: `wrap : (Unit -> Unit needs {..e}) -> Unit -> Unit needs {..e}`.
    /// Applying `wrap pure_fn` resolves `..e` to closed empty so the result
    /// type is `Unit -> Unit` (pure), but at runtime the partial-app emits
    /// a closure with the CPS calling convention (`(user_args, _Evidence,
    /// _ReturnK)`) because `wrap` itself was compiled that way.
    ///
    /// Returns `None` for non-App expressions, saturated calls, calls
    /// whose head isn't a known CPS function, and calls whose head can't
    /// be resolved to a `FunInfo` entry.
    fn cps_shape_from_partial_app(&self, expr: &Expr) -> Option<CpsShape> {
        fn collect_spine(e: &Expr) -> (&Expr, usize) {
            match &e.kind {
                ExprKind::App { func, .. } => {
                    let (head, n) = collect_spine(func);
                    (head, n + 1)
                }
                _ => (e, 0),
            }
        }
        let (head, supplied) = collect_spine(expr);
        if supplied == 0 {
            return None;
        }
        let info = match &head.kind {
            ExprKind::Var { name, .. } => self.resolved_fun_info(head.id, name)?,
            ExprKind::QualifiedName { module, name, .. } => {
                let qualified = format!("{}.{}", module, name);
                self.resolved_fun_info(head.id, &qualified)?
            }
            _ => return None,
        };
        let is_cps = !info.effects.is_empty() || info.is_open_row;
        if !is_cps {
            return None;
        }
        // FunInfo.arity counts Evidence + ReturnK; user arity excludes them.
        let head_user_arity = info.arity.saturating_sub(2);
        if supplied >= head_user_arity {
            return None;
        }
        Some(CpsShape {
            static_effects: info.effects.clone(),
            is_open_row: info.is_open_row,
        })
    }

    /// If `expr` is a `DictMethodAccess` for a trait method that carries
    /// effects, return its runtime CPS shape. Synthesized `DictMethodAccess`
    /// nodes have fresh `NodeId`s with no recorded type, so the type-based
    /// shape lookup misses them. Source the effects from the trait method's
    /// effect signature directly. Without this, a trait method passed as a
    /// first-class value (e.g. `run decode n`) falls through to the pure
    /// adapter and the resulting wrapper drops `_Evidence`/`_ReturnK` when
    /// calling the underlying CPS-shaped method.
    fn cps_shape_from_dict_method_access(&self, expr: &Expr) -> Option<CpsShape> {
        let ExprKind::DictMethodAccess {
            trait_name,
            method_index,
            ..
        } = &expr.kind
        else {
            return None;
        };
        let info = self.trait_info(trait_name)?;
        let method = info.methods.get(*method_index)?;
        let effects = self.canonicalize_effects(method.effect_sig.effects.clone());
        let is_open_row = method.effect_sig.is_open_row;
        if effects.is_empty() && !is_open_row {
            return None;
        }
        Some(CpsShape {
            static_effects: effects,
            is_open_row,
        })
    }

    fn wrap_pure_function_value_as_cps_adapter(
        &mut self,
        expr: &Expr,
        expected_ty: &crate::typechecker::Type,
    ) -> CExpr {
        let (user_arity, _) = util::arity_and_effects_from_type(expected_ty);
        let fun_var = self.fresh();
        let result_var = self.fresh();
        let mut params = Vec::with_capacity(user_arity + 2);
        let mut apply_args = Vec::with_capacity(user_arity);
        for _ in 0..user_arity {
            let param = self.fresh();
            apply_args.push(CExpr::Var(param.clone()));
            params.push(param);
        }
        params.push("_Evidence".to_string());
        params.push("_ReturnK".to_string());

        let pure_fun = self.lower_expr_value(expr);
        let pure_call = CExpr::Apply(Box::new(CExpr::Var(fun_var.clone())), apply_args);
        let return_call = CExpr::Apply(
            Box::new(CExpr::Var("_ReturnK".to_string())),
            vec![CExpr::Var(result_var.clone())],
        );
        let adapter = CExpr::Fun(
            params,
            Box::new(CExpr::Let(
                result_var,
                Box::new(pure_call),
                Box::new(return_call),
            )),
        );
        CExpr::Let(fun_var, Box::new(pure_fun), Box::new(adapter))
    }

    /// Adapt a CPS-shaped runtime value to a pure-shape callable. The
    /// inverse of `wrap_pure_function_value_as_cps_adapter`: needed when
    /// the type system has narrowed a CPS function's row variable to
    /// closed-empty (e.g. via let annotation or by saturating a callback
    /// argument with a pure function), but the underlying value is the
    /// partial application of a row-polymorphic function compiled with
    /// the CPS calling convention.
    ///
    /// The adapter takes the pure shape's user args, invokes the CPS
    /// value with an empty evidence tuple and an identity `_ReturnK`,
    /// and returns the result. Empty evidence is safe because the static
    /// narrowing means no handler effects are actually used by this
    /// invocation; if the underlying function tries to look up evidence,
    /// the type system would have rejected the program upstream.
    fn wrap_cps_function_value_as_pure_adapter(
        &mut self,
        expr: &Expr,
        expected_ty: &crate::typechecker::Type,
    ) -> CExpr {
        let (user_arity, _) = util::arity_and_effects_from_type(expected_ty);
        let fun_var = self.fresh();
        let identity_arg = self.fresh();
        let mut params = Vec::with_capacity(user_arity);
        let mut apply_args = Vec::with_capacity(user_arity + 2);
        for _ in 0..user_arity {
            let p = self.fresh();
            apply_args.push(CExpr::Var(p.clone()));
            params.push(p);
        }
        apply_args.push(CExpr::Tuple(vec![]));
        let identity_k = CExpr::Fun(
            vec![identity_arg.clone()],
            Box::new(CExpr::Var(identity_arg)),
        );
        apply_args.push(identity_k);

        let actual_fun = self.lower_expr_value(expr);
        let call = CExpr::Apply(Box::new(CExpr::Var(fun_var.clone())), apply_args);
        let adapter = CExpr::Fun(params, Box::new(call));
        CExpr::Let(fun_var, Box::new(actual_fun), Box::new(adapter))
    }

    fn adapt_cps_function_value_to_expected_shape(
        &mut self,
        expr: &Expr,
        expected_ty: &crate::typechecker::Type,
        actual_shape: CpsShape,
    ) -> CExpr {
        if actual_shape.is_open_row {
            return self.lower_expr_value(expr);
        }

        let (user_arity, _) = util::arity_and_effects_from_type(expected_ty);
        let fun_var = self.fresh();
        let ev_var = self.fresh();
        let mut params = Vec::with_capacity(user_arity + 2);
        let mut apply_args = Vec::with_capacity(user_arity + 2);
        for _ in 0..user_arity {
            let param = self.fresh();
            apply_args.push(CExpr::Var(param.clone()));
            params.push(param);
        }
        params.push("_Evidence".to_string());
        params.push("_ReturnK".to_string());

        let (_, expected_effects) = util::arity_and_effects_from_type(expected_ty);
        let expected_layout =
            evidence::EvidenceLayout::new(self.canonicalize_effects(expected_effects));
        let selectors = actual_shape
            .static_effects
            .iter()
            .map(|effect| {
                let family = crate::typechecker::applied_effect_family(effect);
                let matches = expected_layout
                    .tags()
                    .iter()
                    .enumerate()
                    .filter(|(_, candidate)| {
                        crate::typechecker::applied_effect_family(candidate) == family
                    })
                    .map(|(idx, _)| idx)
                    .collect::<Vec<_>>();
                if matches.len() == 1 {
                    CExpr::Lit(CLit::Int((matches[0] + 1) as i64))
                } else {
                    CExpr::Lit(CLit::Atom(effect.clone()))
                }
            })
            .collect();
        apply_args.push(CExpr::Var(ev_var.clone()));
        apply_args.push(CExpr::Var("_ReturnK".to_string()));

        let actual_fun = self.lower_expr_value(expr);
        let narrowed_evidence = evidence::reframe_evidence(
            CExpr::Var("_Evidence".to_string()),
            expected_layout.tags().len(),
            selectors,
        );
        let call = CExpr::Apply(Box::new(CExpr::Var(fun_var.clone())), apply_args);
        let adapter = CExpr::Fun(
            params,
            Box::new(CExpr::Let(
                ev_var,
                Box::new(narrowed_evidence),
                Box::new(call),
            )),
        );
        CExpr::Let(fun_var, Box::new(actual_fun), Box::new(adapter))
    }

    fn lower_cps_function_value_with_expected_shape(
        &mut self,
        expr: &Expr,
        expected_ty: &crate::typechecker::Type,
        expected_shape: CpsShape,
    ) -> CExpr {
        if matches!(expr.kind, ExprKind::Lambda { .. }) || Self::is_eta_reduced_effect_expr(expr) {
            // An open callback parameter only describes what its caller can
            // forward; it must not erase the concrete static prefix inferred
            // for a lambda at this call site.  Keeping that prefix lets the
            // lambda address generic handlers positionally (for example a
            // `Gen Int` callback passed through `..e` to generic `from_gen`),
            // without requiring the generic handler to mint a concrete tag at
            // runtime.
            let lambda_shape = self
                .expr_cps_function_shape(expr)
                .filter(|shape| !shape.static_effects.is_empty())
                .unwrap_or(expected_shape);
            let saved_ctx = self.lambda_effect_context.take();
            self.lambda_effect_context = Some(lambda_shape);
            let ce = self
                .lower_eta_reduced_effect_expr(expr)
                .unwrap_or_else(|| self.lower_expr_value(expr));
            self.lambda_effect_context = saved_ctx;
            return ce;
        }

        // Determine the actual runtime shape, prefering the resolved type
        // but falling back to a partial-application analysis when the type
        // system has narrowed the row variable (e.g. `wrap pure_fn` whose
        // type is `Unit -> Unit` but whose runtime closure is CPS-shaped
        // because `wrap` was compiled with `..e`).
        let actual_shape = self
            .expr_cps_function_shape(expr)
            .or_else(|| self.cps_shape_from_partial_app(expr))
            .or_else(|| self.cps_shape_from_dict_method_access(expr));

        if let Some(actual_shape) = actual_shape {
            self.adapt_cps_function_value_to_expected_shape(expr, expected_ty, actual_shape)
        } else {
            self.wrap_pure_function_value_as_cps_adapter(expr, expected_ty)
        }
    }

    pub(super) fn lower_expr_value_with_expected_type(
        &mut self,
        expr: &Expr,
        expected_ty: Option<&crate::typechecker::Type>,
    ) -> CExpr {
        if let Some(expected_ty) = expected_ty {
            if let ExprKind::Constructor { name, .. } = &expr.kind
                && matches!(expected_ty, crate::typechecker::Type::Fun(_, _, _))
                && let Some(ctor_fun) = {
                    let ctor_name = self.resolved_constructor_name_for(expr.id, name);
                    self.lower_constructor_function_value(&ctor_name, expected_ty)
                }
            {
                return ctor_fun;
            }

            if let Some(curried_lambda) =
                self.lower_curried_lambda_for_expected_arity(expr, expected_ty)
            {
                return curried_lambda;
            }

            if let Some((head, ctor_name, args)) = collect_ctor_call_with_head(expr) {
                let resolved_ctor = self.resolved_constructor_name_for(head.id, ctor_name);
                let bare = crate::typechecker::bare_type_name(match expected_ty {
                    crate::typechecker::Type::Con(name, _) => name,
                    _ => "",
                });
                if bare == "List"
                    && let crate::typechecker::Type::Con(_, type_args) = expected_ty
                    && let Some(elem_ty) = type_args.first()
                {
                    match (
                        resolved_ctor.rsplit('.').next().unwrap_or(&resolved_ctor),
                        args.as_slice(),
                    ) {
                        ("Nil", []) => return CExpr::Nil,
                        ("Cons", [head, tail]) => {
                            let head_var = self.fresh();
                            let tail_var = self.fresh();
                            let head_ce =
                                self.lower_expr_value_with_expected_type(head, Some(elem_ty));
                            let tail_ce =
                                self.lower_expr_value_with_expected_type(tail, Some(expected_ty));
                            return CExpr::Let(
                                head_var.clone(),
                                Box::new(head_ce),
                                Box::new(CExpr::Let(
                                    tail_var.clone(),
                                    Box::new(tail_ce),
                                    Box::new(CExpr::Cons(
                                        Box::new(CExpr::Var(head_var)),
                                        Box::new(CExpr::Var(tail_var)),
                                    )),
                                )),
                            );
                        }
                        _ => {}
                    }
                }

                if bare != "List"
                    && let Some(arg_tys) =
                        self.constructor_arg_types_from_expected(&resolved_ctor, expected_ty)
                {
                    let mut vars = Vec::new();
                    let mut bindings = Vec::new();
                    for (idx, arg) in args.iter().enumerate() {
                        let var = self.fresh();
                        let child_expected = arg_tys.get(idx);
                        let val = self.lower_expr_value_with_expected_type(arg, child_expected);
                        vars.push(var.clone());
                        bindings.push((var, val));
                    }
                    let atom = util::mangle_ctor_atom(
                        &resolved_ctor,
                        &self.constructor_atoms,
                        self.handler_origin_module(),
                    );
                    let mut elems = vec![CExpr::Lit(CLit::Atom(atom))];
                    elems.extend(vars.iter().map(|v| CExpr::Var(v.clone())));
                    let tuple = CExpr::Tuple(elems);
                    return self.wrap_let_bindings(bindings, tuple);
                }
            }

            if let ExprKind::Tuple { elements, .. } = &expr.kind
                && let crate::typechecker::Type::Con(name, elem_tys) = expected_ty
                && crate::typechecker::bare_type_name(name) == "Tuple"
                && elem_tys.len() == elements.len()
            {
                let mut vars = Vec::new();
                let mut bindings = Vec::new();
                for (elem, elem_ty) in elements.iter().zip(elem_tys.iter()) {
                    let var = self.fresh();
                    let val = self.lower_expr_value_with_expected_type(elem, Some(elem_ty));
                    vars.push(var.clone());
                    bindings.push((var, val));
                }
                let tuple = CExpr::Tuple(vars.iter().map(|v| CExpr::Var(v.clone())).collect());
                return self.wrap_let_bindings(bindings, tuple);
            }

            if let ExprKind::If {
                cond,
                then_branch,
                else_branch,
                ..
            } = &expr.kind
            {
                let cond_var = self.fresh();
                let cond_ce = self.lower_expr_value(cond);
                let then_ce =
                    self.lower_expr_value_with_expected_type(then_branch, Some(expected_ty));
                let else_ce =
                    self.lower_expr_value_with_expected_type(else_branch, Some(expected_ty));
                return CExpr::Let(
                    cond_var.clone(),
                    Box::new(cond_ce),
                    Box::new(CExpr::Case(
                        Box::new(CExpr::Var(cond_var)),
                        vec![
                            CArm {
                                pat: CPat::Lit(CLit::Atom("true".to_string())),
                                guard: None,
                                body: then_ce,
                            },
                            CArm {
                                pat: CPat::Lit(CLit::Atom("false".to_string())),
                                guard: None,
                                body: else_ce,
                            },
                        ],
                    )),
                );
            }

            if let Some(shape) = self.cps_function_shape_from_type(expected_ty) {
                return self.lower_cps_function_value_with_expected_shape(expr, expected_ty, shape);
            }

            // Expected is a pure function type, but the actual expression
            // is a partial application of a CPS-shaped function. The
            // static narrowing (row variable resolved to closed empty)
            // doesn't change the runtime BEAM arity of the partial-app
            // closure — `wrap pure_fn` is still a 3-arg closure even
            // though its inferred type is `Unit -> Unit`. Wrap it so the
            // call site sees the expected pure shape.
            if matches!(expected_ty, crate::typechecker::Type::Fun(_, _, _))
                && self.cps_shape_from_partial_app(expr).is_some()
            {
                return self.wrap_cps_function_value_as_pure_adapter(expr, expected_ty);
            }

            match &expr.kind {
                ExprKind::RecordCreate {
                    name,
                    fields,
                    record_name,
                } => {
                    let Some(field_tys) = self.record_field_types_from_expected(expected_ty) else {
                        return self.lower_expr_value(expr);
                    };
                    let order = self
                        .record_create_field_order(record_name.as_deref(), expr.id, name)
                        .cloned()
                        .unwrap_or_else(|| {
                            panic!(
                                "codegen: cannot resolve field layout for record `{name}` \
                                 (node {:?}, module `{}`). The record's type could not be \
                                 determined here, so its tuple layout is unknown.",
                                expr.id,
                                self.current_semantic_module_name(),
                            )
                        });
                    let field_map: HashMap<&str, &Expr> =
                        fields.iter().map(|(n, _, e)| (n.as_str(), e)).collect();
                    let mut vars = Vec::new();
                    let mut bindings = Vec::new();
                    for field_name in &order {
                        let var = self.fresh();
                        let field_expr = field_map
                            .get(field_name.as_str())
                            .expect("field missing in RecordCreate");
                        let child_expected = field_tys.get(field_name.as_str());
                        let val =
                            self.lower_expr_value_with_expected_type(field_expr, child_expected);
                        vars.push(var.clone());
                        bindings.push((var, val));
                    }
                    let ctor_name = self
                        .current_record_type_name(expr.id)
                        .and_then(|name| self.canonical_constructor_key_for(name))
                        .unwrap_or_else(|| self.resolved_constructor_name_for(expr.id, name));
                    let atom = util::mangle_ctor_atom(
                        &ctor_name,
                        &self.constructor_atoms,
                        self.handler_origin_module(),
                    );
                    let mut elems = vec![CExpr::Lit(CLit::Atom(atom))];
                    elems.extend(vars.iter().map(|v| CExpr::Var(v.clone())));
                    return self.wrap_let_bindings(bindings, CExpr::Tuple(elems));
                }
                ExprKind::AnonRecordCreate { fields, .. } => {
                    let Some(field_tys) = self.record_field_types_from_expected(expected_ty) else {
                        return self.lower_expr_value(expr);
                    };
                    let names: Vec<&str> = fields.iter().map(|(n, _, _)| n.as_str()).collect();
                    let tag = crate::ast::anon_record_tag(&names);
                    let mut sorted_names: Vec<String> =
                        names.iter().map(|n| n.to_string()).collect();
                    sorted_names.sort();
                    let field_map: HashMap<&str, &Expr> =
                        fields.iter().map(|(n, _, e)| (n.as_str(), e)).collect();
                    let mut vars = Vec::new();
                    let mut bindings = Vec::new();
                    for field_name in &sorted_names {
                        let var = self.fresh();
                        let field_expr = field_map
                            .get(field_name.as_str())
                            .expect("field missing in AnonRecordCreate");
                        let child_expected = field_tys.get(field_name.as_str());
                        let val =
                            self.lower_expr_value_with_expected_type(field_expr, child_expected);
                        vars.push(var.clone());
                        bindings.push((var, val));
                    }
                    let mut elems = vec![CExpr::Lit(CLit::Atom(tag))];
                    elems.extend(vars.iter().map(|v| CExpr::Var(v.clone())));
                    return self.wrap_let_bindings(bindings, CExpr::Tuple(elems));
                }
                _ => {}
            }
        }

        self.lower_expr_value(expr)
    }

    pub(super) fn lower_call_args_with_expected_types(
        &mut self,
        args: &[&Expr],
        param_types: Option<&[crate::typechecker::Type]>,
    ) -> (Vec<String>, Vec<(String, CExpr)>) {
        let mut arg_vars: Vec<String> = Vec::new();
        let mut bindings: Vec<(String, CExpr)> = Vec::new();
        for (i, arg) in args.iter().enumerate() {
            let v = self.fresh();
            let ce = self
                .lower_expr_value_with_expected_type(arg, param_types.and_then(|tys| tys.get(i)));
            arg_vars.push(v.clone());
            bindings.push((v, ce));
        }
        (arg_vars, bindings)
    }

    pub(super) fn lower_call_args(
        &mut self,
        args: &[&Expr],
        param_effects: Option<&HashMap<usize, Vec<String>>>,
    ) -> (Vec<String>, Vec<(String, CExpr)>) {
        let mut arg_vars: Vec<String> = Vec::new();
        let mut bindings: Vec<(String, CExpr)> = Vec::new();
        for (i, arg) in args.iter().enumerate() {
            let v = self.fresh();
            let saved_ctx = self.lambda_effect_context.take();
            if let Some(pe) = param_effects
                && let Some(effs) = pe.get(&i)
            {
                self.lambda_effect_context = Some(CpsShape {
                    static_effects: effs.clone(),
                    is_open_row: false,
                });
            }
            let ce = self
                .lower_eta_reduced_effect_expr(arg)
                .unwrap_or_else(|| self.lower_expr_value(arg));
            self.lambda_effect_context = saved_ctx;
            arg_vars.push(v.clone());
            bindings.push((v, ce));
        }
        (arg_vars, bindings)
    }
    pub(super) fn lower_eta_reduced_effect_op_ref(
        &mut self,
        node_id: crate::ast::NodeId,
        op_name: &str,
        qualifier: Option<&str>,
    ) -> Option<CExpr> {
        let effect_name = self.resolved_effect_call_name(node_id, op_name, qualifier)?;
        let _ = self.effect_defs.get(&effect_name)?.ops.get(op_name)?;
        let applied_effect = self
            .check_result
            .effect_at_node
            .get(&node_id)
            .map(crate::typechecker::applied_effect_key)
            .unwrap_or_else(|| effect_name.clone());
        let applied_effect = self.canonicalize_effect(&applied_effect);
        let op_info = self
            .effect_defs
            .get(&effect_name)?
            .ops
            .get(op_name)?
            .clone();

        // A nullary effect op (`fun now : Int`) can't be an eta-reduced *reference*
        // that still awaits arguments -- `now!` is always a saturated perform.
        // Without this, the zero-param loop below would emit `fun () -> perform`,
        // thunking the perform instead of running it. Fall through to
        // `lower_effect_call`, which performs immediately.
        if op_info.source_param_count == 0 {
            return None;
        }

        let mut params = Vec::new();
        let mut runtime_args = Vec::new();
        for idx in 0..op_info.source_param_count {
            let param = self.fresh();
            if op_info.runtime_param_positions.contains(&idx) {
                runtime_args.push(CExpr::Var(param.clone()));
            }
            params.push(param);
        }

        if let Some(shape) = self.lambda_effect_context.clone() {
            // Raw CPS shape: the resulting closure is passed to a slot that
            // expects an effectful function value, so it takes `_Evidence`
            // and `_ReturnK` and reads the per-op handler out of the
            // evidence vector at call time.
            let evidence = "_Evidence".to_string();
            let return_k = "_ReturnK".to_string();
            runtime_args.push(CExpr::Var(return_k.clone()));
            params.push(evidence.clone());
            params.push(return_k);
            // Build the op lookup against the lambda's evidence parameter.
            let saved_evidence = self.current_evidence.clone();
            self.current_evidence = Some(EvidenceCtx {
                var: evidence,
                layout: evidence::EvidenceLayout::new(shape.static_effects.iter().cloned()),
                is_open: shape.is_open_row,
            });
            let handler_expr = self.evidence_op_lookup(&applied_effect, op_name);
            self.current_evidence = saved_evidence;
            Some(CExpr::Fun(
                params,
                Box::new(CExpr::Apply(Box::new(handler_expr), runtime_args)),
            ))
        } else {
            // Value-closure shape: the resulting lambda is bound locally or
            // passed to a pure-shaped callback slot. Capture the in-scope
            // op closure (read out of current evidence) and provide an
            // identity return continuation.
            let handler_expr = self.evidence_op_lookup(&applied_effect, op_name);
            let return_value = self.fresh();
            runtime_args.push(CExpr::Fun(
                vec![return_value.clone()],
                Box::new(CExpr::Var(return_value)),
            ));
            Some(CExpr::Fun(
                params,
                Box::new(CExpr::Apply(Box::new(handler_expr), runtime_args)),
            ))
        }
    }

    pub(super) fn lower_eta_reduced_effect_expr(&mut self, expr: &Expr) -> Option<CExpr> {
        let mut args = Vec::new();
        let mut current = expr;
        let (effect_call_id, op_name, qualifier) = loop {
            match &current.kind {
                ExprKind::App { func, arg, .. } => {
                    args.push(arg.as_ref());
                    current = func.as_ref();
                }
                ExprKind::EffectCall {
                    name, qualifier, ..
                } => {
                    args.reverse();
                    break (current.id, name.as_str(), qualifier.as_deref());
                }
                _ => return None,
            }
        };

        if !args.is_empty() {
            return None;
        }
        self.lower_eta_reduced_effect_op_ref(effect_call_id, op_name, qualifier)
    }

    fn is_eta_reduced_effect_expr(expr: &Expr) -> bool {
        let mut args = Vec::new();
        let mut current = expr;
        loop {
            match &current.kind {
                ExprKind::App { func, arg, .. } => {
                    args.push(arg.as_ref());
                    current = func.as_ref();
                }
                ExprKind::EffectCall { .. } => return args.is_empty(),
                _ => return false,
            }
        }
    }
}
