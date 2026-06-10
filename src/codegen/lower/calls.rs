use crate::ast::{Expr, ExprKind, NodeId, Pat};
use crate::codegen::cerl::{CExpr, CLit};
use crate::codegen::runtime_shape::CpsShape;

use super::errors::ErrorKind;
use super::evidence;
use super::util::{
    cerl_call, collect_ctor_call, collect_effect_call_expr, collect_fun_call,
    collect_qualified_call, core_var, lower_string_to_binary,
};
use super::{Lowerer, QualifiedCallSite, ResolvedCallSite};

#[derive(Clone, Copy)]
enum RuntimeCpsArgLowering {
    Value,
    EtaReduced,
}

/// How a CPS call reaches its callee. `Value` applies a runtime function value
/// (closure, `FunRef`, or var); `Remote` emits a direct `call 'mod':'fun'(...)`
/// to a known exported function (a cross-module specialized dict method).
enum CpsCallee {
    Value(CExpr),
    Remote { erlang_mod: String, name: String },
}

impl CpsCallee {
    /// Emit the call: apply a value, or a direct remote call to a known fun.
    fn apply(self, args: Vec<CExpr>) -> CExpr {
        match self {
            CpsCallee::Value(f) => CExpr::Apply(Box::new(f), args),
            CpsCallee::Remote { erlang_mod, name } => CExpr::Call(erlang_mod, name, args),
        }
    }
}

struct RuntimeCpsApplySite<'a> {
    plan: super::super::call_effects::CpsCallPlan,
    callee: CpsCallee,
    args: &'a [&'a Expr],
    return_k: Option<CExpr>,
    nested_pure_arg_lowering: RuntimeCpsArgLowering,
    flat_arg_lowering: RuntimeCpsArgLowering,
}

impl<'a> Lowerer<'a> {
    pub(super) fn lower_resolved_fun_call(&mut self, site: ResolvedCallSite<'_>) -> Option<CExpr> {
        let ResolvedCallSite {
            app_id,
            lookup_name,
            emit_name,
            head,
            args,
            return_k,
            call_span,
            fallback_erlang_module,
        } = site;
        // Source of truth: the per-call effect map populated pre-lowering.
        // `info` tells us whether this call is effectful (needs evidence + _ReturnK)
        // and which effects the callee declares; both used to be recomputed here
        // from `resolved_effects` + `effect_handler_ops`.
        let cps_plan = self
            .call_effects
            .get(&app_id)
            .and_then(|info| info.cps_call_plan());
        // `row_forwarded` says "callee is row-polymorphic, forward caller's
        // ambient evidence unchanged (don't project)". Without distinguishing
        // it from closed calls, a call to e.g. `wrap : ... -> ... needs
        // {Stdio, ..e}` would project the caller's evidence down to just
        // `{Stdio}` and drop the entries that the open-row tail is supposed
        // to carry through into `wrap`'s body.
        let is_effectful = cps_plan.is_some();
        let callee_effects_vec = cps_plan
            .as_ref()
            .map(|plan| plan.effects.clone())
            .unwrap_or_default();
        let is_row_forward = cps_plan
            .as_ref()
            .map(|plan| plan.row_forwarded)
            .unwrap_or(false);
        let total_arity = self
            .resolved_fun_info(head.id, lookup_name)
            .map(|f| f.arity);
        let has_static_call_target = total_arity.is_some()
            || fallback_erlang_module.is_some()
            || self.resolved.get(&head.id).is_some_and(|resolved| {
                matches!(
                    resolved.kind,
                    super::super::resolve::ResolvedCodegenKind::BeamFunction { .. }
                        | super::super::resolve::ResolvedCodegenKind::ExternalFunction { .. }
                )
            });
        if !has_static_call_target {
            return None;
        }
        // Effectful callees take `_Evidence` and `_ReturnK`.
        let extras = if is_effectful { 2 } else { 0 };
        let call_arity = total_arity.unwrap_or(args.len() + extras);

        if args.len() + extras == call_arity {
            if is_effectful
                && let Some(hof_call) = self.try_hof_direct_specialized_call(
                    lookup_name,
                    emit_name,
                    head,
                    args,
                    return_k.clone(),
                )
            {
                return Some(hof_call);
            }
            if is_effectful
                && let Some(inlined) =
                    self.try_inline_static_helper_call(lookup_name, head, args, return_k.clone())
            {
                return Some(inlined);
            }
            if is_effectful
                && let Some(variant_call) = self.try_imported_static_helper_variant_call(
                    lookup_name,
                    head,
                    args,
                    return_k.clone(),
                )
            {
                return Some(variant_call);
            }

            let param_types = self.resolved_fun_info(head.id, lookup_name).map(|f| {
                f.param_types
                    .iter()
                    .take(args.len())
                    .cloned()
                    .collect::<Vec<_>>()
            });

            let is_effectful_outer = is_effectful;
            let effectful_arg_idxs: Vec<usize> = if is_effectful_outer {
                args.iter()
                    .enumerate()
                    .filter(|(_, a)| self.expr_is_effectful_call(a))
                    .map(|(i, _)| i)
                    .collect()
            } else {
                Vec::new()
            };

            if !effectful_arg_idxs.is_empty() {
                // CPS-chain effectful argument calls so that aborting handlers
                // skip the outer call entirely. For each effectful arg, the rest
                // of the outer call (and the remaining args) becomes the inner
                // call's return continuation.
                let mut arg_vars: Vec<String> = Vec::with_capacity(args.len());
                let mut pure_bindings: Vec<(String, CExpr)> = Vec::new();
                for (i, arg) in args.iter().enumerate() {
                    let v = self.fresh();
                    arg_vars.push(v.clone());
                    if !effectful_arg_idxs.contains(&i) {
                        let pty = param_types.as_ref().and_then(|t| t.get(i));
                        let ce = self.lower_expr_value_with_expected_type(arg, pty);
                        pure_bindings.push((v, ce));
                    }
                }

                let mut call_args: Vec<CExpr> =
                    arg_vars.iter().map(|v| CExpr::Var(v.clone())).collect();
                // Effectful callee: thread evidence + _ReturnK.
                let (ev_var, ev_ce) =
                    self.build_call_evidence_with(&callee_effects_vec, is_row_forward);
                call_args.push(CExpr::Var(ev_var.clone()));
                let (rk_var, rk_ce) = self.effectful_call_return_k_binding(return_k);
                call_args.push(CExpr::Var(rk_var.clone()));

                let outer_call = self.emit_call(
                    emit_name,
                    head.id,
                    call_arity,
                    call_args,
                    call_span,
                    fallback_erlang_module,
                );
                let mut body = CExpr::Let(rk_var, Box::new(rk_ce), Box::new(outer_call));
                body = CExpr::Let(ev_var, Box::new(ev_ce), Box::new(body));

                // Wrap body with each effectful arg's CPS continuation,
                // innermost (rightmost) first so left-to-right order is preserved.
                for &i in effectful_arg_idxs.iter().rev() {
                    let v = arg_vars[i].clone();
                    let inner_k = CExpr::Fun(vec![v], Box::new(body));
                    body = self.lower_expr_with_call_return_k(args[i], Some(inner_k));
                }

                return Some(self.wrap_let_bindings(pure_bindings, body));
            }

            let (mut arg_vars, mut bindings) =
                self.lower_call_args_with_expected_types(args, param_types.as_deref());
            if is_effectful {
                // Effectful callee: thread evidence + _ReturnK.
                let (ev_var, ev_ce) =
                    self.build_call_evidence_with(&callee_effects_vec, is_row_forward);
                bindings.push((ev_var.clone(), ev_ce));
                arg_vars.push(ev_var);
                let (rk_var, rk_ce) = self.effectful_call_return_k_binding(return_k);
                bindings.push((rk_var.clone(), rk_ce));
                arg_vars.push(rk_var);
            }
            let call_args: Vec<CExpr> = arg_vars.iter().map(|v| CExpr::Var(v.clone())).collect();
            let call = self.emit_call(
                emit_name,
                head.id,
                call_arity,
                call_args,
                call_span,
                fallback_erlang_module,
            );
            return Some(self.wrap_let_bindings(bindings, call));
        }

        if let Some(arity) = total_arity {
            let user_slots = arity.saturating_sub(extras);
            if args.len() < user_slots {
                let remaining_user = user_slots - args.len();
                let param_types = self.resolved_fun_info(head.id, lookup_name).map(|f| {
                    f.param_types
                        .iter()
                        .take(args.len())
                        .cloned()
                        .collect::<Vec<_>>()
                });
                let (arg_vars, bindings) =
                    self.lower_call_args_with_expected_types(args, param_types.as_deref());
                let mut params: Vec<String> = Vec::new();
                for _ in 0..remaining_user {
                    params.push(self.fresh());
                }
                let mut call_args: Vec<CExpr> =
                    arg_vars.iter().map(|v| CExpr::Var(v.clone())).collect();
                call_args.extend(params.iter().map(|p| CExpr::Var(p.clone())));
                if is_effectful {
                    // Closure takes `_Evidence` and `_ReturnK` for the
                    // residual user args; the call forwards them straight
                    // through.
                    let ev = "_Evidence".to_string();
                    params.push(ev.clone());
                    call_args.push(CExpr::Var(ev));
                    let rk = "_ReturnK".to_string();
                    params.push(rk.clone());
                    call_args.push(CExpr::Var(rk));
                }
                let call = self.emit_call(
                    emit_name,
                    head.id,
                    arity,
                    call_args,
                    call_span,
                    fallback_erlang_module,
                );
                let lambda = CExpr::Fun(params, Box::new(call));
                return Some(self.wrap_let_bindings(bindings, lambda));
            }
        }

        None
    }

    fn lower_runtime_cps_arg(&mut self, arg: &Expr, mode: RuntimeCpsArgLowering) -> CExpr {
        match mode {
            RuntimeCpsArgLowering::Value => self.lower_expr_value(arg),
            RuntimeCpsArgLowering::EtaReduced => self
                .lower_eta_reduced_effect_expr(arg)
                .unwrap_or_else(|| self.lower_expr_value(arg)),
        }
    }

    /// Lower a call to an already-materialized runtime CPS callable value.
    ///
    /// The call shape still comes from `CallEffectInfo::cps_call_plan()`;
    /// callers supply only the callee expression and the narrow argument
    /// lowering mode needed to preserve existing value-boundary behavior.
    fn lower_runtime_cps_apply(&mut self, site: RuntimeCpsApplySite<'_>) -> CExpr {
        let RuntimeCpsApplySite {
            plan,
            callee,
            args,
            return_k,
            nested_pure_arg_lowering,
            flat_arg_lowering,
        } = site;
        let absorbed = plan.effects;
        let is_row_forward = plan.row_forwarded;

        let effectful_arg_idxs: Vec<usize> = args
            .iter()
            .enumerate()
            .filter(|(_, a)| self.expr_is_effectful_call(a))
            .map(|(i, _)| i)
            .collect();

        if !effectful_arg_idxs.is_empty() {
            let mut arg_vars: Vec<String> = Vec::with_capacity(args.len());
            let mut pure_bindings: Vec<(String, CExpr)> = Vec::new();
            for (i, arg) in args.iter().enumerate() {
                let v = self.fresh();
                arg_vars.push(v.clone());
                if !effectful_arg_idxs.contains(&i) {
                    let ce = self.lower_runtime_cps_arg(arg, nested_pure_arg_lowering);
                    pure_bindings.push((v, ce));
                }
            }

            let mut call_args: Vec<CExpr> =
                arg_vars.iter().map(|v| CExpr::Var(v.clone())).collect();
            let (ev_var, ev_ce) = self.build_call_evidence_with(&absorbed, is_row_forward);
            call_args.push(CExpr::Var(ev_var.clone()));
            let (rk_var, rk_ce) = self.effectful_call_return_k_binding(return_k);
            call_args.push(CExpr::Var(rk_var.clone()));

            let outer_call = callee.apply(call_args);
            let mut body = CExpr::Let(rk_var, Box::new(rk_ce), Box::new(outer_call));
            body = CExpr::Let(ev_var, Box::new(ev_ce), Box::new(body));

            for &i in effectful_arg_idxs.iter().rev() {
                let v = arg_vars[i].clone();
                let inner_k = CExpr::Fun(vec![v], Box::new(body));
                body = self.lower_expr_with_call_return_k(args[i], Some(inner_k));
            }

            return self.wrap_let_bindings(pure_bindings, body);
        }

        let mut arg_vars: Vec<String> = Vec::with_capacity(args.len());
        let mut bindings: Vec<(String, CExpr)> = Vec::new();
        for arg in args {
            let v = self.fresh();
            let ce = self.lower_runtime_cps_arg(arg, flat_arg_lowering);
            arg_vars.push(v.clone());
            bindings.push((v, ce));
        }
        let (ev_var, ev_ce) = self.build_call_evidence_with(&absorbed, is_row_forward);
        bindings.push((ev_var.clone(), ev_ce));
        arg_vars.push(ev_var);
        let (rk_var, rk_ce) = self.effectful_call_return_k_binding(return_k);
        bindings.push((rk_var.clone(), rk_ce));
        arg_vars.push(rk_var);
        let call = callee.apply(arg_vars.iter().map(|v| CExpr::Var(v.clone())).collect());
        self.wrap_let_bindings(bindings, call)
    }

    /// Lower a call to a runtime closure value bound to a local variable
    /// whose type carries effects (e.g. `let g = factory(); g x`). See
    /// [`Self::lower_resolved_fun_call`] for the resolved-fun counterpart
    /// and the rationale for keeping the two paths separate.
    pub(super) fn lower_effectful_var_call(
        &mut self,
        app_id: NodeId,
        var_name: &str,
        args: &[&Expr],
        return_k: Option<CExpr>,
    ) -> Option<CExpr> {
        if let Some(hof_call) =
            self.try_hof_direct_specialized_value_call(var_name, args, return_k.clone())
        {
            return Some(hof_call);
        }
        // Source of truth: the per-call effect map, keyed by this App's NodeId.
        // Pre-pass already walked the lexical scope and recorded the absorbed
        // effects for the bound variable on its call-site App entry.
        //
        // `is_row_forward` distinguishes two effectful shapes:
        //   - `StaticOps`: callee asks for a specific set of effects. Caller
        //     projects its evidence to that set.
        //   - `RowForwarded`: callee is row-polymorphic (e.g. an open-row
        //     callback param). Caller forwards its full ambient evidence
        //     without narrowing — including when `static_ops` is empty, which
        //     is the open-row-only case (`f: Unit -> Unit needs {..e}`).
        let plan = self
            .call_effects
            .get(&app_id)
            .and_then(|info| info.cps_call_plan())?;
        Some(self.lower_runtime_cps_apply(RuntimeCpsApplySite {
            plan,
            callee: CpsCallee::Value(CExpr::Var(core_var(var_name))),
            args,
            return_k,
            nested_pure_arg_lowering: RuntimeCpsArgLowering::EtaReduced,
            flat_arg_lowering: RuntimeCpsArgLowering::EtaReduced,
        }))
    }

    /// If the trait method call at `app_id` dispatches on a statically-known
    /// impl whose method is hoisted to a top-level function, return a direct
    /// callee — a local `FunRef` (Phase 2) or a cross-module `call` (Phase 3) —
    /// and record the specialization. Returns `None` (and records the fallback
    /// reason) when the site stays on the normal `element/2` dispatch. This only
    /// chooses the callee; argument/evidence/return-continuation threading is
    /// unchanged. `supplied` is the user-arg count and `cps` the call-site ABI.
    fn specialized_dict_method_callee(
        &mut self,
        app_id: NodeId,
        dict: &Expr,
        trait_name: &str,
        method_index: usize,
        supplied: usize,
        cps: bool,
    ) -> Option<CpsCallee> {
        match self.classify_dict_specialization(app_id, dict, trait_name, method_index, supplied, cps)?
        {
            Ok(callee) => {
                self.trait_spec_stats.record_specialized(app_id);
                Some(callee)
            }
            Err(reason) => {
                self.trait_spec_stats.record_fallback(app_id, reason);
                None
            }
        }
    }

    /// Decide a known dispatch site's specialization outcome (no stats / no
    /// mutation). `None` => not a statically-known site (not counted); `Some` =>
    /// a known site, either specialized (`Ok`) or a fallback (`Err(reason)`).
    fn classify_dict_specialization(
        &self,
        app_id: NodeId,
        dict: &Expr,
        trait_name: &str,
        method_index: usize,
        supplied: usize,
        cps: bool,
    ) -> Option<Result<CpsCallee, super::trait_spec_stats::FallbackReason>> {
        use super::trait_spec_stats::FallbackReason;

        let (dict_constructor, sub_dicts_empty) =
            match self.optimization.dict_dispatch.get(&app_id)? {
                super::super::trait_dispatch::DictDispatch::KnownImpl {
                    dict_constructor,
                    method_index: known_index,
                    sub_dicts,
                } if *known_index == method_index => (dict_constructor.clone(), sub_dicts.is_empty()),
                _ => return None,
            };

        Some(if !sub_dicts_empty {
            Err(FallbackReason::Parameterized)
        } else if self.dict_method_user_arity(&dict_constructor, trait_name, method_index)
            != Some(supplied)
        {
            // Partial/over-application: the hoisted function's arity would not
            // match. (Saturated trait calls are the norm; guard anyway.)
            Err(FallbackReason::Unsaturated)
        } else if let Some(hoist) = self.dict_method_hoists.get(&(dict_constructor.clone(), method_index))
        {
            // Local hoisted method: direct `FunRef` apply.
            if hoist.is_cps != cps {
                Err(FallbackReason::AbiMismatch)
            } else {
                let arity = supplied + if cps { 2 } else { 0 };
                Ok(CpsCallee::Value(CExpr::FunRef(hoist.fn_name.clone(), arity)))
            }
        } else if let Some(erlang_mod) = self.imported_dict_erlang_mod(dict) {
            // Imported hoisted method: direct cross-module call. Every module
            // hoists all its nullary dict methods with this deterministic name,
            // and the call's CPS shape derives from the same impl-effect data as
            // the producer's, so the remote function's arity matches.
            let name = format!("__saga_dictmethod_{dict_constructor}_{method_index}");
            Ok(CpsCallee::Remote { erlang_mod, name })
        } else {
            // Known impl on a dict we cannot resolve to a module — leave it on
            // the dict-passing path rather than emit an unresolved call.
            Err(FallbackReason::Imported)
        })
    }

    /// The trait method's user-argument arity (excludes `_Evidence`/`_ReturnK`),
    /// from the trait signature. Available cross-module for imported traits.
    fn trait_method_user_arity(&self, trait_name: &str, method_index: usize) -> Option<usize> {
        self.check_result
            .traits
            .get(trait_name)
            .and_then(|info| info.methods.get(method_index))
            .map(|m| m.param_types.len())
    }

    /// User-argument arity of a dict method's `method_index`, for the saturation
    /// guard. Prefers the trait signature (`trait_name`), which covers local and
    /// imported-into-scope traits. Falls back to the dict constructor's own
    /// method lambda arity — needed when the trait is defined in a *dependency*
    /// the consumer never imported (e.g. a library's internal `VariantPayload`),
    /// surfaced here only because the cross-module fold inlined a body that calls
    /// it. Impl methods carry the full parameter list (eta-reduced impls are
    /// rejected at typecheck), so the lambda arity equals the trait arity.
    fn dict_method_user_arity(
        &self,
        dict_constructor: &str,
        trait_name: &str,
        method_index: usize,
    ) -> Option<usize> {
        self.trait_method_user_arity(trait_name, method_index)
            .or_else(|| self.external_dict_method_arity(dict_constructor, method_index))
    }

    /// The user arity of a dict constructor's method lambda, looked up across the
    /// compiled modules (including dependencies). The elaborated method lambda's
    /// params are the user params (evidence/return-K are added at lowering).
    fn external_dict_method_arity(
        &self,
        dict_constructor: &str,
        method_index: usize,
    ) -> Option<usize> {
        for compiled in self.ctx.modules.values() {
            for decl in &compiled.elaborated {
                if let crate::ast::Decl::DictConstructor { name, methods, .. } = decl
                    && name == dict_constructor
                    && let Some(method) = methods.get(method_index)
                    && let crate::ast::ExprKind::Lambda { params, .. } = &method.kind
                {
                    return Some(params.len());
                }
            }
        }
        None
    }

    /// The Erlang module that defines an imported dict's hoisted methods, by
    /// resolving the dict expression's `DictRef`. `None` for a local dict (which
    /// uses the local `FunRef` path) or an unresolved/non-`DictRef` dict.
    fn imported_dict_erlang_mod(&self, dict: &Expr) -> Option<String> {
        let mut head = dict;
        while let ExprKind::App { func, .. } = &head.kind {
            head = func;
        }
        if !matches!(head.kind, ExprKind::DictRef { .. }) {
            return None;
        }
        match &self.resolved.get(&head.id)?.kind {
            super::super::resolve::ResolvedCodegenKind::BeamFunction {
                erlang_mod: Some(m),
                ..
            } => Some(m.clone()),
            super::super::resolve::ResolvedCodegenKind::ExternalFunction {
                target_erlang_mod,
                ..
            } => Some(target_erlang_mod.clone()),
            _ => None,
        }
    }

    /// Lower a saturated effectful call whose head is a `DictMethodAccess`
    /// (post-elaboration shape of a trait method call). Returns `None` when
    /// the per-call effect map says the call is pure — caller falls through
    /// to the regular non-effectful path which extracts the method via
    /// `erlang:element` and applies it without evidence threading.
    pub(super) fn lower_dict_method_call(
        &mut self,
        app_id: NodeId,
        dict: &Expr,
        trait_name: &str,
        method_index: usize,
        args: &[&Expr],
        return_k: Option<CExpr>,
    ) -> Option<CExpr> {
        let plan = self
            .call_effects
            .get(&app_id)
            .and_then(|info| info.cps_call_plan())?;

        // Statically-known impl with a hoisted method — call it directly,
        // skipping the dict tuple build and `element/2`: a local `FunRef`
        // (Phase 2) or a cross-module call (Phase 3). Only the callee changes;
        // evidence/return-continuation threading is unchanged.
        if let Some(callee) =
            self.specialized_dict_method_callee(app_id, dict, trait_name, method_index, args.len(), true)
        {
            return Some(self.lower_runtime_cps_apply(RuntimeCpsApplySite {
                plan,
                callee,
                args,
                return_k,
                nested_pure_arg_lowering: RuntimeCpsArgLowering::Value,
                flat_arg_lowering: RuntimeCpsArgLowering::EtaReduced,
            }));
        }

        let dict_var = self.fresh();
        let dict_ce = self.lower_expr_value(dict);
        let method_var = self.fresh();
        let extract = cerl_call(
            "erlang",
            "element",
            vec![
                CExpr::Lit(CLit::Int(method_index as i64 + 1)),
                CExpr::Var(dict_var.clone()),
            ],
        );

        let body = self.lower_runtime_cps_apply(RuntimeCpsApplySite {
            plan,
            callee: CpsCallee::Value(CExpr::Var(method_var.clone())),
            args,
            return_k,
            nested_pure_arg_lowering: RuntimeCpsArgLowering::Value,
            flat_arg_lowering: RuntimeCpsArgLowering::EtaReduced,
        });
        let body = CExpr::Let(method_var, Box::new(extract), Box::new(body));
        Some(CExpr::Let(dict_var, Box::new(dict_ce), Box::new(body)))
    }

    /// Lower a saturated effectful call whose head is a `Lambda` literal —
    /// `(fun x -> body) y`. Returns `None` when `call_effects[app_id]`
    /// classifies the call as pure; the caller then falls through to the
    /// regular path where the lambda lowers as a pure closure.
    ///
    /// When effectful, the lambda is recompiled as effectful (taking
    /// `_Evidence`/`_ReturnK` params, body lowered with evidence installed)
    /// by setting `lambda_effect_context` for the duration of `lower_expr`
    /// on the head. The call site threads evidence + return_k like any
    /// other effectful call. This preserves §8: the body sees the *call-time*
    /// evidence (passed as a param), not creation-time evidence.
    pub(super) fn lower_lambda_head_call(
        &mut self,
        app_id: NodeId,
        lambda: &Expr,
        args: &[&Expr],
        return_k: Option<CExpr>,
    ) -> Option<CExpr> {
        let plan = self
            .call_effects
            .get(&app_id)
            .and_then(|info| info.cps_call_plan())?;

        let saved_ctx = self.lambda_effect_context.take();
        self.lambda_effect_context = Some(CpsShape {
            static_effects: plan.effects.clone(),
            is_open_row: plan.row_forwarded,
        });
        let func_ce = self.lower_expr(lambda);
        self.lambda_effect_context = saved_ctx;

        let func_var = self.fresh();
        let body = self.lower_runtime_cps_apply(RuntimeCpsApplySite {
            plan,
            callee: CpsCallee::Value(CExpr::Var(func_var.clone())),
            args,
            return_k,
            nested_pure_arg_lowering: RuntimeCpsArgLowering::Value,
            flat_arg_lowering: RuntimeCpsArgLowering::EtaReduced,
        });
        Some(CExpr::Let(func_var, Box::new(func_ce), Box::new(body)))
    }

    fn lower_generic_apply(&mut self, callee: &Expr, args: &[&Expr]) -> CExpr {
        let callee_arity = match &callee.kind {
            ExprKind::Var { name, .. } if self.resolved.contains_key(&callee.id) => {
                self.resolved_fun_info(callee.id, name).map(|f| f.arity)
            }
            _ => None,
        };

        if let Some(arity) = callee_arity
            && arity < args.len()
        {
            let (arg_vars, mut bindings) = self.lower_call_args(args, None);
            let sat_args: Vec<CExpr> = arg_vars[..arity]
                .iter()
                .map(|v| CExpr::Var(v.clone()))
                .collect();
            let func_ce = self.lower_expr(callee);
            let result_var = self.fresh();
            bindings.push((
                result_var.clone(),
                CExpr::Apply(Box::new(func_ce), sat_args),
            ));

            let extra_args: Vec<CExpr> = arg_vars[arity..]
                .iter()
                .map(|v| CExpr::Var(v.clone()))
                .collect();
            let call = CExpr::Apply(Box::new(CExpr::Var(result_var)), extra_args);
            self.wrap_let_bindings(bindings, call)
        } else {
            let func_var = self.fresh();
            let func_ce = self.lower_expr(callee);
            let (arg_vars, mut bindings) = self.lower_call_args(args, None);
            bindings.insert(0, (func_var.clone(), func_ce));
            let call = CExpr::Apply(
                Box::new(CExpr::Var(func_var)),
                arg_vars.into_iter().map(CExpr::Var).collect(),
            );
            self.wrap_let_bindings(bindings, call)
        }
    }

    pub(super) fn lower_app_expr(&mut self, expr: &Expr) -> CExpr {
        if let Some((ctor_name, args)) = collect_ctor_call(expr) {
            return self.lower_ctor(ctor_name, args);
        }

        if let Some((head_expr, op_name, qualifier, args)) = collect_effect_call_expr(expr) {
            return self.lower_effect_call(
                head_expr.id,
                op_name,
                qualifier,
                &args.into_iter().cloned().collect::<Vec<_>>(),
                None,
            );
        }

        let qualified_call = collect_qualified_call(expr);
        if let Some((module, func_name, head, args)) = qualified_call {
            let qualified = format!("{}.{}", module, func_name);
            if self.is_known_constructor(&qualified) || self.is_known_constructor(func_name) {
                return self.lower_ctor(func_name, args);
            }
            if let Some(resolved) = self.resolved.get(&head.id)
                && let super::super::resolve::ResolvedCodegenKind::Intrinsic { id, .. } =
                    &resolved.kind
                && let Some(ce) = self.lower_intrinsic(*id, &args)
            {
                return ce;
            }
            if self.resolved.contains_key(&head.id) {
                if let Some(call) = self.lower_qualified_call(QualifiedCallSite {
                    app_id: expr.id,
                    module,
                    func_name,
                    head,
                    args: &args,
                    return_k: None,
                    call_span: Some(&expr.span),
                }) {
                    return call;
                }
                return self.lower_generic_apply(head, &args);
            }
            if let Some(call) = self.lower_qualified_call(QualifiedCallSite {
                app_id: expr.id,
                module,
                func_name,
                head,
                args: &args,
                return_k: None,
                call_span: Some(&expr.span),
            }) {
                return call;
            }
        }

        let fun_call = collect_fun_call(expr);
        if let Some((_func_name, head, args)) = fun_call.as_ref()
            && let Some(resolved) = self.resolved.get(&head.id)
            && let super::super::resolve::ResolvedCodegenKind::Intrinsic { id, .. } = &resolved.kind
            && let Some(ce) = self.lower_intrinsic(*id, args)
        {
            return ce;
        }

        if let Some((func_name, _head, args)) = fun_call.as_ref()
            && (*func_name == "panic" || *func_name == "todo")
            && args.len() == 1
        {
            let v = self.fresh();
            let (kind, arg) = if *func_name == "todo" {
                (ErrorKind::Todo, lower_string_to_binary("not implemented"))
            } else {
                (ErrorKind::Panic, self.lower_expr_value(args[0]))
            };
            let error = self.make_error(kind, CExpr::Var(v.clone()), Some(&expr.span));
            return CExpr::Let(v, Box::new(arg), Box::new(error));
        }

        if let Some((func_name, head_expr, args)) = fun_call.as_ref()
            && self.resolved.contains_key(&head_expr.id)
            && let Some(call) = self.lower_resolved_fun_call(ResolvedCallSite {
                app_id: expr.id,
                lookup_name: func_name,
                emit_name: func_name,
                head: head_expr,
                args,
                return_k: None,
                call_span: Some(&expr.span),
                fallback_erlang_module: None,
            })
        {
            return call;
        }

        if let Some((var_name, _head, args)) = fun_call.as_ref()
            && let Some(call) = self.try_hof_direct_specialized_value_call(var_name, args, None)
        {
            return call;
        }

        if self.expr_is_effectful_call(expr)
            && let Some((var_name, _, args)) = fun_call.as_ref()
        {
            return self
                .lower_effectful_var_call(expr.id, var_name, args, None)
                .expect("effectful variable call should lower");
        }

        // Phase 2: pure trait method call with a statically-known, locally-
        // hoisted impl — call the hoisted method function directly instead of
        // building the dict tuple and extracting via `element/2`. Guarded to
        // pure calls (effectful dict calls specialize via the CPS path), so the
        // pure ABI (`cps = false`) is the right one to ask for here.
        if !self.expr_is_effectful_call(expr)
            && let Some((dict, trait_name, method_index, dm_args)) =
                super::util::collect_dict_method_call(expr)
            && let Some(callee) = self.specialized_dict_method_callee(
                expr.id,
                dict,
                trait_name,
                method_index,
                dm_args.len(),
                false,
            )
        {
            let arg_ces: Vec<CExpr> = dm_args.iter().map(|a| self.lower_expr_value(a)).collect();
            return callee.apply(arg_ces);
        }

        let mut callee = expr;
        let mut args_rev = Vec::new();
        while let ExprKind::App { func, arg, .. } = &callee.kind {
            args_rev.push(arg.as_ref());
            callee = func.as_ref();
        }
        args_rev.reverse();

        // Lambda-headed effectful call: `(fun x -> ...) y`. Populator tagged
        // `expr.id` with `CallEffectInfo` based on the lambda's typechecker-
        // resolved effect row. Route through `lower_lambda_head_call` so the
        // lambda is compiled as effectful (params include `_Evidence`/
        // `_ReturnK`) and the call threads evidence + return_k. Returns
        // `None` for pure-classified calls — fall through to the plain path.
        if matches!(callee.kind, ExprKind::Lambda { .. })
            && let Some(call) = self.lower_lambda_head_call(expr.id, callee, &args_rev, None)
        {
            return call;
        }

        if self.expr_is_effectful_call(expr) {
            self.panic_unhandled_effectful_app(expr, Some(callee));
        }

        self.lower_generic_apply(callee, &args_rev)
    }

    /// Lower a qualified function call like `Math.abs x` to `call 'math':'abs'(X)`.
    /// For effectful imported functions, handler params and _ReturnK are threaded.
    pub(super) fn lower_qualified_call(&mut self, site: QualifiedCallSite<'_>) -> Option<CExpr> {
        let QualifiedCallSite {
            app_id,
            module,
            func_name,
            head,
            args,
            return_k,
            call_span,
        } = site;
        let erlang_module = self
            .module_aliases
            .get(module)
            .cloned()
            .unwrap_or_else(|| module.to_lowercase());

        let qualified = format!("{}.{}", module, func_name);
        self.lower_resolved_fun_call(ResolvedCallSite {
            app_id,
            lookup_name: &qualified,
            emit_name: func_name,
            head,
            args,
            return_k,
            call_span,
            fallback_erlang_module: Some(erlang_module.as_str()),
        })
    }
    fn lower_local_fun_ref(
        &mut self,
        name: &str,
        arity: usize,
        effects: Option<Vec<String>>,
        source_module: Option<&str>,
    ) -> CExpr {
        if let Some(source_module) =
            source_module.filter(|source| *source != self.current_source_module)
        {
            let (erlang_mod, target_name) = self
                .imported_handler_external_target(source_module, name, arity)
                .unwrap_or_else(|| (Self::module_name_to_erlang(source_module), name.to_string()));
            if arity == 0 {
                return CExpr::Call(erlang_mod, target_name, vec![]);
            }
            if let Some(effects) = effects.as_ref()
                && !effects.is_empty()
            {
                // Effectful function value: raw-CPS calling convention.
                let expanded_arity = self.expanded_arity(arity, effects);
                return CExpr::Call(
                    "erlang".to_string(),
                    "make_fun".to_string(),
                    vec![
                        CExpr::Lit(CLit::Atom(erlang_mod)),
                        CExpr::Lit(CLit::Atom(target_name)),
                        CExpr::Lit(CLit::Int(expanded_arity as i64)),
                    ],
                );
            }
            return CExpr::Call(
                "erlang".to_string(),
                "make_fun".to_string(),
                vec![
                    CExpr::Lit(CLit::Atom(erlang_mod)),
                    CExpr::Lit(CLit::Atom(target_name)),
                    CExpr::Lit(CLit::Int(arity as i64)),
                ],
            );
        }

        if arity == 0 {
            CExpr::Apply(Box::new(CExpr::FunRef(name.to_string(), 0)), vec![])
        } else if effects.as_ref().is_some_and(|e| !e.is_empty()) {
            // Effectful function used as a value: emit a raw FunRef of the
            // CPS-expanded arity. The calling convention for effectful function
            // values is raw-CPS — call sites supply (user_args..., handlers...,
            // _ReturnK). An eta-wrapper that captures handlers and supplies an
            // identity continuation would be incompatible with HOFs whose body
            // calls the callback in raw-CPS shape (e.g. `decoder n` lowering to
            // `decoder(n, H, K)` in `Lib.at`).
            let lowered_arity = self.fun_arity(name).unwrap_or(arity);
            CExpr::FunRef(name.to_string(), lowered_arity)
        } else {
            let lowered_arity = self.fun_arity(name).unwrap_or(arity);
            CExpr::FunRef(name.to_string(), lowered_arity)
        }
    }

    fn lower_local_fun_call(
        &self,
        name: &str,
        arity: usize,
        call_args: Vec<CExpr>,
        source_module: Option<&str>,
    ) -> CExpr {
        if let Some(source_module) =
            source_module.filter(|source| *source != self.current_source_module)
        {
            let (erlang_mod, target_name) = self
                .imported_handler_external_target(source_module, name, arity)
                .unwrap_or_else(|| (Self::module_name_to_erlang(source_module), name.to_string()));
            CExpr::Call(erlang_mod, target_name, call_args)
        } else {
            CExpr::Apply(Box::new(CExpr::FunRef(name.to_string(), arity)), call_args)
        }
    }

    /// Emit a function call using the resolution map.
    fn emit_call(
        &self,
        func_name: &str,
        head_node_id: crate::ast::NodeId,
        arity: usize,
        call_args: Vec<CExpr>,
        span: Option<&crate::token::Span>,
        fallback_erlang_module: Option<&str>,
    ) -> CExpr {
        let call = match self.resolved.get(&head_node_id) {
            Some(resolved) => match &resolved.kind {
                super::super::resolve::ResolvedCodegenKind::BeamFunction {
                    erlang_mod: Some(erlang_mod),
                    name,
                    ..
                } => CExpr::Call(erlang_mod.clone(), name.clone(), call_args),
                super::super::resolve::ResolvedCodegenKind::ExternalFunction {
                    erlang_mod,
                    name,
                    target_erlang_mod,
                    target_name,
                    ..
                } if resolved.source_module.as_deref() != Some(&self.current_source_module) => {
                    if self.current_handler_source_module.as_deref()
                        == resolved.source_module.as_deref()
                    {
                        CExpr::Call(target_erlang_mod.clone(), target_name.clone(), call_args)
                    } else {
                        CExpr::Call(erlang_mod.clone(), name.clone(), call_args)
                    }
                }
                super::super::resolve::ResolvedCodegenKind::ExternalFunction { name, .. } => self
                    .lower_local_fun_call(
                        name,
                        arity,
                        call_args,
                        resolved.source_module.as_deref(),
                    ),
                super::super::resolve::ResolvedCodegenKind::BeamFunction { name, .. } => self
                    .lower_local_fun_call(
                        name,
                        arity,
                        call_args,
                        resolved.source_module.as_deref(),
                    ),
                super::super::resolve::ResolvedCodegenKind::Intrinsic { .. } => {
                    // Intrinsics are intercepted by `lower_intrinsic` at the
                    // qualified/bare-call dispatch sites above. This arm exists
                    // so the match is exhaustive.
                    debug_assert!(
                        false,
                        "intrinsic should be intercepted upstream: {}",
                        resolved.canonical_name,
                    );
                    CExpr::Apply(
                        Box::new(CExpr::FunRef(func_name.to_string(), arity)),
                        call_args,
                    )
                }
            },
            _ => {
                if let Some(module) = fallback_erlang_module {
                    CExpr::Call(module.to_string(), func_name.to_string(), call_args)
                } else {
                    // Not in resolution map: local function or variable apply
                    CExpr::Apply(
                        Box::new(CExpr::FunRef(func_name.to_string(), arity)),
                        call_args,
                    )
                }
            }
        };
        self.annotate(call, span)
    }

    pub(super) fn lower_resolved_value_ref(
        &mut self,
        node_id: crate::ast::NodeId,
        resolved: super::super::resolve::ResolvedSymbol,
    ) -> CExpr {
        match resolved.kind {
            super::super::resolve::ResolvedCodegenKind::Intrinsic { arity, .. } => {
                CExpr::FunRef(resolved.name, arity)
            }
            super::super::resolve::ResolvedCodegenKind::ExternalFunction {
                erlang_mod,
                name,
                target_erlang_mod,
                target_name,
                arity,
                ..
            } => {
                if resolved.source_module.as_deref() == Some(&self.current_source_module) {
                    return self.lower_local_fun_ref(
                        &name,
                        arity,
                        None,
                        resolved.source_module.as_deref(),
                    );
                }
                let (erlang_mod, name) = if self.current_handler_source_module.as_deref()
                    == resolved.source_module.as_deref()
                {
                    (target_erlang_mod, target_name)
                } else {
                    (erlang_mod, name)
                };
                if arity == 0 {
                    CExpr::Call(erlang_mod, name, vec![])
                } else {
                    CExpr::Call(
                        "erlang".to_string(),
                        "make_fun".to_string(),
                        vec![
                            CExpr::Lit(CLit::Atom(erlang_mod)),
                            CExpr::Lit(CLit::Atom(name)),
                            CExpr::Lit(CLit::Int(arity as i64)),
                        ],
                    )
                }
            }
            super::super::resolve::ResolvedCodegenKind::BeamFunction {
                erlang_mod: Some(erlang_mod),
                name,
                arity,
                ..
            } => {
                if arity == 0 {
                    CExpr::Call(erlang_mod, name, vec![])
                } else {
                    CExpr::Call(
                        "erlang".to_string(),
                        "make_fun".to_string(),
                        vec![
                            CExpr::Lit(CLit::Atom(erlang_mod)),
                            CExpr::Lit(CLit::Atom(name)),
                            CExpr::Lit(CLit::Int(arity as i64)),
                        ],
                    )
                }
            }
            super::super::resolve::ResolvedCodegenKind::BeamFunction {
                name,
                arity,
                effects,
                ..
            } => {
                let eff = if !effects.is_empty() {
                    Some(effects)
                } else {
                    self.resolved_fun_info(node_id, &name)
                        .map(|f| &f.effects)
                        .cloned()
                        .filter(|e| !e.is_empty())
                };
                self.lower_local_fun_ref(&name, arity, eff, resolved.source_module.as_deref())
            }
        }
    }

    fn effectful_call_return_k_binding(&mut self, return_k: Option<CExpr>) -> (String, CExpr) {
        let rk_var = self.fresh();
        let return_k = return_k.unwrap_or_else(|| {
            let p = self.fresh();
            CExpr::Fun(vec![p.clone()], Box::new(CExpr::Var(p)))
        });
        (rk_var, return_k)
    }

    pub(super) fn wrap_let_bindings(&self, bindings: Vec<(String, CExpr)>, body: CExpr) -> CExpr {
        bindings.into_iter().rev().fold(body, |body, (var, val)| {
            CExpr::Let(var, Box::new(val), Box::new(body))
        })
    }

    /// Look up the resolved type bound by a let pattern. Used when lowering
    /// `let r = fun ... -> ...` so the lambda lowers with its full
    /// effectful arity (`_Evidence`/`_ReturnK`) when its type carries effects.
    /// `CheckResult` finalizes span types through the typechecker substitution,
    /// so downstream lowering can read this map directly.
    pub(super) fn let_pat_resolved_type(&self, pat: &Pat) -> Option<crate::typechecker::Type> {
        let Pat::Var { span, .. } = pat else {
            return None;
        };
        self.check_result.type_at_span.get(span).cloned()
    }

    /// Build the evidence value to pass to a callee that declares the given
    /// effects. Returns a fresh let-binding that produces the evidence
    /// (`(var_name, value_expr)`).
    ///
    /// - Closed-row caller (`current_evidence` is `Some` with `is_open == false`)
    ///   and callee effects are a strict subset: emit a runtime
    ///   `project_evidence` narrowing call.
    /// - Otherwise: forward the caller's evidence directly. When the caller
    ///   has no evidence in scope (pure caller installing first effect via a
    ///   `with` further out, or handler-bound value paths), emit an empty
    ///   tuple as a placeholder so arity matches.
    ///
    /// When `is_row_forward` is true, the callee is row-polymorphic and must
    /// receive the caller's full evidence, including entries not known in the
    /// callee's static effect list.
    pub(super) fn build_call_evidence_with(
        &mut self,
        callee_effects: &[String],
        is_row_forward: bool,
    ) -> (String, CExpr) {
        let var = self.fresh();
        let value = match &self.current_evidence {
            Some(ctx) if is_row_forward => CExpr::Var(ctx.var.clone()),
            Some(ctx) if !ctx.is_open => {
                // Project when the callee asks for fewer effects than the
                // caller's static layout carries. The runtime helper handles
                // the case where no narrowing is required (returns the input
                // tuple unchanged when tags match), but we skip the call when
                // we can prove statically that no narrowing is needed.
                let caller_tags: std::collections::HashSet<&str> =
                    ctx.layout.tags().iter().map(|s| s.as_str()).collect();
                let callee_subset = callee_effects
                    .iter()
                    .all(|t| caller_tags.contains(t.as_str()));
                let narrowing = callee_subset && callee_effects.len() < ctx.layout.tags().len();
                if narrowing {
                    let tags: Vec<&str> = callee_effects.iter().map(|s| s.as_str()).collect();
                    evidence::project_evidence(CExpr::Var(ctx.var.clone()), &tags)
                } else {
                    CExpr::Var(ctx.var.clone())
                }
            }
            Some(ctx) => {
                let tags: Vec<&str> = callee_effects.iter().map(|s| s.as_str()).collect();
                evidence::project_evidence(CExpr::Var(ctx.var.clone()), &tags)
            }
            None => CExpr::Tuple(Vec::new()),
        };
        (var, value)
    }
}
