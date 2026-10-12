use crate::ast::{Expr, ExprKind, NodeId, Pat};
use crate::codegen::cerl::{CArm, CExpr, CLit, CPat};

use super::errors::ErrorKind;
use super::evidence;
use super::util::{
    cerl_call, collect_ctor_call_with_head, collect_effect_call_expr, collect_fun_call,
    collect_qualified_call, core_var, lower_string_to_binary,
};
use super::{Lowerer, QualifiedCallSite, ResolvedCallSite};

/// Runtime module holding the slow path of [`Lowerer::arity_checked_apply`].
const ARITY_RUNTIME_MODULE: &str = "saga_runtime";

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

/// The arity of a lowered callee that is visibly a fun of fixed arity: a
/// local function reference, a fun literal, or `erlang:make_fun/3` on a
/// literal arity (how references to imported functions lower).
fn lowered_fun_arity(callee: &CExpr) -> Option<usize> {
    match callee {
        CExpr::FunRef(_, arity) => Some(*arity),
        CExpr::Fun(params, _) => Some(params.len()),
        CExpr::Call(module, name, args) if module == "erlang" && name == "make_fun" => {
            match args.as_slice() {
                [_, _, CExpr::Lit(CLit::Int(arity))] => usize::try_from(*arity).ok(),
                _ => None,
            }
        }
        _ => None,
    }
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

/// How a CPS call passes evidence and reaches its callee.
#[derive(Clone, Copy, PartialEq, Eq)]
enum CpsApplyMode {
    /// Reframe the caller's evidence into the planned callee ABI and apply
    /// the callee directly. The only mode without tagged closures.
    Planned,
    /// Tagged closures: a known function whose body finds its handlers by
    /// tag (a hoisted dictionary method). Pass the caller's frame unchanged
    /// and call directly.
    DirectTagOnly,
    /// Tagged closures: a function value of unknown representation. Pass the
    /// caller's frame unchanged and dispatch on the tag.
    TaggedValue,
}

struct RuntimeCpsApplySite<'a> {
    abi: crate::codegen::runtime_shape::CallableAbi,
    mode: CpsApplyMode,
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
            .planned_call(app_id)
            .and_then(|info| info.cps_call_abi().cloned());
        let is_effectful = cps_plan.is_some();
        let target_evidence = cps_plan
            .as_ref()
            .and_then(|abi| abi.evidence.as_ref())
            .cloned();
        let total_arity = self
            .resolved_fun_info(head.id, lookup_name)
            .map(|info| info.arity());
        let has_static_call_target = total_arity.is_some()
            || fallback_erlang_module.is_some()
            || self.imported_handler_function_source(lookup_name).is_some()
            || self.current_value_ref(head.id).is_some_and(|value| {
                matches!(
                    value,
                    crate::typechecker::ResolvedValue::Global { lookup_name }
                        if lookup_name.contains('.')
                )
            })
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

            let param_types = self
                .resolved_fun_info(head.id, lookup_name)
                .map(|f| f.expected_arg_types(args.len()));

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
                let (ev_var, ev_ce) = self.build_call_evidence_with(
                    target_evidence
                        .as_ref()
                        .expect("effectful call missing target evidence ABI"),
                );
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
                let (ev_var, ev_ce) = self.build_call_evidence_with(
                    target_evidence
                        .as_ref()
                        .expect("effectful call missing target evidence ABI"),
                );
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

        if self.tagged
            && let Some(abi) = self
                .resolved_fun_info(head.id, lookup_name)
                .map(|info| info.abi.clone())
            && abi.evidence.is_some()
            && args.len() < abi.user_arity
        {
            // Partial application of an effectful function: a tagged closure
            // over the supplied arguments that reframes the evidence it is
            // eventually called with into the callee's declared layout.
            let (arg_vars, bindings) = self.lower_call_args(args);
            let own_repr = self.value_repr_of(app_id);
            let value = self.named_function_value(&abi, abi.user_arity - args.len(), own_repr);
            let mut call_args: Vec<CExpr> = arg_vars.into_iter().map(CExpr::Var).collect();
            call_args.extend(value.call_args.iter().cloned());
            let call = self.emit_call(
                emit_name,
                head.id,
                abi.expanded_arity(),
                call_args,
                call_span,
                fallback_erlang_module,
            );
            return Some(self.wrap_let_bindings(bindings, value.finish(call)));
        }

        if let Some(arity) = total_arity {
            let user_slots = arity.saturating_sub(extras);
            if args.len() < user_slots {
                let remaining_user = user_slots - args.len();
                let param_types = self
                    .resolved_fun_info(head.id, lookup_name)
                    .map(|f| f.expected_arg_types(args.len()));
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
    /// The call shape still comes from `CallEffectInfo::cps_call_abi()`;
    /// callers supply only the callee expression and the narrow argument
    /// lowering mode needed to preserve existing value-boundary behavior.
    fn lower_runtime_cps_apply(&mut self, site: RuntimeCpsApplySite<'_>) -> CExpr {
        let RuntimeCpsApplySite {
            abi,
            mode,
            callee,
            args,
            return_k,
            nested_pure_arg_lowering,
            flat_arg_lowering,
        } = site;
        let evidence_abi = abi.evidence.expect("CPS call plan missing evidence ABI");
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

            let (ev_var, ev_ce) = self.cps_apply_evidence(mode, &evidence_abi);
            let (rk_var, rk_ce) = self.effectful_call_return_k_binding(return_k);

            let outer_call = self.emit_cps_callee_call(callee, mode, &arg_vars, &ev_var, &rk_var);
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
        let (ev_var, ev_ce) = self.cps_apply_evidence(mode, &evidence_abi);
        bindings.push((ev_var.clone(), ev_ce));
        let (rk_var, rk_ce) = self.effectful_call_return_k_binding(return_k);
        bindings.push((rk_var.clone(), rk_ce));
        let call = self.emit_cps_callee_call(callee, mode, &arg_vars, &ev_var, &rk_var);
        self.wrap_let_bindings(bindings, call)
    }

    fn cps_apply_evidence(
        &mut self,
        mode: CpsApplyMode,
        planned: &crate::codegen::runtime_shape::EvidenceAbi,
    ) -> (String, CExpr) {
        match mode {
            CpsApplyMode::Planned => self.build_call_evidence_with(planned),
            CpsApplyMode::DirectTagOnly | CpsApplyMode::TaggedValue => {
                self.current_frame_binding()
            }
        }
    }

    fn emit_cps_callee_call(
        &mut self,
        callee: CpsCallee,
        mode: CpsApplyMode,
        user_arg_vars: &[String],
        ev_var: &str,
        rk_var: &str,
    ) -> CExpr {
        match (mode, callee) {
            (CpsApplyMode::TaggedValue, CpsCallee::Value(func)) => {
                let func_var = self.fresh();
                let call = self.tagged_cps_apply(&func_var, user_arg_vars, ev_var, rk_var);
                CExpr::Let(func_var, Box::new(func), Box::new(call))
            }
            (_, callee) => {
                let mut call_args: Vec<CExpr> =
                    user_arg_vars.iter().cloned().map(CExpr::Var).collect();
                call_args.push(CExpr::Var(ev_var.to_string()));
                call_args.push(CExpr::Var(rk_var.to_string()));
                callee.apply(call_args)
            }
        }
    }

    /// The mode for a call through a function value.
    fn value_call_mode(&self) -> CpsApplyMode {
        if self.tagged {
            CpsApplyMode::TaggedValue
        } else {
            CpsApplyMode::Planned
        }
    }

    /// Tagged closures: lower an application that the known-function paths
    /// did not take: a call through a function value, or a named function
    /// applied to more arguments than it takes. `return_k` is only supplied
    /// for an application classified as effectful.
    pub(super) fn lower_tagged_value_app(
        &mut self,
        expr: &Expr,
        return_k: Option<CExpr>,
    ) -> CExpr {
        let mut head = expr;
        let mut args: Vec<&Expr> = Vec::new();
        while let ExprKind::App { func, arg, .. } = &head.kind {
            args.push(arg.as_ref());
            head = func.as_ref();
        }
        args.reverse();

        if let Some(abi) = self.known_named_callee(head)
            && abi.user_arity < args.len()
        {
            return self.lower_over_applied_named_call(expr, abi.user_arity, &args, return_k);
        }

        if !self.expr_is_effectful_call(expr) {
            if let Some((dict, trait_name, method_index, dm_args)) =
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
                let arg_ces: Vec<CExpr> =
                    dm_args.iter().map(|a| self.lower_expr_value(a)).collect();
                let call = callee.apply(arg_ces);
                return self.apply_return_k_with(return_k, call);
            }
            let call = self.lower_generic_apply(head, &args);
            return self.apply_return_k_with(return_k, call);
        }

        if let Some((dict, trait_name, method_index, dm_args)) =
            super::util::collect_dict_method_call(expr)
            && let Some(call) = self.lower_dict_method_call(
                expr.id,
                dict,
                trait_name,
                method_index,
                &dm_args,
                return_k.clone(),
            )
        {
            return call;
        }
        if let ExprKind::Var { name, .. } = &head.kind {
            if let Some(call) =
                self.try_hof_direct_specialized_value_call(name, &args, return_k.clone())
            {
                return call;
            }
            if self.imported_handler_function_source(name).is_some()
                && let Some(call) =
                    self.lower_effectful_var_call(expr.id, name, &args, return_k.clone())
            {
                return call;
            }
        }
        let plan = self
            .planned_call(expr.id)
            .and_then(|info| info.cps_call_abi().cloned())
            .expect("effectful call is missing its CPS plan");
        let func_ce = self.lower_expr_value(head);
        let func_var = self.fresh();
        let body = self.lower_runtime_cps_apply(RuntimeCpsApplySite {
            abi: plan,
            mode: CpsApplyMode::TaggedValue,
            callee: CpsCallee::Value(CExpr::Var(func_var.clone())),
            args: &args,
            return_k,
            nested_pure_arg_lowering: RuntimeCpsArgLowering::Value,
            flat_arg_lowering: RuntimeCpsArgLowering::EtaReduced,
        });
        CExpr::Let(func_var, Box::new(func_ce), Box::new(body))
    }

    /// Tagged closures: `f a b c` where the named function `f` takes fewer
    /// arguments. The saturated call `f a` runs first (in CPS when `f` is
    /// effectful) and its result, a function value, is applied to the rest
    /// according to the result's own type.
    fn lower_over_applied_named_call(
        &mut self,
        expr: &Expr,
        user_arity: usize,
        args: &[&Expr],
        return_k: Option<CExpr>,
    ) -> CExpr {
        let mut inner = expr;
        for _ in user_arity..args.len() {
            let ExprKind::App { func, .. } = &inner.kind else {
                unreachable!("over-applied call is shorter than its argument list");
            };
            inner = func.as_ref();
        }
        let rest = &args[user_arity..];
        let rest_is_cps = self
            .value_type(inner.id)
            .is_some_and(|ty| super::tagged::consumed_arrows_effectful(&ty, rest.len()));
        let func_var = self.fresh();
        let body = if rest_is_cps {
            self.lower_runtime_cps_apply(RuntimeCpsApplySite {
                abi: crate::codegen::runtime_shape::CallableAbi::cps(
                    rest.len(),
                    super::tagged::tag_only_abi(),
                ),
                mode: CpsApplyMode::TaggedValue,
                callee: CpsCallee::Value(CExpr::Var(func_var.clone())),
                args: rest,
                return_k,
                nested_pure_arg_lowering: RuntimeCpsArgLowering::Value,
                flat_arg_lowering: RuntimeCpsArgLowering::EtaReduced,
            })
        } else {
            let (arg_vars, bindings) = self.lower_call_args(rest);
            let call = Self::arity_checked_apply(&func_var, &arg_vars);
            let call = self.apply_return_k_with(return_k, call);
            self.wrap_let_bindings(bindings, call)
        };
        if self.expr_is_effectful_call(inner) {
            let inner_k = CExpr::Fun(vec![func_var], Box::new(body));
            self.lower_expr_with_call_return_k(inner, Some(inner_k))
        } else {
            let inner_ce = self.lower_expr(inner);
            CExpr::Let(func_var, Box::new(inner_ce), Box::new(body))
        }
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
            .planned_call(app_id)
            .and_then(|info| info.cps_call_abi().cloned())?;
        let callee = if let Some(source_module) = self.imported_handler_function_source(var_name) {
            CpsCallee::Remote {
                erlang_mod: Self::module_name_to_erlang(source_module),
                name: var_name.rsplit('.').next().unwrap_or(var_name).to_string(),
            }
        } else {
            CpsCallee::Value(CExpr::Var(core_var(var_name)))
        };
        let mode = match &callee {
            CpsCallee::Value(_) => self.value_call_mode(),
            CpsCallee::Remote { .. } => CpsApplyMode::Planned,
        };
        Some(self.lower_runtime_cps_apply(RuntimeCpsApplySite {
            abi: plan,
            mode,
            callee,
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
        match self.classify_dict_specialization(
            app_id,
            dict,
            trait_name,
            method_index,
            supplied,
            cps,
        )? {
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
                } if *known_index == method_index => {
                    (dict_constructor.clone(), sub_dicts.is_empty())
                }
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
        } else if let Some(hoist) = self
            .dict_method_hoists
            .get(&(dict_constructor.clone(), method_index))
        {
            // Local hoisted method: direct `FunRef` apply.
            if hoist.is_cps != cps {
                Err(FallbackReason::AbiMismatch)
            } else {
                let arity = supplied + if cps { 2 } else { 0 };
                Ok(CpsCallee::Value(CExpr::FunRef(
                    hoist.fn_name.clone(),
                    arity,
                )))
            }
        } else if self.external_dict_constructor_arity(&dict_constructor) == Some(0)
            && let Some(erlang_mod) = self.imported_dict_erlang_mod(dict)
        {
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
        self.trait_info(trait_name)
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

    fn external_dict_constructor_arity(&self, dict_constructor: &str) -> Option<usize> {
        for compiled in self.ctx.modules.values() {
            for decl in &compiled.elaborated {
                if let crate::ast::Decl::DictConstructor {
                    name, dict_params, ..
                } = decl
                    && name == dict_constructor
                {
                    return Some(dict_params.len());
                }
            }
            for dict in &compiled.codegen_info.trait_impl_dicts {
                if dict.dict_name == dict_constructor {
                    return Some(dict.arity);
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
            .planned_call(app_id)
            .and_then(|info| info.cps_call_abi().cloned())?;

        // Statically-known impl with a hoisted method — call it directly,
        // skipping the dict tuple build and `element/2`: a local `FunRef`
        // (Phase 2) or a cross-module call (Phase 3). Only the callee changes;
        // evidence/return-continuation threading is unchanged.
        if let Some(callee) = self.specialized_dict_method_callee(
            app_id,
            dict,
            trait_name,
            method_index,
            args.len(),
            true,
        ) {
            return Some(self.lower_runtime_cps_apply(RuntimeCpsApplySite {
                abi: plan,
                mode: if self.tagged {
                    CpsApplyMode::DirectTagOnly
                } else {
                    CpsApplyMode::Planned
                },
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
        let tuple_index = self.trait_method_tuple_index(trait_name, method_index);
        let extract = cerl_call(
            "erlang",
            "element",
            vec![
                CExpr::Lit(CLit::Int(tuple_index as i64 + 1)),
                CExpr::Var(dict_var.clone()),
            ],
        );

        let body = self.lower_runtime_cps_apply(RuntimeCpsApplySite {
            abi: plan,
            mode: self.value_call_mode(),
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
    /// When effectful, the lambda is compiled with the contextual
    /// `CallableAbi` recorded by the ABI planner before lowering.
    /// The call site threads evidence + return_k like any
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
            .planned_call(app_id)
            .and_then(|info| info.cps_call_abi().cloned())?;

        let implementation = self
            .planned_function_value_implementation(lambda.id)
            .unwrap_or_else(|| {
                panic!(
                    "internal ABI planning error: missing immediate-lambda ABI for {:?}",
                    lambda.id
                )
            });
        assert_eq!(
            implementation, &plan,
            "internal ABI planning error: immediate-lambda ABI disagrees with its call ABI"
        );
        let func_ce = self.lower_expr(lambda);

        let func_var = self.fresh();
        let body = self.lower_runtime_cps_apply(RuntimeCpsApplySite {
            abi: plan,
            mode: self.value_call_mode(),
            callee: CpsCallee::Value(CExpr::Var(func_var.clone())),
            args,
            return_k,
            nested_pure_arg_lowering: RuntimeCpsArgLowering::Value,
            flat_arg_lowering: RuntimeCpsArgLowering::EtaReduced,
        });
        Some(CExpr::Let(func_var, Box::new(func_ce), Box::new(body)))
    }

    /// Lower a saturated effectful call whose head is a field access yielding a
    /// function value — `s.run n` where `run: Int -> Int needs {Logger}` is a
    /// record field holding an effectful closure. The closure was already built
    /// with the CPS evidence-passing convention at the `RecordCreate` site, so
    /// here we just lower the field access to that closure value and apply it
    /// with `_Evidence`/`_ReturnK` threaded — the body resumes against the
    /// *call-time* evidence supplied here, not creation-time evidence.
    ///
    /// Returns `None` when the call isn't classified as effectful, so the caller
    /// falls through to the regular pure-apply path.
    pub(super) fn lower_field_access_head_call(
        &mut self,
        app_id: NodeId,
        head: &Expr,
        args: &[&Expr],
        return_k: Option<CExpr>,
    ) -> Option<CExpr> {
        let plan = self
            .planned_call(app_id)
            .and_then(|info| info.cps_call_abi().cloned())?;
        let func_ce = self.lower_expr_value(head);
        let func_var = self.fresh();
        let body = self.lower_runtime_cps_apply(RuntimeCpsApplySite {
            abi: plan,
            mode: self.value_call_mode(),
            callee: CpsCallee::Value(CExpr::Var(func_var.clone())),
            args,
            return_k,
            nested_pure_arg_lowering: RuntimeCpsArgLowering::Value,
            flat_arg_lowering: RuntimeCpsArgLowering::EtaReduced,
        });
        Some(CExpr::Let(func_var, Box::new(func_ce), Box::new(body)))
    }

    /// The number of arguments the function value `callee` lowers to takes,
    /// when the compiler knows it without looking at the value: a resolved
    /// top-level function. Everything else (locals, parameters, fields, call
    /// results, dictionary methods) is `None` and must be applied through
    /// [`Self::arity_checked_apply`].
    ///
    /// Dictionary methods are deliberately not treated as known. The trait
    /// signature gives the number of declared parameters, but an impl method
    /// whose body is a lambda (`mk b = fun n -> ...` for `mk : a -> (Int ->
    /// Int)`) is stored in the dictionary with the lambda's parameters
    /// flattened in, so the slot's arity can exceed the trait's.
    fn static_callee_arity(&self, callee: &Expr) -> Option<usize> {
        match &callee.kind {
            ExprKind::Var { name, .. } if self.resolved.contains_key(&callee.id) => self
                .resolved_fun_info(callee.id, name)
                .map(|info| info.arity()),
            _ => None,
        }
    }

    /// Apply the function value `callee` to already-evaluated arguments at a
    /// pure-typed call site: a plain `apply` when the callee's arity is
    /// statically known to equal the argument count, the arity-checked call
    /// otherwise.
    pub(super) fn lower_pure_apply_to_vars(&mut self, callee: &Expr, arg_vars: &[String]) -> CExpr {
        let func_ce = self.lower_expr(callee);
        self.apply_function_value(callee, func_ce, arg_vars)
    }

    /// Like [`Self::lower_pure_apply_to_vars`], for a caller that has already
    /// lowered `callee` to `func_ce`.
    pub(super) fn apply_function_value(
        &mut self,
        callee: &Expr,
        func_ce: CExpr,
        arg_vars: &[String],
    ) -> CExpr {
        if self.callee_has_exact_arity(callee, &func_ce, arg_vars.len()) {
            return CExpr::Apply(
                Box::new(func_ce),
                arg_vars.iter().cloned().map(CExpr::Var).collect(),
            );
        }
        let func_var = self.fresh();
        let call = Self::arity_checked_apply(&func_var, arg_vars);
        CExpr::Let(func_var, Box::new(func_ce), Box::new(call))
    }

    /// Like [`Self::apply_function_value`], for a caller that has already
    /// bound the lowered callee `func_ce` to `func_var`.
    pub(super) fn apply_bound_function_value(
        &self,
        callee: &Expr,
        func_ce: &CExpr,
        func_var: &str,
        arg_vars: &[String],
    ) -> CExpr {
        if self.callee_has_exact_arity(callee, func_ce, arg_vars.len()) {
            CExpr::Apply(
                Box::new(CExpr::Var(func_var.to_string())),
                arg_vars.iter().cloned().map(CExpr::Var).collect(),
            )
        } else {
            Self::arity_checked_apply(func_var, arg_vars)
        }
    }

    /// Whether `callee`, lowered to `func_ce`, is statically known to take
    /// exactly `supplied` arguments.
    fn callee_has_exact_arity(&self, callee: &Expr, func_ce: &CExpr, supplied: usize) -> bool {
        // With tagged closures a named effectful function is not a bare fun
        // as a value, so only the lowered shape proves the arity.
        (!self.tagged && self.static_callee_arity(callee) == Some(supplied))
            || lowered_fun_arity(func_ce) == Some(supplied)
    }

    fn lower_generic_apply(&mut self, callee: &Expr, args: &[&Expr]) -> CExpr {
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

        if self.tagged {
            // The callee is a function value: its arity is only known when
            // it visibly lowers to a bare fun.
            let func_var = self.fresh();
            let func_ce = self.lower_expr(callee);
            let (arg_vars, mut bindings) = self.lower_call_args(args);
            let exact_arity = lowered_fun_arity(&func_ce) == Some(arg_vars.len());
            bindings.insert(0, (func_var.clone(), func_ce));
            let call = if exact_arity {
                CExpr::Apply(
                    Box::new(CExpr::Var(func_var)),
                    arg_vars.into_iter().map(CExpr::Var).collect(),
                )
            } else {
                Self::arity_checked_apply(&func_var, &arg_vars)
            };
            return self.wrap_let_bindings(bindings, call);
        }

        let callee_arity = self
            .static_callee_arity(callee)
            .or_else(|| direct_lambda_arity(callee));

        if let Some(arity) = callee_arity {
            if arity < args.len() {
                let (arg_vars, mut bindings) = self.lower_call_args(args);
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

                // The saturated call returned a function value of unknown
                // arity; the leftover arguments go through the arity check.
                let call = Self::arity_checked_apply(&result_var, &arg_vars[arity..]);
                return self.wrap_let_bindings(bindings, call);
            }

            if arity > args.len() {
                let func_var = self.fresh();
                let func_ce = self.lower_expr(callee);
                let (arg_vars, mut bindings) = self.lower_call_args(args);
                let mut params = Vec::with_capacity(arity - args.len());
                for _ in args.len()..arity {
                    params.push(self.fresh());
                }
                let mut call_args: Vec<CExpr> = arg_vars.into_iter().map(CExpr::Var).collect();
                call_args.extend(params.iter().cloned().map(CExpr::Var));
                bindings.insert(0, (func_var.clone(), func_ce));
                let lambda = CExpr::Fun(
                    params,
                    Box::new(CExpr::Apply(Box::new(CExpr::Var(func_var)), call_args)),
                );
                return self.wrap_let_bindings(bindings, lambda);
            }
        }

        let func_var = self.fresh();
        let func_ce = self.lower_expr(callee);
        let (arg_vars, mut bindings) = self.lower_call_args(args);
        let exact_arity =
            callee_arity.is_some() || lowered_fun_arity(&func_ce) == Some(arg_vars.len());
        bindings.insert(0, (func_var.clone(), func_ce));
        let call = if exact_arity {
            // Saturated call to a callee whose arity is statically known.
            CExpr::Apply(
                Box::new(CExpr::Var(func_var)),
                arg_vars.into_iter().map(CExpr::Var).collect(),
            )
        } else {
            Self::arity_checked_apply(&func_var, &arg_vars)
        };
        self.wrap_let_bindings(bindings, call)
    }

    /// Apply a function value whose arity is not statically known (decision D1
    /// in `docs/planning/sound-function-representation.md`).
    ///
    /// Functions are curried in the type system but compiled uncurried, so a
    /// value of type `a -> b` reaching generic code may be a fun of any arity
    /// (and `b` may itself be a function). The emitted shape is
    ///
    /// ```text
    /// case call 'erlang':'is_function'(F, N) of
    ///   <'true'> when 'true' -> apply F(A1, ..., AN)
    ///   <_> when 'true' -> call 'saga_runtime':'apply_n'(F, [A1, ..., AN])
    /// end
    /// ```
    ///
    /// The exact-arity case costs one guard test and stays a direct `apply`
    /// (so tail calls are preserved). On a mismatch the runtime helper builds
    /// a partial application (too few arguments) or calls with what the fun
    /// takes and applies the result to the rest (too many).
    ///
    /// Both the callee and the arguments must already be bound to variables:
    /// they are referenced from both arms.
    pub(super) fn arity_checked_apply(func_var: &str, arg_vars: &[String]) -> CExpr {
        let args = || arg_vars.iter().cloned().map(CExpr::Var);
        let direct = CExpr::Apply(Box::new(CExpr::Var(func_var.to_string())), args().collect());
        let arg_list = args().rev().fold(CExpr::Nil, |tail, arg| {
            CExpr::Cons(Box::new(arg), Box::new(tail))
        });
        let slow = cerl_call(
            ARITY_RUNTIME_MODULE,
            "apply_n",
            vec![CExpr::Var(func_var.to_string()), arg_list],
        );
        let exact_arity = cerl_call(
            "erlang",
            "is_function",
            vec![
                CExpr::Var(func_var.to_string()),
                CExpr::Lit(CLit::Int(arg_vars.len() as i64)),
            ],
        );
        CExpr::Case(
            Box::new(exact_arity),
            vec![
                CArm {
                    pat: CPat::Lit(CLit::Atom("true".to_string())),
                    guard: None,
                    body: direct,
                },
                CArm {
                    pat: CPat::Wildcard,
                    guard: None,
                    body: slow,
                },
            ],
        )
    }

    pub(super) fn lower_app_expr(&mut self, expr: &Expr) -> CExpr {
        if let Some((head, ctor_name, args)) = collect_ctor_call_with_head(expr) {
            let resolved_ctor = self.resolved_constructor_name_for(head.id, ctor_name);
            let origin = self
                .constructor_origin_module_for(head.id, &resolved_ctor)
                .map(str::to_string);
            return self.lower_ctor_with_origin(&resolved_ctor, args, origin.as_deref());
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
            if let Some(ctor_name) = self.maybe_resolved_constructor_name_for(head.id)
                && self.is_known_constructor(&ctor_name)
            {
                let origin = self
                    .constructor_origin_module_for(head.id, &ctor_name)
                    .map(str::to_string);
                return self.lower_ctor_with_origin(&ctor_name, args, origin.as_deref());
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
                if self.tagged {
                    return self.lower_tagged_value_app(expr, None);
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

        // Imported static handler arms may contain calls to private helpers
        // from their defining module. Those nodes can be freshened during
        // elaboration and therefore absent from the consumer's backend
        // resolution map. Emit a direct call to the recovered origin module.
        if let Some((func_name, head_expr, args)) = fun_call.as_ref()
            && let Some(source_module) = self.imported_handler_function_source(func_name)
        {
            let erlang_module = Self::module_name_to_erlang(source_module);
            let lookup_name = format!("{source_module}.{func_name}");
            if let Some(call) = self.lower_resolved_fun_call(ResolvedCallSite {
                app_id: expr.id,
                lookup_name: &lookup_name,
                emit_name: func_name,
                head: head_expr,
                args,
                return_k: None,
                call_span: Some(&expr.span),
                fallback_erlang_module: Some(&erlang_module),
            }) {
                return call;
            }
        }

        if let Some((var_name, _head, args)) = fun_call.as_ref()
            && let Some(call) = self.try_hof_direct_specialized_value_call(var_name, args, None)
        {
            return call;
        }

        if self.tagged {
            return self.lower_tagged_value_app(expr, None);
        }

        if self.expr_is_effectful_call(expr)
            && let Some((var_name, _, args)) = fun_call.as_ref()
        {
            return self
                .lower_effectful_var_call(expr.id, var_name, args, None)
                .expect("effectful variable call should lower");
        }

        if self.expr_is_effectful_call(expr)
            && let Some((dict, trait_name, method_index, args)) =
                super::util::collect_dict_method_call(expr)
            && let Some(call) =
                self.lower_dict_method_call(expr.id, dict, trait_name, method_index, &args, None)
        {
            return call;
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
        abi: crate::codegen::runtime_shape::CallableAbi,
        source_module: Option<&str>,
    ) -> CExpr {
        let arity = abi.expanded_arity();
        if let Some(source_module) =
            source_module.filter(|source| *source != self.current_source_module)
        {
            let (erlang_mod, target_name) = self
                .imported_handler_external_target(source_module, name, arity)
                .unwrap_or_else(|| (Self::module_name_to_erlang(source_module), name.to_string()));
            if arity == 0 {
                return CExpr::Call(erlang_mod, target_name, vec![]);
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
                } else if let Some(crate::typechecker::ResolvedValue::Global { lookup_name }) =
                    self.current_value_ref(head_node_id)
                    && let Some((module, name)) = lookup_name.rsplit_once('.')
                {
                    self.lower_local_fun_call(name, arity, call_args, Some(module))
                } else if let Some(module) = self.imported_handler_function_source(func_name) {
                    let name = func_name.rsplit('.').next().unwrap_or(func_name);
                    self.lower_local_fun_call(name, arity, call_args, Some(module))
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
        if self.tagged
            && let Some(value) = self.tagged_resolved_value_ref(node_id, &resolved)
        {
            return value;
        }
        match resolved.kind {
            super::super::resolve::ResolvedCodegenKind::Intrinsic { arity, .. } => {
                CExpr::FunRef(resolved.name, arity)
            }
            super::super::resolve::ResolvedCodegenKind::ExternalFunction {
                erlang_mod,
                name,
                target_erlang_mod,
                target_name,
                abi,
                ..
            } => {
                if resolved.source_module.as_deref() == Some(&self.current_source_module) {
                    return self.lower_local_fun_ref(&name, abi, resolved.source_module.as_deref());
                }
                let arity = abi.expanded_arity();
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
                abi,
                ..
            } => {
                let arity = abi.expanded_arity();
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
            super::super::resolve::ResolvedCodegenKind::BeamFunction { name, abi, .. } => {
                let abi = if abi.evidence.is_some() {
                    abi
                } else {
                    self.resolved_fun_info(node_id, &name)
                        .map(|f| f.abi.clone())
                        .unwrap_or(abi)
                };
                self.lower_local_fun_ref(&name, abi, resolved.source_module.as_deref())
            }
        }
    }

    /// Tagged closures: a named effectful function used as a value. Returns
    /// `None` for a pure function, a constant or an intrinsic, which keep
    /// their bare reference.
    fn tagged_resolved_value_ref(
        &mut self,
        node_id: crate::ast::NodeId,
        resolved: &super::super::resolve::ResolvedSymbol,
    ) -> Option<CExpr> {
        use super::super::resolve::ResolvedCodegenKind;
        let (name, abi) = match &resolved.kind {
            ResolvedCodegenKind::Intrinsic { .. } => return None,
            ResolvedCodegenKind::ExternalFunction { name, abi, .. } => (name, abi.clone()),
            ResolvedCodegenKind::BeamFunction {
                erlang_mod: Some(_),
                name,
                abi,
                ..
            } => (name, abi.clone()),
            ResolvedCodegenKind::BeamFunction { name, abi, .. } => {
                let abi = if abi.evidence.is_some() {
                    abi.clone()
                } else {
                    self.resolved_fun_info(node_id, name)
                        .map(|f| f.abi.clone())
                        .unwrap_or_else(|| abi.clone())
                };
                (name, abi)
            }
        };
        if abi.evidence.is_none() || abi.user_arity == 0 {
            return None;
        }
        let own_repr = self.value_repr_of(node_id);
        let value = self.named_function_value(&abi, abi.user_arity, own_repr);
        let call = self.emit_call(
            name,
            node_id,
            abi.expanded_arity(),
            value.call_args.clone(),
            None,
            None,
        );
        Some(value.finish(call))
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
        let module_name = self.current_semantic_module_name();
        if module_name == self.current_source_module {
            self.check_result.type_at_span.get(span).cloned()
        } else {
            self.ctx
                .module_semantics(module_name)
                .and_then(|semantics| semantics.type_at_span.get(span).cloned())
        }
    }

    /// Build the evidence value for a planned callee ABI. Returns a fresh
    /// let-binding that produces the evidence
    /// (`(var_name, value_expr)`).
    ///
    /// The authoritative `EvidenceReframePlan` selects the callee's
    /// prefix and forwards only the row tail described by the target ABI.
    /// When no evidence is in scope, emit an empty tuple placeholder so the
    /// CPS arity remains valid for handler-bound paths.
    ///
    pub(super) fn build_call_evidence_with(
        &mut self,
        target: &crate::codegen::runtime_shape::EvidenceAbi,
    ) -> (String, CExpr) {
        let var = self.fresh();
        let value = match &self.current_evidence {
            // Tagged closures: a callee that finds every handler by tag
            // takes the caller's frame unchanged.
            Some(ctx) if self.tagged && super::tagged::is_tag_only(target) => {
                CExpr::Var(ctx.var.clone())
            }
            Some(ctx) => {
                let plan =
                    crate::codegen::runtime_shape::EvidenceReframePlan::between(&ctx.abi, target);
                evidence::apply_reframe(CExpr::Var(ctx.var.clone()), &plan)
            }
            None => CExpr::Tuple(Vec::new()),
        };
        (var, value)
    }
}
