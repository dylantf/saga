use crate::ast::{Expr, ExprKind, NodeId};
use crate::codegen::cerl::{CArm, CExpr, CLit, CPat};
use crate::codegen::ir::{self, Call, Callee, Conv, FnRef, Val};
use crate::codegen::runtime_shape::{CallableAbi, EvidenceAbi};

use super::Lowerer;
use super::evidence;
use super::util::{cerl_call, lower_string_to_binary};

/// Runtime module holding the slow path of [`Lowerer::arity_checked_apply`].
const ARITY_RUNTIME_MODULE: &str = "saga_runtime";

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

impl<'a> Lowerer<'a> {
    /// Lower an application: build it, then lower the node. With `k`, its
    /// value is passed to that continuation; a CPS call or a perform takes
    /// `k` as its own.
    pub(super) fn lower_app(&mut self, expr: &Expr, k: Option<CExpr>) -> CExpr {
        let built = self.build_app(expr);
        self.lower_built(&built, k)
    }

    fn lower_built(&mut self, built: &ir::Expr<'_>, k: Option<CExpr>) -> CExpr {
        let value = match built {
            ir::Expr::Call(call) => return self.lower_call(call, k),
            ir::Expr::Perform { op, args } => {
                let ExprKind::EffectCall {
                    name, qualifier, ..
                } = &op.kind
                else {
                    unreachable!("a perform is built from an operation");
                };
                let args: Vec<Expr> = args.iter().map(|arg| (*arg).clone()).collect();
                return self.lower_effect_call(op.id, name, qualifier.as_deref(), &args, k);
            }
            ir::Expr::Val(val) => self.lower_val(val),
            ir::Expr::Partial {
                target,
                args,
                repr,
                span,
            } => {
                let (arg_vars, bindings) = self.lower_call_args(args);
                let remaining = target.abi.user_arity - args.len();
                let value = self.named_function_value(&target.abi, remaining, *repr);
                let mut call_args: Vec<CExpr> = arg_vars.into_iter().map(CExpr::Var).collect();
                call_args.extend(value.call_args.iter().cloned());
                let call = self.annotate(Self::call_fn(target, call_args), Some(span));
                self.wrap_let_bindings(bindings, value.finish(call))
            }
            ir::Expr::Intrinsic { id, args } => self.lower_intrinsic(*id, args),
            ir::Expr::Raise {
                kind,
                message,
                span,
            } => {
                let v = self.fresh();
                let message = match message {
                    Some(message) => self.lower_val(message),
                    None => lower_string_to_binary("not implemented"),
                };
                let error = self.make_error(*kind, CExpr::Var(v.clone()), Some(span));
                CExpr::Let(v, Box::new(message), Box::new(error))
            }
        };
        self.apply_return_k_with(k, value)
    }

    /// The one lowering of a call. A direct call is evaluated and its value
    /// passed to `k`; a CPS call takes evidence and `k` (the identity when
    /// there is none).
    fn lower_call(&mut self, call: &Call<'_>, k: Option<CExpr>) -> CExpr {
        let args = &call.args;
        match (&call.callee, call.conv()) {
            (Callee::Fn(target), Conv::Direct) => {
                let (arg_vars, bindings) = self.lower_call_args(args);
                let call_args = arg_vars.into_iter().map(CExpr::Var).collect();
                let direct = self.annotate(Self::call_fn(target, call_args), call.span.as_ref());
                let value = self.wrap_let_bindings(bindings, direct);
                self.apply_return_k_with(k, value)
            }
            (Callee::Fn(target), Conv::Cps(evidence)) => {
                if let Some(fast) = self.try_call_fast_paths(call, &k) {
                    return fast;
                }
                let (vars, bindings) = self.cps_call_args(args, Some(evidence), k);
                let call_args = vars.into_iter().map(CExpr::Var).collect();
                let direct = self.annotate(Self::call_fn(target, call_args), call.span.as_ref());
                self.wrap_let_bindings(bindings, direct)
            }
            // A hoisted method of a statically known impl finds its
            // handlers by tag: it takes the caller's frame unchanged.
            (
                Callee::DictMethod {
                    known_impl: Some(method),
                    ..
                },
                Conv::Cps(_),
            ) => {
                let (vars, bindings) = self.cps_call_args(args, None, k);
                let call_args = vars.into_iter().map(CExpr::Var).collect();
                self.wrap_let_bindings(bindings, Self::call_fn(method, call_args))
            }
            (
                Callee::DictMethod {
                    known_impl: Some(method),
                    ..
                },
                Conv::Direct,
            ) => {
                let call_args = args.iter().map(|arg| self.lower_val(arg)).collect();
                self.apply_return_k_with(k, Self::call_fn(method, call_args))
            }
            (
                Callee::DictMethod {
                    dict,
                    slot,
                    known_impl: None,
                },
                Conv::Cps(_),
            ) => {
                let dict_var = self.fresh();
                let dict_ce = self.lower_val(dict);
                let method_var = self.fresh();
                let index = CExpr::Lit(CLit::Int(*slot as i64));
                let method = cerl_call(
                    "erlang",
                    "element",
                    vec![index, CExpr::Var(dict_var.clone())],
                );
                let body = self.tagged_call(&method_var, args, k);
                let body = CExpr::Let(method_var, Box::new(method), Box::new(body));
                CExpr::Let(dict_var, Box::new(dict_ce), Box::new(body))
            }
            (Callee::DictMethod { .. }, Conv::Direct) => {
                unreachable!("a direct method call without a known impl is a call of a value")
            }
            (Callee::Value(func), Conv::Direct) => {
                let value = match self.try_hof_value_call(func, args, None) {
                    Some(fast) => fast,
                    None => {
                        let func_var = self.fresh();
                        let func_ce = self.lower_val(func);
                        self.apply_lowered(func_var, func_ce, args)
                    }
                };
                self.apply_return_k_with(k, value)
            }
            (Callee::Value(func), Conv::Cps(_)) => {
                if let Some(fast) = self.try_hof_value_call(func, args, k.clone()) {
                    return fast;
                }
                let func_ce = self.lower_val(func);
                let func_var = self.fresh();
                let body = self.tagged_call(&func_var, args, k);
                CExpr::Let(func_var, Box::new(func_ce), Box::new(body))
            }
            (Callee::Result(first), conv) => {
                let first_cps = match first.as_ref() {
                    ir::Expr::Call(first) => matches!(first.conv(), Conv::Cps(_)),
                    _ => false,
                };
                // `k` belongs to the pair when either half is a CPS call;
                // otherwise the pair is a value, which `k` is applied to.
                let (inner_k, outer_k) = match conv {
                    Conv::Direct if !first_cps => (None, k),
                    _ => (k, None),
                };
                let func_var = self.fresh();
                let body = match conv {
                    Conv::Cps(_) => self.tagged_call(&func_var, args, inner_k),
                    Conv::Direct => {
                        let (arg_vars, bindings) = self.lower_call_args(args);
                        let call = Self::arity_checked_apply(&func_var, &arg_vars);
                        let call = self.apply_return_k_with(inner_k, call);
                        self.wrap_let_bindings(bindings, call)
                    }
                };
                // The rest is lowered first: it is the continuation of a
                // first half that is a CPS call.
                let pair = if first_cps {
                    let first_k = CExpr::Fun(vec![func_var], Box::new(body));
                    self.lower_built(first, Some(first_k))
                } else {
                    let first_ce = self.lower_built(first, None);
                    CExpr::Let(func_var, Box::new(first_ce), Box::new(body))
                };
                self.apply_return_k_with(outer_k, pair)
            }
        }
    }

    /// The fast paths for a saturated CPS call of a known function. They
    /// still match on the AST.
    fn try_call_fast_paths(&mut self, call: &Call<'_>, k: &Option<CExpr>) -> Option<CExpr> {
        let (lookup, head) = call.site.as_ref()?;
        let args = Self::ast_args(&call.args);
        self.try_hof_direct_specialized_call(lookup, head, &args, k.clone())
            .or_else(|| self.try_inline_static_helper_call(lookup, head, &args, k.clone()))
            .or_else(|| {
                self.try_imported_static_helper_variant_call(lookup, head, &args, k.clone())
            })
    }

    /// The fast path for a call through a variable bound to a function that
    /// has a direct-callback variant. It still matches on the AST.
    fn try_hof_value_call(
        &mut self,
        func: &Val<'_>,
        args: &[Val<'_>],
        k: Option<CExpr>,
    ) -> Option<CExpr> {
        let Val::Ast(Expr {
            kind: ExprKind::Var { name },
            ..
        }) = func
        else {
            return None;
        };
        self.try_hof_direct_specialized_value_call(name, &Self::ast_args(args), k)
    }

    /// The argument expressions of a call, for the fast paths.
    fn ast_args<'e>(args: &[Val<'e>]) -> Vec<&'e Expr> {
        args.iter()
            .map(|arg| match arg {
                Val::Ast(expr) => *expr,
                built => unreachable!("fast paths match on the AST, not on {built:?}"),
            })
            .collect()
    }

    /// The arguments of a CPS call, each bound to a variable: the user
    /// arguments, the evidence, the return continuation (the identity when
    /// there is no `k`). The evidence is the caller's frame reframed into
    /// `evidence`, or, with `None`, passed unchanged (the callee finds its
    /// handlers by tag).
    fn cps_call_args(
        &mut self,
        args: &[Val<'_>],
        evidence: Option<&EvidenceAbi>,
        k: Option<CExpr>,
    ) -> (Vec<String>, Vec<(String, CExpr)>) {
        let (mut vars, mut bindings) = self.lower_call_args(args);
        let (ev_var, ev_ce) = match evidence {
            Some(evidence) => self.build_call_evidence_with(evidence),
            None => self.current_frame_binding(),
        };
        let rk_var = self.fresh();
        let rk_ce = k.unwrap_or_else(|| {
            let p = self.fresh();
            CExpr::Fun(vec![p.clone()], Box::new(CExpr::Var(p)))
        });
        bindings.extend([(ev_var.clone(), ev_ce), (rk_var.clone(), rk_ce)]);
        vars.extend([ev_var, rk_var]);
        (vars, bindings)
    }

    /// A CPS call of the function value bound to `func_var`, whose
    /// representation is not known: dispatch on the tag.
    fn tagged_call(&mut self, func_var: &str, args: &[Val<'_>], k: Option<CExpr>) -> CExpr {
        let (vars, bindings) = self.cps_call_args(args, None, k);
        let (user, rest) = vars.split_at(args.len());
        let func = self.fresh();
        let call = self.tagged_cps_apply(&func, user, &rest[0], &rest[1]);
        let func_ce = CExpr::Var(func_var.to_string());
        self.wrap_let_bindings(
            bindings,
            CExpr::Let(func, Box::new(func_ce), Box::new(call)),
        )
    }

    /// Apply the function value `func_ce` (to be bound to `func_var`) at a
    /// pure type: a plain `apply` when it visibly lowers to a fun of the
    /// arguments' number, the arity-checked call otherwise.
    pub(super) fn apply_lowered(
        &mut self,
        func_var: String,
        func_ce: CExpr,
        args: &[Val<'_>],
    ) -> CExpr {
        let (arg_vars, mut bindings) = self.lower_call_args(args);
        let call = if lowered_fun_arity(&func_ce) == Some(arg_vars.len()) {
            let args = arg_vars.into_iter().map(CExpr::Var).collect();
            CExpr::Apply(Box::new(CExpr::Var(func_var.clone())), args)
        } else {
            Self::arity_checked_apply(&func_var, &arg_vars)
        };
        bindings.insert(0, (func_var, func_ce));
        self.wrap_let_bindings(bindings, call)
    }

    /// If the trait method call at `app_id` dispatches on a statically-known
    /// impl whose method is hoisted to a top-level function, that function —
    /// local (Phase 2) or of another module (Phase 3) — with the call's
    /// convention `abi`; the specialization is recorded. `None` (and the
    /// fallback reason is recorded) when the site stays on the normal
    /// `element/2` dispatch.
    pub(super) fn specialized_dict_method(
        &mut self,
        app_id: NodeId,
        dict: &Expr,
        trait_name: &str,
        method_index: usize,
        abi: CallableAbi,
    ) -> Option<FnRef> {
        match self.classify_dict_specialization(app_id, dict, trait_name, method_index, abi)? {
            Ok(method) => {
                self.trait_spec_stats.record_specialized(app_id);
                Some(method)
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
        abi: CallableAbi,
    ) -> Option<Result<FnRef, super::trait_spec_stats::FallbackReason>> {
        use super::trait_spec_stats::FallbackReason;
        let (supplied, cps) = (abi.user_arity, abi.evidence.is_some());

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
                Ok(FnRef {
                    module: None,
                    name: hoist.fn_name.clone(),
                    abi,
                })
            }
        } else if self.external_dict_constructor_arity(&dict_constructor) == Some(0)
            && let Some(erlang_mod) = self.imported_dict_erlang_mod(dict)
        {
            // Imported hoisted method: direct cross-module call. Every module
            // hoists all its nullary dict methods with this deterministic name,
            // and the call's CPS shape derives from the same impl-effect data as
            // the producer's, so the remote function's arity matches.
            let name = format!("__saga_dictmethod_{dict_constructor}_{method_index}");
            Ok(FnRef {
                module: Some(erlang_mod),
                name,
                abi,
            })
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

    /// Apply the already-lowered function value `func_ce` to
    /// already-evaluated arguments at a pure-typed call site: a plain `apply`
    /// when its arity is statically known to equal the argument count, the
    /// arity-checked call otherwise.
    pub(super) fn apply_function_value(&mut self, func_ce: CExpr, arg_vars: &[String]) -> CExpr {
        if Self::callee_has_exact_arity(&func_ce, arg_vars.len()) {
            return CExpr::Apply(
                Box::new(func_ce),
                arg_vars.iter().cloned().map(CExpr::Var).collect(),
            );
        }
        let func_var = self.fresh();
        let call = Self::arity_checked_apply(&func_var, arg_vars);
        CExpr::Let(func_var, Box::new(func_ce), Box::new(call))
    }

    /// Whether `callee`, lowered to `func_ce`, is statically known to take
    /// exactly `supplied` arguments.
    fn callee_has_exact_arity(func_ce: &CExpr, supplied: usize) -> bool {
        // A named effectful function is not a bare fun as a value, so only
        // the lowered shape proves the arity.
        lowered_fun_arity(func_ce) == Some(supplied)
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

    pub(super) fn wrap_let_bindings(&self, bindings: Vec<(String, CExpr)>, body: CExpr) -> CExpr {
        bindings.into_iter().rev().fold(body, |body, (var, val)| {
            CExpr::Let(var, Box::new(val), Box::new(body))
        })
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
            // A callee that finds every handler by tag takes the caller's
            // frame unchanged.
            Some(ctx) if super::tagged::is_tag_only(target) => CExpr::Var(ctx.var.clone()),
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
