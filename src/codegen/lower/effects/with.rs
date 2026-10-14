use super::*;
use crate::ast::{Annotated, Expr, ExprKind, Handler, HandlerArm, Pat, Stmt};
use crate::codegen::cerl::{CArm, CExpr, CLit, CPat};
use crate::codegen::lower::*;
use std::collections::{HashMap, HashSet};

impl<'a> Lowerer<'a> {
    /// Lower a `with` expression: `expr with handler`.
    ///
    /// Builds handler function(s) from the handler definition and passes them
    /// as extra parameters to the effectful computation.
    pub(crate) fn lower_with_inherited_return_k(
        &mut self,
        expr: &Expr,
        handler: &Handler,
        inherited_return_k: Option<CExpr>,
    ) -> CExpr {
        if let Some(rewritten) = self.lower_with_chain_after_local_handler_bindings(
            expr,
            handler,
            inherited_return_k.clone(),
        ) {
            return rewritten;
        }

        // One lowering, `bind(handled, k)` (see "The Continuation of a
        // `with`" in docs/effect-implementation.md): the handled computation
        // returns to the `with`, the operations of the inherited frame are
        // lifted so that they capture `k` as a meta continuation, and an arm
        // that does not resume throws the abort of this `with`, which is
        // caught where it delimits the computation. It is fused when every
        // arm only resumes in tail position (`chains`: `k` goes into the
        // handled computation, and nothing is lifted or caught).
        let general = !self.with_handler_chains_continuation(handler);
        let fused_k = if general {
            None
        } else {
            inherited_return_k.clone()
        };
        let abort_ref = general.then(|| self.fresh());

        let normalized = self.normalize_with_handler(handler);
        let (inline_arms, explicit_return_clause) = match &normalized {
            WithHandlerLayer::Named { .. } => (Vec::new(), None),
            WithHandlerLayer::Inline {
                arms,
                return_clause,
            } => (arms.clone(), return_clause.clone()),
        };

        let mut condition_bindings: Vec<(String, CExpr)> = Vec::new();
        let named_item = match &normalized {
            WithHandlerLayer::Named { reference } => {
                self.pre_register_local_with_binding(expr, &reference.name);
                let mut item = self.resolve_named_handler_item(reference);
                if let NamedHandlerItem::Conditional {
                    cond_var, cond_ce, ..
                } = &item
                {
                    condition_bindings.push((cond_var.clone(), cond_ce.as_ref().clone()));
                }
                // A handler value is a function of the abort reference of the
                // `with` that installs it, which its arms throw with.
                if let (NamedHandlerItem::Dynamic { tuple_var, .. }, Some(abort_ref)) =
                    (&mut item, &abort_ref)
                {
                    let installed = self.fresh();
                    condition_bindings.push((
                        installed.clone(),
                        CExpr::Apply(
                            Box::new(CExpr::Var(tuple_var.clone())),
                            vec![CExpr::Var(abort_ref.clone())],
                        ),
                    ));
                    *tuple_var = installed;
                }
                Some(item)
            }
            WithHandlerLayer::Inline { .. } => None,
        };

        let (handled_effects, inline_arms_by_op) = if let Some(item) = &named_item {
            (item.effects().to_vec(), HashMap::new())
        } else {
            let mut handled_effects = Vec::new();
            let mut inline_arms_by_op: HashMap<String, Vec<HandlerArm>> = HashMap::new();
            for arm in &inline_arms {
                if let Some(effect) = self.effect_for_handler_arm(arm, None) {
                    if !handled_effects.contains(&effect) {
                        handled_effects.push(effect.clone());
                    }
                    if arm.qualifier.is_some() {
                        inline_arms_by_op
                            .entry(format!("{}.{}", effect, arm.op_name))
                            .or_default()
                            .push(arm.clone());
                    } else {
                        inline_arms_by_op
                            .entry(arm.op_name.clone())
                            .or_default()
                            .push(arm.clone());
                    }
                }
            }
            (handled_effects, inline_arms_by_op)
        };

        let handler_ops = self.effect_handler_ops(&handled_effects);

        // For each op, build a handler function and bind it.
        // Two passes: first allocate fresh closure binding names, then build
        // the handler functions. Handler-arm bodies access sibling handlers
        // through the evidence vector that this `with` installs, not via
        // direct names; the per-binding name is just the closure's let-bound
        // var (so it shows up in the emitted Core Erlang and gets reachability-
        // pruned when unused).
        let saved_no_resume_ops = self.no_resume_ops.clone();
        let saved_direct_ops = self.direct_ops.clone();
        let saved_static_tail_resume_ops = self.static_tail_resume_ops.clone();

        // Pass 1: allocate handler-binding names and pick a per-op plan.
        let mut op_vars: Vec<(String, String, String, OpHandlerPlan)> = Vec::new();
        for (eff, op) in &handler_ops {
            let var_name = self.fresh_handler_binding_name(eff, op);
            let key = format!("{}.{}", eff, op);
            let plan = match &named_item {
                Some(item) => self.plan_named_op_handler(eff, op, item),
                None => self.plan_inline_op_handler(eff, op, &inline_arms_by_op),
            };
            match &plan {
                OpHandlerPlan::Inline { arms }
                    if arms.iter().all(|arm| !arm.body.contains_resume()) =>
                {
                    self.no_resume_ops.insert(key.clone());
                }
                OpHandlerPlan::BeamNative { handler_canonical } => {
                    if self.use_direct_native_fast_path(handler_canonical) {
                        self.direct_ops
                            .insert(key.clone(), handler_canonical.clone());
                    }
                }
                OpHandlerPlan::Static {
                    arm,
                    handler_canonical,
                    ..
                } => {
                    if !arm.body.contains_resume() {
                        self.no_resume_ops.insert(key.clone());
                    }
                    if self.is_beam_native_handler_canonical(handler_canonical)
                        && self.use_direct_native_fast_path(handler_canonical)
                    {
                        self.direct_ops
                            .insert(key.clone(), handler_canonical.clone());
                    }
                }
                _ => {}
            }
            let handler_has_return_clause = explicit_return_clause.is_some()
                || named_item
                    .as_ref()
                    .is_some_and(NamedHandlerItem::has_return_clause);
            if !handler_has_return_clause
                && let Some(static_plan) = self.static_tail_resume_plan_for_op_handler(&plan, eff)
            {
                self.static_tail_resume_ops.insert(key.clone(), static_plan);
            }
            op_vars.push((eff.clone(), op.clone(), var_name, plan));
        }

        // Build the new evidence vector for this `with` block. Group `op_vars`
        // by canonical effect tag, build a `{EffectAtom, OpTuple}` entry per
        // effect, and chain `insert_canonical` calls onto the inherited
        // evidence (an empty tuple when there is no enclosing evidence in
        // scope). Each op closure inside the entry refers to the corresponding
        // handler binding by name (the binding itself is emitted by
        // `attach_scoped_handler_bindings` below). The new evidence variable
        // is published to `current_evidence` for the body lowering and for any
        // call sites inside the body that need to thread evidence.
        //
        // Op tuples must be sorted alphabetically by op name (the canonical
        // shape — see `evidence::build_evidence_entry`); `op_vars` is built
        // from `handler_ops`, which is already op-sorted.
        let saved_evidence = self.current_evidence.clone();
        // The lifted frame has the inherited one's tags and layout. The
        // handled computation and the arms both see it.
        let lifted_evidence = saved_evidence
            .as_ref()
            .zip(abort_ref.as_ref())
            .map(|(frame, r)| {
                let lifted =
                    evidence::lift_evidence(CExpr::Var(frame.var.clone()), CExpr::Var(r.clone()));
                (EvidenceFrame::new(self.fresh(), frame.abi.clone()), lifted)
            });
        let inherited_evidence = match &lifted_evidence {
            Some((frame, _)) => Some(frame.clone()),
            None => saved_evidence.clone(),
        };
        let (new_evidence_var, base_evidence, install_steps) = {
            let mut effect_to_ops: std::collections::BTreeMap<String, Vec<&str>> =
                std::collections::BTreeMap::new();
            let mut effect_to_vars: std::collections::HashMap<(String, String), String> =
                std::collections::HashMap::new();
            for (eff, op, var_name, _plan) in &op_vars {
                effect_to_ops
                    .entry(eff.clone())
                    .or_default()
                    .push(op.as_str());
                effect_to_vars.insert((eff.clone(), op.clone()), var_name.clone());
            }
            // Inherit the outer evidence by var-name. The dominance invariant
            // — that `saved_evidence.var` is in scope at every site where the
            // new evidence binding is placed — is preserved upstream: dynamic
            // handler factories whose closures come from lets inside this
            // wrapped block are rewritten ahead of lowering (see the named-
            // chain rewrite earlier in this file) so the new evidence is only
            // installed for the suffix where the dynamic handler tuples are
            // bound. Non-dynamic withs install handlers that depend only on
            // outer-scope values, so their evidence binding can safely live
            // at the with boundary.
            let base = match &inherited_evidence {
                Some(ctx) => CExpr::Var(ctx.var.clone()),
                None => CExpr::Tuple(Vec::new()),
            };
            let mut steps = Vec::new();
            let mut new_abi = inherited_evidence
                .as_ref()
                .map(|frame| frame.abi.clone())
                .unwrap_or_default();
            for (eff, mut ops) in effect_to_ops {
                ops.sort();
                ops.dedup();
                let op_closures: Vec<CExpr> = ops
                    .iter()
                    .map(|op| {
                        let var = effect_to_vars
                            .get(&(eff.clone(), (*op).to_string()))
                            .expect("internal error: missing handler var for evidence entry");
                        CExpr::Var(var.clone())
                    })
                    .collect();
                let install = new_abi.plan_install(eff.clone());
                new_abi = install.target.clone();
                steps.push((eff, op_closures, install));
            }
            let new_var = self.fresh();
            // Layout mirrors the value we built: union of the inherited
            // tags (when we kept the outer var) and the effects installed
            // here. The is_open flag also propagates from the inherited
            // context — a row-polymorphic outer caller's evidence may carry
            // additional unknown effects beyond the static layout.
            self.current_evidence = Some(crate::codegen::lower::EvidenceFrame::new(
                new_var.clone(),
                new_abi,
            ));
            (new_var, base, steps)
        };

        // Lower the inner expression once handler params are in scope.
        //
        // A statically known `return` clause takes the `with`'s outer
        // continuation as the continuation of its own body, so an effect it
        // performs captures the rest of the enclosing computation. A clause
        // only known at runtime is a plain function: its value is passed to
        // the outer continuation afterwards (`compose_return_k`).
        let static_return_clause = match (&explicit_return_clause, &named_item) {
            (Some(ret), _) => Some((ret.clone(), None)),
            (None, Some(NamedHandlerItem::Static { info, .. })) => info
                .return_clause
                .clone()
                .map(|ret| (ret, info.source_module.clone())),
            _ => None,
        };
        let (return_k_lambda, outer_return_k) = match (static_return_clause, &named_item) {
            (Some((ret, source_module)), _) => (
                Some(self.build_return_lambda(&ret, source_module.as_deref(), fused_k.clone())),
                None,
            ),
            (None, Some(item)) => (self.named_return_lambda(item), fused_k.clone()),
            (None, None) => (None, fused_k.clone()),
        };
        let result = self.lower_handled_inner_expr(expr, return_k_lambda, outer_return_k);
        // The entry of the `with` delimits its handled computation: an abort
        // thrown by one of its arms becomes the value. With no continuation
        // the value of the `with` is returned: the continuation is the
        // identity. Nothing suspends unless a frame was lifted.
        let result = match &abort_ref {
            Some(r) => {
                let vars = [
                    self.fresh(),
                    self.fresh(),
                    self.fresh(),
                    self.fresh(),
                    self.fresh(),
                ];
                evidence::catch_own_abort(result, r, vars)
            }
            None => result,
        };
        let result = match &inherited_return_k {
            Some(k) if general => {
                let vars = [self.fresh(), self.fresh()];
                match k {
                    CExpr::Var(_) => evidence::meta_bind_inline(result, k.clone(), vars),
                    _ => evidence::meta_bind(result, k.clone()),
                }
            }
            None if general && lifted_evidence.is_some() => {
                evidence::meta_bind(result, self.identity_return_lambda())
            }
            _ => result,
        };

        // Handler arm bodies must see the *outer* evidence, not the new one
        // we just installed for the body of `with`. A re-perform of the same
        // op (`fail e = fail! ...`) inside an arm reaches the outer handler
        // stack; if the arm body's effectful calls picked up the new evidence,
        // they'd recurse into the just-installed entry instead.
        let saved_evidence_for_arms =
            std::mem::replace(&mut self.current_evidence, inherited_evidence.clone());

        // Pass 2: build ALL handler functions unconditionally.
        // We'll prune unreachable ones after lowering the body.
        //
        // Re-performing the same op inside an arm body (`fail e = fail! ...`,
        // the "rethrow"/middleware pattern) must reach the outer handler
        // stack, not recurse into this arm. That's already enforced by
        // restoring `current_evidence` to `saved_evidence` for arm-body
        // lowering above — `evidence_op_lookup` reads the outer layout, so
        // op calls inside arms naturally hit the outer handler entry.
        //
        // Thread the with's outer K into abort-handler-arm bodies so their
        // terminal value flows through the host context's CPS chain.
        let saved_handler_inherited_k =
            std::mem::replace(&mut self.current_handler_inherited_k, fused_k);
        let saved_abort_ref = std::mem::replace(&mut self.current_abort_ref, abort_ref.clone());
        let mut handler_bindings: Vec<(String, CExpr)> = Vec::new();
        for (eff, op, var_name, plan) in &op_vars {
            let binding = match plan {
                OpHandlerPlan::Inline { arms } => self.build_inline_op_handler_fun(arms),
                OpHandlerPlan::Static {
                    handler_canonical, ..
                } if self.is_beam_native_handler_canonical(handler_canonical) => {
                    self.build_beam_native_op_fun(op, handler_canonical)
                }
                OpHandlerPlan::Static {
                    arm,
                    source_module,
                    effect_name,
                    captures,
                    ..
                } => self.build_op_handler_fun_for_effect(
                    arm,
                    source_module.as_deref(),
                    captures,
                    Some(effect_name),
                ),
                OpHandlerPlan::Conditional {
                    cond_var,
                    then_arm,
                    then_source,
                    else_arm,
                    else_source,
                } => self.build_conditional_handler_fun(
                    eff,
                    cond_var,
                    then_arm.as_ref(),
                    then_source.as_deref(),
                    else_arm.as_ref(),
                    else_source.as_deref(),
                ),
                OpHandlerPlan::Dynamic { element_expr } => element_expr.clone(),
                OpHandlerPlan::BeamNative { handler_canonical } => {
                    self.build_beam_native_op_fun(op, handler_canonical)
                }
                OpHandlerPlan::Passthrough => self.build_passthrough_handler_fun(),
            };
            handler_bindings.push((var_name.clone(), binding));
        }
        self.current_handler_inherited_k = saved_handler_inherited_k;
        self.current_abort_ref = saved_abort_ref;

        // An entry whose arms can run where the operation is performed, in
        // any `with` inside this one, without lifting: none leaves a frame
        // (each resumes at most once, in tail position, and has no
        // `finally`) and none can suspend (none uses the frame, so none
        // performs anything). Every other entry is marked to be lifted.
        let frame_vars: HashSet<String> = [&saved_evidence, &inherited_evidence]
            .into_iter()
            .flatten()
            .map(|frame| frame.var.clone())
            .collect();
        // An arm of that shape that does perform, through its frame, is
        // direct when every entry of the frame is (`entry/3`, at runtime).
        let mut entry_kinds: HashMap<String, EntryKind> = HashMap::new();
        for ((eff, _op, _var, plan), (_, binding)) in op_vars.iter().zip(&handler_bindings) {
            let mut refs = HashSet::new();
            Self::collect_var_refs(binding, &mut refs);
            let kind = if !op_plan_is_direct(plan) {
                EntryKind::Lifted
            } else if refs.is_disjoint(&frame_vars) {
                EntryKind::Direct
            } else {
                EntryKind::DirectIfFrameIs
            };
            let slot = entry_kinds.entry(eff.clone()).or_insert(EntryKind::Direct);
            *slot = (*slot).max(kind);
        }
        let arm_frame = inherited_evidence.as_ref().map(|frame| frame.var.clone());
        let mut acc = base_evidence;
        for (eff, op_closures, install) in install_steps {
            let entry = match (entry_kinds.get(&eff).copied(), &arm_frame) {
                (Some(EntryKind::Lifted), _) => {
                    evidence::build_evidence_entry(&eff, op_closures, true)
                }
                (Some(EntryKind::DirectIfFrameIs), Some(frame)) => {
                    evidence::entry_for_frame(&eff, op_closures, CExpr::Var(frame.clone()))
                }
                _ => evidence::build_evidence_entry(&eff, op_closures, false),
            };
            acc = evidence::apply_install(acc, entry, &install);
        }
        let evidence_binding = (new_evidence_var.clone(), acc);

        self.no_resume_ops = saved_no_resume_ops;
        self.direct_ops = saved_direct_ops;
        self.static_tail_resume_ops = saved_static_tail_resume_ops;
        // Restore the body-scope evidence we replaced during pass 2 (it is
        // unused after this point but kept symmetrical with the save). Then
        // restore the caller's evidence as the function exits the `with`.
        let _ = saved_evidence_for_arms;
        self.current_evidence = saved_evidence;

        // Post-hoc reachability: scan the lowered body for _Handle_* references,
        // then transitively close through handler binding values.
        let mut needed: HashSet<String> = HashSet::new();
        result.collect_handle_refs(&mut needed);
        // Also seed reachability with any free-variable references to the new
        // evidence variable, so that the evidence binding (and transitively
        // its handler-var dependencies) is retained when the body forwards
        // evidence at call sites.
        let (ev_var, _) = &evidence_binding;
        let mut body_free: HashSet<String> = HashSet::new();
        Self::collect_var_refs(&result, &mut body_free);
        if body_free.contains(ev_var) {
            needed.insert(ev_var.clone());
            // The evidence binding references every handler var it folds in,
            // so pull them into `needed` directly.
            for (eff, op, var_name, _) in &op_vars {
                let _ = (eff, op);
                needed.insert(var_name.clone());
            }
        }
        // Transitive closure: handler arms can reference other handler vars
        let mut changed = true;
        while changed {
            changed = false;
            for (var, val) in &handler_bindings {
                if needed.contains(var) {
                    let mut refs = HashSet::new();
                    val.collect_handle_refs(&mut refs);
                    for r in refs {
                        if needed.insert(r) {
                            changed = true;
                        }
                    }
                }
            }
        }

        // Only emit bindings that are actually referenced
        handler_bindings.retain(|(var, _)| needed.contains(var));

        // Append the evidence binding as the final scoped binding so it is
        // placed after all the handler bindings it references.
        if needed.contains(&evidence_binding.0) {
            handler_bindings.push(evidence_binding);
        }

        let attached =
            self.attach_scoped_handler_bindings(result, condition_bindings, handler_bindings);
        let mut used = HashSet::new();
        Self::collect_var_refs(&attached, &mut used);
        let lowered = match lifted_evidence {
            Some((frame, lifted)) if used.contains(&frame.var) => {
                CExpr::Let(frame.var, Box::new(lifted), Box::new(attached))
            }
            _ => attached,
        };
        match abort_ref {
            Some(r) => CExpr::Let(
                r,
                Box::new(CExpr::Call("erlang".into(), "make_ref".into(), vec![])),
                Box::new(lowered),
            ),
            None => lowered,
        }
    }

    /// If a nested `with` chain uses handler values bound inside the wrapped
    /// block, the handler evidence cannot dominate the prefix that creates
    /// those values. Lower:
    ///
    /// `{ prefix; let h = ...; suffix } with h`
    ///
    /// as:
    ///
    /// `{ prefix; let h = ...; suffix with h }`
    ///
    /// This is intentionally a lowering-only rewrite: it keeps dynamic handler
    /// evidence scoped to the suffix where the handler tuple exists, avoiding
    /// evidence bindings that reference lets which appear later in the input
    /// Core Erlang chain.
    pub(crate) fn lower_with_chain_after_local_handler_bindings(
        &mut self,
        expr: &Expr,
        handler: &Handler,
        inherited_return_k: Option<CExpr>,
    ) -> Option<CExpr> {
        let mut layers_outer_to_inner = vec![handler.clone()];
        let mut base = expr;
        while let ExprKind::With {
            expr: inner,
            handler,
        } = &base.kind
        {
            layers_outer_to_inner.push((**handler).clone());
            base = inner;
        }

        let ExprKind::Block {
            stmts,
            dangling_trivia,
        } = &base.kind
        else {
            return None;
        };

        let local_handler_names: HashSet<String> = layers_outer_to_inner
            .iter()
            .filter_map(|layer| match layer {
                Handler::Named(named) => Some(named.name.clone()),
                Handler::Inline { .. } => None,
            })
            .collect();
        if local_handler_names.is_empty() {
            return None;
        }

        let split_at = stmts
            .iter()
            .enumerate()
            .filter_map(|(idx, stmt)| match &stmt.node {
                Stmt::Let {
                    pattern: Pat::Var { name, .. },
                    value,
                    ..
                } if local_handler_names.contains(name) && self.is_handler_value(value) => {
                    Some(idx)
                }
                _ => None,
            })
            .max()?;

        if split_at + 1 >= stmts.len() {
            return None;
        }

        let suffix = Expr::synth(
            base.span,
            ExprKind::Block {
                stmts: stmts[split_at + 1..].to_vec(),
                dangling_trivia: dangling_trivia.clone(),
            },
        );
        let mut handled_suffix = suffix;
        for layer in layers_outer_to_inner.into_iter().rev() {
            handled_suffix = Expr::synth(
                base.span,
                ExprKind::With {
                    expr: Box::new(handled_suffix),
                    handler: Box::new(layer),
                },
            );
        }

        let mut rewritten_stmts = stmts[..=split_at].to_vec();
        rewritten_stmts.push(Annotated::bare(Stmt::Expr(handled_suffix)));
        let rewritten = Expr::synth(
            base.span,
            ExprKind::Block {
                stmts: rewritten_stmts,
                dangling_trivia: dangling_trivia.clone(),
            },
        );
        Some(self.lower_tail(&rewritten, inherited_return_k))
    }

    /// Build a per-op handler function from a single handler arm.
    ///
    /// Produces: `fun (Arg0, ..., ArgN, K) -> body`
    /// Each op gets its own function with natural arity.
    ///
    /// When the arm has a `finally` block, `current_handler_finally` is set so
    /// that each `resume` site makes the resumed computation a region whose
    /// end runs the cleanup (`fin_resume`), lowered where the arm's variables
    /// (like `conn`) are bound. An arm that does not resume runs the cleanup
    /// before it aborts.
    pub(crate) fn build_op_handler_fun(
        &mut self,
        arm: &HandlerArm,
        source_module: Option<&str>,
        captures: &[(String, Expr)],
    ) -> CExpr {
        self.build_op_handler_fun_for_effect(arm, source_module, captures, None)
    }

    pub(crate) fn build_op_handler_fun_for_effect(
        &mut self,
        arm: &HandlerArm,
        source_module: Option<&str>,
        captures: &[(String, Expr)],
        effect_hint: Option<&str>,
    ) -> CExpr {
        let has_resume = arm.body.contains_resume();
        let effect_name = self
            .effect_for_handler_arm(arm, source_module)
            .or_else(|| effect_hint.map(str::to_string));
        let op_info = effect_name
            .as_ref()
            .and_then(|effect_name| {
                self.effect_defs
                    .get(effect_name)
                    .and_then(|info| info.ops.get(&arm.op_name))
            })
            .cloned();
        let source_param_count = op_info
            .as_ref()
            .map(|op| op.source_param_count)
            .unwrap_or(arm.params.len());
        let runtime_param_positions = op_info
            .as_ref()
            .map(|op| op.runtime_param_positions.clone())
            .unwrap_or_else(|| (0..source_param_count).collect());
        let runtime_param_count = op_info
            .as_ref()
            .map(|op| op.runtime_param_count)
            .unwrap_or(source_param_count);

        // If resume is never called, use `_` (Core Erlang wildcard) so the compiler
        // doesn't warn about the unused continuation parameter. Safe because
        // `contains_resume()` being false guarantees no Resume node exists in the arm
        // body, so `current_handler_k` ("<_>") is never read during lowering.
        let k_var = if has_resume {
            self.fresh()
        } else {
            "_".to_string()
        };
        let param_vars: Vec<String> = (0..runtime_param_count)
            .map(|i| format!("_HArg{}", i))
            .collect();

        // The op's own `where`-constraint dicts arrive as trailing args (after
        // the user runtime params, before the continuation), matching the order
        // the elaborator appends them at the call site. Name them so the body's
        // `DictMethodAccess` references (`__dict_<Trait>_<var>`) bind here.
        let dict_param_vars: Vec<String> = op_info
            .as_ref()
            .map(|op| {
                op.dict_param_names
                    .iter()
                    .map(|n| crate::codegen::lower::core_var(n))
                    .collect()
            })
            .unwrap_or_default();

        let mut fun_params: Vec<String> = param_vars.clone();
        fun_params.extend(dict_param_vars);
        fun_params.push(k_var.clone());

        // Set up K for resume references in the body.
        // The handler arm body is owned by the handler: it produces the
        // handled computation's result itself rather than flowing into an
        // enclosing function-level return continuation.
        let prev_handler_k = self.current_handler_k.replace(k_var);

        // The tail of an arm of a general `with` that does not resume
        // throws the abort of that `with`; a tail `resume` is left as it is
        // (`lower_tail`). An arm of a chained `with` resumes in every tail.
        let abort_k = self.arm_abort_continuation(
            effect_name.as_deref(),
            arm.finally_block.as_deref(),
            has_resume,
        );
        let saved_inherited = std::mem::replace(
            &mut self.current_handler_inherited_k,
            abort_k.as_ref().map(|(var, _)| CExpr::Var(var.clone())),
        );
        let saved_abort_k = std::mem::replace(
            &mut self.current_abort_k,
            abort_k.as_ref().map(|(var, _)| var.clone()),
        );

        // Set current_handler_finally so Resume lowering wraps K calls in try/catch.
        let saved_finally = self.current_handler_finally.take();
        let saved_source_module = self.current_handler_source_module.clone();
        // An inline handler (`source_module == None`) nested inside an imported
        // handler's body physically belongs to that imported module — inherit the
        // enclosing origin rather than clobbering it to `None`, so constructors in
        // the inline arm still canonicalize against the right module.
        let source_module = self.handler_arm_definition_module(arm.id).or(source_module);
        if let Some(source_module) = source_module {
            self.current_handler_source_module = Some(source_module.to_string());
        }
        if let Some(ref fb) = arm.finally_block {
            self.current_handler_finally =
                Some(self.effect_normal_body(fb, "finally block").into_owned());
        }

        // Recovered handler factories are lowered at the call site. Their
        // captured handler parameters are lexical runtime values, not static
        // named handler declarations. Register the capture names while
        // lowering the arm body so `expr with backend` resolves to the tuple
        // bound below instead of attempting a static handler lookup.
        let mut saved_capture_handlers = Vec::new();
        for (capture_name, capture_value) in captures {
            let info = if let ExprKind::Var { name: value_name } = &capture_value.kind {
                self.handle_dynamic_vars
                    .get(value_name)
                    .map(|(_, effects, has_return)| (effects.clone(), *has_return))
                    .or_else(|| self.dynamic_handler_info_from_expr(capture_value))
            } else {
                self.dynamic_handler_info_from_expr(capture_value)
            };
            if let Some((effects, has_return)) = info {
                let previous = self.handle_dynamic_vars.insert(
                    capture_name.clone(),
                    (core_var(capture_name), effects, has_return),
                );
                saved_capture_handlers.push((capture_name.clone(), previous));
            }
        }

        let mut body_ce = self.lower_handler_owned_expr(&arm.body);
        body_ce = Self::bind_abort_continuation(abort_k, body_ce);

        for (capture_name, previous) in saved_capture_handlers.into_iter().rev() {
            if let Some(previous) = previous {
                self.handle_dynamic_vars.insert(capture_name, previous);
            } else {
                self.handle_dynamic_vars.remove(&capture_name);
            }
        }

        self.current_handler_finally = saved_finally;

        // Bind arm's params (possibly patterns) to the positional handler args
        for (i, pat) in arm.params.iter().enumerate().rev() {
            let bound_value = runtime_param_positions
                .iter()
                .position(|&source_idx| source_idx == i)
                .map(|runtime_idx| CExpr::Var(param_vars[runtime_idx].clone()))
                .unwrap_or_else(|| CExpr::Lit(CLit::Atom("unit".to_string())));
            let (var, wrapped_body) = self.destructure_pat(pat, body_ce);
            body_ce = CExpr::Let(var, Box::new(bound_value), Box::new(wrapped_body));
        }

        for (name, value) in captures.iter().rev() {
            // A handler factory argument may itself be a dynamic handler let
            // binding. Such bindings are represented by a fresh tuple variable
            // rather than the source-level Core variable name, so capture that
            // tuple directly. Lowering the source `Var` would emit an unbound
            // variable (e.g. `Base`) in the generated Core Erlang.
            let capture_value = if let ExprKind::Var { name: value_name } = &value.kind {
                self.handle_dynamic_vars
                    .get(value_name)
                    .map(|(tuple_var, _, _)| CExpr::Var(tuple_var.clone()))
                    .unwrap_or_else(|| self.lower_expr(value))
            } else {
                self.lower_expr(value)
            };
            body_ce = CExpr::Let(
                crate::codegen::lower::core_var(name),
                Box::new(capture_value),
                Box::new(body_ce),
            );
        }

        self.current_handler_source_module = saved_source_module;
        self.current_handler_k = prev_handler_k;
        self.current_handler_inherited_k = saved_inherited;
        self.current_abort_k = saved_abort_k;
        CExpr::Fun(fun_params, Box::new(body_ce))
    }

    /// Bind an arm's abort continuation around its body, if the body uses it.
    fn bind_abort_continuation(abort_k: Option<(String, CExpr)>, body: CExpr) -> CExpr {
        let Some((var, value)) = abort_k else {
            return body;
        };
        let mut used = HashSet::new();
        Self::collect_var_refs(&body, &mut used);
        if used.contains(&var) {
            CExpr::Let(var, Box::new(value), Box::new(body))
        } else {
            body
        }
    }

    /// The abort continuation of an arm of the `with` being built, when it
    /// has an abort reference: `(variable, fun(V) -> abort(Ref, Tag, V))`.
    /// An arm with a `finally` block that does not resume runs the cleanup
    /// first.
    fn arm_abort_continuation(
        &mut self,
        effect_name: Option<&str>,
        finally_block: Option<&Expr>,
        has_resume: bool,
    ) -> Option<(String, CExpr)> {
        let abort_ref = self.current_abort_ref.clone()?;
        let tag = effect_name.unwrap_or("unknown");
        let var = self.fresh();
        let param = self.fresh();
        let abort = evidence::abort_continuation(param.clone(), CExpr::Var(abort_ref), tag);
        let value = match (finally_block, has_resume) {
            (Some(fb), false) => {
                let fb = self.effect_normal_body(fb, "finally block").into_owned();
                let cleanup = evidence::meta_run(self.lower_expr(&fb));
                let CExpr::Fun(params, body) = abort else {
                    unreachable!()
                };
                CExpr::Fun(
                    params,
                    Box::new(CExpr::Let("_".to_string(), Box::new(cleanup), body)),
                )
            }
            _ => abort,
        };
        Some((var, value))
    }

    pub(crate) fn build_inline_op_handler_fun(&mut self, arms: &[HandlerArm]) -> CExpr {
        match arms {
            [] => self.build_passthrough_handler_fun(),
            [arm] => self.build_op_handler_fun(arm, None, &[]),
            [first, ..] => self.build_multi_arm_inline_op_handler_fun(first, arms),
        }
    }

    pub(crate) fn build_multi_arm_inline_op_handler_fun(
        &mut self,
        first: &HandlerArm,
        arms: &[HandlerArm],
    ) -> CExpr {
        let has_resume = arms.iter().any(|arm| arm.body.contains_resume());
        let op_info = self
            .effect_for_handler_arm(first, None)
            .and_then(|effect_name| {
                self.effect_defs
                    .get(&effect_name)
                    .and_then(|info| info.ops.get(&first.op_name))
            })
            .cloned();
        let source_param_count = op_info
            .as_ref()
            .map(|op| op.source_param_count)
            .unwrap_or(first.params.len());
        let runtime_param_positions = op_info
            .as_ref()
            .map(|op| op.runtime_param_positions.clone())
            .unwrap_or_else(|| (0..source_param_count).collect());
        let runtime_param_count = op_info
            .as_ref()
            .map(|op| op.runtime_param_count)
            .unwrap_or(source_param_count);

        let k_var = if has_resume {
            self.fresh()
        } else {
            "_".to_string()
        };
        let param_vars: Vec<String> = (0..runtime_param_count)
            .map(|i| format!("_HArg{}", i))
            .collect();
        let mut fun_params = param_vars.clone();
        fun_params.push(k_var.clone());

        let prev_handler_k = self.current_handler_k.replace(k_var);
        let saved_finally = self.current_handler_finally.take();
        // Multi-arm inline handlers are always source-module-less, but if nested
        // inside an imported handler body their code belongs to that module —
        // inherit the enclosing origin (see `build_op_handler_fun_for_effect`).
        let saved_source_module = self.current_handler_source_module.clone();

        let scrutinee = if runtime_param_count == 1 {
            CExpr::Var(param_vars[0].clone())
        } else {
            CExpr::Values(
                param_vars
                    .iter()
                    .map(|param| CExpr::Var(param.clone()))
                    .collect(),
            )
        };

        let mut case_arms = Vec::new();
        for arm in arms {
            self.current_handler_finally = arm
                .finally_block
                .as_ref()
                .map(|fb| self.effect_normal_body(fb, "finally block").into_owned());
            let effect_name = self.effect_for_handler_arm(arm, None);
            let abort_k = self.arm_abort_continuation(
                effect_name.as_deref(),
                arm.finally_block.as_deref(),
                arm.body.contains_resume(),
            );
            let saved_inherited = std::mem::replace(
                &mut self.current_handler_inherited_k,
                abort_k.as_ref().map(|(var, _)| CExpr::Var(var.clone())),
            );
            let saved_abort_k = std::mem::replace(
                &mut self.current_abort_k,
                abort_k.as_ref().map(|(var, _)| var.clone()),
            );
            let mut body_ce = self.lower_handler_owned_expr(&arm.body);
            self.current_handler_inherited_k = saved_inherited;
            self.current_abort_k = saved_abort_k;
            body_ce = Self::bind_abort_continuation(abort_k, body_ce);

            for (source_idx, pat) in arm.params.iter().enumerate().rev() {
                if !runtime_param_positions.contains(&source_idx) {
                    let (var, wrapped_body) = self.destructure_pat(pat, body_ce);
                    body_ce = CExpr::Let(
                        var,
                        Box::new(CExpr::Lit(CLit::Atom("unit".to_string()))),
                        Box::new(wrapped_body),
                    );
                }
            }

            let runtime_pats: Vec<CPat> = runtime_param_positions
                .iter()
                .take(runtime_param_count)
                .map(|&source_idx| {
                    arm.params
                        .get(source_idx)
                        .map(|pat| {
                            self.lower_pat(
                                pat,
                                &self.constructor_atoms,
                                self.handler_origin_module(),
                            )
                        })
                        .unwrap_or(CPat::Wildcard)
                })
                .collect();
            let pat = if runtime_param_count == 1 {
                runtime_pats.into_iter().next().unwrap_or(CPat::Wildcard)
            } else {
                CPat::Values(runtime_pats)
            };
            case_arms.push(CArm {
                pat,
                guard: None,
                body: body_ce,
            });
        }

        self.current_handler_finally = saved_finally;
        self.current_handler_source_module = saved_source_module;
        self.current_handler_k = prev_handler_k;

        CExpr::Fun(
            fun_params,
            Box::new(CExpr::Case(Box::new(scrutinee), case_arms)),
        )
    }
}

/// Whether the arms a plan installs never leave a frame where the operation
/// is performed: each resumes at most once and only in tail position, and
/// none has a `finally` block. A handler value only known at runtime may.
fn op_plan_is_direct(plan: &OpHandlerPlan) -> bool {
    use crate::codegen::handler_analysis::{ResumptionKind, classify_body};
    let arm_is_direct = |arm: &HandlerArm| {
        arm.finally_block.is_none()
            && matches!(
                classify_body(&arm.body),
                ResumptionKind::TailResumptive | ResumptionKind::OneShot
            )
    };
    match plan {
        OpHandlerPlan::Inline { arms } => arms.iter().all(arm_is_direct),
        OpHandlerPlan::Static { arm, .. } => arm_is_direct(arm),
        OpHandlerPlan::Conditional {
            then_arm, else_arm, ..
        } => then_arm.iter().chain(else_arm.iter()).all(arm_is_direct),
        OpHandlerPlan::Dynamic { .. } => false,
        OpHandlerPlan::BeamNative { .. } | OpHandlerPlan::Passthrough => true,
    }
}

/// How an evidence entry installed by a `with` is treated by the `with`s
/// inside it (`lift_evidence`), from least to most lifting.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum EntryKind {
    Direct,
    DirectIfFrameIs,
    Lifted,
}
