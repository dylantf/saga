use super::*;
use crate::ast::{Expr, ExprKind, HandlerArm, NodeId, Pat, Stmt};
use crate::codegen::call_effects;
use crate::codegen::cerl::{CArm, CExpr, CLit, CPat};
use crate::codegen::lower::util::*;
use crate::codegen::lower::*;

impl<'a> Lowerer<'a> {
    pub(crate) fn push_effect_op_trace(
        &mut self,
        node_id: NodeId,
        effect_name: &str,
        op_name: &str,
        source_args: usize,
        runtime_args: usize,
        shape: String,
    ) {
        self.effect_op_trace.push(call_effects::EffectOpTraceEntry {
            node_id,
            effect: effect_name.to_string(),
            op: op_name.to_string(),
            source_args,
            runtime_args,
            shape,
        });
    }

    pub(crate) fn evidence_lookup_trace_shape(&self, effect_name: &str) -> String {
        match &self.current_evidence {
            Some(ctx) if !ctx.is_open && ctx.layout.tags().iter().any(|tag| tag == effect_name) => {
                "evidence-lookup(static-index)".to_string()
            }
            Some(ctx) if ctx.is_open => "evidence-lookup(open-row-bridge)".to_string(),
            Some(_) => "evidence-lookup(runtime-bridge)".to_string(),
            None => "evidence-lookup(missing-evidence)".to_string(),
        }
    }

    pub(crate) fn effect_op_lowering_plan(
        &self,
        effect_key: &str,
        effect_name: &str,
    ) -> EffectOpLoweringPlan {
        if let Some(handler_canonical) = self.direct_ops.get(effect_key).cloned() {
            EffectOpLoweringPlan::DirectNative { handler_canonical }
        } else if let Some(plan) = self.static_tail_resume_ops.get(effect_key).cloned() {
            EffectOpLoweringPlan::DirectStaticTailResume { plan }
        } else {
            EffectOpLoweringPlan::EvidenceLookup {
                trace_shape: self.evidence_lookup_trace_shape(effect_name),
            }
        }
    }

    pub(crate) fn lower_direct_op_result(
        &mut self,
        value: CExpr,
        continuation: Option<CExpr>,
    ) -> CExpr {
        if let Some(k) = continuation {
            match k {
                CExpr::Fun(params, body) if params.len() == 1 => {
                    CExpr::Let(params[0].clone(), Box::new(value), body)
                }
                other => {
                    let result_var = self.fresh();
                    CExpr::Let(
                        result_var.clone(),
                        Box::new(value),
                        Box::new(CExpr::Apply(Box::new(other), vec![CExpr::Var(result_var)])),
                    )
                }
            }
        } else {
            value
        }
    }

    pub(crate) fn static_tail_resume_value_supported(expr: &Expr) -> bool {
        match &expr.kind {
            ExprKind::Lit { .. }
            | ExprKind::Var { .. }
            | ExprKind::Constructor { .. }
            | ExprKind::QualifiedName { .. }
            | ExprKind::DictRef { .. }
            | ExprKind::SymbolIntrinsic { .. } => true,
            ExprKind::Tuple { elements } | ExprKind::ListLit { elements } => elements
                .iter()
                .all(Self::static_tail_resume_value_supported),
            ExprKind::RecordCreate { fields, .. } | ExprKind::AnonRecordCreate { fields } => fields
                .iter()
                .all(|(_, _, value)| Self::static_tail_resume_value_supported(value)),
            ExprKind::Ascription { expr, .. } => Self::static_tail_resume_value_supported(expr),
            _ => false,
        }
    }

    pub(crate) fn static_tail_resume_bindings(
        &mut self,
        params: &[Pat],
        param_vars: &[String],
        runtime_param_positions: &[usize],
    ) -> Option<Vec<(String, CExpr)>> {
        let mut bindings = Vec::new();
        for (source_idx, param) in params.iter().enumerate() {
            let value = runtime_param_positions
                .iter()
                .position(|&runtime_source_idx| runtime_source_idx == source_idx)
                .map(|runtime_idx| CExpr::Var(param_vars[runtime_idx].clone()))
                .unwrap_or_else(|| CExpr::Lit(CLit::Atom("unit".to_string())));
            match param {
                Pat::Var { name, .. } => {
                    bindings.push((crate::codegen::lower::core_var(name), value))
                }
                Pat::Wildcard { .. }
                | Pat::Lit {
                    value: crate::ast::Lit::Unit,
                    ..
                } => {}
                _ => return None,
            }
        }
        Some(bindings)
    }

    pub(crate) fn lower_static_tail_resume_op(
        &mut self,
        plan: crate::codegen::lower::StaticTailResumeOp,
        param_vars: &[String],
        runtime_param_positions: &[usize],
        continuation: Option<CExpr>,
    ) -> Option<CExpr> {
        let body = self.static_tail_resume_direct_body(&plan.arm.body)?;

        let param_bindings = self.static_tail_resume_bindings(
            &plan.arm.params,
            param_vars,
            runtime_param_positions,
        )?;

        // The op's own `where`-constraint dicts are passed as trailing args
        // (after the user params). The closure path binds them via fun params;
        // here we inline the arm body, so bind them explicitly from the trailing
        // `param_vars` slots so `DictMethodAccess` references in the body resolve.
        let dict_names: Vec<String> = self
            .effect_for_handler_arm(&plan.arm, plan.source_module.as_deref())
            .and_then(|eff| {
                self.effect_defs
                    .get(&eff)
                    .and_then(|info| info.ops.get(&plan.arm.op_name))
            })
            .map(|op| op.dict_param_names.clone())
            .unwrap_or_default();
        let dict_bindings: Vec<(String, CExpr)> = dict_names
            .iter()
            .enumerate()
            .filter_map(|(i, name)| {
                let idx = param_vars.len().checked_sub(dict_names.len())? + i;
                param_vars.get(idx).map(|var| {
                    (
                        crate::codegen::lower::core_var(name),
                        CExpr::Var(var.clone()),
                    )
                })
            })
            .collect();
        let capture_bindings: Vec<(String, CExpr)> = plan
            .captures
            .iter()
            .map(|(name, value)| {
                (
                    crate::codegen::lower::core_var(name),
                    self.lower_expr_value(value),
                )
            })
            .collect();
        let variant_capture_bindings: Vec<(String, CExpr)> = self
            .static_helper_variant_capture_bindings
            .iter()
            .map(|(name, param_var)| {
                (
                    crate::codegen::lower::core_var(name),
                    CExpr::Var(param_var.clone()),
                )
            })
            .collect();

        let saved_source_module = self.current_handler_source_module.clone();
        self.current_handler_source_module = plan.source_module;
        let lowered_body = match body {
            StaticTailResumeDirectBody::Expr(value) => {
                let resumed_value = self.lower_expr_value(&value);
                self.lower_direct_op_result(resumed_value, continuation)
            }
            StaticTailResumeDirectBody::Block(stmts) => {
                self.lower_block_with_return_k(&stmts, continuation)
            }
        };
        self.current_handler_source_module = saved_source_module;

        Some(
            capture_bindings
                .into_iter()
                .chain(variant_capture_bindings)
                .chain(param_bindings)
                .chain(dict_bindings)
                .rev()
                .fold(lowered_body, |body, (var, val)| {
                    CExpr::Let(var, Box::new(val), Box::new(body))
                }),
        )
    }

    pub(crate) fn static_tail_resume_params_supported(params: &[Pat]) -> bool {
        params.iter().all(|param| {
            matches!(
                param,
                Pat::Var { .. }
                    | Pat::Wildcard { .. }
                    | Pat::Lit {
                        value: crate::ast::Lit::Unit,
                        ..
                    }
            )
        })
    }

    pub(crate) fn static_tail_resume_prefix_stmt_supported(&self, stmt: &Stmt) -> bool {
        let value = match stmt {
            Stmt::Let { value, .. } | Stmt::Expr(value) => value,
            Stmt::LetFun { .. } => return false,
        };
        !value.contains_resume() && !self.branch_is_effectful(value)
    }

    pub(crate) fn static_tail_resume_direct_body(
        &self,
        body: &Expr,
    ) -> Option<StaticTailResumeDirectBody> {
        match &body.kind {
            ExprKind::Resume { value } if Self::static_tail_resume_value_supported(value) => {
                Some(StaticTailResumeDirectBody::Expr((**value).clone()))
            }
            ExprKind::Block { stmts, .. } => {
                let (last, prefix) = stmts.split_last()?;
                if !prefix
                    .iter()
                    .all(|stmt| self.static_tail_resume_prefix_stmt_supported(&stmt.node))
                {
                    return None;
                }
                let Stmt::Expr(tail) = &last.node else {
                    return None;
                };
                let ExprKind::Resume { value } = &tail.kind else {
                    return None;
                };
                if !Self::static_tail_resume_value_supported(value) {
                    return None;
                }
                let mut rewritten: Vec<Stmt> =
                    prefix.iter().map(|stmt| stmt.node.clone()).collect();
                rewritten.push(Stmt::Expr((**value).clone()));
                Some(StaticTailResumeDirectBody::Block(rewritten))
            }
            _ => None,
        }
    }

    pub(crate) fn static_tail_resume_arm_supported(&self, arm: &HandlerArm) -> bool {
        if arm.finally_block.is_some()
            || self.optimization.handler_analysis.resumption.get(&arm.id)
                != Some(&crate::codegen::handler_analysis::ResumptionKind::TailResumptive)
            || !Self::static_tail_resume_params_supported(&arm.params)
        {
            return false;
        }
        self.static_tail_resume_direct_body(&arm.body).is_some()
    }

    pub(crate) fn static_tail_resume_plan_for_op_handler(
        &self,
        plan: &OpHandlerPlan,
    ) -> Option<crate::codegen::lower::StaticTailResumeOp> {
        match plan {
            OpHandlerPlan::Inline { arms } if arms.len() == 1 => {
                let arm = arms[0].clone();
                self.static_tail_resume_arm_supported(&arm).then_some(
                    crate::codegen::lower::StaticTailResumeOp {
                        arm,
                        source_module: None,
                        captures: Vec::new(),
                    },
                )
            }
            OpHandlerPlan::Static {
                arm,
                source_module,
                handler_canonical,
                captures,
            } if !self.is_beam_native_handler_canonical(handler_canonical)
                && match source_module {
                    Some(module) => module == &self.current_source_module,
                    None => true,
                } =>
            {
                let arm = arm.clone();
                self.static_tail_resume_arm_supported(&arm).then_some(
                    crate::codegen::lower::StaticTailResumeOp {
                        arm,
                        source_module: source_module.clone(),
                        captures: captures.clone(),
                    },
                )
            }
            _ => None,
        }
    }

    pub(crate) fn compose_return_k(
        &mut self,
        inner: Option<CExpr>,
        outer: Option<CExpr>,
    ) -> Option<CExpr> {
        match (inner, outer) {
            (Some(inner), Some(outer)) => {
                let param = self.fresh();
                let inner_value = self.fresh();
                Some(CExpr::Fun(
                    vec![param.clone()],
                    Box::new(CExpr::Let(
                        inner_value.clone(),
                        Box::new(CExpr::Apply(Box::new(inner), vec![CExpr::Var(param)])),
                        Box::new(CExpr::Apply(Box::new(outer), vec![CExpr::Var(inner_value)])),
                    )),
                ))
            }
            (Some(k), None) | (None, Some(k)) => Some(k),
            (None, None) => None,
        }
    }

    pub(crate) fn lower_handler_owned_expr(&mut self, expr: &Expr) -> CExpr {
        // For abort handler arm bodies inside an effectful host context
        // (e.g. an impl method that has its own `_ReturnK`), the abort
        // value must flow through the with's outer K — not just return
        // raw up the Erlang stack, which would bypass the host's CPS
        // chain. `current_handler_inherited_k` carries the with's outer
        // K when applicable. For non-effectful hosts (None) we fall back
        // to plain value-mode lowering: the abort value just becomes the
        // closure's Erlang return value.
        if let Some(k) = self.current_handler_inherited_k.clone() {
            self.lower_expr_with_installed_return_k(expr, Some(k))
        } else {
            self.lower_expr_value(expr)
        }
    }

    pub(crate) fn lower_handled_expr_with_return_k(
        &mut self,
        expr: &Expr,
        return_k: Option<CExpr>,
    ) -> CExpr {
        self.lower_expr_with_installed_return_k(expr, return_k)
    }

    pub(crate) fn lower_handled_inner_expr(
        &mut self,
        expr: &Expr,
        handled_return_k: Option<CExpr>,
        inherited_return_k: Option<CExpr>,
    ) -> CExpr {
        let return_k = self.compose_return_k(handled_return_k, inherited_return_k);
        if self.expr_is_effectful_call(expr) {
            self.lower_expr_with_call_return_k(expr, return_k)
        } else {
            self.lower_handled_expr_with_return_k(expr, return_k)
        }
    }

    pub(crate) fn dynamic_return_lambda(&mut self, tuple_var: &str, op_count: usize) -> CExpr {
        let param = self.fresh();
        let identity = CExpr::Fun(vec![param.clone()], Box::new(CExpr::Var(param)));
        let tuple_size = cerl_call(
            "erlang",
            "tuple_size",
            vec![CExpr::Var(tuple_var.to_string())],
        );
        let return_index = op_count as i64 + 1;
        let return_lambda = cerl_call(
            "erlang",
            "element",
            vec![
                CExpr::Lit(CLit::Int(return_index)),
                CExpr::Var(tuple_var.to_string()),
            ],
        );
        CExpr::Case(
            Box::new(tuple_size),
            vec![
                CArm {
                    pat: CPat::Lit(CLit::Int(return_index)),
                    guard: None,
                    body: return_lambda,
                },
                CArm {
                    pat: CPat::Var("_".to_string()),
                    guard: None,
                    body: identity,
                },
            ],
        )
    }

    pub(crate) fn build_return_lambda(
        &mut self,
        ret: &HandlerArm,
        source_module: Option<&str>,
    ) -> CExpr {
        let saved_source_module = self.current_handler_source_module.clone();
        self.current_handler_source_module = source_module.map(str::to_string);
        // Return-lambda body flows through the lambda's caller (which itself
        // applies inherited_K to the lambda result). Threading inherited_K
        // into the body would double-apply it.
        let saved_inherited = self.current_handler_inherited_k.take();
        let ret_body = self.lower_handler_owned_expr(&ret.body);
        self.current_handler_inherited_k = saved_inherited;
        let (param, body) = if ret.params.is_empty() {
            (self.fresh(), ret_body)
        } else {
            self.destructure_pat(&ret.params[0], ret_body)
        };
        self.current_handler_source_module = saved_source_module;
        CExpr::Fun(vec![param], Box::new(body))
    }

    /// Read the per-op closure for `effect.op` out of the in-scope evidence
    /// vector. Closed-row callers with the effect statically present in their
    /// layout emit pure `element/2` chains; open-row callers (or callers whose
    /// layout doesn't include this effect — happens at handler-arm bodies that
    /// re-perform an effect not held by the current arm's caller layout) fall
    /// back to the runtime bridge.
    pub(crate) fn evidence_op_lookup(&mut self, effect_name: &str, op_name: &str) -> CExpr {
        let ev_ctx = self
            .current_evidence
            .clone()
            .unwrap_or_else(|| panic!("no evidence in scope for op '{}.{}'", effect_name, op_name));
        let op_index = self.evidence_op_index(effect_name, op_name) as i64;
        let layout_has_tag = ev_ctx.layout.tags().iter().any(|t| t == effect_name);
        let entry_op_tuple: CExpr = if !ev_ctx.is_open && layout_has_tag {
            let eff_idx =
                crate::codegen::lower::evidence::evidence_index_of(&ev_ctx.layout, effect_name)
                    as i64;
            cerl_call(
                "erlang",
                "element",
                vec![
                    CExpr::Lit(CLit::Int(2)),
                    cerl_call(
                        "erlang",
                        "element",
                        vec![
                            CExpr::Lit(CLit::Int(eff_idx)),
                            CExpr::Var(ev_ctx.var.clone()),
                        ],
                    ),
                ],
            )
        } else {
            crate::codegen::lower::evidence::find_evidence(
                CExpr::Var(ev_ctx.var.clone()),
                effect_name,
            )
        };
        cerl_call(
            "erlang",
            "element",
            vec![CExpr::Lit(CLit::Int(op_index)), entry_op_tuple],
        )
    }

    /// 1-based op index inside an effect's op tuple. Op tuples are sorted
    /// alphabetically by op name (matches `effect_handler_ops` ordering for a
    /// single effect and the canonical shape produced by handler emission).
    pub(crate) fn evidence_op_index(&self, effect_name: &str, op_name: &str) -> usize {
        let info = self
            .effect_defs
            .get(effect_name)
            .unwrap_or_else(|| panic!("unknown effect '{}'", effect_name));
        let mut ops: Vec<&String> = info.ops.keys().collect();
        ops.sort();
        match ops.iter().position(|n| n.as_str() == op_name) {
            Some(i) => i + 1,
            None => panic!(
                "unknown op '{}' on effect '{}' (have: {:?})",
                op_name, effect_name, ops
            ),
        }
    }
}
