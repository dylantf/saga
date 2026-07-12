use super::*;
use crate::ast::{Expr, ExprKind, Handler, HandlerArm, HandlerItem, Pat, Stmt};
use crate::codegen::cerl::{CArm, CExpr, CLit, CPat};
use crate::codegen::lower::util::*;
use crate::codegen::lower::*;
use std::collections::HashMap;

impl<'a> Lowerer<'a> {
    /// Lower a handler expression to a tuple of per-op handler lambdas.
    /// Used when a handler expression appears as a value (returned from function,
    /// passed as argument, etc.) rather than in a `handle` binding.
    ///
    /// The tuple layout is: ops sorted alphabetically by "Effect.op" key,
    /// with an optional return clause lambda as the last element.
    pub(crate) fn lower_handler_expr_to_tuple(&mut self, body: &crate::ast::HandlerBody) -> CExpr {
        let semantic_module_name = self.current_semantic_module_name().to_string();
        let canonical_effects =
            self.resolved_effect_refs_for_module(&semantic_module_name, &body.effects);
        let handler_ops = self.effect_handler_ops(&canonical_effects);

        // Index arms by op name for quick lookup
        let arms_by_op: std::collections::HashMap<&str, &crate::ast::HandlerArm> = body
            .arms
            .iter()
            .map(|a| (a.node.op_name.as_str(), &a.node))
            .collect();

        let mut tuple_elements = Vec::new();
        for (eff, op) in &handler_ops {
            if let Some(arm) = arms_by_op.get(op.as_str()) {
                tuple_elements.push(self.build_op_handler_fun_for_effect(
                    arm,
                    None,
                    &[],
                    Some(eff),
                ));
            } else {
                // Passthrough: identity continuation
                let k_param = self.fresh();
                tuple_elements.push(CExpr::Fun(
                    vec![k_param.clone()],
                    Box::new(CExpr::Apply(
                        Box::new(CExpr::Var(k_param)),
                        vec![CExpr::Lit(CLit::Atom("unit".to_string()))],
                    )),
                ));
            }
        }
        if let Some(rc) = &body.return_clause {
            let ret_body = self.lower_expr(&rc.body);
            let (param, body) = if rc.params.is_empty() {
                (self.fresh(), ret_body)
            } else {
                self.destructure_pat(&rc.params[0], ret_body)
            };
            tuple_elements.push(CExpr::Fun(vec![param], Box::new(body)));
        }
        CExpr::Tuple(tuple_elements)
    }

    /// Lower a named handler definition to a tuple-of-lambdas.
    /// Used when a handler name appears as a value (e.g. returned from a function,
    /// passed as an argument) rather than in a `with` block.
    pub(crate) fn lower_handler_def_to_tuple(&mut self, handler_name: &str) -> Option<CExpr> {
        let canonical = self.resolve_handler_name(handler_name);
        let info = self.handler_defs.get(&canonical)?.clone();
        let handler_ops = self.effect_handler_ops(&info.effects);

        let mut tuple_elements = Vec::new();
        for (eff, op) in &handler_ops {
            if let Some(arm) = info.arms.iter().find(|a| a.op_name == *op) {
                tuple_elements.push(self.build_op_handler_fun_for_effect(
                    arm,
                    info.source_module.as_deref(),
                    &info.captures,
                    Some(eff),
                ));
            } else {
                let k_param = self.fresh();
                tuple_elements.push(CExpr::Fun(
                    vec![k_param.clone()],
                    Box::new(CExpr::Apply(
                        Box::new(CExpr::Var(k_param)),
                        vec![CExpr::Lit(CLit::Atom("unit".to_string()))],
                    )),
                ));
            }
        }
        if let Some(rc) = &info.return_clause {
            let ret_body = self.lower_expr(&rc.body);
            let (param, body) = if rc.params.is_empty() {
                (self.fresh(), ret_body)
            } else {
                self.destructure_pat(&rc.params[0], ret_body)
            };
            tuple_elements.push(CExpr::Fun(vec![param], Box::new(body)));
        }
        Some(CExpr::Tuple(tuple_elements))
    }

    pub(crate) fn normalize_with_handler(&self, handler: &Handler) -> WithHandlerLayer {
        match handler {
            Handler::Named(named) => WithHandlerLayer::Named {
                reference: named.clone(),
            },
            Handler::Inline { items, .. } => {
                let mut inline_arms = Vec::new();
                let mut return_clause = None;
                for ann in items {
                    match &ann.node {
                        HandlerItem::Named(_) => panic!(
                            "internal lowering error: named handler refs should have been desugared into nested `with` layers before lowering"
                        ),
                        HandlerItem::Arm(a) => inline_arms.push(a.clone()),
                        HandlerItem::Return(rc) => {
                            assert!(
                                return_clause.is_none(),
                                "internal lowering error: inline handler segment has multiple return clauses"
                            );
                            return_clause = Some(Box::new(rc.clone()));
                        }
                    }
                }
                WithHandlerLayer::Inline {
                    arms: inline_arms,
                    return_clause,
                }
            }
        }
    }

    pub(crate) fn pre_register_local_with_binding(&mut self, expr: &Expr, named_ref: &str) {
        let mut current = expr;
        let stmts = loop {
            match &current.kind {
                ExprKind::Block { stmts, .. } => break stmts,
                ExprKind::With { expr: inner, .. } => current = inner,
                _ => return,
            }
        };

        for stmt in stmts {
            if let Stmt::Let { pattern, value, .. } = &stmt.node
                && let Pat::Var {
                    name, id: pat_id, ..
                } = pattern
                && name == named_ref
                && self.is_handler_value(value)
            {
                self.lower_handle_binding(name, Some(*pat_id), value);
            }
        }
    }

    pub(crate) fn resolve_named_handler_item(
        &self,
        reference: &crate::ast::NamedHandlerRef,
    ) -> NamedHandlerItem {
        let name = &reference.name;
        if let Some((tuple_var, effects, has_return)) = self.handle_dynamic_vars.get(name).cloned()
        {
            return NamedHandlerItem::Dynamic {
                tuple_var,
                effects,
                has_return,
            };
        }
        if let Some((cond_var, cond_ce, then_canonical, else_canonical)) =
            self.handle_cond_vars.get(name).cloned()
        {
            let then_info = self
                .handler_defs
                .get(&then_canonical)
                .cloned()
                .unwrap_or_else(|| {
                    panic!(
                        "internal lowering error: unknown conditional handler branch '{}' for '{}'",
                        then_canonical, name
                    )
                });
            let else_info = self
                .handler_defs
                .get(&else_canonical)
                .cloned()
                .unwrap_or_else(|| {
                    panic!(
                        "internal lowering error: unknown conditional handler branch '{}' for '{}'",
                        else_canonical, name
                    )
                });
            return NamedHandlerItem::Conditional {
                cond_var,
                cond_ce: Box::new(cond_ce),
                then_info: Box::new(then_info),
                else_info: Box::new(else_info),
            };
        }
        // A local let-bound alias/factory is registered while lowering the
        // enclosing block. Named-handler refs do not always receive a front-end
        // value-resolution entry (notably when the factory arrived through a
        // re-export), so consult that scoped lowering fact before requiring a
        // NodeId-based resolution.
        if let Some(canonical) = self.handler_canonical.get(name).cloned()
            && let Some(info) = self.handler_defs.get(&canonical).cloned()
        {
            return NamedHandlerItem::Static {
                canonical,
                info: Box::new(info),
            };
        }
        let canonical = self
            .resolved_handler_binding_name(reference.id)
            .unwrap_or_else(|| {
                panic!(
                    "internal lowering error: missing handler resolution for '{}' ({:?})",
                    name, reference.id
                )
            });
        let info = self
            .handler_defs
            .get(&canonical)
            .cloned()
            .unwrap_or_else(|| {
                panic!(
                    "internal lowering error: unknown handler item '{}' (canonical: {})",
                    name, canonical
                )
            });
        NamedHandlerItem::Static {
            canonical,
            info: Box::new(info),
        }
    }

    pub(crate) fn effect_for_handler_arm(
        &self,
        arm: &HandlerArm,
        source_module: Option<&str>,
    ) -> Option<String> {
        let module_name = source_module.unwrap_or_else(|| self.current_semantic_module_name());
        let applied = if module_name == self.current_source_module {
            self.check_result.effect_at_node.get(&arm.id)
        } else {
            self.ctx
                .module_semantics(module_name)
                .and_then(|semantics| semantics.effect_at_node.get(&arm.id))
        };
        if let Some(entry) = applied {
            return Some(self.canonicalize_effect(&crate::typechecker::applied_effect_key(entry)));
        }
        self.resolved_handler_arm_effect_for_module(arm, module_name)
    }

    pub(crate) fn static_arm_for_effect_op(
        &self,
        info: &crate::codegen::lower::HandlerInfo,
        eff: &str,
        op: &str,
    ) -> Option<(HandlerArm, Option<String>)> {
        info.arms
            .iter()
            .find(|arm| self.static_handler_arm_matches_effect_op(info, arm, eff, op))
            .cloned()
            .map(|arm| (arm, info.source_module.clone()))
    }

    fn static_handler_arm_matches_effect_op(
        &self,
        info: &crate::codegen::lower::HandlerInfo,
        arm: &HandlerArm,
        eff: &str,
        op: &str,
    ) -> bool {
        if arm.op_name != op {
            return false;
        }

        let module_name = info
            .source_module
            .as_deref()
            .unwrap_or_else(|| self.current_semantic_module_name());
        if let Some(resolved) = self.effect_for_handler_arm(arm, Some(module_name)) {
            return resolved == eff
                || crate::typechecker::applied_effect_family(&resolved)
                    == crate::typechecker::applied_effect_family(eff);
        }

        self.handler_arm_fallback_matches_effect_op(info, arm, eff)
    }

    fn handler_arm_fallback_matches_effect_op(
        &self,
        info: &crate::codegen::lower::HandlerInfo,
        arm: &HandlerArm,
        eff: &str,
    ) -> bool {
        if let Some(qualifier) = arm.qualifier.as_deref()
            && !self.effect_name_matches_qualifier(eff, qualifier, info.source_module.as_deref())
        {
            return false;
        }

        let mut matches = info.effects.iter().filter(|candidate| {
            self.effect_defs
                .get(candidate.as_str())
                .is_some_and(|effect| effect.ops.contains_key(&arm.op_name))
        });
        match (matches.next(), matches.next()) {
            (Some(candidate), None) => candidate == eff,
            _ => false,
        }
    }

    fn effect_name_matches_qualifier(
        &self,
        eff: &str,
        qualifier: &str,
        source_module: Option<&str>,
    ) -> bool {
        if eff == qualifier || eff.rsplit('.').next() == Some(qualifier) {
            return true;
        }
        if let Some(canonical) = self.effect_canonical.get(qualifier)
            && canonical == eff
        {
            return true;
        }
        source_module
            .map(|module| format!("{module}.{qualifier}"))
            .is_some_and(|canonical| canonical == eff)
    }

    pub(crate) fn dynamic_tuple_element_expr(
        &self,
        tuple_var: &str,
        effects: &[String],
        eff: &str,
        op: &str,
    ) -> CExpr {
        let handler_ops = self.effect_handler_ops(effects);
        let index = handler_ops
            .iter()
            .position(|(item_eff, item_op)| item_eff == eff && item_op == op)
            .unwrap_or_else(|| {
                panic!(
                    "internal lowering error: dynamic handler tuple '{}' is missing op '{}.{}'",
                    tuple_var, eff, op
                )
            });
        cerl_call(
            "erlang",
            "element",
            vec![
                CExpr::Lit(CLit::Int(index as i64 + 1)),
                CExpr::Var(tuple_var.to_string()),
            ],
        )
    }

    pub(crate) fn plan_named_op_handler(
        &self,
        eff: &str,
        op: &str,
        named_item: &NamedHandlerItem,
    ) -> OpHandlerPlan {
        match named_item {
            NamedHandlerItem::Static { canonical, info } => {
                if let Some((arm, source_module)) = self.static_arm_for_effect_op(info, eff, op) {
                    OpHandlerPlan::Static {
                        arm,
                        source_module,
                        effect_name: eff.to_string(),
                        handler_canonical: canonical.clone(),
                        captures: info.captures.clone(),
                    }
                } else if self.is_beam_native_handler_canonical(canonical) {
                    OpHandlerPlan::BeamNative {
                        handler_canonical: canonical.clone(),
                    }
                } else {
                    OpHandlerPlan::Passthrough
                }
            }
            NamedHandlerItem::Conditional {
                cond_var,
                then_info,
                else_info,
                ..
            } => {
                let then_arm = self
                    .static_arm_for_effect_op(then_info, eff, op)
                    .map(|(arm, _)| arm);
                let then_source = then_info.source_module.clone();
                let else_arm = self
                    .static_arm_for_effect_op(else_info, eff, op)
                    .map(|(arm, _)| arm);
                let else_source = else_info.source_module.clone();
                OpHandlerPlan::Conditional {
                    cond_var: cond_var.clone(),
                    then_arm,
                    then_source,
                    else_arm,
                    else_source,
                }
            }
            NamedHandlerItem::Dynamic {
                tuple_var, effects, ..
            } => OpHandlerPlan::Dynamic {
                element_expr: self.dynamic_tuple_element_expr(tuple_var, effects, eff, op),
            },
        }
    }

    pub(crate) fn plan_inline_op_handler(
        &self,
        eff: &str,
        op: &str,
        inline_arms_by_op: &HashMap<String, Vec<HandlerArm>>,
    ) -> OpHandlerPlan {
        let qualified_key = format!("{}.{}", eff, op);
        if let Some(arms) = inline_arms_by_op
            .get(&qualified_key)
            .or_else(|| inline_arms_by_op.get(op))
        {
            return OpHandlerPlan::Inline { arms: arms.clone() };
        }
        OpHandlerPlan::Passthrough
    }

    pub(crate) fn build_passthrough_handler_fun(&mut self) -> CExpr {
        let k_param = self.fresh();
        CExpr::Fun(
            vec![k_param.clone()],
            Box::new(CExpr::Apply(
                Box::new(CExpr::Var(k_param)),
                vec![CExpr::Lit(CLit::Atom("unit".to_string()))],
            )),
        )
    }

    pub(crate) fn build_conditional_handler_fun(
        &mut self,
        effect_name: &str,
        cond_var: &str,
        then_arm: Option<&HandlerArm>,
        then_source: Option<&str>,
        else_arm: Option<&HandlerArm>,
        else_source: Option<&str>,
    ) -> CExpr {
        let then_fun = if let Some(arm) = then_arm {
            self.build_op_handler_fun_for_effect(arm, then_source, &[], Some(effect_name))
        } else {
            self.build_passthrough_handler_fun()
        };
        let else_fun = if let Some(arm) = else_arm {
            self.build_op_handler_fun_for_effect(arm, else_source, &[], Some(effect_name))
        } else {
            self.build_passthrough_handler_fun()
        };
        let arity = match then_arm.or(else_arm) {
            Some(arm) => arm.params.len() + 1,
            None => 1,
        };
        let wrapper_params: Vec<String> = (0..arity).map(|i| format!("_HW{}", i)).collect();
        let args_ce: Vec<CExpr> = wrapper_params
            .iter()
            .map(|p| CExpr::Var(p.clone()))
            .collect();
        let then_call = CExpr::Apply(Box::new(then_fun), args_ce.clone());
        let else_call = CExpr::Apply(Box::new(else_fun), args_ce);
        let case_expr = CExpr::Case(
            Box::new(CExpr::Var(cond_var.to_string())),
            vec![
                CArm {
                    pat: CPat::Lit(CLit::Atom("true".to_string())),
                    guard: None,
                    body: then_call,
                },
                CArm {
                    pat: CPat::Var("_".to_string()),
                    guard: None,
                    body: else_call,
                },
            ],
        );
        CExpr::Fun(wrapper_params, Box::new(case_expr))
    }

    pub(crate) fn identity_return_lambda(&mut self) -> CExpr {
        let param = self.fresh();
        CExpr::Fun(vec![param.clone()], Box::new(CExpr::Var(param)))
    }
}
