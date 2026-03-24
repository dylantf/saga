use std::collections::HashSet;

use crate::ast::{self, Expr};
use crate::token::Span;

use super::{Checker, Diagnostic, Scheme, Type};

impl Checker {
    // --- Handler inference ---

    /// Infer the type of a `with` expression: `expr with handler`
    pub(crate) fn infer_with(
        &mut self,
        expr: &Expr,
        handler: &ast::Handler,
        _with_span: Span,
        with_node_id: crate::ast::NodeId,
    ) -> Result<(Type, super::EffectRow), Diagnostic> {
        let handled = self.handler_handled_effects(handler);

        // Build op_name -> (arm_span, source_module) map for this handler and push onto the stack.
        // This lets EffectCall inference record which arm handles each call (for LSP go-to-def).
        let arm_stack_entry: std::collections::HashMap<String, (Span, Option<String>)> =
            match handler {
                ast::Handler::Named(name, handler_span) => {
                    // Record reference to the handler definition
                    if let Some(def_id) = self.env.def_id(name) {
                        let usage_id = crate::ast::NodeId::fresh();
                        self.record_reference(usage_id, *handler_span, def_id);
                    }
                    self.handlers
                        .get(name)
                        .map(|h| {
                            let src = h.source_module.clone();
                            h.arm_spans
                                .iter()
                                .map(|(op, &span)| (op.clone(), (span, src.clone())))
                                .collect()
                        })
                        .unwrap_or_default()
                }
                ast::Handler::Inline { named, arms, .. } => {
                    let mut map = std::collections::HashMap::new();
                    for n in named {
                        // Record reference to each named handler
                        if let Some(def_id) = self.env.def_id(n) {
                            let usage_id = crate::ast::NodeId::fresh();
                            self.record_reference(usage_id, _with_span, def_id);
                        }
                        if let Some(h) = self.handlers.get(n) {
                            let src = h.source_module.clone();
                            map.extend(
                                h.arm_spans
                                    .iter()
                                    .map(|(op, &span)| (op.clone(), (span, src.clone()))),
                            );
                        }
                    }
                    for arm in arms {
                        map.insert(arm.op_name.clone(), (arm.span, None));
                    }
                    map
                }
            };
        self.lsp.with_arm_stacks.push(arm_stack_entry);

        let result = self.infer_with_inner(expr, handler, handled, with_node_id)?;
        self.lsp.with_arm_stacks.pop();

        Ok(result)
    }

    fn infer_with_inner(
        &mut self,
        expr: &Expr,
        handler: &ast::Handler,
        handled: HashSet<String>,
        with_node_id: crate::ast::NodeId,
    ) -> Result<(Type, super::EffectRow), Diagnostic> {
        // --- Scope 1: infer the inner expression with isolated effect tracking ---
        let inner_scope = self.enter_scope();
        let (expr_ty, inner_effs) = self.infer_expr(expr)?;
        let inner_result = self.exit_scope(inner_scope);

        // Unnecessary handler check: if the inner expression's effects don't
        // overlap with handled effects, the handler is unnecessary.
        if !handled.is_empty() && !inner_effs.effects.iter().any(|(n, _)| handled.contains(n)) {
            let mut effects: Vec<_> = handled.iter().cloned().collect();
            effects.sort();
            self.collected_diagnostics.push(Diagnostic::warning_at(
                expr.span,
                format!(
                    "expression does not use effects {{{}}}; handler is unnecessary",
                    effects.join(", ")
                ),
            ));
        }

        // Save effect cache for handler where-clause enforcement (Named branch)
        // and type param cache inheritance (Inline branch).
        let inner_effect_cache = inner_result.effect_cache;

        // Compute the remaining effect row (inner effects minus handled)
        let remaining_effs = inner_effs.subtract(&handled);

        let with_span = expr.span;
        match handler {
            ast::Handler::Named(name, _) => {
                if !self.handlers.contains_key(name) && self.env.get(name).is_none() {
                    return Err(Diagnostic::error_at(
                        with_span,
                        format!("undefined handler: {}", name),
                    ));
                }
                if let Some(handler_info) = self.handlers.get(name).cloned() {
                    if let Some((param_ty, ret_ty)) = &handler_info.return_type {
                        // Instantiate fresh type vars for each usage site so
                        // polymorphic handlers (e.g. `handler h for Fail a`)
                        // don't leak type bindings between different uses.
                        let mapping: std::collections::HashMap<u32, Type> = handler_info
                            .forall
                            .iter()
                            .map(|&id| (id, self.fresh_var()))
                            .collect();
                        let fresh_param = self.replace_vars(param_ty, &mapping);
                        let fresh_ret = self.replace_vars(ret_ty, &mapping);
                        self.unify_at(&fresh_param, &expr_ty, with_span)?;

                        // Enforce handler where clause constraints at the usage site.
                        // Use the inner expression's effect cache to find what each
                        // effect type param resolved to, then push pending constraints.
                        for ((effect_name, param_idx), trait_names) in
                            &handler_info.where_constraints
                        {
                            if let Some(effect_info) = self.effects.get(effect_name).cloned()
                                && let Some(&param_var_id) = effect_info.type_params.get(*param_idx)
                            {
                                // The effect cache stores the fresh var IDs used at the call site.
                                // Resolve through the cache first, then through substitution.
                                let ty = if let Some(cache) = inner_effect_cache.get(effect_name)
                                    && let Some(cached_ty) = cache.get(&param_var_id)
                                {
                                    self.sub.apply(cached_ty)
                                } else {
                                    self.sub.apply(&Type::Var(param_var_id))
                                };
                                for trait_name in trait_names {
                                    self.trait_state.pending_constraints.push((
                                        trait_name.clone(),
                                        ty.clone(),
                                        with_span,
                                        with_node_id,
                                    ));
                                }
                            }
                        }

                        Ok((self.sub.apply(&fresh_ret), remaining_effs.clone()))
                    } else {
                        Ok((expr_ty, remaining_effs.clone()))
                    }
                } else {
                    Ok((expr_ty, remaining_effs.clone()))
                }
            }
            ast::Handler::Inline {
                named,
                arms,
                return_clause,
            } => {
                for name in named {
                    if !self.handlers.contains_key(name) && self.env.get(name).is_none() {
                        return Err(Diagnostic::error_at(
                            with_span,
                            format!("undefined handler: {}", name),
                        ));
                    }
                }

                // Handler arms inherit the inner expression's effect cache so
                // they see the same type param bindings (e.g. State s -> Int).
                self.effect_meta.type_param_cache = inner_effect_cache;

                // Compute answer_ty: infer return clause first if present,
                // since arms need it for resume return type and body unification.
                let answer_ty = if let Some(ret_arm) = return_clause {
                    let saved_env = self.env.clone();
                    if let Some((param_name, param_span)) = ret_arm.params.first() {
                        let param_id = crate::ast::NodeId::fresh();
                        self.env.insert_with_def(
                            param_name.clone(),
                            Scheme {
                                forall: vec![],
                                constraints: vec![],
                                ty: expr_ty.clone(),
                            },
                            param_id,
                        );
                        self.lsp.node_spans.insert(param_id, *param_span);
                        self.lsp.type_at_span.insert(*param_span, expr_ty.clone());
                        self.lsp
                            .definitions
                            .push((param_id, param_name.clone(), *param_span));
                    }
                    let (ret_ty, _effs) = self.infer_expr(&ret_arm.body)?;
                    self.env = saved_env;
                    ret_ty
                } else {
                    expr_ty.clone()
                };

                let mut all_arm_effs = super::EffectRow::empty();
                for arm in arms {
                    let op_sig = self.lookup_effect_op(&arm.op_name, None, arm.span).ok();

                    let saved_env = self.env.clone();
                    let saved_resume = self.resume_type.take();
                    let saved_resume_ret = self.resume_return_type.take();

                    if let Some(ref sig) = op_sig {
                        self.resume_type = Some(sig.return_type.clone());
                        self.resume_return_type = Some(answer_ty.clone());
                        for (i, (param_name, param_span)) in arm.params.iter().enumerate() {
                            let param_ty = if i < sig.params.len() {
                                sig.params[i].1.clone()
                            } else {
                                self.fresh_var()
                            };
                            let param_id = crate::ast::NodeId::fresh();
                            self.env.insert_with_def(
                                param_name.clone(),
                                Scheme {
                                    forall: vec![],
                                    constraints: vec![],
                                    ty: param_ty.clone(),
                                },
                                param_id,
                            );
                            self.lsp.node_spans.insert(param_id, *param_span);
                            self.lsp.type_at_span.insert(*param_span, param_ty);
                            self.lsp
                                .definitions
                                .push((param_id, param_name.clone(), *param_span));
                        }
                    } else {
                        for (param_name, param_span) in &arm.params {
                            let param_ty = self.fresh_var();
                            let param_id = crate::ast::NodeId::fresh();
                            self.env.insert_with_def(
                                param_name.clone(),
                                Scheme {
                                    forall: vec![],
                                    constraints: vec![],
                                    ty: param_ty.clone(),
                                },
                                param_id,
                            );
                            self.lsp.node_spans.insert(param_id, *param_span);
                            self.lsp.type_at_span.insert(*param_span, param_ty);
                            self.lsp
                                .definitions
                                .push((param_id, param_name.clone(), *param_span));
                        }
                    }

                    let (arm_ty, arm_effs) = self.infer_expr(&arm.body)?;
                    // Accumulate arm effects (minus handled) for propagation
                    let unhandled_arm_effs = arm_effs.subtract(&handled);
                    all_arm_effs = all_arm_effs.merge(&unhandled_arm_effs);
                    // Each arm must produce the answer type
                    self.unify_at(&arm_ty, &answer_ty, arm.span)?;

                    self.resume_type = saved_resume;
                    self.resume_return_type = saved_resume_ret;
                    self.env = saved_env;
                }

                Ok((answer_ty, remaining_effs.merge(&all_arm_effs)))
            }
        }
    }
}
