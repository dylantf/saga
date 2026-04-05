use std::collections::HashSet;

use crate::ast::{self, Expr};
use crate::token::Span;

use super::{Checker, Diagnostic, EffectRow, Scheme, Type};

impl Checker {
    // --- Handler inference ---

    /// Infer the type of a `with` expression: `expr with handler`
    pub(crate) fn infer_with(
        &mut self,
        expr: &Expr,
        handler: &ast::Handler,
        _with_span: Span,
        with_node_id: crate::ast::NodeId,
    ) -> Result<Type, Diagnostic> {
        let handled = self.handler_handled_effects(handler);

        // Build op_name -> (arm_span, source_module) map for LSP go-to-def
        let arm_stack_entry: std::collections::HashMap<String, (Span, Option<String>)> =
            match handler {
                ast::Handler::Named(name, handler_span) => {
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
                    for ann in named {
                        let n = &ann.node.name;
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
                        map.insert(arm.node.op_name.clone(), (arm.node.span, None));
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
    ) -> Result<Type, Diagnostic> {
        // --- Scope 1: infer the inner expression with isolated effect tracking ---
        let inner_scope = self.enter_scope();
        let saved_effs = self.save_effects();
        let expr_ty = self.infer_expr(expr)?;
        let inner_effs = self.restore_effects(saved_effs);
        let inner_result = self.exit_scope(inner_scope);

        // Unnecessary handler check.
        // Named handlers (bundles) only warn when ALL their effects are unused.
        // Inline arms warn per-unused-effect.
        if !handled.is_empty() {
            let used: std::collections::HashSet<&String> =
                inner_effs.effects.iter().map(|e| &e.name).collect();
            let mut unused = Vec::new();

            match handler {
                ast::Handler::Named(name, _) => {
                    // Single named handler: warn only if none of its effects are used
                    let handler_effects: Vec<String> = self
                        .handlers
                        .get(name)
                        .map(|h| h.effects.to_vec())
                        .or_else(|| {
                            self.handler_effects_from_env(name)
                                .map(|e| e.into_iter().collect())
                        })
                        .unwrap_or_default();
                    if !handler_effects.is_empty()
                        && !handler_effects.iter().any(|e| used.contains(e))
                    {
                        unused.extend(handler_effects);
                    }
                }
                ast::Handler::Inline { named, arms, .. } => {
                    // Named refs within inline block: warn per-handler when all unused
                    for ann in named {
                        let handler_effects: Vec<String> = self
                            .handlers
                            .get(&ann.node.name)
                            .map(|h| h.effects.to_vec())
                            .or_else(|| {
                                self.handler_effects_from_env(&ann.node.name)
                                    .map(|e| e.into_iter().collect())
                            })
                            .unwrap_or_default();
                        if !handler_effects.is_empty()
                            && !handler_effects.iter().any(|e| used.contains(e))
                        {
                            unused.extend(handler_effects);
                        }
                    }
                    // Inline arms: warn per-unused-effect
                    for arm in arms {
                        if let Some(eff) =
                            self.effect_for_op(&arm.node.op_name, arm.node.qualifier.as_deref())
                            && !used.contains(&eff)
                        {
                            unused.push(eff);
                        }
                    }
                }
            }

            if !unused.is_empty() {
                unused.sort();
                unused.dedup();
                self.collected_diagnostics.push(Diagnostic::warning_at(
                    expr.span,
                    format!(
                        "expression does not use effects {{{}}}; handler is unnecessary",
                        unused.join(", ")
                    ),
                ));
            }
        }

        let inner_effect_cache = inner_result.effect_cache;

        // Remaining effects: inner minus handled
        let remaining_effs = inner_effs.subtract(&handled);

        let with_span = expr.span;
        match handler {
            ast::Handler::Named(name, name_span) => {
                if !self.handlers.contains_key(name) && self.env.get(name).is_none() {
                    return Err(Diagnostic::error_at(
                        *name_span,
                        format!("undefined handler: {}", name),
                    ));
                }
                if let Some(handler_info) = self.handlers.get(name).cloned() {
                    if let Some((param_ty, ret_ty)) = &handler_info.return_type {
                        let mapping: std::collections::HashMap<u32, Type> = handler_info
                            .forall
                            .iter()
                            .map(|&id| (id, self.fresh_var()))
                            .collect();
                        let fresh_param = self.replace_vars(param_ty, &mapping);
                        let fresh_ret = self.replace_vars(ret_ty, &mapping);
                        self.unify_at(&fresh_param, &expr_ty, with_span)?;

                        for ((effect_name, param_idx), trait_constraints) in
                            &handler_info.where_constraints
                        {
                            if let Some(effect_info) = self.effects.get(effect_name).cloned()
                                && let Some(&param_var_id) = effect_info.type_params.get(*param_idx)
                            {
                                let ty = if let Some(cache) = inner_effect_cache.get(effect_name)
                                    && let Some(cached_ty) = cache.get(&param_var_id)
                                {
                                    self.sub.apply(cached_ty)
                                } else {
                                    self.sub.apply(&Type::Var(param_var_id))
                                };
                                for (trait_name, extra_var_ids) in trait_constraints {
                                    // Map extra type arg var IDs through the fresh var mapping
                                    let extra_types: Vec<Type> = extra_var_ids
                                        .iter()
                                        .map(|id| {
                                            let mapped =
                                                mapping.get(id).cloned().unwrap_or(Type::Var(*id));
                                            self.sub.apply(&mapped)
                                        })
                                        .collect();
                                    self.trait_state.pending_constraints.push((
                                        trait_name.clone(),
                                        extra_types,
                                        ty.clone(),
                                        with_span,
                                        with_node_id,
                                    ));
                                }
                            }
                        }

                        // Merge handler's needs effects into remaining, with fresh vars applied
                        let fresh_needs = EffectRow {
                            effects: handler_info
                                .needs_effects
                                .effects
                                .iter()
                                .map(|entry| super::EffectEntry {
                                    name: entry.name.clone(),
                                    args: entry
                                        .args
                                        .iter()
                                        .map(|t| self.replace_vars(t, &mapping))
                                        .collect(),
                                })
                                .collect(),
                            tail: None,
                        };
                        let final_effs = remaining_effs.merge(&fresh_needs);
                        self.emit_effects(&final_effs);
                        Ok(self.sub.apply(&fresh_ret))
                    } else {
                        let final_effs = remaining_effs.merge(&handler_info.needs_effects);
                        self.emit_effects(&final_effs);
                        Ok(expr_ty)
                    }
                } else {
                    self.emit_effects(&remaining_effs);
                    Ok(expr_ty)
                }
            }
            ast::Handler::Inline {
                named,
                arms,
                return_clause,
                ..
            } => {
                for ann in named {
                    let name = &ann.node.name;
                    let name_span = ann.node.span;
                    if !self.handlers.contains_key(name) && self.env.get(name).is_none() {
                        return Err(Diagnostic::error_at(
                            name_span,
                            format!("undefined handler: {}", name),
                        ));
                    }
                }

                let mut answer_ty = expr_ty.clone();

                self.effect_meta.type_param_cache = inner_effect_cache.clone();

                // Apply named handlers' return type transformations and merge their needs_effects
                let mut named_needs = EffectRow::empty();
                for ann in named {
                    let name = &ann.node.name;
                    if let Some(handler_info) = self.handlers.get(name).cloned() {
                        let mapping: std::collections::HashMap<u32, Type> = handler_info
                            .forall
                            .iter()
                            .map(|&id| (id, self.fresh_var()))
                            .collect();

                        if let Some((param_ty, ret_ty)) = &handler_info.return_type {
                            let fresh_param = self.replace_vars(param_ty, &mapping);
                            let fresh_ret = self.replace_vars(ret_ty, &mapping);
                            self.unify_at(&fresh_param, &answer_ty, with_span)?;
                            answer_ty = self.sub.apply(&fresh_ret);
                        }

                        // Apply where_constraints from the named handler
                        for ((effect_name, param_idx), trait_constraints) in
                            &handler_info.where_constraints
                        {
                            if let Some(effect_info) = self.effects.get(effect_name).cloned()
                                && let Some(&param_var_id) = effect_info.type_params.get(*param_idx)
                            {
                                let ty = if let Some(cache) = inner_effect_cache.get(effect_name)
                                    && let Some(cached_ty) = cache.get(&param_var_id)
                                {
                                    self.sub.apply(cached_ty)
                                } else {
                                    self.sub.apply(&Type::Var(param_var_id))
                                };
                                for (trait_name, extra_var_ids) in trait_constraints {
                                    let extra_types: Vec<Type> = extra_var_ids
                                        .iter()
                                        .map(|id| {
                                            let mapped =
                                                mapping.get(id).cloned().unwrap_or(Type::Var(*id));
                                            self.sub.apply(&mapped)
                                        })
                                        .collect();
                                    self.trait_state.pending_constraints.push((
                                        trait_name.clone(),
                                        extra_types,
                                        ty.clone(),
                                        with_span,
                                        with_node_id,
                                    ));
                                }
                            }
                        }

                        // Merge handler's needs_effects with fresh vars applied
                        let fresh_needs = EffectRow {
                            effects: handler_info
                                .needs_effects
                                .effects
                                .iter()
                                .map(|entry| super::EffectEntry {
                                    name: entry.name.clone(),
                                    args: entry
                                        .args
                                        .iter()
                                        .map(|t| self.replace_vars(t, &mapping))
                                        .collect(),
                                })
                                .collect(),
                            tail: None,
                        };
                        named_needs = named_needs.merge(&fresh_needs);
                    }
                }

                let answer_ty = if let Some(ret_arm) = return_clause {
                    let saved_env = self.env.clone();
                    if let Some((param_name, param_span)) = ret_arm.params.first() {
                        let param_id = crate::ast::NodeId::fresh();
                        self.env.insert_with_def(
                            param_name.clone(),
                            Scheme {
                                forall: vec![],
                                constraints: vec![],
                                ty: answer_ty.clone(),
                            },
                            param_id,
                        );
                        self.lsp.node_spans.insert(param_id, *param_span);
                        self.lsp.type_at_span.insert(*param_span, answer_ty.clone());
                        self.lsp
                            .definitions
                            .push((param_id, param_name.clone(), *param_span));
                    }
                    // Return clause effects accumulate on the outer scope
                    let ret_ty = self.infer_expr(&ret_arm.body)?;
                    self.env = saved_env;
                    ret_ty
                } else {
                    answer_ty
                };

                for arm in arms {
                    let arm = &arm.node;
                    let op_sig = self
                        .lookup_effect_op(&arm.op_name, arm.qualifier.as_deref(), arm.span)
                        .ok();

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

                    // Arm body: subtract effects handled by sibling handlers, but NOT
                    // the effect this arm itself handles (re-entrant calls delegate
                    // to an outer handler, not the current one)
                    let saved_effs = self.save_effects();
                    let arm_ty = self.infer_expr(&arm.body)?;
                    let arm_effs = self.restore_effects(saved_effs);
                    let own_effect = op_sig.as_ref().map(|sig| sig.effect_name.clone());
                    let sibling_handled: HashSet<String> = handled
                        .iter()
                        .filter(|e| own_effect.as_ref() != Some(e))
                        .cloned()
                        .collect();
                    let unhandled_arm_effs = arm_effs.subtract(&sibling_handled);
                    self.emit_effects(&unhandled_arm_effs);

                    self.unify_at(&arm_ty, &answer_ty, arm.span)?;

                    // Typecheck optional `finally` block: effects must be self-contained
                    if let Some(ref finally_expr) = arm.finally_block {
                        let saved_effs2 = self.save_effects();
                        let _finally_ty = self.infer_expr(finally_expr)?;
                        let finally_effs = self.restore_effects(saved_effs2);
                        if let Err(e) = self.check_effects_via_row(
                            &finally_effs,
                            &EffectRow::empty(),
                            &format!("finally block for '{}'", arm.op_name),
                            finally_expr.span,
                        ) {
                            self.collected_diagnostics.push(e);
                        }
                    }

                    self.resume_type = saved_resume;
                    self.resume_return_type = saved_resume_ret;
                    self.env = saved_env;
                }

                // Emit remaining effects from the inner expression, plus named handlers' needs
                // (minus effects handled by sibling handlers in this same block)
                let unhandled_named_needs = named_needs.subtract(&handled);
                let final_effs = remaining_effs.merge(&unhandled_named_needs);
                self.emit_effects(&final_effs);
                Ok(answer_ty)
            }
        }
    }
}
