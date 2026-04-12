use std::collections::HashSet;

use crate::ast::{self, Expr};
use crate::codegen::lower::beam_interop;
use crate::token::Span;

use super::{Checker, Diagnostic, EffectEntry, EffectRow, Type};

impl Checker {
    // --- Handler inference ---

    fn resolve_handled_effect_entries(
        &mut self,
        handled_families: &HashSet<String>,
        inner_effs: &EffectRow,
        span: Span,
    ) -> Result<Vec<EffectEntry>, Diagnostic> {
        let mut handled_entries = Vec::new();

        for family in handled_families {
            let mut matches: Vec<EffectEntry> = Vec::new();
            for entry in &inner_effs.effects {
                if entry.name != *family {
                    continue;
                }

                // Under nested handler semantics, one `with` layer still handles
                // a single effect family. Multiple entries from the same family
                // may appear here only because they were inferred with different
                // fresh vars (for example `Actor a` from a handler need and
                // `Actor msg` from the inner expression). If they can be unified,
                // treat them as one handled instantiation; otherwise keep both so
                // we can report a real multi-instantiation error below.
                let mut merged = false;
                for seen in &mut matches {
                    if self.unify_effect_entry_instantiations(seen, entry).is_ok() {
                        *seen = EffectEntry {
                            name: seen.name.clone(),
                            args: seen.args.iter().map(|arg| self.sub.apply(arg)).collect(),
                        };
                        merged = true;
                        break;
                    }
                }

                if !merged {
                    matches.push(entry.clone());
                }
            }

            if matches.len() > 1 {
                let mut rendered: Vec<String> = matches
                    .iter()
                    .map(|entry| self.prettify_effect_entry(entry))
                    .collect();
                rendered.sort();
                return Err(Diagnostic::error_at(
                    span,
                    format!(
                        "a single `with` cannot handle multiple instantiations of `{}` in the same scope: {}",
                        family.rsplit('.').next().unwrap_or(family),
                        rendered.join(", "),
                    ),
                ));
            }

            if let Some(entry) = matches.into_iter().next() {
                handled_entries.push(entry);
            }
        }

        Ok(handled_entries)
    }

    fn unify_effect_entry_instantiations(
        &mut self,
        a: &EffectEntry,
        b: &EffectEntry,
    ) -> Result<(), Diagnostic> {
        if a.name != b.name || a.args.len() != b.args.len() {
            return Err(Diagnostic::error("effect instantiations differ"));
        }
        let saved_sub = self.sub.clone();
        for (left, right) in a.args.iter().zip(&b.args) {
            if let Err(err) = self.unify(left, right) {
                self.sub = saved_sub;
                return Err(err);
            }
        }
        Ok(())
    }

    /// Infer the type of a `with` expression: `expr with handler`
    pub(crate) fn infer_with(
        &mut self,
        expr: &Expr,
        handler: &ast::Handler,
        _with_span: Span,
        with_node_id: crate::ast::NodeId,
    ) -> Result<Type, Diagnostic> {
        // Check if this with-expression uses handlers that require runtime resource init.
        let handler_names: Vec<String> = match handler {
            ast::Handler::Named(named) => vec![self.resolved_handler_name(named.id, &named.name)],
            ast::Handler::Inline { .. } => handler
                .named_refs()
                .into_iter()
                .map(|h| self.resolved_handler_name(h.id, &h.name))
                .collect(),
        };
        for name in &handler_names {
            if beam_interop::handler_needs_ets_table(name) {
                self.needs_ets_ref_table = true;
            }
            if beam_interop::handler_needs_vec_table(name) {
                self.needs_vec_table = true;
            }
        }

        // Build op_name -> (arm_span, source_module) map for LSP go-to-def
        let arm_stack_entry: std::collections::HashMap<String, (Span, Option<String>)> =
            match handler {
                ast::Handler::Named(named) => {
                    let resolved_name = self.resolved_handler_name(named.id, &named.name);
                    if let Some(def_id) = self.env.def_id(&resolved_name) {
                        let usage_id = crate::ast::NodeId::fresh();
                        self.record_reference(usage_id, named.span, def_id);
                    }
                    self.handlers
                        .get(&resolved_name)
                        .map(|h| {
                            let src = h.source_module.clone();
                            h.arm_spans
                                .iter()
                                .map(|(op, &span)| (op.clone(), (span, src.clone())))
                                .collect()
                        })
                        .unwrap_or_default()
                }
                ast::Handler::Inline { items, .. } => {
                    let mut map = std::collections::HashMap::new();
                    for ann in items {
                        match &ann.node {
                            ast::HandlerItem::Named(named_ref) => {
                                let n = self.resolved_handler_name(named_ref.id, &named_ref.name);
                                if let Some(def_id) = self.env.def_id(&n) {
                                    let usage_id = crate::ast::NodeId::fresh();
                                    self.record_reference(usage_id, _with_span, def_id);
                                }
                                if let Some(h) = self.handlers.get(&n) {
                                    let src = h.source_module.clone();
                                    map.extend(
                                        h.arm_spans
                                            .iter()
                                            .map(|(op, &span)| (op.clone(), (span, src.clone()))),
                                    );
                                }
                            }
                            ast::HandlerItem::Arm(arm) => {
                                map.insert(arm.op_name.clone(), (arm.span, None));
                            }
                            ast::HandlerItem::Return(_) => {}
                        }
                    }
                    map
                }
            };
        self.lsp.with_arm_stacks.push(arm_stack_entry);

        let result = self.infer_with_inner(expr, handler, with_node_id)?;
        self.lsp.with_arm_stacks.pop();

        Ok(result)
    }

    fn infer_with_inner(
        &mut self,
        expr: &Expr,
        handler: &ast::Handler,
        with_node_id: crate::ast::NodeId,
    ) -> Result<Type, Diagnostic> {
        // --- Scope 1: infer the inner expression with isolated effect tracking ---
        let inner_scope = self.enter_scope();
        let saved_effs = self.save_effects();
        let expr_ty = self.infer_expr(expr)?;
        match handler {
            ast::Handler::Named(named) => {
                let resolved_name = self.resolved_handler_name(named.id, &named.name);
                if let Some(def_id) = self.env.def_id(&resolved_name) {
                    let usage_id = crate::ast::NodeId::fresh();
                    self.record_reference(usage_id, named.span, def_id);
                }
            }
            ast::Handler::Inline { .. } => {
                for named_ref in handler.named_refs() {
                    let resolved_name = self.resolved_handler_name(named_ref.id, &named_ref.name);
                    if let Some(def_id) = self.env.def_id(&resolved_name) {
                        let usage_id = crate::ast::NodeId::fresh();
                        self.record_reference(usage_id, named_ref.span, def_id);
                    }
                }
            }
        }
        let handled_families = self.handler_handled_effects(handler);
        let raw_inner_effs = self.restore_effects(saved_effs);
        let inner_effs = self.sub.apply_effect_row(&raw_inner_effs);
        let inner_result = self.exit_scope(inner_scope);
        let outer_effect_cache = self.effect_meta.type_param_cache.clone();
        let handled_entries =
            self.resolve_handled_effect_entries(&handled_families, &inner_effs, expr.span)?;
        let inner_effs = self.sub.apply_effect_row(&inner_effs);

        let inner_effect_cache = inner_result.effect_cache;

        // Remaining effects: inner minus handled
        let remaining_effs = inner_effs.subtract_entries(&handled_entries);

        let with_span = expr.span;
        match handler {
            ast::Handler::Named(named) => {
                let resolved_name = self.resolved_handler_name(named.id, &named.name);
                if !self.handlers.contains_key(&resolved_name) && self.env.get(&resolved_name).is_none() {
                    return Err(Diagnostic::error_at(
                        named.span,
                        format!("undefined handler: {}", named.name),
                    ));
                }
                if let Some(handler_info) = self.handlers.get(&resolved_name).cloned() {
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
                        if handler_info.return_type.is_none()
                            && !handler_info.effects.is_empty()
                            && !handled_entries
                                .iter()
                                .any(|entry| handler_info.effects.contains(&entry.name))
                        {
                            self.collected_diagnostics.push(Diagnostic::warning_at(
                                expr.span,
                                format!(
                                    "expression does not use effects {{{}}}; handler is unnecessary",
                                    handler_info.effects.join(", ")
                                ),
                            ));
                        }
                        Ok(self.sub.apply(&fresh_ret))
                    } else {
                        let final_effs = remaining_effs.merge(&handler_info.needs_effects);
                        self.emit_effects(&final_effs);
                        if handler_info.return_type.is_none()
                            && !handler_info.effects.is_empty()
                            && !handled_entries
                                .iter()
                                .any(|entry| handler_info.effects.contains(&entry.name))
                        {
                            self.collected_diagnostics.push(Diagnostic::warning_at(
                                expr.span,
                                format!(
                                    "expression does not use effects {{{}}}; handler is unnecessary",
                                    handler_info.effects.join(", ")
                                ),
                            ));
                        }
                        Ok(expr_ty)
                    }
                } else {
                    self.emit_effects(&remaining_effs);
                    Ok(expr_ty)
                }
            }
            ast::Handler::Inline { .. } => {
                // After desugaring, Inline handlers contain only Arm and Return
                // items (no Named refs — those are split into their own With layers).
                let answer_ty = expr_ty.clone();

                self.effect_meta.type_param_cache = inner_effect_cache.clone();

                // Return clause: wraps the answer type
                let answer_ty = if let Some(ret_arm) = handler.return_clause() {
                    let saved_env = self.env.clone();
                    let saved_effs = self.save_effects();
                    if let Some(pat) = ret_arm.params.first() {
                        self.bind_pattern(pat, &answer_ty)?;
                    }
                    let ret_ty = self.infer_expr(&ret_arm.body)?;
                    let raw_ret_effs = self.restore_effects(saved_effs);
                    let ret_effs = self.sub.apply_effect_row(&raw_ret_effs);
                    self.emit_effects(&ret_effs);
                    self.env = saved_env;
                    ret_ty
                } else {
                    answer_ty
                };

                // Inline handler arms
                for arm in handler.inline_arms() {
                    let resolved_qualifier = self
                        .resolution
                        .handler_arm_qualifier(arm.id)
                        .or(arm.qualifier.as_deref())
                        .map(|s| s.to_string());
                    let op_sig = self
                        .lookup_effect_op(&arm.op_name, resolved_qualifier.as_deref(), arm.span)
                        .ok();

                    let saved_env = self.env.clone();
                    let saved_resume = self.resume_type.take();
                    let saved_resume_ret = self.resume_return_type.take();
                    let saved_effect_cache = self.effect_meta.type_param_cache.clone();

                    if let Some(ref sig) = op_sig {
                        self.resume_type = Some(sig.return_type.clone());
                        self.resume_return_type = Some(answer_ty.clone());
                        for (i, pat) in arm.params.iter().enumerate() {
                            let param_ty = if i < sig.params.len() {
                                sig.params[i].1.clone()
                            } else {
                                self.fresh_var()
                            };
                            self.bind_pattern(pat, &param_ty)?;
                        }
                    } else {
                        for pat in &arm.params {
                            let param_ty = self.fresh_var();
                            self.bind_pattern(pat, &param_ty)?;
                        }
                    }

                    // Calls to the same effect family inside the arm body
                    // delegate to an outer handler, if one exists.
                    if let Some(ref sig) = op_sig
                        && let Some(outer_mapping) = outer_effect_cache.get(&sig.effect_name)
                    {
                        self.effect_meta
                            .type_param_cache
                            .insert(sig.effect_name.clone(), outer_mapping.clone());
                    }

                    // Arm body effects propagate outward (no sibling subtraction
                    // under nested handler semantics).
                    let saved_effs = self.save_effects();
                    let arm_ty = self.infer_expr(&arm.body)?;
                    let raw_arm_effs = self.restore_effects(saved_effs);
                    let arm_effs = self.sub.apply_effect_row(&raw_arm_effs);
                    self.emit_effects(&arm_effs);

                    self.unify_at(&arm_ty, &answer_ty, arm.span)?;

                    // Typecheck optional `finally` block. Under nested handler
                    // semantics, its effects propagate outward just like the
                    // arm body, so outer handlers may still satisfy them.
                    if let Some(ref finally_expr) = arm.finally_block {
                        let saved_effs2 = self.save_effects();
                        let _finally_ty = self.infer_expr(finally_expr)?;
                        let finally_effs = self.restore_effects(saved_effs2);
                        let finally_effs = self.sub.apply_effect_row(&finally_effs);
                        self.emit_effects(&finally_effs);
                    }

                    self.resume_type = saved_resume;
                    self.resume_return_type = saved_resume_ret;
                    self.effect_meta.type_param_cache = saved_effect_cache;
                    self.env = saved_env;
                }

                // Emit remaining effects from the inner expression
                self.emit_effects(&remaining_effs);

                // Unused handler warning
                let mut unused = Vec::new();
                for arm in handler.inline_arms() {
                    if let Some(eff) = self.effect_for_op(&arm.op_name, arm.qualifier.as_deref())
                        && !handled_entries.iter().any(|e| e.name == eff)
                    {
                        unused.push(eff);
                    }
                }
                if handler.return_clause().is_none() && !unused.is_empty() {
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

                Ok(answer_ty)
            }
        }
    }
}
