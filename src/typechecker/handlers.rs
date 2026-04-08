use std::collections::HashSet;

use crate::ast::{self, Expr};
use crate::codegen::lower::beam_interop;
use crate::token::Span;

use super::{Checker, Diagnostic, EffectEntry, EffectRow, Type};

impl Checker {
    // --- Handler inference ---

    fn push_unique_effect_entry(entries: &mut Vec<EffectEntry>, entry: EffectEntry) {
        if !entries.iter().any(|seen| seen.same_instantiation(&entry)) {
            entries.push(entry);
        }
    }

    fn expand_used_handler_families_for_warning(
        &self,
        mut used_families: std::collections::HashSet<String>,
        handler: &ast::Handler,
    ) -> std::collections::HashSet<String> {
        let ast::Handler::Inline { named, .. } = handler else {
            return used_families;
        };

        loop {
            let mut changed = false;
            for ann in named {
                let Some(info) = self.handlers.get(&ann.node.name) else {
                    continue;
                };
                if info
                    .effects
                    .iter()
                    .any(|effect| used_families.contains(effect))
                {
                    for need in &info.needs_effects.effects {
                        if used_families.insert(need.name.clone()) {
                            changed = true;
                        }
                    }
                }
            }
            if !changed {
                break;
            }
        }

        used_families
    }

    fn resolve_handled_effect_entries(
        &self,
        handled_families: &HashSet<String>,
        inner_effs: &EffectRow,
        span: Span,
    ) -> Result<Vec<EffectEntry>, Diagnostic> {
        let mut handled_entries = Vec::new();

        for family in handled_families {
            let mut matches = Vec::new();
            for entry in &inner_effs.effects {
                if entry.name == *family
                    && !matches
                        .iter()
                        .any(|seen: &EffectEntry| seen.same_instantiation(entry))
                {
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

    /// Infer the type of a `with` expression: `expr with handler`
    pub(crate) fn infer_with(
        &mut self,
        expr: &Expr,
        handler: &ast::Handler,
        _with_span: Span,
        with_node_id: crate::ast::NodeId,
    ) -> Result<Type, Diagnostic> {
        let handled = self.handler_handled_effects(handler);

        // Check if this with-expression uses handlers that require runtime resource init.
        // Handler names are already canonical at this point (resolve pass ran first).
        let handler_names: Vec<&str> = match handler {
            ast::Handler::Named(name, _) => vec![name.as_str()],
            ast::Handler::Inline { named, .. } => {
                named.iter().map(|ann| ann.node.name.as_str()).collect()
            }
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
        handled_families: HashSet<String>,
        with_node_id: crate::ast::NodeId,
    ) -> Result<Type, Diagnostic> {
        // --- Scope 1: infer the inner expression with isolated effect tracking ---
        let inner_scope = self.enter_scope();
        let saved_effs = self.save_effects();
        let expr_ty = self.infer_expr(expr)?;
        let raw_inner_effs = self.restore_effects(saved_effs);
        let inner_effs = self.sub.apply_effect_row(&raw_inner_effs);
        let inner_result = self.exit_scope(inner_scope);
        let outer_effect_cache = self.effect_meta.type_param_cache.clone();
        let handled_entries =
            self.resolve_handled_effect_entries(&handled_families, &inner_effs, expr.span)?;

        let inner_effect_cache = inner_result.effect_cache;

        // Remaining effects: inner minus handled
        let remaining_effs = inner_effs.subtract_entries(&handled_entries);

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
                        if !handler_info.effects.is_empty()
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
                        if !handler_info.effects.is_empty()
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
            ast::Handler::Inline {
                named,
                arms,
                return_clause,
                ..
            } => {
                let mut used_handled_families: std::collections::HashSet<String> =
                    handled_entries.iter().map(|e| e.name.clone()).collect();
                let mut named_handler_entries = Vec::new();
                for ann in named {
                    let name = &ann.node.name;
                    let name_span = ann.node.span;
                    if !self.handlers.contains_key(name) && self.env.get(name).is_none() {
                        return Err(Diagnostic::error_at(
                            name_span,
                            format!("undefined handler: {}", name),
                        ));
                    }
                    if let Some(entries) = self.handler_effect_entries_from_env(name) {
                        for entry in entries {
                            Self::push_unique_effect_entry(&mut named_handler_entries, entry);
                        }
                    } else if let Some(info) = self.handlers.get(name) {
                        for effect_name in &info.effects {
                            Self::push_unique_effect_entry(
                                &mut named_handler_entries,
                                EffectEntry::unnamed(effect_name.clone(), vec![]),
                            );
                        }
                    }
                }
                for entry in &named_handler_entries {
                    if inner_effs
                        .effects
                        .iter()
                        .any(|inner| inner.same_instantiation(entry))
                    {
                        used_handled_families.insert(entry.name.clone());
                    }
                }
                let mut block_handled_entries = handled_entries.clone();
                for entry in &named_handler_entries {
                    Self::push_unique_effect_entry(&mut block_handled_entries, entry.clone());
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
                    let saved_effs = self.save_effects();
                    if let Some(pat) = ret_arm.params.first() {
                        self.bind_pattern(pat, &answer_ty)?;
                    }
                    let ret_ty = self.infer_expr(&ret_arm.body)?;
                    let raw_ret_effs = self.restore_effects(saved_effs);
                    let ret_effs = self.sub.apply_effect_row(&raw_ret_effs);
                    for entry in &named_handler_entries {
                        if ret_effs
                            .effects
                            .iter()
                            .any(|eff| eff.same_instantiation(entry))
                        {
                            used_handled_families.insert(entry.name.clone());
                        }
                    }
                    let unhandled_ret_effs = ret_effs.subtract_entries(&named_handler_entries);
                    self.emit_effects(&unhandled_ret_effs);
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

                    // Arm body: subtract effects handled by sibling handlers, but NOT
                    // the effect this arm itself handles (re-entrant calls delegate
                    // to an outer handler, not the current one)
                    let saved_effs = self.save_effects();
                    let arm_ty = self.infer_expr(&arm.body)?;
                    let raw_arm_effs = self.restore_effects(saved_effs);
                    let arm_effs = self.sub.apply_effect_row(&raw_arm_effs);
                    for entry in &named_handler_entries {
                        if arm_effs
                            .effects
                            .iter()
                            .any(|eff| eff.same_instantiation(entry))
                        {
                            used_handled_families.insert(entry.name.clone());
                        }
                    }
                    let own_effect = op_sig.as_ref().map(|sig| sig.effect_name.clone());
                    let sibling_handled: Vec<EffectEntry> = block_handled_entries
                        .iter()
                        .filter(|entry| own_effect.as_ref() != Some(&entry.name))
                        .cloned()
                        .collect();
                    let unhandled_arm_effs = arm_effs.subtract_entries(&sibling_handled);
                    self.emit_effects(&unhandled_arm_effs);

                    self.unify_at(&arm_ty, &answer_ty, arm.span)?;

                    // Typecheck optional `finally` block: may use effects from named
                    // handlers' `needs` in this `with` block, but must not introduce new ones.
                    if let Some(ref finally_expr) = arm.finally_block {
                        let saved_effs2 = self.save_effects();
                        let _finally_ty = self.infer_expr(finally_expr)?;
                        let finally_effs = self.restore_effects(saved_effs2);
                        if let Err(e) = self.check_effects_via_row(
                            &finally_effs,
                            &named_needs,
                            &format!("finally block for '{}'", arm.op_name),
                            finally_expr.span,
                        ) {
                            self.collected_diagnostics.push(e);
                        }
                    }

                    self.resume_type = saved_resume;
                    self.resume_return_type = saved_resume_ret;
                    self.effect_meta.type_param_cache = saved_effect_cache;
                    self.env = saved_env;
                }

                // Emit remaining effects from the inner expression, plus named handlers' needs
                // (minus effects handled by sibling handlers in this same block)
                let unhandled_named_needs = named_needs.subtract(&handled_families);
                let final_effs = remaining_effs.merge(&unhandled_named_needs);
                self.emit_effects(&final_effs);

                let used_handled_families =
                    self.expand_used_handler_families_for_warning(used_handled_families, handler);
                if !handled_families.is_empty() {
                    let mut unused = Vec::new();
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
                            && !handler_effects
                                .iter()
                                .any(|e| used_handled_families.contains(e))
                        {
                            unused.extend(handler_effects);
                        }
                    }
                    for arm in arms {
                        if let Some(eff) =
                            self.effect_for_op(&arm.node.op_name, arm.node.qualifier.as_deref())
                            && !used_handled_families.contains(&eff)
                        {
                            unused.push(eff);
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
                Ok(answer_ty)
            }
        }
    }
}
