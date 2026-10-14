use std::collections::HashSet;

use crate::ast::{self, Expr};
use crate::codegen::lower::beam_interop;
use crate::token::Span;

use super::{Checker, Diagnostic, EffectEntry, EffectRow, Type};

impl Checker {
    // --- Handler inference ---

    /// Decide, for each effect family a `with` layer handles, which
    /// application of it is handled, and make sure nothing inside the handled
    /// computation can perform the family at another type.
    ///
    /// A handler is found by family, so every operation of the family that
    /// the handled computation performs reaches it, whatever the operation's
    /// type argument. Three things are therefore checked per family:
    ///
    /// - If the computation's row names the family, that entry is the one
    ///   handled, and a handler declared for specific arguments
    ///   (`handler for Fail Int`, a `Handler (Fail Int)` value) must agree
    ///   with it.
    /// - An open tail of the row that inference is still free to refine is
    ///   refined to contain the family at the handled arguments, so a
    ///   callback that turns out to perform the family is typed against this
    ///   handler.
    /// - An open tail fixed by a declared signature (`..r`) cannot be
    ///   refined: the caller chooses it. It is accepted only if the signature
    ///   itself names the family next to that tail (`needs {Fail e, ..r}`),
    ///   which obliges every caller to keep `r` consistent with it.
    ///
    /// Returns the handled entries (one per family actually handled).
    fn resolve_handled_effect_entries(
        &mut self,
        handled_families: &HashSet<String>,
        declared_entries: &[EffectEntry],
        inner_effs: &EffectRow,
        span: Span,
    ) -> Result<Vec<EffectEntry>, Diagnostic> {
        let mut handled_entries = Vec::new();
        let mut families: Vec<&String> = handled_families.iter().collect();
        families.sort();

        for family in families {
            let row = self.sub.apply_effect_row(inner_effs);
            let declared = declared_entries
                .iter()
                .find(|entry| entry.name == *family)
                .cloned();
            let named = row.effects.iter().find(|e| e.name == *family).cloned();

            let entry = match (&named, &declared) {
                (Some(named), Some(declared)) => {
                    if self.unify_family(declared, named).is_err() {
                        return Err(self.handler_mismatch(declared, named, span));
                    }
                    named.clone()
                }
                (Some(named), None) => named.clone(),
                (None, Some(declared)) => declared.clone(),
                (None, None) => {
                    let arity = self
                        .effects
                        .get(family)
                        .map(|info| info.type_params.len())
                        .unwrap_or(0);
                    EffectEntry {
                        name: family.clone(),
                        args: (0..arity).map(|_| self.fresh_var()).collect(),
                    }
                }
            };

            // Only an effect with type parameters can be performed at a type
            // its handler was not written for. For any other effect a tail
            // fixed by a signature is left alone, as it always was: the
            // handler may catch operations the tail turns out to perform,
            // while the signature still (harmlessly) forwards them.
            let parameterised = self
                .effects
                .get(family)
                .is_some_and(|info| !info.type_params.is_empty());
            let mut handled = named.is_some();
            for tail in row.tail_var_ids() {
                if let Some(rigid) = self.rigid_row_var_for(tail) {
                    if !parameterised {
                        continue;
                    }
                    // Any declared companion that agrees with the handled
                    // application will do.
                    let mut agreed = false;
                    for companion in rigid.companions.iter().filter(|c| c.name == *family) {
                        let saved = self.sub.clone();
                        if self.unify_family(companion, &entry).is_ok() {
                            agreed = true;
                            break;
                        }
                        self.sub = saved;
                    }
                    if !agreed {
                        return Err(self.rigid_tail_error(&entry, &rigid, span));
                    }
                    handled = true;
                } else if named.is_none() {
                    let fresh = self.fresh_var();
                    self.bind_row_checked(
                        tail,
                        EffectRow {
                            effects: vec![entry.clone()],
                            tails: vec![fresh],
                        },
                    )
                    .map_err(|e| e.with_span(span))?;
                    handled = true;
                }
            }

            if handled {
                handled_entries.push(EffectEntry {
                    name: entry.name.clone(),
                    args: entry.args.iter().map(|arg| self.sub.apply(arg)).collect(),
                });
            }
        }

        Ok(handled_entries)
    }

    /// If `tail` is (or has been unified with) a row variable fixed by a
    /// declared signature, return what the signature says about it.
    pub(crate) fn rigid_row_var_for(&self, tail: u32) -> Option<super::RigidRowVar> {
        let mut found: Option<super::RigidRowVar> = None;
        for (var, info) in &self.rigid_row_vars {
            let resolved = self.sub.apply_effect_row(&EffectRow {
                effects: vec![],
                tails: vec![Type::Var(*var)],
            });
            if !resolved.tail_var_ids().contains(&tail) {
                continue;
            }
            let entry = found.get_or_insert_with(|| super::RigidRowVar {
                name: info.name.clone(),
                companions: vec![],
            });
            entry.companions.extend(info.companions.iter().cloned());
            // Effects the variable has itself been unified with are named
            // wherever the variable is.
            entry.companions.extend(resolved.effects.iter().cloned());
        }
        if found.is_none() {
            // The row of an open-row trait method called on an abstract type
            // (`..a` for `a: Foo`): the impl chosen by the caller supplies it.
            for var in self.trait_forward_row_vars.keys() {
                if self.sub.apply(&Type::Var(*var)) == Type::Var(tail) {
                    let name = self
                        .trait_state
                        .where_bound_var_names
                        .get(var)
                        .cloned()
                        .unwrap_or_else(|| "a".to_string());
                    found = Some(super::RigidRowVar {
                        name,
                        companions: vec![],
                    });
                    break;
                }
            }
        }
        found
    }

    fn rigid_tail_error(
        &self,
        entry: &EffectEntry,
        rigid: &super::RigidRowVar,
        span: Span,
    ) -> Diagnostic {
        let family = entry.name.rsplit('.').next().unwrap_or(&entry.name);
        let params = self
            .effects
            .get(&entry.name)
            .map(|info| info.type_params.len())
            .unwrap_or(0);
        let example = if params == 0 {
            family.to_string()
        } else {
            format!(
                "{} {}",
                family,
                (0..params)
                    .map(|i| ((b'e' + i as u8) as char).to_string())
                    .collect::<Vec<_>>()
                    .join(" ")
            )
        };
        Diagnostic::error_at(
            span,
            format!(
                "cannot handle `{family}` here: the handled expression has the open effect row \
                 `..{row}`, which is chosen by the caller and might itself contain `{family}` \
                 (at any type). Those operations would reach this handler too. Name the effect \
                 in the type that carries `..{row}`, e.g. `needs {{{example}, ..{row}}}`, so \
                 that every caller agrees on the one `{family}` this handler handles",
                row = rigid.name,
            ),
        )
    }

    fn handler_mismatch(
        &self,
        handler: &EffectEntry,
        performed: &EffectEntry,
        span: Span,
    ) -> Diagnostic {
        let family = handler.name.rsplit('.').next().unwrap_or(&handler.name);
        Diagnostic::error_at(
            span,
            format!(
                "this handler handles `{}`, but the handled expression performs `{}`. A handler \
                 for `{family}` receives every `{family}` operation performed inside it, \
                 whatever its type argument; to keep two instances apart, declare one of them \
                 with `neweffect`",
                self.prettify_effect_entry(handler),
                self.prettify_effect_entry(performed),
            ),
        )
    }

    /// The effects named by a `Handler (...)` type, as row entries.
    fn handler_type_entries(&mut self, ty: &Type) -> Vec<EffectEntry> {
        let resolved = self.sub.apply(ty);
        let Type::Con(name, args) = resolved else {
            return vec![];
        };
        if name != super::canonicalize_type_name("Handler") {
            return vec![];
        }
        args.iter()
            .filter_map(|arg| match self.sub.apply(arg) {
                Type::Con(effect_name, effect_args) => Some(EffectEntry {
                    name: self.normalize_handler_effect_name(effect_name),
                    args: effect_args,
                }),
                _ => None,
            })
            .collect()
    }

    /// Infer the type of a `with` expression: `expr with handler`
    ///
    /// The handler clause is checked in the scope of the wrapped block:
    /// `{ let db = connect (); ... } with db` names a handler the block bound
    /// (docs/handler-bindings.md), and inline arms and `return` clauses see
    /// the block's values the same way. That scope ends with the `with`
    /// expression as a whole.
    pub(crate) fn infer_with(
        &mut self,
        expr: &Expr,
        handler: &ast::Handler,
        with_span: Span,
        with_node_id: crate::ast::NodeId,
    ) -> Result<Type, Diagnostic> {
        let saved_env = self.env.clone();
        let mut wrapped_handlers = Vec::new();
        let result = self.infer_with_open(
            expr,
            handler,
            with_span,
            with_node_id,
            &mut wrapped_handlers,
        );
        self.env = saved_env;
        self.restore_shadowed_handlers(wrapped_handlers);
        result
    }

    /// `infer_with` leaving the wrapped block's scope open, for a `with` that
    /// is itself wrapped by another (`{ ... } with {a, b}` is one `with`
    /// layer per handler) or followed by a `finally` block.
    pub(crate) fn infer_with_open(
        &mut self,
        expr: &Expr,
        handler: &ast::Handler,
        _with_span: Span,
        with_node_id: crate::ast::NodeId,
        wrapped_handlers: &mut super::infer::ShadowedHandlers,
    ) -> Result<Type, Diagnostic> {
        // Check if this with-expression uses handlers that require runtime resource init.
        let handler_names: Vec<String> = match handler {
            ast::Handler::Named(named) => vec![self.resolved_handler_name(named.id, &named.name)],
            ast::Handler::Inline { .. } => handler
                .named_refs()
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

        let result = self.infer_with_inner(expr, handler, with_node_id, wrapped_handlers)?;
        self.lsp.with_arm_stacks.pop();

        Ok(result)
    }

    fn infer_with_inner(
        &mut self,
        expr: &Expr,
        handler: &ast::Handler,
        with_node_id: crate::ast::NodeId,
        wrapped_handlers: &mut super::infer::ShadowedHandlers,
    ) -> Result<Type, Diagnostic> {
        // --- Scope 1: infer the inner expression with isolated effect tracking ---
        let inner_scope = self.enter_scope();
        let saved_effs = self.save_effects();
        let expr_ty = self.infer_expr_keeping_block_scope(expr, wrapped_handlers)?;
        // What the handler is installed around includes the effects of any
        // open-row trait method the expression used as a value.
        self.resolve_open_row_refs(super::open_row_refs::OpenRowFinish::Keep);
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
        // Leave the inner scope before anything below can fail.
        let raw_inner_effs = self.restore_effects(saved_effs);
        let inner_result = self.exit_scope(inner_scope);
        let handled_families = self.handler_handled_effects(handler);
        // A named handler declaration is a scheme: its type variables are
        // instantiated once per `with`, shared by the effects it handles,
        // its return clause and its `needs`.
        let named_handler_info = match handler {
            ast::Handler::Named(named) => {
                let resolved_name = self.resolved_handler_name(named.id, &named.name);
                self.handlers.get(&resolved_name).cloned()
            }
            ast::Handler::Inline { .. } => None,
        };
        let handler_mapping: std::collections::HashMap<u32, Type> = named_handler_info
            .as_ref()
            .map(|info| {
                info.forall
                    .iter()
                    .map(|&id| (id, self.fresh_var()))
                    .collect()
            })
            .unwrap_or_default();
        let explicitly_handled: Vec<EffectEntry> = match handler {
            ast::Handler::Named(named) => {
                if let Some(info) = &named_handler_info {
                    info.effect_entries
                        .iter()
                        .map(|entry| EffectEntry {
                            name: entry.name.clone(),
                            args: entry
                                .args
                                .iter()
                                .map(|arg| Self::replace_vars(arg, &handler_mapping))
                                .collect(),
                        })
                        .collect()
                } else {
                    // A handler value in scope (a parameter, say): its type
                    // says what it handles.
                    let resolved_name = self.resolved_handler_name(named.id, &named.name);
                    match self.env.get(&resolved_name).map(|scheme| scheme.ty.clone()) {
                        Some(ty) => {
                            // What it handles must be known here: this is
                            // where the handled effects are checked against
                            // the expression and removed from its row.
                            let entries = self.handler_type_entries(&ty);
                            let known = match self.sub.apply(&ty) {
                                Type::Con(name, args) => {
                                    name == super::canonicalize_type_name("Handler")
                                        && !args.is_empty()
                                        && entries.len() == args.len()
                                }
                                _ => false,
                            };
                            if !known {
                                return Err(Diagnostic::error_at(
                                    named.span,
                                    format!(
                                        "cannot tell which effects `{}` handles: its type is not \
                                         a known `Handler (...)` at this point. Give it a type \
                                         annotation such as `Handler (Fail String)`",
                                        named.name
                                    ),
                                ));
                            }
                            entries
                        }
                        None => Vec::new(),
                    }
                }
            }
            ast::Handler::Inline { .. } => Vec::new(),
        };
        let inner_effs = self.normalize_row_at(&raw_inner_effs, expr.span)?;
        let outer_effect_cache = self.effect_meta.type_param_cache.clone();
        let handled_entries = self.resolve_handled_effect_entries(
            &handled_families,
            &explicitly_handled,
            &inner_effs,
            expr.span,
        )?;
        let inner_effs = self.sub.apply_effect_row(&inner_effs);

        let inner_effect_cache = inner_result.effect_cache;

        // Remaining effects: inner minus handled. Open tails stay: a handler
        // cannot discharge effects it cannot name.
        let remaining_effs = inner_effs.subtract_entries(&handled_entries);

        let with_span = expr.span;
        match handler {
            ast::Handler::Named(named) => {
                let resolved_name = self.resolved_handler_name(named.id, &named.name);
                if !self.handlers.contains_key(&resolved_name)
                    && self.env.get(&resolved_name).is_none()
                {
                    return Err(Diagnostic::error_at(
                        named.span,
                        format!("undefined handler: {}", named.name),
                    ));
                }
                if let Some(handler_info) = self.handlers.get(&resolved_name).cloned() {
                    if let Some((param_ty, ret_ty)) = &handler_info.return_type {
                        let mapping = handler_mapping.clone();
                        let fresh_param = Self::replace_vars(param_ty, &mapping);
                        let fresh_ret = Self::replace_vars(ret_ty, &mapping);
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
                                        .map(|t| Self::replace_vars(t, &mapping))
                                        .collect(),
                                })
                                .collect(),
                            tails: vec![],
                        };
                        let final_effs =
                            self.merge_rows(&remaining_effs, &fresh_needs, with_span)?;
                        self.emit_effects(&final_effs, with_span)?;
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
                        let final_effs = self.merge_rows(
                            &remaining_effs,
                            &handler_info.needs_effects,
                            with_span,
                        )?;
                        self.emit_effects(&final_effs, with_span)?;
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
                    self.emit_effects(&remaining_effs, with_span)?;
                    Ok(expr_ty)
                }
            }
            ast::Handler::Inline { .. } => {
                // After desugaring, Inline handlers contain only Arm and Return
                // items (no Named refs — those are split into their own With layers).
                self.effect_meta.type_param_cache = inner_effect_cache.clone();

                // Return clause: wraps the answer type
                let (ret_ty, ret_effs) = if let Some(ret_arm) = handler.return_clause() {
                    let saved_env = self.env.clone();
                    let saved_effs = self.save_effects();
                    if let Some(pat) = ret_arm.params.first() {
                        self.bind_pattern(pat, &expr_ty)?;
                    }
                    let ret_ty = self.infer_expr(&ret_arm.body)?;
                    let raw_ret_effs = self.restore_effects(saved_effs);
                    let ret_effs = self.sub.apply_effect_row(&raw_ret_effs);
                    self.emit_effects(&ret_effs, ret_arm.body.span)?;
                    self.env = saved_env;
                    (ret_ty, ret_effs)
                } else {
                    (expr_ty.clone(), EffectRow::empty())
                };

                // What `resume` returns and performs. Resuming runs the rest
                // of the handled computation under this handler, then the
                // `return` clause, so it performs what this `with` does not
                // handle, the `return` clause's effects, and (since a later
                // operation runs an arm inside it) the arms' effects:
                // `ρ_arm`, which takes them below. A function value an arm
                // builds around `resume` performs all that when called, so
                // the answer type's arrows get room for it (slack tails).
                // Slack that nothing needed is closed again at the end.
                let vars_before = self.next_var;
                let answer_ty = self.open_answer_spine(&ret_ty, with_node_id);
                let arm_slack = self.new_slack(super::unify::Slack::Arm, with_node_id);
                let mut resume_row = self.merge_rows(&remaining_effs, &ret_effs, with_span)?;
                resume_row.tails.push(arm_slack);
                let resume_row = self.normalize_row_at(&resume_row, with_span)?;
                self.resume_rows.insert(with_node_id, resume_row.clone());
                let mut arms_effs = EffectRow::empty();

                // Inline handler arms
                for arm in handler.inline_arms() {
                    let resolved_qualifier = self
                        .resolution
                        .handler_arm(arm.id)
                        .map(|resolved| resolved.effect.as_str())
                        .or(arm.qualifier.as_deref())
                        .map(|s| s.to_string());
                    let op_sig = self
                        .lookup_effect_op(&arm.op_name, resolved_qualifier.as_deref(), arm.span)
                        .ok();

                    let saved_env = self.env.clone();
                    let saved_resume = self.resume_type.take();
                    let saved_resume_ret = self.resume_return_type.take();
                    let saved_resume_effs = self.resume_effects.take();
                    let saved_effect_cache = self.effect_meta.type_param_cache.clone();

                    // The type variables the operation's signature uses as
                    // effect arguments (`e` in a callback's `needs {Fail e}`)
                    // are chosen by whoever performs the operation. The
                    // effect's own parameters are not: the application of
                    // the effect being handled says what they are.
                    let arm_effect_arg_vars: Vec<(u32, String)> = match op_sig {
                        Some(ref sig) => {
                            let mut own_params = Vec::new();
                            if let Some(mapping) =
                                self.effect_meta.type_param_cache.get(&sig.effect_name)
                            {
                                for ty in mapping.values() {
                                    super::unify::collect_free_vars(ty, &mut own_params);
                                }
                            }
                            self.op_sig_effect_arg_vars(sig)
                                .into_iter()
                                .filter(|(var, _)| !own_params.contains(var))
                                .collect()
                        }
                        None => Vec::new(),
                    };

                    let mut arm_rigid_rows = std::collections::HashMap::new();
                    if let Some(ref sig) = op_sig {
                        // The operation's signature is a declared type the
                        // arm implements as written: its row variables are
                        // chosen by whoever performs the operation.
                        for (_, param_ty) in &sig.params {
                            Self::collect_rigid_row_vars(param_ty, &[], &mut arm_rigid_rows);
                        }
                        Self::collect_rigid_row_vars(&sig.return_type, &[], &mut arm_rigid_rows);
                        Self::collect_rigid_row_vars_in_row(&sig.needs, &[], &mut arm_rigid_rows);
                        self.rigid_row_vars
                            .extend(arm_rigid_rows.iter().map(|(id, info)| (*id, info.clone())));
                    }
                    if let Some(ref sig) = op_sig {
                        // Pin the op's effect type parameters (e.g. `e` in
                        // `Fail e`) to the concrete instantiation actually being
                        // handled (`Fail String`), so the arm's payload pattern
                        // gets the real type. The effect can reach this `with`
                        // through a function call rather than a direct op call,
                        // in which case the per-scope type-param cache has no
                        // entry and the op would otherwise instantiate with a
                        // free var — letting the arm use the payload at the wrong
                        // type and crash at runtime.
                        if let Some(effect_info) = self.effects.get(&sig.effect_name).cloned()
                            && let Some(entry) = handled_entries
                                .iter()
                                .find(|e| e.name == sig.effect_name)
                                .cloned()
                        {
                            self.lsp.effect_at_node.insert(arm.id, entry.clone());
                            for (param_id, arg) in
                                effect_info.type_params.iter().zip(entry.args.iter())
                            {
                                let var = self
                                    .effect_meta
                                    .type_param_cache
                                    .get(&sig.effect_name)
                                    .and_then(|m| m.get(param_id))
                                    .cloned()
                                    .unwrap_or(Type::Var(*param_id));
                                self.unify_at(&var, arg, arm.span)?;
                            }
                        }
                        self.resume_type = Some(sig.return_type.clone());
                        self.resume_return_type = Some(answer_ty.clone());
                        self.resume_effects = Some(resume_row.clone());
                        for (i, pat) in arm.params.iter().enumerate() {
                            let param_ty = if i < sig.params.len() {
                                sig.params[i].1.clone()
                            } else {
                                self.fresh_var()
                            };
                            self.bind_pattern(pat, &param_ty)?;
                        }
                        // Bring the op's own `where` constraints into scope as
                        // assumptions so the arm body may use the trait on the
                        // op's abstract type var (mirrors the named-handler path).
                        self.add_op_constraint_where_bounds(&sig.constraints);
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
                    // A `finally` block sees what the arm body's block binds,
                    // so with one present that block's scope stays open until
                    // the `finally` block has been checked.
                    let mut body_handlers = Vec::new();
                    let arm_ty = if arm.finally_block.is_some() {
                        self.infer_expr_keeping_block_scope(&arm.body, &mut body_handlers)?
                    } else {
                        self.infer_expr(&arm.body)?
                    };
                    let raw_arm_effs = self.restore_effects(saved_effs);
                    let arm_effs = self.sub.apply_effect_row(&raw_arm_effs);
                    self.emit_effects(&arm_effs, arm.span)?;
                    arms_effs = self.merge_rows(&arms_effs, &arm_effs, arm.span)?;

                    // Arm result against the handled expression's answer type.
                    self.coerce_at(&arm_ty, &answer_ty, arm.span, Some(&arm.body))?;
                    self.check_rigid_row_vars_abstract(
                        &arm_rigid_rows,
                        &format!("operation `{}`", arm.op_name),
                        arm.span,
                        true,
                    )?;
                    self.check_effect_arg_vars_abstract(
                        &arm_effect_arg_vars,
                        &[],
                        true,
                        &format!("operation `{}`", arm.op_name),
                        arm.span,
                    )?;
                    self.check_effect_arg_vars_stay_inside(
                        &arm_effect_arg_vars,
                        &arm_effs.effects,
                        Some(&answer_ty),
                        &format!("operation `{}`", arm.op_name),
                        arm.span,
                    )?;

                    // Typecheck optional `finally` block. Under nested handler
                    // semantics, its effects propagate outward just like the
                    // arm body, so outer handlers may still satisfy them.
                    if let Some(ref finally_expr) = arm.finally_block {
                        let saved_effs2 = self.save_effects();
                        let _finally_ty = self.infer_expr(finally_expr)?;
                        let finally_effs = self.restore_effects(saved_effs2);
                        let finally_effs = self.sub.apply_effect_row(&finally_effs);
                        self.emit_effects(&finally_effs, finally_expr.span)?;
                        arms_effs = self.merge_rows(&arms_effs, &finally_effs, arm.span)?;
                    }
                    self.restore_shadowed_handlers(body_handlers);

                    self.resume_type = saved_resume;
                    self.resume_return_type = saved_resume_ret;
                    self.resume_effects = saved_resume_effs;
                    self.effect_meta.type_param_cache = saved_effect_cache;
                    self.env = saved_env;
                }

                // The arms' own effects are part of what resuming performs
                // (`ρ_arm` takes them); then the slack this `with` made, and
                // whatever is left of it, is closed.
                self.coerce_at(
                    &Self::row_as_fun(arms_effs),
                    &Self::row_as_fun(resume_row),
                    with_span,
                    None,
                )?;
                self.close_slack(with_node_id, vars_before, with_span)?;

                // Emit remaining effects from the inner expression
                self.emit_effects(&remaining_effs, with_span)?;

                // Unused handler warning
                let mut unused = Vec::new();
                for arm in handler.inline_arms() {
                    if let Some(eff) = self
                        .resolution
                        .handler_arm(arm.id)
                        .map(|resolved| resolved.effect.clone())
                        .or_else(|| self.effect_for_op(&arm.op_name, arm.qualifier.as_deref()))
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

                Ok(self.sub.apply(&answer_ty))
            }
        }
    }

    /// `ty` with a fresh slack tail (`Slack::Answer`) added to the row of
    /// each arrow along its result spine: the type of a `with` whose arms
    /// may return functions that resume.
    pub(crate) fn open_answer_spine(&mut self, ty: &Type, with: crate::ast::NodeId) -> Type {
        match self.sub.apply(ty) {
            Type::Fun(param, ret, mut row) => {
                let ret = self.open_answer_spine(&ret, with);
                row.tails
                    .push(self.new_slack(super::unify::Slack::Answer, with));
                let _ = self.normalize_row(&row);
                Type::Fun(param, Box::new(ret), row)
            }
            other => other,
        }
    }

    pub(crate) fn new_slack(&mut self, kind: super::unify::Slack, with: crate::ast::NodeId) -> Type {
        let var = self.fresh_var();
        if let Type::Var(id) = var {
            self.slack_rows.insert(id, (kind, with));
        }
        var
    }

    /// A row as the row of a function, for comparing two rows through
    /// `coerce_at`.
    pub(crate) fn row_as_fun(row: EffectRow) -> Type {
        Type::Fun(Box::new(Type::unit()), Box::new(Type::unit()), row)
    }

    /// Close the slack `with` made to the empty row: an instantiation, so
    /// every inclusion established so far still holds, and the answer type
    /// keeps exactly what some arm needed. Inference variables made while
    /// the `with` was checked (from `vars_before` on) that slack was bound
    /// to are closed too, so none of them is left open in the answer type.
    pub(crate) fn close_slack(
        &mut self,
        with: crate::ast::NodeId,
        vars_before: u32,
        span: Span,
    ) -> Result<(), Diagnostic> {
        let mine: Vec<u32> = self
            .slack_rows
            .iter()
            .filter(|(_, (_, owner))| *owner == with)
            .map(|(id, _)| *id)
            .collect();
        let reached = self.sub.apply_effect_row(&EffectRow {
            effects: vec![],
            tails: mine.iter().map(|id| Type::Var(*id)).collect(),
        });
        for tail in reached.tail_var_ids() {
            // A declared row variable is not ours to close: one of the
            // operation's (an arm's callback) still stands for what the
            // callback performs where the operation was called.
            if mine.contains(&tail) || (tail >= vars_before && !self.is_rigid_tail(tail)) {
                self.bind_row_checked(tail, EffectRow::empty())
                    .map_err(|e| e.with_span(span))?;
            }
        }
        for id in mine {
            self.slack_rows.remove(&id);
        }
        Ok(())
    }
}
