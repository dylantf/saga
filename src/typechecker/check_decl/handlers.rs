use super::*;

impl Checker {
    /// Phase 1: Register effect name and type params (stub with empty ops).
    /// Called first for ALL effects so that forward references between effects
    /// (e.g. Process referencing Actor) resolve during op signature processing.
    pub(crate) fn register_effect_stub(&mut self, name: &str, effect_type_params: &[TypeParam]) {
        let mut type_param_ids = Vec::new();
        for tp in effect_type_params {
            let var = self.fresh_var_of_kind(tp.kind);
            let id = match &var {
                Type::Var(id) => *id,
                _ => unreachable!(),
            };
            type_param_ids.push(id);
        }
        let key = if let Some(module) = &self.current_module {
            format!("{}.{}", module, name)
        } else {
            name.into()
        };
        self.effects.insert(
            key.clone(),
            EffectDefInfo {
                type_params: type_param_ids,
                ops: vec![],
                op_spans: std::collections::HashMap::new(),
                source_module: self.current_module.clone(),
            },
        );
        self.type_param_kinds
            .insert(key, effect_type_params.iter().map(|p| p.kind).collect());
        self.type_arity
            .insert(name.into(), effect_type_params.len());
        if let Some(module) = &self.current_module {
            self.type_param_kinds.insert(
                format!("{}.{}", module, name),
                effect_type_params.iter().map(|p| p.kind).collect(),
            );
            self.type_arity
                .insert(format!("{}.{}", module, name), effect_type_params.len());
        }
    }


    /// Phase 2: Fill in effect op signatures (after all effect stubs are registered).
    pub(crate) fn register_effect_ops(
        &mut self,
        name: &str,
        effect_type_params: &[TypeParam],
        operations: &[&ast::EffectOp],
    ) -> Result<(), Diagnostic> {
        let key = if let Some(module) = &self.current_module {
            format!("{}.{}", module, name)
        } else {
            name.to_string()
        };
        // Retrieve the type param IDs created during stub registration.
        let type_param_ids = self
            .effects
            .get(&key)
            .map(|info| info.type_params.clone())
            .unwrap_or_default();

        let shared_params: Vec<(String, u32)> = effect_type_params
            .iter()
            .zip(type_param_ids.iter())
            .map(|(tp, &id)| (tp.name.clone(), id))
            .collect();

        let mut ops = Vec::new();
        let mut op_spans = std::collections::HashMap::new();
        for op in operations {
            let mut params_list = shared_params.clone();
            let param_types: Vec<(String, Type)> = op
                .params
                .iter()
                .map(|(label, texpr)| {
                    (
                        label.clone(),
                        self.convert_user_type_expr(texpr, &mut params_list),
                    )
                })
                .collect();
            let return_type = self.convert_user_type_expr(&op.return_type, &mut params_list);
            // Convert the op's own `needs` clause to an EffectRow
            let needs = if !op.effects.is_empty() || !op.effect_row_var.is_empty() {
                let effect_refs: Vec<EffectEntry> = op
                    .effects
                    .iter()
                    .map(|e| {
                        let args = self.convert_effect_ref_args(e, &mut params_list);
                        let resolved_name = self.resolved_effect_name(e.id, &e.name);
                        EffectEntry::unnamed(resolved_name, args)
                    })
                    .collect();
                let tails: Vec<Type> = op
                    .effect_row_var
                    .iter()
                    .map(|(rv_name, _)| {
                        let id =
                            if let Some((_, id)) = params_list.iter().find(|(n, _)| n == rv_name) {
                                *id
                            } else {
                                let id = self.next_var;
                                self.next_var += 1;
                                params_list.push((rv_name.clone(), id));
                                id
                            };
                        Type::Var(id)
                    })
                    .collect();
                EffectRow {
                    effects: effect_refs,
                    tails,
                }
            } else {
                EffectRow::empty()
            };
            let mut constraints = Vec::new();
            for bound in &op.where_clause {
                for tr in &bound.traits {
                    let resolved = self.resolved_trait_name_at(tr.id, &tr.name);
                    self.lsp.type_references.push((tr.span, resolved));
                }
                let Some(var_id) = params_list
                    .iter()
                    .find(|(n, _)| *n == bound.type_var)
                    .map(|(_, id)| *id)
                else {
                    return Err(Diagnostic::error_at(
                        op.span,
                        format!(
                            "where clause references unknown type variable '{}' in effect operation '{}'",
                            bound.type_var, op.name
                        ),
                    ));
                };
                // Remember the source name of this op type variable so handler
                // arm bodies (and elaboration) can name the dictionary param
                // consistently (`__dict_<Trait>_<var>`). The var id is globally
                // unique to this op, so this never collides with other bindings.
                self.trait_state
                    .where_bound_var_names
                    .insert(var_id, bound.type_var.clone());
                for tr in &bound.traits {
                    let resolved_trait = self.resolved_trait_name_at(tr.id, &tr.name);
                    self.validate_trait_bound_kind(
                        &resolved_trait,
                        &bound.type_var,
                        var_id,
                        tr.span,
                    )?;
                    let extra_types: Vec<Type> = tr
                        .type_args
                        .iter()
                        .map(|te| self.convert_user_type_expr(te, &mut params_list))
                        .collect();
                    constraints.push((resolved_trait, var_id, extra_types));
                }
            }
            op_spans.insert(op.name.clone(), op.span);
            ops.push(EffectOpSig {
                name: op.name.clone(),
                effect_name: name.to_string(),
                params: param_types,
                return_type,
                needs,
                constraints,
            });
        }
        self.scope_map
            .register_effect_ops(&key, ops.iter().map(|op| op.name.as_str()));
        if let Some(info) = self.effects.get_mut(&key) {
            info.ops = ops;
            info.op_spans = op_spans;
        }
        Ok(())
    }


    /// Register an effect operation's own `where` constraints as where-bound
    /// assumptions, so a handler arm body implementing that operation may use
    /// the trait on the operation's abstract type variable.
    pub(crate) fn add_op_constraint_where_bounds(
        &mut self,
        constraints: &[(String, u32, Vec<Type>)],
    ) {
        for (trait_name, var_id, extra_types) in constraints {
            self.trait_state
                .where_bounds
                .entry(*var_id)
                .or_default()
                .insert(trait_name.clone());
            if !extra_types.is_empty() {
                self.trait_state
                    .where_bound_trait_args
                    .insert((*var_id, trait_name.clone()), extra_types.clone());
            }
        }
    }


    pub(crate) fn register_handler(&mut self, decl: &ast::Decl) -> Result<(), Diagnostic> {
        let ast::Decl::HandlerDef {
            id: def_id,
            name,
            name_span,
            body,
            span,
            ..
        } = decl
        else {
            unreachable!("register_handler called with non-HandlerDef");
        };
        let ast::HandlerBody {
            effects: effect_names,
            needs,
            where_clause,
            arms,
            return_clause,
        } = body;
        let return_clause = return_clause.as_deref();
        // Save and clear effect/field tracking for this handler body
        let body_scope = self.enter_scope();

        // Build type param bindings from handler's effect refs.
        // E.g. `handler counter for State Int` with effect State s:
        //   creates mapping {s_var_id -> Int}
        // Also track type variable names -> var IDs for where clause binding.
        let mut handler_type_mapping: std::collections::HashMap<u32, Type> =
            std::collections::HashMap::new();
        let mut type_var_params: Vec<(String, u32)> = Vec::new();
        for effect_ref in effect_names {
            self.record_effect_ref(effect_ref);
            let resolved_effect_name = self.resolved_effect_name(effect_ref.id, &effect_ref.name);
            if let Some(info) = self.effects.get(&resolved_effect_name) {
                let info = info.clone();
                for (i, &param_id) in info.type_params.iter().enumerate() {
                    if let Some(type_arg_expr) = effect_ref.type_args.get(i) {
                        let expected_kind = self.var_kind(param_id);
                        let concrete_ty = self.convert_type_expr_kinded(
                            type_arg_expr,
                            &mut type_var_params,
                            expected_kind,
                        );
                        let concrete_ty = self.canonicalize_handler_effect_types(concrete_ty);
                        handler_type_mapping.insert(param_id, concrete_ty);
                    }
                }
            } else {
                self.collected_diagnostics.push(Diagnostic::error_at(
                    effect_ref.span,
                    format!("undefined effect: {}", effect_ref.name),
                ));
            }
        }

        // Register where clause bounds on handler type params.
        // E.g. `handler show_store for Store a where {a: Show}` registers Show bound on `a`'s var.
        for bound in where_clause {
            if let Some((_, var_id)) = type_var_params.iter().find(|(n, _)| n == &bound.type_var) {
                self.trait_state
                    .where_bound_var_names
                    .insert(*var_id, bound.type_var.clone());
                for tr in &bound.traits {
                    let resolved_req = self.resolved_trait_name_at(tr.id, &tr.name);
                    if let Err(diag) = self.validate_trait_bound_kind(
                        &resolved_req,
                        &bound.type_var,
                        *var_id,
                        tr.span,
                    ) {
                        self.collected_diagnostics.push(diag);
                    }
                    self.lsp
                        .type_references
                        .push((tr.span, resolved_req.clone()));
                    self.trait_state
                        .where_bounds
                        .entry(*var_id)
                        .or_default()
                        .insert(resolved_req);
                }
            } else {
                self.collected_diagnostics.push(Diagnostic::error_at(
                    *span,
                    format!(
                        "where clause references unknown type variable '{}' in handler '{}'",
                        bound.type_var, name
                    ),
                ));
            }
        }

        let saved_outer_named = self.outer_named_type_vars.clone();
        for (name, var_id) in &type_var_params {
            self.outer_named_type_vars.insert(name.clone(), *var_id);
        }

        // Fresh type variable for the handler's answer type.
        // Arms unify against this; the return clause (if any) constrains it later.
        let answer_ty = self.fresh_var();

        // Save effects and start fresh for handler body checking
        let handler_saved_effs = self.save_effects();

        // Build effect row from handler's `needs` clause so `finally` blocks can
        // use these effects (they're already provided by the handler's caller).
        let needs_row = self.effect_row_from_refs(needs);

        // Validate that each arm's operation belongs to the handler's declared effects
        let mut seen_ops: std::collections::HashSet<String> = std::collections::HashSet::new();
        let mut arm_spans: std::collections::HashMap<String, Span> =
            std::collections::HashMap::new();
        for arm_ann in arms {
            let arm = &arm_ann.node;
            if !seen_ops.insert(arm.op_name.clone()) {
                return Err(Diagnostic::error_at(
                    arm.span,
                    format!("duplicate handler arm for operation '{}'", arm.op_name),
                ));
            }
            let mut belongs_to_declared = false;
            let mut matched_op: Option<EffectOpSig> = None;
            for effect_ref in effect_names {
                let resolved_effect_name =
                    self.resolved_effect_name(effect_ref.id, &effect_ref.name);
                if let Some(info) = self.effects.get(&resolved_effect_name)
                    && let Some(op) = info.ops.iter().find(|o| o.name == arm.op_name)
                {
                    if belongs_to_declared {
                        return Err(Diagnostic::error_at(
                            arm.span,
                            format!(
                                "ambiguous handler arm '{}': operation exists in multiple effects",
                                arm.op_name
                            ),
                        ));
                    }
                    belongs_to_declared = true;
                    // Record arm span -> (op definition span, source module) for LSP go-to-def (level 2)
                    if let Some(&op_span) = info.op_spans.get(&arm.op_name) {
                        self.lsp
                            .handler_arm_targets
                            .insert(arm.span, (op_span, info.source_module.clone()));
                    }
                    arm_spans.insert(arm.op_name.clone(), arm.span);
                    // Apply handler type bindings to specialize the op signature
                    let specialized = EffectOpSig {
                        name: op.name.clone(),
                        effect_name: op.effect_name.clone(),
                        params: op
                            .params
                            .iter()
                            .map(|(label, t)| {
                                (label.clone(), Self::replace_vars(t, &handler_type_mapping))
                            })
                            .collect(),
                        return_type: Self::replace_vars(&op.return_type, &handler_type_mapping),
                        needs: op.needs.clone(),
                        constraints: op
                            .constraints
                            .iter()
                            .map(|(trait_name, var_id, extra_types)| {
                                let mapped_id = match handler_type_mapping.get(var_id) {
                                    Some(Type::Var(id)) => *id,
                                    _ => *var_id,
                                };
                                let mapped_extras = extra_types
                                    .iter()
                                    .map(|ty| Self::replace_vars(ty, &handler_type_mapping))
                                    .collect();
                                (trait_name.clone(), mapped_id, mapped_extras)
                            })
                            .collect(),
                    };
                    matched_op = Some(specialized);
                }
            }
            if !belongs_to_declared {
                return Err(Diagnostic::error_at(
                    arm.span,
                    format!(
                        "handler arm '{}' is not an operation of {}",
                        arm.op_name,
                        effect_names
                            .iter()
                            .map(|e| format!("'{}'", e.name))
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                ));
            }

            let op_sig = matched_op.unwrap();

            // Bind op params and set resume context, then check body
            let saved_env = self.env.clone();
            let saved_resume = self.resume_type.take();
            let saved_resume_ret = self.resume_return_type.take();
            self.resume_type = Some(op_sig.return_type.clone());
            self.resume_return_type = Some(answer_ty.clone());

            for (i, pat) in arm.params.iter().enumerate() {
                let param_ty = if i < op_sig.params.len() {
                    op_sig.params[i].1.clone()
                } else {
                    self.fresh_var()
                };
                self.bind_pattern(pat, &param_ty)?;
            }

            // The operation's own `where` constraints (e.g. `set : a -> a -> Unit
            // where {a: PgType}`) hold as *assumptions* inside the arm body: the
            // handler is implementing the op, so it may use the trait on the
            // op's abstract type var just like a function body may use its own
            // where-bounds. Register them as where-bounds so trait method calls
            // in the body discharge against them. Like the handler's own
            // `where_clause` bounds above, these persist until the global
            // `check_pending_constraints` pass (which snapshots `where_bounds`);
            // they key off the op signature's own var ids, which are globally
            // unique and never appear at call sites (those instantiate fresh).
            self.add_op_constraint_where_bounds(&op_sig.constraints);

            let body_ty = self.infer_expr(&arm.body)?;
            if let Err(e) = self.unify(&answer_ty, &body_ty) {
                self.collected_diagnostics.push(e.with_span(arm.span));
            }

            // Typecheck optional `finally` block: may use the handler's `needs` effects
            // (they're already provided by the caller) but must not introduce new ones.
            if let Some(ref finally_expr) = arm.finally_block {
                let saved_effs = self.save_effects();
                let _finally_ty = self.infer_expr(finally_expr)?;
                let finally_effs = self.restore_effects(saved_effs);
                if let Err(e) = self.check_effects_via_row(
                    &finally_effs,
                    &needs_row,
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

        // Check the return clause body if present, capturing the param var and return type
        let handler_return_type = if let Some(rc) = return_clause {
            let saved_env = self.env.clone();
            let saved_resume = self.resume_type.take();
            let param_ty = self.fresh_var();
            let param_var_id = match &param_ty {
                Type::Var(id) => *id,
                _ => unreachable!(),
            };
            if let Some(pat) = rc.params.first() {
                self.bind_pattern(pat, &param_ty)?;
            }
            let ret_ty = self.infer_expr(&rc.body)?;
            // Constrain answer_ty to match the return clause's body type
            if let Err(e) = self.unify(&answer_ty, &ret_ty) {
                self.collected_diagnostics.push(e.with_span(rc.body.span));
            }
            self.resume_type = saved_resume;
            self.env = saved_env;
            // Freeze by applying sub: resolves internal handler vars but leaves
            // polymorphic vars (handler type params, answer type) as free Var nodes.
            let frozen_param = self.sub.apply(&Type::Var(param_var_id));
            let frozen_ret = self.sub.apply(&ret_ty);
            Some((frozen_param, frozen_ret))
        } else {
            // No return clause: the handler doesn't transform the result type.
            // Freeze answer_ty so usage sites get a template to instantiate.
            let frozen = self.sub.apply(&answer_ty);
            Some((frozen.clone(), frozen))
        };

        // Collect accumulated handler effects and restore outer scope
        let all_handler_effs = self.restore_effects(handler_saved_effs);
        let _scope_result = self.exit_scope(body_scope);
        let declared_effects: std::collections::HashSet<String> = needs
            .iter()
            .map(|e| {
                self.resolve_effect(&e.name)
                    .and_then(|info| {
                        let short = e.name.rsplit('.').next().unwrap_or(&e.name);
                        info.source_module
                            .as_ref()
                            .map(|m| format!("{}.{}", m, short))
                    })
                    .unwrap_or_else(|| {
                        if let Some(m) = &self.current_module {
                            format!("{}.{}", m, e.name)
                        } else {
                            e.name.clone()
                        }
                    })
            })
            .collect();

        let body_effects: std::collections::HashSet<String> = all_handler_effs
            .effects
            .iter()
            .map(|e| e.name.clone())
            .collect();
        if !body_effects.is_empty() || !declared_effects.is_empty() {
            let err_span = arms.first().map(|a| a.node.span).unwrap_or(*span);
            let undeclared: Vec<String> = body_effects
                .difference(&declared_effects)
                .cloned()
                .collect();
            if !undeclared.is_empty() {
                let mut sorted = undeclared;
                sorted.sort();
                let label = format!("handler '{}'", name);
                if declared_effects.is_empty() {
                    return Err(Diagnostic::error_at(
                        err_span,
                        format!(
                            "{} uses effects {{{}}} but has no 'needs' declaration",
                            label,
                            sorted.join(", ")
                        ),
                    ));
                } else {
                    return Err(Diagnostic::error_at(
                        err_span,
                        format!(
                            "{} uses effects {{{}}} not declared in its 'needs' clause",
                            label,
                            sorted.join(", ")
                        ),
                    ));
                }
            }
        }

        // Check that all operations from the handled effects are covered
        if !self.allow_bodyless_annotations {
            let handled_ops: std::collections::HashSet<&str> =
                arms.iter().map(|a| a.node.op_name.as_str()).collect();
            for effect_ref in effect_names {
                if let Some(info) = self.resolve_effect(&effect_ref.name) {
                    let missing: Vec<_> = info
                        .ops
                        .iter()
                        .filter(|op| !handled_ops.contains(op.name.as_str()))
                        .map(|op| op.name.as_str())
                        .collect();
                    if !missing.is_empty() {
                        self.collected_diagnostics.push(Diagnostic::error_at(
                            effect_ref.span,
                            format!(
                                "handler '{}' is missing {} from effect '{}'",
                                name,
                                missing.join(", "),
                                effect_ref.name,
                            ),
                        ));
                    }
                }
            }
        }

        // Collect free vars from frozen return type and needs effects as forall (polymorphic per usage).
        let mut forall = if let Some((ref param_ty, ref ret_ty)) = handler_return_type {
            let mut vars = Vec::new();
            crate::typechecker::collect_free_vars(param_ty, &mut vars);
            crate::typechecker::collect_free_vars(ret_ty, &mut vars);
            vars
        } else {
            vec![]
        };
        for entry in &all_handler_effs.effects {
            for t in &entry.args {
                crate::typechecker::collect_free_vars(t, &mut forall);
            }
        }

        // Build where_constraints map: (effect_name, param_index) -> trait constraints.
        // Links where clause type vars back to their position in the effect's type param list.
        let mut where_constraints: crate::typechecker::HandlerWhereConstraints =
            std::collections::HashMap::new();
        for bound in where_clause {
            if let Some((_, var_id)) = type_var_params.iter().find(|(n, _)| n == &bound.type_var) {
                // Find which effect and param index this var corresponds to
                for effect_ref in effect_names {
                    if let Some(info) = self.resolve_effect(&effect_ref.name) {
                        let canonical_effect =
                            self.resolved_effect_name(effect_ref.id, &effect_ref.name);
                        for (i, &param_id) in info.type_params.iter().enumerate() {
                            if let Some(mapped_ty) = handler_type_mapping.get(&param_id)
                                && matches!(mapped_ty, Type::Var(id) if *id == *var_id)
                            {
                                let entry = where_constraints
                                    .entry((canonical_effect.clone(), i))
                                    .or_default();
                                for tr in &bound.traits {
                                    let resolved_trait = self
                                        .resolve_trait_name(&tr.name)
                                        .unwrap_or_else(|| tr.name.clone());
                                    let extra_var_ids: Vec<u32> = tr
                                        .type_args
                                        .iter()
                                        .filter_map(|te| match te {
                                            crate::ast::TypeExpr::Var { name, .. } => {
                                                type_var_params
                                                    .iter()
                                                    .find(|(n, _)| n == name)
                                                    .map(|(_, id)| *id)
                                            }
                                            _ => None,
                                        })
                                        .collect();
                                    entry.push((resolved_trait, extra_var_ids));
                                }
                            }
                        }
                    }
                }
            }
        }

        // Canonicalize effect names so they match canonical names in effect rows.
        let canonical_effects: Vec<String> = effect_names
            .iter()
            .map(|e| {
                self.resolve_effect(&e.name)
                    .and_then(|info| {
                        let short = e.name.rsplit('.').next().unwrap_or(&e.name);
                        info.source_module
                            .as_ref()
                            .map(|m| format!("{}.{}", m, short))
                    })
                    .unwrap_or_else(|| {
                        if let Some(m) = &self.current_module {
                            format!("{}.{}", m, e.name)
                        } else {
                            e.name.clone()
                        }
                    })
            })
            .collect();
        let info = HandlerInfo {
            effects: canonical_effects,
            return_type: handler_return_type,
            needs_effects: all_handler_effs,
            forall,
            arm_spans,
            where_constraints,
            source_module: self.current_module.clone(),
        };
        self.handlers.insert(name.into(), info.clone());
        if let Some(module) = &self.current_module {
            self.handlers.insert(format!("{}.{}", module, name), info);
        }

        // Build Handler type from the effects this handler handles.
        // E.g. `handler h for Log` -> Con("Handler", [Con("Log", [])])
        // E.g. `handler h for State Int` -> Con("Handler", [Con("State", [Int])])
        let handler_effect_types: Vec<Type> = effect_names
            .iter()
            .map(|e| {
                let type_args: Vec<Type> = self.convert_effect_ref_args(e, &mut vec![]);
                Type::Con(self.canonical_effect_name(&e.name), type_args)
            })
            .collect();
        let handler_ty = Type::Con(
            crate::typechecker::canonicalize_type_name("Handler").into(),
            handler_effect_types,
        );

        // Put the handler name in the env so it can be referenced
        self.env.insert_with_def(
            name.into(),
            Scheme {
                forall: vec![],
                constraints: vec![],
                ty: handler_ty,
            },
            *def_id,
        );
        self.outer_named_type_vars = saved_outer_named;
        self.lsp.node_spans.insert(*def_id, *name_span);

        Ok(())
    }

    // --- Trait constraint checking ---

}
