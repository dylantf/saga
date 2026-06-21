use super::*;

impl Checker {
    /// Check a group of function clauses that share the same name.
    /// Handles recursion (pre-binds name) and multi-clause pattern matching.
    pub(crate) fn check_fun_clauses(
        &mut self,
        name: &str,
        clauses: &[&Decl],
        fun_var: &Type,
        annotation: FunctionAnnotation<'_>,
        where_constraints: &[(String, u32, Vec<Type>)],
    ) -> Result<(), Diagnostic> {
        let annotation_span = annotation.span;
        // All clauses must have the same arity
        let arity = match clauses[0] {
            Decl::FunBinding { params, .. } => params.len(),
            _ => unreachable!(),
        };
        let declared_effect_row = (arity == 0).then_some(annotation.effect_row).flatten();
        let annotation = annotation.ty;

        let result_ty = self.fresh_var();
        let param_types: Vec<Type> = (0..arity).map(|_| self.fresh_var()).collect();

        // If there's a type annotation, unify param/result types with it upfront
        // so annotation constraints guide inference (important for polymorphic recursion).
        // Also unify the pre-bound var so recursive calls see the correct type.
        if let Some(ann_ty) = annotation {
            let mut ann_current = ann_ty.clone();
            // Collect effect rows from each arrow in the annotation so we can
            // preserve them in the pre-type (including row variables like ..e).
            let mut ann_effect_rows = Vec::new();
            for param_ty in &param_types {
                match ann_current {
                    Type::Fun(ann_param, ann_ret, ann_row) => {
                        self.unify(param_ty, &ann_param)?;
                        ann_effect_rows.push(ann_row);
                        ann_current = *ann_ret;
                    }
                    _ => break,
                }
            }
            self.unify(&result_ty, &ann_current)?;

            // Build the function type from annotation-constrained params and unify
            // with pre-bound var. Use the annotation's effect rows to preserve row
            // variables (..e) instead of creating pure arrows that would cause the
            // row variable to be bound to empty during later unification.
            let mut pre_ty = result_ty.clone();
            for (i, param_ty) in param_types.iter().rev().enumerate() {
                let row_idx = param_types.len() - 1 - i;
                if let Some(row) = ann_effect_rows.get(row_idx) {
                    pre_ty = Type::Fun(Box::new(param_ty.clone()), Box::new(pre_ty), row.clone());
                } else {
                    pre_ty = Type::arrow(param_ty.clone(), pre_ty);
                }
            }
            self.unify(fun_var, &pre_ty)?;
        }

        // Register where clause bounds on type variable IDs
        for (trait_name, var_id, extra_types) in where_constraints {
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

        // Snapshot pending constraints so we can partition new ones after body checking
        let constraints_before = self.trait_state.pending_constraints.len();
        let mut returned_handler_info: Option<crate::typechecker::HandlerInfo> = None;

        // Expose the function signature's named type params to nested
        // `convert_type_expr` calls inside the body, so an inline ascription
        // like `(Proxy : Proxy n)` in `fun f : Proxy n -> ... where {n : KnownSymbol}`
        // resolves `n` to the signature's `n` instead of minting a fresh var.
        // Without this, the body silently picks the wrong dict at runtime.
        let saved_outer_named = std::mem::take(&mut self.outer_named_type_vars);
        if let Some(params) = self.fun_type_param_vars.get(name).cloned() {
            for (pname, pid) in params {
                self.outer_named_type_vars.insert(pname, pid);
            }
        }

        // Save and clear effect tracking and field candidate tracking for this function body
        let body_scope = self.enter_scope();

        // Pre-populate effect type param cache from annotation constraints (e.g. needs {State Int})
        if let Some(constraints) = self.effect_meta.fun_type_constraints.get(name).cloned() {
            for (effect_name, concrete_types) in &constraints {
                if let Some(info) = self.effects.get(effect_name).cloned() {
                    let mapping: std::collections::HashMap<u32, Type> = info
                        .type_params
                        .iter()
                        .zip(concrete_types.iter())
                        .map(|(&param_id, ty)| (param_id, ty.clone()))
                        .collect();
                    self.effect_meta
                        .type_param_cache
                        .insert(effect_name.clone(), mapping);
                }
            }
        }

        // Save effects and start fresh for this function body
        let saved_trait_forward = std::mem::take(&mut self.trait_forward_row_vars);
        let saved_effs = self.save_effects();
        for clause in clauses {
            let Decl::FunBinding {
                params,
                guard,
                body,
                span,
                ..
            } = clause
            else {
                unreachable!()
            };

            if params.len() != arity {
                return Err(Diagnostic::error_at(
                    *span,
                    format!(
                        "clause for '{}' has {} params, expected {}",
                        name,
                        params.len(),
                        arity
                    ),
                ));
            }

            let saved_env = self.env.clone();
            let saved_handlers = self.handlers.clone();

            for (pat, ty) in params.iter().zip(param_types.iter()) {
                self.bind_pattern(pat, ty)?;
            }

            if let Some(guard) = guard {
                if let Some(span) = crate::typechecker::find_effect_call(guard) {
                    return Err(Diagnostic::error_at(
                        span,
                        "Effect calls are not allowed in guard expressions".to_string(),
                    ));
                }
                let guard_saved = self.save_effects();
                let guard_ty = self.infer_expr(guard)?;
                self.restore_effects(guard_saved);
                self.unify_at(&guard_ty, &Type::bool(), guard.span)?;
            }

            let body_ty = if annotation.is_some() {
                self.infer_expr_against(body, &result_ty)?
            } else {
                self.infer_expr(body)?
            };
            if returned_handler_info.is_none() {
                returned_handler_info = self.extract_handler_info(body);
            }
            self.unify_at(&result_ty, &body_ty, body.span)?;

            self.env = saved_env;
            self.handlers = saved_handlers;
        }
        // Collect accumulated effects and restore outer scope
        let raw_all_body_effs = self.restore_effects(saved_effs);
        let all_body_effs = self.sub.apply_effect_row(&raw_all_body_effs);

        // Absorption (boundary half): when a function directly calls a callback
        // parameter like `f ()` in `run_state init f = (f (), init)`, the callee's
        // effect row is emitted to the accumulator. But those effects belong to the
        // *caller* of run_state, not run_state itself. We subtract effects declared
        // on any callback parameter types.
        //
        // There is a second absorption site in infer.rs App (call-site half) that
        // handles the inverse case: passing a lambda to a HOF like `try_it (fun () -> ...)`.
        // Both are needed because they fire at different points in inference:
        // - Call-site: lambda effects propagate immediately during lambda inference,
        //   before the boundary runs. Only the App knows the HOF's parameter type.
        // - Boundary: direct callback calls emit effects from the callee's type.
        //   Only the boundary knows which params are callback parameters.
        let mut absorbed = std::collections::HashSet::new();
        for pt in &param_types {
            let resolved = self.sub.apply(pt);
            crate::typechecker::collect_callback_effects(&resolved, &mut absorbed);
        }
        // Collect row variable IDs from callback parameters' open effect rows.
        // These represent unknown effects that must be propagated via `needs`.
        let mut callback_row_vars = std::collections::HashSet::new();
        for pt in &param_types {
            let resolved = self.sub.apply(pt);
            fn collect_row_vars(ty: &Type, out: &mut std::collections::HashSet<u32>) {
                if let Type::Fun(_, ret, row) = ty {
                    for tail in &row.tails {
                        if let Type::Var(id) = tail {
                            out.insert(*id);
                        }
                    }
                    collect_row_vars(ret, out);
                }
            }
            collect_row_vars(&resolved, &mut callback_row_vars);
        }
        // Effects declared on a callback parameter must be handled by the HOF:
        // either via an internal `with` block (in which case they were already
        // subtracted from `all_body_effs` during `with` inference) or by
        // declaring them in the function's own `needs` row (forward to caller).
        // Without either, the lowerer has no source for the handler at the
        // point the callback is invoked. Detect this here so the user gets a
        // typechecker error instead of a codegen ICE.
        if let Some(ann) = annotation {
            let declared_row_for_check = declared_effect_row
                .map(|row| self.sub.apply_effect_row(row))
                .or_else(|| innermost_effect_row(&self.sub.apply(ann)))
                .unwrap_or_else(EffectRow::empty);
            let declared_names: std::collections::HashSet<String> = declared_row_for_check
                .effects
                .iter()
                .map(|e| e.name.clone())
                .collect();
            let mut unhandled: Vec<String> = absorbed
                .iter()
                .filter(|eff| {
                    all_body_effs.effects.iter().any(|e| &e.name == *eff)
                        && !declared_names.contains(*eff)
                })
                .cloned()
                .collect();
            if !unhandled.is_empty() {
                unhandled.sort();
                let err_span = annotation_span.unwrap_or_else(|| match clauses[0] {
                    Decl::FunBinding { span, .. } => *span,
                    _ => unreachable!(),
                });
                return Err(Diagnostic::error_at(
                    err_span,
                    format!(
                        "`{}` calls a callback parameter whose declared effect{} {{{}}} {} not handled; \
                         either wrap the callback call in `with`, or add `needs {{{}}}` to the annotation \
                         to forward the effect{} to the caller",
                        name,
                        if unhandled.len() == 1 { "" } else { "s" },
                        unhandled.join(", "),
                        if unhandled.len() == 1 { "is" } else { "are" },
                        unhandled.join(", "),
                        if unhandled.len() == 1 { "" } else { "s" },
                    ),
                ));
            }
        }

        // No boundary subtraction: `all_body_effs` already reflects exactly what
        // this function performs. Calling a callback parameter (`f ()`) emits the
        // callback's effects via the application; an internal `with` discharges
        // them at its boundary; anything left is genuinely forwarded and belongs
        // in this function's row. Subtracting the callback's *declared* effects
        // here used to clobber the function's own/forwarded uses of the same
        // effect (the definition-side twin of the call-site absorption bug), and
        // then `call_site_absorbed` had to mute the resulting bogus "unused
        // effect" warnings. Both are gone. (`absorbed` is still computed above —
        // it drives the "callback effect neither handled nor forwarded" error.)

        // Check exhaustiveness of function clause patterns (multi-column Maranget)
        if clauses.len() > 1
            || clauses.iter().any(|c| {
                if let Decl::FunBinding { params, .. } = c {
                    params.iter().any(|p| {
                        !matches!(
                            p,
                            crate::ast::Pat::Var { .. } | crate::ast::Pat::Wildcard { .. }
                        )
                    })
                } else {
                    false
                }
            })
        {
            self.check_fun_exhaustiveness(name, clauses, &param_types)?;
        }

        // Check effect requirements against declared needs via row comparison.
        // all_body_effs was accumulated on self.effect_row during body inference.
        let scope_result = self.exit_scope(body_scope);
        let body_field_candidates = scope_result.field_candidates;

        let declared_row = declared_effect_row
            .map(|row| self.sub.apply_effect_row(row))
            .or_else(|| annotation.and_then(|ann| innermost_effect_row(&self.sub.apply(ann))))
            .unwrap_or_else(EffectRow::empty);

        // A callback parameter with an open effect row (..e) represents
        // unknown effects that can't be handled with `with` — they must be
        // propagated via `needs {..e}` on the function's own annotation, and
        // the row variable must be the SAME one (connected). Every open tail
        // on a callback parameter must be forwarded: forwarding only some of
        // them (e.g. declaring `needs {..a}` while a second callback carries
        // `..b`) would silently drop `..b`'s effects from the signature even
        // though the body still requires them.
        if annotation.is_some() && !callback_row_vars.is_empty() {
            // A callback tail is satisfied if the declared row has a tail that
            // resolves to the same root. Tails that have already resolved to a
            // concrete (closed) row carry no unknown effects, so they don't
            // need forwarding.
            let unpropagated: Vec<u32> = callback_row_vars
                .iter()
                .copied()
                .filter(|&cb_id| {
                    let cb_resolved = self.sub.apply(&Type::Var(cb_id));
                    if !matches!(cb_resolved, Type::Var(_)) {
                        return false;
                    }
                    !declared_row
                        .tails
                        .iter()
                        .any(|t| self.sub.apply(t) == cb_resolved)
                })
                .collect();
            if !unpropagated.is_empty() {
                let err_span = annotation_span.unwrap_or_else(|| match clauses[0] {
                    Decl::FunBinding { span, .. } => *span,
                    _ => unreachable!(),
                });
                return Err(Diagnostic::error_at(
                    err_span,
                    format!(
                        "`{}` accepts a callback with an open effect row but does not forward it; \
                         every `..` row variable on a callback parameter must also appear in the \
                         function's own `needs` clause",
                        name,
                    ),
                ));
            }
        }

        // Open-row trait constraint forwarding requirement. When an open-row
        // trait method is called on an abstract, where-bound type variable `a`,
        // `emit_concrete_trait_impl_effects` surfaces `a` as an effect row tail
        // and records it in `trait_forward_row_vars`. Like the open-row callback
        // rule above, these effects are unknowable to this function, so it cannot
        // handle them — it must forward each as `needs {..a}` (or it's an error).
        // The surfaced tail rides through `all_body_effs`; per-method precision
        // comes from surfacing only happening when the method is actually called.
        if annotation.is_some() && !self.trait_forward_row_vars.is_empty() {
            let declared_tail_ids: std::collections::HashSet<u32> = declared_row
                .tails
                .iter()
                .filter_map(|t| match self.sub.apply(t) {
                    Type::Var(id) => Some(id),
                    _ => None,
                })
                .collect();
            // Drive the check off the recorded row vars (which persist across a
            // `with`), not off `all_body_effs.tails`: an internal `with` rebuilds
            // the effect row and drops the abstract tail, but it cannot actually
            // handle an open row (you can't name its effects), so the obligation
            // still leaks to callers. Fire whenever a recorded var is *still
            // abstract* (sub.apply → Type::Var) and not forwarded in the declared
            // row. A var that resolved to a concrete type at a concrete call site
            // is no longer a row variable — that's the concrete-discharge escape
            // hatch, and it stays intact.
            let mut unforwarded: Vec<(u32, String)> = Vec::new();
            for (var_id, trait_name) in &self.trait_forward_row_vars {
                let resolved = self.sub.apply(&Type::Var(*var_id));
                let Type::Var(rid) = resolved else {
                    continue;
                };
                if !declared_tail_ids.contains(&rid) {
                    unforwarded.push((rid, trait_name.clone()));
                }
            }
            if !unforwarded.is_empty() {
                unforwarded.sort();
                unforwarded.dedup();
                let (rid, trait_name) = &unforwarded[0];
                // Recover the source name of the type variable (e.g. `a`) for the
                // diagnostic; fall back to the trait's self position if unknown.
                let var_name = self
                    .fun_type_param_vars
                    .get(name)
                    .and_then(|params| {
                        params.iter().find_map(|(pname, pid)| {
                            if self.sub.apply(&Type::Var(*pid)) == Type::Var(*rid) {
                                Some(pname.clone())
                            } else {
                                None
                            }
                        })
                    })
                    .unwrap_or_else(|| "a".to_string());
                let pretty_trait = trait_name.rsplit('.').next().unwrap_or(trait_name);
                let err_span = annotation_span.unwrap_or_else(|| match clauses[0] {
                    Decl::FunBinding { span, .. } => *span,
                    _ => unreachable!(),
                });
                return Err(Diagnostic::error_at(
                    err_span,
                    format!(
                        "`{}` calls an open-row method of `{} {}` but does not forward its \
                         effects; add `needs {{..{}}}` to the annotation to forward `{}`'s \
                         effects to the caller",
                        name, pretty_trait, var_name, var_name, var_name,
                    ),
                ));
            }
        }

        if !all_body_effs.is_empty() || !declared_row.is_empty() {
            let err_span = match clauses[0] {
                Decl::FunBinding { span, .. } => *span,
                _ => unreachable!(),
            };
            // EXPERIMENT (infer-local-effects): only enforce the
            // declared-vs-body effect check when the function is annotated.
            // Unannotated functions are necessarily private (pub requires an
            // annotation); let their inferred effect row stand and propagate.
            if annotation.is_some() {
                self.check_effects_via_row(
                    &all_body_effs,
                    &declared_row,
                    &format!("function '{}'", name),
                    err_span,
                )?;
            }

            // Check for effects declared but never used. `all_body_effs` now
            // accurately reflects what the body performs (no absorption fudging),
            // so an effect declared in `needs` but absent from the body is
            // genuinely dead — including the case the old absorption hid: a HOF
            // that declares an effect it actually discharges (e.g. the dead
            // `Actor` that motivated `spawn`'s honest signature).
            let body_effect_names: std::collections::HashSet<String> = all_body_effs
                .effects
                .iter()
                .map(|e| e.name.clone())
                .collect();
            let declared_effects: std::collections::HashSet<String> = declared_row
                .effects
                .iter()
                .map(|e| e.name.clone())
                .collect();
            // Effects forwarded via the body's result TYPE (i.e. the body
            // returns a function whose arrows carry the effect: alias / eta /
            // partial application / returning an effectful function) are
            // discharged, not unused — `greet = emit` never *performs* {Log} but
            // forwards it through `emit`'s type. This only fires when the result
            // is itself a function (has arrows); a body that applies its args
            // down to a concrete value (Unit/Int/record/…) has an arrow-free
            // result type, so `forwarded` is empty and the warning behaves
            // normally. Known (benign) limitation: after unification the body
            // type carries the annotation's effects, so a bare alias of a PURE
            // function under an effectful annotation (`greet = ignore`) is also
            // suppressed. That's a no-op passthrough; over-declaring is sound;
            // this is a style lint. Any function that does real work and returns
            // a value still gets the warning.
            let mut forwarded_effects: std::collections::HashSet<String> =
                std::collections::HashSet::new();
            collect_arrow_effects(&self.sub.apply(&result_ty), &mut forwarded_effects);
            let unused: Vec<_> = declared_effects
                .difference(&body_effect_names)
                .filter(|name| !forwarded_effects.contains(*name))
                .collect();
            if !unused.is_empty() {
                let span = annotation_span.expect("unused effects implies annotation exists");
                let mut effects: Vec<_> = unused.into_iter().cloned().collect();
                effects.sort();
                self.pending_warnings
                    .push(crate::typechecker::PendingWarning::UnusedEffects {
                        span,
                        fun_name: name.to_string(),
                        effects,
                    });
            }
        }

        self.trait_forward_row_vars = saved_trait_forward;

        // Check for unresolved ambiguous field accesses. Any var still in field_candidates
        // after the full body was checked is genuinely ambiguous -- the programmer needs
        // to add a type annotation to disambiguate.
        for (var_id, (record_names, field_span)) in body_field_candidates {
            let resolved = self.sub.apply(&Type::Var(var_id));
            if matches!(resolved, Type::Var(_)) {
                let mut names = record_names.clone();
                names.sort();
                return Err(Diagnostic::error_at(
                    field_span,
                    format!(
                        "ambiguous field access: could be any of [{}] which all have this field; add a type annotation to disambiguate",
                        names.join(", ")
                    ),
                ));
            }
        }

        if let Some(info) = returned_handler_info {
            self.handler_funs.insert(name.to_string(), info);
        } else {
            self.handler_funs.remove(name);
        }

        // Build curried function type. Effect row comes from:
        // 1. The annotation's EffectRow (for annotated functions)
        // 2. The inferred body effects (for unannotated functions)
        // 3. Empty row (for pure functions)
        let mut fun_ty = result_ty;
        let effect_row = declared_effect_row
            .map(|row| self.sub.apply_effect_row(row))
            .or_else(|| annotation.and_then(|ann| innermost_effect_row(&self.sub.apply(ann))))
            .or_else(|| {
                if all_body_effs.is_empty() {
                    None
                } else {
                    Some(all_body_effs.clone())
                }
            });
        let mut first_arrow = true;
        for param_ty in param_types.into_iter().rev() {
            if first_arrow {
                if let Some(ref row) = effect_row {
                    fun_ty = Type::Fun(Box::new(param_ty), Box::new(fun_ty), row.clone());
                } else {
                    fun_ty = Type::arrow(param_ty, fun_ty);
                }
            } else {
                fun_ty = Type::arrow(param_ty, fun_ty);
            }
            first_arrow = false;
        }

        // Unify with the pre-bound variable (resolves recursive uses)
        self.unify(fun_var, &fun_ty)?;

        // Check against type annotation if present
        if let Some(ann_ty) = annotation {
            self.unify(&fun_ty, ann_ty).map_err(|e| {
                let span = match clauses[0] {
                    Decl::FunBinding { span, .. } => *span,
                    _ => unreachable!(),
                };
                Diagnostic::error_at(
                    span,
                    format!("type annotation mismatch for '{}': {}", name, e.message),
                )
            })?;
        }

        let scheme = self.build_fun_scheme(
            name,
            fun_ty,
            constraints_before,
            annotation.is_some(),
            where_constraints,
        )?;
        self.env.insert(name.into(), scheme);
        self.outer_named_type_vars = saved_outer_named;
        Ok(())
    }


    /// Look up the source-level type variable name for a resolved type var ID.
    /// `where_bound_var_names` is keyed by original (pre-substitution) var IDs,
    /// so we resolve each bound ID through substitution to find the match.
    pub(crate) fn resolve_where_var_name(&self, trait_name: &str, resolved_id: u32) -> Option<String> {
        self.trait_state
            .where_bounds
            .iter()
            .find_map(|(bound_id, traits)| {
                if traits
                    .iter()
                    .any(|bound_trait| self.trait_implies(bound_trait, trait_name))
                {
                    match self.sub.apply(&Type::Var(*bound_id)) {
                        Type::Var(r) if r == resolved_id => self
                            .trait_state
                            .where_bound_var_names
                            .get(bound_id)
                            .cloned(),
                        _ => None,
                    }
                } else {
                    None
                }
            })
            .or_else(|| {
                self.trait_state
                    .where_bound_var_names
                    .get(&resolved_id)
                    .cloned()
            })
    }


    pub(crate) fn trait_implies(&self, bound_trait: &str, required_trait: &str) -> bool {
        let bound = self
            .resolve_trait_name(bound_trait)
            .unwrap_or_else(|| bound_trait.to_string());
        let required = self
            .resolve_trait_name(required_trait)
            .unwrap_or_else(|| required_trait.to_string());
        self.trait_implies_canonical(&bound, &required, &mut std::collections::HashSet::new())
    }


    pub(crate) fn trait_implies_canonical(
        &self,
        bound_trait: &str,
        required_trait: &str,
        seen: &mut std::collections::HashSet<String>,
    ) -> bool {
        if bound_trait == required_trait {
            return true;
        }
        if !seen.insert(bound_trait.to_string()) {
            return false;
        }
        self.trait_state
            .traits
            .get(bound_trait)
            .is_some_and(|info| {
                info.supertraits.iter().any(|supertrait| {
                    self.trait_implies_canonical(supertrait, required_trait, seen)
                })
            })
    }


    /// Partition pending constraints into scheme-level (polymorphic) vs global
    /// (concrete), then generalize the function type into a scheme with constraints.
    pub(crate) fn build_fun_scheme(
        &mut self,
        name: &str,
        fun_ty: Type,
        constraints_before: usize,
        has_annotation: bool,
        where_constraints: &[(String, u32, Vec<Type>)],
    ) -> Result<Scheme, Diagnostic> {
        let new_constraints = self
            .trait_state
            .pending_constraints
            .split_off(constraints_before);

        // Collect type vars that appear in the function's type (used for
        // phantom detection and ambiguous-variable checks below).
        let mut type_vars = Vec::new();
        crate::typechecker::collect_free_vars(&self.sub.apply(&fun_ty), &mut type_vars);

        let mut scheme_constraints: Vec<(String, u32, Vec<Type>, Span)> = Vec::new();
        for (trait_name, trait_type_arg_types, ty, span, node_id) in new_constraints {
            let resolved = self.sub.apply(&ty);
            match resolved {
                Type::Var(id) => {
                    if is_generic_trait_name(&trait_name)
                        && let Some(rep_ty) = trait_type_arg_types.first()
                        && let Some(record_ty) =
                            anon_record_from_generic_rep(&self.sub.apply(rep_ty))
                    {
                        self.unify_at(&Type::Var(id), &record_ty, span)?;
                        self.trait_state.pending_constraints.push((
                            trait_name,
                            trait_type_arg_types,
                            Type::Var(id),
                            span,
                            node_id,
                        ));
                        continue;
                    }

                    if is_generic_trait_name(&trait_name) {
                        let mut extra_vars = Vec::new();
                        for extra in &trait_type_arg_types {
                            crate::typechecker::collect_free_vars(&self.sub.apply(extra), &mut extra_vars);
                        }
                        if extra_vars.iter().any(|extra| !type_vars.contains(extra)) {
                            self.trait_state.pending_constraints.push((
                                trait_name,
                                trait_type_arg_types,
                                Type::Var(id),
                                span,
                                node_id,
                            ));
                            continue;
                        }
                    }

                    // Check where_bounds, resolving bound var IDs through
                    // substitution so they match after annotation unification.
                    let in_where =
                        self.trait_state
                            .where_bounds
                            .iter()
                            .any(|(bound_id, traits)| {
                                traits
                                    .iter()
                                    .any(|bound_trait| self.trait_implies(bound_trait, &trait_name))
                                    && match self.sub.apply(&Type::Var(*bound_id)) {
                                        Type::Var(resolved) => resolved == id,
                                        _ => false,
                                    }
                            });
                    if in_where {
                        let var_name = self.resolve_where_var_name(&trait_name, id);
                        self.evidence.push(crate::typechecker::TraitEvidence {
                            node_id,
                            trait_name: trait_name.clone(),
                            resolved_type: None,
                            resolved_record_type: None,
                            type_var_name: var_name,
                            trait_type_args: trait_type_arg_types.iter().map(|t| self.sub.apply(t)).collect(),
                            resolved_symbol: None,
                        });
                        continue;
                    }

                    // Phantom constraint matching: if the constraint var doesn't
                    // appear in the function's type, it's from a trait method with
                    // phantom type params. Match against the function's own
                    // where-constraints (local, not global where_bounds) to connect
                    // the phantom var to the caller's type system.
                    if !type_vars.contains(&id) {
                        let matched = where_constraints
                            .iter()
                            .find(|(wc_trait, _, _)| *wc_trait == trait_name);
                        if let Some((_, wc_var_id, wc_extras)) = matched {
                            let wc_resolved = self.sub.apply(&Type::Var(*wc_var_id));
                            self.unify_at(&Type::Var(id), &wc_resolved, span)?;
                            // Unify extra type args pairwise
                            for (phantom_extra, where_extra) in
                                trait_type_arg_types.iter().zip(wc_extras.iter())
                            {
                                let pe = self.sub.apply(phantom_extra);
                                let we = self.sub.apply(where_extra);
                                self.unify_at(&pe, &we, span)?;
                            }
                            let resolved_id = match self.sub.apply(&Type::Var(id)) {
                                Type::Var(rid) => rid,
                                _ => id,
                            };
                            let var_name = self.resolve_where_var_name(&trait_name, resolved_id);
                            self.evidence.push(crate::typechecker::TraitEvidence {
                                node_id,
                                trait_name: trait_name.clone(),
                                resolved_type: None,
                                resolved_record_type: None,
                                type_var_name: var_name,
                                trait_type_args: trait_type_arg_types.iter().map(|t| self.sub.apply(t)).collect(),
                                resolved_symbol: None,
                            });
                            continue;
                        }
                    }

                    // A Var-self constraint on a var that isn't part of this
                    // function's polymorphism (not in fun_ty, not bound by a
                    // where clause, not matched by phantom-constraint pairing)
                    // must come from instantiating a callee whose scheme carries
                    // a where-clause existential. The companion concrete-self
                    // constraint in the same batch will pin this var via the
                    // FUNCTIONAL_TRAITS coherence rule, but only at module-end
                    // `check_pending_constraints` time. Defer it there instead
                    // of erroring (including under has_annotation) or
                    // pretending it constrains a local tvar.
                    if !type_vars.contains(&id) {
                        self.trait_state.pending_constraints.push((
                            trait_name,
                            trait_type_arg_types,
                            resolved.clone(),
                            span,
                            node_id,
                        ));
                        continue;
                    }
                    if has_annotation {
                        return Err(Diagnostic::error_at(
                            span,
                            format!(
                                "trait {} required but not declared in where clause for '{}'",
                                trait_name, name
                            ),
                        ));
                    }
                    // Record evidence for inferred constraints too, so the
                    // elaborator can resolve trait method calls (DictMethodAccess).
                    let var_name = self.resolve_where_var_name(&trait_name, id);
                    self.evidence.push(crate::typechecker::TraitEvidence {
                        node_id,
                        trait_name: trait_name.clone(),
                        resolved_type: None,
                        resolved_record_type: None,
                        type_var_name: var_name,
                        trait_type_args: trait_type_arg_types
                            .iter()
                            .map(|t| self.sub.apply(t))
                            .collect(),
                        resolved_symbol: None,
                    });
                    let resolved_extras = trait_type_arg_types
                        .iter()
                        .map(|ty| self.sub.apply(ty))
                        .collect();
                    scheme_constraints.push((trait_name, id, resolved_extras, span));
                }
                _ => {
                    self.trait_state.pending_constraints.push((
                        trait_name,
                        trait_type_arg_types,
                        ty,
                        span,
                        node_id,
                    ));
                }
            }
        }

        self.env.remove(name);
        let mut scheme = self.generalize(&fun_ty);

        // Collect var IDs introduced by where-clause constraints (both the self
        // var and any vars appearing inside extras). Where clauses may
        // introduce existentials — vars that aren't free in `fun_ty` but are
        // pinned at call sites via the FUNCTIONAL_TRAITS coherence rule (e.g.
        // `where {a: Generic r, r: MyJson}` introduces `r`). These must be
        // quantified in the scheme so instantiation freshens them in lockstep
        // with visible vars and the companion constraint survives.
        let mut where_var_ids: std::collections::HashSet<u32> = std::collections::HashSet::new();
        for (_, var_id, extra_types) in where_constraints {
            if let Type::Var(id) = self.sub.apply(&Type::Var(*var_id)) {
                where_var_ids.insert(id);
            }
            for extra in extra_types {
                let mut vs = Vec::new();
                crate::typechecker::collect_free_vars(&self.sub.apply(extra), &mut vs);
                where_var_ids.extend(vs);
            }
        }

        for (trait_name, var_id, extra_types) in where_constraints {
            let resolved_id = match self.sub.apply(&Type::Var(*var_id)) {
                Type::Var(id) => id,
                _ => continue,
            };
            let resolved_extras: Vec<Type> =
                extra_types.iter().map(|ty| self.sub.apply(ty)).collect();
            // Extend forall with the constraint's self var and any free vars in
            // its extras if they aren't already quantified. This admits
            // existentials into the scheme without disturbing visible
            // generalization.
            if !scheme.forall.contains(&resolved_id) {
                scheme.forall.push(resolved_id);
            }
            for extra in &resolved_extras {
                let mut vs = Vec::new();
                crate::typechecker::collect_free_vars(extra, &mut vs);
                for v in vs {
                    if !scheme.forall.contains(&v) {
                        scheme.forall.push(v);
                    }
                }
            }
            scheme
                .constraints
                .push((trait_name.clone(), resolved_id, resolved_extras));
        }

        for (trait_name, var_id, extra_types, span) in scheme_constraints {
            // An inferred constraint var is "covered" if it appears in the
            // visible function type OR if it's a where-clause existential that
            // will be pinned at the call site.
            let covered = type_vars.contains(&var_id) || where_var_ids.contains(&var_id);
            if !covered {
                let display = trait_name.rsplit('.').next().unwrap_or(&trait_name);
                return Err(Diagnostic::error_at(
                    span,
                    format!(
                        "ambiguous type variable requires {} but has no concrete type in '{}'",
                        display, name
                    ),
                ));
            }
            if scheme.forall.contains(&var_id)
                && !scheme
                    .constraints
                    .iter()
                    .any(|(t, v, _)| t == &trait_name && *v == var_id)
            {
                for extra in &extra_types {
                    let mut vs = Vec::new();
                    crate::typechecker::collect_free_vars(extra, &mut vs);
                    for v in vs {
                        if !scheme.forall.contains(&v) {
                            scheme.forall.push(v);
                        }
                    }
                }
                scheme.constraints.push((trait_name, var_id, extra_types));
            }
        }

        Ok(scheme)
    }


    /// Check exhaustiveness of multi-clause function patterns using Maranget.
    pub(crate) fn check_fun_exhaustiveness(
        &self,
        name: &str,
        clauses: &[&Decl],
        param_types: &[Type],
    ) -> Result<(), Diagnostic> {
        use crate::typechecker::exhaustiveness::{self as exh, ExhaustivenessCtx, SPat};

        // Only check if at least one param resolves to a known ADT or Tuple
        let resolved_types: Vec<_> = param_types.iter().map(|t| self.sub.apply(t)).collect();
        let has_adt_param = resolved_types.iter().any(|t| match t {
            Type::Con(name, _) => {
                self.adt_variants.contains_key(name)
                    || name == crate::typechecker::canonicalize_type_name("Tuple")
            }
            _ => false,
        });
        if !has_adt_param {
            return Ok(());
        }

        let ctx = ExhaustivenessCtx {
            adt_variants: &self.adt_variants,
        };
        let sctx = self.simplify_ctx();

        // Build pattern matrix: one row per clause, one column per param
        let mut matrix: Vec<Vec<SPat>> = Vec::new();

        for clause in clauses {
            let Decl::FunBinding {
                params,
                guard,
                span,
                ..
            } = clause
            else {
                unreachable!()
            };

            let row: Vec<SPat> = params
                .iter()
                .enumerate()
                .map(|(i, p)| exh::simplify_pat(p, resolved_types.get(i), &sctx))
                .collect();

            // Redundancy check
            if guard.is_none() && !exh::useful(&ctx, &matrix, &row) {
                return Err(Diagnostic::error_at(
                    *span,
                    format!(
                        "unreachable clause for '{}': all cases already covered",
                        name
                    ),
                ));
            }

            if guard.is_none() {
                matrix.push(row);
            }
        }

        // Exhaustiveness check
        let wildcard_row: Vec<SPat> = (0..param_types.len()).map(|_| SPat::Wildcard).collect();
        if exh::useful(&ctx, &matrix, &wildcard_row) {
            let witnesses = exh::find_all_witnesses(&ctx, &matrix, param_types.len());
            let span = match clauses[0] {
                Decl::FunBinding { span, .. } => *span,
                _ => unreachable!(),
            };
            if !witnesses.is_empty() {
                let formatted: Vec<String> =
                    witnesses.iter().map(|w| exh::format_witness(w)).collect();
                return Err(Diagnostic::error_at(
                    span,
                    format!(
                        "non-exhaustive clauses for '{}': missing {}",
                        name,
                        formatted.join(", ")
                    ),
                ));
            }
            return Err(Diagnostic::error_at(
                span,
                format!("non-exhaustive clauses for '{}'", name),
            ));
        }

        Ok(())
    }

    // --- Registration helpers ---

}
