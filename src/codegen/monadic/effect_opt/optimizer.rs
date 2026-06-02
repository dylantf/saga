use super::*;

impl<'info, 'data> Optimizer<'info, 'data> {
    pub(super) fn new(
        opts: RunOptions,
        handler_analysis: &'info HandlerAnalysis,
        effect_info: &'info EffectInfo<'data>,
        context: OptimizerContext,
    ) -> Self {
        Self {
            opts,
            context,
            handler_analysis,
            effect_info,
            handler_stack: Vec::new(),
            handler_value_bindings: Vec::new(),
            dict_value_bindings: Vec::new(),
            dict_method_bindings: Vec::new(),
            pure_atom_bindings: Vec::new(),
            inline_candidates: HashMap::new(),
            handler_factory_candidates: HashMap::new(),
            dict_constructors: HashMap::new(),
            variant_candidates: HashMap::new(),
            generated_variant_names: HashSet::new(),
            in_progress_private_helpers: HashSet::new(),
            pending_variants: Vec::new(),
            inline_blocked_names: Vec::new(),
        }
    }

    pub(super) fn optimize_program(&mut self, mut program: MProgram) -> MProgram {
        let mut changed = true;
        while changed {
            self.inline_candidates = collect_inline_candidates(&program);
            self.handler_factory_candidates = collect_handler_factory_candidates(&program);
            self.dict_constructors = collect_dict_constructors(&program);
            self.variant_candidates = collect_variant_candidates(&program);
            self.pending_variants.clear();
            changed = false;
            program = program
                .into_iter()
                .map(|decl| {
                    let (decl, ch) = self.optimize_decl(decl);
                    changed |= ch == Change::Changed;
                    decl
                })
                .collect();
            if !self.pending_variants.is_empty() {
                changed = true;
                program.append(&mut self.pending_variants);
            }
            let before_cleanup_len = program.len();
            program = remove_dead_variant_sources(program);
            if program.len() != before_cleanup_len {
                changed = true;
            }
        }
        program
    }

    fn optimize_decl(&mut self, decl: MDecl) -> (MDecl, Change) {
        match decl {
            MDecl::FunBinding(f) => {
                let (guard, guard_change) = optimize_optional_expr_with(self, f.guard);
                let param_names = bound_names_in_pats(&f.params);
                let (body, body_change) =
                    self.optimize_expr_with_blocked_names(param_names, f.body);
                let mut change = guard_change;
                change.mark_if(body_change);
                (MDecl::FunBinding(MFunBinding { guard, body, ..f }), change)
            }
            MDecl::Val(v) => {
                let (value, change) = self.optimize_expr(v.value);
                (MDecl::Val(MVal { value, ..v }), change)
            }
            MDecl::DictConstructor(d) => {
                let mut change = Change::Unchanged;
                let methods = d
                    .methods
                    .into_iter()
                    .map(|method| {
                        let (method, ch) = self.optimize_expr(method);
                        change.mark_if(ch);
                        method
                    })
                    .collect();
                (
                    MDecl::DictConstructor(MDictConstructor { methods, ..d }),
                    change,
                )
            }
            MDecl::Passthrough(_) => (decl, Change::Unchanged),
        }
    }

    pub(super) fn optimize_expr(&mut self, expr: MExpr) -> (MExpr, Change) {
        let (expr, child_change) = self.optimize_children(expr);
        let (expr, lambda_app_change) = self.try_inline_lambda_app(expr);
        let (expr, private_helper_change) = self.try_imported_private_helper_call(expr);
        let (expr, variant_change) = self.try_native_function_variant_call(expr);
        let (expr, inline_change) = self.try_inline_helper_call(expr);
        let (expr, static_variant_change) = self.try_static_function_variant_call(expr);
        let (expr, case_known_change) = self.try_case_known_scrutinee(expr);
        let (expr, native_change) = self.try_native_direct_call(expr);
        let (expr, finally_direct_change) = self.try_finally_direct_call(expr);
        let (expr, direct_change) = self.try_direct_call(expr);
        let (expr, handler_factory_change) = self.try_inline_let_bound_handler_factory(expr);
        let (expr, handler_value_change) = self.try_inline_let_bound_handler_value(expr);
        let (expr, collapse_change) = self.try_bind_collapse(expr);
        let (expr, let_collapse_change) = self.try_let_pure_collapse(expr);
        let (expr, let_change) = self.try_bind_to_let(expr);
        let (expr, dead_let_change) = self.try_dead_pure_let(expr);
        let (expr, dead_with_change) = self.try_dead_pure_static_with(expr);
        let mut change = child_change;
        change.mark_if(lambda_app_change);
        change.mark_if(private_helper_change);
        change.mark_if(variant_change);
        change.mark_if(inline_change);
        change.mark_if(static_variant_change);
        change.mark_if(case_known_change);
        change.mark_if(native_change);
        change.mark_if(finally_direct_change);
        change.mark_if(direct_change);
        change.mark_if(handler_factory_change);
        change.mark_if(handler_value_change);
        change.mark_if(collapse_change);
        change.mark_if(let_collapse_change);
        change.mark_if(let_change);
        change.mark_if(dead_let_change);
        change.mark_if(dead_with_change);
        (expr, change)
    }

    fn optimize_children(&mut self, expr: MExpr) -> (MExpr, Change) {
        match expr {
            MExpr::Pure(atom) => {
                let (atom, change) = self.optimize_atom(atom);
                (MExpr::Pure(atom), change)
            }
            MExpr::Yield { op, args, source } => {
                let (args, change) = self.optimize_atoms(args);
                (MExpr::Yield { op, args, source }, change)
            }
            MExpr::Bind {
                var,
                value,
                body,
                mode,
            } => {
                let (value, value_change) = self.optimize_expr(*value);
                let (body, body_change) = self.optimize_body_after_binding(&var, &value, *body);
                let mut change = value_change;
                change.mark_if(body_change);
                (
                    MExpr::Bind {
                        var,
                        value: Box::new(value),
                        body: Box::new(body),
                        mode,
                    },
                    change,
                )
            }
            MExpr::Let { var, value, body } => {
                let (value, value_change) = self.optimize_expr(*value);
                let (body, body_change) = self.optimize_body_after_binding(&var, &value, *body);
                let mut change = value_change;
                change.mark_if(body_change);
                (
                    MExpr::Let {
                        var,
                        value: Box::new(value),
                        body: Box::new(body),
                    },
                    change,
                )
            }
            MExpr::Ensure { body, cleanup } => {
                let (body, body_change) = self.optimize_expr(*body);
                let (cleanup, cleanup_change) = self.optimize_expr(*cleanup);
                let mut change = body_change;
                change.mark_if(cleanup_change);
                (
                    MExpr::Ensure {
                        body: Box::new(body),
                        cleanup: Box::new(cleanup),
                    },
                    change,
                )
            }
            MExpr::Case {
                scrutinee,
                arms,
                source,
            } => {
                let (scrutinee, mut change) = self.optimize_atom(scrutinee);
                let arms = arms
                    .into_iter()
                    .map(|arm| {
                        let (arm, ch) = self.optimize_arm(arm);
                        change.mark_if(ch);
                        arm
                    })
                    .collect();
                (
                    MExpr::Case {
                        scrutinee,
                        arms,
                        source,
                    },
                    change,
                )
            }
            MExpr::If {
                cond,
                then_branch,
                else_branch,
                source,
            } => {
                let (cond, cond_change) = self.optimize_atom(cond);
                let (then_branch, then_change) = self.optimize_expr(*then_branch);
                let (else_branch, else_change) = self.optimize_expr(*else_branch);
                let mut change = cond_change;
                change.mark_if(then_change);
                change.mark_if(else_change);
                (
                    MExpr::If {
                        cond,
                        then_branch: Box::new(then_branch),
                        else_branch: Box::new(else_branch),
                        source,
                    },
                    change,
                )
            }
            MExpr::App { head, args, source } => {
                let (head, head_change) = self.optimize_atom(head);
                let (args, args_change) = self.optimize_atoms(args);
                let mut change = head_change;
                change.mark_if(args_change);
                (MExpr::App { head, args, source }, change)
            }
            MExpr::With {
                handler,
                body,
                source,
            } => {
                let (handler, handler_change) = self.optimize_handler_with_cleared_stack(handler);
                let (handler, dynamic_change) = self.specialize_dynamic_handler_binding(handler);
                let frame = handler_frame(&handler);
                let (body, body_change) = if let Some(frame) = frame {
                    self.optimize_expr_with_frame(*body, frame)
                } else {
                    self.optimize_expr(*body)
                };
                let mut change = handler_change;
                change.mark_if(dynamic_change);
                change.mark_if(body_change);
                (
                    MExpr::With {
                        handler,
                        body: Box::new(body),
                        source,
                    },
                    change,
                )
            }
            MExpr::Resume { value, source } => {
                let (value, change) = self.optimize_atom(value);
                (MExpr::Resume { value, source }, change)
            }
            MExpr::FieldAccess {
                record,
                field,
                record_name,
                anon_fields,
                source,
            } => {
                let (record, change) = self.optimize_atom(record);
                (
                    MExpr::FieldAccess {
                        record,
                        field,
                        record_name,
                        anon_fields,
                        source,
                    },
                    change,
                )
            }
            MExpr::RecordUpdate {
                record,
                fields,
                record_name,
                anon_fields,
                source,
            } => {
                let (record, record_change) = self.optimize_atom(record);
                let (fields, fields_change) = self.optimize_field_atoms(fields);
                let mut change = record_change;
                change.mark_if(fields_change);
                (
                    MExpr::RecordUpdate {
                        record,
                        fields,
                        record_name,
                        anon_fields,
                        source,
                    },
                    change,
                )
            }
            MExpr::DictMethodAccess {
                dict,
                trait_name,
                method_index,
                source,
            } => {
                let (dict, change) = self.optimize_atom(dict);
                (
                    MExpr::DictMethodAccess {
                        dict,
                        trait_name,
                        method_index,
                        source,
                    },
                    change,
                )
            }
            MExpr::ForeignCall {
                module,
                func,
                args,
                source,
            } => {
                let (args, change) = self.optimize_atoms(args);
                (
                    MExpr::ForeignCall {
                        module,
                        func,
                        args,
                        source,
                    },
                    change,
                )
            }
            MExpr::BinOp {
                op,
                left,
                right,
                source,
            } => {
                let (left, left_change) = self.optimize_atom(left);
                let (right, right_change) = self.optimize_atom(right);
                let mut change = left_change;
                change.mark_if(right_change);
                (
                    MExpr::BinOp {
                        op,
                        left,
                        right,
                        source,
                    },
                    change,
                )
            }
            MExpr::UnaryMinus { value, source } => {
                let (value, change) = self.optimize_atom(value);
                (MExpr::UnaryMinus { value, source }, change)
            }
            MExpr::BitString { segments, source } => {
                let mut change = Change::Unchanged;
                let segments = segments
                    .into_iter()
                    .map(|mut seg| {
                        let (value, value_change) = self.optimize_atom(seg.value);
                        seg.value = value;
                        change.mark_if(value_change);
                        if let Some(size) = seg.size {
                            let (size, size_change) = self.optimize_atom(size);
                            seg.size = Some(size);
                            change.mark_if(size_change);
                        }
                        seg
                    })
                    .collect();
                (MExpr::BitString { segments, source }, change)
            }
            MExpr::Receive {
                arms,
                after,
                source,
            } => {
                let mut change = Change::Unchanged;
                let arms = arms
                    .into_iter()
                    .map(|arm| {
                        let (arm, ch) = self.optimize_arm(arm);
                        change.mark_if(ch);
                        arm
                    })
                    .collect();
                let after = after.map(|(timeout, body)| {
                    let (timeout, timeout_change) = self.optimize_atom(timeout);
                    let (body, body_change) = self.optimize_expr(*body);
                    change.mark_if(timeout_change);
                    change.mark_if(body_change);
                    (timeout, Box::new(body))
                });
                (
                    MExpr::Receive {
                        arms,
                        after,
                        source,
                    },
                    change,
                )
            }
            MExpr::LetFun {
                name,
                params,
                body,
                rest,
                source,
            } => {
                let body_blocked_names = {
                    let mut names = vec![name.clone()];
                    names.extend(bound_names_in_pats(&params));
                    names
                };
                let saved = std::mem::take(&mut self.handler_stack);
                let (body, body_change) =
                    self.optimize_expr_with_blocked_names(body_blocked_names, *body);
                self.handler_stack = saved;
                let (rest, rest_change) =
                    self.optimize_expr_with_blocked_names(vec![name.clone()], *rest);
                let mut change = body_change;
                change.mark_if(rest_change);
                (
                    MExpr::LetFun {
                        name,
                        params,
                        body: Box::new(body),
                        rest: Box::new(rest),
                        source,
                    },
                    change,
                )
            }
            MExpr::HandlerValue {
                effects,
                arms,
                return_clause,
                source,
            } => {
                let mut change = Change::Unchanged;
                let arms = arms
                    .into_iter()
                    .map(|arm| {
                        let (arm, ch) = self.optimize_handler_arm(arm);
                        change.mark_if(ch);
                        arm
                    })
                    .collect();
                let return_clause = return_clause.map(|arm| {
                    let (arm, ch) = self.optimize_handler_arm(*arm);
                    change.mark_if(ch);
                    Box::new(arm)
                });
                (
                    MExpr::HandlerValue {
                        effects,
                        arms,
                        return_clause,
                        source,
                    },
                    change,
                )
            }
        }
    }

    fn try_bind_collapse(&self, expr: MExpr) -> (MExpr, Change) {
        if !self.opts.bind_collapse() {
            return (expr, Change::Unchanged);
        }

        let MExpr::Bind {
            var,
            value,
            body,
            mode,
        } = expr
        else {
            return (expr, Change::Unchanged);
        };

        let MExpr::Pure(atom) = *value else {
            return (
                MExpr::Bind {
                    var,
                    value,
                    body,
                    mode,
                },
                Change::Unchanged,
            );
        };

        let free_names = free_atom_names(&atom);
        let substituted = subst_expr(*body, &var, &atom, &free_names);
        if substituted.blocked {
            (
                MExpr::Bind {
                    var,
                    value: Box::new(MExpr::Pure(atom)),
                    body: Box::new(substituted.value),
                    mode,
                },
                Change::Unchanged,
            )
        } else {
            (substituted.value, Change::Changed)
        }
    }

    fn try_case_known_scrutinee(&self, expr: MExpr) -> (MExpr, Change) {
        let MExpr::Case {
            scrutinee,
            arms,
            source,
        } = expr
        else {
            return (expr, Change::Unchanged);
        };

        let Some(scrutinee) = closed_case_scrutinee(&scrutinee) else {
            return (
                MExpr::Case {
                    scrutinee,
                    arms,
                    source,
                },
                Change::Unchanged,
            );
        };

        for arm in &arms {
            let Some(bindings) = match_pat_atom(&arm.pattern, &scrutinee) else {
                continue;
            };
            if arm.guard.is_some() {
                return (
                    MExpr::Case {
                        scrutinee,
                        arms,
                        source,
                    },
                    Change::Unchanged,
                );
            }

            let mut body = arm.body.clone();
            for (target, replacement) in bindings.into_iter().rev() {
                let free_names = free_atom_names(&replacement);
                let substituted = subst_expr(body, &target, &replacement, &free_names);
                if substituted.blocked {
                    return (
                        MExpr::Case {
                            scrutinee,
                            arms,
                            source,
                        },
                        Change::Unchanged,
                    );
                }
                body = substituted.value;
            }
            return (body, Change::Changed);
        }

        (
            MExpr::Case {
                scrutinee,
                arms,
                source,
            },
            Change::Unchanged,
        )
    }

    fn try_bind_to_let(&self, expr: MExpr) -> (MExpr, Change) {
        if !self.opts.bind_to_let() {
            return (expr, Change::Unchanged);
        }

        let MExpr::Bind {
            var,
            value,
            body,
            mode,
        } = expr
        else {
            return (expr, Change::Unchanged);
        };

        if self.expr_is_non_yielding(&value) {
            (MExpr::Let { var, value, body }, Change::Changed)
        } else {
            (
                MExpr::Bind {
                    var,
                    value,
                    body,
                    mode,
                },
                Change::Unchanged,
            )
        }
    }

    fn expr_is_non_yielding(&self, expr: &MExpr) -> bool {
        if expr_is_pure(expr) {
            return true;
        }

        match expr {
            MExpr::Bind { value, body, .. } | MExpr::Let { value, body, .. } => {
                self.expr_is_non_yielding(value) && self.expr_is_non_yielding(body)
            }
            MExpr::Case { arms, .. } => arms.iter().all(|arm| {
                // Guard lowering has its own stricter subset; keep general
                // app promotion out of guards until that path grows with it.
                arm.guard.as_ref().is_none_or(expr_is_pure) && self.expr_is_non_yielding(&arm.body)
            }),
            MExpr::If {
                then_branch,
                else_branch,
                ..
            } => self.expr_is_non_yielding(then_branch) && self.expr_is_non_yielding(else_branch),
            MExpr::FieldAccess { .. }
            | MExpr::RecordUpdate { .. }
            | MExpr::DictMethodAccess { .. }
            | MExpr::BinOp { .. }
            | MExpr::UnaryMinus { .. }
            | MExpr::BitString { .. } => true,
            MExpr::App { head, .. } => self.app_head_is_closed_empty_effect_row(head),
            MExpr::Pure(_)
            | MExpr::Yield { .. }
            | MExpr::Ensure { .. }
            | MExpr::With { .. }
            | MExpr::Resume { .. }
            | MExpr::ForeignCall { .. }
            | MExpr::Receive { .. }
            | MExpr::LetFun { .. }
            | MExpr::HandlerValue { .. } => false,
        }
    }

    fn app_head_is_closed_empty_effect_row(&self, head: &Atom) -> bool {
        let source = atom_source(head);
        if let Some(ty) = self.effect_info.type_at_node.get(&source) {
            let (_, effects, has_open_row) = type_shape::arity_and_evidence_from_type(ty);
            return effects.is_empty() && !has_open_row;
        }

        if let Some(resolved) = self.context.resolution.get(&source) {
            return match &resolved.kind {
                ResolvedCodegenKind::BeamFunction { effects, .. }
                | ResolvedCodegenKind::ExternalFunction { effects, .. } => effects.is_empty(),
                ResolvedCodegenKind::Intrinsic { .. } => true,
            };
        }

        match head {
            Atom::Lambda { body, .. } => self.expr_is_non_yielding(body),
            Atom::DictRef { .. } => true,
            _ => false,
        }
    }

    fn try_let_pure_collapse(&self, expr: MExpr) -> (MExpr, Change) {
        if !self.opts.bind_collapse() {
            return (expr, Change::Unchanged);
        }

        let MExpr::Let { var, value, body } = expr else {
            return (expr, Change::Unchanged);
        };

        let MExpr::Pure(atom) = *value else {
            return (MExpr::Let { var, value, body }, Change::Unchanged);
        };

        let free_names = free_atom_names(&atom);
        let substituted = subst_expr(*body, &var, &atom, &free_names);
        if substituted.blocked {
            (
                MExpr::Let {
                    var,
                    value: Box::new(MExpr::Pure(atom)),
                    body: Box::new(substituted.value),
                },
                Change::Unchanged,
            )
        } else {
            (substituted.value, Change::Changed)
        }
    }

    fn try_dead_pure_let(&self, expr: MExpr) -> (MExpr, Change) {
        if !self.opts.dead_pure_let() {
            return (expr, Change::Unchanged);
        }

        let (var, value, body, mode) = match expr {
            MExpr::Let { var, value, body } => (var, value, body, None),
            MExpr::Bind {
                var,
                value,
                body,
                mode,
            } => (var, value, body, Some(mode)),
            other => return (other, Change::Unchanged),
        };

        if self.binding_value_is_removable_when_unused(&value) && !expr_contains_target(&body, &var)
        {
            (*body, Change::Changed)
        } else {
            (rebuild_binding(var, value, body, mode), Change::Unchanged)
        }
    }

    fn binding_value_is_removable_when_unused(&self, value: &MExpr) -> bool {
        expr_is_pure(value)
            || matches!(
                value,
                MExpr::HandlerValue { .. } | MExpr::DictMethodAccess { .. }
            )
            || self.expr_is_dict_constructor_app(value)
    }

    fn expr_is_dict_constructor_app(&self, value: &MExpr) -> bool {
        let MExpr::App { head, .. } = value else {
            return false;
        };
        self.dict_constructor_for_head(head).is_some()
    }

    fn try_dead_pure_static_with(&self, expr: MExpr) -> (MExpr, Change) {
        if !self.opts.dead_pure_with() {
            return (expr, Change::Unchanged);
        }

        let MExpr::With {
            handler,
            body,
            source,
        } = expr
        else {
            return (expr, Change::Unchanged);
        };

        match &handler {
            MHandler::Static { return_clause, .. }
                if return_clause.is_none() && expr_is_handler_independent_value(&body) =>
            {
                (*body, Change::Changed)
            }
            _ => (
                MExpr::With {
                    handler,
                    body,
                    source,
                },
                Change::Unchanged,
            ),
        }
    }

    fn try_inline_lambda_app(&self, expr: MExpr) -> (MExpr, Change) {
        let MExpr::App {
            head,
            args,
            source: app_source,
        } = expr
        else {
            return (expr, Change::Unchanged);
        };

        let Atom::Lambda {
            params,
            body,
            source: lambda_source,
        } = head
        else {
            return (
                MExpr::App {
                    head,
                    args,
                    source: app_source,
                },
                Change::Unchanged,
            );
        };
        if !immediate_lambda_app_is_supported(&params, &body, args.len()) {
            return (
                MExpr::App {
                    head: Atom::Lambda {
                        params,
                        body,
                        source: lambda_source,
                    },
                    args,
                    source: app_source,
                },
                Change::Unchanged,
            );
        }

        let inlined = inline_helper_candidate(
            &InlineCandidate {
                params,
                body: *body,
            },
            &args,
        )
        .expect("supported lambda application should inline");
        (inlined, Change::Changed)
    }

    fn optimize_arm(&mut self, arm: MArm) -> (MArm, Change) {
        let blocked_names = bound_names_in_pat(&arm.pattern);
        let (guard, guard_change) =
            optimize_optional_expr_with_blocked_names(self, arm.guard, blocked_names.clone());
        let (body, body_change) = self.optimize_expr_with_blocked_names(blocked_names, arm.body);
        let mut change = guard_change;
        change.mark_if(body_change);
        (MArm { guard, body, ..arm }, change)
    }

    fn optimize_body_after_binding(
        &mut self,
        var: &MVar,
        value: &MExpr,
        body: MExpr,
    ) -> (MExpr, Change) {
        if let Some(candidate) = handler_value_candidate(value) {
            self.handler_value_bindings
                .push((var.name.clone(), Some(candidate)));
        } else {
            self.handler_value_bindings.push((var.name.clone(), None));
        }
        if let Some(candidate) = self.dict_value_candidate(value) {
            self.dict_value_bindings
                .push((var.name.clone(), Some(candidate)));
        } else {
            self.dict_value_bindings.push((var.name.clone(), None));
        }
        if let Some(candidate) = self.dict_method_candidate(value) {
            self.dict_method_bindings
                .push((var.name.clone(), Some(candidate)));
        } else {
            self.dict_method_bindings.push((var.name.clone(), None));
        }
        if let MExpr::Pure(atom) = value {
            self.pure_atom_bindings
                .push((var.name.clone(), closed_dict_constructor_arg(atom)));
        } else {
            self.pure_atom_bindings.push((var.name.clone(), None));
        }
        let (body, change) = self.optimize_expr_with_blocked_names(vec![var.name.clone()], body);
        self.pure_atom_bindings.pop();
        self.dict_method_bindings.pop();
        self.dict_value_bindings.pop();
        self.handler_value_bindings.pop();
        (body, change)
    }

    fn dict_value_candidate(&self, value: &MExpr) -> Option<DictValueCandidate> {
        let MExpr::App { head, args, .. } = value else {
            return None;
        };
        let constructor = self.dict_constructor_for_head(head)?;
        if constructor.dict_params.len() != args.len() {
            return None;
        }

        let mut param_replacements = Vec::with_capacity(args.len());
        let mut arg_keys = Vec::with_capacity(args.len());
        for (param, arg) in constructor.dict_params.iter().zip(args) {
            let (replacement, key) = match arg {
                Atom::Var { name: arg_var, .. } => self
                    .lookup_dict_value(&arg_var.name)
                    .map(|arg_dict| (arg_dict.atom, arg_dict.key))
                    .or_else(|| {
                        self.lookup_pure_atom(&arg_var.name).map(|arg| {
                            let key = atom_key(&arg);
                            (arg, key)
                        })
                    })
                    .or_else(|| {
                        closed_dict_constructor_arg(arg).map(|arg| {
                            let key = atom_key(&arg);
                            (arg, key)
                        })
                    })?,
                _ => {
                    let arg = closed_dict_constructor_arg(arg)?;
                    let key = atom_key(&arg);
                    (arg, key)
                }
            };
            param_replacements.push((
                MVar {
                    name: param.clone(),
                    id: 0,
                },
                replacement,
            ));
            arg_keys.push(key);
        }

        let mut methods = Vec::with_capacity(constructor.methods.len());
        for method in &constructor.methods {
            let MExpr::Pure(atom @ Atom::Lambda { .. }) = method else {
                return None;
            };
            let mut method = atom.clone();
            for (target, replacement) in &param_replacements {
                let free_names = free_atom_names(replacement);
                let substituted = subst_atom(method, target, replacement, &free_names);
                if substituted.blocked {
                    return None;
                }
                method = substituted.value;
            }
            methods.push(method);
        }

        let key = if arg_keys.is_empty() {
            constructor.name.clone()
        } else {
            format!("{}({})", constructor.name, arg_keys.join(","))
        };
        Some(DictValueCandidate {
            atom: Atom::Tuple {
                elements: methods.clone(),
                source: constructor.id,
            },
            methods,
            key,
        })
    }

    fn dict_constructor_for_head(&self, head: &Atom) -> Option<&MDictConstructor> {
        match head {
            Atom::DictRef { name, .. } => self
                .dict_constructors
                .get(name)
                .or_else(|| self.context.imported_dict_constructors.get(name)),
            Atom::Var { name, source } => {
                let canonical = self
                    .context
                    .resolution
                    .get(source)
                    .map(|resolved| resolved.canonical_name.as_str());
                canonical
                    .and_then(|name| self.context.imported_dict_constructors.get(name))
                    .or_else(|| self.context.imported_dict_constructors.get(&name.name))
                    .or_else(|| self.dict_constructors.get(&name.name))
            }
            Atom::QualifiedRef { name, source, .. } => {
                let canonical = self
                    .context
                    .resolution
                    .get(source)
                    .map(|resolved| resolved.canonical_name.as_str());
                canonical
                    .and_then(|name| self.context.imported_dict_constructors.get(name))
                    .or_else(|| self.context.imported_dict_constructors.get(name))
            }
            _ => None,
        }
    }

    fn dict_method_candidate(&self, value: &MExpr) -> Option<InlineCandidate> {
        let MExpr::DictMethodAccess {
            dict, method_index, ..
        } = value
        else {
            return None;
        };
        let method = self.dict_method_atom(dict, *method_index)?;
        let Atom::Lambda { params, body, .. } = method else {
            return None;
        };
        if !dict_method_params_are_supported(&params) {
            return None;
        }
        Some(InlineCandidate {
            params: params.clone(),
            body: body.as_ref().clone(),
        })
    }

    fn dict_method_atom(&self, dict: &Atom, method_index: usize) -> Option<Atom> {
        match dict {
            Atom::Var { name, .. } => self
                .lookup_dict_value(&name.name)
                .and_then(|dict| dict.methods.get(method_index).cloned()),
            Atom::Tuple { elements, .. } => elements.get(method_index).cloned(),
            Atom::DictRef { name, .. } => self
                .dict_constructors
                .get(name)
                .or_else(|| self.context.imported_dict_constructors.get(name))
                .filter(|constructor| constructor.dict_params.is_empty())
                .and_then(|constructor| constructor.methods.get(method_index))
                .and_then(|method| match method {
                    MExpr::Pure(atom) => Some(atom.clone()),
                    _ => None,
                }),
            _ => None,
        }
    }

    fn lookup_dict_value(&self, name: &str) -> Option<DictValueCandidate> {
        self.dict_value_bindings
            .iter()
            .rev()
            .find(|(bound_name, _)| bound_name == name)?
            .1
            .clone()
    }

    fn lookup_dict_method(&self, name: &str) -> Option<InlineCandidate> {
        self.dict_method_bindings
            .iter()
            .rev()
            .find(|(bound_name, _)| bound_name == name)?
            .1
            .clone()
    }

    fn lookup_pure_atom(&self, name: &str) -> Option<Atom> {
        self.pure_atom_bindings
            .iter()
            .rev()
            .find(|(bound_name, _)| bound_name == name)?
            .1
            .clone()
    }

    fn dict_param_replacements(&self, params: &[Pat], args: &[Atom]) -> Vec<DictParamReplacement> {
        params
            .iter()
            .zip(args)
            .filter_map(|(param, arg)| {
                let Pat::Var { name, id, .. } = param else {
                    return None;
                };
                let Atom::Var { name: arg_var, .. } = arg else {
                    return None;
                };
                let dict = self.lookup_dict_value(&arg_var.name)?;
                Some(DictParamReplacement {
                    target: MVar {
                        name: name.clone(),
                        id: id.0,
                    },
                    replacement: dict.atom,
                    key: dict.key,
                })
            })
            .collect()
    }

    fn value_param_replacements(
        &self,
        params: &[Pat],
        args: &[Atom],
    ) -> Vec<ValueParamReplacement> {
        params
            .iter()
            .zip(args)
            .filter_map(|(param, arg)| {
                let Pat::Var { name, id, .. } = param else {
                    return None;
                };
                let replacement = match arg {
                    Atom::Var { name, .. } => self
                        .lookup_pure_atom(&name.name)
                        .and_then(|atom| closed_constructor_variant_arg(&atom))
                        .or_else(|| closed_constructor_variant_arg(arg))?,
                    _ => closed_constructor_variant_arg(arg)?,
                };
                Some(ValueParamReplacement {
                    target: MVar {
                        name: name.clone(),
                        id: id.0,
                    },
                    key: atom_key(&replacement),
                    replacement,
                })
            })
            .collect()
    }

    fn callback_param_replacements(
        &self,
        params: &[Pat],
        args: &[Atom],
    ) -> Vec<CallbackParamReplacement> {
        params
            .iter()
            .zip(args)
            .filter_map(|(param, arg)| {
                let Pat::Var { name, id, .. } = param else {
                    return None;
                };
                let Atom::Lambda {
                    params,
                    body,
                    source,
                } = arg
                else {
                    return None;
                };
                if !helper_params_are_supported(params)
                    || !self.expr_has_specialization_opportunity(body)
                {
                    return None;
                }
                Some(CallbackParamReplacement {
                    target: MVar {
                        name: name.clone(),
                        id: id.0,
                    },
                    candidate: InlineCandidate {
                        params: params.clone(),
                        body: body.as_ref().clone(),
                    },
                    key: format!("{}:{}", name, source.0),
                    captures: lambda_capture_names(arg),
                })
            })
            .collect()
    }

    fn specialize_dynamic_handler_binding(&self, handler: MHandler) -> (MHandler, Change) {
        let MHandler::Dynamic {
            effects,
            op_tuple,
            return_lambda,
            source,
        } = handler
        else {
            return (handler, Change::Unchanged);
        };

        let Atom::Var { name, .. } = &op_tuple else {
            return (
                MHandler::Dynamic {
                    effects,
                    op_tuple,
                    return_lambda,
                    source,
                },
                Change::Unchanged,
            );
        };

        let Some((_, maybe_candidate)) = self
            .handler_value_bindings
            .iter()
            .rev()
            .find(|(bound_name, _)| bound_name == &name.name)
        else {
            return (
                MHandler::Dynamic {
                    effects,
                    op_tuple,
                    return_lambda,
                    source,
                },
                Change::Unchanged,
            );
        };
        let Some(candidate) = maybe_candidate.as_ref() else {
            return (
                MHandler::Dynamic {
                    effects,
                    op_tuple,
                    return_lambda,
                    source,
                },
                Change::Unchanged,
            );
        };

        if return_lambda.is_some() || !handler_effect_sets_match(&candidate.effects, &effects) {
            return (
                MHandler::Dynamic {
                    effects,
                    op_tuple,
                    return_lambda,
                    source,
                },
                Change::Unchanged,
            );
        }

        (
            MHandler::Static {
                effects: candidate.effects.clone(),
                arms: candidate.arms.clone(),
                return_clause: candidate.return_clause.as_deref().cloned(),
                source: candidate.source,
            },
            Change::Changed,
        )
    }

    fn optimize_handler(&mut self, handler: MHandler) -> (MHandler, Change) {
        match handler {
            MHandler::Static {
                effects,
                arms,
                return_clause,
                source,
            } => {
                let mut change = Change::Unchanged;
                let arms = arms
                    .into_iter()
                    .map(|arm| {
                        let (arm, ch) = self.optimize_handler_arm(arm);
                        change.mark_if(ch);
                        arm
                    })
                    .collect();
                let return_clause = return_clause.map(|arm| {
                    let (arm, ch) = self.optimize_handler_arm(arm);
                    change.mark_if(ch);
                    arm
                });
                (
                    MHandler::Static {
                        effects,
                        arms,
                        return_clause,
                        source,
                    },
                    change,
                )
            }
            MHandler::Native { .. } => (handler, Change::Unchanged),
            MHandler::Composite { handlers, source } => {
                let mut change = Change::Unchanged;
                let handlers = handlers
                    .into_iter()
                    .map(|handler| {
                        let (handler, ch) = self.optimize_handler(handler);
                        change.mark_if(ch);
                        handler
                    })
                    .collect();
                (MHandler::Composite { handlers, source }, change)
            }
            MHandler::Dynamic {
                effects,
                op_tuple,
                return_lambda,
                source,
            } => {
                let (op_tuple, op_change) = self.optimize_atom(op_tuple);
                let (return_lambda, return_change) =
                    optimize_optional_atom_with(self, return_lambda);
                let mut change = op_change;
                change.mark_if(return_change);
                (
                    MHandler::Dynamic {
                        effects,
                        op_tuple,
                        return_lambda,
                        source,
                    },
                    change,
                )
            }
        }
    }

    fn optimize_handler_arm(&mut self, arm: MHandlerArm) -> (MHandlerArm, Change) {
        let blocked_names = bound_names_in_pats(&arm.params);
        let (body, body_change) =
            self.optimize_expr_with_blocked_names(blocked_names.clone(), *arm.body);
        let (finally_block, finally_change) =
            optimize_optional_boxed_expr_with_blocked_names(self, arm.finally_block, blocked_names);
        let mut change = body_change;
        change.mark_if(finally_change);
        (
            MHandlerArm {
                body: Box::new(body),
                finally_block,
                ..arm
            },
            change,
        )
    }

    pub(super) fn optimize_atom(&mut self, atom: Atom) -> (Atom, Change) {
        match atom {
            Atom::Ctor { name, args, source } => {
                let (args, change) = self.optimize_atoms(args);
                (Atom::Ctor { name, args, source }, change)
            }
            Atom::Tuple { elements, source } => {
                let (elements, change) = self.optimize_atoms(elements);
                (Atom::Tuple { elements, source }, change)
            }
            Atom::AnonRecord { fields, source } => {
                let (fields, change) = self.optimize_field_atoms(fields);
                (Atom::AnonRecord { fields, source }, change)
            }
            Atom::Record {
                name,
                fields,
                source,
            } => {
                let (fields, change) = self.optimize_field_atoms(fields);
                (
                    Atom::Record {
                        name,
                        fields,
                        source,
                    },
                    change,
                )
            }
            Atom::Lambda {
                params,
                body,
                source,
            } => {
                let (body, change) = self.optimize_expr_with_cleared_stack(*body);
                (
                    Atom::Lambda {
                        params,
                        body: Box::new(body),
                        source,
                    },
                    change,
                )
            }
            Atom::BackendSpawnThunk { callback, source } => {
                let (callback, change) = self.optimize_spawn_callback_atom(*callback);
                (
                    Atom::BackendSpawnThunk {
                        callback: Box::new(callback),
                        source,
                    },
                    change,
                )
            }
            Atom::Var { .. }
            | Atom::Lit { .. }
            | Atom::DictRef { .. }
            | Atom::QualifiedRef { .. }
            | Atom::Symbol { .. }
            | Atom::BackendAtom { .. } => (atom, Change::Unchanged),
        }
    }

    fn optimize_atoms(&mut self, atoms: Vec<Atom>) -> (Vec<Atom>, Change) {
        let mut change = Change::Unchanged;
        let atoms = atoms
            .into_iter()
            .map(|atom| {
                let (atom, ch) = self.optimize_atom(atom);
                change.mark_if(ch);
                atom
            })
            .collect();
        (atoms, change)
    }

    fn optimize_field_atoms(
        &mut self,
        fields: Vec<(String, Atom)>,
    ) -> (Vec<(String, Atom)>, Change) {
        let mut change = Change::Unchanged;
        let fields = fields
            .into_iter()
            .map(|(name, atom)| {
                let (atom, ch) = self.optimize_atom(atom);
                change.mark_if(ch);
                (name, atom)
            })
            .collect();
        (fields, change)
    }

    fn optimize_handler_with_cleared_stack(&mut self, handler: MHandler) -> (MHandler, Change) {
        let saved = std::mem::take(&mut self.handler_stack);
        let out = self.optimize_handler(handler);
        self.handler_stack = saved;
        out
    }

    pub(super) fn optimize_expr_with_blocked_names(
        &mut self,
        names: Vec<String>,
        expr: MExpr,
    ) -> (MExpr, Change) {
        let old_len = self.inline_blocked_names.len();
        self.inline_blocked_names.extend(names);
        let out = self.optimize_expr(expr);
        self.inline_blocked_names.truncate(old_len);
        out
    }

    fn optimize_expr_with_cleared_stack(&mut self, expr: MExpr) -> (MExpr, Change) {
        let saved = std::mem::take(&mut self.handler_stack);
        let out = self.optimize_expr(expr);
        self.handler_stack = saved;
        out
    }

    fn optimize_expr_with_frame(&mut self, expr: MExpr, frame: HandlerFrame) -> (MExpr, Change) {
        self.handler_stack.push(frame);
        let out = self.optimize_expr(expr);
        self.handler_stack.pop();
        out
    }

    fn try_native_function_variant_call(&mut self, expr: MExpr) -> (MExpr, Change) {
        if !self.opts.native_function_variants() || !self.native_variant_stack_eligible() {
            return (expr, Change::Unchanged);
        }

        let (expr, change) = self.try_function_variant_call(expr, native_variant_name, false);
        if change == Change::Changed {
            return (expr, change);
        }

        self.try_imported_function_variant_call(expr, variant_name_for_imported, false)
    }

    fn try_static_function_variant_call(&mut self, expr: MExpr) -> (MExpr, Change) {
        if !self.opts.static_function_variants() || !self.static_variant_stack_eligible() {
            return (expr, Change::Unchanged);
        }

        let (expr, change) = self.try_function_variant_call(expr, static_variant_name, true);
        if change == Change::Changed {
            return (expr, change);
        }

        self.try_imported_function_variant_call(expr, variant_name_for_imported_static, true)
    }

    fn try_function_variant_call(
        &mut self,
        expr: MExpr,
        variant_name_for_stack: fn(&str, &[HandlerFrame]) -> String,
        require_no_residual_yields: bool,
    ) -> (MExpr, Change) {
        let MExpr::App { head, args, source } = expr else {
            return (expr, Change::Unchanged);
        };

        let Atom::Var {
            name,
            source: _head_source,
        } = &head
        else {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        };
        if is_generated_variant_name(&name.name)
            || self.inline_blocked_names.iter().any(|n| n == &name.name)
        {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        }

        let Some(candidate) = self.variant_candidates.get(&name.name).cloned() else {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        };
        if args.len() != candidate.binding.params.len() {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        }
        let dict_replacements = self.dict_param_replacements(&candidate.binding.params, &args);
        let self_recursive = expr_calls_any(
            &candidate.binding.body,
            &HashSet::from([candidate.binding.name.clone()]),
        );
        let value_replacements = if self_recursive {
            Vec::new()
        } else {
            self.value_param_replacements(&candidate.binding.params, &args)
        };
        let callback_replacements =
            self.callback_param_replacements(&candidate.binding.params, &args);
        let has_hidden_effect_specialization = self
            .effect_summary(&candidate.binding.body)
            .has_specialization_opportunity();
        if callback_replacements.is_empty()
            && value_replacements.is_empty()
            && !has_hidden_effect_specialization
            && !expr_contains_dict_method_access(&candidate.binding.body)
        {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        }
        let capture_names =
            self.variant_capture_names(callback_replacements.iter().flat_map(|r| &r.captures));
        if captures_collide_with_params(&capture_names, &candidate.binding.params) {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        }

        let variant_name = variant_name_with_capture_key(
            variant_name_with_callback_key(
                variant_name_with_value_key(
                    variant_name_with_dict_key(
                        variant_name_for_stack(&candidate.binding.name, &self.handler_stack),
                        &dict_replacements,
                    ),
                    &value_replacements,
                ),
                &callback_replacements,
            ),
            &capture_names,
        );
        if variant_name == name.name {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        }

        let pending_len = self.pending_variants.len();
        let generated_names_before = self.generated_variant_names.clone();
        let Some(mut variant_body) = self.optimized_variant_body(
            &candidate.binding,
            &name.name,
            &variant_name,
            capture_names.iter().cloned(),
            VariantSpecializations {
                dict: &dict_replacements,
                values: &value_replacements,
                callbacks: &callback_replacements,
            },
        ) else {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        };
        let has_arg_specialization = !dict_replacements.is_empty()
            || !value_replacements.is_empty()
            || !callback_replacements.is_empty();
        if !variant_body_has_useful_specialization(
            &candidate.binding.body,
            &variant_body,
            has_arg_specialization,
            has_hidden_effect_specialization,
        ) || (require_no_residual_yields && expr_yield_count(&variant_body) != 0)
        {
            self.pending_variants.truncate(pending_len);
            self.generated_variant_names = generated_names_before;
            return (MExpr::App { head, args, source }, Change::Unchanged);
        }

        let (variant_params, args) = prune_unused_dict_variant_args(
            &candidate.binding.params,
            args,
            &variant_body,
            &dict_replacements,
        );
        let (variant_params, args) =
            append_capture_variant_args(variant_params, args, &capture_names, source);
        variant_body =
            append_capture_args_to_self_calls(variant_body, &variant_name, &capture_names, source);
        self.push_function_variant(
            &variant_name,
            variant_body,
            candidate.binding.clone(),
            variant_params,
        );

        (
            MExpr::App {
                head: Atom::Var {
                    name: MVar {
                        name: variant_name,
                        id: name.id,
                    },
                    // Generated variant names are not in the source
                    // resolution map. Reusing the user's original reference
                    // NodeId makes the lowerer resolve this call back to the
                    // source function, so attach the function declaration id
                    // instead.
                    source: candidate.binding.id,
                },
                args,
                source,
            },
            Change::Changed,
        )
    }

    fn try_imported_function_variant_call(
        &mut self,
        expr: MExpr,
        variant_name_for_imported: fn(&str, &str, &[HandlerFrame]) -> String,
        require_no_residual_yields: bool,
    ) -> (MExpr, Change) {
        let MExpr::App { head, args, source } = expr else {
            return (expr, Change::Unchanged);
        };

        let Some((head_name, head_id, head_source)) = imported_variant_head_info(&head) else {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        };
        if is_generated_variant_name(&head_name)
            || self.inline_blocked_names.iter().any(|n| n == &head_name)
        {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        }

        let Some(resolved) = self.context.resolution.get(&head_source) else {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        };
        if !matches!(resolved.kind, ResolvedCodegenKind::BeamFunction { .. }) {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        }

        let Some(candidate) = self.lookup_imported_function_variant(resolved) else {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        };
        if args.len() != candidate.binding.params.len() {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        }
        let dict_replacements = self.dict_param_replacements(&candidate.binding.params, &args);
        let self_recursive = expr_calls_any(
            &candidate.binding.body,
            &HashSet::from([candidate.binding.name.clone()]),
        );
        let value_replacements = if self_recursive {
            Vec::new()
        } else {
            self.value_param_replacements(&candidate.binding.params, &args)
        };
        let callback_replacements =
            self.callback_param_replacements(&candidate.binding.params, &args);
        let has_hidden_effect_specialization = self
            .effect_summary(&candidate.binding.body)
            .has_specialization_opportunity();
        if callback_replacements.is_empty()
            && value_replacements.is_empty()
            && !has_hidden_effect_specialization
            && !expr_contains_dict_method_access(&candidate.binding.body)
        {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        }
        let capture_names =
            self.variant_capture_names(callback_replacements.iter().flat_map(|r| &r.captures));
        if captures_collide_with_params(&capture_names, &candidate.binding.params) {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        }

        let variant_name = variant_name_with_capture_key(
            variant_name_with_callback_key(
                variant_name_with_value_key(
                    variant_name_with_dict_key(
                        variant_name_for_imported(
                            &candidate.source_module,
                            &candidate.binding.name,
                            &self.handler_stack,
                        ),
                        &dict_replacements,
                    ),
                    &value_replacements,
                ),
                &callback_replacements,
            ),
            &capture_names,
        );
        let extra_blocked_names = candidate
            .public_names
            .iter()
            .cloned()
            .chain(capture_names.iter().cloned());
        let pending_len = self.pending_variants.len();
        let generated_names_before = self.generated_variant_names.clone();
        let Some(mut variant_body) = self.optimized_variant_body(
            &candidate.binding,
            &candidate.binding.name,
            &variant_name,
            extra_blocked_names,
            VariantSpecializations {
                dict: &dict_replacements,
                values: &value_replacements,
                callbacks: &callback_replacements,
            },
        ) else {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        };
        let has_arg_specialization = !dict_replacements.is_empty()
            || !value_replacements.is_empty()
            || !callback_replacements.is_empty();
        if !variant_body_has_useful_specialization(
            &candidate.binding.body,
            &variant_body,
            has_arg_specialization,
            has_hidden_effect_specialization,
        ) || (require_no_residual_yields && expr_yield_count(&variant_body) != 0)
        {
            self.pending_variants.truncate(pending_len);
            self.generated_variant_names = generated_names_before;
            return (MExpr::App { head, args, source }, Change::Unchanged);
        }

        let (variant_params, args) = prune_unused_dict_variant_args(
            &candidate.binding.params,
            args,
            &variant_body,
            &dict_replacements,
        );
        let (variant_params, args) =
            append_capture_variant_args(variant_params, args, &capture_names, source);
        variant_body =
            append_capture_args_to_self_calls(variant_body, &variant_name, &capture_names, source);
        self.push_function_variant(
            &variant_name,
            variant_body,
            candidate.binding.clone(),
            variant_params,
        );

        (
            MExpr::App {
                head: Atom::Var {
                    name: MVar {
                        name: variant_name,
                        id: head_id,
                    },
                    source: candidate.binding.id,
                },
                args,
                source,
            },
            Change::Changed,
        )
    }

    fn try_imported_private_helper_call(&mut self, expr: MExpr) -> (MExpr, Change) {
        let MExpr::App { head, args, source } = expr else {
            return (expr, Change::Unchanged);
        };

        let Some((head_name, head_id, head_source)) = imported_variant_head_info(&head) else {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        };
        if is_generated_variant_name(&head_name)
            || self.inline_blocked_names.iter().any(|n| n == &head_name)
        {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        }

        let Some(resolved) = self.context.resolution.get(&head_source) else {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        };
        if !matches!(resolved.kind, ResolvedCodegenKind::BeamFunction { .. }) {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        }

        let Some(candidate) = self.lookup_imported_private_helper(resolved) else {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        };
        if args.len() != candidate.binding.params.len() {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        }

        let helper_name = imported_private_helper_variant_name(
            &candidate.source_module,
            &candidate.binding.name,
            &self.handler_stack,
        );
        if !self.generated_variant_names.contains(&helper_name)
            && !self.in_progress_private_helpers.contains(&helper_name)
        {
            self.in_progress_private_helpers.insert(helper_name.clone());
            let body =
                self.optimized_imported_private_helper_body(&candidate.binding, &helper_name);
            self.in_progress_private_helpers.remove(&helper_name);
            self.push_function_variant(
                &helper_name,
                body,
                candidate.binding.clone(),
                candidate.binding.params.clone(),
            );
        }

        (
            MExpr::App {
                head: Atom::Var {
                    name: MVar {
                        name: helper_name,
                        id: head_id,
                    },
                    source: candidate.binding.id,
                },
                args,
                source,
            },
            Change::Changed,
        )
    }

    fn optimized_variant_body(
        &mut self,
        binding: &MFunBinding,
        old_name: &str,
        variant_name: &str,
        extra_blocked_names: impl IntoIterator<Item = String>,
        specializations: VariantSpecializations<'_>,
    ) -> Option<MExpr> {
        let mut variant_body =
            rewrite_direct_calls_to_name(binding.body.clone(), old_name, variant_name, binding.id);
        for replacement in specializations.dict {
            let free_names = free_atom_names(&replacement.replacement);
            let substituted = subst_expr(
                variant_body,
                &replacement.target,
                &replacement.replacement,
                &free_names,
            );
            if substituted.blocked {
                return None;
            }
            variant_body = substituted.value;
        }
        for replacement in specializations.values {
            let free_names = free_atom_names(&replacement.replacement);
            let substituted = subst_expr(
                variant_body,
                &replacement.target,
                &replacement.replacement,
                &free_names,
            );
            if substituted.blocked {
                return None;
            }
            variant_body = substituted.value;
        }
        for replacement in specializations.callbacks {
            variant_body = rewrite_direct_callback_calls(
                variant_body,
                &replacement.target,
                &replacement.candidate,
            )?;
        }

        let old_blocked_len = self.inline_blocked_names.len();
        self.inline_blocked_names
            .extend(bound_names_in_pats(&binding.params));
        self.inline_blocked_names.extend(extra_blocked_names);
        let mut optimized_body = variant_body;
        let mut body_change = Change::Unchanged;
        loop {
            let (next_body, change) = self.optimize_expr(optimized_body);
            if change == Change::Unchanged {
                optimized_body = next_body;
                break;
            }
            body_change = Change::Changed;
            optimized_body = next_body;
        }
        self.inline_blocked_names.truncate(old_blocked_len);

        if body_change == Change::Unchanged {
            None
        } else {
            Some(optimized_body)
        }
    }

    fn optimized_imported_private_helper_body(
        &mut self,
        binding: &MFunBinding,
        helper_name: &str,
    ) -> MExpr {
        let old_blocked_len = self.inline_blocked_names.len();
        self.inline_blocked_names
            .extend(bound_names_in_pats(&binding.params));
        let mut optimized_body = rewrite_direct_calls_to_name(
            binding.body.clone(),
            &binding.name,
            helper_name,
            binding.id,
        );
        loop {
            let (next_body, change) = self.optimize_expr(optimized_body);
            optimized_body = next_body;
            if change == Change::Unchanged {
                break;
            }
        }
        self.inline_blocked_names.truncate(old_blocked_len);
        optimized_body
    }

    fn push_function_variant(
        &mut self,
        variant_name: &str,
        variant_body: MExpr,
        source_binding: MFunBinding,
        params: Vec<Pat>,
    ) {
        if self.generated_variant_names.contains(variant_name) {
            return;
        }
        self.generated_variant_names
            .insert(variant_name.to_string());
        self.pending_variants.push(MDecl::FunBinding(MFunBinding {
            name: variant_name.to_string(),
            public: false,
            params,
            body: variant_body,
            ..source_binding
        }));
    }

    pub(super) fn lookup_imported_function_variant(
        &self,
        resolved: &crate::codegen::resolve::ResolvedSymbol,
    ) -> Option<ImportedFunctionVariantCandidate> {
        if let Some(candidate) = self
            .context
            .imported_function_variants
            .get(&resolved.canonical_name)
        {
            if self.is_current_module(&candidate.source_module) {
                return None;
            }
            return Some(candidate.clone());
        }

        let mut matching = self
            .context
            .imported_function_variants
            .values()
            .filter(|candidate| {
                candidate.binding.name == resolved.name
                    && source_module_matches(
                        resolved.source_module.as_deref(),
                        &candidate.source_module,
                    )
            });
        let candidate = matching.next()?;
        if matching.next().is_some() {
            return None;
        }
        if self.is_current_module(&candidate.source_module) {
            return None;
        }
        Some(candidate.clone())
    }

    fn lookup_imported_handler_factory(
        &self,
        head: &Atom,
    ) -> Option<ImportedHandlerFactoryCandidate> {
        let (head_name, _, head_source) = imported_variant_head_info(head)?;
        if self.inline_blocked_names.iter().any(|n| n == &head_name) {
            return None;
        }
        let resolved = self.context.resolution.get(&head_source)?;
        if !matches!(resolved.kind, ResolvedCodegenKind::BeamFunction { .. }) {
            return None;
        }
        if let Some(candidate) = self
            .context
            .imported_handler_factories
            .get(&resolved.canonical_name)
        {
            if self.is_current_module(&candidate.source_module) {
                return None;
            }
            return Some(candidate.clone());
        }

        let mut matching = self
            .context
            .imported_handler_factories
            .values()
            .filter(|candidate| {
                head_name == resolved.name
                    && source_module_matches(
                        resolved.source_module.as_deref(),
                        &candidate.source_module,
                    )
            });
        let candidate = matching.next()?;
        if matching.next().is_some() {
            return None;
        }
        if self.is_current_module(&candidate.source_module) {
            return None;
        }
        Some(candidate.clone())
    }

    fn lookup_imported_private_helper(
        &self,
        resolved: &crate::codegen::resolve::ResolvedSymbol,
    ) -> Option<ImportedPrivateHelperCandidate> {
        if let Some(candidate) = self
            .context
            .imported_private_helpers
            .get(&resolved.canonical_name)
        {
            if self.is_current_module(&candidate.source_module) {
                return None;
            }
            return Some(candidate.clone());
        }

        let mut matching = self
            .context
            .imported_private_helpers
            .values()
            .filter(|candidate| {
                candidate.binding.name == resolved.name
                    && source_module_matches(
                        resolved.source_module.as_deref(),
                        &candidate.source_module,
                    )
            });
        let candidate = matching.next()?;
        if matching.next().is_some() {
            return None;
        }
        if self.is_current_module(&candidate.source_module) {
            return None;
        }
        Some(candidate.clone())
    }

    fn is_current_module(&self, module: &str) -> bool {
        self.context
            .current_module
            .as_deref()
            .is_some_and(|current| modules_match(current, module))
    }

    fn handler_stack_capture_names(&self) -> Vec<String> {
        let mut in_scope = HashSet::new();
        in_scope.extend(self.inline_blocked_names.iter().cloned());
        for (name, _) in &self.handler_value_bindings {
            in_scope.insert(name.clone());
        }
        for (name, _) in &self.dict_value_bindings {
            in_scope.insert(name.clone());
        }
        for (name, _) in &self.dict_method_bindings {
            in_scope.insert(name.clone());
        }
        for (name, _) in &self.pure_atom_bindings {
            in_scope.insert(name.clone());
        }

        let mut captures = HashSet::new();
        for frame in &self.handler_stack {
            if let HandlerFrame::Static { arms, .. } = frame {
                for arm in arms {
                    collect_handler_arm_free_names(arm, &mut captures, &HashSet::new());
                }
            }
        }
        let mut captures = captures
            .into_iter()
            .filter(|name| in_scope.contains(name))
            .collect::<Vec<_>>();
        captures.sort();
        captures
    }

    fn variant_capture_names<'a>(
        &self,
        extra_captures: impl IntoIterator<Item = &'a String>,
    ) -> Vec<String> {
        let mut captures = self.handler_stack_capture_names();
        captures.extend(extra_captures.into_iter().cloned());
        captures.sort();
        captures.dedup();
        captures
    }

    fn native_variant_stack_eligible(&self) -> bool {
        let mut has_native = false;
        for frame in &self.handler_stack {
            match frame {
                HandlerFrame::Native { .. } => has_native = true,
                HandlerFrame::Static { .. } => return false,
                HandlerFrame::Blocking { .. } => {}
            }
        }
        has_native
    }

    fn static_variant_stack_eligible(&self) -> bool {
        let mut has_static = false;
        for frame in &self.handler_stack {
            match frame {
                HandlerFrame::Static { .. } => has_static = true,
                HandlerFrame::Native { .. } => return false,
                HandlerFrame::Blocking { .. } => {}
            }
        }
        has_static
    }

    fn optimize_spawn_callback_atom(&mut self, atom: Atom) -> (Atom, Change) {
        match atom {
            Atom::Lambda {
                params,
                body,
                source,
            } => {
                let blocked_names = bound_names_in_pats(&params);
                let (body, change) = self.optimize_expr_with_blocked_names(blocked_names, *body);
                (
                    Atom::Lambda {
                        params,
                        body: Box::new(body),
                        source,
                    },
                    change,
                )
            }
            other => self.optimize_atom(other),
        }
    }

    fn try_inline_helper_call(&self, expr: MExpr) -> (MExpr, Change) {
        if !self.opts.helper_inline() || self.handler_stack.is_empty() {
            return (expr, Change::Unchanged);
        }

        let MExpr::App { head, args, source } = expr else {
            return (expr, Change::Unchanged);
        };

        let Atom::Var { name, .. } = &head else {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        };
        if let Some(candidate) = self.lookup_dict_method(&name.name) {
            let Some(inlined) = inline_helper_candidate(&candidate, &args) else {
                return (MExpr::App { head, args, source }, Change::Unchanged);
            };
            let has_known_case_arg = args.iter().any(|arg| closed_case_scrutinee(arg).is_some());
            if (!has_known_case_arg && expr_node_count(&inlined) > FUNCTION_VARIANT_BODY_BUDGET)
                || (!self.expr_has_specialization_opportunity(&inlined) && !expr_is_pure(&inlined))
            {
                return (MExpr::App { head, args, source }, Change::Unchanged);
            }
            return (inlined, Change::Changed);
        }

        if self.inline_blocked_names.iter().any(|n| n == &name.name) {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        }

        let Some(candidate) = self.inline_candidates.get(&name.name) else {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        };
        let Some(inlined) = inline_helper_candidate(candidate, &args) else {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        };
        if !self.expr_has_specialization_opportunity(&inlined) {
            return (MExpr::App { head, args, source }, Change::Unchanged);
        }

        (inlined, Change::Changed)
    }

    fn expr_has_specialization_opportunity(&self, expr: &MExpr) -> bool {
        self.effect_summary(expr).has_specialization_opportunity()
            || expr_contains_dict_method_access(expr)
    }

    fn effect_summary(&self, expr: &MExpr) -> EffectSummary {
        let mut call_stack = HashSet::new();
        self.effect_summary_expr(expr, &mut call_stack, &self.handler_stack)
    }

    fn effect_summary_expr(
        &self,
        expr: &MExpr,
        call_stack: &mut HashSet<String>,
        handler_stack: &[HandlerFrame],
    ) -> EffectSummary {
        match expr {
            MExpr::Yield { op, args, .. } => {
                let mut summary = EffectSummary::default();
                if self.yield_is_erasable_under_stack(op, args, handler_stack) {
                    summary.erasable_yields += 1;
                } else {
                    summary.residual_yields += 1;
                }
                for arg in args {
                    summary.add_assign(Self::effect_summary_atom(arg));
                }
                summary
            }
            MExpr::Pure(atom) | MExpr::Resume { value: atom, .. } => {
                Self::effect_summary_atom(atom)
            }
            MExpr::Bind { value, body, .. } | MExpr::Let { value, body, .. } => {
                let mut summary = self.effect_summary_expr(value, call_stack, handler_stack);
                summary.add_assign(self.effect_summary_expr(body, call_stack, handler_stack));
                summary
            }
            MExpr::Ensure { body, cleanup } => {
                let mut summary = self.effect_summary_expr(body, call_stack, handler_stack);
                summary.add_assign(self.effect_summary_expr(cleanup, call_stack, handler_stack));
                summary
            }
            MExpr::Case {
                scrutinee, arms, ..
            } => {
                let mut summary = Self::effect_summary_atom(scrutinee);
                for arm in arms {
                    if let Some(guard) = &arm.guard {
                        summary.add_assign(self.effect_summary_expr(
                            guard,
                            call_stack,
                            handler_stack,
                        ));
                    }
                    summary.add_assign(self.effect_summary_expr(
                        &arm.body,
                        call_stack,
                        handler_stack,
                    ));
                }
                summary
            }
            MExpr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                let mut summary = Self::effect_summary_atom(cond);
                summary.add_assign(self.effect_summary_expr(
                    then_branch,
                    call_stack,
                    handler_stack,
                ));
                summary.add_assign(self.effect_summary_expr(
                    else_branch,
                    call_stack,
                    handler_stack,
                ));
                summary
            }
            MExpr::App { head, args, .. } => {
                let mut summary = Self::effect_summary_atom(head);
                for arg in args {
                    summary.add_assign(Self::effect_summary_atom(arg));
                }
                if let Some((key, body)) = self.summary_callee_body(head, args)
                    && call_stack.insert(key.clone())
                {
                    let callee_summary = self.effect_summary_expr(&body, call_stack, handler_stack);
                    if callee_summary.has_specialization_opportunity() {
                        summary.summarized_calls += 1;
                    }
                    summary.add_assign(callee_summary);
                    call_stack.remove(&key);
                }
                summary
            }
            MExpr::With { handler, body, .. } => {
                let mut summary = self.effect_summary_handler(handler, call_stack, handler_stack);
                if let Some(frame) = handler_frame(handler) {
                    let mut nested_stack = handler_stack.to_vec();
                    nested_stack.push(frame);
                    summary.add_assign(self.effect_summary_expr(body, call_stack, &nested_stack));
                } else {
                    summary.add_assign(self.effect_summary_expr(body, call_stack, handler_stack));
                }
                summary
            }
            MExpr::FieldAccess { record, .. } | MExpr::UnaryMinus { value: record, .. } => {
                Self::effect_summary_atom(record)
            }
            MExpr::DictMethodAccess { dict, .. } => Self::effect_summary_atom(dict),
            MExpr::RecordUpdate { record, fields, .. } => {
                let mut summary = Self::effect_summary_atom(record);
                for (_, atom) in fields {
                    summary.add_assign(Self::effect_summary_atom(atom));
                }
                summary
            }
            MExpr::ForeignCall { args, .. } => {
                let mut summary = EffectSummary::default();
                for arg in args {
                    summary.add_assign(Self::effect_summary_atom(arg));
                }
                summary
            }
            MExpr::BinOp { left, right, .. } => {
                let mut summary = Self::effect_summary_atom(left);
                summary.add_assign(Self::effect_summary_atom(right));
                summary
            }
            MExpr::BitString { segments, .. } => {
                let mut summary = EffectSummary::default();
                for segment in segments {
                    summary.add_assign(Self::effect_summary_atom(&segment.value));
                    if let Some(size) = &segment.size {
                        summary.add_assign(Self::effect_summary_atom(size));
                    }
                }
                summary
            }
            MExpr::Receive { arms, after, .. } => {
                let mut summary = EffectSummary::default();
                for arm in arms {
                    if let Some(guard) = &arm.guard {
                        summary.add_assign(self.effect_summary_expr(
                            guard,
                            call_stack,
                            handler_stack,
                        ));
                    }
                    summary.add_assign(self.effect_summary_expr(
                        &arm.body,
                        call_stack,
                        handler_stack,
                    ));
                }
                if let Some((timeout, body)) = after {
                    summary.add_assign(Self::effect_summary_atom(timeout));
                    summary.add_assign(self.effect_summary_expr(body, call_stack, handler_stack));
                }
                summary
            }
            MExpr::LetFun { body, rest, .. } => {
                let mut summary = self.effect_summary_expr(body, call_stack, handler_stack);
                summary.add_assign(self.effect_summary_expr(rest, call_stack, handler_stack));
                summary
            }
            MExpr::HandlerValue {
                arms,
                return_clause,
                ..
            } => {
                let mut summary = EffectSummary::default();
                for arm in arms {
                    summary.add_assign(self.effect_summary_handler_arm(
                        arm,
                        call_stack,
                        handler_stack,
                    ));
                }
                if let Some(arm) = return_clause {
                    summary.add_assign(self.effect_summary_handler_arm(
                        arm,
                        call_stack,
                        handler_stack,
                    ));
                }
                summary
            }
        }
    }

    fn effect_summary_atom(atom: &Atom) -> EffectSummary {
        match atom {
            Atom::Ctor { args, .. } | Atom::Tuple { elements: args, .. } => {
                let mut summary = EffectSummary::default();
                for arg in args {
                    summary.add_assign(Self::effect_summary_atom(arg));
                }
                summary
            }
            Atom::AnonRecord { fields, .. } | Atom::Record { fields, .. } => {
                let mut summary = EffectSummary::default();
                for (_, atom) in fields {
                    summary.add_assign(Self::effect_summary_atom(atom));
                }
                summary
            }
            Atom::Lambda { body, .. } => {
                // Lambdas run under the handler stack at their eventual call
                // site, not necessarily the stack where the closure value is
                // created. Keep this summary about immediate call bodies.
                if expr_contains_yield(body) {
                    EffectSummary {
                        blockers: 1,
                        ..EffectSummary::default()
                    }
                } else {
                    EffectSummary::default()
                }
            }
            Atom::BackendSpawnThunk { callback, .. } => Self::effect_summary_atom(callback),
            Atom::Var { .. }
            | Atom::Lit { .. }
            | Atom::DictRef { .. }
            | Atom::QualifiedRef { .. }
            | Atom::Symbol { .. }
            | Atom::BackendAtom { .. } => EffectSummary::default(),
        }
    }

    fn effect_summary_handler(
        &self,
        handler: &MHandler,
        call_stack: &mut HashSet<String>,
        handler_stack: &[HandlerFrame],
    ) -> EffectSummary {
        match handler {
            MHandler::Static {
                arms,
                return_clause,
                ..
            } => {
                let mut summary = EffectSummary::default();
                for arm in arms {
                    summary.add_assign(self.effect_summary_handler_arm(
                        arm,
                        call_stack,
                        handler_stack,
                    ));
                }
                if let Some(arm) = return_clause {
                    summary.add_assign(self.effect_summary_handler_arm(
                        arm,
                        call_stack,
                        handler_stack,
                    ));
                }
                summary
            }
            MHandler::Composite { handlers, .. } => {
                let mut summary = EffectSummary::default();
                for handler in handlers {
                    summary.add_assign(self.effect_summary_handler(
                        handler,
                        call_stack,
                        handler_stack,
                    ));
                }
                summary
            }
            MHandler::Dynamic {
                op_tuple,
                return_lambda,
                ..
            } => {
                let mut summary = Self::effect_summary_atom(op_tuple);
                if let Some(return_lambda) = return_lambda {
                    summary.add_assign(Self::effect_summary_atom(return_lambda));
                }
                summary
            }
            MHandler::Native { .. } => EffectSummary::default(),
        }
    }

    fn effect_summary_handler_arm(
        &self,
        arm: &MHandlerArm,
        call_stack: &mut HashSet<String>,
        handler_stack: &[HandlerFrame],
    ) -> EffectSummary {
        let mut summary = self.effect_summary_expr(&arm.body, call_stack, handler_stack);
        if let Some(cleanup) = &arm.finally_block {
            summary.add_assign(self.effect_summary_expr(cleanup, call_stack, handler_stack));
        }
        summary
    }

    fn yield_is_erasable_under_stack(
        &self,
        op: &crate::codegen::monadic::ir::EffectOpRef,
        args: &[Atom],
        handler_stack: &[HandlerFrame],
    ) -> bool {
        self.resolve_direct_call_arm_in_stack(handler_stack, op)
            .is_some_and(|arm| inline_tail_resumptive_arm(arm, args).is_some())
            || self
                .resolve_finally_direct_call_arm_in_stack(handler_stack, op)
                .is_some_and(|arm| {
                    inline_tail_resumptive_arm(arm, args)
                        .and_then(|inlined| inlined.finally_block)
                        .is_some_and(|cleanup| {
                            cleanup_vars_are_available_at_perform_site(&cleanup, args)
                        })
                })
            || self
                .resolve_native_direct_call_handler_in_stack(handler_stack, op)
                .and_then(|handler| {
                    native_direct_call_expr(handler, op, args, crate::ast::NodeId(0))
                })
                .is_some()
    }

    fn summary_callee_body(&self, head: &Atom, args: &[Atom]) -> Option<(String, MExpr)> {
        let (head_name, _, head_source) = imported_variant_head_info(head)?;
        if is_generated_variant_name(&head_name)
            || self
                .inline_blocked_names
                .iter()
                .any(|name| name == &head_name)
        {
            return None;
        }

        if let Some(candidate) = self.variant_candidates.get(&head_name)
            && args.len() == candidate.binding.params.len()
        {
            let body = self.summary_body_with_dict_replacements(&candidate.binding, args)?;
            return Some((format!("local:{}", candidate.binding.name), body));
        }

        let resolved = self.context.resolution.get(&head_source)?;
        if !matches!(resolved.kind, ResolvedCodegenKind::BeamFunction { .. }) {
            return None;
        }
        let candidate = self.lookup_imported_function_variant(resolved)?;
        if args.len() != candidate.binding.params.len() {
            return None;
        }
        let body = self.summary_body_with_dict_replacements(&candidate.binding, args)?;
        Some((
            format!(
                "imported:{}.{}",
                candidate.source_module, candidate.binding.name
            ),
            body,
        ))
    }

    fn summary_body_with_dict_replacements(
        &self,
        binding: &MFunBinding,
        args: &[Atom],
    ) -> Option<MExpr> {
        let mut body = binding.body.clone();
        for replacement in self.dict_param_replacements(&binding.params, args) {
            let free_names = free_atom_names(&replacement.replacement);
            let substituted = subst_expr(
                body,
                &replacement.target,
                &replacement.replacement,
                &free_names,
            );
            if substituted.blocked {
                return None;
            }
            body = substituted.value;
        }
        Some(body)
    }

    fn try_direct_call(&self, expr: MExpr) -> (MExpr, Change) {
        if !self.opts.direct_call() {
            return (expr, Change::Unchanged);
        }

        let MExpr::Yield { op, args, source } = expr else {
            return (expr, Change::Unchanged);
        };

        let Some(arm) = self.resolve_direct_call_arm(&op) else {
            return (MExpr::Yield { op, args, source }, Change::Unchanged);
        };

        let Some(inlined) = inline_tail_resumptive_arm(arm, &args) else {
            return (MExpr::Yield { op, args, source }, Change::Unchanged);
        };

        (rewrite_resumes_to_pure(inlined.body), Change::Changed)
    }

    fn try_inline_let_bound_handler_value(&self, expr: MExpr) -> (MExpr, Change) {
        if !self.opts.handler_value_specialization() {
            return (expr, Change::Unchanged);
        }

        let MExpr::Let { var, value, body } = expr else {
            return (expr, Change::Unchanged);
        };

        let MExpr::HandlerValue {
            effects,
            arms,
            return_clause,
            source: handler_source,
        } = *value
        else {
            return (MExpr::Let { var, value, body }, Change::Unchanged);
        };

        let handler_value = || MExpr::HandlerValue {
            effects: effects.clone(),
            arms: arms.clone(),
            return_clause: return_clause.clone(),
            source: handler_source,
        };

        let MExpr::With {
            handler:
                MHandler::Dynamic {
                    effects: dynamic_effects,
                    op_tuple,
                    return_lambda,
                    source: dynamic_source,
                },
            body: with_body,
            source: with_source,
        } = *body
        else {
            return (
                MExpr::Let {
                    var,
                    value: Box::new(handler_value()),
                    body,
                },
                Change::Unchanged,
            );
        };

        let rebuild = |return_lambda| MExpr::Let {
            var: var.clone(),
            value: Box::new(handler_value()),
            body: Box::new(MExpr::With {
                handler: MHandler::Dynamic {
                    effects: dynamic_effects.clone(),
                    op_tuple: op_tuple.clone(),
                    return_lambda,
                    source: dynamic_source,
                },
                body: with_body.clone(),
                source: with_source,
            }),
        };

        if !atom_is_var_name(&op_tuple, &var) {
            return (rebuild(return_lambda), Change::Unchanged);
        }
        if return_lambda.is_some() || !handler_effect_sets_match(&effects, &dynamic_effects) {
            return (rebuild(return_lambda), Change::Unchanged);
        }

        (
            MExpr::With {
                handler: MHandler::Static {
                    effects,
                    arms,
                    return_clause: return_clause.map(|arm| *arm),
                    source: handler_source,
                },
                body: with_body,
                source: with_source,
            },
            Change::Changed,
        )
    }

    fn try_inline_let_bound_handler_factory(&self, expr: MExpr) -> (MExpr, Change) {
        if !self.opts.handler_factory_inline() {
            return (expr, Change::Unchanged);
        }

        let (var, value, body, mode) = match expr {
            MExpr::Let { var, value, body } => (var, value, body, None),
            MExpr::Bind {
                var,
                value,
                body,
                mode,
            } => (var, value, body, Some(mode)),
            other => return (other, Change::Unchanged),
        };

        let MExpr::App { head, args, source } = *value else {
            return (rebuild_binding(var, value, body, mode), Change::Unchanged);
        };

        let local_candidate = match &head {
            Atom::Var { name, .. } => self.handler_factory_candidates.get(&name.name).cloned(),
            _ => None,
        };

        let candidate = if let Some(candidate) = local_candidate {
            candidate
        } else if let Some(candidate) = self.lookup_imported_handler_factory(&head) {
            InlineCandidate {
                params: candidate.params,
                body: candidate.body,
            }
        } else {
            return (
                rebuild_binding(var, Box::new(MExpr::App { head, args, source }), body, mode),
                Change::Unchanged,
            );
        };
        let Some(inlined) = inline_helper_candidate(&candidate, &args) else {
            return (
                rebuild_binding(var, Box::new(MExpr::App { head, args, source }), body, mode),
                Change::Unchanged,
            );
        };
        let Some((prefix, handler_value)) = split_handler_factory_body(inlined) else {
            return (
                rebuild_binding(var, Box::new(MExpr::App { head, args, source }), body, mode),
                Change::Unchanged,
            );
        };

        (
            splice_handler_factory_prefix(
                prefix,
                rebuild_binding(var, Box::new(handler_value), body, mode),
            ),
            Change::Changed,
        )
    }

    fn try_finally_direct_call(&self, expr: MExpr) -> (MExpr, Change) {
        if !self.opts.direct_call() {
            return (expr, Change::Unchanged);
        }

        let MExpr::Bind {
            var,
            value,
            body,
            mode,
        } = expr
        else {
            return (expr, Change::Unchanged);
        };

        let MExpr::Yield { op, args, .. } = &*value else {
            return (
                MExpr::Bind {
                    var,
                    value,
                    body,
                    mode,
                },
                Change::Unchanged,
            );
        };

        let Some(arm) = self.resolve_finally_direct_call_arm(op) else {
            return (
                MExpr::Bind {
                    var,
                    value,
                    body,
                    mode,
                },
                Change::Unchanged,
            );
        };

        let Some(inlined) = inline_tail_resumptive_arm(arm, args) else {
            return (
                MExpr::Bind {
                    var,
                    value,
                    body,
                    mode,
                },
                Change::Unchanged,
            );
        };
        let Some(cleanup) = inlined.finally_block else {
            return (
                MExpr::Bind {
                    var,
                    value,
                    body,
                    mode,
                },
                Change::Unchanged,
            );
        };
        if !cleanup_vars_are_available_at_perform_site(&cleanup, args) {
            return (
                MExpr::Bind {
                    var,
                    value,
                    body,
                    mode,
                },
                Change::Unchanged,
            );
        }

        let continued = MExpr::Bind {
            var,
            value: Box::new(rewrite_resumes_to_pure(inlined.body)),
            body,
            mode,
        };
        (
            MExpr::Ensure {
                body: Box::new(continued),
                cleanup: Box::new(cleanup),
            },
            Change::Changed,
        )
    }

    fn resolve_direct_call_arm(
        &self,
        op: &crate::codegen::monadic::ir::EffectOpRef,
    ) -> Option<&MHandlerArm> {
        self.resolve_direct_call_arm_in_stack(&self.handler_stack, op)
    }

    fn resolve_direct_call_arm_in_stack<'stack>(
        &self,
        handler_stack: &'stack [HandlerFrame],
        op: &crate::codegen::monadic::ir::EffectOpRef,
    ) -> Option<&'stack MHandlerArm> {
        let arms = self.innermost_static_arms_for_op_in_stack(handler_stack, op)?;
        let arm = single_matching_arm(arms, op)?;
        if arm.finally_block.is_some() {
            return None;
        }
        if expr_contains_yield(&arm.body) {
            return None;
        }
        if self.handler_analysis.resumption.get(&arm.id) != Some(&ResumptionKind::TailResumptive) {
            return None;
        }
        Some(arm)
    }

    fn resolve_finally_direct_call_arm(
        &self,
        op: &crate::codegen::monadic::ir::EffectOpRef,
    ) -> Option<&MHandlerArm> {
        self.resolve_finally_direct_call_arm_in_stack(&self.handler_stack, op)
    }

    fn resolve_finally_direct_call_arm_in_stack<'stack>(
        &self,
        handler_stack: &'stack [HandlerFrame],
        op: &crate::codegen::monadic::ir::EffectOpRef,
    ) -> Option<&'stack MHandlerArm> {
        let arms = self.innermost_static_arms_for_op_in_stack(handler_stack, op)?;
        let arm = single_matching_arm(arms, op)?;
        let cleanup = arm.finally_block.as_ref()?;
        if cleanup.contains_resume() {
            return None;
        }
        if expr_contains_yield(&arm.body) {
            return None;
        }
        if self.handler_analysis.resumption.get(&arm.id) != Some(&ResumptionKind::TailResumptive) {
            return None;
        }
        Some(arm)
    }

    fn innermost_static_arms_for_op_in_stack<'stack>(
        &self,
        handler_stack: &'stack [HandlerFrame],
        op: &crate::codegen::monadic::ir::EffectOpRef,
    ) -> Option<&'stack [MHandlerArm]> {
        for frame in handler_stack.iter().rev() {
            if !frame.handles_effect(&op.effect) {
                continue;
            }
            return match frame {
                HandlerFrame::Static { arms, .. } => Some(arms),
                HandlerFrame::Native { .. } | HandlerFrame::Blocking { .. } => None,
            };
        }
        None
    }

    fn try_native_direct_call(&mut self, expr: MExpr) -> (MExpr, Change) {
        if !self.opts.native_direct_call() {
            return (expr, Change::Unchanged);
        }

        let MExpr::Yield { op, args, source } = expr else {
            return (expr, Change::Unchanged);
        };

        let Some(handler) = self.resolve_native_direct_call_handler(&op) else {
            return (MExpr::Yield { op, args, source }, Change::Unchanged);
        };

        if handler.rsplit('.').next().unwrap_or(handler) == "beam_actor"
            && op.effect == "Std.Actor.Process"
            && op.op == "spawn"
            && args.len() == 1
        {
            let (callback, _) = self.optimize_spawn_callback_atom(args[0].clone());
            return (
                MExpr::ForeignCall {
                    module: "erlang".to_string(),
                    func: "spawn".to_string(),
                    args: vec![backend_spawn_thunk_at(callback, source)],
                    source,
                },
                Change::Changed,
            );
        }

        let Some(direct_call) = native_direct_call_expr(handler, &op, &args, source) else {
            return (MExpr::Yield { op, args, source }, Change::Unchanged);
        };

        (direct_call, Change::Changed)
    }

    fn resolve_native_direct_call_handler(
        &self,
        op: &crate::codegen::monadic::ir::EffectOpRef,
    ) -> Option<&str> {
        self.resolve_native_direct_call_handler_in_stack(&self.handler_stack, op)
    }

    fn resolve_native_direct_call_handler_in_stack<'stack>(
        &self,
        handler_stack: &'stack [HandlerFrame],
        op: &crate::codegen::monadic::ir::EffectOpRef,
    ) -> Option<&'stack str> {
        for frame in handler_stack.iter().rev() {
            match frame {
                HandlerFrame::Native { effects, handler }
                    if effects.iter().any(|e| e == &op.effect) =>
                {
                    return Some(handler);
                }
                HandlerFrame::Static { effects, .. } | HandlerFrame::Blocking { effects }
                    if effects.iter().any(|e| e == &op.effect) =>
                {
                    return None;
                }
                _ => {}
            }
        }
        None
    }
}

fn source_module_matches(resolved: Option<&str>, candidate: &str) -> bool {
    resolved.is_none_or(|module| modules_match(module, candidate))
}

fn modules_match(left: &str, right: &str) -> bool {
    left == right || erlang_module_name(left) == erlang_module_name(right)
}

fn erlang_module_name(module: &str) -> String {
    module.to_lowercase().replace('.', "_")
}
