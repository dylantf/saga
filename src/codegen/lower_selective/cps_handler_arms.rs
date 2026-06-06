use super::*;

impl<'a, 'info> DirectLowerer<'a, 'info> {
    pub(super) fn lower_cps_static_handler_arm_group(
        &mut self,
        arms: &[&MHandlerArm],
        outer_evidence: CExpr,
        abort_marker: Option<&str>,
    ) -> CExpr {
        match arms {
            [] => self.unsupported("static handler operation group has no arms"),
            [arm] => self.lower_cps_static_handler_arm(arm, outer_evidence, abort_marker),
            [first, rest @ ..] => {
                let source_params = lower_param_names(&first.params);
                let perform_evidence = self.fresh_cps_temp("_ArmEvidence");
                let arm_k = self.fresh_cps_temp("_ArmK");
                let mut params = source_params.clone();
                params.push(perform_evidence);
                params.push(arm_k.clone());

                for arm in rest {
                    if arm.params.len() != first.params.len() {
                        self.unsupported(
                            "static handler operation arms have inconsistent parameter counts",
                        );
                    }
                }

                let scrutinee = CExpr::Tuple(
                    source_params
                        .iter()
                        .map(|param| CExpr::Var(param.clone()))
                        .collect(),
                );
                let case_arms = arms
                    .iter()
                    .map(|arm| {
                        self.push_scope();
                        self.bind_cps_handler_arm_param_locals(arm);
                        let body = self.lower_cps_handler_arm_expr(
                            &arm.body,
                            outer_evidence.clone(),
                            CExpr::Var(arm_k.clone()),
                            arm.finally_block.as_deref(),
                        );
                        let body = if self.handler_arm_is_optimized_tail_resume(arm) {
                            self.resume_direct_handler_arm_result(body, CExpr::Var(arm_k.clone()))
                        } else {
                            body
                        };
                        let body = if let Some(marker) = abort_marker
                            && self.handler_arm_semantically_aborts(arm)
                        {
                            self.wrap_aborting_handler_arm_result(body, marker)
                        } else {
                            body
                        };
                        let pat =
                            CPat::Tuple(arm.params.iter().map(|pat| self.lower_pat(pat)).collect());
                        self.pop_scope();
                        CArm {
                            pat,
                            guard: None,
                            body,
                        }
                    })
                    .collect();

                CExpr::Fun(
                    params,
                    Box::new(CExpr::Case(Box::new(scrutinee), case_arms)),
                )
            }
        }
    }

    pub(super) fn lower_cps_static_handler_arm(
        &mut self,
        arm: &MHandlerArm,
        outer_evidence: CExpr,
        abort_marker: Option<&str>,
    ) -> CExpr {
        let source_params = lower_param_names(&arm.params);
        let perform_evidence = self.fresh_cps_temp("_ArmEvidence");
        let arm_k = self.fresh_cps_temp("_ArmK");
        let mut params = source_params.clone();
        params.push(perform_evidence);
        params.push(arm_k.clone());

        self.push_scope();
        self.bind_cps_handler_arm_param_locals(arm);
        let body = self.lower_cps_handler_arm_expr(
            &arm.body,
            outer_evidence,
            CExpr::Var(arm_k.clone()),
            arm.finally_block.as_deref(),
        );
        let body = if self.handler_arm_is_optimized_tail_resume(arm) {
            self.resume_direct_handler_arm_result(body, CExpr::Var(arm_k.clone()))
        } else {
            body
        };
        let body = if let Some(marker) = abort_marker
            && self.handler_arm_semantically_aborts(arm)
        {
            self.wrap_aborting_handler_arm_result(body, marker)
        } else {
            body
        };
        let body = self.wrap_param_match(&arm.params, &source_params, body);
        self.pop_scope();

        CExpr::Fun(params, Box::new(body))
    }

    pub(super) fn lower_cps_handler_arm_expr(
        &mut self,
        expr: &MExpr,
        outer_evidence: CExpr,
        arm_k: CExpr,
        finally_block: Option<&MExpr>,
    ) -> CExpr {
        if let MExpr::Pure(atom) = expr
            && self.handler_arm_atom_is_cps_island_subset(atom)
        {
            if let Some(cleanup) = finally_block
                && !self.atom_contains_resume(atom)
            {
                return self.lower_direct_handler_result_with_finally(
                    expr,
                    cleanup,
                    outer_evidence,
                );
            }
            return self.lower_cps_handler_arm_atom(atom, outer_evidence, arm_k, finally_block);
        }
        if self.expr_is_direct_subset(expr) {
            return match finally_block {
                Some(cleanup) => {
                    self.lower_direct_handler_result_with_finally(expr, cleanup, outer_evidence)
                }
                None => self.lower_expr(expr),
            };
        }
        match expr {
            MExpr::Yield { op, args, .. } => {
                if finally_block.is_some() {
                    self.unsupported_expr(expr);
                }
                self.lower_cps_yield(op, args, outer_evidence, arm_k)
            }
            MExpr::Resume { value, .. } => {
                self.lower_resume_with_finally(value, arm_k, finally_block, outer_evidence)
            }
            MExpr::Bind {
                var, value, body, ..
            }
            | MExpr::Let { var, value, body }
                if matches!(&**value, MExpr::Resume { .. }) =>
            {
                let MExpr::Resume {
                    value: resume_value,
                    ..
                } = &**value
                else {
                    unreachable!();
                };
                let local_shape = self
                    .direct_local_shape_for_expr(value)
                    .or_else(|| self.direct_call_shape_for_local_use_in_expr(&var.name, body));
                let lowered_value = self.lower_resume_with_finally(
                    resume_value,
                    arm_k.clone(),
                    finally_block,
                    outer_evidence.clone(),
                );
                self.push_scope();
                self.current_scope_mut().insert(var.name.clone());
                if let Some(shape) = local_shape {
                    self.current_shape_scope_mut()
                        .insert(var.name.clone(), shape);
                }
                let lowered_body =
                    self.lower_cps_handler_arm_expr(body, outer_evidence, arm_k, finally_block);
                self.pop_scope();
                CExpr::Let(
                    core_var(&var.name),
                    Box::new(lowered_value),
                    Box::new(lowered_body),
                )
            }
            MExpr::Bind {
                var, value, body, ..
            }
            | MExpr::Let { var, value, body }
                if self.handler_arm_expr_is_cps_callback_call_subset(value) =>
            {
                let MExpr::App { head, args, .. } = &**value else {
                    unreachable!();
                };
                let local_shape = self.direct_local_shape_for_expr(value);
                let lowered_value =
                    self.lower_cps_callback_call_result_value(head, args, outer_evidence.clone());
                self.push_scope();
                self.current_scope_mut().insert(var.name.clone());
                if let Some(shape) = local_shape {
                    self.current_shape_scope_mut()
                        .insert(var.name.clone(), shape);
                }
                let lowered_body =
                    self.lower_cps_handler_arm_expr(body, outer_evidence, arm_k, finally_block);
                self.pop_scope();
                CExpr::Let(
                    core_var(&var.name),
                    Box::new(lowered_value),
                    Box::new(lowered_body),
                )
            }
            MExpr::Bind {
                var, value, body, ..
            }
            | MExpr::Let { var, value, body }
                if self.handler_arm_expr_is_cps_island_subset(value) =>
            {
                let local_shape = self.direct_local_shape_for_expr(value);
                let lowered_value = self.lower_cps_handler_arm_expr(
                    value,
                    outer_evidence.clone(),
                    arm_k.clone(),
                    None,
                );
                self.push_scope();
                self.current_scope_mut().insert(var.name.clone());
                if let Some(shape) = local_shape {
                    self.current_shape_scope_mut()
                        .insert(var.name.clone(), shape);
                }
                let lowered_body =
                    self.lower_cps_handler_arm_expr(body, outer_evidence, arm_k, finally_block);
                self.pop_scope();
                CExpr::Let(
                    core_var(&var.name),
                    Box::new(lowered_value),
                    Box::new(lowered_body),
                )
            }
            MExpr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => CExpr::Case(
                Box::new(self.lower_atom(cond)),
                vec![
                    CArm {
                        pat: CPat::Lit(CLit::Atom("true".to_string())),
                        guard: None,
                        body: self.lower_cps_handler_arm_expr(
                            then_branch,
                            outer_evidence.clone(),
                            arm_k.clone(),
                            finally_block,
                        ),
                    },
                    CArm {
                        pat: CPat::Lit(CLit::Atom("false".to_string())),
                        guard: None,
                        body: self.lower_cps_handler_arm_expr(
                            else_branch,
                            outer_evidence,
                            arm_k,
                            finally_block,
                        ),
                    },
                ],
            ),
            MExpr::Case {
                scrutinee, arms, ..
            } => CExpr::Case(
                Box::new(self.lower_atom(scrutinee)),
                arms.iter()
                    .map(|arm| {
                        self.lower_cps_handler_case_arm(
                            arm,
                            outer_evidence.clone(),
                            arm_k.clone(),
                            finally_block,
                        )
                    })
                    .collect(),
            ),
            MExpr::App { head, args, .. }
                if self.handler_arm_expr_is_cps_callback_call_subset(expr) =>
            {
                self.lower_cps_app(head, args, outer_evidence, arm_k)
            }
            MExpr::App { head, args, .. } => self
                .lower_flat_map_identity_resume_handler_arm(
                    head,
                    args,
                    arm_k,
                    finally_block,
                    outer_evidence,
                )
                .unwrap_or_else(|| {
                    self.unsupported_expr(&MExpr::App {
                        head: head.clone(),
                        args: args.clone(),
                        source: NodeId::fresh(),
                    })
                }),
            _ => self.unsupported_expr(expr),
        }
    }

    pub(super) fn lower_cps_handler_arm_lambda(
        &mut self,
        params: &[Pat],
        body: &MExpr,
        outer_evidence: CExpr,
        arm_k: CExpr,
        finally_block: Option<&MExpr>,
    ) -> CExpr {
        let param_names = lower_param_names(params);
        self.push_scope();
        for pat in params {
            self.bind_pat_locals(pat);
        }
        let lowered_body =
            self.lower_cps_handler_arm_expr(body, outer_evidence, arm_k, finally_block);
        let lowered_body = self.wrap_param_match(params, &param_names, lowered_body);
        self.pop_scope();
        CExpr::Fun(param_names, Box::new(lowered_body))
    }

    pub(super) fn lower_cps_handler_arm_atom(
        &mut self,
        atom: &Atom,
        outer_evidence: CExpr,
        arm_k: CExpr,
        finally_block: Option<&MExpr>,
    ) -> CExpr {
        match atom {
            Atom::Lambda { params, body, .. }
                if self.handler_arm_lambda_is_cps_island_subset(params, body) =>
            {
                self.lower_cps_handler_arm_lambda(
                    params,
                    body,
                    outer_evidence,
                    arm_k,
                    finally_block,
                )
            }
            Atom::Ctor { name, args, .. } => self.lower_cps_handler_arm_ctor_atom(
                name,
                args,
                outer_evidence,
                arm_k,
                finally_block,
            ),
            Atom::Tuple { elements, .. } => CExpr::Tuple(
                elements
                    .iter()
                    .map(|arg| {
                        self.lower_cps_handler_arm_atom(
                            arg,
                            outer_evidence.clone(),
                            arm_k.clone(),
                            finally_block,
                        )
                    })
                    .collect(),
            ),
            Atom::AnonRecord { fields, .. } => {
                let names: Vec<&str> = fields.iter().map(|(name, _)| name.as_str()).collect();
                let tag = crate::ast::anon_record_tag(&names);
                let mut sorted: Vec<&(String, Atom)> = fields.iter().collect();
                sorted.sort_by(|a, b| a.0.cmp(&b.0));
                let mut elems = vec![CExpr::Lit(CLit::Atom(tag))];
                elems.extend(sorted.into_iter().map(|(_, atom)| {
                    self.lower_cps_handler_arm_atom(
                        atom,
                        outer_evidence.clone(),
                        arm_k.clone(),
                        finally_block,
                    )
                }));
                CExpr::Tuple(elems)
            }
            Atom::Record { name, fields, .. } => {
                let mut elems = vec![CExpr::Lit(CLit::Atom(mangle_ctor_atom(name, self.ctors)))];
                elems.extend(fields.iter().map(|(_, atom)| {
                    self.lower_cps_handler_arm_atom(
                        atom,
                        outer_evidence.clone(),
                        arm_k.clone(),
                        finally_block,
                    )
                }));
                CExpr::Tuple(elems)
            }
            Atom::Lit { value, .. } => lower_lit_atom(value),
            Atom::Symbol { symbol, .. } => {
                crate::codegen::lower::util::lower_string_to_binary(symbol)
            }
            Atom::Var { .. } | Atom::QualifiedRef { .. } | Atom::DictRef { .. }
                if self.atom_is_direct_subset(atom) =>
            {
                self.lower_atom(atom)
            }
            Atom::BackendAtom { .. } | Atom::BackendSpawnThunk { .. } | Atom::DictRef { .. } => {
                self.unsupported_atom(atom)
            }
            Atom::Var { .. } | Atom::QualifiedRef { .. } => self.unsupported_atom(atom),
            Atom::Lambda { .. } => self.unsupported_atom(atom),
        }
    }

    pub(super) fn lower_cps_handler_arm_ctor_atom(
        &mut self,
        name: &str,
        args: &[Atom],
        outer_evidence: CExpr,
        arm_k: CExpr,
        finally_block: Option<&MExpr>,
    ) -> CExpr {
        let bare = name.rsplit('.').next().unwrap_or(name);
        match bare {
            "Nil" if args.is_empty() => return CExpr::Nil,
            "True" if args.is_empty() => return CExpr::Lit(CLit::Atom("true".to_string())),
            "False" if args.is_empty() => return CExpr::Lit(CLit::Atom("false".to_string())),
            _ => {}
        }
        if name == "Cons" && args.len() == 2 {
            return CExpr::Cons(
                Box::new(self.lower_cps_handler_arm_atom(
                    &args[0],
                    outer_evidence.clone(),
                    arm_k.clone(),
                    finally_block,
                )),
                Box::new(self.lower_cps_handler_arm_atom(
                    &args[1],
                    outer_evidence,
                    arm_k,
                    finally_block,
                )),
            );
        }
        let mut elems = vec![CExpr::Lit(CLit::Atom(mangle_ctor_atom(name, self.ctors)))];
        elems.extend(args.iter().map(|arg| {
            self.lower_cps_handler_arm_atom(
                arg,
                outer_evidence.clone(),
                arm_k.clone(),
                finally_block,
            )
        }));
        CExpr::Tuple(elems)
    }

    pub(super) fn lower_flat_map_identity_resume_handler_arm(
        &mut self,
        head: &Atom,
        args: &[Atom],
        arm_k: CExpr,
        finally_block: Option<&MExpr>,
        outer_evidence: CExpr,
    ) -> Option<CExpr> {
        if !self.is_flat_map_identity_resume_app(head, args) {
            return None;
        }
        let CallShape::Direct(callable) = self.call_shape(head)? else {
            return None;
        };
        let Atom::Lambda { params, body, .. } = &args[0] else {
            return None;
        };
        let MExpr::Resume { value, .. } = &**body else {
            return None;
        };

        let callback_params = lower_param_names(params);
        self.push_scope();
        for param in params {
            self.bind_pat_locals(param);
        }
        let callback_body =
            self.lower_resume_with_finally(value, arm_k, finally_block, outer_evidence);
        let callback_body = self.wrap_param_match(params, &callback_params, callback_body);
        self.pop_scope();

        let lowered_args = vec![
            CExpr::Fun(callback_params, Box::new(callback_body)),
            self.lower_atom(&args[1]),
        ];
        Some(match callable.module {
            Some(module) => CExpr::Call(module, callable.name, lowered_args),
            None => CExpr::Apply(
                Box::new(CExpr::FunRef(callable.name, callable.arity)),
                lowered_args,
            ),
        })
    }
}
