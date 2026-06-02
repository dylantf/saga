use super::*;

impl<'a, 'info> DirectLowerer<'a, 'info> {
    pub(super) fn lower_cps_expr(&mut self, expr: &MExpr, return_k: CExpr) -> CExpr {
        match expr {
            MExpr::Yield { op, args, .. } => self.lower_cps_yield(op, args, return_k),
            MExpr::Bind {
                var, value, body, ..
            } => self.lower_cps_bind(var, value, body, return_k),
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
                        body: self.lower_cps_expr(then_branch, return_k.clone()),
                    },
                    CArm {
                        pat: CPat::Lit(CLit::Atom("false".to_string())),
                        guard: None,
                        body: self.lower_cps_expr(else_branch, return_k),
                    },
                ],
            ),
            MExpr::Case {
                scrutinee, arms, ..
            } => CExpr::Case(
                Box::new(self.lower_atom(scrutinee)),
                arms.iter()
                    .map(|arm| self.lower_cps_arm(arm, return_k.clone()))
                    .collect(),
            ),
            MExpr::App { head, args, .. } => self.lower_cps_app(head, args, return_k),
            _ if self.expr_is_direct_subset(expr) => {
                CExpr::Apply(Box::new(return_k), vec![self.lower_expr(expr)])
            }
            _ => self.unsupported_expr(expr),
        }
    }

    fn lower_cps_bind(
        &mut self,
        var: &MVar,
        value: &MExpr,
        body: &MExpr,
        return_k: CExpr,
    ) -> CExpr {
        if self.expr_is_direct_subset(value) {
            let local_shape = self.direct_local_shape_for_expr(value);
            let lowered_value = self.lower_expr(value);
            self.push_scope();
            self.current_scope_mut().insert(var.name.clone());
            if let Some(shape) = local_shape {
                self.current_shape_scope_mut()
                    .insert(var.name.clone(), shape);
            }
            let lowered_body = self.lower_cps_expr(body, return_k);
            self.pop_scope();
            return CExpr::Let(
                core_var(&var.name),
                Box::new(lowered_value),
                Box::new(lowered_body),
            );
        }

        let k_arg = self.fresh_cps_temp("_CpsBindArg");
        self.push_scope();
        self.current_scope_mut().insert(var.name.clone());
        let lowered_body = self.lower_cps_expr(body, return_k);
        self.pop_scope();
        let k_body = CExpr::Let(
            core_var(&var.name),
            Box::new(CExpr::Var(k_arg.clone())),
            Box::new(lowered_body),
        );
        let k_fun = CExpr::Fun(vec![k_arg], Box::new(k_body));
        self.lower_cps_expr(value, k_fun)
    }

    fn lower_cps_yield(&mut self, op: &EffectOpRef, args: &[Atom], return_k: CExpr) -> CExpr {
        let find_call = CExpr::Call(
            "std_evidence_bridge".to_string(),
            "find_evidence".to_string(),
            vec![
                CExpr::Var("_Evidence".to_string()),
                CExpr::Lit(CLit::Atom(op.effect.clone())),
            ],
        );
        let op_closure = CExpr::Call(
            "erlang".to_string(),
            "element".to_string(),
            vec![CExpr::Lit(CLit::Int(op.op_index as i64)), find_call],
        );

        let mut apply_args: Vec<CExpr> = args.iter().map(|arg| self.lower_atom(arg)).collect();
        apply_args.push(CExpr::Var("_Evidence".to_string()));
        apply_args.push(return_k);
        CExpr::Apply(Box::new(op_closure), apply_args)
    }

    fn lower_cps_app(&mut self, head: &Atom, args: &[Atom], return_k: CExpr) -> CExpr {
        let Some(CallShape::Cps {
            module,
            name,
            source_arity,
            adapter_arity,
            ..
        }) = self.call_shape(head)
        else {
            if self.expr_is_direct_subset(&MExpr::App {
                head: head.clone(),
                args: args.to_vec(),
                source: NodeId::fresh(),
            }) {
                let value = self.lower_app(head, args);
                return CExpr::Apply(Box::new(return_k), vec![value]);
            }
            self.unsupported_expr(&MExpr::App {
                head: head.clone(),
                args: args.to_vec(),
                source: NodeId::fresh(),
            });
        };

        self.assert_app_arity(&name, args.len(), source_arity);
        self.assert_app_arity(&name, args.len() + 2, adapter_arity);

        let mut lowered_args: Vec<CExpr> = args.iter().map(|arg| self.lower_atom(arg)).collect();
        lowered_args.push(CExpr::Var("_Evidence".to_string()));
        lowered_args.push(return_k);

        match module {
            Some(module) => CExpr::Call(module, name, lowered_args),
            None => CExpr::Apply(Box::new(CExpr::FunRef(name, adapter_arity)), lowered_args),
        }
    }

    fn lower_cps_arm(&mut self, arm: &MArm, return_k: CExpr) -> CArm {
        self.push_scope();
        collect_pat_binders(&arm.pattern, self.current_scope_mut());
        let body = self.lower_cps_expr(&arm.body, return_k);
        let guard = arm.guard.as_ref().map(|g| self.lower_expr(g));
        let pat = self.lower_pat(&arm.pattern);
        self.pop_scope();
        CArm { pat, guard, body }
    }
}
