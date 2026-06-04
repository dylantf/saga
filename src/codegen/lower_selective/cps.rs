use super::*;

impl<'a, 'info> DirectLowerer<'a, 'info> {
    pub(super) fn lower_cps_expr(
        &mut self,
        expr: &MExpr,
        evidence: CExpr,
        return_k: CExpr,
    ) -> CExpr {
        match expr {
            MExpr::Yield { op, args, .. } => self.lower_cps_yield(op, args, evidence, return_k),
            MExpr::Let { var, value, body }
            | MExpr::Bind {
                var, value, body, ..
            } => self.lower_cps_bind(var, value, body, evidence, return_k),
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
                        body: self.lower_cps_expr(then_branch, evidence.clone(), return_k.clone()),
                    },
                    CArm {
                        pat: CPat::Lit(CLit::Atom("false".to_string())),
                        guard: None,
                        body: self.lower_cps_expr(else_branch, evidence, return_k),
                    },
                ],
            ),
            MExpr::Case {
                scrutinee, arms, ..
            } => self.lower_cps_case_chain(scrutinee, arms, evidence, return_k),
            MExpr::Receive { arms, after, .. } => {
                self.lower_cps_receive(arms, after.as_ref(), evidence, return_k)
            }
            MExpr::App { head, args, .. } if self.expr_is_direct_subset(expr) => {
                CExpr::Apply(Box::new(return_k), vec![self.lower_app(head, args)])
            }
            MExpr::App { head, args, .. } => self.lower_cps_app(head, args, evidence, return_k),
            MExpr::With { handler, body, .. } => {
                self.lower_cps_with(handler, body, evidence, return_k)
            }
            MExpr::BinOp {
                op, left, right, ..
            } => CExpr::Apply(
                Box::new(return_k),
                vec![binop_atoms(
                    op,
                    self.lower_atom(left),
                    self.lower_atom(right),
                )],
            ),
            MExpr::UnaryMinus { value, .. } => CExpr::Apply(
                Box::new(return_k),
                vec![CExpr::Call(
                    "erlang".to_string(),
                    "-".to_string(),
                    vec![CExpr::Lit(CLit::Int(0)), self.lower_atom(value)],
                )],
            ),
            MExpr::BitString { segments, .. } => CExpr::Apply(
                Box::new(return_k),
                vec![self.lower_bitstring_value(segments)],
            ),
            MExpr::HandlerValue {
                arms,
                return_clause,
                ..
            } => CExpr::Apply(
                Box::new(return_k),
                vec![self.lower_cps_handler_value(arms, return_clause.as_deref(), evidence)],
            ),
            _ if self.expr_is_direct_subset(expr) => {
                CExpr::Apply(Box::new(return_k), vec![self.lower_expr(expr)])
            }
            _ => self.unsupported_expr(expr),
        }
    }

    pub(super) fn lower_receive_pat(&mut self, pat: &Pat) -> (CPat, Option<(String, String)>) {
        match pat {
            Pat::Constructor { name, args, .. } if is_system_msg(name) && args.len() == 2 => {
                let pid_pat = self.lower_pat(&args[0]);
                let (reason_pat, wrapper) = match &args[1] {
                    Pat::Var { name, .. } => {
                        let raw = self.fresh_cps_temp("_RawExitReason");
                        (CPat::Var(raw.clone()), Some((core_var(name), raw)))
                    }
                    other => (self.lower_pat(other), None),
                };
                (system_msg_pattern(name, pid_pat, reason_pat), wrapper)
            }
            _ => (self.lower_pat(pat), None),
        }
    }

    pub(super) fn exit_reason_from_erlang(&mut self, raw_var: &str) -> CExpr {
        let normal = mangle_ctor_atom("Normal", self.ctors);
        let shutdown = mangle_ctor_atom("Shutdown", self.ctors);
        let killed = mangle_ctor_atom("Killed", self.ctors);
        let noproc = mangle_ctor_atom("Noproc", self.ctors);
        let error = mangle_ctor_atom("Error", self.ctors);
        let other = mangle_ctor_atom("Other", self.ctors);

        let error_msg_var = self.fresh_cps_temp("_ErrorMsg");
        let error_msg_var2 = self.fresh_cps_temp("_ErrorMsg");
        let other_var = self.fresh_cps_temp("_OtherReason");
        let fmt_var = self.fresh_cps_temp("_FormattedReason");
        let stringify = CExpr::Call(
            "unicode".to_string(),
            "characters_to_binary".to_string(),
            vec![CExpr::Call(
                "io_lib".to_string(),
                "format".to_string(),
                vec![
                    crate::codegen::lower::util::lower_string_to_binary("~p"),
                    CExpr::Cons(
                        Box::new(CExpr::Var(other_var.clone())),
                        Box::new(CExpr::Nil),
                    ),
                ],
            )],
        );

        CExpr::Case(
            Box::new(CExpr::Var(raw_var.to_string())),
            vec![
                CArm {
                    pat: CPat::Lit(CLit::Atom("normal".to_string())),
                    guard: None,
                    body: CExpr::Lit(CLit::Atom(normal)),
                },
                CArm {
                    pat: CPat::Lit(CLit::Atom("shutdown".to_string())),
                    guard: None,
                    body: CExpr::Lit(CLit::Atom(shutdown)),
                },
                CArm {
                    pat: CPat::Lit(CLit::Atom("killed".to_string())),
                    guard: None,
                    body: CExpr::Lit(CLit::Atom(killed)),
                },
                CArm {
                    pat: CPat::Lit(CLit::Atom("noproc".to_string())),
                    guard: None,
                    body: CExpr::Lit(CLit::Atom(noproc)),
                },
                CArm {
                    pat: CPat::Tuple(vec![
                        CPat::Tuple(vec![
                            CPat::Lit(CLit::Atom("saga_error".to_string())),
                            CPat::Wildcard,
                            CPat::Var(error_msg_var.clone()),
                            CPat::Wildcard,
                            CPat::Wildcard,
                            CPat::Wildcard,
                            CPat::Wildcard,
                        ]),
                        CPat::Wildcard,
                    ]),
                    guard: None,
                    body: CExpr::Tuple(vec![
                        CExpr::Lit(CLit::Atom(error.clone())),
                        CExpr::Var(error_msg_var),
                    ]),
                },
                CArm {
                    pat: CPat::Tuple(vec![CPat::Var(error_msg_var2.clone()), CPat::Wildcard]),
                    guard: Some(CExpr::Call(
                        "erlang".to_string(),
                        "is_binary".to_string(),
                        vec![CExpr::Var(error_msg_var2.clone())],
                    )),
                    body: CExpr::Tuple(vec![
                        CExpr::Lit(CLit::Atom(error)),
                        CExpr::Var(error_msg_var2),
                    ]),
                },
                CArm {
                    pat: CPat::Var(other_var.clone()),
                    guard: None,
                    body: CExpr::Let(
                        fmt_var.clone(),
                        Box::new(stringify),
                        Box::new(CExpr::Tuple(vec![
                            CExpr::Lit(CLit::Atom(other)),
                            CExpr::Var(fmt_var),
                        ])),
                    ),
                },
            ],
        )
    }
}

fn is_system_msg(ctor_name: &str) -> bool {
    let bare = ctor_name.rsplit('.').next().unwrap_or(ctor_name);
    matches!(bare, "Down" | "Exit")
}

fn system_msg_pattern(ctor_name: &str, pid_pat: CPat, reason_pat: CPat) -> CPat {
    let bare = ctor_name.rsplit('.').next().unwrap_or(ctor_name);
    match bare {
        "Down" => CPat::Tuple(vec![
            CPat::Lit(CLit::Atom("DOWN".to_string())),
            CPat::Wildcard,
            CPat::Lit(CLit::Atom("process".to_string())),
            pid_pat,
            reason_pat,
        ]),
        "Exit" => CPat::Tuple(vec![
            CPat::Lit(CLit::Atom("EXIT".to_string())),
            pid_pat,
            reason_pat,
        ]),
        _ => unreachable!("not a system message: {ctor_name}"),
    }
}
