use super::*;
use crate::ast::{CaseArm, Pat};
use crate::codegen::cerl::{CArm, CExpr, CLit, CPat};
use crate::codegen::lower::util::*;
use crate::codegen::lower::*;

impl<'a> Lowerer<'a> {
    /// Lower a `case` expression over an already-bound scrutinee variable.
    ///
    /// Complex guards cannot be emitted directly in Core Erlang. When any arm
    /// contains one, we build a right-associated chain of one-arm cases so the
    /// fallthrough for each suffix is lowered exactly once.
    pub(crate) fn lower_case_expr(&mut self, scrut_var: &str, arms: &[CaseArm]) -> CExpr {
        let arms_ref: Vec<&CaseArm> = arms.iter().collect();
        if arms_ref
            .iter()
            .all(|arm| arm.guard.as_ref().is_none_or(is_guard_safe))
        {
            let mut lowered = self.lower_case_arms_inner(scrut_var, &arms_ref);
            let has_total_catchall = arms_ref
                .iter()
                .any(|arm| arm.guard.is_none() && Self::is_catchall_pat(&arm.pattern));
            if !has_total_catchall {
                lowered.push(CArm {
                    pat: CPat::Wildcard,
                    guard: None,
                    body: self.case_clause_error_expr(),
                });
            }
            return CExpr::Case(Box::new(CExpr::Var(scrut_var.to_string())), lowered);
        }

        self.lower_case_expr_chain(scrut_var, &arms_ref)
    }


    pub(crate) fn lower_case_arms_inner(&mut self, _scrut_var: &str, arms: &[&CaseArm]) -> Vec<CArm> {
        let mut result = Vec::new();

        for arm in arms {
            let pat = self.lower_pat(
                &arm.pattern,
                &self.constructor_atoms,
                self.handler_origin_module(),
            );

            match &arm.guard {
                None => {
                    result.push(CArm {
                        pat,
                        guard: None,
                        body: self.lower_expr(&arm.body),
                    });
                }
                Some(guard) if is_guard_safe(guard) => {
                    result.push(CArm {
                        pat,
                        guard: Some(self.lower_expr(guard)),
                        body: self.lower_expr(&arm.body),
                    });
                }
                Some(_guard) => {
                    unreachable!("complex guards should be handled by lower_case_expr_chain");
                }
            }
        }

        result
    }


    pub(crate) fn lower_case_expr_chain(&mut self, scrut_var: &str, arms: &[&CaseArm]) -> CExpr {
        let mut rest = self.case_clause_error_expr();

        for arm in arms.iter().rev() {
            let rest_var = self.fresh();
            let rest_ref = CExpr::Apply(Box::new(CExpr::Var(rest_var.clone())), vec![]);
            let pat = self.lower_pat(
                &arm.pattern,
                &self.constructor_atoms,
                self.handler_origin_module(),
            );
            let body_ce = self.lower_expr(&arm.body);

            let current = match &arm.guard {
                None => {
                    if Self::is_catchall_pat(&arm.pattern) {
                        self.bind_catchall_pattern(scrut_var, &arm.pattern, body_ce)
                    } else {
                        CExpr::Case(
                            Box::new(CExpr::Var(scrut_var.to_string())),
                            vec![
                                CArm {
                                    pat,
                                    guard: None,
                                    body: body_ce,
                                },
                                CArm {
                                    pat: CPat::Wildcard,
                                    guard: None,
                                    body: rest_ref,
                                },
                            ],
                        )
                    }
                }
                Some(guard) if is_guard_safe(guard) => CExpr::Case(
                    Box::new(CExpr::Var(scrut_var.to_string())),
                    vec![
                        CArm {
                            pat,
                            guard: Some(self.lower_expr(guard)),
                            body: body_ce,
                        },
                        CArm {
                            pat: CPat::Wildcard,
                            guard: None,
                            body: rest_ref,
                        },
                    ],
                ),
                Some(guard) => {
                    let guarded_body = CExpr::Case(
                        Box::new(self.lower_expr(guard)),
                        vec![
                            CArm {
                                pat: CPat::Lit(CLit::Atom("true".to_string())),
                                guard: None,
                                body: body_ce,
                            },
                            CArm {
                                pat: CPat::Wildcard,
                                guard: None,
                                body: rest_ref.clone(),
                            },
                        ],
                    );

                    if Self::is_catchall_pat(&arm.pattern) {
                        self.bind_catchall_pattern(scrut_var, &arm.pattern, guarded_body)
                    } else {
                        CExpr::Case(
                            Box::new(CExpr::Var(scrut_var.to_string())),
                            vec![
                                CArm {
                                    pat,
                                    guard: None,
                                    body: guarded_body,
                                },
                                CArm {
                                    pat: CPat::Wildcard,
                                    guard: None,
                                    body: rest_ref,
                                },
                            ],
                        )
                    }
                }
            };

            rest = CExpr::Let(
                rest_var,
                Box::new(CExpr::Fun(vec![], Box::new(rest))),
                Box::new(current),
            );
        }

        rest
    }


    pub(crate) fn case_clause_error_expr(&self) -> CExpr {
        CExpr::Call(
            "erlang".to_string(),
            "error".to_string(),
            vec![CExpr::Lit(CLit::Atom("case_clause".to_string()))],
        )
    }


    pub(crate) fn is_catchall_pat(pat: &Pat) -> bool {
        matches!(pat, Pat::Wildcard { .. } | Pat::Var { .. })
    }


    pub(crate) fn bind_catchall_pattern(&self, scrut_var: &str, pat: &Pat, body: CExpr) -> CExpr {
        match pat {
            Pat::Wildcard { .. } => body,
            Pat::Var { name, .. } => CExpr::Let(
                core_var(name),
                Box::new(CExpr::Var(scrut_var.to_string())),
                Box::new(body),
            ),
            _ => unreachable!("only catchall patterns should be rebound directly"),
        }
    }

}
