use super::*;
use crate::ast::{BinOp, Expr, Pat};
use crate::codegen::cerl::{CArm, CExpr, CLit, CPat};
use crate::token::Span;
use crate::typechecker::Type;
use crate::codegen::lower::util::*;
use crate::codegen::lower::*;

impl<'a> Lowerer<'a> {
    /// Lower a saturated constructor call to the appropriate Core Erlang form.
    pub(crate) fn lower_ctor_with_origin(
        &mut self,
        name: &str,
        args: Vec<&Expr>,
        origin_module: Option<&str>,
    ) -> CExpr {
        let bare_name = name.rsplit('.').next().unwrap_or(name);
        match bare_name {
            "Nil" if args.is_empty() => return CExpr::Nil,
            "True" if args.is_empty() => return CExpr::Lit(CLit::Atom("true".to_string())),
            "False" if args.is_empty() => return CExpr::Lit(CLit::Atom("false".to_string())),
            _ if args.is_empty()
                && crate::codegen::lower::beam_interop::exit_reason_bare_atom(bare_name).is_some() =>
            {
                return CExpr::Lit(CLit::Atom(
                    crate::codegen::lower::beam_interop::exit_reason_bare_atom(bare_name)
                        .unwrap()
                        .to_string(),
                ));
            }
            _ => {}
        }
        match name {
            "Cons" if args.len() == 2 => {
                let head_var = self.fresh();
                let tail_var = self.fresh();
                let head_ce = self.lower_expr_value(args[0]);
                let tail_ce = self.lower_expr_value(args[1]);
                CExpr::Let(
                    head_var.clone(),
                    Box::new(head_ce),
                    Box::new(CExpr::Let(
                        tail_var.clone(),
                        Box::new(tail_ce),
                        Box::new(CExpr::Cons(
                            Box::new(CExpr::Var(head_var)),
                            Box::new(CExpr::Var(tail_var)),
                        )),
                    )),
                )
            }
            _ => {
                // ADT constructor: tagged tuple {name, arg1, arg2, ...}
                // Look up field types from the constructor's scheme so that
                // lambda args inherit a `lambda_effect_context` and get the
                // proper CPS expansion (evidence + _ReturnK).
                let field_tys: Vec<Option<crate::typechecker::Type>> = {
                    let scheme = self.check_result.constructors.get(name);
                    if let Some(scheme) = scheme {
                        let mut tys = Vec::new();
                        let mut current = &scheme.ty;
                        while let crate::typechecker::Type::Fun(param, ret, _) = current {
                            tys.push(Some((**param).clone()));
                            current = ret;
                        }
                        tys
                    } else {
                        vec![None; args.len()]
                    }
                };

                let mut vars: Vec<String> = Vec::new();
                let mut bindings: Vec<(String, CExpr)> = Vec::new();
                for (idx, arg) in args.iter().enumerate() {
                    let var = self.fresh();
                    let val = match field_tys.get(idx).and_then(|t| t.as_ref()) {
                        Some(ty) => self.lower_expr_value_with_expected_type(arg, Some(ty)),
                        None => self.lower_expr_value(arg),
                    };
                    vars.push(var.clone());
                    bindings.push((var, val));
                }
                let atom = mangle_ctor_atom(
                    name,
                    &self.constructor_atoms,
                    origin_module.or_else(|| self.handler_origin_module()),
                );
                let mut elems = vec![CExpr::Lit(CLit::Atom(atom))];
                elems.extend(vars.iter().map(|v| CExpr::Var(v.clone())));
                let tuple = CExpr::Tuple(elems);
                bindings.into_iter().rev().fold(tuple, |body, (var, val)| {
                    CExpr::Let(var, Box::new(val), Box::new(body))
                })
            }
        }
    }


    /// Bind a possibly-effectful expression to `var_name` for use in `body`.
    /// If the expression is effectful, this CPS-chains it so that an aborting
    /// handler bypasses `body` entirely; otherwise emits a plain `let`.
    ///
    /// This is the load-bearing primitive for routing potentially-effectful
    /// sub-expressions through composite forms (constructor args, tuple
    /// elements, binop operands, case scrutinees, etc.).
    pub(crate) fn lower_bind_expr_with_cps(
        &mut self,
        expr: &Expr,
        var_name: String,
        expected: Option<Type>,
        body: CExpr,
    ) -> CExpr {
        if self.expr_is_effectful_call(expr) || self.has_nested_effectful_expr(expr) {
            let inner_k = CExpr::Fun(vec![var_name], Box::new(body));
            let inner_k_var = self.fresh();
            let inner_body = if self.expr_is_effectful_call(expr) {
                self.lower_expr_with_call_return_k(expr, Some(CExpr::Var(inner_k_var.clone())))
            } else {
                self.lower_expr_with_k_inner(expr, &inner_k_var)
            };
            CExpr::Let(inner_k_var, Box::new(inner_k), Box::new(inner_body))
        } else {
            let ce = match expected {
                Some(ty) => self.lower_expr_value_with_expected_type(expr, Some(&ty)),
                None => self.lower_expr_value(expr),
            };
            CExpr::Let(var_name, Box::new(ce), Box::new(body))
        }
    }


    /// Assemble a composite expression from `slots`, then apply `k_var` to
    /// the result. Effectful slots are CPS-chained so an aborting handler
    /// bypasses both the assembly and the outer continuation.
    ///
    /// `build` receives one fresh variable name per slot, in order, and
    /// returns the CExpr that combines them into the final value.
    /// Evaluation order is left-to-right (slot 0 evaluates first).
    pub(crate) fn lower_with_cps_slots<F>(
        &mut self,
        slots: Vec<CpsSlot<'_>>,
        k_var: &str,
        build: F,
    ) -> CExpr
    where
        F: FnOnce(&mut Self, &[String]) -> CExpr,
    {
        let vars: Vec<String> = (0..slots.len()).map(|_| self.fresh()).collect();
        let built = build(self, &vars);
        let mut body = CExpr::Apply(Box::new(CExpr::Var(k_var.to_string())), vec![built]);
        for (slot, var) in slots.into_iter().zip(vars.iter()).rev() {
            body = match slot {
                CpsSlot::Pure(ce) => CExpr::Let(var.clone(), Box::new(ce), Box::new(body)),
                CpsSlot::Expr { expr, expected } => {
                    self.lower_bind_expr_with_cps(expr, var.clone(), expected, body)
                }
            };
        }
        body
    }


    /// Lower a saturated constructor call and apply `k_var` to the constructed
    /// value. Effectful args are CPS-chained so an aborting handler skips the
    /// constructor wrapping (and `k_var`) instead of leaking its abort tuple
    /// into a constructor slot.
    ///
    /// Mirrors [`lower_record_create_with_k`] for ADT constructors.
    pub(crate) fn lower_ctor_with_k_origin(
        &mut self,
        name: &str,
        args: Vec<&Expr>,
        k_var: &str,
        origin_module: Option<&str>,
    ) -> CExpr {
        let bare = name.rsplit('.').next().unwrap_or(name);
        let is_cons = name == "Cons" && args.len() == 2;
        let is_bare_atom = args.is_empty()
            && (matches!(bare, "Nil" | "True" | "False")
                || crate::codegen::lower::beam_interop::exit_reason_bare_atom(bare).is_some());

        // For bare-atom/empty-arg ctors there's nothing to CPS-chain; defer.
        if is_bare_atom {
            let ce = self.lower_ctor_with_origin(name, args, origin_module);
            return self.lower_value_to_k_with_ce(ce, k_var);
        }

        let field_tys: Vec<Option<crate::typechecker::Type>> = if is_cons {
            vec![None, None]
        } else if let Some(scheme) = self.check_result.constructors.get(name) {
            let mut tys = Vec::new();
            let mut current = &scheme.ty;
            while let crate::typechecker::Type::Fun(param, ret, _) = current {
                tys.push(Some((**param).clone()));
                current = ret;
            }
            tys
        } else {
            vec![None; args.len()]
        };

        let slots: Vec<CpsSlot<'_>> = args
            .iter()
            .enumerate()
            .map(|(i, &arg)| CpsSlot::Expr {
                expr: arg,
                expected: field_tys.get(i).and_then(|t| t.clone()),
            })
            .collect();

        let is_cons_local = is_cons;
        let name_owned = name.to_string();
        self.lower_with_cps_slots(slots, k_var, |this, vars| {
            if is_cons_local {
                CExpr::Cons(
                    Box::new(CExpr::Var(vars[0].clone())),
                    Box::new(CExpr::Var(vars[1].clone())),
                )
            } else {
                let atom = mangle_ctor_atom(
                    &name_owned,
                    &this.constructor_atoms,
                    origin_module.or_else(|| this.handler_origin_module()),
                );
                let mut elems = vec![CExpr::Lit(CLit::Atom(atom))];
                elems.extend(vars.iter().map(|v| CExpr::Var(v.clone())));
                CExpr::Tuple(elems)
            }
        })
    }


    /// Tuple-literal variant of [`Self::lower_ctor_with_k`]: CPS-chain
    /// effectful elements so an aborting handler bypasses the tuple build
    /// and the outer continuation.
    pub(crate) fn lower_tuple_with_k(&mut self, elems: &[Expr], k_var: &str) -> CExpr {
        let slots: Vec<CpsSlot<'_>> = elems
            .iter()
            .map(|e| CpsSlot::Expr {
                expr: e,
                expected: None,
            })
            .collect();
        self.lower_with_cps_slots(slots, k_var, |_, vars| {
            CExpr::Tuple(vars.iter().map(|v| CExpr::Var(v.clone())).collect())
        })
    }


    /// BinOp variant of [`Self::lower_ctor_with_k`]: CPS-chain effectful
    /// operands so an aborting handler bypasses the arithmetic/comparison
    /// call and the outer continuation. Short-circuit `&&` / `||` route
    /// through the case-with-k path via `lower_expr_with_k_inner` instead.
    pub(crate) fn lower_binop_with_k(
        &mut self,
        op: &BinOp,
        left: &Expr,
        right: &Expr,
        span: Option<&crate::token::Span>,
        k_var: &str,
    ) -> CExpr {
        if matches!(op, BinOp::And | BinOp::Or) {
            // Short-circuit semantics: case on left, k threaded into branches.
            return self.lower_short_circuit_with_k(left, right, matches!(op, BinOp::And), k_var);
        }

        let op_owned = op.clone();
        let span_owned: Option<crate::token::Span> = span.cloned();
        self.lower_with_cps_slots(
            vec![
                CpsSlot::Expr {
                    expr: left,
                    expected: None,
                },
                CpsSlot::Expr {
                    expr: right,
                    expected: None,
                },
            ],
            k_var,
            |this, vars| {
                this.annotate(
                    binop_call(&op_owned, &vars[0], &vars[1]),
                    span_owned.as_ref(),
                )
            },
        )
    }


    pub(crate) fn lower_short_circuit_with_k(
        &mut self,
        left: &Expr,
        right: &Expr,
        and: bool,
        k_var: &str,
    ) -> CExpr {
        let left_var = self.fresh();
        let short_val = CExpr::Lit(CLit::Atom(if and { "false" } else { "true" }.to_string()));
        let short_arm = CExpr::Apply(Box::new(CExpr::Var(k_var.to_string())), vec![short_val]);
        let right_arm = self.lower_branch_with_k(right, k_var);
        let (true_arm, false_arm) = if and {
            (right_arm, short_arm)
        } else {
            (short_arm, right_arm)
        };
        let case_expr = CExpr::Case(
            Box::new(CExpr::Var(left_var.clone())),
            vec![
                CArm {
                    pat: CPat::Lit(CLit::Atom("true".to_string())),
                    guard: None,
                    body: true_arm,
                },
                CArm {
                    pat: CPat::Lit(CLit::Atom("false".to_string())),
                    guard: None,
                    body: false_arm,
                },
            ],
        );
        self.lower_bind_expr_with_cps(left, left_var, None, case_expr)
    }


    /// Field-access variant: `(eff_expr).field`. CPS-chains the record
    /// sub-expression so an aborting handler skips the `element/2` call
    /// (which would otherwise crash with `badarg` on the abort tuple).
    pub(crate) fn lower_field_access_with_k(
        &mut self,
        record_expr: &Expr,
        field_idx: i64,
        k_var: &str,
    ) -> CExpr {
        self.lower_with_cps_slots(
            vec![CpsSlot::Expr {
                expr: record_expr,
                expected: None,
            }],
            k_var,
            |_, vars| {
                cerl_call(
                    "erlang",
                    "element",
                    vec![
                        CExpr::Lit(CLit::Int(field_idx)),
                        CExpr::Var(vars[0].clone()),
                    ],
                )
            },
        )
    }


    /// Record-update variant of [`Self::lower_record_create_with_k`]: CPS-chain
    /// effectful field updates (and the base record sub-expression) so an
    /// aborting handler bypasses the rebuilt tuple and the outer continuation.
    pub(crate) fn lower_record_update_with_k(
        &mut self,
        record_expr: &Expr,
        field_order: Vec<String>,
        fields: &[(String, crate::token::Span, Expr)],
        k_var: &str,
    ) -> CExpr {
        use std::collections::HashMap;
        let field_map: HashMap<&str, &Expr> =
            fields.iter().map(|(n, _, e)| (n.as_str(), e)).collect();

        let rec_var = self.fresh();

        // Destructure the base record with a single tuple pattern up front
        // (`case rec_var of <{Tag, F0, F1, ...}> -> ...`) instead of reading
        // each untouched field with `erlang:element/2`. The pattern match
        // proves the record's arity *locally*, so beam_ssa lowers every field
        // read to the fast unguarded `get_tuple_element`. Reading via
        // `element/2` only becomes `get_tuple_element` when beam can prove the
        // arity by whole-module type inference, which an opaque cross-module
        // call in the data-flow path defeats -- leaving the slow guarded BIF.
        let tag_var = self.fresh();
        let mut pat_vars: Vec<Option<String>> = Vec::with_capacity(field_order.len());

        // Slot layout: [tag, field_0, field_1, ...]. Tag and untouched fields
        // are Pure slots reading the variables bound by the destructure.
        // Updated fields are Expr slots that get CPS-chained if effectful.
        let mut slots: Vec<CpsSlot<'_>> = Vec::with_capacity(field_order.len() + 1);
        slots.push(CpsSlot::Pure(CExpr::Var(tag_var.clone())));
        for name in field_order.iter() {
            slots.push(match field_map.get(name.as_str()) {
                Some(new_expr) => {
                    pat_vars.push(None);
                    CpsSlot::Expr {
                        expr: new_expr,
                        expected: None,
                    }
                }
                None => {
                    let fv = self.fresh();
                    pat_vars.push(Some(fv.clone()));
                    CpsSlot::Pure(CExpr::Var(fv))
                }
            });
        }

        let inner = self.lower_with_cps_slots(slots, k_var, |_, vars| {
            CExpr::Tuple(vars.iter().map(|v| CExpr::Var(v.clone())).collect())
        });

        let destructured = Self::record_destructure_case(&rec_var, &tag_var, &pat_vars, inner);
        self.lower_bind_expr_with_cps(record_expr, rec_var, None, destructured)
    }


    /// Build `case rec_var of <{TagVar, ...field pats...}> when 'true' -> body`,
    /// binding the record's tag and its untouched fields so subsequent reads use
    /// `get_tuple_element` (arity proven locally) rather than `erlang:element/2`.
    /// `pat_vars[pos]` is `Some(var)` to bind that field (untouched) or `None`
    /// (a wildcard) when the field is being overwritten and its old value unused.
    pub(crate) fn record_destructure_case(
        rec_var: &str,
        tag_var: &str,
        pat_vars: &[Option<String>],
        body: CExpr,
    ) -> CExpr {
        let mut pats: Vec<CPat> = Vec::with_capacity(pat_vars.len() + 1);
        pats.push(CPat::Var(tag_var.to_string()));
        for pv in pat_vars {
            pats.push(match pv {
                Some(v) => CPat::Var(v.clone()),
                None => CPat::Wildcard,
            });
        }
        CExpr::Case(
            Box::new(CExpr::Var(rec_var.to_string())),
            vec![CArm {
                pat: CPat::Tuple(pats),
                guard: None,
                body,
            }],
        )
    }


    pub(crate) fn lower_value_to_k_with_ce(&mut self, ce: CExpr, k_var: &str) -> CExpr {
        let v = self.fresh();
        CExpr::Let(
            v.clone(),
            Box::new(ce),
            Box::new(CExpr::Apply(
                Box::new(CExpr::Var(k_var.to_string())),
                vec![CExpr::Var(v)],
            )),
        )
    }


    pub(crate) fn lower_binop(
        &mut self,
        op: &BinOp,
        left: &Expr,
        right: &Expr,
        span: Option<&crate::token::Span>,
    ) -> CExpr {
        match op {
            BinOp::And => return self.lower_short_circuit(left, right, true),
            BinOp::Or => return self.lower_short_circuit(left, right, false),
            _ => {}
        }

        let left_var = self.fresh();
        let right_var = self.fresh();
        let left_ce = self.lower_expr_value(left);
        let right_ce = self.lower_expr_value(right);
        let call = self.annotate(binop_call(op, &left_var, &right_var), span);

        CExpr::Let(
            left_var.clone(),
            Box::new(left_ce),
            Box::new(CExpr::Let(
                right_var.clone(),
                Box::new(right_ce),
                Box::new(call),
            )),
        )
    }


    /// `a && b` -> `case a of true -> b; false -> false end`
    /// `a || b` -> `case a of true -> true; false -> b end`
    pub(crate) fn lower_short_circuit(&mut self, left: &Expr, right: &Expr, and: bool) -> CExpr {
        let left_var = self.fresh();
        let left_ce = self.lower_expr_value(left);
        let right_ce = self.lower_expr_value(right);
        let short_val = CExpr::Lit(CLit::Atom(if and { "false" } else { "true" }.to_string()));
        let (true_arm, false_arm) = if and {
            (right_ce, short_val)
        } else {
            (short_val, right_ce)
        };
        CExpr::Let(
            left_var.clone(),
            Box::new(left_ce),
            Box::new(CExpr::Case(
                Box::new(CExpr::Var(left_var)),
                vec![
                    CArm {
                        pat: CPat::Lit(CLit::Atom("true".to_string())),
                        guard: None,
                        body: true_arm,
                    },
                    CArm {
                        pat: CPat::Lit(CLit::Atom("false".to_string())),
                        guard: None,
                        body: false_arm,
                    },
                ],
            )),
        )
    }


    /// Apply an optional return continuation to a final value.
    pub(crate) fn apply_return_k_with(&mut self, return_k: Option<CExpr>, val: CExpr) -> CExpr {
        if let Some(k) = return_k {
            let v = self.fresh();
            CExpr::Let(
                v.clone(),
                Box::new(val),
                Box::new(CExpr::Apply(Box::new(k), vec![CExpr::Var(v)])),
            )
        } else {
            val
        }
    }


    /// Bind a pattern to a single variable name, wrapping the body in a
    /// destructuring `case` if the pattern is non-trivial (tuple, constructor, etc.).
    /// Returns `(var_name, body)` where `var_name` is safe to use in a `Let` or `Fun` param.
    pub(crate) fn destructure_pat(&mut self, pat: &Pat, body: CExpr) -> (String, CExpr) {
        self.destructure_pat_inner(pat, body, false, None)
    }


    pub(crate) fn destructure_pat_assert(&mut self, pat: &Pat, body: CExpr, span: Span) -> (String, CExpr) {
        self.destructure_pat_inner(pat, body, true, Some(span))
    }


    pub(crate) fn destructure_pat_inner(
        &mut self,
        pat: &Pat,
        body: CExpr,
        is_assert: bool,
        span: Option<Span>,
    ) -> (String, CExpr) {
        if !is_assert && let Some(var) = pat_binding_var(pat) {
            return (var, body);
        }
        let tmp = self.fresh();
        let cpat = self.lower_pat(pat, &self.constructor_atoms, self.handler_origin_module());
        let mut arms = vec![CArm {
            pat: cpat,
            guard: None,
            body,
        }];
        if is_assert {
            // Add wildcard arm that panics with structured error info
            let msg = lower_string_to_binary("Assertion failed: pattern did not match");
            arms.push(CArm {
                pat: CPat::Wildcard,
                guard: None,
                body: self.make_error(crate::codegen::lower::errors::ErrorKind::AssertFail, msg, span.as_ref()),
            });
        }
        let wrapped = CExpr::Case(Box::new(CExpr::Var(tmp.clone())), arms);
        (tmp, wrapped)
    }

}
