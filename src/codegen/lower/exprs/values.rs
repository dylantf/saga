use crate::ast::{BinOp, Expr, Pat};
use crate::codegen::cerl::{CArm, CExpr, CLit, CPat};
use crate::codegen::lower::util::*;
use crate::codegen::lower::*;
use crate::token::Span;

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
                && crate::codegen::lower::beam_interop::exit_reason_bare_atom(bare_name)
                    .is_some() =>
            {
                return CExpr::Lit(CLit::Atom(
                    crate::codegen::lower::beam_interop::exit_reason_bare_atom(bare_name)
                        .unwrap()
                        .to_string(),
                ));
            }
            _ => {}
        }
        match bare_name {
            "Cons" if args.len() == 2 => {
                let head_var = self.fresh();
                let tail_var = self.fresh();
                let head_ce = self.lower_operand(args[0], "a constructor");
                let tail_ce = self.lower_operand(args[1], "a constructor");
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
                let mut vars: Vec<String> = Vec::new();
                let mut bindings: Vec<(String, CExpr)> = Vec::new();
                for arg in &args {
                    let var = self.fresh();
                    let val = self.lower_operand(arg, "a constructor");
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

    /// Bind an expression that performs effects to `var_name` for use in
    /// `body`, making `body` its continuation. Unlike
    /// [`Self::lower_bind_expr_with_cps`] the expression may also be a
    /// direct effect operation (`op! x`), and a direct effectful call
    /// receives the continuation as its `_ReturnK` without an intermediate
    /// binding.
    pub(crate) fn lower_bind_effectful_expr(
        &mut self,
        expr: &Expr,
        var_name: String,
        body: CExpr,
    ) -> CExpr {
        let k = CExpr::Fun(vec![var_name], Box::new(body));
        if self.expr_is_effectful_call(expr) {
            return self.lower_expr_with_call_return_k(expr, Some(k));
        }
        let k_var = self.fresh();
        let inner = self.lower_terminal_effectful_expr_to_k(expr, &k_var);
        CExpr::Let(k_var, Box::new(k), Box::new(inner))
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
        let left_ce = self.lower_operand(left, "a binary operator");
        let right_ce = self.lower_operand(right, "a binary operator");
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
        let left_ce = self.lower_operand(left, "`&&`/`||`");
        let right_ce = self.lower_operand(right, "`&&`/`||`");
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

    pub(crate) fn destructure_pat_assert(
        &mut self,
        pat: &Pat,
        body: CExpr,
        span: Span,
    ) -> (String, CExpr) {
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
                body: self.make_error(
                    crate::codegen::lower::errors::ErrorKind::AssertFail,
                    msg,
                    span.as_ref(),
                ),
            });
        }
        let wrapped = CExpr::Case(Box::new(CExpr::Var(tmp.clone())), arms);
        (tmp, wrapped)
    }
}
