//! Codegen builtins that can't be expressed as @external or bridge files.
//!
//! Most stdlib builtins have been migrated to .bridge.erl files.
//! Remaining:
//! - print/println/eprint/eprintln: wired to io:format
//! - dbg: debug dict extraction + stderr printing + value passthrough
//! - catch_panic: Core Erlang try/catch with CPS isolation

use super::Lowerer;
use crate::codegen::cerl::{CArm, CExpr, CLit, CPat};

use super::util::cerl_call;

impl Lowerer<'_> {
    /// Lower print/println/eprint/eprintln to io:format.
    /// `x` is always a String.
    pub(super) fn lower_builtin_print(
        &mut self,
        args: &[&crate::ast::Expr],
        stderr: bool,
        newline: bool,
    ) -> Option<CExpr> {
        if args.len() != 1 {
            return None;
        }
        let val = self.lower_expr(args[0]);
        let v = self.fresh();
        let fmt = if newline { "~ts~n" } else { "~ts" };
        let mut fmt_args = vec![
            CExpr::Lit(CLit::Str(fmt.into())),
            CExpr::Cons(Box::new(CExpr::Var(v.clone())), Box::new(CExpr::Nil)),
        ];
        if stderr {
            fmt_args.insert(0, CExpr::Lit(CLit::Atom("standard_error".into())));
        }
        let format_call = cerl_call("io", "format", fmt_args);
        Some(CExpr::Let(v, Box::new(val), Box::new(format_call)))
    }

    /// Lower `dbg(dict, x)` to: let s = debug(x) in io:format(stderr, "~ts~n", [s]), x
    /// After elaboration, `dbg x` becomes `dbg(__dict_Debug_a, x)`.
    pub(super) fn lower_builtin_dbg(
        &mut self,
        args: &[&crate::ast::Expr],
    ) -> Option<CExpr> {
        if args.len() != 2 {
            return None;
        }
        let dict = self.lower_expr(args[0]);
        let val = self.lower_expr(args[1]);
        let d = self.fresh();
        let v = self.fresh();
        let debug_fn = self.fresh();
        let s = self.fresh();
        let dummy = self.fresh();

        // Extract debug function from dict: element(1, Dict)
        let extract_debug = cerl_call(
            "erlang",
            "element",
            vec![CExpr::Lit(CLit::Int(1)), CExpr::Var(d.clone())],
        );
        // Apply debug to value
        let apply_debug = CExpr::Apply(
            Box::new(CExpr::Var(debug_fn.clone())),
            vec![CExpr::Var(v.clone())],
        );
        // Print to stderr
        let print_stderr = cerl_call(
            "io",
            "format",
            vec![
                CExpr::Lit(CLit::Atom("standard_error".into())),
                CExpr::Lit(CLit::Str("~ts~n".into())),
                CExpr::Cons(Box::new(CExpr::Var(s.clone())), Box::new(CExpr::Nil)),
            ],
        );

        // let d = dict in let v = val in let debug_fn = element(1, d) in
        // let s = debug_fn(v) in let _ = io:format(stderr, ..., [s]) in v
        Some(CExpr::Let(
            d.clone(),
            Box::new(dict),
            Box::new(CExpr::Let(
                v.clone(),
                Box::new(val),
                Box::new(CExpr::Let(
                    debug_fn,
                    Box::new(extract_debug),
                    Box::new(CExpr::Let(
                        s,
                        Box::new(apply_debug),
                        Box::new(CExpr::Let(
                            dummy,
                            Box::new(print_stderr),
                            Box::new(CExpr::Var(v)),
                        )),
                    )),
                )),
            )),
        ))
    }

    /// Lower `catch_panic thunk` to a Core Erlang try/catch.
    /// Clears the CPS return continuation so the thunk returns its value
    /// normally instead of tail-calling into the caller's continuation.
    pub(super) fn lower_catch_panic(&mut self, thunk_expr: &crate::ast::Expr) -> CExpr {
        let saved_return_k = self.current_return_k.take();
        let saved_pending_k = self.pending_callee_return_k.take();
        let thunk = self.lower_expr(thunk_expr);
        self.current_return_k = saved_return_k;
        self.pending_callee_return_k = saved_pending_k;

        let applied = CExpr::Apply(Box::new(thunk), vec![]);
        let ok_var = self.fresh();
        let class_var = self.fresh();
        let reason_var = self.fresh();
        let trace_var = self.fresh();
        let msg_var = self.fresh();

        let ok_body = CExpr::Tuple(vec![
            CExpr::Lit(CLit::Atom("ok".into())),
            CExpr::Var(ok_var.clone()),
        ]);

        let catch_body = CExpr::Case(
            Box::new(CExpr::Var(reason_var.clone())),
            vec![
                CArm {
                    pat: CPat::Tuple(vec![
                        CPat::Lit(CLit::Atom("dylang_panic".into())),
                        CPat::Var(msg_var.clone()),
                    ]),
                    guard: None,
                    body: CExpr::Tuple(vec![
                        CExpr::Lit(CLit::Atom("error".into())),
                        CExpr::Var(msg_var),
                    ]),
                },
                CArm {
                    pat: CPat::Wildcard,
                    guard: None,
                    body: cerl_call(
                        "erlang",
                        "raise",
                        vec![
                            CExpr::Var(class_var.clone()),
                            CExpr::Var(reason_var.clone()),
                            CExpr::Var(trace_var.clone()),
                        ],
                    ),
                },
            ],
        );

        CExpr::Try {
            expr: Box::new(applied),
            ok_var,
            ok_body: Box::new(ok_body),
            catch_vars: (class_var, reason_var, trace_var),
            catch_body: Box::new(catch_body),
        }
    }
}
