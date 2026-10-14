//! Codegen builtins that can't be expressed as @external or bridge files.
//!
//! Most stdlib builtins have been migrated to .bridge.erl files.
//! Remaining:
//! - print/println/eprint/eprintln: wired to io:format
//! - dbg: debug dict extraction + stderr printing + value passthrough
//! - catch_panic: Core Erlang try/catch with CPS isolation

use super::Lowerer;
use crate::codegen::cerl::{CArm, CExpr, CLit, CPat};
use crate::codegen::ir::Val;
use crate::intrinsics::IntrinsicId;

use super::util::cerl_call;

impl Lowerer<'_> {
    /// Lower a call of an intrinsic. The builder made it only for a number
    /// of arguments the intrinsic is lowered for.
    pub(super) fn lower_intrinsic(&mut self, intrinsic: IntrinsicId, args: &[Val<'_>]) -> CExpr {
        let args: Vec<CExpr> = match intrinsic {
            IntrinsicId::CatchPanic => return self.lower_catch_panic(&args[0]),
            _ => args.iter().map(|arg| self.lower_val(arg)).collect(),
        };
        let lowered = match intrinsic {
            IntrinsicId::PrintStdout => self.lower_builtin_print_values(args, false, false),
            IntrinsicId::PrintStderr => self.lower_builtin_print_values(args, true, false),
            _ => self.lower_builtin_dbg_values(args),
        };
        lowered.expect("the builder checked the intrinsic's argument count")
    }

    fn lower_builtin_print_values(
        &mut self,
        mut args: Vec<CExpr>,
        stderr: bool,
        newline: bool,
    ) -> Option<CExpr> {
        if args.len() != 1 {
            return None;
        }
        let val = args.remove(0);
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

    /// `dbg(dict, x)`: let s = debug(x) in io:format(stderr, "~ts~n", [s]).
    /// After elaboration, `dbg x` is `dbg(__dict_Debug_a, x)`. With the
    /// dictionary alone (partial application) it is `fun(value) -> ...`.
    fn lower_builtin_dbg_values(&mut self, mut args: Vec<CExpr>) -> Option<CExpr> {
        match args.len() {
            1 => {
                // Partial application: fn2 = dbg -> fn2(dict) = fun(v) -> dbg_inline(dict, v)
                let dict = args.remove(0);
                let d = self.fresh();
                let v_param = self.fresh();
                let body = self.dbg_body(CExpr::Var(d.clone()), CExpr::Var(v_param.clone()));
                let lambda = CExpr::Fun(vec![v_param], Box::new(body));
                Some(CExpr::Let(d, Box::new(dict), Box::new(lambda)))
            }
            2 => {
                let val = args.pop().expect("checked len");
                let dict = args.pop().expect("checked len");
                let d = self.fresh();
                let v = self.fresh();
                let body = self.dbg_body(CExpr::Var(d.clone()), CExpr::Var(v.clone()));
                Some(CExpr::Let(
                    d,
                    Box::new(dict),
                    Box::new(CExpr::Let(v, Box::new(val), Box::new(body))),
                ))
            }
            _ => None,
        }
    }

    /// Shared dbg logic: extract debug fn from dict, apply to value, print to stderr.
    fn dbg_body(&mut self, dict: CExpr, val: CExpr) -> CExpr {
        let debug_fn = self.fresh();
        let s = self.fresh();
        let extract = cerl_call("erlang", "element", vec![CExpr::Lit(CLit::Int(1)), dict]);
        let apply = CExpr::Apply(Box::new(CExpr::Var(debug_fn.clone())), vec![val]);
        let print = cerl_call(
            "io",
            "format",
            vec![
                CExpr::Lit(CLit::Atom("standard_error".into())),
                CExpr::Lit(CLit::Str("~ts~n".into())),
                CExpr::Cons(Box::new(CExpr::Var(s.clone())), Box::new(CExpr::Nil)),
            ],
        );
        CExpr::Let(
            debug_fn,
            Box::new(extract),
            Box::new(CExpr::Let(s, Box::new(apply), Box::new(print))),
        )
    }

    /// Lower `catch_panic thunk` to a Core Erlang try/catch.
    /// Clears the CPS return continuation so the thunk returns its value
    /// normally instead of tail-calling into the caller's continuation.
    pub(super) fn lower_catch_panic(&mut self, thunk: &Val<'_>) -> CExpr {
        let thunk = self.lower_val(thunk);

        // The thunk's type is effectful, so it may be a tagged closure:
        // call it with the current evidence and an identity continuation.
        let (ev_var, ev_ce) = self.current_frame_binding();
        let call = self.tagged_cps_apply_value(
            thunk,
            vec![CExpr::Lit(CLit::Atom("unit".into()))],
            CExpr::Var(ev_var.clone()),
        );
        let applied = CExpr::Let(ev_var, Box::new(ev_ce), Box::new(call));
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
                // The abort of a `with` around the thunk is not a panic: it
                // goes on to that `with`.
                CArm {
                    pat: CPat::Tuple(vec![
                        CPat::Lit(CLit::Atom("$saga_abort".into())),
                        CPat::Wildcard,
                        CPat::Wildcard,
                        CPat::Wildcard,
                    ]),
                    guard: Some(cerl_call(
                        "erlang",
                        "=:=",
                        vec![
                            CExpr::Var(class_var.clone()),
                            CExpr::Lit(CLit::Atom("throw".into())),
                        ],
                    )),
                    body: CExpr::PrimOp(
                        "raw_raise".to_string(),
                        vec![
                            CExpr::Var(class_var.clone()),
                            CExpr::Var(reason_var.clone()),
                            CExpr::Var(trace_var.clone()),
                        ],
                    ),
                },
                // Match {saga_error, _Kind, Msg, _Module, _Fun, _File, _Line}
                CArm {
                    pat: CPat::Tuple(vec![
                        CPat::Lit(CLit::Atom("saga_error".into())),
                        CPat::Wildcard, // kind
                        CPat::Var(msg_var.clone()),
                        CPat::Wildcard, // module
                        CPat::Wildcard, // function
                        CPat::Wildcard, // file
                        CPat::Wildcard, // line
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
                    body: CExpr::Tuple(vec![
                        CExpr::Lit(CLit::Atom("error".into())),
                        cerl_call(
                            "saga_runtime",
                            "format_caught_panic",
                            vec![
                                CExpr::Var(class_var.clone()),
                                CExpr::Var(reason_var.clone()),
                            ],
                        ),
                    ]),
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
