//! Codegen builtins that require Erlang-level pattern matching and can't
//! be expressed as @external declarations in .dy files.
//!
//! - Dict.empty: maps:new() (value, not a function)
//! - Dict.get: maps:find with {ok,V}|error -> Maybe conversion
//! - Int.parse: string:to_integer with {N,[]}|_ -> Maybe conversion
//! - Float.parse: string:to_float with {F,[]}|_ -> Maybe conversion

use super::Lowerer;
use crate::codegen::cerl::{CArm, CExpr, CLit, CPat};

use super::util::cerl_call;

impl Lowerer<'_> {
    /// Lower Int.parse / Float.parse to Erlang calls with Maybe wrapping.
    pub(super) fn lower_builtin_conversion(
        &mut self,
        module: &str,
        func_name: &str,
        args: &[&crate::ast::Expr],
    ) -> Option<CExpr> {
        match (module, func_name) {
            // Int.parse s  ->  case string:to_integer(S) of
            //   {N, []} -> N            (Some = bare value)
            //   _       -> 'undefined'  (None)
            ("Int", "parse") => {
                let arg = self.lower_expr(args[0]);
                let v = self.fresh();
                let n = self.fresh();
                let result = self.fresh();
                let call = cerl_call("string", "to_integer", vec![CExpr::Var(v.clone())]);
                let case = CExpr::Case(
                    Box::new(CExpr::Var(result.clone())),
                    vec![
                        CArm {
                            pat: CPat::Tuple(vec![CPat::Var(n.clone()), CPat::Nil]),
                            guard: None,
                            body: CExpr::Var(n),
                        },
                        CArm {
                            pat: CPat::Wildcard,
                            guard: None,
                            body: CExpr::Lit(CLit::Atom("undefined".to_string())),
                        },
                    ],
                );
                Some(CExpr::Let(
                    v,
                    Box::new(arg),
                    Box::new(CExpr::Let(result, Box::new(call), Box::new(case))),
                ))
            }

            // Float.parse s  ->  case string:to_float(S) of
            //   {F, []} -> F            (Some = bare value)
            //   _       -> 'undefined'  (None)
            ("Float", "parse") => {
                let arg = self.lower_expr(args[0]);
                let v = self.fresh();
                let f = self.fresh();
                let result = self.fresh();
                let call = cerl_call("string", "to_float", vec![CExpr::Var(v.clone())]);
                let case = CExpr::Case(
                    Box::new(CExpr::Var(result.clone())),
                    vec![
                        CArm {
                            pat: CPat::Tuple(vec![CPat::Var(f.clone()), CPat::Nil]),
                            guard: None,
                            body: CExpr::Var(f),
                        },
                        CArm {
                            pat: CPat::Wildcard,
                            guard: None,
                            body: CExpr::Lit(CLit::Atom("undefined".to_string())),
                        },
                    ],
                );
                Some(CExpr::Let(
                    v,
                    Box::new(arg),
                    Box::new(CExpr::Let(result, Box::new(call), Box::new(case))),
                ))
            }

            _ => None,
        }
    }

    /// Lower Dict.get to maps:find with {ok,V}|error -> Maybe conversion.
    pub(super) fn lower_builtin_dict(
        &mut self,
        module: &str,
        func_name: &str,
        args: &[&crate::ast::Expr],
    ) -> Option<CExpr> {
        if module != "Dict" {
            return None;
        }

        match func_name {
            // Dict.get key dict -> case maps:find(Key, Dict) of
            //   {ok, V} -> V            (Some = bare value)
            //   error   -> 'undefined'  (None)
            "get" => {
                let key_expr = self.lower_expr(args[0]);
                let dict_expr = self.lower_expr(args[1]);
                let k = self.fresh();
                let d = self.fresh();
                let result = self.fresh();
                let v = self.fresh();

                let call = cerl_call(
                    "maps",
                    "find",
                    vec![CExpr::Var(k.clone()), CExpr::Var(d.clone())],
                );
                let case = CExpr::Case(
                    Box::new(CExpr::Var(result.clone())),
                    vec![
                        CArm {
                            pat: CPat::Tuple(vec![
                                CPat::Lit(CLit::Atom("ok".to_string())),
                                CPat::Var(v.clone()),
                            ]),
                            guard: None,
                            body: CExpr::Var(v),
                        },
                        CArm {
                            pat: CPat::Lit(CLit::Atom("error".to_string())),
                            guard: None,
                            body: CExpr::Lit(CLit::Atom("undefined".to_string())),
                        },
                    ],
                );

                Some(CExpr::Let(
                    k,
                    Box::new(key_expr),
                    Box::new(CExpr::Let(
                        d,
                        Box::new(dict_expr),
                        Box::new(CExpr::Let(result, Box::new(call), Box::new(case))),
                    )),
                ))
            }

            _ => None,
        }
    }

    /// Lower `print(dict, x)` to `let S = apply show(X) in io:format("~s~n", [S])`.
    /// After elaboration, `print x` becomes `print(__dict_Show_a, x)`.
    pub(super) fn lower_builtin_print(&mut self, args: &[&crate::ast::Expr]) -> Option<CExpr> {
        if args.len() == 1 {
            // Un-elaborated print (e.g. inside handler bodies): print(x) where x is a String
            let val = self.lower_expr(args[0]);
            let v = self.fresh();
            let format_call = cerl_call(
                "io",
                "format",
                vec![
                    CExpr::Lit(CLit::Str("~s~n".into())),
                    CExpr::Cons(Box::new(CExpr::Var(v.clone())), Box::new(CExpr::Nil)),
                ],
            );
            return Some(CExpr::Let(v, Box::new(val), Box::new(format_call)));
        }
        if args.len() != 2 {
            return None;
        }
        let dict = self.lower_expr(args[0]);
        let val = self.lower_expr(args[1]);
        let d = self.fresh();
        let v = self.fresh();
        let show_fn = self.fresh();
        let s = self.fresh();

        // Extract show function from dict: element(1, Dict)
        let extract_show = cerl_call(
            "erlang",
            "element",
            vec![CExpr::Lit(CLit::Int(1)), CExpr::Var(d.clone())],
        );
        // Apply show to value
        let apply_show = CExpr::Apply(
            Box::new(CExpr::Var(show_fn.clone())),
            vec![CExpr::Var(v.clone())],
        );
        // io:format("~s~n", [S])
        let format_call = cerl_call(
            "io",
            "format",
            vec![
                CExpr::Lit(CLit::Str("~s~n".into())),
                CExpr::Cons(Box::new(CExpr::Var(s.clone())), Box::new(CExpr::Nil)),
            ],
        );

        Some(CExpr::Let(
            d.clone(),
            Box::new(dict),
            Box::new(CExpr::Let(
                v,
                Box::new(val),
                Box::new(CExpr::Let(
                    show_fn,
                    Box::new(extract_show),
                    Box::new(CExpr::Let(s, Box::new(apply_show), Box::new(format_call))),
                )),
            )),
        ))
    }
}
