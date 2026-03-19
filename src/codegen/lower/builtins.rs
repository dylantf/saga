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

    /// Lower String builtins that need Erlang return value transformation.
    /// - String.find/strip_prefix: nomatch -> None, value -> Some value
    /// - String.contains/starts_with/ends_with: nomatch -> false, _ -> true
    /// - String.split: string:split(S, Sep, all) needs a fixed atom arg
    pub(super) fn lower_builtin_string(
        &mut self,
        module: &str,
        func_name: &str,
        args: &[&crate::ast::Expr],
    ) -> Option<CExpr> {
        if module != "String" {
            return None;
        }

        // Helper: case Result of nomatch -> 'undefined' (None); V -> V (Some) end
        let nomatch_to_maybe = |result_var: String, v: String| {
            CExpr::Case(
                Box::new(CExpr::Var(result_var)),
                vec![
                    CArm {
                        pat: CPat::Lit(CLit::Atom("nomatch".to_string())),
                        guard: None,
                        body: CExpr::Lit(CLit::Atom("undefined".to_string())),
                    },
                    CArm {
                        pat: CPat::Var(v.clone()),
                        guard: None,
                        body: CExpr::Var(v),
                    },
                ],
            )
        };

        // Helper: case Result of nomatch -> 'false'; _ -> 'true' end
        let nomatch_to_bool = |result_var: String| {
            CExpr::Case(
                Box::new(CExpr::Var(result_var)),
                vec![
                    CArm {
                        pat: CPat::Lit(CLit::Atom("nomatch".to_string())),
                        guard: None,
                        body: CExpr::Lit(CLit::Atom("false".to_string())),
                    },
                    CArm {
                        pat: CPat::Wildcard,
                        guard: None,
                        body: CExpr::Lit(CLit::Atom("true".to_string())),
                    },
                ],
            )
        };

        match func_name {
            // String.find s sub -> case string:find(S, Sub) of nomatch -> None; V -> Some V end
            "find" => {
                let s = self.lower_expr(args[0]);
                let sub = self.lower_expr(args[1]);
                let sv = self.fresh();
                let subv = self.fresh();
                let result = self.fresh();
                let v = self.fresh();
                let call = cerl_call(
                    "string",
                    "find",
                    vec![CExpr::Var(sv.clone()), CExpr::Var(subv.clone())],
                );
                Some(CExpr::Let(
                    sv,
                    Box::new(s),
                    Box::new(CExpr::Let(
                        subv,
                        Box::new(sub),
                        Box::new(CExpr::Let(
                            result.clone(),
                            Box::new(call),
                            Box::new(nomatch_to_maybe(result, v)),
                        )),
                    )),
                ))
            }

            // String.strip_prefix s prefix -> case string:prefix(S, P) of nomatch -> None; V -> Some V end
            "strip_prefix" => {
                let s = self.lower_expr(args[0]);
                let prefix = self.lower_expr(args[1]);
                let sv = self.fresh();
                let pv = self.fresh();
                let result = self.fresh();
                let v = self.fresh();
                let call = cerl_call(
                    "string",
                    "prefix",
                    vec![CExpr::Var(sv.clone()), CExpr::Var(pv.clone())],
                );
                Some(CExpr::Let(
                    sv,
                    Box::new(s),
                    Box::new(CExpr::Let(
                        pv,
                        Box::new(prefix),
                        Box::new(CExpr::Let(
                            result.clone(),
                            Box::new(call),
                            Box::new(nomatch_to_maybe(result, v)),
                        )),
                    )),
                ))
            }

            // String.contains s sub -> case string:find(S, Sub) of nomatch -> false; _ -> true end
            "contains" => {
                let s = self.lower_expr(args[0]);
                let sub = self.lower_expr(args[1]);
                let sv = self.fresh();
                let subv = self.fresh();
                let result = self.fresh();
                let call = cerl_call(
                    "string",
                    "find",
                    vec![CExpr::Var(sv.clone()), CExpr::Var(subv.clone())],
                );
                Some(CExpr::Let(
                    sv,
                    Box::new(s),
                    Box::new(CExpr::Let(
                        subv,
                        Box::new(sub),
                        Box::new(CExpr::Let(
                            result.clone(),
                            Box::new(call),
                            Box::new(nomatch_to_bool(result)),
                        )),
                    )),
                ))
            }

            // String.starts_with s prefix -> case string:prefix(S, P) of nomatch -> false; _ -> true end
            "starts_with" => {
                let s = self.lower_expr(args[0]);
                let prefix = self.lower_expr(args[1]);
                let sv = self.fresh();
                let pv = self.fresh();
                let result = self.fresh();
                let call = cerl_call(
                    "string",
                    "prefix",
                    vec![CExpr::Var(sv.clone()), CExpr::Var(pv.clone())],
                );
                Some(CExpr::Let(
                    sv,
                    Box::new(s),
                    Box::new(CExpr::Let(
                        pv,
                        Box::new(prefix),
                        Box::new(CExpr::Let(
                            result.clone(),
                            Box::new(call),
                            Box::new(nomatch_to_bool(result)),
                        )),
                    )),
                ))
            }

            // String.ends_with: reverse both, then prefix check
            "ends_with" => {
                let s = self.lower_expr(args[0]);
                let suffix = self.lower_expr(args[1]);
                let sv = self.fresh();
                let sufv = self.fresh();
                let rs = self.fresh();
                let rsuf = self.fresh();
                let result = self.fresh();
                let rev_s = cerl_call("string", "reverse", vec![CExpr::Var(sv.clone())]);
                let rev_suf = cerl_call("string", "reverse", vec![CExpr::Var(sufv.clone())]);
                let call = cerl_call(
                    "string",
                    "prefix",
                    vec![CExpr::Var(rs.clone()), CExpr::Var(rsuf.clone())],
                );
                Some(CExpr::Let(
                    sv,
                    Box::new(s),
                    Box::new(CExpr::Let(
                        sufv,
                        Box::new(suffix),
                        Box::new(CExpr::Let(
                            rs,
                            Box::new(rev_s),
                            Box::new(CExpr::Let(
                                rsuf,
                                Box::new(rev_suf),
                                Box::new(CExpr::Let(
                                    result.clone(),
                                    Box::new(call),
                                    Box::new(nomatch_to_bool(result)),
                                )),
                            )),
                        )),
                    )),
                ))
            }

            // String.split s sep -> string:split(S, Sep, all)
            "split" => {
                let s = self.lower_expr(args[0]);
                let sep = self.lower_expr(args[1]);
                let sv = self.fresh();
                let sepv = self.fresh();
                let call = cerl_call(
                    "string",
                    "split",
                    vec![
                        CExpr::Var(sv.clone()),
                        CExpr::Var(sepv.clone()),
                        CExpr::Lit(CLit::Atom("all".to_string())),
                    ],
                );
                Some(CExpr::Let(
                    sv,
                    Box::new(s),
                    Box::new(CExpr::Let(sepv, Box::new(sep), Box::new(call))),
                ))
            }

            _ => None,
        }
    }

    /// Lower Regex builtins that call re:run/re:replace with fixed option args.
    pub(super) fn lower_builtin_regex(
        &mut self,
        module: &str,
        func_name: &str,
        args: &[&crate::ast::Expr],
    ) -> Option<CExpr> {
        if module != "Regex" {
            return None;
        }

        match func_name {
            // Regex.match pattern s -> case re:run(S, Pat) of {match,_} -> true; nomatch -> false end
            "match" => {
                let pat = self.lower_expr(args[0]);
                let s = self.lower_expr(args[1]);
                let pv = self.fresh();
                let sv = self.fresh();
                let result = self.fresh();
                let call = cerl_call(
                    "re",
                    "run",
                    vec![CExpr::Var(sv.clone()), CExpr::Var(pv.clone())],
                );
                let case = CExpr::Case(
                    Box::new(CExpr::Var(result.clone())),
                    vec![
                        CArm {
                            pat: CPat::Lit(CLit::Atom("nomatch".to_string())),
                            guard: None,
                            body: CExpr::Lit(CLit::Atom("false".to_string())),
                        },
                        CArm {
                            pat: CPat::Wildcard,
                            guard: None,
                            body: CExpr::Lit(CLit::Atom("true".to_string())),
                        },
                    ],
                );
                Some(CExpr::Let(
                    pv,
                    Box::new(pat),
                    Box::new(CExpr::Let(
                        sv,
                        Box::new(s),
                        Box::new(CExpr::Let(result, Box::new(call), Box::new(case))),
                    )),
                ))
            }

            // Regex.find pattern s -> case re:run(S, Pat, [{capture,first,binary}]) of
            //   {match,[V]} -> V; nomatch -> undefined end
            "find" => {
                let pat = self.lower_expr(args[0]);
                let s = self.lower_expr(args[1]);
                let pv = self.fresh();
                let sv = self.fresh();
                let result = self.fresh();
                let v = self.fresh();
                let opts = CExpr::Cons(
                    Box::new(CExpr::Tuple(vec![
                        CExpr::Lit(CLit::Atom("capture".to_string())),
                        CExpr::Lit(CLit::Atom("first".to_string())),
                        CExpr::Lit(CLit::Atom("list".to_string())),
                    ])),
                    Box::new(CExpr::Nil),
                );
                let call = cerl_call(
                    "re",
                    "run",
                    vec![CExpr::Var(sv.clone()), CExpr::Var(pv.clone()), opts],
                );
                let case = CExpr::Case(
                    Box::new(CExpr::Var(result.clone())),
                    vec![
                        CArm {
                            pat: CPat::Tuple(vec![
                                CPat::Lit(CLit::Atom("match".to_string())),
                                CPat::Cons(Box::new(CPat::Var(v.clone())), Box::new(CPat::Nil)),
                            ]),
                            guard: None,
                            body: CExpr::Var(v),
                        },
                        CArm {
                            pat: CPat::Wildcard,
                            guard: None,
                            body: CExpr::Lit(CLit::Atom("undefined".to_string())),
                        },
                    ],
                );
                Some(CExpr::Let(
                    pv,
                    Box::new(pat),
                    Box::new(CExpr::Let(
                        sv,
                        Box::new(s),
                        Box::new(CExpr::Let(result, Box::new(call), Box::new(case))),
                    )),
                ))
            }

            // Regex.find_all pattern s -> case re:run(S, Pat, [global, {capture,first,binary}]) of
            //   {match, Matches} -> lists:map(fun([X]) -> X end, Matches); nomatch -> [] end
            "find_all" => {
                let pat = self.lower_expr(args[0]);
                let s = self.lower_expr(args[1]);
                let pv = self.fresh();
                let sv = self.fresh();
                let result = self.fresh();
                let matches = self.fresh();
                let x = self.fresh();
                let opts = CExpr::Cons(
                    Box::new(CExpr::Lit(CLit::Atom("global".to_string()))),
                    Box::new(CExpr::Cons(
                        Box::new(CExpr::Tuple(vec![
                            CExpr::Lit(CLit::Atom("capture".to_string())),
                            CExpr::Lit(CLit::Atom("first".to_string())),
                            CExpr::Lit(CLit::Atom("list".to_string())),
                        ])),
                        Box::new(CExpr::Nil),
                    )),
                );
                let call = cerl_call(
                    "re",
                    "run",
                    vec![CExpr::Var(sv.clone()), CExpr::Var(pv.clone()), opts],
                );
                // fun([X]) -> X -- unwrap each [Match] to Match
                let unwrap_fn = CExpr::Fun(
                    vec![x.clone()],
                    Box::new(CExpr::Case(
                        Box::new(CExpr::Var(x.clone())),
                        vec![CArm {
                            pat: CPat::Cons(Box::new(CPat::Var(x.clone())), Box::new(CPat::Nil)),
                            guard: None,
                            body: CExpr::Var(x.clone()),
                        }],
                    )),
                );
                let unwrap_var = self.fresh();
                let map_call = cerl_call(
                    "lists",
                    "map",
                    vec![CExpr::Var(unwrap_var.clone()), CExpr::Var(matches.clone())],
                );
                let case = CExpr::Case(
                    Box::new(CExpr::Var(result.clone())),
                    vec![
                        CArm {
                            pat: CPat::Tuple(vec![
                                CPat::Lit(CLit::Atom("match".to_string())),
                                CPat::Var(matches.clone()),
                            ]),
                            guard: None,
                            body: CExpr::Let(
                                unwrap_var,
                                Box::new(unwrap_fn),
                                Box::new(map_call),
                            ),
                        },
                        CArm {
                            pat: CPat::Wildcard,
                            guard: None,
                            body: CExpr::Nil,
                        },
                    ],
                );
                Some(CExpr::Let(
                    pv,
                    Box::new(pat),
                    Box::new(CExpr::Let(
                        sv,
                        Box::new(s),
                        Box::new(CExpr::Let(result, Box::new(call), Box::new(case))),
                    )),
                ))
            }

            // Regex.replace pattern s replacement -> re:replace(S, Pat, Rep, [{return,list}])
            "replace" => {
                let pat = self.lower_expr(args[0]);
                let s = self.lower_expr(args[1]);
                let rep = self.lower_expr(args[2]);
                let pv = self.fresh();
                let sv = self.fresh();
                let rv = self.fresh();
                let opts = CExpr::Cons(
                    Box::new(CExpr::Tuple(vec![
                        CExpr::Lit(CLit::Atom("return".to_string())),
                        CExpr::Lit(CLit::Atom("list".to_string())),
                    ])),
                    Box::new(CExpr::Nil),
                );
                let call = cerl_call(
                    "re",
                    "replace",
                    vec![
                        CExpr::Var(sv.clone()),
                        CExpr::Var(pv.clone()),
                        CExpr::Var(rv.clone()),
                        opts,
                    ],
                );
                Some(CExpr::Let(
                    pv,
                    Box::new(pat),
                    Box::new(CExpr::Let(
                        sv,
                        Box::new(s),
                        Box::new(CExpr::Let(rv, Box::new(rep), Box::new(call))),
                    )),
                ))
            }

            // Regex.replace_all pattern s replacement -> re:replace(S, Pat, Rep, [global, {return,list}])
            "replace_all" => {
                let pat = self.lower_expr(args[0]);
                let s = self.lower_expr(args[1]);
                let rep = self.lower_expr(args[2]);
                let pv = self.fresh();
                let sv = self.fresh();
                let rv = self.fresh();
                let opts = CExpr::Cons(
                    Box::new(CExpr::Lit(CLit::Atom("global".to_string()))),
                    Box::new(CExpr::Cons(
                        Box::new(CExpr::Tuple(vec![
                            CExpr::Lit(CLit::Atom("return".to_string())),
                            CExpr::Lit(CLit::Atom("list".to_string())),
                        ])),
                        Box::new(CExpr::Nil),
                    )),
                );
                let call = cerl_call(
                    "re",
                    "replace",
                    vec![
                        CExpr::Var(sv.clone()),
                        CExpr::Var(pv.clone()),
                        CExpr::Var(rv.clone()),
                        opts,
                    ],
                );
                Some(CExpr::Let(
                    pv,
                    Box::new(pat),
                    Box::new(CExpr::Let(
                        sv,
                        Box::new(s),
                        Box::new(CExpr::Let(rv, Box::new(rep), Box::new(call))),
                    )),
                ))
            }

            _ => None,
        }
    }

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
}
