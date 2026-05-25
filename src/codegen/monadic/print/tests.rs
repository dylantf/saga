use super::*;
use crate::ast::{Lit, NodeId, Pat};
use crate::token::{Span, StringKind};

    fn sp() -> Span {
        Span { start: 0, end: 0 }
    }

    fn nid(n: u32) -> NodeId {
        NodeId(n)
    }

    fn mv(name: &str) -> MVar {
        MVar {
            name: name.to_string(),
            id: 0,
        }
    }

    fn var(name: &str, id: u32) -> Atom {
        Atom::Var {
            name: mv(name),
            source: nid(id),
        }
    }

    fn int_lit(n: i64, id: u32) -> Atom {
        Atom::Lit {
            value: Lit::Int(n.to_string(), n),
            source: nid(id),
        }
    }

    fn op(effect: &str, op: &str, idx: u32) -> EffectOpRef {
        EffectOpRef {
            effect: effect.to_string(),
            op: op.to_string(),
            op_index: idx,
        }
    }

    #[test]
    fn bind_chain_is_flat_and_deterministic() {
        // fun foo (x) = bind y <- App(plus, [x, 1]); bind z <- App(g, [y]); Pure(z)
        let body = MExpr::Bind {
            var: mv("y"),
            value: Box::new(MExpr::App {
                head: var("plus", 10),
                args: vec![var("x", 11), int_lit(1, 12)],
                source: nid(13),
            }),
            body: Box::new(MExpr::Bind {
                var: mv("z"),
                value: Box::new(MExpr::App {
                    head: var("g", 14),
                    args: vec![var("y", 15)],
                    source: nid(16),
                }),
                body: Box::new(MExpr::Pure(var("z", 17))),
            }),
        };
        let f = MFunBinding {
            id: nid(1),
            name: "foo".to_string(),
            name_span: sp(),
            params: vec![Pat::Var {
                id: nid(2),
                name: "x".to_string(),
                span: sp(),
            }],
            body,
            span: sp(),
        };
        let prog = vec![MDecl::FunBinding(f)];

        let s1 = print_program(&prog);
        let s2 = print_program(&prog);
        assert_eq!(s1, s2, "printer must be deterministic");

        let expected = "\
fun foo (x) [#1] =
  bind y <- App(Var(plus), [Var(x), Lit(1)]) [#13]
  bind z <- App(Var(g), [Var(y)]) [#16]
  Pure(Var(z))";
        assert_eq!(s1, expected);

        // No leading indentation creep: each bind keyword sits at column 2.
        let lines: Vec<&str> = s1.lines().collect();
        assert!(lines[1].starts_with("  bind y"));
        assert!(lines[2].starts_with("  bind z"));
        assert!(lines[3].starts_with("  Pure"));
    }

    #[test]
    fn pure_of_each_atom_variant() {
        let cases: Vec<(Atom, &str)> = vec![
            (var("x", 0), "Pure(Var(x))"),
            (int_lit(42, 0), "Pure(Lit(42))"),
            (
                Atom::Lit {
                    value: Lit::Float("1.5".to_string(), 1.5),
                    source: nid(0),
                },
                "Pure(Lit(1.5))",
            ),
            (
                Atom::Lit {
                    value: Lit::String("hi".to_string(), StringKind::Normal),
                    source: nid(0),
                },
                "Pure(Lit(\"hi\"))",
            ),
            (
                Atom::Lit {
                    value: Lit::Bool(true),
                    source: nid(0),
                },
                "Pure(Lit(true))",
            ),
            (
                Atom::Lit {
                    value: Lit::Unit,
                    source: nid(0),
                },
                "Pure(Lit(()))",
            ),
            (
                Atom::Ctor {
                    name: "Some".to_string(),
                    args: vec![var("x", 0)],
                    source: nid(0),
                },
                "Pure(Ctor(Some, [Var(x)]))",
            ),
            (
                Atom::Ctor {
                    name: "None".to_string(),
                    args: vec![],
                    source: nid(0),
                },
                "Pure(Ctor(None))",
            ),
            (
                Atom::Tuple {
                    elements: vec![var("a", 0), var("b", 0)],
                    source: nid(0),
                },
                "Pure(Tuple([Var(a), Var(b)]))",
            ),
            (
                Atom::AnonRecord {
                    fields: vec![("x".to_string(), var("a", 0))],
                    source: nid(0),
                },
                "Pure(AnonRecord({x: Var(a)}))",
            ),
            (
                Atom::Record {
                    name: "P".to_string(),
                    fields: vec![("x".to_string(), int_lit(1, 0))],
                    source: nid(0),
                },
                "Pure(Record(P, {x: Lit(1)}))",
            ),
            (
                Atom::DictRef {
                    name: "ShowInt".to_string(),
                    source: nid(0),
                },
                "Pure(DictRef(ShowInt))",
            ),
            (
                Atom::QualifiedRef {
                    module: "Std.IO".to_string(),
                    name: "print".to_string(),
                    source: nid(0),
                },
                "Pure(QualifiedRef(Std.IO.print))",
            ),
            (
                Atom::Symbol {
                    symbol: "ok".to_string(),
                    source: nid(0),
                },
                "Pure(Symbol(ok))",
            ),
        ];
        for (atom, expected) in cases {
            let s = print_expr(&MExpr::Pure(atom));
            assert_eq!(s, expected);
        }
    }

    #[test]
    fn pure_of_lambda_atom() {
        let lam = Atom::Lambda {
            params: vec![Pat::Var {
                id: nid(0),
                name: "x".to_string(),
                span: sp(),
            }],
            body: Box::new(MExpr::Pure(var("x", 1))),
            source: nid(2),
        };
        assert_eq!(print_atom(&lam), "Lambda([x], Pure(Var(x)))");
    }

    #[test]
    fn yield_with_resolved_op_ref() {
        let e = MExpr::Yield {
            op: op("Log", "log", 1),
            args: vec![Atom::Lit {
                value: Lit::String("hello".to_string(), StringKind::Normal),
                source: nid(5),
            }],
            source: nid(7),
        };
        assert_eq!(
            print_expr(&e),
            "Yield(Log/log@1, [Lit(\"hello\")]) [#7]"
        );
    }

    #[test]
    fn static_handler_with_arms_and_return() {
        let arm = MHandlerArm {
            id: nid(42),
            op: op("Log", "log", 1),
            params: vec![Pat::Var {
                id: nid(0),
                name: "msg".to_string(),
                span: sp(),
            }],
            body: Box::new(MExpr::Bind {
                var: mv("_"),
                value: Box::new(MExpr::ForeignCall {
                    module: "io".to_string(),
                    func: "format".to_string(),
                    args: vec![
                        Atom::Lit {
                            value: Lit::String("~s~n".to_string(), StringKind::Normal),
                            source: nid(50),
                        },
                        var("msg", 51),
                    ],
                    source: nid(52),
                }),
                body: Box::new(MExpr::Resume {
                    value: Atom::Lit {
                        value: Lit::Unit,
                        source: nid(53),
                    },
                    source: nid(43),
                }),
            }),
            finally_block: None,
            span: sp(),
        };
        let ret = MHandlerArm {
            id: nid(44),
            op: op("", "return", 0),
            params: vec![Pat::Var {
                id: nid(0),
                name: "v".to_string(),
                span: sp(),
            }],
            body: Box::new(MExpr::Pure(var("v", 45))),
            finally_block: None,
            span: sp(),
        };
        let with = MExpr::With {
            handler: MHandler::Static {
                effects: vec!["Log".to_string()],
                arms: vec![arm],
                return_clause: Some(ret),
                source: nid(100),
            },
            body: Box::new(MExpr::Pure(Atom::Lit {
                value: Lit::Unit,
                source: nid(101),
            })),
            source: nid(102),
        };
        let s = print_expr(&with);
        let expected = "\
with handler<Static>(effects=[Log]) [#100] {
  arm Log/log@1(msg) [#42]:
    bind _ <- ForeignCall(io:format, [Lit(\"~s~n\"), Var(msg)]) [#52]
    Resume(Lit(())) [#43]
  return(v) [#44]:
    Pure(Var(v))
} in
Pure(Lit(()))";
        assert_eq!(s, expected);
    }

    #[test]
    fn dynamic_handler_shows_op_tuple() {
        let with = MExpr::With {
            handler: MHandler::Dynamic {
                effects: vec!["State".to_string()],
                op_tuple: var("h", 60),
                return_lambda: None,
                source: nid(61),
            },
            body: Box::new(MExpr::Pure(var("x", 62))),
            source: nid(63),
        };
        let s = print_expr(&with);
        let expected = "\
with handler<Dynamic>(effects=[State], op_tuple=Var(h)) [#61] {
  return = None
} in
Pure(Var(x))";
        assert_eq!(s, expected);
    }

    #[test]
    fn resume_shows_source_node_id() {
        let e = MExpr::Resume {
            value: int_lit(0, 70),
            source: nid(71),
        };
        assert_eq!(print_expr(&e), "Resume(Lit(0)) [#71]");
    }

    #[test]
    fn app_with_many_args_shows_all() {
        let e = MExpr::App {
            head: var("f", 0),
            args: vec![var("a", 0), var("b", 0), var("c", 0), var("d", 0)],
            source: nid(80),
        };
        assert_eq!(
            print_expr(&e),
            "App(Var(f), [Var(a), Var(b), Var(c), Var(d)]) [#80]"
        );
    }
