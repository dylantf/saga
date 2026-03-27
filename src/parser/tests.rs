use super::*;
use crate::ast::Handler;
use crate::lexer::Lexer;
use crate::token::Span;
use crate::token::StringKind;

/// Extract effect names from a slice of EffectRef for test assertions
fn effect_names(refs: &[crate::ast::EffectRef]) -> Vec<&str> {
    refs.iter().map(|e| e.name.as_str()).collect()
}

fn parse(source: &str) -> Program {
    let tokens = Lexer::new(source).lex().unwrap();
    Parser::new(tokens).parse_program().unwrap()
}

fn parse_expr(source: &str) -> Expr {
    let tokens = Lexer::new(source).lex().unwrap();
    Parser::new(tokens).parse_expr(0).unwrap()
}

fn parse_pattern(source: &str) -> Pat {
    let tokens = Lexer::new(source).lex().unwrap();
    Parser::new(tokens).parse_pattern().unwrap()
}

// --- Literals ---

#[test]
fn literal_int() {
    let expr = parse_expr("42");
    assert!(matches!(
        expr,
        Expr {
            kind: ExprKind::Lit {
                value: Lit::Int(_, 42),
                ..
            },
            ..
        }
    ));
}

#[test]
fn literal_float() {
    let expr = parse_expr("1.5");
    assert!(
        matches!(expr, Expr { kind: ExprKind::Lit { value: Lit::Float(_, f), .. }, .. } if f == 1.5)
    );
}

#[test]
fn literal_string() {
    let expr = parse_expr("\"hello\"");
    assert!(
        matches!(expr, Expr { kind: ExprKind::Lit { value: Lit::String(s, _), .. }, .. } if s == "hello")
    );
}

#[test]
fn literal_bool() {
    let t = parse_expr("True");
    let f = parse_expr("False");
    assert!(matches!(
        t,
        Expr {
            kind: ExprKind::Lit {
                value: Lit::Bool(true),
                ..
            },
            ..
        }
    ));
    assert!(matches!(
        f,
        Expr {
            kind: ExprKind::Lit {
                value: Lit::Bool(false),
                ..
            },
            ..
        }
    ));
}

// --- Variables and constructors ---

#[test]
fn variable() {
    let expr = parse_expr("foo");
    assert!(matches!(expr, Expr { kind: ExprKind::Var { name, .. }, .. } if name == "foo"));
}

#[test]
fn constructor() {
    let expr = parse_expr("Just");
    assert!(
        matches!(expr, Expr { kind: ExprKind::Constructor { name, .. }, .. } if name == "Just")
    );
}

// --- Binary operators ---

#[test]
fn binary_add() {
    let expr = parse_expr("1 + 2");
    assert!(matches!(
        expr,
        Expr {
            kind: ExprKind::BinOp { op: BinOp::Add, .. },
            ..
        }
    ));
}

#[test]
fn binary_precedence_mul_over_add() {
    // 1 + 2 * 3 should parse as 1 + (2 * 3)
    let expr = parse_expr("1 + 2 * 3");
    match expr {
        Expr {
            kind:
                ExprKind::BinOp {
                    op: BinOp::Add,
                    left,
                    right,
                    ..
                },
            ..
        } => {
            assert!(matches!(
                *left,
                Expr {
                    kind: ExprKind::Lit {
                        value: Lit::Int(_, 1),
                        ..
                    },
                    ..
                }
            ));
            assert!(matches!(
                *right,
                Expr {
                    kind: ExprKind::BinOp { op: BinOp::Mul, .. },
                    ..
                }
            ));
        }
        _ => panic!("expected Add at top level, got {:?}", expr),
    }
}

#[test]
fn binary_precedence_comparison_over_logic() {
    // x == 1 && y == 2 should parse as (x == 1) && (y == 2)
    let expr = parse_expr("x == 1 && y == 2");
    match expr {
        Expr {
            kind:
                ExprKind::BinOp {
                    op: BinOp::And,
                    left,
                    right,
                    ..
                },
            ..
        } => {
            assert!(matches!(
                *left,
                Expr {
                    kind: ExprKind::BinOp { op: BinOp::Eq, .. },
                    ..
                }
            ));
            assert!(matches!(
                *right,
                Expr {
                    kind: ExprKind::BinOp { op: BinOp::Eq, .. },
                    ..
                }
            ));
        }
        _ => panic!("expected And at top level, got {:?}", expr),
    }
}

#[test]
fn binary_left_associative() {
    // 1 - 2 - 3 should parse as (1 - 2) - 3
    let expr = parse_expr("1 - 2 - 3");
    match expr {
        Expr {
            kind:
                ExprKind::BinOp {
                    op: BinOp::Sub,
                    left,
                    right,
                    ..
                },
            ..
        } => {
            assert!(matches!(
                *left,
                Expr {
                    kind: ExprKind::BinOp { op: BinOp::Sub, .. },
                    ..
                }
            ));
            assert!(matches!(
                *right,
                Expr {
                    kind: ExprKind::Lit {
                        value: Lit::Int(_, 3),
                        ..
                    },
                    ..
                }
            ));
        }
        _ => panic!("expected Sub at top level, got {:?}", expr),
    }
}

// --- Parenthesized expressions ---

#[test]
fn parenthesized() {
    // (1 + 2) * 3 should have Mul at top
    let expr = parse_expr("(1 + 2) * 3");
    match expr {
        Expr {
            kind:
                ExprKind::BinOp {
                    op: BinOp::Mul,
                    left,
                    ..
                },
            ..
        } => {
            assert!(matches!(
                *left,
                Expr {
                    kind: ExprKind::BinOp { op: BinOp::Add, .. },
                    ..
                }
            ));
        }
        _ => panic!("expected Mul at top level, got {:?}", expr),
    }
}

// --- Unary minus ---

#[test]
fn unary_minus() {
    let expr = parse_expr("-x");
    assert!(matches!(
        expr,
        Expr {
            kind: ExprKind::UnaryMinus { .. },
            ..
        }
    ));
}

#[test]
fn unary_minus_precedence() {
    // -x + 1 should parse as (-x) + 1
    let expr = parse_expr("-x + 1");
    match expr {
        Expr {
            kind:
                ExprKind::BinOp {
                    op: BinOp::Add,
                    left,
                    ..
                },
            ..
        } => {
            assert!(matches!(
                *left,
                Expr {
                    kind: ExprKind::UnaryMinus { .. },
                    ..
                }
            ));
        }
        _ => panic!("expected Add at top level, got {:?}", expr),
    }
}

// --- Function application ---

#[test]
fn application_single_arg() {
    let expr = parse_expr("f x");
    match expr {
        Expr {
            kind: ExprKind::App { func, arg, .. },
            ..
        } => {
            assert!(matches!(*func, Expr { kind: ExprKind::Var { name, .. }, .. } if name == "f"));
            assert!(matches!(*arg, Expr { kind: ExprKind::Var { name, .. }, .. } if name == "x"));
        }
        _ => panic!("expected App, got {:?}", expr),
    }
}

#[test]
fn application_curried() {
    // f x y should parse as App(App(f, x), y)
    let expr = parse_expr("f x y");
    match expr {
        Expr {
            kind: ExprKind::App { func, arg, .. },
            ..
        } => {
            assert!(matches!(*arg, Expr { kind: ExprKind::Var { name, .. }, .. } if name == "y"));
            assert!(matches!(
                *func,
                Expr {
                    kind: ExprKind::App { .. },
                    ..
                }
            ));
        }
        _ => panic!("expected nested App, got {:?}", expr),
    }
}

#[test]
fn application_binds_tighter_than_binop() {
    // f x + g y should parse as (f x) + (g y)
    let expr = parse_expr("f x + g y");
    match expr {
        Expr {
            kind:
                ExprKind::BinOp {
                    op: BinOp::Add,
                    left,
                    right,
                    ..
                },
            ..
        } => {
            assert!(matches!(
                *left,
                Expr {
                    kind: ExprKind::App { .. },
                    ..
                }
            ));
            assert!(matches!(
                *right,
                Expr {
                    kind: ExprKind::App { .. },
                    ..
                }
            ));
        }
        _ => panic!("expected Add at top level, got {:?}", expr),
    }
}

// --- Pipes ---

#[test]
fn forward_pipe() {
    let expr = parse_expr("x |> f");
    match expr {
        Expr { kind: ExprKind::Pipe { ref segments, .. }, .. } => {
            assert_eq!(segments.len(), 2);
            assert!(matches!(segments[0].node, Expr { kind: ExprKind::Var { ref name, .. }, .. } if name == "x"));
            assert!(matches!(segments[1].node, Expr { kind: ExprKind::Var { ref name, .. }, .. } if name == "f"));
        }
        _ => panic!("expected Pipe, got {:?}", expr),
    }
}

#[test]
fn type_ascription() {
    let expr = parse_expr("(x : Int)");
    match expr {
        Expr {
            kind: ExprKind::Ascription {
                expr, type_expr, ..
            },
            ..
        } => {
            assert!(matches!(*expr, Expr { kind: ExprKind::Var { name, .. }, .. } if name == "x"));
            assert!(matches!(type_expr, TypeExpr::Named { name: n, .. } if n == "Int"));
        }
        _ => panic!("expected Ascription, got {:?}", expr),
    }
}

#[test]
fn type_ascription_lower_than_pipe() {
    // `x |> f : Int` should parse as `(x |> f) : Int`
    let expr = parse_expr("x |> f : Int");
    match expr {
        Expr { kind: ExprKind::Ascription { expr, .. }, .. } => {
            assert!(matches!(*expr, Expr { kind: ExprKind::Pipe { .. }, .. }));
        }
        _ => panic!("expected Ascription wrapping Pipe, got {:?}", expr),
    }
}

#[test]
fn backward_pipe() {
    let expr = parse_expr("f <| x");
    match expr {
        Expr { kind: ExprKind::PipeBack { segments }, .. } => {
            assert_eq!(segments.len(), 2);
            assert!(matches!(&segments[0].node, Expr { kind: ExprKind::Var { name, .. }, .. } if name == "f"));
            assert!(matches!(&segments[1].node, Expr { kind: ExprKind::Var { name, .. }, .. } if name == "x"));
        }
        _ => panic!("expected PipeBack, got {:?}", expr),
    }
}

#[test]
fn cons_operator_expr() {
    let expr = parse_expr("x :: xs");
    match expr {
        Expr { kind: ExprKind::Cons { head, tail }, .. } => {
            assert!(matches!(*head, Expr { kind: ExprKind::Var { name, .. }, .. } if name == "x"));
            assert!(matches!(*tail, Expr { kind: ExprKind::Var { name, .. }, .. } if name == "xs"));
        }
        _ => panic!("expected Cons, got {:?}", expr),
    }
}

#[test]
fn cons_operator_right_associative() {
    // 1 :: 2 :: xs  =>  Cons(1, Cons(2, xs))
    let expr = parse_expr("1 :: 2 :: xs");
    match expr {
        Expr { kind: ExprKind::Cons { head, tail }, .. } => {
            assert!(matches!(*head, Expr { kind: ExprKind::Lit { value: Lit::Int(_, 1), .. }, .. }));
            // tail is Cons(2, xs)
            assert!(matches!(*tail, Expr { kind: ExprKind::Cons { .. }, .. }));
        }
        _ => panic!("expected Cons, got {:?}", expr),
    }
}

// --- If/else ---

#[test]
fn if_else() {
    let expr = parse_expr("if True then 1 else 2");
    match expr {
        Expr {
            kind:
                ExprKind::If {
                    cond,
                    then_branch,
                    else_branch,
                    ..
                },
            ..
        } => {
            assert!(matches!(
                *cond,
                Expr {
                    kind: ExprKind::Lit {
                        value: Lit::Bool(true),
                        ..
                    },
                    ..
                }
            ));
            assert!(matches!(
                *then_branch,
                Expr {
                    kind: ExprKind::Lit {
                        value: Lit::Int(_, 1),
                        ..
                    },
                    ..
                }
            ));
            assert!(matches!(
                *else_branch,
                Expr {
                    kind: ExprKind::Lit {
                        value: Lit::Int(_, 2),
                        ..
                    },
                    ..
                }
            ));
        }
        _ => panic!("expected If, got {:?}", expr),
    }
}

#[test]
fn if_else_if() {
    let expr = parse_expr("if x then 1 else if y then 2 else 3");
    match expr {
        Expr {
            kind: ExprKind::If { else_branch, .. },
            ..
        } => {
            assert!(matches!(
                *else_branch,
                Expr {
                    kind: ExprKind::If { .. },
                    ..
                }
            ));
        }
        _ => panic!("expected If, got {:?}", expr),
    }
}

// --- Blocks ---

#[test]
fn block_single_expr() {
    let expr = parse_expr("{ 42 }");
    match expr {
        Expr {
            kind: ExprKind::Block { stmts, .. },
            ..
        } => {
            assert_eq!(stmts.len(), 1);
            assert!(matches!(
                stmts[0].node,
                Stmt::Expr(Expr {
                    kind: ExprKind::Lit {
                        value: Lit::Int(_, 42),
                        ..
                    },
                    ..
                })
            ));
        }
        _ => panic!("expected Block, got {:?}", expr),
    }
}

#[test]
fn block_with_let() {
    let expr = parse_expr("{\n  let x = 1\n  x + 2\n}");
    match expr {
        Expr {
            kind: ExprKind::Block { stmts, .. },
            ..
        } => {
            assert_eq!(stmts.len(), 2);
            assert!(
                matches!(&stmts[0].node, Stmt::Let { pattern: Pat::Var { name, .. }, .. } if name == "x")
            );
            assert!(matches!(
                &stmts[1].node,
                Stmt::Expr(Expr {
                    kind: ExprKind::BinOp { op: BinOp::Add, .. },
                    ..
                })
            ));
        }
        _ => panic!("expected Block, got {:?}", expr),
    }
}

// --- Patterns ---

#[test]
fn pattern_wildcard() {
    let pat = parse_pattern("_");
    assert!(matches!(pat, Pat::Wildcard { .. }));
}

#[test]
fn pattern_underscore_prefixed_is_var() {
    let pat = parse_pattern("_unused");
    assert!(matches!(pat, Pat::Var { ref name, .. } if name == "_unused"));
}

#[test]
fn pattern_var() {
    let pat = parse_pattern("x");
    assert!(matches!(pat, Pat::Var { name, .. } if name == "x"));
}

#[test]
fn pattern_lit_int() {
    let pat = parse_pattern("42");
    assert!(matches!(
        pat,
        Pat::Lit {
            value: Lit::Int(_, 42),
            ..
        }
    ));
}

#[test]
fn pattern_lit_bool() {
    let pat = parse_pattern("True");
    assert!(matches!(
        pat,
        Pat::Lit {
            value: Lit::Bool(true),
            ..
        }
    ));
}

#[test]
fn pattern_lit_negative_int() {
    let pat = parse_pattern("-1");
    assert!(matches!(
        pat,
        Pat::Lit {
            value: Lit::Int(_, -1),
            ..
        }
    ));
}

#[test]
fn pattern_lit_float() {
    let pat = parse_pattern("1.5");
    assert!(matches!(pat, Pat::Lit { value: Lit::Float(_, f), .. } if f == 1.5));
}

#[test]
fn pattern_lit_negative_float() {
    let pat = parse_pattern("-2.5");
    assert!(matches!(pat, Pat::Lit { value: Lit::Float(_, f), .. } if f == -2.5));
}

#[test]
fn pattern_negative_in_case() {
    let expr = parse_expr("case x { -1 -> \"neg\"; 0 -> \"zero\"; _ -> \"other\" }");
    match expr {
        Expr {
            kind: ExprKind::Case { arms, .. },
            ..
        } => {
            assert_eq!(arms.len(), 3);
            assert!(matches!(
                &arms[0].node.pattern,
                Pat::Lit {
                    value: Lit::Int(_, -1),
                    ..
                }
            ));
        }
        _ => panic!("expected Case"),
    }
}

#[test]
fn pattern_string_literal() {
    let pat = parse_pattern("\"hello\"");
    assert!(matches!(
        pat,
        Pat::Lit {
            value: Lit::String(s, _),
            ..
        } if s == "hello"
    ));
}

#[test]
fn pattern_string_prefix() {
    let pat = parse_pattern("\"hello \" <> rest");
    match pat {
        Pat::StringPrefix { prefix, rest, .. } => {
            assert_eq!(prefix, "hello ");
            assert!(matches!(*rest, Pat::Var { name, .. } if name == "rest"));
        }
        _ => panic!("expected StringPrefix, got {:?}", pat),
    }
}

#[test]
fn pattern_string_prefix_in_case() {
    let expr = parse_expr("case msg { \"[ERROR]: \" <> detail -> detail; _ -> \"unknown\" }");
    match expr {
        Expr {
            kind: ExprKind::Case { arms, .. },
            ..
        } => {
            assert_eq!(arms.len(), 2);
            assert!(
                matches!(&arms[0].node.pattern, Pat::StringPrefix { prefix, .. } if prefix == "[ERROR]: ")
            );
        }
        _ => panic!("expected Case"),
    }
}

#[test]
fn pattern_string_concat_requires_literal_on_left() {
    let tokens = Lexer::new("x <> \"suffix\"").lex().unwrap();
    let result = Parser::new(tokens).parse_pattern();
    assert!(result.is_err());
}

#[test]
fn pattern_bare_constructor() {
    let pat = parse_pattern("Nothing");
    match pat {
        Pat::Constructor { name, args, .. } => {
            assert_eq!(name, "Nothing");
            assert!(args.is_empty());
        }
        _ => panic!("expected Constructor, got {:?}", pat),
    }
}

#[test]
fn pattern_constructor_with_args() {
    let pat = parse_pattern("Just(x)");
    match pat {
        Pat::Constructor { name, args, .. } => {
            assert_eq!(name, "Just");
            assert_eq!(args.len(), 1);
            assert!(matches!(&args[0], Pat::Var { name, .. } if name == "x"));
        }
        _ => panic!("expected Constructor, got {:?}", pat),
    }
}

#[test]
fn pattern_constructor_multiple_args() {
    let pat = parse_pattern("Cons(a, b)");
    match pat {
        Pat::Constructor { name, args, .. } => {
            assert_eq!(name, "Cons");
            assert_eq!(args.len(), 2);
        }
        _ => panic!("expected Constructor, got {:?}", pat),
    }
}

#[test]
fn pattern_nested_constructor() {
    let pat = parse_pattern("Just(Cons(a, b))");
    match pat {
        Pat::Constructor { name, args, .. } => {
            assert_eq!(name, "Just");
            assert_eq!(args.len(), 1);
            assert!(matches!(&args[0], Pat::Constructor { name, .. } if name == "Cons"));
        }
        _ => panic!("expected Constructor, got {:?}", pat),
    }
}

#[test]
fn pattern_constructor_space_separated() {
    let pat = parse_pattern("Just x");
    match pat {
        Pat::Constructor { name, args, .. } => {
            assert_eq!(name, "Just");
            assert_eq!(args.len(), 1);
            assert!(matches!(&args[0], Pat::Var { name, .. } if name == "x"));
        }
        _ => panic!("expected Constructor, got {:?}", pat),
    }
}

#[test]
fn pattern_constructor_space_separated_multi_arg() {
    let pat = parse_pattern("Pair a b");
    match pat {
        Pat::Constructor { name, args, .. } => {
            assert_eq!(name, "Pair");
            assert_eq!(args.len(), 2);
            assert!(matches!(&args[0], Pat::Var { name, .. } if name == "a"));
            assert!(matches!(&args[1], Pat::Var { name, .. } if name == "b"));
        }
        _ => panic!("expected Constructor, got {:?}", pat),
    }
}

#[test]
fn pattern_constructor_space_separated_nested() {
    let pat = parse_pattern("Foo Bar");
    match pat {
        Pat::Constructor { name, args, .. } => {
            assert_eq!(name, "Foo");
            assert_eq!(args.len(), 1);
            assert!(
                matches!(&args[0], Pat::Constructor { name, args, .. } if name == "Bar" && args.is_empty())
            );
        }
        _ => panic!("expected Constructor, got {:?}", pat),
    }
}

#[test]
fn pattern_constructor_with_paren_args() {
    // Foo(1, 2) and Foo (1, 2) both parse as Foo with two args (paren syntax)
    let pat = parse_pattern("Foo (1, 2)");
    match pat {
        Pat::Constructor { name, args, .. } => {
            assert_eq!(name, "Foo");
            assert_eq!(args.len(), 2);
        }
        _ => panic!("expected Constructor, got {:?}", pat),
    }
}

#[test]
fn pattern_constructor_space_separated_with_grouped_tuple() {
    // To pass a tuple as a single arg, use nested parens or a binding
    let pat = parse_pattern("Foo ((1, 2))");
    match pat {
        Pat::Constructor { name, args, .. } => {
            assert_eq!(name, "Foo");
            assert_eq!(args.len(), 1);
            assert!(matches!(&args[0], Pat::Tuple { elements, .. } if elements.len() == 2));
        }
        _ => panic!("expected Constructor, got {:?}", pat),
    }
}

#[test]
fn pattern_constructor_space_separated_with_literal() {
    let pat = parse_pattern("Just 42");
    match pat {
        Pat::Constructor { name, args, .. } => {
            assert_eq!(name, "Just");
            assert_eq!(args.len(), 1);
            assert!(matches!(
                &args[0],
                Pat::Lit {
                    value: Lit::Int(_, 42),
                    ..
                }
            ));
        }
        _ => panic!("expected Constructor, got {:?}", pat),
    }
}

#[test]
fn pattern_bare_constructor_still_works() {
    let pat = parse_pattern("Nothing");
    match pat {
        Pat::Constructor { name, args, .. } => {
            assert_eq!(name, "Nothing");
            assert!(args.is_empty());
        }
        _ => panic!("expected Constructor, got {:?}", pat),
    }
}

#[test]
fn pattern_record() {
    let pat = parse_pattern("User { name, age }");
    match pat {
        Pat::Record { name, fields, .. } => {
            assert_eq!(name, "User");
            assert_eq!(fields.len(), 2);
            assert_eq!(fields[0], ("name".to_string(), None));
            assert_eq!(fields[1], ("age".to_string(), None));
        }
        _ => panic!("expected Record pattern, got {:?}", pat),
    }
}

#[test]
fn pattern_record_with_alias() {
    let pat = parse_pattern("Error { code: c }");
    match pat {
        Pat::Record { name, fields, .. } => {
            assert_eq!(name, "Error");
            assert_eq!(fields.len(), 1);
            assert_eq!(fields[0].0, "code");
            assert!(matches!(&fields[0].1, Some(Pat::Var { name, .. }) if name == "c"));
        }
        _ => panic!("expected Record pattern, got {:?}", pat),
    }
}

#[test]
fn pattern_cons_operator() {
    let pat = parse_pattern("x :: xs");
    match pat {
        Pat::Constructor { name, args, .. } => {
            assert_eq!(name, "Cons");
            assert_eq!(args.len(), 2);
            assert!(matches!(&args[0], Pat::Var { name, .. } if name == "x"));
            assert!(matches!(&args[1], Pat::Var { name, .. } if name == "xs"));
        }
        _ => panic!("expected Constructor, got {:?}", pat),
    }
}

#[test]
fn pattern_cons_right_associative() {
    // x :: y :: zs  =>  Cons(x, Cons(y, zs))
    let pat = parse_pattern("x :: y :: zs");
    match pat {
        Pat::Constructor { name, args, .. } => {
            assert_eq!(name, "Cons");
            assert!(matches!(&args[0], Pat::Var { name, .. } if name == "x"));
            assert!(matches!(&args[1], Pat::Constructor { name, .. } if name == "Cons"));
        }
        _ => panic!("expected Constructor, got {:?}", pat),
    }
}

#[test]
fn pattern_list_empty() {
    let pat = parse_pattern("[]");
    match pat {
        Pat::Constructor { name, args, .. } => {
            assert_eq!(name, "Nil");
            assert!(args.is_empty());
        }
        _ => panic!("expected Constructor, got {:?}", pat),
    }
}

#[test]
fn pattern_list_single() {
    let pat = parse_pattern("[x]");
    match pat {
        Pat::Constructor { name, args, .. } => {
            assert_eq!(name, "Cons");
            assert_eq!(args.len(), 2);
            assert!(matches!(&args[0], Pat::Var { name, .. } if name == "x"));
            assert!(matches!(&args[1], Pat::Constructor { name, .. } if name == "Nil"));
        }
        _ => panic!("expected Constructor, got {:?}", pat),
    }
}

#[test]
fn pattern_list_two_elements() {
    let pat = parse_pattern("[x, y]");
    match pat {
        Pat::Constructor { name, args, .. } => {
            assert_eq!(name, "Cons");
            assert_eq!(args.len(), 2);
            assert!(matches!(&args[0], Pat::Var { name, .. } if name == "x"));
            match &args[1] {
                Pat::Constructor { name, args, .. } => {
                    assert_eq!(name, "Cons");
                    assert_eq!(args.len(), 2);
                    assert!(matches!(&args[0], Pat::Var { name, .. } if name == "y"));
                    assert!(matches!(&args[1], Pat::Constructor { name, .. } if name == "Nil"));
                }
                _ => panic!("expected inner Cons, got {:?}", args[1]),
            }
        }
        _ => panic!("expected Constructor, got {:?}", pat),
    }
}

// --- Declarations ---

#[test]
fn fun_annotation_simple() {
    let decls = parse("fun add : (a: Int) -> (b: Int) -> Int");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::FunSignature {
            name,
            params,
            return_type,
            public,
            effects,
            ..
        } => {
            assert_eq!(name, "add");
            assert!(!public);
            assert_eq!(params.len(), 2);
            assert_eq!(params[0].0, "a");
            assert!(matches!(&params[0].1, TypeExpr::Named { name: n, .. } if n == "Int"));
            assert!(matches!(return_type, TypeExpr::Named { name: n, .. } if n == "Int"));
            assert!(effects.is_empty());
        }
        _ => panic!("expected FunAnnotation, got {:?}", decls[0]),
    }
}

#[test]
fn fun_annotation_public_with_effects() {
    let decls = parse("pub fun print : (msg: String) -> Unit needs { Console }");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::FunSignature {
            public, effects, ..
        } => {
            assert!(public);
            assert_eq!(effect_names(effects), vec!["Console"]);
        }
        _ => panic!("expected FunAnnotation, got {:?}", decls[0]),
    }
}

#[test]
fn fun_annotation_unit_param() {
    let decls = parse("fun do_work : Unit -> Int needs { Log }");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::FunSignature {
            name,
            params,
            effects,
            ..
        } => {
            assert_eq!(name, "do_work");
            assert_eq!(params.len(), 1);
            assert_eq!(params[0].0, "_0");
            assert_eq!(params[0].1, TypeExpr::Named { name: "Unit".into(), span: Span { start: 0, end: 0 } });
            assert_eq!(effect_names(effects), vec!["Log"]);
        }
        _ => panic!("expected FunAnnotation, got {:?}", decls[0]),
    }
}

#[test]
fn fun_binding_simple() {
    let decls = parse("add x y = x + y");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::FunBinding {
            name,
            params,
            guard,
            body,
            ..
        } => {
            assert_eq!(name, "add");
            assert_eq!(params.len(), 2);
            assert!(guard.is_none());
            assert!(matches!(
                body,
                Expr {
                    kind: ExprKind::BinOp { op: BinOp::Add, .. },
                    ..
                }
            ));
        }
        _ => panic!("expected FunBinding, got {:?}", decls[0]),
    }
}

#[test]
fn fun_binding_with_guard() {
    let decls = parse("abs n | n < 0 = -n");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::FunBinding { name, guard, .. } => {
            assert_eq!(name, "abs");
            assert!(guard.is_some());
        }
        _ => panic!("expected FunBinding, got {:?}", decls[0]),
    }
}

// --- Type definitions ---

#[test]
fn type_def_simple() {
    let decls = parse("type Option a\n  = Just(a)\n  | Nothing");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::TypeDef {
            name,
            type_params,
            variants,
            ..
        } => {
            assert_eq!(name, "Option");
            assert_eq!(type_params, &vec!["a".to_string()]);
            assert_eq!(variants.len(), 2);
            assert_eq!(variants[0].node.name, "Just");
            assert_eq!(variants[0].node.fields.len(), 1);
            assert_eq!(variants[1].node.name, "Nothing");
            assert!(variants[1].node.fields.is_empty());
        }
        _ => panic!("expected TypeDef, got {:?}", decls[0]),
    }
}

// --- Case expressions ---

#[test]
fn case_simple() {
    let expr = parse_expr("case x {\n  Just(v) -> v\n  Nothing -> 0\n}");
    match expr {
        Expr {
            kind: ExprKind::Case { arms, .. },
            ..
        } => {
            assert_eq!(arms.len(), 2);
            assert!(arms[0].node.guard.is_none());
            assert!(matches!(&arms[0].node.pattern, Pat::Constructor { name, .. } if name == "Just"));
            assert!(matches!(&arms[1].node.pattern, Pat::Constructor { name, .. } if name == "Nothing"));
        }
        _ => panic!("expected Case, got {:?}", expr),
    }
}

#[test]
fn case_with_guard() {
    let expr = parse_expr("case x {\n  n | n > 0 -> n\n  _ -> 0\n}");
    match expr {
        Expr {
            kind: ExprKind::Case { arms, .. },
            ..
        } => {
            assert_eq!(arms.len(), 2);
            assert!(arms[0].node.guard.is_some());
            assert!(arms[1].node.guard.is_none());
            assert!(matches!(&arms[1].node.pattern, Pat::Wildcard { .. }));
        }
        _ => panic!("expected Case, got {:?}", expr),
    }
}

// --- Type expressions ---

#[test]
fn type_expr_named() {
    let decls = parse("fun id : (x: Int) -> Int");
    match &decls[0] {
        Decl::FunSignature {
            params,
            return_type,
            ..
        } => {
            assert!(matches!(&params[0].1, TypeExpr::Named { name: n, .. } if n == "Int"));
            assert!(matches!(return_type, TypeExpr::Named { name: n, .. } if n == "Int"));
        }
        _ => panic!("expected FunAnnotation"),
    }
}

#[test]
fn type_expr_application() {
    let decls = parse("fun unwrap : (x: Option a) -> a");
    match &decls[0] {
        Decl::FunSignature {
            params,
            return_type,
            ..
        } => {
            assert!(matches!(&params[0].1, TypeExpr::App { .. }));
            assert!(matches!(return_type, TypeExpr::Var { name: v, .. } if v == "a"));
        }
        _ => panic!("expected FunAnnotation"),
    }
}

#[test]
fn type_expr_arrow() {
    let decls = parse("fun apply : (f: a -> b) -> (x: a) -> b");
    match &decls[0] {
        Decl::FunSignature { params, .. } => {
            assert!(matches!(&params[0].1, TypeExpr::Arrow { .. }));
        }
        _ => panic!("expected FunAnnotation"),
    }
}

// --- Combined programs ---

#[test]
fn annotation_and_binding() {
    let decls = parse("fun add : (a: Int) -> (b: Int) -> Int\nadd x y = x + y");
    assert_eq!(decls.len(), 2);
    assert!(matches!(&decls[0], Decl::FunSignature { .. }));
    assert!(matches!(&decls[1], Decl::FunBinding { .. }));
}

#[test]
fn multiple_bindings_pattern_match() {
    let decls = parse("abs n | n < 0 = -n\nabs n = n");
    assert_eq!(decls.len(), 2);
    match &decls[0] {
        Decl::FunBinding { guard, .. } => assert!(guard.is_some()),
        _ => panic!("expected FunBinding"),
    }
    match &decls[1] {
        Decl::FunBinding { guard, .. } => assert!(guard.is_none()),
        _ => panic!("expected FunBinding"),
    }
}

// --- Record create ---

#[test]
fn record_create_simple() {
    let expr = parse_expr("User { name: \"Dylan\", age: 30 }");
    match expr {
        Expr {
            kind: ExprKind::RecordCreate { name, fields, .. },
            ..
        } => {
            assert_eq!(name, "User");
            assert_eq!(fields.len(), 2);
            assert_eq!(fields[0].0, "name");
            assert!(
                matches!(&fields[0].2, Expr { kind: ExprKind::Lit { value: Lit::String(s, _), .. }, .. } if s == "Dylan")
            );
            assert_eq!(fields[1].0, "age");
            assert!(matches!(
                &fields[1].2,
                Expr {
                    kind: ExprKind::Lit {
                        value: Lit::Int(_, 30),
                        ..
                    },
                    ..
                }
            ));
        }
        _ => panic!("expected RecordCreate, got {:?}", expr),
    }
}

#[test]
fn record_create_single_field() {
    let expr = parse_expr("Point { x: 1 }");
    match expr {
        Expr {
            kind: ExprKind::RecordCreate { name, fields, .. },
            ..
        } => {
            assert_eq!(name, "Point");
            assert_eq!(fields.len(), 1);
        }
        _ => panic!("expected RecordCreate, got {:?}", expr),
    }
}

#[test]
fn record_create_with_expr_values() {
    let expr = parse_expr("Point { x: 1 + 2, y: 3 * 4 }");
    match expr {
        Expr {
            kind: ExprKind::RecordCreate { fields, .. },
            ..
        } => {
            assert_eq!(fields.len(), 2);
            assert!(matches!(
                &fields[0].2,
                Expr {
                    kind: ExprKind::BinOp { op: BinOp::Add, .. },
                    ..
                }
            ));
            assert!(matches!(
                &fields[1].2,
                Expr {
                    kind: ExprKind::BinOp { op: BinOp::Mul, .. },
                    ..
                }
            ));
        }
        _ => panic!("expected RecordCreate, got {:?}", expr),
    }
}

#[test]
fn record_create_multiline() {
    let expr = parse_expr("User {\n  name: \"Dylan\"\n  age: 30\n}");
    match expr {
        Expr {
            kind: ExprKind::RecordCreate { name, fields, .. },
            ..
        } => {
            assert_eq!(name, "User");
            assert_eq!(fields.len(), 2);
        }
        _ => panic!("expected RecordCreate, got {:?}", expr),
    }
}

#[test]
fn bare_constructor_without_braces() {
    let expr = parse_expr("Nothing");
    assert!(
        matches!(expr, Expr { kind: ExprKind::Constructor { name, .. }, .. } if name == "Nothing")
    );
}

// --- Record update ---

#[test]
fn record_update_simple() {
    let expr = parse_expr("{ user | age: 31 }");
    match expr {
        Expr {
            kind: ExprKind::RecordUpdate { record, fields, .. },
            ..
        } => {
            assert!(
                matches!(*record, Expr { kind: ExprKind::Var { name, .. }, .. } if name == "user")
            );
            assert_eq!(fields.len(), 1);
            assert_eq!(fields[0].0, "age");
            assert!(matches!(
                &fields[0].2,
                Expr {
                    kind: ExprKind::Lit {
                        value: Lit::Int(_, 31),
                        ..
                    },
                    ..
                }
            ));
        }
        _ => panic!("expected RecordUpdate, got {:?}", expr),
    }
}

#[test]
fn record_update_multiple_fields() {
    let expr = parse_expr("{ user | name: \"New\", age: 31 }");
    match expr {
        Expr {
            kind: ExprKind::RecordUpdate { fields, .. },
            ..
        } => {
            assert_eq!(fields.len(), 2);
            assert_eq!(fields[0].0, "name");
            assert_eq!(fields[1].0, "age");
        }
        _ => panic!("expected RecordUpdate, got {:?}", expr),
    }
}

#[test]
fn record_update_with_expr_value() {
    let expr = parse_expr("{ user | age: user.age + 1 }");
    match expr {
        Expr {
            kind: ExprKind::RecordUpdate { fields, .. },
            ..
        } => {
            assert_eq!(fields.len(), 1);
            assert!(matches!(
                &fields[0].2,
                Expr {
                    kind: ExprKind::BinOp { op: BinOp::Add, .. },
                    ..
                }
            ));
        }
        _ => panic!("expected RecordUpdate, got {:?}", expr),
    }
}

#[test]
fn block_still_works() {
    // Make sure blocks didn't break with record update disambiguation
    let expr = parse_expr("{\n  let x = 1\n  x\n}");
    assert!(matches!(
        expr,
        Expr {
            kind: ExprKind::Block { .. },
            ..
        }
    ));
}

#[test]
fn block_single_expr_still_works() {
    let expr = parse_expr("{ 42 }");
    match expr {
        Expr {
            kind: ExprKind::Block { stmts, .. },
            ..
        } => {
            assert_eq!(stmts.len(), 1);
            assert!(matches!(
                &stmts[0].node,
                Stmt::Expr(Expr {
                    kind: ExprKind::Lit {
                        value: Lit::Int(_, 42),
                        ..
                    },
                    ..
                })
            ));
        }
        _ => panic!("expected Block, got {:?}", expr),
    }
}

// --- Field access ---

#[test]
fn field_access_simple() {
    let expr = parse_expr("user.name");
    match expr {
        Expr {
            kind: ExprKind::FieldAccess { expr, field, .. },
            ..
        } => {
            assert!(
                matches!(*expr, Expr { kind: ExprKind::Var { name, .. }, .. } if name == "user")
            );
            assert_eq!(field, "name");
        }
        _ => panic!("expected FieldAccess, got {:?}", expr),
    }
}

#[test]
fn field_access_chained() {
    let expr = parse_expr("user.profile.name");
    match expr {
        Expr {
            kind: ExprKind::FieldAccess {
                expr: inner, field, ..
            },
            ..
        } => {
            assert_eq!(field, "name");
            match *inner {
                Expr {
                    kind:
                        ExprKind::FieldAccess {
                            expr: innermost,
                            field: mid_field,
                            ..
                        },
                    ..
                } => {
                    assert!(
                        matches!(*innermost, Expr { kind: ExprKind::Var { name, .. }, .. } if name == "user")
                    );
                    assert_eq!(mid_field, "profile");
                }
                _ => panic!("expected nested FieldAccess"),
            }
        }
        _ => panic!("expected FieldAccess, got {:?}", expr),
    }
}

#[test]
fn field_access_in_application() {
    // `f user.name` should be App(f, FieldAccess(user, name))
    let expr = parse_expr("f user.name");
    match expr {
        Expr {
            kind: ExprKind::App { func, arg, .. },
            ..
        } => {
            assert!(matches!(*func, Expr { kind: ExprKind::Var { name, .. }, .. } if name == "f"));
            assert!(
                matches!(*arg, Expr { kind: ExprKind::FieldAccess { field, .. }, .. } if field == "name")
            );
        }
        _ => panic!("expected App, got {:?}", expr),
    }
}

#[test]
fn field_access_in_binop() {
    let expr = parse_expr("user.age + 1");
    match expr {
        Expr {
            kind:
                ExprKind::BinOp {
                    left,
                    op: BinOp::Add,
                    ..
                },
            ..
        } => {
            assert!(
                matches!(*left, Expr { kind: ExprKind::FieldAccess { field, .. }, .. } if field == "age")
            );
        }
        _ => panic!("expected BinOp, got {:?}", expr),
    }
}

// --- Record definitions ---

#[test]
fn record_def_simple() {
    let decls = parse("record User {\n  name: String,\n  age: Int,\n}");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::RecordDef { name, fields, .. } => {
            assert_eq!(name, "User");
            assert_eq!(fields.len(), 2);
            assert_eq!(fields[0].node.0, "name");
            assert!(matches!(&fields[0].node.1, TypeExpr::Named { name: n, .. } if n == "String"));
            assert_eq!(fields[1].node.0, "age");
            assert!(matches!(&fields[1].node.1, TypeExpr::Named { name: n, .. } if n == "Int"));
        }
        _ => panic!("expected RecordDef, got {:?}", decls[0]),
    }
}

#[test]
fn record_def_no_trailing_comma() {
    let decls = parse("record Point { x: Int, y: Int }");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::RecordDef { name, fields, .. } => {
            assert_eq!(name, "Point");
            assert_eq!(fields.len(), 2);
        }
        _ => panic!("expected RecordDef, got {:?}", decls[0]),
    }
}

#[test]
fn record_def_with_type_app() {
    let decls = parse("record Container {\n  value: Option Int,\n}");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::RecordDef { fields, .. } => {
            assert_eq!(fields.len(), 1);
            assert!(matches!(&fields[0].node.1, TypeExpr::App { .. }));
        }
        _ => panic!("expected RecordDef, got {:?}", decls[0]),
    }
}

#[test]
fn record_def_with_type_params() {
    let decls = parse("record Box a { value: a }");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::RecordDef {
            name,
            type_params,
            fields,
            ..
        } => {
            assert_eq!(name, "Box");
            assert_eq!(type_params, &["a"]);
            assert_eq!(fields.len(), 1);
            assert_eq!(fields[0].node.0, "value");
            assert!(matches!(&fields[0].node.1, TypeExpr::Var { name: v, .. } if v == "a"));
        }
        _ => panic!("expected RecordDef, got {:?}", decls[0]),
    }
}

#[test]
fn record_def_with_multiple_type_params() {
    let decls = parse("record Pair a b {\n  fst: a,\n  snd: b,\n}");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::RecordDef {
            name,
            type_params,
            fields,
            ..
        } => {
            assert_eq!(name, "Pair");
            assert_eq!(type_params, &["a", "b"]);
            assert_eq!(fields.len(), 2);
        }
        _ => panic!("expected RecordDef, got {:?}", decls[0]),
    }
}

// --- Effect definitions ---

#[test]
fn effect_def_single_op() {
    let decls = parse("effect Log {\n  fun log : (level: String) -> (msg: String) -> Unit\n}");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::EffectDef {
            name, operations, ..
        } => {
            assert_eq!(name, "Log");
            assert_eq!(operations.len(), 1);
            assert_eq!(operations[0].node.name, "log");
            assert_eq!(operations[0].node.params.len(), 2);
            assert_eq!(operations[0].node.params[0].0, "level");
            assert_eq!(operations[0].node.params[1].0, "msg");
        }
        _ => panic!("expected EffectDef, got {:?}", decls[0]),
    }
}

#[test]
fn effect_def_multiple_ops() {
    let decls = parse(
        "effect Http {\n  fun get : (url: String) -> String\n  fun post : (url: String) -> (body: String) -> String\n}",
    );
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::EffectDef {
            name, operations, ..
        } => {
            assert_eq!(name, "Http");
            assert_eq!(operations.len(), 2);
            assert_eq!(operations[0].node.name, "get");
            assert_eq!(operations[1].node.name, "post");
            assert_eq!(operations[1].node.params.len(), 2);
        }
        _ => panic!("expected EffectDef, got {:?}", decls[0]),
    }
}

// --- Handler definitions ---

#[test]
fn handler_def_simple() {
    let decls = parse("handler console_log for Log {\n  log level msg = print! (level <> msg)\n}");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::HandlerDef {
            name,
            effects,
            arms,
            return_clause,
            ..
        } => {
            assert_eq!(name, "console_log");
            assert_eq!(effect_names(effects), vec!["Log"]);
            assert_eq!(arms.len(), 1);
            assert_eq!(arms[0].node.op_name, "log");
            let param_names: Vec<&str> = arms[0].node.params.iter().map(|(n, _)| n.as_str()).collect();
            assert_eq!(param_names, vec!["level", "msg"]);
            assert!(return_clause.is_none());
        }
        _ => panic!("expected HandlerDef, got {:?}", decls[0]),
    }
}

#[test]
fn handler_def_with_return_clause() {
    let decls = parse(
        "handler to_result for Fail {\n  fail reason = Err(reason)\n  return value = Ok(value)\n}",
    );
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::HandlerDef {
            name,
            arms,
            return_clause,
            ..
        } => {
            assert_eq!(name, "to_result");
            assert_eq!(arms.len(), 1);
            assert_eq!(arms[0].node.op_name, "fail");
            assert!(return_clause.is_some());
            let rc = return_clause.as_ref().unwrap();
            let rc_names: Vec<&str> = rc.params.iter().map(|(n, _)| n.as_str()).collect();
            assert_eq!(rc_names, vec!["value"]);
        }
        _ => panic!("expected HandlerDef, got {:?}", decls[0]),
    }
}

#[test]
fn handler_def_multi_effect() {
    let decls = parse(
        "handler dev_env for Log, Http {\n  log level msg = resume ()\n  get url = resume \"ok\"\n}",
    );
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::HandlerDef { effects, arms, .. } => {
            assert_eq!(effect_names(effects), vec!["Log", "Http"]);
            assert_eq!(arms.len(), 2);
        }
        _ => panic!("expected HandlerDef, got {:?}", decls[0]),
    }
}

#[test]
fn handler_def_with_needs() {
    let decls = parse(
        "handler stripe for Billing needs {Log, Http} {\n  charge account amount = resume (fake_receipt ())\n}",
    );
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::HandlerDef {
            name,
            effects,
            needs,
            arms,
            ..
        } => {
            assert_eq!(name, "stripe");
            assert_eq!(effect_names(effects), vec!["Billing"]);
            assert_eq!(effect_names(needs), vec!["Log", "Http"]);
            assert_eq!(arms.len(), 1);
            assert_eq!(arms[0].node.op_name, "charge");
        }
        _ => panic!("expected HandlerDef, got {:?}", decls[0]),
    }
}

#[test]
fn handler_def_without_needs() {
    let decls =
        parse("handler mock for Billing {\n  charge account amount = resume (fake_receipt ())\n}");
    match &decls[0] {
        Decl::HandlerDef { needs, .. } => {
            assert!(needs.is_empty());
        }
        _ => panic!("expected HandlerDef"),
    }
}

#[test]
fn handler_def_needs_trailing_comma() {
    let decls =
        parse("handler stripe for Billing needs {Log, Http,} {\n  charge a b = resume ()\n}");
    match &decls[0] {
        Decl::HandlerDef { needs, .. } => {
            assert_eq!(effect_names(needs), vec!["Log", "Http"]);
        }
        _ => panic!("expected HandlerDef"),
    }
}

// --- Effect call expressions ---

#[test]
fn effect_call_simple() {
    let expr = parse_expr("log! \"hello\"");
    match &expr {
        Expr {
            kind: ExprKind::App { func, arg, .. },
            ..
        } => {
            match func.as_ref() {
                Expr {
                    kind:
                        ExprKind::EffectCall {
                            name, qualifier, ..
                        },
                    ..
                } => {
                    assert_eq!(name, "log");
                    assert!(qualifier.is_none());
                }
                _ => panic!("expected EffectCall, got {:?}", func),
            }
            assert!(
                matches!(arg.as_ref(), Expr { kind: ExprKind::Lit { value: Lit::String(s, _), .. }, .. } if s == "hello")
            );
        }
        _ => panic!("expected App(EffectCall, _), got {:?}", expr),
    }
}

#[test]
fn effect_call_no_args() {
    let expr = parse_expr("read_line!");
    match &expr {
        Expr {
            kind: ExprKind::EffectCall {
                name, qualifier, ..
            },
            ..
        } => {
            assert_eq!(name, "read_line");
            assert!(qualifier.is_none());
        }
        _ => panic!("expected EffectCall, got {:?}", expr),
    }
}

#[test]
fn effect_call_qualified() {
    let expr = parse_expr("Cache.get! \"key\"");
    match &expr {
        Expr {
            kind: ExprKind::App { func, .. },
            ..
        } => match func.as_ref() {
            Expr {
                kind:
                    ExprKind::EffectCall {
                        name, qualifier, ..
                    },
                ..
            } => {
                assert_eq!(name, "get");
                assert_eq!(qualifier.as_deref(), Some("Cache"));
            }
            _ => panic!("expected EffectCall, got {:?}", func),
        },
        _ => panic!("expected App(EffectCall, _), got {:?}", expr),
    }
}

// --- Resume ---

#[test]
fn resume_expr() {
    let expr = parse_expr("resume ()");
    match &expr {
        Expr {
            kind: ExprKind::Resume { value, .. },
            ..
        } => {
            assert!(matches!(
                value.as_ref(),
                Expr {
                    kind: ExprKind::Lit {
                        value: Lit::Unit,
                        ..
                    },
                    ..
                }
            ));
        }
        _ => panic!("expected Resume, got {:?}", expr),
    }
}

#[test]
fn resume_with_value() {
    let expr = parse_expr("resume answer");
    match &expr {
        Expr {
            kind: ExprKind::Resume { value, .. },
            ..
        } => {
            assert!(
                matches!(value.as_ref(), Expr { kind: ExprKind::Var { name, .. }, .. } if name == "answer")
            );
        }
        _ => panic!("expected Resume, got {:?}", expr),
    }
}

// --- With expressions ---

#[test]
fn with_named_handler() {
    // `with` has lowest precedence — wraps the entire expression
    let expr = parse_expr("run_server () with console_log");
    match &expr {
        Expr {
            kind:
                ExprKind::With {
                    expr: inner,
                    handler,
                    ..
                },
            ..
        } => {
            assert!(matches!(
                inner.as_ref(),
                Expr {
                    kind: ExprKind::App { .. },
                    ..
                }
            ));
            assert!(matches!(handler.as_ref(), Handler::Named(n, _) if n == "console_log"));
        }
        _ => panic!("expected With, got {:?}", expr),
    }
}

#[test]
fn with_inline_handler() {
    let expr = parse_expr("run_server () with {\n  log level msg = print! msg\n}");
    match &expr {
        Expr {
            kind: ExprKind::With { handler, .. },
            ..
        } => match handler.as_ref() {
            Handler::Inline {
                named,
                arms,
                return_clause,
                ..
            } => {
                assert!(named.is_empty());
                assert_eq!(arms.len(), 1);
                assert_eq!(arms[0].node.op_name, "log");
                let param_names: Vec<&str> = arms[0].node.params.iter().map(|(n, _)| n.as_str()).collect();
                assert_eq!(param_names, vec!["level", "msg"]);
                assert!(return_clause.is_none());
            }
            _ => panic!("expected Inline handler, got {:?}", handler),
        },
        _ => panic!("expected With, got {:?}", expr),
    }
}

#[test]
fn with_mixed_handlers() {
    let expr = parse_expr("run () with {\n  console_log,\n  get url = resume \"ok\"\n}");
    match &expr {
        Expr {
            kind: ExprKind::With { handler, .. },
            ..
        } => match handler.as_ref() {
            Handler::Inline { named, arms, .. } => {
                assert_eq!(named, &["console_log"]);
                assert_eq!(arms.len(), 1);
                assert_eq!(arms[0].node.op_name, "get");
            }
            _ => panic!("expected Inline handler, got {:?}", handler),
        },
        _ => panic!("expected With, got {:?}", expr),
    }
}

#[test]
fn with_inline_arms_single_line_comma_separated() {
    let expr = parse_expr("run () with { fail msg = Err msg, return value = Ok value }");
    match &expr {
        Expr {
            kind: ExprKind::With { handler, .. },
            ..
        } => match handler.as_ref() {
            Handler::Inline { named, arms, return_clause, .. } => {
                assert!(named.is_empty());
                assert_eq!(arms.len(), 1);
                assert_eq!(arms[0].node.op_name, "fail");
                assert!(return_clause.is_some());
                assert_eq!(return_clause.as_ref().unwrap().op_name, "return");
            }
            _ => panic!("expected Inline handler, got {:?}", handler),
        },
        _ => panic!("expected With, got {:?}", expr),
    }
}

#[test]
fn with_inline_arms_multiline_no_commas() {
    let expr = parse_expr("run () with {\n  fail msg = Err msg\n  return value = Ok value\n}");
    match &expr {
        Expr {
            kind: ExprKind::With { handler, .. },
            ..
        } => match handler.as_ref() {
            Handler::Inline { named, arms, return_clause, .. } => {
                assert!(named.is_empty());
                assert_eq!(arms.len(), 1);
                assert_eq!(arms[0].node.op_name, "fail");
                assert!(return_clause.is_some());
            }
            _ => panic!("expected Inline handler, got {:?}", handler),
        },
        _ => panic!("expected With, got {:?}", expr),
    }
}

// --- Where clause on annotations ---

#[test]
fn fun_annotation_with_where_clause() {
    let decls = parse("fun show : (x: a) -> String where {a: Show}");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::FunSignature { where_clause, .. } => {
            assert_eq!(where_clause.len(), 1);
            assert_eq!(where_clause[0].type_var, "a");
            let trait_names: Vec<&str> = where_clause[0].traits.iter().map(|(t, _)| t.as_str()).collect();
            assert_eq!(trait_names, vec!["Show"]);
        }
        _ => panic!("expected FunAnnotation, got {:?}", decls[0]),
    }
}

#[test]
fn fun_annotation_where_multiple_bounds() {
    let decls = parse("fun compare : (x: a) -> (y: b) -> Int where {a: Show + Eq, b: Ord}");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::FunSignature { where_clause, .. } => {
            assert_eq!(where_clause.len(), 2);
            assert_eq!(where_clause[0].type_var, "a");
            let trait_names_0: Vec<&str> = where_clause[0].traits.iter().map(|(t, _)| t.as_str()).collect();
            assert_eq!(trait_names_0, vec!["Show", "Eq"]);
            assert_eq!(where_clause[1].type_var, "b");
            let trait_names_1: Vec<&str> = where_clause[1].traits.iter().map(|(t, _)| t.as_str()).collect();
            assert_eq!(trait_names_1, vec!["Ord"]);
        }
        _ => panic!("expected FunAnnotation, got {:?}", decls[0]),
    }
}

#[test]
fn fun_annotation_needs_and_where() {
    let decls = parse("fun f : (x: a) -> Unit needs {Log} where {a: Show}");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::FunSignature {
            effects,
            where_clause,
            ..
        } => {
            assert_eq!(effect_names(effects), vec!["Log"]);
            assert_eq!(where_clause.len(), 1);
            assert_eq!(where_clause[0].type_var, "a");
        }
        _ => panic!("expected FunAnnotation, got {:?}", decls[0]),
    }
}

// --- Trait definitions ---

#[test]
fn trait_def_simple() {
    let decls = parse("trait Show a {\n  fun show : (x: a) -> String\n}");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::TraitDef {
            name,
            type_param,
            supertraits,
            methods,
            ..
        } => {
            assert_eq!(name, "Show");
            assert_eq!(type_param, "a");
            assert!(supertraits.is_empty());
            assert_eq!(methods.len(), 1);
            assert_eq!(methods[0].node.name, "show");
            assert_eq!(methods[0].node.params.len(), 1);
        }
        _ => panic!("expected TraitDef, got {:?}", decls[0]),
    }
}

#[test]
fn trait_def_with_supertraits() {
    let decls = parse("trait Ord a where {a: Eq} {\n  fun compare : (x: a) -> (y: a) -> Ordering\n}");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::TraitDef {
            name,
            type_param,
            supertraits,
            methods,
            ..
        } => {
            assert_eq!(name, "Ord");
            assert_eq!(type_param, "a");
            let st_names: Vec<&str> = supertraits.iter().map(|(n, _)| n.as_str()).collect();
            assert_eq!(st_names, &["Eq"]);
            assert_eq!(methods.len(), 1);
            assert_eq!(methods[0].node.name, "compare");
            assert_eq!(methods[0].node.params.len(), 2);
        }
        _ => panic!("expected TraitDef, got {:?}", decls[0]),
    }
}

// --- Impl definitions ---

#[test]
fn impl_def_simple() {
    let decls = parse("impl Show for User {\n  show user = user.name\n}");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::ImplDef {
            trait_name,
            target_type,
            methods,
            ..
        } => {
            assert_eq!(trait_name, "Show");
            assert_eq!(target_type, "User");
            assert_eq!(methods.len(), 1);
            assert_eq!(methods[0].node.name, "show");
            assert_eq!(methods[0].node.params.len(), 1);
        }
        _ => panic!("expected ImplDef, got {:?}", decls[0]),
    }
}

#[test]
fn impl_def_with_needs() {
    let decls = parse("impl Store for Redis needs {Http, Fail} {\n  get key = http_get key\n}");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::ImplDef {
            trait_name,
            target_type,
            needs,
            methods,
            ..
        } => {
            assert_eq!(trait_name, "Store");
            assert_eq!(target_type, "Redis");
            assert_eq!(effect_names(needs), vec!["Http", "Fail"]);
            assert_eq!(methods.len(), 1);
            assert_eq!(methods[0].node.name, "get");
        }
        _ => panic!("expected ImplDef, got {:?}", decls[0]),
    }
}

// --- Visibility (pub) ---

#[test]
fn pub_type_def() {
    let decls = parse("pub type Shape = Circle(Float)");
    match &decls[0] {
        Decl::TypeDef { public, name, .. } => {
            assert!(public, "pub type should set public = true");
            assert_eq!(name, "Shape");
        }
        _ => panic!("expected TypeDef"),
    }
}

#[test]
fn private_type_def() {
    let decls = parse("type Shape = Circle(Float)");
    match &decls[0] {
        Decl::TypeDef { public, .. } => {
            assert!(!public, "bare type should set public = false");
        }
        _ => panic!("expected TypeDef"),
    }
}

#[test]
fn pub_record_def() {
    let decls = parse("pub record User { name: String }");
    match &decls[0] {
        Decl::RecordDef { public, name, .. } => {
            assert!(public);
            assert_eq!(name, "User");
        }
        _ => panic!("expected RecordDef"),
    }
}

#[test]
fn private_record_def() {
    let decls = parse("record User { name: String }");
    match &decls[0] {
        Decl::RecordDef { public, .. } => {
            assert!(!public);
        }
        _ => panic!("expected RecordDef"),
    }
}

#[test]
fn pub_effect_def() {
    let decls = parse("pub effect Log {\n  fun log : (msg: String) -> Unit\n}");
    match &decls[0] {
        Decl::EffectDef { public, name, .. } => {
            assert!(public);
            assert_eq!(name, "Log");
        }
        _ => panic!("expected EffectDef"),
    }
}

#[test]
fn private_effect_def() {
    let decls = parse("effect Log {\n  fun log : (msg: String) -> Unit\n}");
    match &decls[0] {
        Decl::EffectDef { public, .. } => {
            assert!(!public);
        }
        _ => panic!("expected EffectDef"),
    }
}

#[test]
fn pub_handler_def() {
    let decls = parse("pub handler console_log for Log {\n  log msg = resume ()\n}");
    match &decls[0] {
        Decl::HandlerDef { public, name, .. } => {
            assert!(public);
            assert_eq!(name, "console_log");
        }
        _ => panic!("expected HandlerDef"),
    }
}

#[test]
fn private_handler_def() {
    let decls = parse("handler console_log for Log {\n  log msg = resume ()\n}");
    match &decls[0] {
        Decl::HandlerDef { public, .. } => {
            assert!(!public);
        }
        _ => panic!("expected HandlerDef"),
    }
}

#[test]
fn pub_trait_def() {
    let decls = parse("pub trait Show a {\n  fun show : (x: a) -> String\n}");
    match &decls[0] {
        Decl::TraitDef { public, name, .. } => {
            assert!(public);
            assert_eq!(name, "Show");
        }
        _ => panic!("expected TraitDef"),
    }
}

#[test]
fn private_trait_def() {
    let decls = parse("trait Show a {\n  fun show : (x: a) -> String\n}");
    match &decls[0] {
        Decl::TraitDef { public, .. } => {
            assert!(!public);
        }
        _ => panic!("expected TraitDef"),
    }
}

#[test]
fn pub_fun_annotation() {
    let decls = parse("pub fun add : (a: Int) -> (b: Int) -> Int");
    match &decls[0] {
        Decl::FunSignature { public, name, .. } => {
            assert!(public);
            assert_eq!(name, "add");
        }
        _ => panic!("expected FunAnnotation"),
    }
}

#[test]
fn private_fun_annotation() {
    let decls = parse("fun add : (a: Int) -> (b: Int) -> Int");
    match &decls[0] {
        Decl::FunSignature { public, .. } => {
            assert!(!public);
        }
        _ => panic!("expected FunAnnotation"),
    }
}

// --- String interpolation ---

#[test]
fn interp_empty() {
    // $"" → StringInterp with no parts
    let expr = parse_expr(r#"$"""#);
    assert!(matches!(expr, Expr { kind: ExprKind::StringInterp { ref parts, .. }, .. } if parts.is_empty()));
}

#[test]
fn interp_no_holes() {
    // $"hello" → StringInterp with one literal part
    let expr = parse_expr(r#"$"hello""#);
    match expr {
        Expr { kind: ExprKind::StringInterp { parts, .. }, .. } => {
            assert_eq!(parts.len(), 1);
            assert!(matches!(&parts[0], StringPart::Lit(s) if s == "hello"));
        }
        other => panic!("expected StringInterp, got {:?}", other),
    }
}

#[test]
fn interp_single_hole() {
    // $"{x}" → StringInterp with one Expr part
    let expr = parse_expr(r#"$"{x}""#);
    match expr {
        Expr { kind: ExprKind::StringInterp { parts, .. }, .. } => {
            assert_eq!(parts.len(), 1);
            assert!(matches!(&parts[0], StringPart::Expr(e) if matches!(&e.kind, ExprKind::Var { name, .. } if name == "x")));
        }
        other => panic!("expected StringInterp, got {:?}", other),
    }
}

#[test]
fn interp_literal_and_hole() {
    // $"hello {name}" → StringInterp with literal + expr
    let expr = parse_expr(r#"$"hello {name}""#);
    match expr {
        Expr { kind: ExprKind::StringInterp { parts, .. }, .. } => {
            assert_eq!(parts.len(), 2);
            assert!(matches!(&parts[0], StringPart::Lit(s) if s == "hello "));
            assert!(matches!(&parts[1], StringPart::Expr(e) if matches!(&e.kind, ExprKind::Var { name, .. } if name == "name")));
        }
        other => panic!("expected StringInterp, got {:?}", other),
    }
}

#[test]
fn interp_escaped_braces() {
    // $"\{" → StringInterp with literal "{"
    let expr = parse_expr("$\"\\{\"");
    match expr {
        Expr { kind: ExprKind::StringInterp { parts, .. }, .. } => {
            assert_eq!(parts.len(), 1);
            assert!(matches!(&parts[0], StringPart::Lit(s) if s == "{"));
        }
        other => panic!("expected StringInterp, got {:?}", other),
    }
}

#[test]
fn interp_pipe_in_hole() {
    // $"{xs |> show}" parses without error
    parse_expr(r#"$"{xs |> show}""#);
}

// --- List comprehensions ---

#[test]
fn list_comprehension_simple_generator() {
    let expr = parse_expr("[x | x <- xs]");
    match expr {
        Expr { kind: ExprKind::ListComprehension { body, qualifiers }, .. } => {
            assert!(matches!(*body, Expr { kind: ExprKind::Var { name, .. }, .. } if name == "x"));
            assert_eq!(qualifiers.len(), 1);
            assert!(matches!(&qualifiers[0], ComprehensionQualifier::Generator(
                Pat::Var { name, .. }, _
            ) if name == "x"));
        }
        other => panic!("expected ListComprehension, got {:?}", other),
    }
}

#[test]
fn list_comprehension_with_guard() {
    let expr = parse_expr("[x | x <- xs, x > 0]");
    match expr {
        Expr { kind: ExprKind::ListComprehension { qualifiers, .. }, .. } => {
            assert_eq!(qualifiers.len(), 2);
            assert!(matches!(&qualifiers[0], ComprehensionQualifier::Generator(..)));
            assert!(matches!(&qualifiers[1], ComprehensionQualifier::Guard(..)));
        }
        other => panic!("expected ListComprehension, got {:?}", other),
    }
}

#[test]
fn list_comprehension_nested_generators() {
    let expr = parse_expr("[x + y | x <- xs, y <- ys]");
    match expr {
        Expr { kind: ExprKind::ListComprehension { qualifiers, .. }, .. } => {
            assert_eq!(qualifiers.len(), 2);
            assert!(matches!(&qualifiers[0], ComprehensionQualifier::Generator(
                Pat::Var { name, .. }, _
            ) if name == "x"));
            assert!(matches!(&qualifiers[1], ComprehensionQualifier::Generator(
                Pat::Var { name, .. }, _
            ) if name == "y"));
        }
        other => panic!("expected ListComprehension, got {:?}", other),
    }
}

#[test]
fn list_comprehension_with_let() {
    let expr = parse_expr("[y | x <- xs, let y = x + 1]");
    match expr {
        Expr { kind: ExprKind::ListComprehension { qualifiers, .. }, .. } => {
            assert_eq!(qualifiers.len(), 2);
            assert!(matches!(&qualifiers[0], ComprehensionQualifier::Generator(..)));
            assert!(matches!(&qualifiers[1], ComprehensionQualifier::Let(..)));
        }
        other => panic!("expected ListComprehension, got {:?}", other),
    }
}

#[test]
fn empty_list_still_works() {
    let expr = parse_expr("[]");
    assert!(matches!(expr, Expr { kind: ExprKind::ListLit { ref elements, .. }, .. } if elements.is_empty()));
}

#[test]
fn normal_list_still_works() {
    let expr = parse_expr("[1, 2]");
    match expr {
        Expr { kind: ExprKind::ListLit { elements, .. }, .. } => {
            assert_eq!(elements.len(), 2);
            assert!(matches!(&elements[0], Expr { kind: ExprKind::Lit { value: Lit::Int(_, 1) }, .. }));
            assert!(matches!(&elements[1], Expr { kind: ExprKind::Lit { value: Lit::Int(_, 2) }, .. }));
        }
        other => panic!("expected ListLit, got {:?}", other),
    }
}

#[test]
fn list_comprehension_map_transform() {
    // [x * 2 | x <- xs] parses without error
    parse_expr("[x * 2 | x <- xs]");
}

// --- Function composition ---

#[test]
fn compose_forward() {
    let expr = parse_expr("f >> g");
    match expr {
        Expr { kind: ExprKind::ComposeForward { segments }, .. } => {
            assert_eq!(segments.len(), 2);
            assert!(matches!(&segments[0].node, Expr { kind: ExprKind::Var { name, .. }, .. } if name == "f"));
            assert!(matches!(&segments[1].node, Expr { kind: ExprKind::Var { name, .. }, .. } if name == "g"));
        }
        other => panic!("expected ComposeForward, got {:?}", other),
    }
}

#[test]
fn compose_backward() {
    let expr = parse_expr("f << g");
    match expr {
        Expr { kind: ExprKind::ComposeBack { segments }, .. } => {
            assert_eq!(segments.len(), 2);
            assert!(matches!(&segments[0].node, Expr { kind: ExprKind::Var { name, .. }, .. } if name == "f"));
            assert!(matches!(&segments[1].node, Expr { kind: ExprKind::Var { name, .. }, .. } if name == "g"));
        }
        other => panic!("expected ComposeBack, got {:?}", other),
    }
}

#[test]
fn compose_chain() {
    // f >> g >> h parses without error (left-associative)
    parse_expr("f >> g >> h");
}

// --- Generic effects ---

#[test]
fn effect_def_with_type_params() {
    let decls = parse("effect State s {\n  fun get : Unit -> s\n  fun put : (val: s) -> Unit\n}");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::EffectDef {
            name,
            type_params,
            operations,
            ..
        } => {
            assert_eq!(name, "State");
            assert_eq!(type_params, &["s"]);
            assert_eq!(operations.len(), 2);
            assert_eq!(operations[0].node.name, "get");
            assert_eq!(operations[1].node.name, "put");
        }
        _ => panic!("expected EffectDef"),
    }
}

#[test]
fn handler_for_parameterized_effect() {
    let decls =
        parse("handler counter for State Int {\n  get () = resume 0\n  put val = resume ()\n}");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::HandlerDef {
            name,
            effects,
            arms,
            ..
        } => {
            assert_eq!(name, "counter");
            assert_eq!(effects.len(), 1);
            assert_eq!(effects[0].name, "State");
            assert_eq!(effects[0].type_args.len(), 1);
            assert_eq!(effects[0].type_args[0], TypeExpr::Named { name: "Int".into(), span: Span { start: 0, end: 0 } });
            assert_eq!(arms.len(), 2);
        }
        _ => panic!("expected HandlerDef"),
    }
}

#[test]
fn handler_with_where_clause() {
    let decls = parse(
        "handler show_store for Store a where {a: Show} {\n  save item = resume ()\n  load () = resume \"\"\n}",
    );
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::HandlerDef {
            name,
            effects,
            where_clause,
            arms,
            ..
        } => {
            assert_eq!(name, "show_store");
            assert_eq!(effects.len(), 1);
            assert_eq!(effects[0].name, "Store");
            assert_eq!(where_clause.len(), 1);
            assert_eq!(where_clause[0].type_var, "a");
            assert_eq!(where_clause[0].traits.len(), 1);
            assert_eq!(where_clause[0].traits[0].0, "Show");
            assert_eq!(arms.len(), 2);
        }
        _ => panic!("expected HandlerDef"),
    }
}

#[test]
fn handler_with_needs_and_where_clause() {
    let decls = parse(
        "handler logged_store for Store a needs {Log} where {a: Show} {\n  save item = { log! (show item); resume () }\n  load () = resume \"\"\n}",
    );
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::HandlerDef {
            name,
            effects,
            needs,
            where_clause,
            ..
        } => {
            assert_eq!(name, "logged_store");
            assert_eq!(effects[0].name, "Store");
            assert_eq!(effect_names(needs), vec!["Log"]);
            assert_eq!(where_clause.len(), 1);
            assert_eq!(where_clause[0].type_var, "a");
            assert_eq!(where_clause[0].traits[0].0, "Show");
        }
        _ => panic!("expected HandlerDef"),
    }
}

#[test]
fn fun_annotation_needs_parameterized_effect() {
    let decls = parse("fun foo : Unit -> Int needs {State Int}");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::FunSignature { effects, .. } => {
            assert_eq!(effects.len(), 1);
            assert_eq!(effects[0].name, "State");
            assert_eq!(effects[0].type_args.len(), 1);
            assert_eq!(effects[0].type_args[0], TypeExpr::Named { name: "Int".into(), span: Span { start: 0, end: 0 } });
        }
        _ => panic!("expected FunAnnotation"),
    }
}

#[test]
fn needs_mixed_parameterized_and_plain() {
    let decls = parse("fun foo : Unit -> Int needs {State Int, Log}");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::FunSignature { effects, .. } => {
            assert_eq!(effects.len(), 2);
            assert_eq!(effects[0].name, "State");
            assert_eq!(effects[0].type_args.len(), 1);
            assert_eq!(effects[1].name, "Log");
            assert_eq!(effects[1].type_args.len(), 0);
        }
        _ => panic!("expected FunAnnotation"),
    }
}

// --- @external ---

#[test]
fn external_fun_basic() {
    let decls =
        parse(r#"@external("erlang", "lists", "reverse") fun reverse : (list: List a) -> List a"#);
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::FunSignature {
            public,
            name,
            params,
            annotations,
            ..
        } => {
            assert!(!public);
            assert_eq!(name, "reverse");
            assert_eq!(params.len(), 1);
            assert_eq!(params[0].0, "list");
            assert_eq!(annotations.len(), 1);
            assert_eq!(annotations[0].name, "external");
            assert_eq!(annotations[0].args, vec![
                Lit::String("erlang".to_string(), StringKind::Normal),
                Lit::String("lists".to_string(), StringKind::Normal),
                Lit::String("reverse".to_string(), StringKind::Normal),
            ]);
        }
        _ => panic!("expected FunSignature with @external"),
    }
}

#[test]
fn external_fun_pub() {
    let decls = parse(r#"@external("erlang", "maps", "new") pub fun empty : Unit -> Dict a b"#);
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::FunSignature {
            public,
            name,
            params,
            annotations,
            ..
        } => {
            assert!(public);
            assert_eq!(name, "empty");
            assert_eq!(params.len(), 1); // () counts as a unit param
            assert_eq!(annotations.len(), 1);
            assert_eq!(annotations[0].name, "external");
        }
        _ => panic!("expected FunSignature with @external"),
    }
}

#[test]
fn external_fun_multiline() {
    let decls = parse(
        r#"
@external("erlang", "lists", "foldl")
fun foldl : (f: a -> b -> a) -> (acc: a) -> (list: List b) -> a
"#,
    );
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::FunSignature {
            name,
            params,
            annotations,
            ..
        } => {
            assert_eq!(name, "foldl");
            assert_eq!(params.len(), 3);
            assert_eq!(annotations.len(), 1);
            assert_eq!(annotations[0].name, "external");
        }
        _ => panic!("expected FunSignature with @external"),
    }
}

#[test]
fn external_fun_with_where_clause() {
    let decls = parse(
        r#"@external("erlang", "my_mod", "do_thing") fun do_thing : (x: a) -> String where {a: Show}"#,
    );
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::FunSignature {
            name,
            where_clause,
            annotations,
            ..
        } => {
            assert_eq!(name, "do_thing");
            assert_eq!(where_clause.len(), 1);
            assert_eq!(where_clause[0].type_var, "a");
            let trait_names: Vec<&str> = where_clause[0].traits.iter().map(|(t, _)| t.as_str()).collect();
            assert_eq!(trait_names, vec!["Show"]);
            assert_eq!(annotations.len(), 1);
            assert_eq!(annotations[0].name, "external");
        }
        _ => panic!("expected FunSignature with @external"),
    }
}

#[test]
fn type_def_deriving_show() {
    let decls = parse("type Color = Red | Green | Blue deriving (Show)");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::TypeDef { name, deriving, .. } => {
            assert_eq!(name, "Color");
            assert_eq!(deriving, &vec!["Show".to_string()]);
        }
        _ => panic!("expected TypeDef"),
    }
}

#[test]
fn type_def_deriving_multiple() {
    // Parser accepts multiple traits even if not all are implemented yet
    let decls = parse("type Foo = A | B deriving (Show, Eq)");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::TypeDef { deriving, .. } => {
            assert_eq!(deriving, &vec!["Show".to_string(), "Eq".to_string()]);
        }
        _ => panic!("expected TypeDef"),
    }
}

#[test]
fn type_def_no_deriving() {
    let decls = parse("type Foo = A | B");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::TypeDef { deriving, .. } => {
            assert!(deriving.is_empty());
        }
        _ => panic!("expected TypeDef"),
    }
}

#[test]
fn receive_simple() {
    let expr = parse_expr("receive {\n  Ping(sender) -> sender\n  Stop -> 0\n}");
    match expr {
        Expr {
            kind: ExprKind::Receive {
                arms, after_clause, ..
            },
            ..
        } => {
            assert_eq!(arms.len(), 2);
            assert!(after_clause.is_none());
        }
        _ => panic!("expected Receive, got {:?}", expr),
    }
}

#[test]
fn receive_with_after() {
    let expr = parse_expr("receive {\n  Msg(x) -> x\n  after 5000 -> 0\n}");
    match expr {
        Expr {
            kind: ExprKind::Receive {
                arms, after_clause, ..
            },
            ..
        } => {
            assert_eq!(arms.len(), 1);
            assert!(after_clause.is_some());
        }
        _ => panic!("expected Receive, got {:?}", expr),
    }
}

#[test]
fn receive_with_guard() {
    let expr = parse_expr("receive {\n  Msg(x) | x > 0 -> x\n  _ -> 0\n}");
    match expr {
        Expr {
            kind: ExprKind::Receive { arms, .. },
            ..
        } => {
            assert_eq!(arms.len(), 2);
            assert!(arms[0].node.guard.is_some());
            assert!(arms[1].node.guard.is_none());
        }
        _ => panic!("expected Receive, got {:?}", expr),
    }
}
