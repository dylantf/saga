use super::*;
use crate::ast::Handler;
use crate::lexer::Lexer;

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
        Expr::Lit {
            value: Lit::Int(42),
            ..
        }
    ));
}

#[test]
fn literal_float() {
    let expr = parse_expr("1.5");
    assert!(matches!(expr, Expr::Lit { value: Lit::Float(f), .. } if f == 1.5));
}

#[test]
fn literal_string() {
    let expr = parse_expr("\"hello\"");
    assert!(matches!(expr, Expr::Lit { value: Lit::String(s), .. } if s == "hello"));
}

#[test]
fn literal_bool() {
    let t = parse_expr("True");
    let f = parse_expr("False");
    assert!(matches!(
        t,
        Expr::Lit {
            value: Lit::Bool(true),
            ..
        }
    ));
    assert!(matches!(
        f,
        Expr::Lit {
            value: Lit::Bool(false),
            ..
        }
    ));
}

// --- Variables and constructors ---

#[test]
fn variable() {
    let expr = parse_expr("foo");
    assert!(matches!(expr, Expr::Var { name, .. } if name == "foo"));
}

#[test]
fn constructor() {
    let expr = parse_expr("Some");
    assert!(matches!(expr, Expr::Constructor { name, .. } if name == "Some"));
}

// --- Binary operators ---

#[test]
fn binary_add() {
    let expr = parse_expr("1 + 2");
    assert!(matches!(expr, Expr::BinOp { op: BinOp::Add, .. }));
}

#[test]
fn binary_precedence_mul_over_add() {
    // 1 + 2 * 3 should parse as 1 + (2 * 3)
    let expr = parse_expr("1 + 2 * 3");
    match expr {
        Expr::BinOp {
            op: BinOp::Add,
            left,
            right,
            ..
        } => {
            assert!(matches!(
                *left,
                Expr::Lit {
                    value: Lit::Int(1),
                    ..
                }
            ));
            assert!(matches!(*right, Expr::BinOp { op: BinOp::Mul, .. }));
        }
        _ => panic!("expected Add at top level, got {:?}", expr),
    }
}

#[test]
fn binary_precedence_comparison_over_logic() {
    // x == 1 && y == 2 should parse as (x == 1) && (y == 2)
    let expr = parse_expr("x == 1 && y == 2");
    match expr {
        Expr::BinOp {
            op: BinOp::And,
            left,
            right,
            ..
        } => {
            assert!(matches!(*left, Expr::BinOp { op: BinOp::Eq, .. }));
            assert!(matches!(*right, Expr::BinOp { op: BinOp::Eq, .. }));
        }
        _ => panic!("expected And at top level, got {:?}", expr),
    }
}

#[test]
fn binary_left_associative() {
    // 1 - 2 - 3 should parse as (1 - 2) - 3
    let expr = parse_expr("1 - 2 - 3");
    match expr {
        Expr::BinOp {
            op: BinOp::Sub,
            left,
            right,
            ..
        } => {
            assert!(matches!(*left, Expr::BinOp { op: BinOp::Sub, .. }));
            assert!(matches!(
                *right,
                Expr::Lit {
                    value: Lit::Int(3),
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
        Expr::BinOp {
            op: BinOp::Mul,
            left,
            ..
        } => {
            assert!(matches!(*left, Expr::BinOp { op: BinOp::Add, .. }));
        }
        _ => panic!("expected Mul at top level, got {:?}", expr),
    }
}

// --- Unary minus ---

#[test]
fn unary_minus() {
    let expr = parse_expr("-x");
    assert!(matches!(expr, Expr::UnaryMinus { .. }));
}

#[test]
fn unary_minus_precedence() {
    // -x + 1 should parse as (-x) + 1
    let expr = parse_expr("-x + 1");
    match expr {
        Expr::BinOp {
            op: BinOp::Add,
            left,
            ..
        } => {
            assert!(matches!(*left, Expr::UnaryMinus { .. }));
        }
        _ => panic!("expected Add at top level, got {:?}", expr),
    }
}

// --- Function application ---

#[test]
fn application_single_arg() {
    let expr = parse_expr("f x");
    match expr {
        Expr::App { func, arg, .. } => {
            assert!(matches!(*func, Expr::Var { name, .. } if name == "f"));
            assert!(matches!(*arg, Expr::Var { name, .. } if name == "x"));
        }
        _ => panic!("expected App, got {:?}", expr),
    }
}

#[test]
fn application_curried() {
    // f x y should parse as App(App(f, x), y)
    let expr = parse_expr("f x y");
    match expr {
        Expr::App { func, arg, .. } => {
            assert!(matches!(*arg, Expr::Var { name, .. } if name == "y"));
            assert!(matches!(*func, Expr::App { .. }));
        }
        _ => panic!("expected nested App, got {:?}", expr),
    }
}

#[test]
fn application_binds_tighter_than_binop() {
    // f x + g y should parse as (f x) + (g y)
    let expr = parse_expr("f x + g y");
    match expr {
        Expr::BinOp {
            op: BinOp::Add,
            left,
            right,
            ..
        } => {
            assert!(matches!(*left, Expr::App { .. }));
            assert!(matches!(*right, Expr::App { .. }));
        }
        _ => panic!("expected Add at top level, got {:?}", expr),
    }
}

// --- Pipes ---

#[test]
fn forward_pipe() {
    // x |> f desugars to App(f, x)
    let expr = parse_expr("x |> f");
    match expr {
        Expr::App { func, arg, .. } => {
            assert!(matches!(*func, Expr::Var { name, .. } if name == "f"));
            assert!(matches!(*arg, Expr::Var { name, .. } if name == "x"));
        }
        _ => panic!("expected App from pipe, got {:?}", expr),
    }
}

#[test]
fn backward_pipe() {
    // f <| x desugars to App(f, x)
    let expr = parse_expr("f <| x");
    match expr {
        Expr::App { func, arg, .. } => {
            assert!(matches!(*func, Expr::Var { name, .. } if name == "f"));
            assert!(matches!(*arg, Expr::Var { name, .. } if name == "x"));
        }
        _ => panic!("expected App from backward pipe, got {:?}", expr),
    }
}

#[test]
fn cons_operator_expr() {
    // x :: xs  desugars to  App(App(Cons, x), xs)
    let expr = parse_expr("x :: xs");
    match expr {
        Expr::App { func, arg, .. } => {
            assert!(matches!(*arg, Expr::Var { name, .. } if name == "xs"));
            match *func {
                Expr::App { func, arg, .. } => {
                    assert!(matches!(*func, Expr::Constructor { name, .. } if name == "Cons"));
                    assert!(matches!(*arg, Expr::Var { name, .. } if name == "x"));
                }
                _ => panic!("expected inner App"),
            }
        }
        _ => panic!("expected App from ::, got {:?}", expr),
    }
}

#[test]
fn cons_operator_right_associative() {
    // 1 :: 2 :: xs  =>  Cons(1, Cons(2, xs))
    let expr = parse_expr("1 :: 2 :: xs");
    // Outer: App(App(Cons, 1), <inner>)
    match expr {
        Expr::App { arg, .. } => {
            // arg is Cons(2, xs)
            assert!(matches!(*arg, Expr::App { .. }));
        }
        _ => panic!("expected App, got {:?}", expr),
    }
}

// --- If/else ---

#[test]
fn if_else() {
    let expr = parse_expr("if True then 1 else 2");
    match expr {
        Expr::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            assert!(matches!(
                *cond,
                Expr::Lit {
                    value: Lit::Bool(true),
                    ..
                }
            ));
            assert!(matches!(
                *then_branch,
                Expr::Lit {
                    value: Lit::Int(1),
                    ..
                }
            ));
            assert!(matches!(
                *else_branch,
                Expr::Lit {
                    value: Lit::Int(2),
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
        Expr::If { else_branch, .. } => {
            assert!(matches!(*else_branch, Expr::If { .. }));
        }
        _ => panic!("expected If, got {:?}", expr),
    }
}

// --- Blocks ---

#[test]
fn block_single_expr() {
    let expr = parse_expr("{ 42 }");
    match expr {
        Expr::Block { stmts, .. } => {
            assert_eq!(stmts.len(), 1);
            assert!(matches!(
                stmts[0],
                Stmt::Expr(Expr::Lit {
                    value: Lit::Int(42),
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
        Expr::Block { stmts, .. } => {
            assert_eq!(stmts.len(), 2);
            assert!(matches!(&stmts[0], Stmt::Let { pattern: Pat::Var { name, .. }, .. } if name == "x"));
            assert!(matches!(
                &stmts[1],
                Stmt::Expr(Expr::BinOp { op: BinOp::Add, .. })
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
fn pattern_wildcard_prefixed() {
    let pat = parse_pattern("_unused");
    assert!(matches!(pat, Pat::Wildcard { .. }));
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
            value: Lit::Int(42),
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
fn pattern_bare_constructor() {
    let pat = parse_pattern("None");
    match pat {
        Pat::Constructor { name, args, .. } => {
            assert_eq!(name, "None");
            assert!(args.is_empty());
        }
        _ => panic!("expected Constructor, got {:?}", pat),
    }
}

#[test]
fn pattern_constructor_with_args() {
    let pat = parse_pattern("Some(x)");
    match pat {
        Pat::Constructor { name, args, .. } => {
            assert_eq!(name, "Some");
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
    let pat = parse_pattern("Some(Cons(a, b))");
    match pat {
        Pat::Constructor { name, args, .. } => {
            assert_eq!(name, "Some");
            assert_eq!(args.len(), 1);
            assert!(matches!(&args[0], Pat::Constructor { name, .. } if name == "Cons"));
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
    let decls = parse("fun add (a: Int) (b: Int) -> Int");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::FunAnnotation {
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
            assert!(matches!(&params[0].1, TypeExpr::Named(n) if n == "Int"));
            assert!(matches!(return_type, TypeExpr::Named(n) if n == "Int"));
            assert!(effects.is_empty());
        }
        _ => panic!("expected FunAnnotation, got {:?}", decls[0]),
    }
}

#[test]
fn fun_annotation_public_with_effects() {
    let decls = parse("pub fun print (msg: String) -> Unit needs { Console }");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::FunAnnotation {
            public, effects, ..
        } => {
            assert!(public);
            assert_eq!(effects, &vec!["Console".to_string()]);
        }
        _ => panic!("expected FunAnnotation, got {:?}", decls[0]),
    }
}

#[test]
fn fun_annotation_unit_param() {
    let decls = parse("fun do_work () -> Int needs { Log }");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::FunAnnotation {
            name,
            params,
            effects,
            ..
        } => {
            assert_eq!(name, "do_work");
            assert_eq!(params.len(), 1);
            assert_eq!(params[0].0, "_");
            assert_eq!(params[0].1, TypeExpr::Named("Unit".into()));
            assert_eq!(effects, &vec!["Log".to_string()]);
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
            assert!(matches!(body, Expr::BinOp { op: BinOp::Add, .. }));
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
    let decls = parse("type Option a {\n  Some(a)\n  None\n}");
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
            assert_eq!(variants[0].name, "Some");
            assert_eq!(variants[0].fields.len(), 1);
            assert_eq!(variants[1].name, "None");
            assert!(variants[1].fields.is_empty());
        }
        _ => panic!("expected TypeDef, got {:?}", decls[0]),
    }
}

// --- Case expressions ---

#[test]
fn case_simple() {
    let expr = parse_expr("case x {\n  Some(v) -> v\n  None -> 0\n}");
    match expr {
        Expr::Case { arms, .. } => {
            assert_eq!(arms.len(), 2);
            assert!(arms[0].guard.is_none());
            assert!(matches!(&arms[0].pattern, Pat::Constructor { name, .. } if name == "Some"));
            assert!(matches!(&arms[1].pattern, Pat::Constructor { name, .. } if name == "None"));
        }
        _ => panic!("expected Case, got {:?}", expr),
    }
}

#[test]
fn case_with_guard() {
    let expr = parse_expr("case x {\n  n if n > 0 -> n\n  _ -> 0\n}");
    match expr {
        Expr::Case { arms, .. } => {
            assert_eq!(arms.len(), 2);
            assert!(arms[0].guard.is_some());
            assert!(arms[1].guard.is_none());
            assert!(matches!(&arms[1].pattern, Pat::Wildcard { .. }));
        }
        _ => panic!("expected Case, got {:?}", expr),
    }
}

// --- Type expressions ---

#[test]
fn type_expr_named() {
    let decls = parse("fun id (x: Int) -> Int");
    match &decls[0] {
        Decl::FunAnnotation {
            params,
            return_type,
            ..
        } => {
            assert!(matches!(&params[0].1, TypeExpr::Named(n) if n == "Int"));
            assert!(matches!(return_type, TypeExpr::Named(n) if n == "Int"));
        }
        _ => panic!("expected FunAnnotation"),
    }
}

#[test]
fn type_expr_application() {
    let decls = parse("fun unwrap (x: Option a) -> a");
    match &decls[0] {
        Decl::FunAnnotation {
            params,
            return_type,
            ..
        } => {
            assert!(matches!(&params[0].1, TypeExpr::App(_, _)));
            assert!(matches!(return_type, TypeExpr::Var(v) if v == "a"));
        }
        _ => panic!("expected FunAnnotation"),
    }
}

#[test]
fn type_expr_arrow() {
    let decls = parse("fun apply (f: a -> b) (x: a) -> b");
    match &decls[0] {
        Decl::FunAnnotation { params, .. } => {
            assert!(matches!(&params[0].1, TypeExpr::Arrow(_, _, _)));
        }
        _ => panic!("expected FunAnnotation"),
    }
}

// --- Combined programs ---

#[test]
fn annotation_and_binding() {
    let decls = parse("fun add (a: Int) (b: Int) -> Int\nadd x y = x + y");
    assert_eq!(decls.len(), 2);
    assert!(matches!(&decls[0], Decl::FunAnnotation { .. }));
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
        Expr::RecordCreate { name, fields, .. } => {
            assert_eq!(name, "User");
            assert_eq!(fields.len(), 2);
            assert_eq!(fields[0].0, "name");
            assert!(
                matches!(&fields[0].1, Expr::Lit { value: Lit::String(s), .. } if s == "Dylan")
            );
            assert_eq!(fields[1].0, "age");
            assert!(matches!(
                &fields[1].1,
                Expr::Lit {
                    value: Lit::Int(30),
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
        Expr::RecordCreate { name, fields, .. } => {
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
        Expr::RecordCreate { fields, .. } => {
            assert_eq!(fields.len(), 2);
            assert!(matches!(&fields[0].1, Expr::BinOp { op: BinOp::Add, .. }));
            assert!(matches!(&fields[1].1, Expr::BinOp { op: BinOp::Mul, .. }));
        }
        _ => panic!("expected RecordCreate, got {:?}", expr),
    }
}

#[test]
fn record_create_multiline() {
    let expr = parse_expr("User {\n  name: \"Dylan\"\n  age: 30\n}");
    match expr {
        Expr::RecordCreate { name, fields, .. } => {
            assert_eq!(name, "User");
            assert_eq!(fields.len(), 2);
        }
        _ => panic!("expected RecordCreate, got {:?}", expr),
    }
}

#[test]
fn bare_constructor_without_braces() {
    let expr = parse_expr("None");
    assert!(matches!(expr, Expr::Constructor { name, .. } if name == "None"));
}

// --- Record update ---

#[test]
fn record_update_simple() {
    let expr = parse_expr("{ user | age: 31 }");
    match expr {
        Expr::RecordUpdate { record, fields, .. } => {
            assert!(matches!(*record, Expr::Var { name, .. } if name == "user"));
            assert_eq!(fields.len(), 1);
            assert_eq!(fields[0].0, "age");
            assert!(matches!(
                &fields[0].1,
                Expr::Lit {
                    value: Lit::Int(31),
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
        Expr::RecordUpdate { fields, .. } => {
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
        Expr::RecordUpdate { fields, .. } => {
            assert_eq!(fields.len(), 1);
            assert!(matches!(&fields[0].1, Expr::BinOp { op: BinOp::Add, .. }));
        }
        _ => panic!("expected RecordUpdate, got {:?}", expr),
    }
}

#[test]
fn block_still_works() {
    // Make sure blocks didn't break with record update disambiguation
    let expr = parse_expr("{\n  let x = 1\n  x\n}");
    assert!(matches!(expr, Expr::Block { .. }));
}

#[test]
fn block_single_expr_still_works() {
    let expr = parse_expr("{ 42 }");
    match expr {
        Expr::Block { stmts, .. } => {
            assert_eq!(stmts.len(), 1);
            assert!(matches!(
                &stmts[0],
                Stmt::Expr(Expr::Lit {
                    value: Lit::Int(42),
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
        Expr::FieldAccess { expr, field, .. } => {
            assert!(matches!(*expr, Expr::Var { name, .. } if name == "user"));
            assert_eq!(field, "name");
        }
        _ => panic!("expected FieldAccess, got {:?}", expr),
    }
}

#[test]
fn field_access_chained() {
    let expr = parse_expr("user.profile.name");
    match expr {
        Expr::FieldAccess {
            expr: inner, field, ..
        } => {
            assert_eq!(field, "name");
            match *inner {
                Expr::FieldAccess {
                    expr: innermost,
                    field: mid_field,
                    ..
                } => {
                    assert!(matches!(*innermost, Expr::Var { name, .. } if name == "user"));
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
        Expr::App { func, arg, .. } => {
            assert!(matches!(*func, Expr::Var { name, .. } if name == "f"));
            assert!(matches!(*arg, Expr::FieldAccess { field, .. } if field == "name"));
        }
        _ => panic!("expected App, got {:?}", expr),
    }
}

#[test]
fn field_access_in_binop() {
    let expr = parse_expr("user.age + 1");
    match expr {
        Expr::BinOp {
            left,
            op: BinOp::Add,
            ..
        } => {
            assert!(matches!(*left, Expr::FieldAccess { field, .. } if field == "age"));
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
            assert_eq!(fields[0].0, "name");
            assert!(matches!(&fields[0].1, TypeExpr::Named(n) if n == "String"));
            assert_eq!(fields[1].0, "age");
            assert!(matches!(&fields[1].1, TypeExpr::Named(n) if n == "Int"));
        }
        _ => panic!("expected RecordDef, got {:?}", decls[0]),
    }
}

#[test]
fn record_def_no_trailing_comma() {
    let decls = parse("record Point {\n  x: Int\n  y: Int\n}");
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
            assert!(matches!(&fields[0].1, TypeExpr::App(_, _)));
        }
        _ => panic!("expected RecordDef, got {:?}", decls[0]),
    }
}

// --- Effect definitions ---

#[test]
fn effect_def_single_op() {
    let decls = parse("effect Log {\n  fun log (level: String) (msg: String) -> Unit\n}");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::EffectDef { name, operations, .. } => {
            assert_eq!(name, "Log");
            assert_eq!(operations.len(), 1);
            assert_eq!(operations[0].name, "log");
            assert_eq!(operations[0].params.len(), 2);
            assert_eq!(operations[0].params[0].0, "level");
            assert_eq!(operations[0].params[1].0, "msg");
        }
        _ => panic!("expected EffectDef, got {:?}", decls[0]),
    }
}

#[test]
fn effect_def_multiple_ops() {
    let decls = parse("effect Http {\n  fun get (url: String) -> String\n  fun post (url: String) (body: String) -> String\n}");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::EffectDef { name, operations, .. } => {
            assert_eq!(name, "Http");
            assert_eq!(operations.len(), 2);
            assert_eq!(operations[0].name, "get");
            assert_eq!(operations[1].name, "post");
            assert_eq!(operations[1].params.len(), 2);
        }
        _ => panic!("expected EffectDef, got {:?}", decls[0]),
    }
}

// --- Handler definitions ---

#[test]
fn handler_def_simple() {
    let decls = parse("handler console_log for Log {\n  log level msg -> print! (level <> msg)\n}");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::HandlerDef { name, effects, arms, return_clause, .. } => {
            assert_eq!(name, "console_log");
            assert_eq!(effects, &["Log"]);
            assert_eq!(arms.len(), 1);
            assert_eq!(arms[0].op_name, "log");
            assert_eq!(arms[0].params, vec!["level", "msg"]);
            assert!(return_clause.is_none());
        }
        _ => panic!("expected HandlerDef, got {:?}", decls[0]),
    }
}

#[test]
fn handler_def_with_return_clause() {
    let decls = parse("handler to_result for Fail {\n  fail reason -> Err(reason)\n  return value -> Ok(value)\n}");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::HandlerDef { name, arms, return_clause, .. } => {
            assert_eq!(name, "to_result");
            assert_eq!(arms.len(), 1);
            assert_eq!(arms[0].op_name, "fail");
            assert!(return_clause.is_some());
            let rc = return_clause.as_ref().unwrap();
            assert_eq!(rc.params, vec!["value"]);
        }
        _ => panic!("expected HandlerDef, got {:?}", decls[0]),
    }
}

#[test]
fn handler_def_multi_effect() {
    let decls = parse("handler dev_env for Log, Http {\n  log level msg -> resume ()\n  get url -> resume \"ok\"\n}");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::HandlerDef { effects, arms, .. } => {
            assert_eq!(effects, &["Log", "Http"]);
            assert_eq!(arms.len(), 2);
        }
        _ => panic!("expected HandlerDef, got {:?}", decls[0]),
    }
}

#[test]
fn handler_def_with_needs() {
    let decls = parse("handler stripe for Billing needs {Log, Http} {\n  charge account amount -> resume (fake_receipt ())\n}");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::HandlerDef { name, effects, needs, arms, .. } => {
            assert_eq!(name, "stripe");
            assert_eq!(effects, &["Billing"]);
            assert_eq!(needs, &["Log", "Http"]);
            assert_eq!(arms.len(), 1);
            assert_eq!(arms[0].op_name, "charge");
        }
        _ => panic!("expected HandlerDef, got {:?}", decls[0]),
    }
}

#[test]
fn handler_def_without_needs() {
    let decls = parse("handler mock for Billing {\n  charge account amount -> resume (fake_receipt ())\n}");
    match &decls[0] {
        Decl::HandlerDef { needs, .. } => {
            assert!(needs.is_empty());
        }
        _ => panic!("expected HandlerDef"),
    }
}

#[test]
fn handler_def_needs_trailing_comma() {
    let decls = parse("handler stripe for Billing needs {Log, Http,} {\n  charge a b -> resume ()\n}");
    match &decls[0] {
        Decl::HandlerDef { needs, .. } => {
            assert_eq!(needs, &["Log", "Http"]);
        }
        _ => panic!("expected HandlerDef"),
    }
}

// --- Effect call expressions ---

#[test]
fn effect_call_simple() {
    let expr = parse_expr("log! \"hello\"");
    match &expr {
        Expr::App { func, arg, .. } => {
            match func.as_ref() {
                Expr::EffectCall { name, qualifier, .. } => {
                    assert_eq!(name, "log");
                    assert!(qualifier.is_none());
                }
                _ => panic!("expected EffectCall, got {:?}", func),
            }
            assert!(matches!(arg.as_ref(), Expr::Lit { value: Lit::String(s), .. } if s == "hello"));
        }
        _ => panic!("expected App(EffectCall, _), got {:?}", expr),
    }
}

#[test]
fn effect_call_no_args() {
    let expr = parse_expr("read_line!");
    match &expr {
        Expr::EffectCall { name, qualifier, .. } => {
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
        Expr::App { func, .. } => match func.as_ref() {
            Expr::EffectCall { name, qualifier, .. } => {
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
        Expr::Resume { value, .. } => {
            assert!(matches!(value.as_ref(), Expr::Lit { value: Lit::Unit, .. }));
        }
        _ => panic!("expected Resume, got {:?}", expr),
    }
}

#[test]
fn resume_with_value() {
    let expr = parse_expr("resume answer");
    match &expr {
        Expr::Resume { value, .. } => {
            assert!(matches!(value.as_ref(), Expr::Var { name, .. } if name == "answer"));
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
        Expr::With { expr: inner, handler, .. } => {
            assert!(matches!(inner.as_ref(), Expr::App { .. }));
            assert!(matches!(handler.as_ref(), Handler::Named(n) if n == "console_log"));
        }
        _ => panic!("expected With, got {:?}", expr),
    }
}

#[test]
fn with_inline_handler() {
    let expr = parse_expr("run_server () with {\n  log level msg -> print! msg\n}");
    match &expr {
        Expr::With { handler, .. } => match handler.as_ref() {
            Handler::Inline { named, arms, return_clause } => {
                assert!(named.is_empty());
                assert_eq!(arms.len(), 1);
                assert_eq!(arms[0].op_name, "log");
                assert_eq!(arms[0].params, vec!["level", "msg"]);
                assert!(return_clause.is_none());
            }
            _ => panic!("expected Inline handler, got {:?}", handler),
        },
        _ => panic!("expected With, got {:?}", expr),
    }
}

#[test]
fn with_mixed_handlers() {
    let expr = parse_expr("run () with {\n  console_log,\n  get url -> resume \"ok\"\n}");
    match &expr {
        Expr::With { handler, .. } => match handler.as_ref() {
            Handler::Inline { named, arms, .. } => {
                assert_eq!(named, &["console_log"]);
                assert_eq!(arms.len(), 1);
                assert_eq!(arms[0].op_name, "get");
            }
            _ => panic!("expected Inline handler, got {:?}", handler),
        },
        _ => panic!("expected With, got {:?}", expr),
    }
}

// --- Where clause on annotations ---

#[test]
fn fun_annotation_with_where_clause() {
    let decls = parse("fun show (x: a) -> String where {a: Show}");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::FunAnnotation { where_clause, .. } => {
            assert_eq!(where_clause.len(), 1);
            assert_eq!(where_clause[0].type_var, "a");
            assert_eq!(where_clause[0].traits, vec!["Show"]);
        }
        _ => panic!("expected FunAnnotation, got {:?}", decls[0]),
    }
}

#[test]
fn fun_annotation_where_multiple_bounds() {
    let decls = parse("fun compare (x: a) (y: b) -> Int where {a: Show + Eq, b: Ord}");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::FunAnnotation { where_clause, .. } => {
            assert_eq!(where_clause.len(), 2);
            assert_eq!(where_clause[0].type_var, "a");
            assert_eq!(where_clause[0].traits, vec!["Show", "Eq"]);
            assert_eq!(where_clause[1].type_var, "b");
            assert_eq!(where_clause[1].traits, vec!["Ord"]);
        }
        _ => panic!("expected FunAnnotation, got {:?}", decls[0]),
    }
}

#[test]
fn fun_annotation_needs_and_where() {
    let decls = parse("fun f (x: a) -> Unit needs {Log} where {a: Show}");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::FunAnnotation { effects, where_clause, .. } => {
            assert_eq!(effects, &["Log"]);
            assert_eq!(where_clause.len(), 1);
            assert_eq!(where_clause[0].type_var, "a");
        }
        _ => panic!("expected FunAnnotation, got {:?}", decls[0]),
    }
}

// --- Trait definitions ---

#[test]
fn trait_def_simple() {
    let decls = parse("trait Show a {\n  fun show (x: a) -> String\n}");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::TraitDef { name, type_param, supertraits, methods, .. } => {
            assert_eq!(name, "Show");
            assert_eq!(type_param, "a");
            assert!(supertraits.is_empty());
            assert_eq!(methods.len(), 1);
            assert_eq!(methods[0].name, "show");
            assert_eq!(methods[0].params.len(), 1);
        }
        _ => panic!("expected TraitDef, got {:?}", decls[0]),
    }
}

#[test]
fn trait_def_with_supertraits() {
    let decls = parse("trait Ord a where {a: Eq} {\n  fun compare (x: a) (y: a) -> Ordering\n}");
    assert_eq!(decls.len(), 1);
    match &decls[0] {
        Decl::TraitDef { name, type_param, supertraits, methods, .. } => {
            assert_eq!(name, "Ord");
            assert_eq!(type_param, "a");
            assert_eq!(supertraits, &["Eq"]);
            assert_eq!(methods.len(), 1);
            assert_eq!(methods[0].name, "compare");
            assert_eq!(methods[0].params.len(), 2);
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
        Decl::ImplDef { trait_name, target_type, methods, .. } => {
            assert_eq!(trait_name, "Show");
            assert_eq!(target_type, "User");
            assert_eq!(methods.len(), 1);
            assert_eq!(methods[0].0, "show");
            assert_eq!(methods[0].1.len(), 1);
        }
        _ => panic!("expected ImplDef, got {:?}", decls[0]),
    }
}

// --- Visibility (pub) ---

#[test]
fn pub_type_def() {
    let decls = parse("pub type Shape { Circle(Float) }");
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
    let decls = parse("type Shape { Circle(Float) }");
    match &decls[0] {
        Decl::TypeDef { public, .. } => {
            assert!(!public, "bare type should set public = false");
        }
        _ => panic!("expected TypeDef"),
    }
}

#[test]
fn pub_record_def() {
    let decls = parse("pub record User {\n  name: String\n}");
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
    let decls = parse("record User {\n  name: String\n}");
    match &decls[0] {
        Decl::RecordDef { public, .. } => {
            assert!(!public);
        }
        _ => panic!("expected RecordDef"),
    }
}

#[test]
fn pub_effect_def() {
    let decls = parse("pub effect Log {\n  fun log (msg: String) -> Unit\n}");
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
    let decls = parse("effect Log {\n  fun log (msg: String) -> Unit\n}");
    match &decls[0] {
        Decl::EffectDef { public, .. } => {
            assert!(!public);
        }
        _ => panic!("expected EffectDef"),
    }
}

#[test]
fn pub_handler_def() {
    let decls = parse("pub handler console_log for Log {\n  log msg -> resume ()\n}");
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
    let decls = parse("handler console_log for Log {\n  log msg -> resume ()\n}");
    match &decls[0] {
        Decl::HandlerDef { public, .. } => {
            assert!(!public);
        }
        _ => panic!("expected HandlerDef"),
    }
}

#[test]
fn pub_trait_def() {
    let decls = parse("pub trait Show a {\n  fun show (x: a) -> String\n}");
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
    let decls = parse("trait Show a {\n  fun show (x: a) -> String\n}");
    match &decls[0] {
        Decl::TraitDef { public, .. } => {
            assert!(!public);
        }
        _ => panic!("expected TraitDef"),
    }
}

#[test]
fn pub_fun_annotation() {
    let decls = parse("pub fun add (a: Int) (b: Int) -> Int");
    match &decls[0] {
        Decl::FunAnnotation { public, name, .. } => {
            assert!(public);
            assert_eq!(name, "add");
        }
        _ => panic!("expected FunAnnotation"),
    }
}

#[test]
fn private_fun_annotation() {
    let decls = parse("fun add (a: Int) (b: Int) -> Int");
    match &decls[0] {
        Decl::FunAnnotation { public, .. } => {
            assert!(!public);
        }
        _ => panic!("expected FunAnnotation"),
    }
}

// --- String interpolation ---

#[test]
fn interp_empty() {
    // $"" → ""
    let expr = parse_expr(r#"$"""#);
    assert!(matches!(expr, Expr::Lit { value: Lit::String(s), .. } if s.is_empty()));
}

#[test]
fn interp_no_holes() {
    // $"hello" → "hello"
    let expr = parse_expr(r#"$"hello""#);
    assert!(matches!(expr, Expr::Lit { value: Lit::String(s), .. } if s == "hello"));
}

#[test]
fn interp_single_hole() {
    // $"{x}" → show(x)
    let expr = parse_expr(r#"$"{x}""#);
    assert!(matches!(
        expr,
        Expr::App { func, arg, .. }
        if matches!(func.as_ref(), Expr::Var { name, .. } if name == "show")
        && matches!(arg.as_ref(), Expr::Var { name, .. } if name == "x")
    ));
}

#[test]
fn interp_literal_and_hole() {
    // $"hello {name}" → "hello " <> show(name)
    let expr = parse_expr(r#"$"hello {name}""#);
    assert!(matches!(
        expr,
        Expr::BinOp { op: BinOp::Concat, left, right, .. }
        if matches!(left.as_ref(), Expr::Lit { value: Lit::String(s), .. } if s == "hello ")
        && matches!(right.as_ref(), Expr::App { func, .. }
            if matches!(func.as_ref(), Expr::Var { name, .. } if name == "show"))
    ));
}

#[test]
fn interp_escaped_braces() {
    // $"\{" → "{"
    let expr = parse_expr("$\"\\{\"");
    assert!(matches!(expr, Expr::Lit { value: Lit::String(s), .. } if s == "{"));
}

#[test]
fn interp_pipe_in_hole() {
    // $"{xs |> show}" parses without error
    parse_expr(r#"$"{xs |> show}""#);
}
