use super::*;
use crate::lexer::Lexer;
use crate::parser::Parser;
use std::fs;
use std::path::Path;
use std::time::{SystemTime, UNIX_EPOCH};

fn check(src: &str) -> Result<Checker, Diagnostic> {
    let mut lexer = Lexer::new(src);
    let tokens = lexer.lex().expect("lex error");
    let mut parser = Parser::new(tokens);
    let mut program = parser.parse_program().expect("parse error");
    let imported = crate::derive::collect_imported_decls(&program, None);
    let derive_errors = crate::derive::expand_derives(&mut program, &imported);
    if let Some(first) = derive_errors.into_iter().next() {
        return Err(first);
    }
    crate::desugar::desugar_program(&mut program);
    let mut checker = Checker::new();
    // Load prelude (which imports Std first, then stdlib modules)
    let prelude_src = include_str!("../stdlib/prelude.saga");
    let prelude_tokens = Lexer::new(prelude_src).lex().expect("prelude lex error");
    let mut prelude_program = Parser::new(prelude_tokens)
        .parse_program()
        .expect("prelude parse error");
    crate::derive::expand_derives(&mut prelude_program, &crate::derive::ImportedDecls::empty());
    crate::desugar::desugar_program(&mut prelude_program);
    checker
        .check_program_inner(&mut prelude_program)
        .map_err(|e| e.into_iter().next().unwrap())?;
    checker
        .check_program_inner(&mut program)
        .map_err(|e| e.into_iter().next().unwrap())?;
    Ok(checker)
}

fn infer_expr_type(src: &str) -> Result<Type, Diagnostic> {
    // Wrap expression in a let binding so we can pull its type
    let wrapped = format!("let _result = {}", src);
    let checker = check(&wrapped)?;
    let scheme = checker.env.get("_result").expect("_result not in env");
    Ok(checker.sub.apply(&scheme.ty))
}

fn check_with_project_files(files: &[(&str, &str)], main_src: &str) -> Result<Checker, Diagnostic> {
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock before epoch")
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "saga-typechecker-{}-{}",
        std::process::id(),
        unique
    ));

    fn write_file(root: &Path, rel: &str, src: &str) {
        let path = root.join(rel);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).expect("create temp module dir");
        }
        fs::write(path, src).expect("write temp module");
    }

    fs::create_dir_all(&root).expect("create temp project root");
    for (rel, src) in files {
        write_file(&root, rel, src);
    }

    let result = (|| -> Result<Checker, Diagnostic> {
        let mut checker = Checker::with_project_root(root.clone());
        let module_map = crate::typechecker::scan_project_modules(&root).expect("scan modules");
        checker.set_module_map(module_map);

        let prelude_src = include_str!("../stdlib/prelude.saga");
        let prelude_tokens = Lexer::new(prelude_src).lex().expect("prelude lex error");
        let mut prelude_program = Parser::new(prelude_tokens)
            .parse_program()
            .expect("prelude parse error");
        crate::derive::expand_derives(&mut prelude_program, &crate::derive::ImportedDecls::empty());
        crate::desugar::desugar_program(&mut prelude_program);
        checker
            .check_program_inner(&mut prelude_program)
            .map_err(|e| e.into_iter().next().unwrap())?;

        let mut lexer = Lexer::new(main_src);
        let tokens = lexer.lex().expect("lex error");
        let mut parser = Parser::new(tokens);
        let mut program = parser.parse_program().expect("parse error");
        let imported = crate::derive::collect_imported_decls(&program, checker.module_map());
        let derive_errors = crate::derive::expand_derives(&mut program, &imported);
        if let Some(first) = derive_errors.into_iter().next() {
            return Err(first);
        }
        crate::desugar::desugar_program(&mut program);
        checker
            .check_program_inner(&mut program)
            .map_err(|e| e.into_iter().next().unwrap())?;
        Ok(checker)
    })();

    let _ = fs::remove_dir_all(&root);
    result
}

#[test]
fn literal_int() {
    let ty = infer_expr_type("42").unwrap();
    assert_eq!(ty, Type::int());
}

#[test]
fn literal_float() {
    let ty = infer_expr_type("3.14").unwrap();
    assert_eq!(ty, Type::float());
}

#[test]
fn literal_string() {
    let ty = infer_expr_type("\"hello\"").unwrap();
    assert_eq!(ty, Type::string());
}

#[test]
fn literal_bool() {
    let ty = infer_expr_type("True").unwrap();
    assert_eq!(ty, Type::bool());
}

#[test]
fn literal_unit() {
    let ty = infer_expr_type("()").unwrap();
    assert_eq!(ty, Type::unit());
}

#[test]
fn variable_lookup() {
    let checker = check("let x = 42\nlet y = x").unwrap();
    let ty = checker.sub.apply(&checker.env.get("y").unwrap().ty);
    assert_eq!(ty, Type::int());
}

#[test]
fn undefined_variable() {
    let result = check("let x = y");
    assert!(result.is_err());
}

#[test]
fn binary_add() {
    let ty = infer_expr_type("1 + 2").unwrap();
    assert_eq!(ty, Type::int());
}

#[test]
fn binary_comparison() {
    let ty = infer_expr_type("1 < 2").unwrap();
    assert_eq!(ty, Type::bool());
}

#[test]
fn binary_concat() {
    let ty = infer_expr_type("\"a\" <> \"b\"").unwrap();
    assert_eq!(ty, Type::string());
}

#[test]
fn if_expression() {
    let ty = infer_expr_type("if True then 1 else 2").unwrap();
    assert_eq!(ty, Type::int());
}

#[test]
fn if_branch_mismatch() {
    let result = infer_expr_type("if True then 1 else \"hello\"");
    assert!(result.is_err());
}

#[test]
fn function_identity() {
    let checker = check("id x = x").unwrap();
    let scheme = checker.env.get("id").unwrap();
    let ty = checker.sub.apply(&scheme.ty);
    // Should be ?a -> ?a (polymorphic)
    match ty {
        Type::Fun(a, b, _) => assert_eq!(a, b),
        _ => panic!("expected arrow type, got {}", ty),
    }
}

#[test]
fn function_application() {
    let checker = check("id x = x\nlet y = id 42").unwrap();
    let ty = checker.sub.apply(&checker.env.get("y").unwrap().ty);
    assert_eq!(ty, Type::int());
}

#[test]
fn type_mismatch_in_addition() {
    let result = infer_expr_type("1 + \"hello\"");
    assert!(result.is_err());
}

#[test]
fn lambda_simple() {
    let ty = infer_expr_type("fun x -> x + 1").unwrap();
    assert_eq!(ty, Type::arrow(Type::int(), Type::int()));
}

#[test]
fn block_returns_last() {
    let ty = infer_expr_type("{\n  let x = 1\n  x + 2\n}").unwrap();
    assert_eq!(ty, Type::int());
}

#[test]
fn constructor_type() {
    let checker = check("type Maybe a\n  = Just(a)\n  | Nothing\nlet x = Just 42").unwrap();
    let ty = checker.sub.apply(&checker.env.get("x").unwrap().ty);
    assert_eq!(ty, Type::Con("Maybe".into(), vec![Type::int()]));
}

#[test]
fn case_literal_patterns() {
    let ty = infer_expr_type("case 1 {\n  0 -> \"zero\"\n  _ -> \"other\"\n}").unwrap();
    assert_eq!(ty, Type::string());
}

#[test]
fn case_constructor_patterns() {
    let checker =
        check("type Maybe a\n  = Just(a)\n  | Nothing\nlet x = case Just 42 {\n  Just(n) -> n + 1\n  Nothing -> 0\n}")
            .unwrap();
    let ty = checker.sub.apply(&checker.env.get("x").unwrap().ty);
    assert_eq!(ty, Type::int());
}

#[test]
fn case_branch_type_mismatch() {
    let result = check(
        "type Maybe a\n  = Just(a)\n  | Nothing\nlet x = case Just 42 {\n  Just(n) -> n\n  Nothing -> \"nope\"\n}",
    );
    assert!(result.is_err());
}

#[test]
fn case_binds_pattern_vars() {
    let checker =
        check("type Maybe a\n  = Just(a)\n  | Nothing\nlet x = case Just \"hello\" {\n  Just(s) -> s <> \" world\"\n  Nothing -> \"default\"\n}")
            .unwrap();
    let ty = checker.sub.apply(&checker.env.get("x").unwrap().ty);
    assert_eq!(ty, Type::string());
}

#[test]
fn case_with_guard() {
    let ty =
        infer_expr_type("case 5 {\n  x when x > 0 -> \"positive\"\n  _ -> \"non-positive\"\n}")
            .unwrap();
    assert_eq!(ty, Type::string());
}

#[test]
fn case_pattern_vars_dont_leak() {
    let result = check(
        "type Maybe a\n  = Just(a)\n  | Nothing\nlet x = case Just 42 {\n  Just(n) -> n\n  Nothing -> n\n}",
    );
    assert!(result.is_err());
}

#[test]
fn constructor_no_args() {
    let checker = check("type Maybe a\n  = Just(a)\n  | Nothing\nlet x = Nothing").unwrap();
    let ty = checker.sub.apply(&checker.env.get("x").unwrap().ty);
    match ty {
        Type::Con(name, args) => {
            assert_eq!(name, "Maybe");
            assert_eq!(args.len(), 1);
            // The type param is unresolved -- it's a free variable
            assert!(matches!(args[0], Type::Var(_)));
        }
        _ => panic!("expected Con, got {}", ty),
    }
}

#[test]
fn recursive_function() {
    let checker = check("factorial n = if n == 0 then 1 else n * factorial (n - 1)").unwrap();
    let scheme = checker.env.get("factorial").unwrap();
    let ty = checker.sub.apply(&scheme.ty);
    assert_eq!(ty, Type::arrow(Type::int(), Type::int()));
}

#[test]
fn multi_clause_with_guards() {
    let checker = check("abs n when n < 0 = 0 - n\nabs n = n").unwrap();
    let scheme = checker.env.get("abs").unwrap();
    let ty = checker.sub.apply(&scheme.ty);
    assert_eq!(ty, Type::arrow(Type::int(), Type::int()));
}

#[test]
fn multi_clause_literal_patterns() {
    let checker = check("fib 0 = 0\nfib 1 = 1\nfib n = fib (n - 1) + fib (n - 2)").unwrap();
    let scheme = checker.env.get("fib").unwrap();
    let ty = checker.sub.apply(&scheme.ty);
    assert_eq!(ty, Type::arrow(Type::int(), Type::int()));
}

#[test]
fn mutual_recursion() {
    let checker = check("is_even n = if n == 0 then True else is_odd (n - 1)\nis_odd n = if n == 0 then False else is_even (n - 1)").unwrap();
    let even_ty = checker.sub.apply(&checker.env.get("is_even").unwrap().ty);
    assert_eq!(even_ty, Type::arrow(Type::int(), Type::bool()));
    let odd_ty = checker.sub.apply(&checker.env.get("is_odd").unwrap().ty);
    assert_eq!(odd_ty, Type::arrow(Type::int(), Type::bool()));
}

#[test]
fn list_cons_expression() {
    let checker = check("let xs = 1 :: 2 :: Nil").unwrap();
    let ty = checker.sub.apply(&checker.env.get("xs").unwrap().ty);
    assert_eq!(
        ty,
        Type::Con(
            crate::typechecker::canonicalize_type_name("List").into(),
            vec![Type::int()]
        )
    );
}

#[test]
fn record_create() {
    let checker = check("record Point { x: Int, y: Int }\nlet p = Point { x: 3, y: 4 }").unwrap();
    let ty = checker.sub.apply(&checker.env.get("p").unwrap().ty);
    assert_eq!(ty, Type::Con("Point".into(), vec![]));
}

#[test]
fn record_field_access() {
    let checker =
        check("record Point { x: Int, y: Int }\nlet p = Point { x: 3, y: 4 }\nlet a = p.x")
            .unwrap();
    let ty = checker.sub.apply(&checker.env.get("a").unwrap().ty);
    assert_eq!(ty, Type::int());
}

#[test]
fn record_field_type_mismatch() {
    let result = check("record Point { x: Int, y: Int }\nlet p = Point { x: \"bad\", y: 4 }");
    assert!(result.is_err());
}

#[test]
fn record_unknown_field() {
    let result = check("record Point { x: Int, y: Int }\nlet p = Point { x: 1, z: 2 }");
    assert!(result.is_err());
}

#[test]
fn record_update() {
    let checker = check(
        "record Point { x: Int, y: Int }\nlet p = Point { x: 3, y: 4 }\nlet q = { p | x: 10 }",
    )
    .unwrap();
    let ty = checker.sub.apply(&checker.env.get("q").unwrap().ty);
    assert_eq!(ty, Type::Con("Point".into(), vec![]));
}

#[test]
fn record_update_type_mismatch() {
    let result = check(
        "record Point { x: Int, y: Int }\nlet p = Point { x: 3, y: 4 }\nlet q = { p | x: \"bad\" }",
    );
    assert!(result.is_err());
}

#[test]
fn record_pattern() {
    let checker =
        check("record Point { x: Int, y: Int }\nget_x p = case p {\n  Point { x, y } -> x\n}")
            .unwrap();
    let ty = checker.sub.apply(&checker.env.get("get_x").unwrap().ty);
    assert_eq!(
        ty,
        Type::arrow(Type::Con("Point".into(), vec![]), Type::int())
    );
}

#[test]
fn record_pattern_with_alias() {
    let checker = check(
        "record User { name: String, age: Int }\nget_name u = case u {\n  User { name: n, age } -> n\n}",
    )
    .unwrap();
    let ty = checker.sub.apply(&checker.env.get("get_name").unwrap().ty);
    assert_eq!(
        ty,
        Type::arrow(Type::Con("User".into(), vec![]), Type::string())
    );
}

#[test]
fn polymorphic_record_create() {
    let checker = check("record Box a { value: a }\nlet b = Box { value: 42 }").unwrap();
    let ty = checker.sub.apply(&checker.env.get("b").unwrap().ty);
    assert_eq!(ty, Type::Con("Box".into(), vec![Type::int()]));
}

#[test]
fn polymorphic_record_field_access() {
    let checker =
        check("record Box a { value: a }\nlet b = Box { value: 42 }\nlet v = b.value").unwrap();
    let ty = checker.sub.apply(&checker.env.get("v").unwrap().ty);
    assert_eq!(ty, Type::int());
}

#[test]
fn polymorphic_record_different_instantiations() {
    let checker = check(
        "record Box a { value: a }\nlet b1 = Box { value: 42 }\nlet b2 = Box { value: \"hello\" }",
    )
    .unwrap();
    let ty1 = checker.sub.apply(&checker.env.get("b1").unwrap().ty);
    let ty2 = checker.sub.apply(&checker.env.get("b2").unwrap().ty);
    assert_eq!(ty1, Type::Con("Box".into(), vec![Type::int()]));
    assert_eq!(ty2, Type::Con("Box".into(), vec![Type::string()]));
}

#[test]
fn polymorphic_record_update() {
    let checker =
        check("record Box a { value: a }\nlet b = Box { value: 42 }\nlet b2 = { b | value: 99 }")
            .unwrap();
    let ty = checker.sub.apply(&checker.env.get("b2").unwrap().ty);
    assert_eq!(ty, Type::Con("Box".into(), vec![Type::int()]));
}

#[test]
fn polymorphic_record_pattern() {
    let checker =
        check("record Box a { value: a }\nunwrap b = case b {\n  Box { value: v } -> v\n}")
            .unwrap();
    let scheme = checker.env.get("unwrap").unwrap();
    // unwrap : Box a -> a (polymorphic)
    let ty = checker.sub.apply(&scheme.ty);
    match &ty {
        Type::Fun(arg, ret, _) => {
            match arg.as_ref() {
                Type::Con(name, params) => {
                    assert_eq!(name, "Box");
                    assert_eq!(params.len(), 1);
                    // The param and return type should be the same variable
                    assert_eq!(params[0], **ret);
                }
                _ => panic!("expected Box type, got {:?}", arg),
            }
        }
        _ => panic!("expected arrow type, got {:?}", ty),
    }
}

#[test]
fn polymorphic_record_two_params() {
    let checker =
        check("record Pair a b { fst: a, snd: b }\nlet p = Pair { fst: 1, snd: \"hi\" }").unwrap();
    let ty = checker.sub.apply(&checker.env.get("p").unwrap().ty);
    assert_eq!(
        ty,
        Type::Con("Pair".into(), vec![Type::int(), Type::string()])
    );
}

#[test]
fn polymorphic_record_field_access_infers_param() {
    let checker = check(
        "record Box a { value: a }\nget_value b = b.value\nlet x = get_value (Box { value: 42 })",
    )
    .unwrap();
    let ty = checker.sub.apply(&checker.env.get("x").unwrap().ty);
    assert_eq!(ty, Type::int());
}

#[test]
fn polymorphic_record_constructor_as_function() {
    // Record constructor should be usable as a function: Box : a -> Box a
    let checker = check("record Box a { value: a }\nlet b = Box { value: 42 }").unwrap();
    let scheme = checker.constructors.get("Box").unwrap();
    assert_eq!(scheme.forall.len(), 1);
}

#[test]
fn annotation_correct() {
    let checker =
        check("fun fib : (n: Int) -> Int\nfib 0 = 0\nfib 1 = 1\nfib n = fib (n - 1) + fib (n - 2)")
            .unwrap();
    let ty = checker.sub.apply(&checker.env.get("fib").unwrap().ty);
    assert_eq!(ty, Type::arrow(Type::int(), Type::int()));
}

#[test]
fn zero_arity_function_constant_typechecks() {
    let checker = check("pub fun answer : Int\nanswer = 5").unwrap();
    let ty = checker.sub.apply(&checker.env.get("answer").unwrap().ty);
    assert_eq!(ty, Type::int());
}

#[test]
fn annotation_mismatch() {
    let result = check("fun add : (a: Int) -> (b: Int) -> String\nadd a b = a + b");
    assert!(result.is_err());
}

#[test]
fn annotation_without_body() {
    let result = check("fun foo : (x: Int) -> Int");
    assert!(result.is_err());
}

#[test]
fn annotation_multi_param() {
    let checker = check("fun add : (a: Int) -> (b: Int) -> Int\nadd a b = a + b").unwrap();
    let ty = checker.sub.apply(&checker.env.get("add").unwrap().ty);
    assert_eq!(
        ty,
        Type::arrow(Type::int(), Type::arrow(Type::int(), Type::int()))
    );
}

#[test]
fn annotation_constrains_polymorphism() {
    // id without annotation is polymorphic; with annotation it's constrained to Int -> Int
    let checker = check("fun myid : (x: Int) -> Int\nmyid x = x").unwrap();
    let ty = checker.sub.apply(&checker.env.get("myid").unwrap().ty);
    assert_eq!(ty, Type::arrow(Type::int(), Type::int()));
}

#[test]
fn annotation_polymorphic() {
    // fun id : (x: a) -> a should work with the polymorphic identity
    let checker = check("fun id : (x: a) -> a\nid x = x").unwrap();
    let scheme = checker.env.get("id").unwrap();
    let ty = checker.sub.apply(&scheme.ty);
    match ty {
        Type::Fun(a, b, _) => assert_eq!(a, b),
        _ => panic!("expected arrow, got {}", ty),
    }
}

#[test]
fn pipe_operator() {
    let checker = check("let x = 42 |> show").unwrap();
    let ty = checker.sub.apply(&checker.env.get("x").unwrap().ty);
    assert_eq!(ty, Type::string());
}

// --- Effect needs tracking ---

/// All effect names appearing on any arrow of a checked function's inferred
/// type. Lets effect-inference assertions ignore which arrow the row landed on
/// (e.g. effects on a returned function vs the function's own arrow).
fn fun_effects(checker: &Checker, name: &str) -> Vec<String> {
    fn walk(ty: &Type, out: &mut std::collections::HashSet<String>) {
        if let Type::Fun(_, ret, row) = ty {
            for e in &row.effects {
                out.insert(e.name.clone());
            }
            walk(ret, out);
        }
    }
    let scheme = checker.env.get(name).expect("function not in env");
    let ty = checker.sub.apply(&scheme.ty);
    let mut set = std::collections::HashSet::new();
    walk(&ty, &mut set);
    let mut v: Vec<String> = set.into_iter().collect();
    v.sort();
    v
}

#[test]
fn effect_call_without_needs_infers_for_local() {
    // A local (unannotated) function that performs an effect now INFERS its
    // effect row instead of erroring -- `needs` is only required on `pub`
    // functions (which carry an annotation).
    let c = check("effect Fail {\n  fun fail : (msg: String) -> a\n}\nfoo x = fail! \"oops\"")
        .expect("unannotated effectful local should check");
    assert!(
        fun_effects(&c, "foo").iter().any(|e| e.contains("Fail")),
        "foo should infer {{Fail}}, got: {:?}",
        fun_effects(&c, "foo")
    );
}

#[test]
fn effect_call_with_correct_needs() {
    check(
        "effect Fail {\n  fun fail : (msg: String) -> a\n}\nfun foo : (x: Int) -> Int needs {Fail}\nfoo x = fail! \"oops\"",
    )
    .unwrap();
}

#[test]
fn effect_call_with_wrong_needs() {
    let result = check(
        "effect Fail {\n  fun fail : (msg: String) -> a\n}\neffect Log {\n  fun log : (msg: String) -> Unit\n}\nfun foo : (x: Int) -> Int needs {Log}\nfoo x = fail! \"oops\"",
    );
    assert!(result.is_err());
    let err = result.err().expect("expected error");
    assert!(
        err.message.contains("Fail"),
        "expected Fail in error, got: {}",
        err.message
    );
}

#[test]
fn effect_handled_with_named_handler() {
    // Effect is handled inline, so the enclosing function doesn't need it
    check(
        "effect Fail {\n  fun fail : (msg: String) -> a\n}\nhandler catch_fail for Fail {\n  fail msg = 0\n}\nmain x = (fail! \"oops\") with catch_fail",
    )
    .unwrap();
}

#[test]
fn effect_handled_with_inline_handler() {
    check(
        "effect Fail {\n  fun fail : (msg: String) -> a\n}\nmain x = (fail! \"oops\") with {\n  fail msg = 0\n}",
    )
    .unwrap();
}

#[test]
fn effect_propagates_through_function_call() {
    // An unannotated caller of a `needs {Fail}` function INFERS and propagates
    // {Fail} without needing its own declaration.
    let c = check(
        "effect Fail {\n  fun fail : (msg: String) -> a\n}\nfun bar : (x: Int) -> Int needs {Fail}\nbar x = fail! \"oops\"\nfoo x = bar x",
    )
    .expect("unannotated caller should infer the propagated effect");
    assert!(
        fun_effects(&c, "foo").iter().any(|e| e.contains("Fail")),
        "foo should infer propagated {{Fail}}, got: {:?}",
        fun_effects(&c, "foo")
    );
}

#[test]
fn effect_propagation_with_needs_declared() {
    check(
        "effect Fail {\n  fun fail : (msg: String) -> a\n}\nfun bar : (x: Int) -> Int needs {Fail}\nbar x = fail! \"oops\"\nfun foo : (x: Int) -> Int needs {Fail}\nfoo x = bar x",
    )
    .unwrap();
}

#[test]
fn effect_propagation_handled_by_caller() {
    // Caller handles the effect, so doesn't need to declare it
    check(
        "effect Fail {\n  fun fail : (msg: String) -> a\n}\nfun bar : (x: Int) -> Int needs {Fail}\nbar x = fail! \"oops\"\nfoo x = (bar x) with {\n  fail msg = 0\n}",
    )
    .unwrap();
}

#[test]
fn handler_arm_body_effect_from_sibling_is_unhandled_under_nested_semantics() {
    // Under nested handler semantics, `with {silent, fail msg = { log! ... }}`
    // desugars to `(expr with silent) with { fail msg = ... }`.
    // The `fail` arm body uses `log!`, but `silent` only wraps the inner
    // expression, not the outer arm body. So `log!` is unhandled.
    let result = check(
        "effect Log {\n  fun log : (msg: String) -> Unit\n}\n\
         effect Fail {\n  fun fail : (msg: String) -> a\n}\n\
         handler silent for Log {\n  log msg = resume ()\n}\n\
         fun risky : Unit -> Int needs {Fail, Log}\n\
         risky () = fail! \"oops\"\n\
         main () = risky () with {\n  silent,\n  fail msg = {\n    log! (\"caught: \" <> msg)\n    0\n  }\n}",
    );
    assert!(result.is_err(), "expected unhandled Log error");
}

#[test]
fn inline_handler_arm_effect_from_sibling_is_unhandled_under_nested_semantics() {
    // `console` is now an inner handler; the `fail` arm body's `println` is unhandled.
    let result = check(
        "type AppError = HttpError String\n\
         effect Fail a {\n  fun fail : a -> b\n}\n\
         fun run_app : Unit -> Unit needs {Fail AppError}\n\
         run_app () = fail! (HttpError \"oops\")\n\
         main () = {\n\
           run_app ()\n\
         } with {\n\
           console,\n\
           fail err = case err {\n\
             HttpError e -> println (\"HTTP: \" <> e)\n\
           }\n\
         }",
    );
    assert!(result.is_err(), "expected unhandled Stdio error");
}

#[test]
fn inline_handler_return_clause_effect_from_sibling_is_unhandled_under_nested_semantics() {
    // `console` is now an inner handler; the `return` clause's `println` is unhandled.
    let result = check(
        "effect Fail {\n  fun fail : String -> a\n}\n\
         fun run_app : Unit -> String needs {Fail}\n\
         run_app () = \"ok\"\n\
         main () = {\n\
           run_app ()\n\
         } with {\n\
           console,\n\
           fail _ = \"bad\",\n\
           return value = {\n\
             println value\n\
             value\n\
           }\n\
         }",
    );
    assert!(result.is_err(), "expected unhandled Stdio error");
}

#[test]
fn inline_handler_finally_effect_can_be_handled_by_outer_scope_under_nested_semantics() {
    check(
        "effect Log {\n  fun log : (msg: String) -> Unit\n}\n\
         effect Fail {\n  fun fail : (msg: String) -> a\n}\n\
         handler silent for Log {\n  log _ = resume ()\n}\n\
         fun risky : Unit -> Int needs {Fail}\n\
         risky () = fail! \"oops\"\n\
         main () = {\n\
           risky () with {\n\
             fail msg = 0 finally {\n\
               log! \"cleanup\"\n\
             }\n\
           }\n\
         } with silent",
    )
    .unwrap();
}

#[test]
fn handler_arm_body_unhandled_effect_propagates() {
    // An inline handler arm body uses Log, not handled by the `with`. The
    // enclosing unannotated function INFERS {Log} (propagated from the arm body).
    let c = check(
        "effect Log {\n  fun log : (msg: String) -> Unit\n}\n\
         effect Fail {\n  fun fail : (msg: String) -> a\n}\n\
         fun risky : Unit -> Int needs {Fail}\n\
         risky () = fail! \"oops\"\n\
         foo () = risky () with {\n  fail msg = {\n    log! \"caught\"\n    0\n  }\n}",
    )
    .expect("unannotated foo should infer the unhandled arm-body effect");
    assert!(
        fun_effects(&c, "foo").iter().any(|e| e.contains("Log")),
        "foo should infer {{Log}} from the arm body, got: {:?}",
        fun_effects(&c, "foo")
    );
}

#[test]
fn lambda_effects_ride_on_returned_function_type() {
    // `foo x = fun y -> fail! ...` RETURNS an effectful function. The effect
    // rides on the returned arrow (calling `foo` itself performs nothing), so
    // the unannotated foo checks and its type carries {Fail}.
    let c =
        check("effect Fail {\n  fun fail : (msg: String) -> a\n}\nfoo x = fun y -> fail! \"oops\"")
            .expect("function returning an effectful lambda should check");
    assert!(
        fun_effects(&c, "foo").iter().any(|e| e.contains("Fail")),
        "foo's type should carry {{Fail}} on the returned arrow, got: {:?}",
        fun_effects(&c, "foo")
    );
}

#[test]
fn lambda_effects_covered_by_enclosing_needs() {
    // Lambda effects are fine when the enclosing function declares them
    check(
        "effect Fail {\n  fun fail : (msg: String) -> a\n}\nfun foo : (x: Int) -> Int needs {Fail}\nfoo x = (fun y -> fail! \"oops\") x",
    )
    .unwrap();
}

#[test]
fn lambda_effects_absorbed_by_hof_annotation() {
    // HOF parameter annotated with `needs {Fail}` absorbs the effect from the lambda
    check(
        "effect Fail {\n  fun fail : (msg: String) -> a\n}\nfun run : (f: Unit -> Int needs {Fail}) -> Int\nrun f = f () with { fail msg = 0 }\nfoo x = run (fun () -> fail! \"oops\")",
    )
    .unwrap();
}

#[test]
fn tuple_pattern_lambda_argument_uses_expected_callback_type_for_fields() {
    check(
        "record WindDetails { wind_avg: Int, wind_gust: Int }\n\
         record Normalized { wind_avg: Maybe Int, wind_gust: Maybe Int }\n\
         fun map_rows : (rows: List a) -> (f: a -> b) -> List b\n\
         map_rows rows f = List.map f rows\n\
         rows = [(1, WindDetails { wind_avg: 10, wind_gust: 20 })]\n\
         main () = map_rows rows (fun (sesh_id, wd) -> wd.wind_avg + sesh_id)",
    )
    .unwrap();
}

#[test]
fn first_argument_lambda_can_use_later_argument_constraints_for_tuple_pattern() {
    check(
        "record WindDetails { wind_avg: Int, wind_gust: Int }\n\
         record Normalized { wind_avg: Maybe Int, wind_gust: Maybe Int }\n\
         rows = [(1, WindDetails { wind_avg: 10, wind_gust: 20 })]\n\
         main () = List.filter_map (fun pair -> case pair {\n\
           (sesh_id, wd) -> Just (wd.wind_avg + sesh_id)\n\
         }) rows",
    )
    .unwrap();
}

#[test]
fn annotated_eta_reduced_hof_can_constrain_first_argument_lambda() {
    check(
        "record WindDetails { wind_avg: Int, wind_gust: Int }\n\
         record Normalized { wind_avg: Maybe Int, wind_gust: Maybe Int }\n\
         fun wind_rows : List (Int, WindDetails) -> List Int\n\
         wind_rows = List.filter_map (fun pair -> case pair {\n\
           (sesh_id, wd) -> Just (wd.wind_avg + sesh_id)\n\
         })",
    )
    .unwrap();
}

#[test]
fn named_binder_lambda_argument_still_typechecks() {
    check(
        "record Row { sesh_id: Int, wind_avg: Int }\n\
         fun push_values : (rows: List a) -> (bind_row: a -> List Int) -> List Int\n\
         push_values rows bind_row = List.flat_map bind_row rows\n\
         rows = [Row { sesh_id: 1, wind_avg: 10 }]\n\
         main () = push_values rows (fun row -> [row.sesh_id, row.wind_avg])",
    )
    .unwrap();
}

#[test]
fn non_lambda_callback_argument_still_needs_annotation_for_ambiguous_fields() {
    let result = check(
        "record WindDetails { wind_avg: Int }\n\
         record Normalized { wind_avg: Maybe Int }\n\
         bind_row pair = case pair {\n\
           (_, wd) -> wd.wind_avg\n\
         }\n\
         rows = [(1, WindDetails { wind_avg: 10 })]\n\
         main () = List.map bind_row rows",
    );
    assert!(result.is_err(), "expected ambiguous field error");
    let err = result.err().unwrap();
    assert!(
        err.message.contains("ambiguous field") && err.message.contains("wind_avg"),
        "got: {}",
        err.message
    );
}

#[test]
fn multiple_effects_needs_all() {
    let result = check(
        "effect Fail {\n  fun fail : (msg: String) -> a\n}\neffect Log {\n  fun log : (msg: String) -> Unit\n}\nfun foo : (x: Int) -> Int needs {Fail}\nfoo x = {\n  log! \"hello\"\n  fail! \"oops\"\n}",
    );
    assert!(result.is_err());
    let err = result.err().expect("expected error");
    assert!(
        err.message.contains("Log"),
        "expected Log in error, got: {}",
        err.message
    );
}

#[test]
fn multiple_effects_all_declared() {
    check(
        "effect Fail {\n  fun fail : (msg: String) -> a\n}\neffect Log {\n  fun log : (msg: String) -> Unit\n}\nfun foo : (x: Int) -> Unit needs {Fail, Log}\nfoo x = {\n  log! \"hello\"\n  fail! \"oops\"\n}",
    )
    .unwrap();
}

#[test]
fn with_subtracts_only_handled_effect() {
    // `with console` handles Log but not Fail. The unannotated foo INFERS the
    // remaining {Fail} and NOT {Log} (subtracted by the handler).
    let c = check(
        "effect Fail {\n  fun fail : (msg: String) -> a\n}\neffect Log {\n  fun log : (msg: String) -> Unit\n}\nhandler console for Log {\n  log msg = { dbg msg; resume () }\n}\nfoo x = {\n  log! \"hello\"\n  fail! \"oops\"\n} with console",
    )
    .expect("unannotated foo should infer the unhandled remainder");
    let effs = fun_effects(&c, "foo");
    assert!(
        effs.iter().any(|e| e.contains("Fail")),
        "foo should infer remaining {{Fail}}, got: {:?}",
        effs
    );
    assert!(
        !effs.iter().any(|e| e.contains("Log")),
        "Log should be subtracted by `with console`, got: {:?}",
        effs
    );
}

#[test]
fn pure_function_no_needs_ok() {
    // Pure functions without effects don't need any annotation
    check("add a b = a + b").unwrap();
}

// --- Traits ---

#[test]
fn trait_method_in_env() {
    let checker = check("trait Greet a {\n  fun greet : (x: a) -> String\n}").unwrap();
    let scheme = checker.env.get("Greet.greet").unwrap();
    let ty = checker.sub.apply(&scheme.ty);
    match ty {
        Type::Fun(_, ret, _) => assert_eq!(*ret, Type::string()),
        _ => panic!("expected arrow, got {}", ty),
    }
}

#[test]
fn impl_missing_method() {
    let result = check(
        "record User { name: String }\ntrait Greet a {\n  fun greet : (x: a) -> String\n}\nimpl Greet for User {\n}",
    );
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message.contains("missing method"),
        "got: {}",
        err.message
    );
}

#[test]
fn impl_extra_method() {
    let result = check(
        "record User { name: String }\ntrait Greet a {\n  fun greet : (x: a) -> String\n}\nimpl Greet for User {\n  greet u = u.name\n  bogus u = u.name\n}",
    );
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message.contains("not defined in trait"),
        "got: {}",
        err.message
    );
}

#[test]
fn impl_method_with_too_many_params_is_arity_error_not_undefined_var() {
    // `greet : a -> String` declares one parameter; binding two must report a
    // clear arity error. Regression: the surplus param `extra` used to be
    // silently dropped, so its use in the body leaked as "undefined variable".
    let result = check(
        "record User { name: String }\ntrait Greet a {\n  fun greet : (x: a) -> String\n}\nimpl Greet for User {\n  greet u extra = extra\n}",
    );
    let err = result.err().expect("expected an error");
    assert!(
        err.message.contains("binds 2 parameter")
            && !err.message.contains("undefined variable"),
        "got: {}",
        err.message
    );
}

#[test]
fn impl_wrong_return_type() {
    let result = check(
        "record User { name: String }\ntrait Greet a {\n  fun greet : (x: a) -> String\n}\nimpl Greet for User {\n  greet u = 42\n}",
    );
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message.contains("type mismatch"),
        "got: {}",
        err.message
    );
}

#[test]
fn impl_correct() {
    check(
        "record User { name: String }\ntrait Greet a {\n  fun greet : (x: a) -> String\n}\nimpl Greet for User {\n  greet u = u.name\n}",
    )
    .unwrap();
}

#[test]
fn impl_pure_no_needs_ok() {
    // Impl with no effects needs no 'needs' clause
    check(
        "record InMemory { store: String }
trait Store a {
  fun get : (x: a) -> String
}
impl Store for InMemory {
  get s = s.store
}",
    )
    .unwrap();
}

#[test]
fn impl_uses_effect_without_needs_is_error() {
    // Impl method uses an effect but the impl has no 'needs' declaration
    let result = check(
        "effect Fail { fun fail : (msg: String) -> a }
record Redis { url: String }
trait Store a {
  fun get : (x: a) -> String
}
impl Store for Redis {
  get s = fail! \"oops\"
}",
    );
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message.contains("Fail"),
        "expected Fail in error, got: {}",
        err.message
    );
}

#[test]
fn impl_uses_effect_with_correct_needs_ok() {
    // Impl method uses an effect and declares it in 'needs'
    check(
        "effect Fail { fun fail : (msg: String) -> a }
record Redis { url: String }
trait Store a {
  fun get : (x: a) -> String needs {..e}
}
impl Store for Redis needs {Fail} {
  get s = fail! \"oops\"
}",
    )
    .unwrap();
}

// --- Trait-effect propagation (bugfix) ---
//
// An effectful impl's effects must reach the caller of a concrete trait-method
// dispatch. Previously they were checked against the method body locally and
// silently dropped at call sites. See docs/planning/effect-polymorphic-traits.md.

#[test]
fn concrete_trait_method_call_propagates_impl_effect() {
    // `foo 42` selects the `Foo Int` impl, which needs Config. `call_it`
    // declares no needs and provides no handler -> error.
    let result = check(
        "effect Config { fun config : Unit -> String }
trait Foo a { fun foo : a -> Int needs {..e} }
impl Foo for Int needs {Config} {
  foo thing = if config! () == \"x\" then thing else thing
}
fun call_it : Unit -> Int
call_it () = foo 42",
    );
    assert!(result.is_err(), "expected Config to propagate to call_it");
    assert!(
        result.err().unwrap().message.contains("Config"),
        "expected Config in the error"
    );
}

#[test]
fn concrete_trait_method_call_with_needs_ok() {
    check(
        "effect Config { fun config : Unit -> String }
trait Foo a { fun foo : a -> Int needs {..e} }
impl Foo for Int needs {Config} {
  foo thing = if config! () == \"x\" then thing else thing
}
fun call_it : Unit -> Int needs {Config}
call_it () = foo 42",
    )
    .unwrap();
}

#[test]
fn pure_sibling_method_of_effectful_impl_stays_pure() {
    // Per-method precision: calling the PURE method of an impl that has a
    // separate effectful method must NOT require the effect.
    check(
        "effect Config { fun config : Unit -> String }
trait Foo a {
  fun eff : a -> Int needs {..e}
  fun pure_m : a -> Int
}
impl Foo for Int needs {Config} {
  eff thing = if config! () == \"x\" then thing else thing
  pure_m thing = thing + 1
}
fun call_pure : Unit -> Int
call_pure () = pure_m 42",
    )
    .unwrap();
}

#[test]
fn effectful_sibling_method_still_propagates() {
    // The effectful method of the same impl still propagates.
    let result = check(
        "effect Config { fun config : Unit -> String }
trait Foo a {
  fun eff : a -> Int needs {..e}
  fun pure_m : a -> Int
}
impl Foo for Int needs {Config} {
  eff thing = if config! () == \"x\" then thing else thing
  pure_m thing = thing + 1
}
fun call_eff : Unit -> Int
call_eff () = eff 42",
    );
    assert!(result.is_err(), "expected Config to propagate via eff");
    assert!(result.err().unwrap().message.contains("Config"));
}

#[test]
fn pure_trait_method_with_effectful_impl_is_bounding_error() {
    // A pure trait method does not permit any impl effects: an effectful impl
    // (even one that declares `needs {Config}`) is a bounding error, because
    // the effect-capability is not opted into on the trait method.
    let result = check(
        "effect Config { fun config : Unit -> String }
trait Foo a { fun foo : a -> Int }
impl Foo for Int needs {Config} {
  foo thing = if config! () == \"x\" then thing else thing
}",
    );
    assert!(
        result.is_err(),
        "expected a bounding error for effectful impl of a pure trait method"
    );
    let err = result.err().unwrap();
    assert!(
        err.message.contains("does not permit"),
        "expected a bounding error, got: {}",
        err.message
    );
}

#[test]
fn pure_impl_emits_nothing() {
    // Guard against over-emission: a fully pure impl invents no effects.
    check(
        "trait Foo a { fun foo : a -> Int }
impl Foo for Int { foo thing = thing + 1 }
fun call_it : Unit -> Int
call_it () = foo 42",
    )
    .unwrap();
}

#[test]
fn where_bound_call_at_concrete_type_propagates_impl_effect() {
    // A where-bound generic carries the `Foo` constraint; calling it at a
    // concrete `Int` resolves the constraint to the effectful impl, so the
    // obligation propagates to the concrete caller.
    let result = check(
        "effect Config { fun config : Unit -> String }
trait Foo a { fun foo : a -> Int needs {..e} }
impl Foo for Int needs {Config} {
  foo thing = if config! () == \"x\" then thing else thing
}
fun count_foos : a -> Int needs {..a} where {a: Foo}
count_foos x = foo x + 2
fun use_it : Unit -> Int
use_it () = count_foos 42",
    );
    assert!(
        result.is_err(),
        "expected Config to propagate through the where-bound call"
    );
    assert!(result.err().unwrap().message.contains("Config"));
}

#[test]
fn concrete_trait_effect_handled_by_with_is_ok() {
    // Handling the propagated effect with a `with` satisfies the obligation
    // (and the handler is not flagged unnecessary).
    check(
        "effect Config { fun config : Unit -> String }
trait Foo a { fun foo : a -> Int needs {..e} }
impl Foo for Int needs {Config} {
  foo thing = if config! () == \"x\" then thing else thing
}
fun call_it : Unit -> Int
call_it () = foo 42 with { config () = resume \"x\" }",
    )
    .unwrap();
}

#[test]
fn closed_named_trait_effect_handled_in_wrapper_does_not_leak_at_concrete_call() {
    // Regression for a concrete-discharge over-emission. A CLOSED-NAMED
    // effectful trait method carries its effect in the type, so a generic
    // wrapper that handles it internally with `with` is genuinely pure.
    // Calling that wrapper at a concrete type must NOT resurrect the handled
    // effect via concrete discharge. Mirrors saga_json's
    // `serialize x = serialize_with x with json_defaults` leaking JsonOptions
    // into pure callers.
    check(
        "effect Config { fun config : Unit -> String }
trait Foo a { fun foo : a -> Int needs {Config} }
impl Foo for Int needs {Config} {
  foo thing = if config! () == \"x\" then thing else thing
}
fun wrap : a -> Int where {a: Foo}
wrap x = foo x with { config () = resume \"x\" }
fun use_it : Unit -> Int
use_it () = wrap 42",
    )
    .unwrap();
}

#[test]
fn closed_named_trait_effect_still_propagates_via_type_when_unhandled() {
    // Complement to the no-leak test: closed-named effects must still propagate
    // through the normal type row. A wrapper that does NOT handle the effect is
    // effectful and a pure caller must be rejected. Guards against
    // over-correcting the no-leak fix into dropping closed-named propagation.
    let result = check(
        "effect Config { fun config : Unit -> String }
trait Foo a { fun foo : a -> Int needs {Config} }
impl Foo for Int needs {Config} {
  foo thing = if config! () == \"x\" then thing else thing
}
fun wrap : a -> Int where {a: Foo}
wrap x = foo x
fun use_it : Unit -> Int
use_it () = wrap 42",
    );
    assert!(
        result.is_err(),
        "expected the unhandled Config effect to propagate to the pure caller"
    );
    assert!(result.err().unwrap().message.contains("Config"));
}

// --- Open-row generic surfacing + required forwarding (Phase B) ---
//
// When an open-row trait method is called on an abstract, where-bound type
// variable `a`, the constraint's effects must surface as `..a` and be forwarded
// in the function's `needs` clause, or it's an error. See
// docs/planning/effect-polymorphic-traits.md.

#[test]
fn open_row_generic_requires_forwarding() {
    // count_foos calls the open-row `foo` on abstract `a`; without `needs {..a}`
    // the surfaced row variable is unforwarded -> error.
    let result = check(
        "effect Config { fun config : Unit -> String }
trait Foo a { fun foo : a -> Int needs {..e} }
impl Foo for Int needs {Config} {
  foo thing = if config! () == \"x\" then thing else thing
}
fun count_foos : a -> Int where {a: Foo}
count_foos x = foo x + 2",
    );
    assert!(
        result.is_err(),
        "expected a missing-forward error for the open-row constraint"
    );
    let err = result.err().unwrap();
    assert!(
        err.message.contains("..a") && err.message.contains("Foo"),
        "expected an actionable `needs {{..a}}` diagnostic, got: {}",
        err.message
    );
}

#[test]
fn open_row_generic_with_forwarding_ok() {
    // Declaring `needs {..a}` forwards the constraint's effects -> ok.
    check(
        "effect Config { fun config : Unit -> String }
trait Foo a { fun foo : a -> Int needs {..e} }
impl Foo for Int needs {Config} {
  foo thing = if config! () == \"x\" then thing else thing
}
fun count_foos : a -> Int needs {..a} where {a: Foo}
count_foos x = foo x + 2",
    )
    .unwrap();
}

#[test]
fn show_bound_generic_needs_no_row_var() {
    // A generic over a pure trait method (Show) must NOT require `..a`: pure
    // trait methods never surface a forwarded row variable.
    check(
        "fun stringify : a -> String where {a: Show}
stringify x = show x",
    )
    .unwrap();
}

#[test]
fn closed_named_trait_method_generic_unaffected() {
    // A closed/named trait method's effects are part of its type and propagate
    // through the normal row, requiring the named effect (not `..a`).
    let result = check(
        "effect Config { fun config : Unit -> String }
trait Foo a { fun foo : a -> Int needs {Config} }
impl Foo for Int needs {Config} {
  foo thing = if config! () == \"x\" then thing else thing
}
fun count_foos : a -> Int where {a: Foo}
count_foos x = foo x + 2",
    );
    assert!(
        result.is_err(),
        "expected the named Config effect to be required"
    );
    assert!(result.err().unwrap().message.contains("Config"));
}

#[test]
fn closed_named_trait_method_generic_with_needs_ok() {
    check(
        "effect Config { fun config : Unit -> String }
trait Foo a { fun foo : a -> Int needs {Config} }
impl Foo for Int needs {Config} {
  foo thing = if config! () == \"x\" then thing else thing
}
fun count_foos : a -> Int needs {Config} where {a: Foo}
count_foos x = foo x + 2",
    )
    .unwrap();
}

#[test]
fn open_row_generic_with_wrapper_still_requires_forwarding() {
    // A `with` cannot handle an open row (you can't name its effects), so it
    // does not discharge the forwarding obligation: the function is still
    // effectful from the outside and must declare `needs {..a}`. The `with`
    // rebuilds the row and drops the abstract tail, so the check must be driven
    // off the recorded constraint var, not the body's residual tail.
    let result = check(
        "effect Config { fun config : Unit -> String }
trait Foo a { fun foo : a -> Int needs {..e} }
impl Foo for Int needs {Config} {
  foo thing = if config! () == \"x\" then thing else thing
}
fun handled : a -> Int where {a: Foo}
handled x = foo x with { config () = resume \"x\" }",
    );
    assert!(
        result.is_err(),
        "expected a `with` wrapper to still require `needs {{..a}}`"
    );
    let err = result.err().unwrap();
    assert!(
        err.message.contains("..a") && err.message.contains("Foo"),
        "expected an actionable `needs {{..a}}` diagnostic, got: {}",
        err.message
    );
}

#[test]
fn open_row_generic_with_wrapper_and_forwarding_ok() {
    // Declaring `needs {..a}` makes the `with`-wrapped form legal.
    check(
        "effect Config { fun config : Unit -> String }
trait Foo a { fun foo : a -> Int needs {..e} }
impl Foo for Int needs {Config} {
  foo thing = if config! () == \"x\" then thing else thing
}
fun handled : a -> Int needs {..a} where {a: Foo}
handled x = foo x with { config () = resume \"x\" }",
    )
    .unwrap();
}

#[test]
fn open_row_generic_pure_sibling_needs_no_forwarding() {
    // Per-method precision: a generic that calls only the PURE sibling of an
    // open-row method must not require forwarding.
    check(
        "effect Config { fun config : Unit -> String }
trait Foo a {
  fun eff : a -> Int needs {..e}
  fun pure_m : a -> Int
}
impl Foo for Int needs {Config} {
  eff thing = if config! () == \"x\" then thing else thing
  pure_m thing = thing + 1
}
fun count_pure : a -> Int where {a: Foo}
count_pure x = pure_m x + 2",
    )
    .unwrap();
}

#[test]
fn impl_needs_missing_one_effect_is_error() {
    // Impl method uses Fail and Log but only declares Fail in needs
    let result = check(
        "effect Fail { fun fail : (msg: String) -> a }
effect Log { fun log : (msg: String) -> Unit }
record Redis { url: String }
trait Store a {
  fun get : (x: a) -> String
}
impl Store for Redis needs {Fail} {
  get s = {
    log! \"hello\"
    fail! \"oops\"
  }
}",
    );
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message.contains("Log"),
        "expected Log in error, got: {}",
        err.message
    );
}

#[test]
fn impl_for_undefined_trait() {
    let result = check("record User { name: String }\nimpl Bogus for User {\n  foo u = u.name\n}");
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message.contains("undefined trait"),
        "got: {}",
        err.message
    );
}

#[test]
fn trait_constraint_no_impl() {
    // Calling a trait method on a type with no impl should fail
    let result = check(
        "record User { name: String }
trait Describe a {
  fun describe : (x: a) -> String
}
main () = describe (User { name: \"Alice\" })",
    );
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message.contains("no impl of Describe for User"),
        "got: {}",
        err.message
    );
}

#[test]
fn trait_constraint_with_impl_ok() {
    // Calling a trait method on a type with an impl should succeed
    check(
        "record User { name: String }
trait Describe a {
  fun describe : (x: a) -> String
}
impl Describe for User {
  describe u = u.name
}
main () = describe (User { name: \"Alice\" })",
    )
    .unwrap();
}

// --- Where clause tests ---

#[test]
fn where_clause_satisfies_constraint() {
    check(
        "trait Describe a {
  fun describe : (x: a) -> String
}
fun show_it : (x: a) -> String where {a: Describe}
show_it x = describe x",
    )
    .unwrap();
}

#[test]
fn where_clause_missing_bound_fails() {
    let result = check(
        "trait Describe a {
  fun describe : (x: a) -> String
}
fun show_it : (x: a) -> String
show_it x = describe x",
    );
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message
            .contains("trait Describe required but not declared in where clause"),
        "got: {}",
        err.message
    );
}

#[test]
fn where_clause_propagates_to_callers() {
    check(
        "record User { name: String }
trait Describe a {
  fun describe : (x: a) -> String
}
impl Describe for User {
  describe u = u.name
}
fun show_it : (x: a) -> String where {a: Describe}
show_it x = describe x
main () = show_it (User { name: \"Alice\" })",
    )
    .unwrap();
}

#[test]
fn where_clause_propagates_missing_impl() {
    let result = check(
        "record User { name: String }
trait Describe a {
  fun describe : (x: a) -> String
}
fun show_it : (x: a) -> String where {a: Describe}
show_it x = describe x
main () = show_it (User { name: \"Alice\" })",
    );
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message.contains("no impl of Describe for User"),
        "got: {}",
        err.message
    );
}

#[test]
fn effect_op_where_clause_satisfied_by_impl() {
    check(
        "record User { name: String }
trait Fooable a {
  fun foo_name : a -> String
}
impl Fooable for User {
  foo_name user = user.name
}
effect Foo {
  fun do_the_foo : a -> String where {a: Fooable}
}
fun use_it : User -> String needs {Foo}
use_it user = do_the_foo! user",
    )
    .unwrap();
}

#[test]
fn effect_op_where_clause_satisfied_by_function_where_bound() {
    check(
        "trait Fooable a {
  fun foo_name : a -> String
}
effect Foo {
  fun do_the_foo : a -> String where {a: Fooable}
}
fun use_it : a -> String needs {Foo} where {a: Fooable}
use_it x = do_the_foo! x",
    )
    .unwrap();
}

#[test]
fn effect_op_where_clause_usable_in_named_handler_arm() {
    // A handler implementing an op may use the op's own `where` constraint as an
    // assumption on the op's abstract type var, just like a function body uses
    // its own where-bounds. Previously this reported a spurious "ambiguous type
    // variable requires Fooable".
    check(
        "trait Fooable a {
  fun foo_name : a -> String
}
effect Foo {
  fun do_the_foo : a -> String where {a: Fooable}
}
handler use_foo for Foo {
  do_the_foo x = resume (foo_name x)
}",
    )
    .unwrap();
}

#[test]
fn effect_op_where_clause_usable_in_inline_handler_arm() {
    check(
        "trait Fooable a {
  fun foo_name : a -> String
}
effect Foo {
  fun do_the_foo : a -> String where {a: Fooable}
}
impl Fooable for Int {
  foo_name n = show n
}
main () = {
  do_the_foo! 1 with {
    do_the_foo x = resume (foo_name x)
  }
}",
    )
    .unwrap();
}

#[test]
fn effect_op_where_clause_missing_impl_fails() {
    let result = check(
        "record User { name: String }
trait Fooable a {
  fun foo_name : a -> String
}
effect Foo {
  fun do_the_foo : a -> String where {a: Fooable}
}
fun use_it : User -> String needs {Foo}
use_it user = do_the_foo! user",
    );
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message.contains("no impl of Fooable for User"),
        "got: {}",
        err.message
    );
}

#[test]
fn where_clause_multiple_bounds() {
    check(
        "trait Describe a {
  fun describe : (x: a) -> String
}
trait Greet a {
  fun greet : (x: a) -> String
}
fun both : (x: a) -> String where {a: Describe + Greet}
both x = describe x",
    )
    .unwrap();
}

#[test]
fn where_clause_unknown_type_var() {
    let result = check(
        "trait Describe a {
  fun describe : (x: a) -> String
}
fun show_it : (x: a) -> String where {b: Describe}
show_it x = describe x",
    );
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message.contains("unknown type variable 'b'"),
        "got: {}",
        err.message
    );
}

#[test]
fn ambiguous_type_var_from_where_clause() {
    // Calling a function with a where clause on a type variable that is never
    // bound to a concrete type should be an error, not silently ignored.
    // e.g. Ok("foo") |> unwrap where unwrap requires {b: Show} but b is never resolved.
    let result = check(
        "type MyResult a b
  = Ok(a)
  | Err(b)
fun unwrap : (r: MyResult a b) -> a where {b: Show}
unwrap r = case r {
  Ok(a) -> a
  Err(_) -> panic \"error\"
}
main () = unwrap (Ok(\"hello\"))",
    );
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message
            .contains("ambiguous type variable requires Show"),
        "got: {}",
        err.message
    );
}

#[test]
fn no_ambiguity_when_type_var_is_concrete() {
    // When the type variable IS resolved to a concrete type, no error.
    check(
        "trait Describe a {
  fun describe : (x: a) -> String
}
impl Describe for String {
  describe s = s
}
type Result a b
  = Ok(a)
  | Err(b)
fun unwrap : (r: Result a b) -> a where {b: Describe}
unwrap r = case r {
  Ok(a) -> a
  Err(b) -> describe b
}
main () = unwrap (Err(\"oops\"))",
    )
    .unwrap();
}

#[test]
fn ascription_correct_type() {
    check("main () = (42 : Int)").unwrap();
}

#[test]
fn ascription_wrong_type() {
    let result = check("main () = (42 : String)");
    assert!(result.is_err());
}

#[test]
fn ascription_resolves_ambiguous_type_var() {
    check(
        "type MyResult a b
  = Ok(a)
  | Err(b)
main () = {
  let x = (Ok(1) : MyResult Int String)
  x
}",
    )
    .unwrap();
}

#[test]
fn inferred_constraint_propagation() {
    // Function without where clause infers constraint; caller with impl succeeds
    check(
        "record User { name: String }
trait Describe a {
  fun describe : (x: a) -> String
}
impl Describe for User {
  describe u = u.name
}
wrapper x = describe x
main () = wrapper (User { name: \"Alice\" })",
    )
    .unwrap();
}

#[test]
fn inferred_constraint_no_impl() {
    // Function without where clause infers constraint; caller without impl fails
    let result = check(
        "record User { name: String }
trait Describe a {
  fun describe : (x: a) -> String
}
wrapper x = describe x
main () = wrapper (User { name: \"Alice\" })",
    );
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message.contains("no impl of Describe for User"),
        "got: {}",
        err.message
    );
}

// --- Supertrait enforcement ---

#[test]
fn supertrait_satisfied() {
    let result = check(
        "trait Eq a {
  fun eq : (x: a) -> (y: a) -> Bool
}
trait Ord a where {a: Eq} {
  fun compare : (x: a) -> (y: a) -> Int
}
record Foo { x: Int }
impl Eq for Foo {
  eq a b = a.x == b.x
}
impl Ord for Foo {
  compare a b = a.x - b.x
}
main () = compare (Foo { x: 1 }) (Foo { x: 2 })",
    );
    assert!(result.is_ok(), "got: {:?}", result.err());
}

#[test]
fn supertrait_bound_provides_parent_methods() {
    let result = check(
        "trait Parent a {
  fun parent : a -> Int
}
trait Child a where {a: Parent} {
  fun child : a -> Int
}
impl Parent for Int {
  parent x = x + 1
}
impl Child for Int {
  child x = x + 10
}
fun both : a -> Int where {a: Child}
both x = parent x + child x
let answer = both 2",
    );
    assert!(result.is_ok(), "got: {:?}", result.err());
}

#[test]
fn supertrait_missing_impl_fails() {
    let result = check(
        "trait Eq a {
  fun eq : (x: a) -> (y: a) -> Bool
}
trait Ord a where {a: Eq} {
  fun compare : (x: a) -> (y: a) -> Int
}
record Foo { x: Int }
impl Ord for Foo {
  compare a b = a.x - b.x
}
main () = compare (Foo { x: 1 }) (Foo { x: 2 })",
    );
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message.contains("requires impl Eq for Foo"),
        "got: {}",
        err.message
    );
}

#[test]
fn supertrait_multiple_supertraits() {
    let result = check(
        "trait Show a {
  fun show : (x: a) -> String
}
trait Eq a {
  fun eq : (x: a) -> (y: a) -> Bool
}
trait Special a where {a: Show + Eq} {
  fun special : (x: a) -> String
}
record Bar { num: Int }
impl Show for Bar {
  show b = \"Bar\"
}
impl Eq for Bar {
  eq a b = a.num == b.num
}
impl Special for Bar {
  special b = show b
}
main () = special (Bar { num: 1 })",
    );
    assert!(result.is_ok(), "got: {:?}", result.err());
}

#[test]
fn supertrait_one_of_multiple_missing() {
    let result = check(
        "trait Show a {
  fun show : (x: a) -> String
}
trait Eq a {
  fun eq : (x: a) -> (y: a) -> Bool
}
trait Special a where {a: Show + Eq} {
  fun special : (x: a) -> String
}
record Bar { num: Int }
impl Show for Bar {
  show b = \"Bar\"
}
impl Special for Bar {
  special b = show b
}
main () = special (Bar { num: 1 })",
    );
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message.contains("requires impl Eq for Bar"),
        "got: {}",
        err.message
    );
}

// --- Built-in Show constraint ---

#[test]
fn show_works_for_primitives() {
    check("main () = dbg (show 42)").unwrap();
    check("main () = dbg (show 1.5)").unwrap();
    check("main () = dbg \"hello\"").unwrap();
    check("main () = dbg (show True)").unwrap();
    check("main () = dbg (debug ())").unwrap();
    check("let x = show 42\nmain () = dbg x").unwrap();
}

#[test]
fn show_fails_for_custom_type_without_impl() {
    let result = check(
        "record Foo { x: Int }
main () = dbg (show (Foo { x: 1 }))",
    );
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message.contains("no impl of Show for Foo"),
        "got: {}",
        err.message
    );
}

#[test]
fn show_works_for_custom_type_with_impl() {
    check(
        "record Foo { x: Int }
impl Show for Foo {
  show f = \"Foo\"
}
main () = dbg (show (Foo { x: 1 }))",
    )
    .unwrap();
}

#[test]
fn show_constraint_propagates() {
    // Function using show on polymorphic arg should infer Show constraint
    let result = check(
        "record Foo { x: Int }
display x = show x
main () = display (Foo { x: 1 })",
    );
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message.contains("no impl of Show for Foo"),
        "got: {}",
        err.message
    );
}

#[test]
fn effectful_function_application_reports_argument_mismatch() {
    let result = check(
        "import Std.IO (console, println)
main () = {
  println (dbg 1)
} with {console}",
    );
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message
            .contains("type mismatch: expected String, got Unit"),
        "got: {}",
        err.message
    );
}

#[test]
fn lambda_body_effectful_function_application_reports_argument_mismatch() {
    let result = check(
        "import Std.IO (console, println)
main () = {
  let f = fun user -> println (dbg user)
  f \"hi\"
} with {console}",
    );
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message
            .contains("type mismatch: expected String, got Unit"),
        "got: {}",
        err.message
    );
}

// --- Num constraint tests ---

#[test]
fn num_arithmetic_on_int() {
    assert!(check("main () = 1 + 2 * 3 - 4 / 2 % 3").is_ok());
}

#[test]
fn num_arithmetic_on_float() {
    assert!(check("main () = 1.0 + 2.0 * 3.0").is_ok());
}

#[test]
fn mod_on_float_works() {
    // Float now has Num impl with mod, lowered to math:fmod
    assert!(check("main () = 1.0 % 2.0").is_ok());
}

#[test]
fn mod_on_int_works() {
    assert!(check("main () = 7 % 3").is_ok());
}

#[test]
fn div_int_returns_int() {
    assert!(check("main () = 7 / 2").is_ok());
}

#[test]
fn div_float_returns_float() {
    assert!(check("main () = 7.0 / 2.0").is_ok());
}

#[test]
fn div_mixed_int_float_fails() {
    assert!(check("main () = 7 / 2.0").is_err());
}

#[test]
fn num_arithmetic_on_string_fails() {
    let result = check("main () = \"a\" + \"b\"");
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message.contains("Num") && err.message.contains("String"),
        "got: {}",
        err.message
    );
}

#[test]
fn num_arithmetic_on_bool_fails() {
    let result = check("main () = True + False");
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message.contains("Num") && err.message.contains("Bool"),
        "got: {}",
        err.message
    );
}

#[test]
fn num_unary_minus() {
    assert!(check("main () = -(5)").is_ok());
}

#[test]
fn num_constraint_propagates() {
    // Polymorphic function using + should infer Num constraint
    let result = check(
        "record Foo { x: Int }
add a b = a + b
main () = add (Foo { x: 1 }) (Foo { x: 2 })",
    );
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message.contains("Num") && err.message.contains("Foo"),
        "got: {}",
        err.message
    );
}

#[test]
fn user_defined_add_does_not_collide_with_stdlib() {
    // Users should be able to define their own `add` without conflicting with Int.add
    assert!(
        check(
            "fun add : String -> String -> String
add a b = a <> b
main () = add \"hello\" \"world\""
        )
        .is_ok()
    );
}

#[test]
fn semigroup_where_clause_supports_concat() {
    assert!(
        check(
            "fun combine_all : a -> a -> a where {a: Semigroup}
combine_all a b = a <> b
main () = combine_all [\"hello\"] [\"world\"]"
        )
        .is_ok()
    );
}

#[test]
fn monoid_empty_for_stdlib_semigroups() {
    let result = check(
        r#"
fun combine_empty : a -> a where {a: Monoid}
combine_empty x = combine empty x

let s : String = combine_empty "hello"
let xs : List Int = combine_empty [1, 2]
let bs : BitString = combine_empty <<1, 2>>
"#,
    );
    assert!(result.is_ok(), "got: {:?}", result.err());
}

// --- Eq constraint tests ---

#[test]
fn eq_comparison_on_int() {
    assert!(check("main () = 1 == 1").is_ok());
}

#[test]
fn eq_comparison_on_string() {
    assert!(check("main () = \"a\" != \"b\"").is_ok());
}

#[test]
fn eq_comparison_on_bool() {
    assert!(check("main () = True == False").is_ok());
}

#[test]
fn eq_comparison_on_custom_type_fails() {
    let result = check(
        "record Foo { x: Int }
main () = (Foo { x: 1 }) == (Foo { x: 2 })",
    );
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message.contains("Eq") && err.message.contains("Foo"),
        "got: {}",
        err.message
    );
}

// --- Ord constraint tests ---

#[test]
fn ord_comparison_on_int() {
    assert!(check("main () = 1 < 2").is_ok());
}

#[test]
fn ord_comparison_on_string() {
    assert!(check("main () = \"a\" < \"b\"").is_ok());
}

#[test]
fn ord_comparison_on_bool_fails() {
    let result = check("main () = True < False");
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message.contains("Ord") && err.message.contains("Bool"),
        "got: {}",
        err.message
    );
}

#[test]
fn ord_constraint_propagates() {
    // Polymorphic function using < should infer Ord constraint
    assert!(
        check(
            "smaller a b = if a < b then a else b
main () = smaller 1 2"
        )
        .is_ok()
    );
}

#[test]
fn ord_constraint_propagates_missing_impl() {
    let result = check(
        "record Foo { x: Int }
smaller a b = if a < b then a else b
main () = smaller (Foo { x: 1 }) (Foo { x: 2 })",
    );
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message.contains("Ord") && err.message.contains("Foo"),
        "got: {}",
        err.message
    );
}

// --- Conditional impl tests ---

#[test]
fn debug_list_of_ints() {
    assert!(check("main () = debug [1, 2, 3]").is_ok());
}

#[test]
fn debug_list_of_strings() {
    assert!(check("main () = debug [\"a\", \"b\"]").is_ok());
}

#[test]
fn debug_list_of_custom_type_fails() {
    let result = check(
        "record Foo { x: Int }
main () = debug [Foo { x: 1 }]",
    );
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message.contains("Debug") && err.message.contains("Foo"),
        "got: {}",
        err.message
    );
}

#[test]
fn debug_nested_list() {
    // List (List Int) -- Debug propagates through both layers
    assert!(check("main () = debug [[1, 2], [3]]").is_ok());
}

// --- User-defined conditional impl tests ---

#[test]
fn user_conditional_impl_satisfied() {
    // impl Show for Box a where {a: Show} -- show (Box 1) should work
    let result = check(
        "type Box a = Box(a)
impl Show for Box a where {a: Show} {
  show box = \"box\"
}
main () = show (Box 1)",
    );
    assert!(result.is_ok(), "got: {}", result.err().unwrap().message);
}

#[test]
fn user_conditional_impl_unsatisfied() {
    // show (Box (Foo {})) should fail -- Foo has no Show impl
    let result = check(
        "record Foo { x: Int }
type Box a = Box(a)
impl Show for Box a where {a: Show} {
  show box = \"box\"
}
main () = show (Box (Foo { x: 1 }))",
    );
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message.contains("Show") && err.message.contains("Foo"),
        "got: {}",
        err.message
    );
}

#[test]
fn user_conditional_impl_unknown_type_var() {
    let result = check(
        "type Box a = Box(a)
impl Show for Box a where {b: Show} {
  show box = \"box\"
}
main () = ()",
    );
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message.contains("unknown type variable") && err.message.contains("'b'"),
        "got: {}",
        err.message
    );
}

// --- Tuple tests ---

#[test]
fn tuple_pair() {
    let result = check("main () = (1, \"hello\")");
    assert!(result.is_ok(), "got: {}", result.err().unwrap().message);
}

#[test]
fn tuple_triple() {
    let result = check("main () = (1, 2.0, True)");
    assert!(result.is_ok(), "got: {}", result.err().unwrap().message);
}

#[test]
fn tuple_pattern_in_case() {
    let result = check(
        "main () = case (1, \"hi\") {
  (x, y) -> x
}",
    );
    assert!(result.is_ok(), "got: {}", result.err().unwrap().message);
}

#[test]
fn tuple_show() {
    assert!(check("main () = show (1, 2)").is_ok());
}

#[test]
fn tuple_show_fails_without_element_show() {
    let result = check(
        "record Foo { x: Int }
main () = show (Foo { x: 1 }, 2)",
    );
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message.contains("Show") && err.message.contains("Foo"),
        "got: {}",
        err.message
    );
}

#[test]
fn tuple_any_arity() {
    let result = check("main () = (1, 2, 3, 4, 5)");
    assert!(result.is_ok(), "got: {}", result.err().unwrap().message);
}

#[test]
fn tuple_type_annotation() {
    let result = check(
        "fun fst : (p: (Int, String)) -> Int
fst p = case p { (x, _) -> x }
main () = fst (1, \"hello\")",
    );
    assert!(result.is_ok(), "got: {}", result.err().unwrap().message);
}

// --- Handler needs checking ---

#[test]
fn handler_uses_effect_without_needs_is_error() {
    // Handler body uses an effect but declares no needs
    let result = check(
        "effect Log { fun log : (msg: String) -> Unit }
effect Http { fun get : (url: String) -> String }
handler my_http for Http {
  get url = {
    log! \"fetching\"
    resume \"ok\"
  }
}",
    );
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message.contains("Log"),
        "expected Log in error, got: {}",
        err.message
    );
}

#[test]
fn handler_uses_effect_with_correct_needs_ok() {
    // Handler body uses Log and declares needs {Log}
    let result = check(
        "effect Log { fun log : (msg: String) -> Unit }
effect Http { fun get : (url: String) -> String }
handler console for Log {
  log msg = resume ()
}
handler my_http for Http needs {Log} {
  get url = {
    log! \"fetching\"
    resume \"ok\"
  }
}",
    );
    assert!(result.is_ok(), "got: {}", result.err().unwrap().message);
}

#[test]
fn pure_handler_no_needs_ok() {
    // Handler body has no effects -- no needs clause needed
    let result = check(
        "effect Http { fun get : (url: String) -> String }
handler mock_http for Http {
  get url = resume \"mocked\"
}",
    );
    assert!(result.is_ok(), "got: {}", result.err().unwrap().message);
}

#[test]
fn handler_needs_missing_one_effect_is_error() {
    // Handler uses Log and Http but only declares needs {Log}
    let result = check(
        "effect Log { fun log : (msg: String) -> Unit }
effect Http { fun get : (url: String) -> String }
effect Db { fun query : (sql: String) -> String }
handler log_impl for Log { log msg = resume () }
handler my_db for Db needs {Log} {
  query sql = {
    log! \"querying\"
    get! \"/check\"
    resume \"row\"
  }
}",
    );
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message.contains("Http"),
        "expected Http in error, got: {}",
        err.message
    );
}

#[test]
fn handler_missing_operation() {
    // Handler for an effect with two ops but only handles one
    let result = check(
        "effect State {\n  fun get : Unit -> Int\n  fun put : (n: Int) -> Unit\n}\nhandler partial for State {\n  get () = resume 0\n}",
    );
    assert!(result.is_err());
}

#[test]
fn handler_empty_body() {
    let result =
        check("effect Log {\n  fun log : (msg: String) -> Unit\n}\nhandler noop for Log {}");
    assert!(result.is_err());
}

// --- Let binding type annotations ---

#[test]
fn let_annotation_correct() {
    check("main () = { let x: Int = 5\n x }").unwrap();
}

#[test]
fn let_annotation_mismatch() {
    let result = check("main () = { let x: String = 5\n x }");
    assert!(result.is_err());
}

#[test]
fn let_annotation_guides_inference() {
    // Annotation constrains the binding's type for subsequent use
    check(
        "fun add : (x: Int) -> Int
add x = x + 1
main () = { let n: Int = 10\n add n }",
    )
    .unwrap();
}

#[test]
fn top_level_let_annotation_correct() {
    check("let x: Int = 5\nmain () = x").unwrap();
}

#[test]
fn top_level_let_annotation_mismatch() {
    let result = check("let x: String = 5\nmain () = x");
    assert!(result.is_err());
}

// --- String interpolation ---

#[test]
fn interp_infers_string() {
    let ty = infer_expr_type(r#"$"hello {42}""#).unwrap();
    assert_eq!(ty, Type::string());
}

#[test]
fn interp_show_constraint_enforced() {
    // A type without Show cannot appear in a hole
    let result = check(
        r#"type Foo = Foo
main () = $"val: {Foo}""#,
    );
    assert!(result.is_err());
}

// --- Exhaustiveness checking ---

#[test]
fn exhaustive_case_all_constructors() {
    check(
        "type Maybe a = Just(a) | Nothing
let x = case Just 42 {
  Just(n) -> n
  Nothing -> 0
}",
    )
    .unwrap();
}

#[test]
fn exhaustive_case_wildcard() {
    check(
        "type Maybe a = Just(a) | Nothing
let x = case Just 42 {
  Just(n) -> n
  _ -> 0
}",
    )
    .unwrap();
}

#[test]
fn exhaustive_case_var_pattern() {
    check(
        "type Maybe a = Just(a) | Nothing
let x = case Just 42 {
  y -> 0
}",
    )
    .unwrap();
}

#[test]
fn non_exhaustive_case_missing_constructor() {
    let result = check(
        "type Maybe a = Just(a) | Nothing
let x = case Just 42 {
  Just(n) -> n
}",
    );
    let err = result.err().expect("expected type error");
    assert!(
        err.message.contains("non-exhaustive"),
        "expected non-exhaustive error, got: {}",
        err.message
    );
    assert!(err.message.contains("Nothing"));
}

#[test]
fn non_exhaustive_case_three_variants() {
    let result = check(
        "type Color = Red | Green | Blue
fun f : (c: Color) -> Int
f c = case c {
  Red -> 1
}",
    );
    let err = result.err().expect("expected type error");
    assert!(err.message.contains("non-exhaustive"));
    assert!(err.message.contains("Green"));
    assert!(err.message.contains("Blue"));
}

#[test]
fn exhaustive_case_bool_literals() {
    check(
        "let x = case True {
  True -> 1
  False -> 0
}",
    )
    .unwrap();
}

#[test]
fn non_exhaustive_case_bool_missing_false() {
    let result = check(
        "let x = case True {
  True -> 1
}",
    );
    let err = result.err().expect("expected type error");
    assert!(err.message.contains("non-exhaustive"));
    assert!(err.message.contains("False"));
}

#[test]
fn exhaustive_case_guard_with_wildcard_fallback() {
    // Guarded arm doesn't count for exhaustiveness, but wildcard fallback covers all
    check(
        "type Maybe a = Just(a) | Nothing
let x = case Just 42 {
  Just(n) when n > 0 -> n
  _ -> 0
}",
    )
    .unwrap();
}

#[test]
fn non_exhaustive_case_only_guarded_arm() {
    // Guarded arm alone doesn't cover the constructor
    let result = check(
        "type Maybe a = Just(a) | Nothing
let x = case Just 42 {
  Just(n) when n > 0 -> n
  Nothing -> 0
}",
    );
    let err = result.err().expect("expected type error");
    assert!(err.message.contains("non-exhaustive"));
    assert!(err.message.contains("Just"));
}

#[test]
fn case_int_with_wildcard() {
    // Int with literal patterns + wildcard is fine
    check(
        "let x = case 42 {
  0 -> \"zero\"
  _ -> \"other\"
}",
    )
    .unwrap();
}

#[test]
fn do_else_exhaustive() {
    check(
        "type Result a e = Ok(a) | Err(e)
fun get : Unit -> Result Int String
get () = Ok(42)
let x = do {
  Ok(n) <- get ()
  n
} else {
  Err(_) -> 0
}",
    )
    .unwrap();
}

#[test]
fn do_else_non_exhaustive() {
    let result = check(
        "type Shape = Circle | Rect | Point
fun get_shape : Unit -> Shape
get_shape () = Circle
let x = do {
  Circle <- get_shape ()
  1
} else {
  Rect -> 2
}",
    );
    let err = result.err().expect("expected type error");
    assert!(err.message.contains("non-exhaustive do...else"));
    assert!(err.message.contains("Point"));
}

#[test]
fn do_else_wildcard_covers_all() {
    check(
        "type Result a e = Ok(a) | Err(e)
fun get : Unit -> Result Int String
get () = Ok(42)
let x = do {
  Ok(n) <- get ()
  n
} else {
  _ -> 0
}",
    )
    .unwrap();
}

#[test]
fn do_else_propagates_payload_type_to_else_arm() {
    // Regression: the else-arm pattern's payload type variable must be
    // unified with the binding's actual type, otherwise patterns like
    // `Err(e) -> Err(e)` leave `e` as a free variable and the do-block's
    // result type is ambiguous (Result _ a instead of Result _ DecodeError).
    //
    // This test deliberately omits an outer function signature so the
    // do-block must infer its own type purely from the bindings. With
    // the bug, the result type ends up as Result _ a where `a` is free,
    // and using the result with a trait-requiring function (Debug here)
    // produces an "ambiguous type variable requires Debug" error.
    check(
        "type DecodeError = DecodeError String deriving (Debug)
fun step1 : Unit -> Result Int DecodeError
step1 () = Ok(1)
fun step2 : Unit -> Result String DecodeError
step2 () = Ok(\"two\")
let _ = {
  let result = do {
    Ok(n) <- step1 ()
    Ok(s) <- step2 ()
    Ok((n, s))
  } else {
    Err(e) -> Err(e)
  }
  dbg result
}",
    )
    .unwrap();
}

// --- Unreachable arm detection ---

#[test]
fn unreachable_duplicate_constructor() {
    let result = check(
        "type Maybe a = Just(a) | Nothing
let x = case Just 42 {
  Just(n) -> n
  Nothing -> 0
  Just(m) -> m
}",
    );
    let err = result.err().expect("expected type error");
    assert!(err.message.contains("unreachable"));
    assert!(err.message.contains("Just"));
}

#[test]
fn unreachable_after_wildcard() {
    let result = check(
        "type Maybe a = Just(a) | Nothing
let x = case Just 42 {
  _ -> 0
  Just(n) -> n
}",
    );
    let err = result.err().expect("expected type error");
    assert!(err.message.contains("unreachable"));
}

#[test]
fn unreachable_wildcard_after_all_covered() {
    let result = check(
        "type Maybe a = Just(a) | Nothing
let x = case Just 42 {
  Just(n) -> n
  Nothing -> 0
  _ -> 99
}",
    );
    let err = result.err().expect("expected type error");
    assert!(err.message.contains("unreachable"));
}

#[test]
fn unreachable_bool_duplicate() {
    let result = check(
        "let x = case True {
  True -> 1
  False -> 0
  True -> 2
}",
    );
    let err = result.err().expect("expected type error");
    assert!(err.message.contains("unreachable"));
    assert!(err.message.contains("True"));
}

#[test]
fn guarded_arm_not_redundant() {
    // A guarded arm followed by an unguarded arm for the same constructor is fine
    check(
        "type Maybe a = Just(a) | Nothing
let x = case Just 42 {
  Just(n) when n > 0 -> n
  Just(n) -> 0
  Nothing -> 0
}",
    )
    .unwrap();
}

// --- Primitive exhaustiveness (require wildcard) ---

#[test]
fn int_case_without_wildcard() {
    let result = check(
        "let x = case 42 {
  0 -> \"zero\"
  1 -> \"one\"
}",
    );
    let err = result.err().expect("expected type error");
    assert!(err.message.contains("non-exhaustive"));
    assert!(err.message.contains("Int"));
}

#[test]
fn int_case_with_var_fallback() {
    check(
        "let x = case 42 {
  0 -> \"zero\"
  n -> \"other\"
}",
    )
    .unwrap();
}

#[test]
fn int_case_only_guarded_arms() {
    let result = check(
        "let x = case 42 {
  n when n > 0 -> \"positive\"
  n when n < 0 -> \"negative\"
}",
    );
    let err = result.err().expect("expected type error");
    assert!(err.message.contains("non-exhaustive"));
    assert!(err.message.contains("Int"));
}

#[test]
fn string_case_without_wildcard() {
    let result = check(
        r#"let x = case "hello" {
  "hello" -> 1
  "world" -> 2
}"#,
    );
    let err = result.err().expect("expected type error");
    assert!(err.message.contains("non-exhaustive"));
    assert!(err.message.contains("String"));
}

#[test]
fn string_case_only_guarded_arms() {
    let result = check(
        r#"let x = case "hello" {
  s when s == "hello" -> 1
}"#,
    );
    let err = result.err().expect("expected type error");
    assert!(err.message.contains("non-exhaustive"));
    assert!(err.message.contains("String"));
}

// --- Record exhaustiveness ---

#[test]
fn record_pattern_with_literal_field_non_exhaustive() {
    let result = check(
        r#"record User { name: String, age: Int }
let u = User "Dylan" 25
let x = case u {
  User { name: "Dylan", .. } -> 1
}"#,
    );
    let err = result.err().expect("expected type error");
    assert!(
        err.message.contains("non-exhaustive"),
        "expected non-exhaustive error, got: {}",
        err.message
    );
}

#[test]
fn record_pattern_with_wildcard_field_exhaustive() {
    check(
        r#"record User { name: String, age: Int }
let u = User "Dylan" 25
let x = case u {
  User { name: "Dylan", .. } -> 1
  User { .. } -> 2
}"#,
    )
    .unwrap();
}

#[test]
fn record_pattern_bare_binding_exhaustive() {
    // User { name, age } lists all fields -- should be exhaustive
    check(
        r#"record User { name: String, age: Int }
let u = User "Dylan" 25
let x = case u {
  User { name, age } -> 1
}"#,
    )
    .unwrap();
}

#[test]
fn record_pattern_partial_without_rest_is_error() {
    let result = check(
        r#"record User { name: String, age: Int }
let u = User "Dylan" 25
let x = case u {
  User { name } -> 1
}"#,
    );
    let err = result.err().expect("expected type error");
    assert!(
        err.message.contains("missing fields"),
        "expected missing fields error, got: {}",
        err.message
    );
}

#[test]
fn record_pattern_partial_with_rest() {
    // User { name, .. } is allowed -- `..` means ignore remaining fields
    check(
        r#"record User { name: String, age: Int }
let u = User "Dylan" 25
let x = case u {
  User { name, .. } -> 1
}"#,
    )
    .unwrap();
}

#[test]
fn record_nested_anon_record_literal_non_exhaustive() {
    let result = check(
        r#"record House { address: { street: String, city: String }, bedrooms: Int }
let h = House { address: { street: "250th", city: "NYC" }, bedrooms: 3 }
let x = case h {
  House { address: { street: "250th Street", city }, .. } -> 1
}"#,
    );
    let err = result.err().expect("expected type error");
    assert!(
        err.message.contains("non-exhaustive"),
        "expected non-exhaustive error, got: {}",
        err.message
    );
}

#[test]
fn record_nested_anon_record_with_catchall() {
    check(
        r#"record House { address: { street: String, city: String }, bedrooms: Int }
let h = House { address: { street: "250th", city: "NYC" }, bedrooms: 3 }
let x = case h {
  House { address: { street: "250th Street", city }, .. } -> 1
  House { .. } -> 2
}"#,
    )
    .unwrap();
}

#[test]
fn anon_record_partial_with_rest() {
    check(
        r#"record House { address: { street: String, city: String }, bedrooms: Int }
let h = House { address: { street: "250th", city: "NYC" }, bedrooms: 3 }
let x = case h {
  House { address: { street, .. }, .. } -> street
}"#,
    )
    .unwrap();
}

// --- Nested pattern exhaustiveness (Maranget) ---

#[test]
fn nested_exhaustive_all_combinations() {
    // All 4 combinations of (Bool, Bool) inside a constructor
    check(
        "type Pair = MkPair(Bool, Bool)
fun f : (p: Pair) -> Int
f p = case p {
  MkPair(True, True) -> 1
  MkPair(True, False) -> 2
  MkPair(False, True) -> 3
  MkPair(False, False) -> 4
}",
    )
    .unwrap();
}

#[test]
fn nested_non_exhaustive_missing_combination() {
    // Missing MkPair(False, False)
    let result = check(
        "type Pair = MkPair(Bool, Bool)
fun f : (p: Pair) -> Int
f p = case p {
  MkPair(True, True) -> 1
  MkPair(True, False) -> 2
  MkPair(False, True) -> 3
}",
    );
    let err = result.err().expect("expected type error");
    assert!(err.message.contains("non-exhaustive"));
    assert!(err.message.contains("MkPair"));
    assert!(err.message.contains("False"));
}

#[test]
fn nested_exhaustive_with_wildcard_in_subpattern() {
    // Wildcard in second position covers both True and False
    check(
        "type Pair = MkPair(Bool, Bool)
fun f : (p: Pair) -> Int
f p = case p {
  MkPair(True, _) -> 1
  MkPair(False, _) -> 2
}",
    )
    .unwrap();
}

#[test]
fn nested_exhaustive_with_top_level_wildcard() {
    // A top-level wildcard covers everything
    check(
        "type Pair = MkPair(Bool, Bool)
fun f : (p: Pair) -> Int
f p = case p {
  MkPair(True, True) -> 1
  _ -> 0
}",
    )
    .unwrap();
}

#[test]
fn nested_redundant_after_wildcards() {
    // MkPair(True, True) is already covered by the two wildcard arms
    let result = check(
        "type Pair = MkPair(Bool, Bool)
fun f : (p: Pair) -> Int
f p = case p {
  MkPair(True, _) -> 1
  MkPair(False, _) -> 2
  MkPair(True, True) -> 3
}",
    );
    let err = result.err().expect("expected type error");
    assert!(err.message.contains("unreachable"));
}

#[test]
fn nested_maybe_of_bool_exhaustive() {
    // Maybe(Bool) fully covered
    check(
        "type Maybe a = Just(a) | Nothing
fun f : (m: Maybe Bool) -> Int
f m = case m {
  Just(True) -> 1
  Just(False) -> 2
  Nothing -> 0
}",
    )
    .unwrap();
}

#[test]
fn nested_maybe_of_bool_missing() {
    // Missing Just(False)
    let result = check(
        "type Maybe a = Just(a) | Nothing
fun f : (m: Maybe Bool) -> Int
f m = case m {
  Just(True) -> 1
  Nothing -> 0
}",
    );
    let err = result.err().expect("expected type error");
    assert!(err.message.contains("non-exhaustive"));
    assert!(err.message.contains("Just"));
}

#[test]
fn nested_list_cons_exhaustive() {
    // List with nested pattern on head
    check(
        "type Maybe a = Just(a) | Nothing
fun f : (xs: List (Maybe Int)) -> Int
f xs = case xs {
  Just(_) :: _ -> 1
  Nothing :: _ -> 2
  [] -> 0
}",
    )
    .unwrap();
}

#[test]
fn list_non_exhaustive_missing_nil() {
    let result = check(
        "fun f : (xs: List Int) -> Int
f xs = case xs {
  Cons _ _ -> 1
}",
    );
    let err = result.err().expect("expected type error");
    assert!(
        err.message.contains("non-exhaustive"),
        "expected non-exhaustive error, got: {}",
        err.message
    );
    assert!(err.message.contains("Nil"));
}

#[test]
fn list_non_exhaustive_missing_cons() {
    let result = check(
        "fun f : (xs: List Int) -> Int
f xs = case xs {
  Nil -> 0
}",
    );
    let err = result.err().expect("expected type error");
    assert!(
        err.message.contains("non-exhaustive"),
        "expected non-exhaustive error, got: {}",
        err.message
    );
    assert!(err.message.contains("Cons"));
}

#[test]
fn tuple_exhaustive_bool_pair() {
    check(
        "fun f : (p: (Bool, Bool)) -> Int
f p = case p {
  (True, True) -> 1
  (True, False) -> 2
  (False, True) -> 3
  (False, False) -> 4
}",
    )
    .unwrap();
}

#[test]
fn tuple_non_exhaustive_missing() {
    let result = check(
        "fun f : (p: (Bool, Bool)) -> Int
f p = case p {
  (True, True) -> 1
  (True, False) -> 2
  (False, True) -> 3
}",
    );
    let err = result.err().expect("expected type error");
    assert!(err.message.contains("non-exhaustive"));
}

#[test]
fn tuple_exhaustive_with_wildcard() {
    check(
        "fun f : (p: (Bool, Bool)) -> Int
f p = case p {
  (True, _) -> 1
  (False, _) -> 2
}",
    )
    .unwrap();
}

// --- Function head exhaustiveness ---

#[test]
fn fun_clauses_exhaustive_bool() {
    check(
        "fun f : (x: Bool) -> Int
f True = 1
f False = 0",
    )
    .unwrap();
}

#[test]
fn fun_clauses_non_exhaustive_bool() {
    let result = check(
        "fun f : (x: Bool) -> Int
f True = 1",
    );
    let err = result.err().expect("expected type error");
    assert!(err.message.contains("non-exhaustive"));
    assert!(err.message.contains("False"));
}

#[test]
fn fun_clauses_exhaustive_adt() {
    check(
        "type Maybe a = Just(a) | Nothing
fun f : (m: Maybe Int) -> Int
f (Just(x)) = x
f Nothing = 0",
    )
    .unwrap();
}

#[test]
fn fun_clauses_non_exhaustive_adt() {
    let result = check(
        "type Maybe a = Just(a) | Nothing
fun f : (m: Maybe Int) -> Int
f (Just(x)) = x",
    );
    let err = result.err().expect("expected type error");
    assert!(err.message.contains("non-exhaustive"));
    assert!(err.message.contains("Nothing"));
}

#[test]
fn fun_clauses_redundant() {
    let result = check(
        "fun f : (x: Bool) -> Int
f True = 1
f False = 0
f True = 2",
    );
    let err = result.err().expect("expected type error");
    assert!(err.message.contains("unreachable"));
}

#[test]
fn fun_clauses_with_wildcard_exhaustive() {
    check(
        "type Color = Red | Green | Blue
fun f : (c: Color) -> Int
f Red = 1
f _ = 0",
    )
    .unwrap();
}

#[test]
fn fun_clauses_single_var_param_skips_check() {
    // Single clause with variable param should not trigger exhaustiveness
    check(
        "fun f : (x: Int) -> Int
f x = x + 1",
    )
    .unwrap();
}

// --- Dict ---

#[test]
fn dict_new_typechecks() {
    assert!(check("import Std.Dict\nmain () = Dict.new ()").is_ok());
}

// `Dict` is a compiler builtin, not a type declared in Std.Dict. Qualifying it
// through the module (`Dict.Dict`, an aliased prefix, or the fully-qualified
// `Std.Dict.Dict`) must resolve to the one true builtin canonical rather than
// minting a phantom `Type::Con("Dict.Dict", ..)` that fails to unify with the
// real builtin while printing identically.
#[test]
fn qualified_builtin_type_in_annotation_resolves_to_builtin() {
    check(
        "import Std.Dict as Dict\n\
         main () = {\n\
           let d: Dict.Dict Int Int = Dict.from_list [(1, 2)]\n\
           Dict.size d\n\
         }",
    )
    .unwrap();
}

#[test]
fn aliased_builtin_type_in_annotation_resolves_to_builtin() {
    check(
        "import Std.Dict as Dicts\n\
         main () = {\n\
           let d: Dicts.Dict Int Int = Dicts.from_list [(1, 2)]\n\
           Dicts.size d\n\
         }",
    )
    .unwrap();
}

#[test]
fn fully_qualified_builtin_type_in_annotation_resolves_to_builtin() {
    check(
        "import Std.Dict as Dict\n\
         main () = {\n\
           let d: Std.Dict.Dict Int Int = Dict.from_list [(1, 2)]\n\
           Dict.size d\n\
         }",
    )
    .unwrap();
}

// Exposing a builtin type by name is legitimate — it must not error with
// "'Dict' is not exported".
#[test]
fn exposing_builtin_type_does_not_error() {
    check(
        "import Std.Dict (Dict)\n\
         import Std.Dict as Dict\n\
         main () = {\n\
           let d: Dict Int Int = Dict.from_list [(1, 2)]\n\
           Dict.size d\n\
         }",
    )
    .unwrap();
}

// Dict.put, Dict.keys, Dict.values, Dict.size, Dict.from_list, Dict.to_list,
// Dict.member are now defined in Std/Dict.saga via @external declarations.
// Their type checking is covered by module integration tests.

#[test]
fn string_literal_pattern() {
    assert!(
        check(
            "fun f : (s: String) -> Int
f s = case s {
  \"hello\" -> 1
  _ -> 0
}"
        )
        .is_ok()
    );
}

#[test]
fn string_prefix_pattern() {
    assert!(
        check(
            "fun f : (s: String) -> String
f s = case s {
  \"prefix\" <> rest -> rest
  _ -> s
}"
        )
        .is_ok()
    );
}

#[test]
fn effect_call_in_case_guard_rejected() {
    let result = check(
        "effect Check {
  fun check : (n: Int) -> Bool
}

fun filter : (x: Int) -> Int needs {Check}
filter x = case x {
  n when check! n -> n
  _ -> 0
}",
    );
    assert!(result.is_err());
    let err = result.err().expect("expected type error");
    assert!(
        err.message.contains("not allowed in guard"),
        "expected guard error, got: {}",
        err.message
    );
}

#[test]
fn effect_call_in_multi_clause_guard_rejected() {
    let result = check(
        "effect Check {
  fun check : (n: Int) -> Bool
}

fun filter : (x: Int) -> Int needs {Check}
filter x when check! x = x
filter _ = 0",
    );
    assert!(result.is_err());
    let err = result.err().expect("expected type error");
    assert!(
        err.message.contains("not allowed in guard"),
        "expected guard error, got: {}",
        err.message
    );
}

#[test]
fn pure_guard_still_works() {
    // Make sure we didn't break normal guards
    assert!(
        check(
            "clamp x = case x {
  n when n < 0 -> 0
  n -> n
}"
        )
        .is_ok()
    );
}

// --- Generic effects ---

#[test]
fn generic_effect_basic() {
    // effect State s with get/put, handler for State Int, function using it
    assert!(
        check(
            "effect State s {
  fun get : Unit -> s
  fun put : (v: s) -> Unit
}

handler counter for State Int {
  get () = resume 0
  put v = resume ()
}

fun use_state : Unit -> Unit needs {State}
use_state () = {
  let x = get! ()
  put! (x + 1)
}"
        )
        .is_ok()
    );
}

#[test]
fn generic_effect_type_shared_across_ops() {
    // get returns s, put takes s -- they must agree
    // Here the handler says State Int, so get returns Int and put takes Int
    assert!(
        check(
            "effect State s {
  fun get : Unit -> s
  fun put : (v: s) -> Unit
}

handler string_state for State String {
  get () = resume \"hello\"
  put v = resume ()
}

fun use_string_state : Unit -> Unit needs {State}
use_string_state () = {
  let s = get! ()
  put! (s <> \" world\")
}"
        )
        .is_ok()
    );
}

#[test]
fn non_parameterized_effects_still_work() {
    // Existing non-parameterized effects should work exactly as before
    assert!(
        check(
            "effect Log {
  fun log : (msg: String) -> Unit
}

handler console for Log {
  log msg = resume ()
}

fun work : Unit -> Unit needs {Log}
work () = log! \"hello\""
        )
        .is_ok()
    );
}

#[test]
fn generic_effect_handler_type_mismatch() {
    // Handler declares State Int but resumes with a String -- should fail
    let result = check(
        "effect State s {
  fun get : Unit -> s
  fun put : (v: s) -> Unit
}

handler bad for State Int {
  get () = resume \"not an int\"
  put v = resume ()
}",
    );
    assert!(result.is_err());
}

#[test]
fn generic_effect_get_infers_type() {
    // get! returns s, and adding 1 to it constrains s to Int
    assert!(
        check(
            "effect State s {
  fun get : Unit -> s
  fun put : (v: s) -> Unit
}

fun inc : Unit -> Unit needs {State}
inc () = {
  let x = get! ()
  put! (x + 1)
}"
        )
        .is_ok()
    );
}

#[test]
fn generic_effect_put_get_type_mismatch() {
    // get returns s, put takes s -- using get as Int then putting a String should fail
    let result = check(
        "effect State s {
  fun get : Unit -> s
  fun put : (v: s) -> Unit
}

fun bad : Unit -> Unit needs {State}
bad () = {
  let x = get! ()
  let _ = x + 1
  put! \"hello\"
}",
    );
    assert!(result.is_err());
}

#[test]
fn generic_effect_multiple_type_params() {
    // Effect with two type params
    assert!(
        check(
            "effect Store k v {
  fun read : (key: k) -> v
  fun write : (key: k) -> (data: v) -> Unit
}

handler dict_store for Store String Int {
  read key = resume 0
  write key data = resume ()
}"
        )
        .is_ok()
    );
}

#[test]
fn generic_effect_with_existing_effects() {
    // Generic and non-generic effects together
    assert!(
        check(
            "effect Log {
  fun log : (msg: String) -> Unit
}

effect State s {
  fun get : Unit -> s
  fun put : (v: s) -> Unit
}

fun work : Unit -> Unit needs {Log, State}
work () = {
  log! \"starting\"
  let x = get! ()
  put! (x + 1)
  log! \"done\"
}"
        )
        .is_ok()
    );
}

#[test]
fn generic_effect_independent_across_functions() {
    // Two functions can use the same generic effect at different types
    assert!(
        check(
            "effect State s {
  fun get : Unit -> s
  fun put : (v: s) -> Unit
}

fun use_int : Unit -> Unit needs {State}
use_int () = {
  let x = get! ()
  put! (x + 1)
}

fun use_string : Unit -> Unit needs {State}
use_string () = {
  let s = get! ()
  put! (s <> \"!\")
}"
        )
        .is_ok()
    );
}

#[test]
fn generic_effect_put_then_get() {
    // Inference works when put constrains the type first, then get uses it
    assert!(
        check(
            "effect State s {
  fun get : Unit -> s
  fun put : (v: s) -> Unit
}

fun put_then_get : Unit -> Int needs {State}
put_then_get () = {
  put! 42
  get! ()
}"
        )
        .is_ok()
    );
}

#[test]
fn generic_effect_put_then_get_mismatch() {
    // put constrains s to Int, but return type is String -- should fail
    let result = check(
        "effect State s {
  fun get : Unit -> s
  fun put : (v: s) -> Unit
}

fun bad : Unit -> String needs {State}
bad () = {
  put! 42
  get! ()
}",
    );
    assert!(result.is_err());
}

#[test]
fn generic_effect_complex_type_param() {
    // Type param can be a complex type like List Int
    assert!(
        check(
            "effect State s {
  fun get : Unit -> s
  fun put : (v: s) -> Unit
}

type List a = Nil | Cons(a, List a)

handler list_state for State (List Int) {
  get () = resume Nil
  put v = resume ()
}"
        )
        .is_ok()
    );
}

#[test]
fn generic_effect_handler_return_clause() {
    // Return clause should work with the specialized type
    assert!(
        check(
            "effect State s {
  fun get : Unit -> s
  fun put : (v: s) -> Unit
}

type Result a = Ok(a) | Err(String)

handler safe_state for State Int {
  get () = resume 0
  put v = resume ()
  return value = Ok(value)
}"
        )
        .is_ok()
    );
}

#[test]
fn generic_effect_op_with_function_param() {
    // Effect op that takes a function over the type param
    assert!(
        check(
            "effect State s {
  fun get : Unit -> s
  fun put : (v: s) -> Unit
  fun modify : (f: s -> s) -> Unit
}

handler counter for State Int {
  get () = resume 0
  put v = resume ()
  modify f = resume ()
}

fun use_modify : Unit -> Unit needs {State}
use_modify () = {
  put! 10
  modify! (fun x -> x + x)
}",
        )
        .is_ok()
    );
}

#[test]
fn generic_effect_op_with_function_param_mismatch() {
    // modify takes (s -> s) but lambda has wrong type
    let result = check(
        "effect State s {
  fun get : Unit -> s
  fun put : (v: s) -> Unit
  fun modify : (f: s -> s) -> Unit
}

fun bad : Unit -> Unit needs {State}
bad () = {
  put! 42
  modify! (fun x -> \"not an int\")
}",
    );
    assert!(result.is_err());
}

#[test]
fn generic_effect_multi_param_partial_mismatch() {
    // Store k v: read constrains v to Int, write uses String for v -- should fail
    let result = check(
        "effect Store k v {
  fun read : (key: k) -> v
  fun write : (key: k) -> (data: v) -> Unit
}

fun bad : Unit -> Unit needs {Store}
bad () = {
  let x = read! \"key\"
  let _ = x + 1
  write! \"key\" \"not an int\"
}",
    );
    assert!(result.is_err());
}

#[test]
fn generic_effect_with_scopes_independent() {
    // Effect type params should be independent across with scopes
    assert!(
        check(
            "effect State s {
  fun get : Unit -> s
  fun put : (v: s) -> Unit
}

handler int_state for State Int {
  get () = resume 0
  put v = resume ()
}

handler string_state for State String {
  get () = resume \"\"
  put v = resume ()
}

fun use_int : Unit -> Unit needs {State}
use_int () = {
  let x = get! ()
  put! (x + 1)
}

fun use_string : Unit -> Unit needs {State}
use_string () = {
  let s = get! ()
  put! (s <> \"!\")
}

main () = {
  use_int () with int_state
  use_string () with string_state
}"
        )
        .is_ok()
    );
}

#[test]
fn generic_effect_needs_type_arg_constrains_body() {
    // needs {State Int} should constrain s=Int, so put! "hello" should fail
    let result = check(
        "effect State s {
  fun get : Unit -> s
  fun put : (v: s) -> Unit
}

fun bad : Unit -> Unit needs {State Int}
bad () = put! \"hello\"",
    );
    assert!(result.is_err());
}

#[test]
fn generic_effect_needs_type_arg_allows_matching_usage() {
    // needs {State Int} with consistent Int usage should pass
    assert!(
        check(
            "effect State s {
  fun get : Unit -> s
  fun put : (v: s) -> Unit
}

fun good : Unit -> Unit needs {State Int}
good () = {
  let x = get! ()
  put! (x + 1)
}"
        )
        .is_ok()
    );
}

#[test]
fn generic_effect_needs_type_arg_get_returns_correct_type() {
    // needs {State String} means get! returns String, so adding 1 should fail
    let result = check(
        "effect State s {
  fun get : Unit -> s
  fun put : (v: s) -> Unit
}

fun bad : Unit -> Int needs {State String}
bad () = {
  let x = get! ()
  x + 1
}",
    );
    assert!(result.is_err());
}

#[test]
fn generic_effect_needs_type_var_from_annotation() {
    // needs {State a} where a is a type var from the function signature
    // should link the effect's type param to the function's type param
    let result = check(
        "effect State s {
  fun get : Unit -> s
  fun put : (v: s) -> Unit
}

fun transform : (f: a -> a) -> a needs {State a}
transform f = {
  let x = get! ()
  let y = f x
  put! y
  y
}",
    );
    if let Err(e) = &result {
        eprintln!("ERROR: {:?}", e);
    }
    assert!(result.is_ok());
}

#[test]
fn generic_effect_needs_type_var_mismatch() {
    // needs {State a} but body treats a as both Int (s+1) and String (put! "hello")
    let result = check(
        "effect State s {
  fun get : Unit -> s
  fun put : (v: s) -> Unit
}

fun bad : (x: a) -> Int needs {State a}
bad x = {
  let s = get! ()
  put! \"hello\"
  s + 1
}",
    );
    assert!(result.is_err());
}

#[test]
fn generic_effect_effarrow_polymorphic_hof() {
    // A polymorphic HOF that takes an effectful callback and returns a type var
    // should be callable at different types (regression: EffArrow + return type var
    // caused generalization failure when prelude is loaded)
    assert!(
        check(
            "effect State s {
  fun get : Unit -> s
  fun put : (v: s) -> Unit
}

fun run_state : (init: s) -> (f: Unit -> a needs {State s}) -> (a, s)
run_state init f = {
  let state_fn = f () with {
    get () = fun s -> (resume s) s
    put new_s = fun _ -> (resume ()) new_s
    return value = fun s -> (value, s)
  }
  state_fn init
}

fun use_it : Unit -> Int
use_it () = {
  let (a, _) = run_state 0 (fun () -> get! ())
  let (b, _) = run_state \"\" (fun () -> get! ())
  a
}",
        )
        .is_ok()
    );
}

#[test]
fn handler_where_clause_allows_trait_methods() {
    // Where clause on handler should let arm bodies call trait methods on type params
    assert!(
        check(
            "effect Store s {
  fun save : s -> Unit
  fun load : Unit -> s
}

handler show_store for Store a where {a: Show} {
  save item = {
    let _ = show item
    resume ()
  }
  load () = resume (show 42)
}"
        )
        .is_ok()
    );
}

#[test]
fn handler_where_clause_with_needs_and_where() {
    // Handler with both needs and where clause should typecheck
    assert!(
        check(
            "effect Log {
  fun log : String -> Unit
}

effect Store s {
  fun save : s -> Unit
}

handler logged_store for Store a needs {Log} where {a: Show} {
  save item = {
    log! (show item)
    resume ()
  }
}"
        )
        .is_ok()
    );
}

#[test]
fn handler_where_clause_multiple_bounds() {
    // Multiple trait bounds on the same type param
    assert!(
        check(
            "effect Store s {
  fun save : s -> Unit
  fun load : Unit -> s
}

handler eq_show_store for Store a where {a: Show + Eq} {
  save item = {
    let _ = show item
    let _ = item == item
    resume ()
  }
  load () = resume (show 42)
}"
        )
        .is_ok()
    );
}

#[test]
fn handler_where_clause_unknown_type_var() {
    // Referencing a type var not in the effect's params should produce an error
    let result = check(
        "effect Store s {
  fun save : s -> Unit
  fun load : Unit -> s
}

handler bad for Store Int where {b: Show} {
  save item = resume ()
  load () = resume 42
}",
    );
    assert!(result.is_err());
}

#[test]
fn main_cannot_have_effects() {
    let result = check(
        "effect Log {
  fun log : (msg: String) -> Unit
}

# NB: main should not be annotated at all anyway
fun main : Unit -> Unit needs {Log}
main () = log! \"hello\"",
    );
    assert!(result.is_err());
    let err = result.err().expect("expected error");
    assert!(
        err.message.contains("cannot use `needs`"),
        "expected error about main + needs, got: {}",
        err.message
    );
}

#[test]
fn effect_forwarded_through_open_row_hof_reaches_main() {
    // Regression: a callback's effects flowing through a HOF's open effect row
    // (`..e`) must propagate to the caller, even when the saturating argument
    // comes *after* the callback in the call spine. The callback lambda is
    // deferred until after the saturating arg is processed, so the saturated
    // call's effects must be emitted only once the deferred lambda has bound the
    // row variable -- otherwise `{Boom}` would be silently dropped and `main`
    // would type-check despite never handling it.
    let result = check(
        "effect Boom {
  fun boom : (msg: String) -> a
}
fun risky : Int -> Int needs {Boom}
risky n = if n > 0 then n else boom! \"bad\"
fun call_with : (f: Int -> Int needs {..e}) -> (x: Int) -> Int needs {..e}
call_with f x = f x
main () = call_with (fun n -> risky n) 1",
    );
    assert!(
        result.is_err(),
        "main using an unhandled effect via an open-row HOF should not type-check"
    );
    let err = result.err().expect("expected error");
    assert!(
        err.message.contains("cannot use `needs`"),
        "expected error about main + needs, got: {}",
        err.message
    );
}

#[test]
fn effect_forwarded_through_open_row_hof_can_be_handled() {
    // The same forwarding must still allow the caller to discharge the effect
    // with a `with` handler -- the propagated effect is real, not spurious.
    let result = check(
        "effect Boom {
  fun boom : (msg: String) -> a
}
fun risky : Int -> Int needs {Boom}
risky n = if n > 0 then n else boom! \"bad\"
fun call_with : (f: Int -> Int needs {..e}) -> (x: Int) -> Int needs {..e}
call_with f x = f x
main () = call_with (fun n -> risky n) 1 with { boom msg = 0 }",
    );
    assert!(
        result.is_ok(),
        "handling the forwarded effect should type-check, got: {:?}",
        result.err()
    );
}

#[test]
fn parameterized_effect_pins_type_arg_from_body() {
    // `needs {Fail}` omits Fail's type argument. The omitted arg is a real
    // inferable slot, pinned from the body's usage, so a function that only
    // ever fails with a String is `Fail String` and a consistent program is
    // accepted.
    let result = check(
        "effect Fail e {
  fun fail : e -> a
}
fun parse : String -> Int needs {Fail}
parse s = fail! s
main () = parse \"x\" with { fail msg = String.length msg }",
    );
    assert!(
        result.is_ok(),
        "consistent single-type use of a parameterized effect should check, got: {:?}",
        result.err()
    );
}

#[test]
fn parameterized_effect_conflicting_instantiations_forwarded_is_error() {
    // Two functions forward `Fail` at different type arguments (`String` and
    // `Int`) into one caller. A parameterized effect has a single runtime
    // handler slot per family, so this must be a type error rather than a
    // silent runtime payload-type crash.
    let result = check(
        "effect Fail e {
  fun fail : e -> a
}
fun a : Int -> Int needs {Fail}
a n = fail! \"str\"
fun b : Int -> Int needs {Fail}
b n = fail! 99
fun both : Int -> Int needs {Fail}
both n = a n + b n
main () = both 1 with { fail msg = 0 }",
    );
    assert!(
        result.is_err(),
        "forwarding Fail String and Fail Int together should not type-check"
    );
    assert!(
        result
            .as_ref()
            .err()
            .map(|e| e.message.contains("conflicting types"))
            .unwrap_or(false),
        "expected an effect-conflict error, got: {:?}",
        result.err()
    );
}

#[test]
fn parameterized_effect_handler_payload_gets_concrete_type() {
    // The effect arrives at `main` via a function call (not a direct op call),
    // so the inline handler arm must still see the concrete payload type
    // (`String`). Using it at the wrong type (`msg + 1`) is a compile error,
    // not a runtime `badarith`.
    let result = check(
        "effect Fail e {
  fun fail : e -> a
}
fun parse : String -> Int needs {Fail}
parse s = fail! s
main () = parse \"x\" with { fail msg = msg + 1 }",
    );
    assert!(
        result.is_err(),
        "handler treating a String payload as Int should not type-check"
    );
}

#[test]
fn external_fun_cannot_have_effects() {
    let result = check(
        r#"
        @external("erlang", "file", "read_file")
        fun read_file : (path: String) -> String needs {IO}
        "#,
    );
    let err = result.err().expect("expected error");
    assert!(
        err.message.contains("external function") && err.message.contains("cannot declare effects"),
        "expected error about external + needs, got: {}",
        err.message
    );
}

// --- Impl body can call helper functions defined in the same file ---

#[test]
fn impl_body_calls_helper_function() {
    check(
        r#"
trait Display a {
    fun display : (x: a) -> String
}

fun helper : (n: Int) -> String
helper n = show n

type Wrapper = Wrapper(Int)

impl Display for Wrapper {
  display Wrapper(n) = "Wrapped: " <> helper n
}
"#,
    )
    .unwrap();
}

#[test]
fn impl_body_calls_unannotated_helper() {
    check(
        r#"
trait Display a {
    fun display : (x: a) -> String
}

helper n = show n

type Wrapper = Wrapper(Int)

impl Display for Wrapper {
    display Wrapper(n) = "Wrapped: " <> helper n
}
"#,
    )
    .unwrap();
}

#[test]
fn script_mode_allows_std_imports() {
    check("import Std.List\nlet xs = List.map (fun x -> x + 1) [1, 2, 3]").unwrap();
}

#[test]
fn script_mode_rejects_user_imports() {
    match check("import MyLib") {
        Err(err) => assert!(
            err.to_string().contains("project"),
            "expected project.toml hint, got: {}",
            err
        ),
        Ok(_) => panic!("should reject user import in script mode"),
    }
}

#[test]
fn local_function_simple() {
    check(
        r#"
let result = {
  let double x = x + 1
  double 5
}
"#,
    )
    .unwrap();
}

#[test]
fn local_function_recursive() {
    check(
        r#"
let result = {
  let fact n = if n == 0 then 1 else n * fact (n - 1)
  fact 5
}
"#,
    )
    .unwrap();
}

#[test]
fn local_function_multi_clause() {
    check(
        r#"
let result = {
  let fib 0 = 0
  let fib 1 = 1
  let fib n = fib (n - 1) + fib (n - 2)
  fib 10
}
"#,
    )
    .unwrap();
}

#[test]
fn derive_show_simple_enum() {
    check(
        r#"
type Color = Red | Green | Blue deriving (Show)
let x = show Red
"#,
    )
    .unwrap();
}

#[test]
fn derive_show_with_fields() {
    check(
        r#"
type Shape
  = Circle(Int)
  | Rect(Int, Int)
  | Point
  deriving (Show)
let x = show (Circle 5)
"#,
    )
    .unwrap();
}

#[test]
fn derive_show_polymorphic() {
    check(
        r#"
type Box a = Box(a) | Empty deriving (Show)
let x = show (Box 42)
"#,
    )
    .unwrap();
}

#[test]
fn derive_default_record() {
    check(
        r#"
record Settings { retries: Int, name: String, enabled: Bool } deriving (Default)
let x : Settings = default
let y = x.retries + 1
"#,
    )
    .unwrap();
}

#[test]
fn derive_default_parameterized_record() {
    check(
        r#"
record Box a { value: a, label: String } deriving (Default)
let x : Box Int = default
let y = x.value + 1
"#,
    )
    .unwrap();
}

#[test]
fn derive_default_record_does_not_require_phantom_param_default() {
    check(
        r#"
type Marker = Marker
record Phantom a { value: Int } deriving (Default)
let x : Phantom Marker = default
let y = x.value + 1
"#,
    )
    .unwrap();
}

#[test]
fn receive_requires_actor_effect() {
    let result = check(
        r#"
type Msg = Ping | Stop
foo () = receive {
  Ping -> 1
  Stop -> 0
}
"#,
    );
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message.contains("Actor"),
        "expected Actor error, got: {}",
        err.message
    );
}

#[test]
fn receive_typechecks_with_actor() {
    check(
        r#"
import Std.Actor (Actor)

type Msg = Ping | Stop

fun handle_msg : (x: Int) -> Int needs {Actor Msg}
handle_msg x = receive {
  Ping -> 1
  Stop -> 0
}
"#,
    )
    .unwrap();
}

#[test]
fn receive_after_timeout_must_be_int() {
    let result = check(
        r#"
import Std.Actor

type Msg = Ping

fun handle_msg : Unit -> Int needs {Actor Msg}
handle_msg () = receive {
  Ping -> 1
  after "not an int" -> 0
}
"#,
    );
    assert!(result.is_err());
}

#[test]
fn receive_no_exhaustiveness_error() {
    // Partial match in receive should not error (no exhaustiveness)
    check(
        r#"
import Std.Actor (Actor)

type Msg = A | B | C

fun handle_msg : Unit -> Int needs {Actor Msg}
handle_msg () = receive {
  A -> 1
}
"#,
    )
    .unwrap();
}

#[test]
fn imported_effect_resolves_in_nested_callback_annotation() {
    check(
        r#"
import Std.IO (Stdio)

@external("erlang", "repro", "raw")
fun raw : (Unit -> String needs {Stdio}) -> String
"#,
    )
    .unwrap();
}

#[test]
fn imported_effect_resolves_in_effect_op_callback_annotation() {
    check(
        r#"
import Std.IO (Stdio)

effect Pg {
  fun query : (decode: Unit -> String needs {Stdio}) -> String
}
"#,
    )
    .unwrap();
}

#[test]
fn conflicting_duplicate_effect_requirements_are_rejected() {
    let err = check(
        r#"
import Std.Actor (Process, Actor)

fun mixed_actor_messages : Unit -> String needs {Process, Actor Unit, Actor String}
mixed_actor_messages () = "ok"
"#,
    )
    .err()
    .expect("expected conflicting Actor effect error");

    assert!(
        err.message.contains("conflicting effect requirements"),
        "expected conflict error, got: {}",
        err.message
    );
    assert!(
        err.message.contains("Actor Unit") && err.message.contains("Actor String"),
        "expected both Actor instantiations in error, got: {}",
        err.message
    );
}

#[test]
fn with_rejects_mixed_effect_instantiations_for_inline_handler() {
    let err = check(
        r#"
import Std.Fail (Fail)

type AppError =
  | HttpError String
  | DbError String
  | ValidationError String

fun run_app : Unit -> Unit needs {Fail AppError}
run_app () = fail! (HttpError "oops")

fun run_app2 : Unit -> Unit needs {Fail String}
run_app2 () = fail! "something"

main () = {
  run_app ()
  run_app2 ()
} with {
  fail _ = ()
}
"#,
    )
    .err()
    .expect("expected mixed Fail instantiations to be rejected");

    assert!(
        err.message.contains("single `with`"),
        "expected with-scope conflict error, got: {}",
        err.message
    );
    assert!(
        err.message.contains("Fail AppError") && err.message.contains("Fail String"),
        "expected both Fail instantiations in error, got: {}",
        err.message
    );
}

#[test]
fn with_rejects_mixed_effect_instantiations_for_named_handler() {
    let err = check(
        r#"
import Std.Fail (Fail)

type AppError = HttpError String

handler app_fail for Fail AppError {
  fail _ = ()
}

fun run_app : Unit -> Unit needs {Fail AppError}
run_app () = fail! (HttpError "oops")

fun run_app2 : Unit -> Unit needs {Fail String}
run_app2 () = fail! "something"

main () = {
  run_app ()
  run_app2 ()
} with app_fail
"#,
    )
    .err()
    .expect("expected named handler to reject mixed Fail instantiations");

    assert!(
        err.message.contains("Fail AppError") && err.message.contains("Fail String"),
        "expected both Fail instantiations in error, got: {}",
        err.message
    );
}

#[test]
fn with_rejects_mixed_effect_instantiations_for_handler_binding() {
    let err = check(
        r#"
import Std.Fail (Fail)

type AppError = HttpError String

handler app_fail for Fail AppError {
  fail _ = ()
}

fun run_app : Unit -> Unit needs {Fail AppError}
run_app () = fail! (HttpError "oops")

fun run_app2 : Unit -> Unit needs {Fail String}
run_app2 () = fail! "something"

main () = {
  let h = app_fail
  {
    run_app ()
    run_app2 ()
  } with h
}
"#,
    )
    .err()
    .expect("expected handler binding to reject mixed Fail instantiations");

    assert!(
        err.message.contains("Fail AppError") && err.message.contains("Fail String"),
        "expected both Fail instantiations in error, got: {}",
        err.message
    );
}

#[test]
fn with_accepts_same_effect_instantiation_multiple_times() {
    check(
        r#"
import Std.Fail (Fail)

type AppError =
  | HttpError String
  | DbError String

handler app_fail for Fail AppError {
  fail _ = ()
}

fun run_app : Unit -> Unit needs {Fail AppError}
run_app () = fail! (HttpError "oops")

fun run_app2 : Unit -> Unit needs {Fail AppError}
run_app2 () = fail! (DbError "still bad")

main () = {
  run_app ()
  run_app2 ()
} with app_fail
"#,
    )
    .unwrap();
}

#[test]
fn nested_with_can_translate_between_effect_instantiations() {
    check(
        r#"
import Std.Fail (Fail)

type AppError =
  | HttpError String
  | ValidationError String

fun run_app : Unit -> Unit needs {Fail AppError}
run_app () = fail! (HttpError "oops")

fun run_app2 : Unit -> Unit needs {Fail String}
run_app2 () = fail! "something"

fun combined : Unit -> Unit needs {Fail AppError}
combined () = {
  run_app ()
  run_app2 () with {
    fail msg = fail! (ValidationError msg)
  }
}
"#,
    )
    .unwrap();
}

#[test]
fn error_messages_show_resolved_types() {
    // Type mismatch should show concrete type names, not ?-variables
    let err = check("fun f : (x: Int) -> String\nf x = x")
        .err()
        .expect("expected type error");
    assert!(
        err.message.contains("Int") && err.message.contains("String"),
        "error should show concrete types, got: {}",
        err.message
    );
    assert!(
        !err.message.contains('?'),
        "error should not contain ?-variables, got: {}",
        err.message
    );
}

#[test]
fn error_messages_show_resolved_types_with_constructors() {
    // Passing wrong type to a function should show the actual types
    let err = check(
        r#"
fun add : (a: Int) -> (b: Int) -> Int
add a b = a + b

main () = add "hello" 1
"#,
    )
    .err()
    .expect("expected type error");
    assert!(
        err.message.contains("String") || err.message.contains("Int"),
        "error should show concrete types, got: {}",
        err.message
    );
    assert!(
        !err.message.contains('?'),
        "error should not contain ?-variables, got: {}",
        err.message
    );
}

// --- Type-at-span recording tests ---

#[test]
fn type_at_span_records_function_params() {
    // Function params go through bind_pattern which records the type (Pat -> type_at_span)
    let checker = check("fun foo : (x: Int) -> Int\nfoo x = x").unwrap();
    let result = checker.to_result();
    let types: Vec<_> = result
        .type_at_span
        .values()
        .map(|ty| format!("{}", result.sub.apply(ty)))
        .collect();
    assert!(
        types.iter().any(|ty| ty == "Int"),
        "expected Int for param x, got: {:?}",
        types
    );
}

#[test]
fn type_at_node_records_locals_in_body() {
    // Let bindings inside function bodies are the main LSP hover use case.
    // Pat bindings go to type_at_span, Expr usage refs go to type_at_node.
    let checker = check("main () = {\n  let x = 42\n  let y = x\n  y\n}").unwrap();
    let result = checker.to_result();
    let pat_types: Vec<_> = result
        .type_at_span
        .values()
        .map(|ty| format!("{}", result.sub.apply(ty)))
        .collect();
    let expr_types: Vec<_> = result
        .type_at_node
        .values()
        .map(|ty| format!("{}", result.sub.apply(ty)))
        .collect();
    let all_types: Vec<_> = pat_types.iter().chain(expr_types.iter()).collect();
    let int_count = all_types.iter().filter(|ty| **ty == "Int").count();
    assert!(
        int_count >= 3,
        "expected at least 3 Int entries (x bind, x use, y bind), got {} in {:?}",
        int_count,
        all_types
    );
}

#[test]
fn type_at_span_records_case_bindings() {
    let checker = check(
        r#"
type Maybe a = Just(a) | Nothing
main () = case Just 42 {
  Just(x) -> x
  Nothing -> 0
}
"#,
    )
    .unwrap();
    let result = checker.to_result();
    let types: Vec<_> = result
        .type_at_span
        .values()
        .map(|ty| format!("{}", result.sub.apply(ty)))
        .collect();
    assert!(
        types.iter().any(|ty| ty == "Int"),
        "expected Int for case-bound x, got: {:?}",
        types
    );
}

#[test]
fn type_at_span_has_exact_span_text() {
    // Verify that spans in type_at_span and type_at_node map to exactly the
    // variable name (no leading/trailing whitespace).
    let src = "record House { year_built: Int }\nmain () = {\n  let house = House { year_built: 2005 }\n  house\n}";
    let checker = check(src).unwrap();
    let result = checker.to_result();
    for span in result.type_at_span.keys() {
        if span.end <= src.len() {
            let text = &src[span.start..span.end];
            assert_eq!(
                text,
                text.trim(),
                "type_at_span contains whitespace: {:?}",
                text
            );
        }
    }
    for node_id in result.type_at_node.keys() {
        if let Some(span) = result.node_spans.get(node_id)
            && span.end <= src.len()
        {
            let text = &src[span.start..span.end];
            assert_eq!(
                text,
                text.trim(),
                "type_at_node span contains whitespace: {:?}",
                text
            );
        }
    }
}

// --- Effect op name collision tests ---

#[test]
fn ambiguous_unqualified_effect_op_is_error() {
    // Two effects define the same op name; unqualified call should error
    let result = check(
        "effect A {
  fun ping : Unit -> Int
}
effect B {
  fun ping : Unit -> Int
}
main x = ping!",
    );
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message.contains("ambiguous"),
        "expected ambiguity error, got: {}",
        err.message
    );
}

#[test]
fn qualified_effect_op_resolves_ambiguity() {
    // Two effects with same op name; qualified call should work
    check(
        "effect A {
  fun ping : Unit -> Int
}
effect B {
  fun ping : Unit -> String
}
fun foo : (x: Int) -> Int needs {A}
foo x = A.ping! ()",
    )
    .unwrap();
}

#[test]
fn multi_effect_handler_op_name_collision_is_error() {
    // Handler for two effects that share an op name should error on ambiguity
    let result = check(
        "effect A {
  fun ping : Unit -> Int
}
effect B {
  fun ping : Unit -> String
}
handler h for A, B {
  ping () = resume 0
}",
    );
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message.contains("ambiguous"),
        "expected ambiguity error, got: {}",
        err.message
    );
}

#[test]
fn multi_effect_handler_no_collision_works() {
    // Handler for two effects with distinct op names should work fine
    check(
        "effect Logger {
  fun log : (msg: String) -> Unit
}
effect Counter {
  fun inc : Unit -> Unit
}
handler h for Logger, Counter {
  log msg = resume ()
  inc () = resume ()
}",
    )
    .unwrap();
}

#[test]
fn duplicate_handler_arm_is_error() {
    // Same op name twice in one handler should error
    let result = check(
        "effect Foo {
  fun a : Unit -> Int
  fun b : Unit -> Int
}
handler foo for Foo {
  a () = 1
  b () = 2
  b () = 3
}",
    );
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message.contains("duplicate"),
        "expected duplicate error, got: {}",
        err.message
    );
}

#[test]
fn duplicate_impl_method_is_error() {
    let result = check(
        "trait Foo a {
  fun a : (x: a) -> Int
}
impl Foo for String {
  a _ = 42
  a _ = 43
}",
    );
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message.contains("duplicate"),
        "expected duplicate method error, got: {}",
        err.message
    );
}

#[test]
fn duplicate_impl_for_same_type_is_error() {
    let result = check(
        "trait Foo a {
  fun a : (x: a) -> Int
}
impl Foo for String {
  a _ = 42
}
impl Foo for String {
  a _ = 43
}",
    );
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message.contains("duplicate impl") || err.message.contains("already implemented"),
        "expected duplicate impl error, got: {}",
        err.message
    );
}

#[test]
fn duplicate_impl_for_parameterized_type_is_error() {
    let result = check(
        "trait MyShow a {
  fun my_show : (x: a) -> String
}
impl MyShow for List a {
  my_show _ = \"list1\"
}
impl MyShow for List a {
  my_show _ = \"list2\"
}",
    );
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message.contains("duplicate impl") || err.message.contains("already implemented"),
        "expected duplicate impl error, got: {}",
        err.message
    );
}

#[test]
fn derive_plus_handwritten_impl_is_error() {
    let result = check(
        "record Foo { x: Int } deriving (Show)
impl Show for Foo {
  show _ = \"foo\"
}",
    );
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message.contains("duplicate impl") || err.message.contains("already implemented"),
        "expected duplicate impl error from derive+handwritten collision, got: {}",
        err.message
    );
}

#[test]
fn different_traits_same_type_no_collision() {
    check(
        "trait TA a { fun fa : (x: a) -> Int }
trait TB a { fun fb : (x: a) -> Int }
impl TA for String { fa _ = 1 }
impl TB for String { fb _ = 2 }",
    )
    .unwrap();
}

#[test]
fn coherence_identical_args_caught_by_overlap() {
    let result = check(
        "trait Generic a r {
  fun to : (x: a) -> r
}
type RepA = RepA
record Foo { x: Int }
impl Generic RepA for Foo {
  to _ = RepA
}
impl Generic RepA for Foo {
  to _ = RepA
}",
    );
    assert!(result.is_err(), "expected duplicate impl error");
    let err = result.err().unwrap();
    assert!(
        err.message.contains("duplicate impl") || err.message.contains("already implemented"),
        "expected duplicate impl error, got: {}",
        err.message
    );
}

#[test]
fn coherence_different_first_params_no_violation() {
    // The trait param `r` appears in both param and return position so the
    // impl unification stays local to each impl; pre-existing limitation of
    // phantom-r multi-param traits means we cannot exercise two impls where
    // `r` is only return-position. The coherence rule itself targets
    // (target_type, trait_type_args) and would reject mismatches; this test
    // confirms differing first params (different target types) are accepted.
    check(
        // Same trait arg (RepA) but different targets — coherence is
        // per-target, so both impls are allowed.  Multi-impl tests with
        // *different* trait args trip a pre-existing limitation: the trait
        // method's non-self type vars (the `r` in `Generic a r`) are shared
        // across impl checks, so the second impl's body would fail to unify.
        // That's orthogonal to the coherence rule under test here.
        "trait Generic a r {
  fun to : (x: a) -> r
}
type RepA = RepA
record Foo { x: Int }
record Bar { y: Int }
impl Generic RepA for Foo {
  to _ = RepA
}
impl Generic RepA for Bar {
  to _ = RepA
}",
    )
    .unwrap();
}

#[test]
fn multi_param_trait_distinct_impls_freshen_vars() {
    // Two impls of `Generic a r` with different first AND second params.
    // Coherence allows this (different first params); the freshening fix
    // ensures the trait's `r` var is fresh per impl so unification doesn't
    // leak across impls.
    check(
        "trait Generic a r {
  fun to : (x: a) -> r
  fun from : (x: r) -> a
}
record Foo { x: Int }
record Bar { y: Int }
type RepFoo = RepFoo Int
type RepBar = RepBar Int
impl Generic RepFoo for Foo {
  to f = RepFoo f.x
  from r = case r { RepFoo n -> Foo { x: n } }
}
impl Generic RepBar for Bar {
  to b = RepBar b.y
  from r = case r { RepBar n -> Bar { y: n } }
}",
    )
    .unwrap();
}

// --- Phase 1c: TraitApp where-clause form ---

#[test]
fn where_app_old_form_sugar_still_works() {
    // Old-form `where {a: Show}` should continue to typecheck unchanged.
    check(
        "trait Show2 a { fun show2 : (x: a) -> String }
impl Show2 for Int { show2 _ = \"int\" }
fun foo : (x: a) -> String where {a: Show2}
foo x = show2 x",
    )
    .unwrap();
}

#[test]
fn free_function_with_existential_where_clause_typechecks() {
    // `fun via_generic : a -> String where {a: Generic r, r: ToJson}`
    // introduces `r` as an existential — it's not free in `a -> String`.
    // The constraint on `r` must survive instantiation at call sites so the
    // FUNCTIONAL_TRAITS coherence rule can pin `r` from the concrete `a`,
    // and the elaborator can thread both dictionaries. Regression for the
    // bug where the existential constraint was dropped from the scheme,
    // causing the user argument to land in the second dict slot.
    check(
        "trait Generic a r {
  fun to : (x: a) -> r
}
trait ToJson a {
  fun to_json : (x: a) -> String
}
record Person { name: String }
type RepPerson = RepPerson String
impl Generic RepPerson for Person {
  to p = RepPerson p.name
}
impl ToJson for RepPerson {
  to_json r = case r { RepPerson s -> s }
}
fun via_generic : (x: a) -> String where {a: Generic r, r: ToJson}
via_generic x = to_json (to x)
fun caller : (p: Person) -> String
caller p = via_generic p",
    )
    .unwrap();
}

#[test]
fn where_app_unknown_trait_errors() {
    let result = check(
        "record Person { name: String }
impl Show for Person where {NotATrait Person r} {
  show _ = \"x\"
}",
    );
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message.contains("unknown trait") || err.message.contains("NotATrait"),
        "expected unknown-trait error, got: {}",
        err.message
    );
}

#[test]
fn where_app_fresh_var_in_non_functional_trait_errors() {
    let result = check(
        "trait NotFn a b { fun nf : (x: a) -> b }
record Person { name: String }
impl Show for Person where {NotFn Person r} {
  show _ = \"x\"
}",
    );
    assert!(
        result.is_err(),
        "expected error for non-functional fresh var"
    );
    let err = result.err().unwrap();
    assert!(
        err.message.contains("fresh type variable not determined")
            || err.message.contains("not a functional trait"),
        "expected functional-trait error, got: {}",
        err.message
    );
}

#[test]
fn same_trait_different_types_no_collision() {
    check(
        "trait TA a { fun fa : (x: a) -> Int }
impl TA for String { fa _ = 1 }
impl TA for Int { fa _ = 2 }",
    )
    .unwrap();
}

// --- Type arity checking ---

#[test]
fn type_arity_too_many_args_builtin_list() {
    let result = check("fun foo : (x: List Int String) -> Int\nfoo x = 1");
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message.contains("expects 1 type argument") && err.message.contains("given 2"),
        "expected arity error, got: {}",
        err.message
    );
}

#[test]
fn type_arity_too_many_args_user_type() {
    let result = check("type Box a = Box(a)\nfun foo : (x: Box Int String) -> Int\nfoo x = 1");
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message.contains("expects 1 type argument") && err.message.contains("given 2"),
        "expected arity error, got: {}",
        err.message
    );
}

#[test]
fn type_arity_nullary_with_args() {
    let result = check("fun foo : (x: Int String) -> Int\nfoo x = 1");
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message.contains("expects 0 type arguments") && err.message.contains("given 1"),
        "expected arity error, got: {}",
        err.message
    );
}

#[test]
fn type_arity_correct_usage() {
    // These should all pass without error
    check("fun foo : (x: List Int) -> Int\nfoo x = 1").unwrap();
    check("fun foo : (x: Maybe Int) -> Int\nfoo _ = 1").unwrap();
    check("fun foo : (x: Result String Int) -> Int\nfoo _ = 1").unwrap();
}

#[test]
fn type_arity_too_many_args_maybe() {
    let result = check("fun foo : (x: Maybe Int Float) -> Int\nfoo _ = 1");
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message.contains("Maybe") && err.message.contains("expects 1 type argument"),
        "expected arity error for Maybe, got: {}",
        err.message
    );
}

#[test]
fn references_map_populated() {
    let checker = check("id x = x\nmain () = id 42").unwrap();
    let result = checker.to_result();

    // env tracks definition NodeIds for top-level functions
    let id_def = result.env.def_id("id");
    assert!(id_def.is_some(), "env should have def_id for 'id'");

    // The resolution map has entries (usage -> definition)
    assert!(
        result.references.len() >= 2,
        "expected at least 2 references (x in body + id in main), got {}",
        result.references.len()
    );

    // At least one reference points to the 'id' definition
    let id_def_id = id_def.unwrap();
    let id_refs: Vec<_> = result
        .references
        .values()
        .filter(|&&def_id| def_id == id_def_id)
        .collect();
    assert!(
        !id_refs.is_empty(),
        "should have at least one reference to 'id'"
    );
}

// --- Partial application effect tests ---

#[test]
fn partial_application_pure_function_typechecks() {
    check("fun myAdd : Int -> Int -> Int\nmyAdd a b = a + b\nincrement = myAdd 1\nmain () = dbg (show (increment 6))").unwrap();
}

#[test]
fn partial_application_effectful_defers_effects() {
    // Partial application of an effectful function should not propagate
    // effects to the enclosing scope; they're deferred to the call site
    check(
        "effect Boom {\n  fun boom : (msg: String) -> a\n}\nfun risky : Int -> Int -> Int needs {Boom}\nrisky a b = a + b\nmain () = {\n  let f = risky 1\n  f 2 with { boom msg = 0 }\n}",
    )
    .unwrap();
}

#[test]
fn partial_application_effectful_no_handler_is_error() {
    let result = check(
        "effect Boom {\n  fun boom : (msg: String) -> a\n}\nfun risky : Int -> Int -> Int needs {Boom}\nrisky a b = a + b\nmain () = {\n  let f = risky 1\n  f 2\n}",
    );
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message.contains("Boom"),
        "expected Boom effect error, got: {}",
        err.message
    );
}

#[test]
fn with_on_partial_application_is_error() {
    let result = check(
        "effect Boom {\n  fun boom : (msg: String) -> a\n}\nhandler safe for Boom {\n  boom msg = 0\n}\nfun risky : Int -> Int -> Int needs {Boom}\nrisky a b = a + b\nmain () = {\n  let _ = risky 1 with safe\n  0\n}",
    );
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message.contains("type mismatch") || err.message.contains("unnecessary"),
        "expected type mismatch or unnecessary handler message, got: {}",
        err.message
    );
}

#[test]
fn imported_handler_factory_with_private_effect_typechecks() {
    let db_module = r#"module Db

effect Postgres {
  fun ping : Unit -> Unit
}

pub fun run : Unit -> Unit needs {Postgres}
run () = ping! ()

pub fun connect : Unit -> Handler Postgres
connect () = handler for Postgres {
  ping () = resume ()
}
"#;

    let main_src = r#"import Db (connect, run)

main () = {
  let db = connect ()
  {
    run ()
  } with db
}
"#;

    check_with_project_files(&[("lib/Db.saga", db_module)], main_src).unwrap();
}

fn env_module_source() -> &'static str {
    r#"module Env

pub effect Env {
  fun get : String -> String
}

pub handler system_env for Env {
  get key = resume "value"
}
"#
}

#[test]
fn imported_handler_does_not_expose_private_effect_op_bare() {
    let main_src = r#"import Env (system_env)

main () = get! "HOME" with system_env
"#;

    let err = match check_with_project_files(&[("lib/Env.saga", env_module_source())], main_src) {
        Ok(_) => panic!("expected bare private effect op to be unavailable"),
        Err(err) => err,
    };
    assert!(
        err.message.contains("undefined effect operation: get"),
        "expected undefined bare op error, got: {}",
        err.message
    );
}

#[test]
fn exposing_effect_exposes_its_ops_bare() {
    let main_src = r#"import Env (Env, system_env)

main () = get! "HOME" with system_env
"#;

    check_with_project_files(&[("lib/Env.saga", env_module_source())], main_src).unwrap();
}

#[test]
fn imported_effect_op_remains_available_qualified_without_exposing() {
    let main_src = r#"import Env

main () = Env.Env.get! "HOME" with Env.system_env
"#;

    check_with_project_files(&[("lib/Env.saga", env_module_source())], main_src).unwrap();
}

#[test]
fn exposed_imported_effect_ops_with_same_name_are_ambiguous() {
    let a_module = r#"module A

pub effect Store {
  fun get : Unit -> Int
}

pub handler store for Store {
  get () = resume 1
}
"#;
    let b_module = r#"module B

pub effect Cache {
  fun get : Unit -> Int
}

pub handler cache for Cache {
  get () = resume 2
}
"#;
    let main_src = r#"import A (Store, store)
import B (Cache, cache)

main () = get! () with {store, cache}
"#;

    let err = match check_with_project_files(
        &[("lib/A.saga", a_module), ("lib/B.saga", b_module)],
        main_src,
    ) {
        Ok(_) => panic!("expected ambiguous bare effect op"),
        Err(err) => err,
    };
    assert!(
        err.message
            .contains("ambiguous effect operation 'get': found in [A.Store, B.Cache]"),
        "expected ambiguous effect op error with candidate list, got: {}",
        err.message
    );
}

#[test]
fn local_effect_op_shadows_imported_when_names_collide() {
    // Locally defined effects shadow imports for bare op resolution. Same
    // tier rule as trait methods.
    let env_module = r#"module Env

pub effect Env {
  fun get : String -> String
}

pub handler system_env for Env {
  get key = resume "imported-value"
}
"#;
    let main_src = r#"import Env (Env, system_env)

effect Local {
  fun get : String -> String
}

handler local_env for Local {
  get key = resume "local-value"
}

main () = get! "HOME" with local_env
"#;
    check_with_project_files(&[("lib/Env.saga", env_module)], main_src).unwrap();
}

#[test]
fn ambiguous_local_effect_ops_error_with_candidate_list() {
    // Two locally defined effects with the same op name produce a proper
    // ambiguous diagnostic listing the candidates.
    let main_src = r#"effect A {
  fun foo : Unit -> Int
}

effect B {
  fun foo : Unit -> Int
}

handler a_h for A { foo () = resume 1 }
handler b_h for B { foo () = resume 2 }

main () = foo! () with {a_h, b_h}
"#;
    let err = match check(main_src) {
        Ok(_) => panic!("expected ambiguous bare effect op"),
        Err(err) => err,
    };
    assert!(
        err.message
            .contains("ambiguous effect operation 'foo': found in [A, B]"),
        "expected ambiguous effect op error with candidate list, got: {}",
        err.message
    );
}

#[test]
fn only_exposed_imported_effect_op_is_bare_visible_when_names_collide() {
    let a_module = r#"module A

pub effect Store {
  fun get : Unit -> Int
}

pub handler store for Store {
  get () = resume 1
}
"#;
    let b_module = r#"module B

pub effect Cache {
  fun get : Unit -> Int
}

pub handler cache for Cache {
  get () = resume 2
}
"#;
    let main_src = r#"import A (Store, store)
import B (cache)

main () = get! () with store
"#;

    check_with_project_files(
        &[("lib/A.saga", a_module), ("lib/B.saga", b_module)],
        main_src,
    )
    .unwrap();
}

#[test]
fn effect_ops_cannot_be_exposed_directly() {
    let main_src = r#"import Env (get)

main () = Env.Env.get! "HOME" with Env.system_env
"#;

    let err = match check_with_project_files(&[("lib/Env.saga", env_module_source())], main_src) {
        Ok(_) => panic!("expected direct op exposing to be rejected"),
        Err(err) => err,
    };
    assert!(
        err.message
            .contains("'get' is not exported by module 'Env'"),
        "expected invalid import error, got: {}",
        err.message
    );
}

// --- Trait scope routing tests ---

fn describe_module_source() -> &'static str {
    r#"module Describe

pub trait Describe a {
  fun describe : a -> String
}

pub fun describe_thing : a -> String where {a: Describe}
describe_thing x = describe x
"#
}

#[test]
fn imported_module_does_not_expose_trait_method_bare() {
    let main_src = r#"import Describe (describe_thing)

main () = describe 42
"#;
    let err = match check_with_project_files(
        &[("lib/Describe.saga", describe_module_source())],
        main_src,
    ) {
        Ok(_) => panic!("expected bare trait method to be unavailable"),
        Err(err) => err,
    };
    assert!(
        err.message.contains("undefined variable: describe"),
        "expected undefined-variable error, got: {}",
        err.message
    );
}

#[test]
fn exposing_trait_exposes_its_methods_bare() {
    let main_src = r#"import Describe (Describe)

impl Describe for Int {
  describe x = "int"
}

main () = describe 42
"#;
    check_with_project_files(&[("lib/Describe.saga", describe_module_source())], main_src).unwrap();
}

#[test]
fn imported_trait_method_remains_available_qualified_without_exposing() {
    let main_src = r#"import Describe

impl Describe.Describe for Int {
  describe x = "int"
}

main () = Describe.Describe.describe 42
"#;
    check_with_project_files(&[("lib/Describe.saga", describe_module_source())], main_src).unwrap();
}

#[test]
fn exposed_imported_trait_methods_with_same_name_are_ambiguous() {
    let a_module = r#"module A

pub trait Foo a {
  fun pp : a -> String
}
"#;
    let b_module = r#"module B

pub trait Bar a {
  fun pp : a -> String
}
"#;
    let main_src = r#"import A (Foo)
import B (Bar)

impl Foo for Int { pp x = "a" }
impl Bar for Int { pp x = "b" }

main () = pp 1
"#;

    let err = match check_with_project_files(
        &[("lib/A.saga", a_module), ("lib/B.saga", b_module)],
        main_src,
    ) {
        Ok(_) => panic!("expected ambiguous bare trait method"),
        Err(err) => err,
    };
    assert!(
        err.message
            .contains("ambiguous trait method 'pp': found in [A.Foo, B.Bar]"),
        "expected ambiguous trait method error with candidate list, got: {}",
        err.message
    );
}

#[test]
fn ambiguous_local_trait_methods_error_with_candidate_list() {
    // Two locally defined traits with the same method name produce a proper
    // ambiguous diagnostic listing the candidate traits — mirrors the
    // effects parallel.
    let main_src = r#"trait A a {
  fun foo : a -> Int
}

trait B a {
  fun foo : a -> Int
}

impl A for Int { foo x = 1 }
impl B for Int { foo x = 2 }

main () = foo 1
"#;
    let err = match check(main_src) {
        Ok(_) => panic!("expected ambiguous bare trait method"),
        Err(err) => err,
    };
    assert!(
        err.message
            .contains("ambiguous trait method 'foo': found in [A, B]"),
        "expected ambiguous trait method error with candidate list, got: {}",
        err.message
    );
}

#[test]
fn only_exposed_imported_trait_method_is_bare_visible_when_names_collide() {
    let a_module = r#"module A

pub trait Foo a {
  fun pp : a -> String
}
"#;
    let b_module = r#"module B

pub trait Bar a {
  fun pp : a -> String
}

pub fun b_helper : Unit -> Unit
b_helper () = ()
"#;
    let main_src = r#"import A (Foo)
import B (b_helper)

impl Foo for Int { pp x = "a" }
impl B.Bar for Int { pp x = "b" }

main () = pp 1
"#;
    check_with_project_files(
        &[("lib/A.saga", a_module), ("lib/B.saga", b_module)],
        main_src,
    )
    .unwrap();
}

#[test]
fn trait_methods_cannot_be_exposed_directly() {
    let main_src = r#"import Describe (describe)

main () = ()
"#;
    let err = match check_with_project_files(
        &[("lib/Describe.saga", describe_module_source())],
        main_src,
    ) {
        Ok(_) => panic!("expected direct method exposing to be rejected"),
        Err(err) => err,
    };
    assert!(
        err.message
            .contains("'describe' is not exported by module 'Describe'"),
        "expected invalid import error, got: {}",
        err.message
    );
}

#[test]
fn local_trait_methods_remain_bare_visible() {
    check(
        r#"trait Local a {
  fun lm : a -> Int
}

impl Local for Int {
  lm x = x
}

main () = lm 42
"#,
    )
    .unwrap();
}

#[test]
fn local_trait_method_shadows_imported_when_names_collide() {
    // When a local trait and an imported trait both contribute the same bare
    // method name, the local trait's method wins for bare resolution. The
    // resolver records nothing for the ambiguous union and inference falls
    // back to the bare env entry, which only the local trait registers.
    let main_src = r#"import Describe (Describe)

trait LocalDescribe a {
  fun describe : a -> String
}

impl Describe for Int { describe x = "int" }
impl LocalDescribe for Int { describe x = "local-int" }

main () = describe 42
"#;
    check_with_project_files(&[("lib/Describe.saga", describe_module_source())], main_src).unwrap();
}

#[test]
fn imported_handler_binding_inside_wrapped_block_typechecks_in_inline_list() {
    let db_module = r#"module Db

effect Postgres {
  fun ping : Unit -> Unit
}

pub fun run : Unit -> Unit needs {Postgres}
run () = ping! ()

pub fun connect : Unit -> Handler Postgres
connect () = handler for Postgres {
  ping () = resume ()
}
"#;

    let main_src = r#"import Std.IO (console)
import Db (connect, run)

main () = {
  let db = connect ()
  {
    run ()
    println "ok"
  }
} with {db, console}
"#;

    let checker = check_with_project_files(&[("lib/Db.saga", db_module)], main_src).unwrap();
    assert!(
        !checker
            .collected_diagnostics
            .iter()
            .any(|d| d.message.contains("unused variable: `db`")),
        "unexpected diagnostics: {:?}",
        checker
            .collected_diagnostics
            .iter()
            .map(|d| d.message.clone())
            .collect::<Vec<_>>()
    );
}

#[test]
fn imported_record_tuple_pattern_lambda_argument_typechecks_through_push_values_shape() {
    let db_module = r#"module Db

pub record WindDetails {
  wind_avg: Int,
  wind_gust: Int,
  sesh_type: String,
}

pub fun make_wind : Int -> Int -> String -> WindDetails
make_wind wind_avg wind_gust sesh_type =
  WindDetails { wind_avg: wind_avg, wind_gust: wind_gust, sesh_type: sesh_type }

pub fun push_values : (rows: List a) -> (bind_row: a -> List Int) -> List Int
push_values rows bind_row = List.flat_map bind_row rows
"#;

    let input_module = r#"module Input

pub record Normalized {
  wind_avg: Maybe Int,
  wind_gust: Maybe Int,
  sesh_type: Maybe String,
}
"#;

    let main_src = r#"import Db (make_wind, push_values)
import Input (Normalized)

rows = [
  (1, make_wind 10 20 "spot"),
]

main () =
  push_values rows (fun (sesh_id, wd) -> [
    sesh_id,
    wd.wind_avg,
    wd.wind_gust,
  ])
"#;

    check_with_project_files(
        &[("lib/Db.saga", db_module), ("lib/Input.saga", input_module)],
        main_src,
    )
    .unwrap();
}

#[test]
fn imported_record_first_argument_lambda_typechecks_through_filter_map_shape() {
    let db_module = r#"module Db

pub record WindDetails {
  wind_avg: Int,
  wind_gust: Int,
}

pub fun make_wind : Int -> Int -> WindDetails
make_wind wind_avg wind_gust =
  WindDetails { wind_avg: wind_avg, wind_gust: wind_gust }
"#;

    let input_module = r#"module Input

pub record Normalized {
  wind_avg: Maybe Int,
  wind_gust: Maybe Int,
}
"#;

    let main_src = r#"import Db (make_wind)
import Input (Normalized)

rows = [
  (1, make_wind 10 20),
]

main () =
  List.filter_map (fun pair -> case pair {
    (sesh_id, wd) -> Just (wd.wind_avg + sesh_id)
  }) rows
"#;

    check_with_project_files(
        &[("lib/Db.saga", db_module), ("lib/Input.saga", input_module)],
        main_src,
    )
    .unwrap();
}

#[test]
fn with_on_pure_call_is_warning() {
    let checker = check(
        "effect Boom {\n  fun boom : (msg: String) -> a\n}\nfun myAdd : Int -> Int -> Int\nmyAdd a b = a + b\nmain () = myAdd 1 2 with { boom msg = 0 }",
    )
    .unwrap();
    assert!(
        checker.collected_diagnostics.iter().any(|d| {
            matches!(d.severity, Severity::Warning) && d.message.contains("unnecessary")
        }),
        "expected unnecessary handler warning"
    );
}

#[test]
fn effects_propagate_at_saturation_not_reference() {
    // Referencing an effectful function without calling it should not
    // propagate effects (they propagate when fully saturated)
    check(
        "effect Boom {\n  fun boom : (msg: String) -> a\n}\nfun risky : Int -> Int needs {Boom}\nrisky x = x\nmain () = {\n  let f = risky\n  f 1 with { boom msg = 0 }\n}",
    )
    .unwrap();
}

#[test]
fn defining_effectful_closure_does_not_leak_into_pure_function() {
    // A closure is a value: defining it performs nothing, its effects live in
    // its arrow type and are realized only when it is applied. A pure function
    // that builds an effectful closure but never calls it must type-check.
    // (Regression: lambda inference used to emit body effects at definition.)
    check(
        "effect Tick { fun tick : Unit -> Int }
fun pure_fn : Unit -> Int
pure_fn () = {
  let _f = fun () -> tick! ()
  42
}",
    )
    .unwrap();
}

#[test]
fn lambda_handling_own_effect_makes_hof_call_pure() {
    // The callback discharges its own effect at an internal `with`, so a HOF
    // that runs it inline performs nothing — even though the HOF's signature
    // names the effect on both its callback parameter and its result. The
    // caller is pure. (Absorbed = declared-callback minus actual-lambda effects,
    // applied to the HOF's result row.)
    check(
        "effect Tick { fun tick : Unit -> Int }
handler th for Tick { tick () = resume 1 }
fun run_forward : (Unit -> Int needs {Tick, ..e}) -> Int needs {Tick, ..e}
run_forward f = f ()
fun caller : Unit -> Int
caller () = run_forward (fun () -> tick! () with th)",
    )
    .unwrap();
}

#[test]
fn dead_declared_effect_discharged_by_callback_warns() {
    // `caller` declares {Tick} but only feeds a callback to a handler-HOF, so it
    // performs no Tick — the declaration is dead and must warn. The old call-site
    // absorption muted exactly this (it was the `spawn` dead-`Actor` wart).
    let mut checker = check(
        "effect Tick { fun tick : Unit -> Int }
handler th for Tick { tick () = resume 1 }
fun run_handled : (Unit -> Int needs {Tick}) -> Int
run_handled f = f () with th
fun caller : Unit -> Int needs {Tick}
caller () = run_handled (fun () -> tick! ())",
    )
    .unwrap();
    checker.zonk_warnings();
    assert!(
        checker.collected_diagnostics.iter().any(|d| {
            matches!(d.severity, Severity::Warning)
                && d.message.contains("caller")
                && d.message.contains("Tick")
                && d.message.contains("never uses")
        }),
        "expected unused-effect warning on `caller`, got: {:?}",
        checker.collected_diagnostics
    );
}

#[test]
fn forwarded_and_own_callback_effects_are_not_flagged_unused() {
    // `run_forward` forwards the callback's effect (calls it inline); `run_self`
    // handles the callback's effect but performs its own. Both genuinely perform
    // {Tick}, so neither may be flagged as declaring an unused effect. (The
    // boundary absorption used to clobber these, then a suppression hid the
    // resulting bogus warnings — both are gone.)
    let mut checker = check(
        "effect Tick { fun tick : Unit -> Int }
handler th for Tick { tick () = resume 1 }
fun run_forward : (Unit -> Int needs {Tick, ..e}) -> Int needs {Tick, ..e}
run_forward f = f ()
fun run_self : (Unit -> Int needs {Tick}) -> Int needs {Tick}
run_self make = {
  let inner = make () with th
  let outer = tick! ()
  inner + outer
}",
    )
    .unwrap();
    checker.zonk_warnings();
    assert!(
        !checker
            .collected_diagnostics
            .iter()
            .any(|d| matches!(d.severity, Severity::Warning) && d.message.contains("never uses")),
        "no unused-effect warning expected, got: {:?}",
        checker.collected_diagnostics
    );
}

// --- Effect row polymorphism ---

#[test]
fn effect_row_var_basic_hof() {
    // HOF with open effect row: lambda with extra effects is accepted.
    // The extra Log effect propagates through ..e to the caller.
    check(
        "effect Assert {\n  fun assert_ok : (ok: Bool) -> Unit\n}\neffect Log {\n  fun log : (msg: String) -> Unit\n}\nfun run : (f: Unit -> Unit needs {Assert, ..e}) -> Unit needs {..e}\nrun f = f () with { assert_ok ok = () }\nfun caller : Unit -> Unit needs {Log}\ncaller () = run (fun () -> {\n  assert_ok! True\n  log! \"hello\"\n})",
    )
    .unwrap();
}

#[test]
fn effect_row_var_pure_lambda_satisfies_open_row() {
    // A pure lambda satisfies a parameter with an open effect row
    check(
        "effect Chk {\n  fun chk : (ok: Bool) -> Unit\n}\nfun run : (f: Unit -> Unit needs {..e}) -> Unit needs {..e}\nrun f = f ()\nmain () = run (fun () -> ())",
    )
    .unwrap();
}

#[test]
fn effect_row_var_propagation() {
    // Extra effects from the lambda propagate through the row variable
    // to the caller's needs clause
    check(
        "effect Fail {\n  fun fail : (msg: String) -> a\n}\neffect Log {\n  fun log : (msg: String) -> Unit\n}\nfun run_with_fail : (f: Unit -> Int needs {Fail, ..e}) -> Int needs {..e}\nrun_with_fail f = f () with { fail msg = 0 }\nfun caller : Unit -> Int needs {Log}\ncaller () = run_with_fail (fun () -> {\n  log! \"hello\"\n  fail! \"oops\"\n})",
    )
    .unwrap();
}

#[test]
fn effect_row_var_only_row_var() {
    // `needs {..e}` with no concrete effects
    check(
        "fun apply : (f: Unit -> Int needs {..e}) -> Int needs {..e}\napply f = f ()\nmain () = apply (fun () -> 42)",
    )
    .unwrap();
}

#[test]
fn effect_row_var_closed_row_rejects_extra_effects() {
    // A lambda with extra effects should be rejected when the parameter has a closed row
    let result = check(
        "effect Assert {\n  fun assert_ok : (ok: Bool) -> Unit\n}\neffect Log {\n  fun log : (msg: String) -> Unit\n}\nfun run : (f: Unit -> Unit needs {Assert}) -> Unit\nrun f = f () with { assert_ok ok = () }\nmain () = run (fun () -> {\n  assert_ok! True\n  log! \"hello\"\n})",
    );
    assert!(
        result.is_err(),
        "expected error for extra effects in closed row"
    );
}

#[test]
fn effect_row_var_function_open_needs() {
    // Function with open needs clause allows extra effects in body
    check(
        "effect Fail {\n  fun fail : (msg: String) -> a\n}\neffect Log {\n  fun log : (msg: String) -> Unit\n}\nfun both : Int -> Int needs {Fail, ..e}\nboth x = {\n  log! \"hello\"\n  fail! \"oops\"\n}",
    )
    .unwrap();
}

#[test]
fn needs_empty_enforces_purity() {
    // `needs {}` means the callback must be pure -- no effects allowed
    let result = check(
        "effect Log {\n  fun log : (msg: String) -> Unit\n}\nfun run_pure : (f: Unit -> Int needs {}) -> Int\nrun_pure f = f ()\nmain () = run_pure (fun () -> {\n  log! \"hello\"\n  42\n})",
    );
    assert!(
        result.is_err(),
        "expected error: effectful lambda passed to pure parameter"
    );
}

#[test]
fn needs_empty_accepts_pure_lambda() {
    // `needs {}` should accept a pure lambda
    check(
        "fun run_pure : (f: Unit -> Int needs {}) -> Int\nrun_pure f = f ()\nmain () = run_pure (fun () -> 42)",
    )
    .unwrap();
}

#[test]
fn effect_row_var_handler_not_unnecessary() {
    // When effects flow through a row variable, the handler should not be
    // flagged as unnecessary (the string-based tracking can't see row-bound effects)
    check(
        "effect Log {\n  fun log : (msg: String) -> Unit\n}\nfun run : (f: Unit -> Unit needs {..e}) -> Unit needs {..e}\nrun f = f ()\nmain () = run (fun () -> log! \"hello\") with { log msg = () }",
    )
    .unwrap();
}

// --- Multiple row variables ---

#[test]
fn multi_row_var_forwards_union_of_two_open_rows() {
    // Two callbacks each with their own open row; the HOF forwards the union
    // `needs {..a, ..b}`. Each tail binds independently.
    check(
        "effect Foo {\n  fun foo : Unit -> Int\n}\n\
         effect Bar {\n  fun bar : Unit -> Int\n}\n\
         fun do_work : (Unit -> Int needs {..a}) -> (Unit -> Int needs {..b}) -> Int needs {..a, ..b}\n\
         do_work a b = {\n  let ra = a ()\n  let rb = b ()\n  ra + rb\n}\n\
         main () = {\n  let res = do_work (fun () -> foo! ()) (fun () -> bar! ())\n  res\n} with {\n  foo () = resume 42\n  bar () = resume 3\n}",
    )
    .unwrap();
}

#[test]
fn multi_row_var_with_named_effects_on_each_callback() {
    // Each callback carries a named effect plus its own open tail; the HOF
    // forwards both names and both tails.
    check(
        "effect Foo {\n  fun foo : Unit -> Int\n}\n\
         effect Bar {\n  fun bar : Unit -> Int\n}\n\
         effect Baz {\n  fun baz : Unit -> Int\n}\n\
         fun do_work : (Unit -> Int needs {Foo, ..a}) -> (Unit -> Int needs {Bar, ..b}) -> Int needs {Foo, Bar, ..a, ..b}\n\
         do_work a b = {\n  let ra = a ()\n  let rb = b ()\n  ra + rb\n}\n\
         main () = {\n  do_work (fun () -> foo! () + baz! ()) (fun () -> bar! ())\n} with {\n  foo () = resume 42\n  bar () = resume 3\n  baz () = resume 100\n}",
    )
    .unwrap();
}

#[test]
fn multi_row_var_two_open_tails_in_callback_are_ambiguous() {
    // A callback parameter whose row has two unconstrained open tails cannot
    // absorb a named effect: it is undetermined which tail it belongs to.
    let result = check(
        "effect Foo {\n  fun foo : Unit -> Int\n}\n\
         fun consume : (Unit -> Int needs {..a, ..b}) -> Int needs {..a, ..b}\n\
         consume f = f ()\n\
         main () = {\n  consume (fun () -> foo! ())\n} with {\n  foo () = resume 1\n}",
    );
    let err = match result {
        Err(e) => e,
        Ok(_) => panic!("expected ambiguous multi-open-tail error, got Ok"),
    };
    assert!(
        err.message.contains("ambiguous effect row"),
        "expected ambiguous effect row error, got: {}",
        err.message
    );
}

#[test]
fn multi_row_var_must_forward_every_callback_tail() {
    // Two callbacks with independent open rows, but the function only declares
    // `needs {..a}` — `..b`'s effects would silently escape the signature. The
    // body still calls `b ()`, so this must be rejected.
    let result = check(
        "effect Foo {\n  fun foo : Unit -> Int\n}\n\
         effect Bar {\n  fun bar : Unit -> Int\n}\n\
         fun do_work : (Unit -> Int needs {..a}) -> (Unit -> Int needs {..b}) -> Int needs {..a}\n\
         do_work a b = {\n  let ra = a ()\n  let rb = b ()\n  ra + rb\n}",
    );
    let err = match result {
        Err(e) => e,
        Ok(_) => panic!("expected error: callback row variable ..b not forwarded"),
    };
    assert!(
        err.message.contains("does not forward it"),
        "expected unforwarded-row error, got: {}",
        err.message
    );
}

// --- Comprehensive effect flow tests ---

#[test]
fn effect_propagation_through_chain() {
    // Effects propagate through a chain: a -> b -> c
    check(
        "effect Log {\n  fun log : (msg: String) -> Unit\n}\n\
         fun c : Unit -> Unit needs {Log}\nc () = log! \"from c\"\n\
         fun b : Unit -> Unit needs {Log}\nb () = c ()\n\
         fun a : Unit -> Unit needs {Log}\na () = b ()",
    )
    .unwrap();
}

#[test]
fn effect_propagation_missing_needs_in_chain() {
    // b calls c which needs Log, but b doesn't declare Log
    let result = check(
        "effect Log {\n  fun log : (msg: String) -> Unit\n}\n\
         fun c : Unit -> Unit needs {Log}\nc () = log! \"from c\"\n\
         fun b : Unit -> Unit\nb () = c ()",
    );
    assert!(result.is_err());
    assert!(result.err().unwrap().message.contains("Log"));
}

#[test]
fn handler_subtracts_effect_from_chain() {
    // a calls b which needs Log, handles it -- no needs on a
    check(
        "effect Log {\n  fun log : (msg: String) -> Unit\n}\n\
         fun b : Unit -> Unit needs {Log}\nb () = log! \"hello\"\n\
         fun a : Unit -> Unit\na () = b () with { log msg = () }",
    )
    .unwrap();
}

#[test]
fn handler_partial_subtraction() {
    // Handler handles Log but not Fail -- Fail propagates
    check(
        "effect Log {\n  fun log : (msg: String) -> Unit\n}\n\
         effect Fail {\n  fun fail : (msg: String) -> a\n}\n\
         fun work : Unit -> Unit needs {Log, Fail}\n\
         work () = { log! \"start\"\n  fail! \"oops\" }\n\
         fun caller : Unit -> Unit needs {Fail}\n\
         caller () = work () with { log msg = () }",
    )
    .unwrap();
}

#[test]
fn handler_partial_subtraction_missing_needs() {
    // Handler handles Log but not Fail, caller doesn't declare Fail
    let result = check(
        "effect Log {\n  fun log : (msg: String) -> Unit\n}\n\
         effect Fail {\n  fun fail : (msg: String) -> a\n}\n\
         fun work : Unit -> Unit needs {Log, Fail}\n\
         work () = { log! \"start\"\n  fail! \"oops\" }\n\
         fun caller : Unit -> Unit\n\
         caller () = work () with { log msg = () }",
    );
    assert!(result.is_err());
    assert!(result.err().unwrap().message.contains("Fail"));
}

#[test]
fn hof_absorption_basic() {
    // HOF takes callback with Fail, handles it -- caller doesn't need Fail
    check(
        "effect Fail {\n  fun fail : (msg: String) -> a\n}\n\
         fun try_it : (f: Unit -> String needs {Fail}) -> String\n\
         try_it f = f () with { fail msg = \"err\" }\n\
         fun caller : Unit -> String\ncaller () = try_it (fun () -> fail! \"boom\")",
    )
    .unwrap();
}

#[test]
fn hof_absorption_pure_callback_accepted() {
    // Pure callback passed where effectful callback expected (effect subtyping)
    check(
        "effect Fail {\n  fun fail : (msg: String) -> a\n}\n\
         fun try_it : (f: Unit -> String needs {Fail}) -> String\n\
         try_it f = f () with { fail msg = \"err\" }\n\
         fun caller : Unit -> String\ncaller () = try_it (fun () -> \"hello\")",
    )
    .unwrap();
}

#[test]
fn hof_absorption_applies_substitutions_before_exact_subtraction() {
    check(
        "effect State s {\n  fun get : Unit -> s\n  fun put : s -> Unit\n}\n\
         fun run_state : s -> (Unit -> a needs {State s}) -> (a, s)\n\
         run_state init f = {\n\
           let state_fn = f () with {\n\
             get () = fun s -> (resume s) s\n\
             put new_s = fun _ -> (resume ()) new_s\n\
             return value = fun s -> (value, s)\n\
           }\n\
           state_fn init\n\
         }\n\
         fun caller : Unit -> Unit\n\
         caller () = {\n\
           let (value, _) = run_state 0 (fun () -> get! ())\n\
           let _ = value\n\
           ()\n\
         }",
    )
    .unwrap();
}

#[test]
fn nested_hof_absorption_does_not_leak_inner_closed_effects() {
    check(
        "effect Assert {\n  fun assert : Bool -> String -> Unit\n}\n\
         effect State s {\n  fun get : Unit -> s\n  fun put : s -> Unit\n}\n\
         fun use : (body: Unit -> Unit needs {Assert, ..e}) -> Unit needs {..e}\n\
         use body = body () with { assert _ _ = resume () }\n\
         fun run_state : s -> (Unit -> a needs {State s}) -> (a, s)\n\
         run_state init f = {\n\
           let state_fn = f () with {\n\
             get () = fun s -> (resume s) s\n\
             put new_s = fun _ -> (resume ()) new_s\n\
             return value = fun s -> (value, s)\n\
           }\n\
           state_fn init\n\
         }\n\
         fun caller : Unit -> Unit\n\
         caller () = use (fun () -> {\n\
           let (value, _) = run_state 0 (fun () -> get! ())\n\
           let _ = value\n\
           assert! True \"\"\n\
         })",
    )
    .unwrap();
}

#[test]
fn effect_op_row_variable_freshens_per_call_site() {
    // Regression: `instantiate_effect_op`'s `collect_vars` walked Type::Fun's
    // params and return type but ignored the effect row, so a row variable
    // appearing only in the effect row (e.g. `..e` in
    // `spawn : (f: Unit -> Unit needs {Actor msg, ..e}) -> Pid msg
    //   needs {Actor msg, ..e}`) was never freshened across call sites.
    // After one call bound the row var, subsequent call sites inherited the
    // binding and rejected callbacks whose effect row didn't match.
    //
    // Here the callback uses Process+Monitor+Timer+Actor+Logger (a closed,
    // multi-effect row). The parent's row variable for spawn must bind to
    // the lambda's extras, but only if it's fresh.
    check(
        "import Std.Actor (Process, Actor, Monitor, Timer)\n\
         effect Logger {\n  fun log : String -> Unit\n}\n\
         type Msg = Tick\n\
         fun worker : Unit -> Unit\n  \
           needs {Process, Actor Msg, Monitor, Timer, Logger}\n\
         worker () = receive {\n  \
           Tick -> {\n    \
             log! \"x\"\n    \
             let _pid = spawn! (fun () -> ())\n    \
             let _ref = monitor! (self! ())\n    \
             sleep! 1\n    \
             worker ()\n  \
           }\n\
         }\n\
         fun parent : Unit -> Unit\n  \
           needs {Process, Actor Msg, Monitor, Timer, Logger}\n\
         parent () = {\n  \
           let _pid = spawn! (fun () -> worker ())\n  \
           ()\n\
         }",
    )
    .unwrap();
}

#[test]
fn handler_factory_must_propagate_handler_needs() {
    // A function that returns a `handler for E needs {X}` constructs a handler
    // value whose arm bodies use X. The arm closures capture evidence from the
    // construction site — i.e. the factory function must have X in its own
    // `needs` so the lowerer threads it through. Without this, the codegen
    // ICEs when lowering the arm body because the construction site's
    // evidence has no X. Detect at typecheck.
    let unhandled = "effect Outer {\n  fun notify : String -> Unit\n}\n\
                     effect Inner {\n  fun do_thing : Int -> Unit\n}\n\
                     fun make_inner : Unit -> Handler Inner\n\
                     make_inner () = handler for Inner needs {Outer} {\n\
                       do_thing n = { notify! \"x\"; resume () }\n\
                     }";
    let err = match check(unhandled) {
        Ok(_) => panic!("expected typechecker error for handler factory missing needs"),
        Err(e) => e,
    };
    assert!(
        err.message.contains("Outer") && err.message.contains("needs"),
        "expected handler-factory needs-propagation error, got: {}",
        err.message
    );

    // Declaring `needs {Outer}` on the factory itself fixes it: the factory
    // receives a hidden Outer handler param at call time and the arm closures
    // capture it.
    check(
        "effect Outer {\n  fun notify : String -> Unit\n}\n\
         effect Inner {\n  fun do_thing : Int -> Unit\n}\n\
         fun make_inner : Unit -> Handler Inner needs {Outer}\n\
         make_inner () = handler for Inner needs {Outer} {\n\
           do_thing n = { notify! \"x\"; resume () }\n\
         }",
    )
    .unwrap();
}

#[test]
fn closed_callback_effect_must_be_handled_or_forwarded() {
    // A HOF whose callback parameter declares closed `needs {X}` must either
    // install an internal `with` handler for X or forward X via the function's
    // own `needs` clause. Otherwise the runtime has no way to source the
    // handler when the callback is invoked, and the lowerer would ICE.
    // Regression: typechecker used to silently absorb the effect.
    let unhandled = "effect Outer {\n  fun outer_op : Unit -> Unit\n}\n\
                     fun framework_call : (Unit -> Unit needs {Outer}) -> Unit\n\
                     framework_call f = f ()";
    let err = match check(unhandled) {
        Ok(_) => panic!("expected typechecker error for unhandled callback effect"),
        Err(e) => e,
    };
    assert!(
        err.message.contains("Outer") && err.message.contains("not handled"),
        "expected unhandled-callback-effect error, got: {}",
        err.message
    );

    // Forwarding via the function's own `needs` is fine.
    check(
        "effect Outer {\n  fun outer_op : Unit -> Unit\n}\n\
         fun framework_call : (Unit -> Unit needs {Outer}) -> Unit needs {Outer}\n\
         framework_call f = f ()",
    )
    .unwrap();

    // Internal `with` is also fine (existing pattern, already verified by
    // run_state-style tests).
    check(
        "effect Outer {\n  fun outer_op : Unit -> Unit\n}\n\
         fun framework_call : (Unit -> Unit needs {Outer}) -> Unit\n\
         framework_call f = f () with { outer_op _ = resume () }",
    )
    .unwrap();
}

#[test]
fn row_var_propagation_extra_effects() {
    // Open row: extra effects from callback propagate through ..e
    check(
        "effect Fail {\n  fun fail : (msg: String) -> a\n}\n\
         effect Log {\n  fun log : (msg: String) -> Unit\n}\n\
         fun run : (f: Unit -> Unit needs {Fail, ..e}) -> Unit needs {..e}\n\
         run f = f () with { fail msg = () }\n\
         fun caller : Unit -> Unit needs {Log}\n\
         caller () = run (fun () -> { fail! \"x\"\n  log! \"y\" })",
    )
    .unwrap();
}

#[test]
fn unnecessary_handler_warning_fires() {
    // Handler for Log on expression that doesn't use Log
    let checker = check(
        "effect Log {\n  fun log : (msg: String) -> Unit\n}\n\
         fun pure_fn : Unit -> Int\npure_fn () = 42\n\
         fun caller : Unit -> Int\n\
         caller () = pure_fn () with { log msg = { ()\n  0 } }",
    )
    .unwrap();
    let warnings: Vec<_> = checker
        .collected_diagnostics
        .iter()
        .filter(|d| d.message.contains("unnecessary"))
        .collect();
    assert!(!warnings.is_empty(), "expected unnecessary handler warning");
}

#[test]
fn no_unnecessary_handler_warning_when_used() {
    // Handler for Log on expression that uses Log -- no warning
    let checker = check(
        "effect Log {\n  fun log : (msg: String) -> Unit\n}\n\
         fun greet : Unit -> Unit needs {Log}\ngreet () = log! \"hello\"\n\
         fun caller : Unit -> Unit\n\
         caller () = greet () with { log msg = () }",
    )
    .unwrap();
    let warnings: Vec<_> = checker
        .collected_diagnostics
        .iter()
        .filter(|d| d.message.contains("unnecessary"))
        .collect();
    assert!(warnings.is_empty(), "unexpected warning: {:?}", warnings);
}

#[test]
fn trait_method_needs_survives_in_scheme() {
    let checker = check(
        "effect Fail e {\n  fun fail : e -> a\n}\n\
         trait Decode a {\n  fun decode : Int -> a needs {Fail String}\n}\n\
         impl Decode for Int needs {Fail String} {\n  decode n = if n < 0 then fail! \"neg\" else n\n}",
    )
    .unwrap();
    let trait_info = checker.trait_state.traits.get("Decode").unwrap();
    let method = &trait_info.methods[0];
    let resolved = checker.sub.apply(&method.scheme.ty);
    let effects = super::effects_from_type(&resolved);
    assert!(effects.contains("Fail"), "effects were {:?}", effects);
    assert_eq!(method.effect_sig.effects, vec!["Fail".to_string()]);
    assert!(!method.effect_sig.is_open_row);
    assert_eq!(method.effect_sig.user_arity, 1);
}

#[test]
fn trait_method_signature_displays_user_method_type() {
    let checker = check(
        "trait Describe a {\n  fun describe_it : a -> String\n}\n\
         record Person { name: String }\n\
         impl Describe for Person {\n  describe_it p = $\"Name is: {p.name}\"\n}",
    )
    .unwrap();
    let result = checker.to_result();

    assert_eq!(
        result.trait_method_signature("Describe", "describe_it"),
        Some("Describe.describe_it : a -> String".to_string())
    );
}

#[test]
fn no_unnecessary_handler_warning_for_where_bound_effectful_trait_method() {
    let checker = check(
        "effect Fail e {\n  fun fail : e -> a\n}\n\
         trait Decode a {\n  fun decode : Int -> a needs {Fail String}\n}\n\
         impl Decode for Int needs {Fail String} {\n  decode n = if n < 0 then fail! \"neg\" else n\n}\n\
         type Wrap a = Wrap a\n\
         impl Decode for Wrap a where {a: Decode} needs {Fail String} {\n  decode n = Wrap (decode n)\n}\n\
         handler to_result for Fail a {\n  fail e = Err e\n  return v = Ok v\n}\n\
         fun run_wrap : Int -> Result (Wrap Int) String\n\
         run_wrap n = decode n with to_result",
    )
    .unwrap();
    let warnings: Vec<_> = checker
        .collected_diagnostics
        .iter()
        .filter(|d| d.message.contains("unnecessary"))
        .collect();
    assert!(warnings.is_empty(), "unexpected warning: {:?}", warnings);
}

#[test]
fn no_unnecessary_handler_warning_for_indirect_named_handler_dependencies() {
    let checker = check(
        "effect Worker {\n  fun work : Unit -> Unit\n}\n\
         effect Ref {\n  fun tick : Unit -> Unit\n}\n\
         handler worker_impl for Worker {\n\
           work () = resume ()\n\
         }\n\
         handler ref_impl for Ref needs {Worker} {\n\
           tick () = { work! ()\n  resume () }\n\
         }\n\
         fun caller : Unit -> Unit\n\
         caller () = tick! () with { ref_impl, worker_impl }",
    )
    .unwrap();
    let warnings: Vec<_> = checker
        .collected_diagnostics
        .iter()
        .filter(|d| d.message.contains("unnecessary"))
        .collect();
    assert!(warnings.is_empty(), "unexpected warning: {:?}", warnings);
}

#[test]
fn no_unnecessary_handler_warning_for_nested_named_return_handlers() {
    let checker = check(
        "effect Counter {\n  fun get : Unit -> Int\n}\n\
         handler add_one for Counter {\n\
           get () = resume 10\n\
           return value = value + 1\n\
         }\n\
         handler times_two for Counter {\n\
           get () = resume 20\n\
           return value = value * 2\n\
         }\n\
         fun caller : Unit -> Int\n\
         caller () = get! () with {add_one, times_two}",
    )
    .unwrap();
    let warnings: Vec<_> = checker
        .collected_diagnostics
        .iter()
        .filter(|d| d.message.contains("unnecessary"))
        .collect();
    assert!(warnings.is_empty(), "unexpected warning: {:?}", warnings);
}

#[test]
fn effect_in_if_branches_merge() {
    check(
        "effect Log {\n  fun log : (msg: String) -> Unit\n}\n\
         effect Fail {\n  fun fail : (msg: String) -> a\n}\n\
         fun work : (x: Bool) -> Unit needs {Log, Fail}\n\
         work x = if x then log! \"yes\" else fail! \"no\"",
    )
    .unwrap();
}

#[test]
fn effect_in_case_arms_merge() {
    check(
        "effect Log {\n  fun log : (msg: String) -> Unit\n}\n\
         effect Fail {\n  fun fail : (msg: String) -> a\n}\n\
         fun work : (x: Int) -> Unit needs {Log, Fail}\n\
         work x = case x {\n  0 -> log! \"zero\"\n  _ -> fail! \"nonzero\"\n}",
    )
    .unwrap();
}

#[test]
fn effect_in_block_statements_merge() {
    check(
        "effect Log {\n  fun log : (msg: String) -> Unit\n}\n\
         effect Fail {\n  fun fail : (msg: String) -> a\n}\n\
         fun work : Unit -> Unit needs {Log, Fail}\n\
         work () = {\n  log! \"start\"\n  fail! \"end\"\n}",
    )
    .unwrap();
}

#[test]
fn partial_application_preserves_effects() {
    check(
        "effect Log {\n  fun log : (msg: String) -> Unit\n}\n\
         fun greet : (name: String) -> (greeting: String) -> Unit needs {Log}\n\
         greet name greeting = log! (name <> greeting)\n\
         fun caller : Unit -> Unit needs {Log}\n\
         caller () = {\n  let f = greet \"hello\"\n  f \"world\"\n}",
    )
    .unwrap();
}

#[test]
fn nested_handlers_scope_isolation() {
    // Inner handler handles Fail, outer handler handles Log.
    // Effects from inner handler arms don't leak to the outer scope.
    check(
        "effect Log {\n  fun log : (msg: String) -> Unit\n}\n\
         effect Fail {\n  fun fail : (msg: String) -> a\n}\n\
         fun work : Unit -> Unit needs {Log, Fail}\n\
         work () = { log! \"start\"\n  fail! \"oops\" }\n\
         fun outer : Unit -> Unit\n\
         outer () = {\n\
           work () with {\n\
             log msg = (),\n\
             fail msg = (),\n\
           }\n\
         }",
    )
    .unwrap();
}

#[test]
fn nested_handlers_inner_arm_uses_outer_effect() {
    // Inner handler arm uses an effect that the outer handler handles.
    // The arm's Log effect should propagate out of the inner handler
    // and be caught by the outer handler.
    check(
        "effect Log {\n  fun log : (msg: String) -> Unit\n}\n\
         effect Fail {\n  fun fail : (msg: String) -> a\n}\n\
         fun work : Unit -> Unit needs {Fail}\n\
         work () = fail! \"oops\"\n\
         fun outer : Unit -> Unit\n\
         outer () = {\n\
           work () with { fail msg = log! \"caught\" }\n\
         } with { log msg = () }",
    )
    .unwrap();
}

#[test]
fn nested_handlers_unhandled_arm_effect_propagates() {
    // Inner handler arm uses Log, no outer handler -- caller must declare it
    check(
        "effect Log {\n  fun log : (msg: String) -> Unit\n}\n\
         effect Fail {\n  fun fail : (msg: String) -> a\n}\n\
         fun work : Unit -> Unit needs {Fail}\n\
         work () = fail! \"oops\"\n\
         fun caller : Unit -> Unit needs {Log}\n\
         caller () = work () with { fail msg = log! \"caught\" }",
    )
    .unwrap();
}

#[test]
fn nested_handlers_unhandled_arm_effect_error() {
    // Inner handler arm uses Log, no handler for it, caller doesn't declare it
    let result = check(
        "effect Log {\n  fun log : (msg: String) -> Unit\n}\n\
         effect Fail {\n  fun fail : (msg: String) -> a\n}\n\
         fun work : Unit -> Unit needs {Fail}\n\
         work () = fail! \"oops\"\n\
         fun caller : Unit -> Unit\n\
         caller () = work () with { fail msg = log! \"caught\" }",
    );
    assert!(result.is_err());
    assert!(result.err().unwrap().message.contains("Log"));
}

// --- Effect subtyping (directional) tests ---

#[test]
fn effectful_callback_where_pure_expected_is_error() {
    // Passing an effectful lambda where a pure callback is expected should fail,
    // even when the caller declares the effect in its own needs clause.
    let result = check(
        "effect Log {\n  fun log : (msg: String) -> Unit\n}\n\
         fun apply_pure : (f: Int -> Int) -> Int\n\
         apply_pure f = f 42\n\
         fun caller : Unit -> Int needs {Log}\n\
         caller () = apply_pure (fun x -> { log! \"hi\"\n  x })",
    );
    assert!(
        result.is_err(),
        "effectful callback should be rejected by pure parameter"
    );
    let msg = result.err().unwrap().message;
    assert!(
        msg.contains("Log"),
        "error should mention the disallowed effect: {}",
        msg
    );
}

#[test]
fn effectful_callback_where_fewer_effects_expected_is_error() {
    // Callback has Log + Fail but parameter only allows Fail
    let result = check(
        "effect Log {\n  fun log : (msg: String) -> Unit\n}\n\
         effect Fail {\n  fun fail : (msg: String) -> a\n}\n\
         fun try_it : (f: Unit -> Int needs {Fail}) -> Int\n\
         try_it f = f () with { fail msg = 0 }\n\
         fun caller : Unit -> Int needs {Log}\n\
         caller () = try_it (fun () -> { log! \"hi\"\n  fail! \"oops\" })",
    );
    assert!(
        result.is_err(),
        "callback with extra effects should be rejected"
    );
    let msg = result.err().unwrap().message;
    assert!(msg.contains("Log"), "error should mention Log: {}", msg);
}

#[test]
fn pure_callback_where_effectful_expected_still_works() {
    // A pure lambda passed where an effectful callback is expected should still work
    // (effect subtyping: pure is a subtype of effectful)
    check(
        "effect Fail {\n  fun fail : (msg: String) -> a\n}\n\
         fun try_it : (f: Unit -> Int needs {Fail}) -> Int\n\
         try_it f = f () with { fail msg = 0 }\n\
         fun caller : Unit -> Int\n\
         caller () = try_it (fun () -> 42)",
    )
    .unwrap();
}

#[test]
fn open_row_callback_accepts_extra_effects() {
    // With an open row (..e), extra effects from the callback should propagate
    // through the row variable, not trigger a subtype error
    check(
        "effect Fail {\n  fun fail : (msg: String) -> a\n}\n\
         effect Log {\n  fun log : (msg: String) -> Unit\n}\n\
         fun run : (f: Unit -> Unit needs {Fail, ..e}) -> Unit needs {..e}\n\
         run f = f () with { fail msg = () }\n\
         fun caller : Unit -> Unit needs {Log}\n\
         caller () = run (fun () -> { fail! \"x\"\n  log! \"y\" })",
    )
    .unwrap();
}

// --- Multi-param trait tests ---

#[test]
fn multi_param_trait_def_and_impl() {
    check(
        "trait ConvertTo a b {\n\
         fun rate : Unit -> Float\n\
         }\n\
         impl ConvertTo Int for Float {\n\
         rate () = 1.0\n\
         }",
    )
    .unwrap();
}

#[test]
fn impl_with_parenthesized_parameterized_trait_type_arg_typechecks() {
    check(
        "trait Selectable row selection {\n\
           fun to_projection : selection -> row\n\
         }\n\
         type Selected2 a b = Selected2 a b\n\
         type Select2 a b = Select2 a b\n\
         impl Selectable (Selected2 a b) for Select2 a b {\n\
           to_projection selection = case selection {\n\
             Selected2 x y -> Select2 x y\n\
           }\n\
         }\n\
         fun use_it : Unit -> Select2 Int String\n\
         use_it () = to_projection (Selected2 1 \"title\")\n",
    )
    .unwrap();
}

#[test]
fn multi_param_trait_arity_mismatch() {
    let result = check(
        "trait ConvertTo a b {\n\
         fun rate : Unit -> Float\n\
         }\n\
         impl ConvertTo for Float {\n\
         rate () = 1.0\n\
         }",
    );
    assert!(result.is_err());
}

#[test]
fn multi_param_trait_too_many_args() {
    let result = check(
        "trait Show a {\n\
         fun show : a -> String\n\
         }\n\
         impl Show Int for Float {\n\
         show x = \"float\"\n\
         }",
    );
    assert!(result.is_err());
}

#[test]
fn multi_param_trait_where_clause_typechecks() {
    // A function with a multi-param trait constraint in its where clause
    check(
        "trait ConvertTo a b {\n\
         fun rate : Unit -> Float\n\
         }\n\
         fun convert : a -> b where {a: ConvertTo b}\n\
         convert x = x",
    )
    .unwrap();
}

#[test]
fn multi_param_trait_where_clause_constraint_propagates() {
    // The constraint from the where clause should flow through instantiation
    check(
        "trait ConvertTo a b {\n\
         fun rate : Unit -> Float\n\
         }\n\
         impl ConvertTo Int for Float {\n\
         rate () = 1.0\n\
         }\n\
         fun convert : a -> Float where {a: ConvertTo Int}\n\
         convert x = x",
    )
    .unwrap();
}

#[test]
fn multi_param_trait_multiple_impls_different_type_args() {
    // Two impls of the same trait with different type args should coexist
    check(
        "trait ConvertTo a b {\n\
         fun rate : Unit -> Float\n\
         }\n\
         impl ConvertTo Int for Float {\n\
         rate () = 1.0\n\
         }\n\
         impl ConvertTo Float for Int {\n\
         rate () = 0.5\n\
         }",
    )
    .unwrap();
}

#[test]
fn multi_param_trait_display_with_constraints() {
    // Verify constraint display includes type args
    let checker = check(
        "trait ConvertTo a b {\n\
         fun rate : Unit -> Float\n\
         }\n\
         fun convert : a -> b where {a: ConvertTo b}\n\
         convert x = x",
    )
    .unwrap();
    let scheme = checker.env.get("convert").unwrap();
    let display = scheme.display_with_constraints(&checker.sub);
    assert!(
        display.contains("ConvertTo"),
        "display should contain 'ConvertTo': {}",
        display
    );
}

#[test]
fn handler_with_multi_param_trait_where_clause() {
    // Handler with a multi-param trait in its where clause.
    // The handler constrains the effect's type param with ConvertTo Int,
    // and when used with a concrete type (Float), the impl is resolved.
    check(
        "trait ConvertTo a b {\n\
         fun rate : Unit -> Float\n\
         }\n\
         effect State s {\n\
         fun get : Unit -> s\n\
         fun put : s -> Unit\n\
         }\n\
         impl ConvertTo Int for Float {\n\
         rate () = 1.0\n\
         }\n\
         handler my_handler for State a where {a: ConvertTo Int} {\n\
         get () = resume 1.5\n\
         put x = resume ()\n\
         }",
    )
    .unwrap();
}

// --- Phantom type param tests (trait methods that don't mention the self type) ---

#[test]
fn phantom_trait_method_in_where_clause_function() {
    // rate : Unit -> Float doesn't mention `a` or `b`, but the constraint
    // should still flow through the where clause.
    check(
        "trait ConvertTo a b {\n\
         fun rate : Unit -> Float\n\
         }\n\
         impl ConvertTo Int for Float {\n\
         rate () = 1.0\n\
         }\n\
         fun convert : a -> Float where {a: ConvertTo Int}\n\
         convert x = rate ()",
    )
    .unwrap();
}

#[test]
fn phantom_trait_method_without_where_clause_fails() {
    // Calling a phantom trait method without the required where clause should error.
    let result = check(
        "trait ConvertTo a b {\n\
         fun rate : Unit -> Float\n\
         }\n\
         fun bad : Unit -> Float\n\
         bad () = rate ()",
    );
    assert!(result.is_err());
}

#[test]
fn phantom_trait_method_wrong_trait_in_where_clause_fails() {
    // Where clause has a different trait than what the phantom method requires.
    let result = check(
        "trait ConvertTo a b {\n\
         fun rate : Unit -> Float\n\
         }\n\
         trait Other a {\n\
         fun other : a -> String\n\
         }\n\
         fun bad : a -> Float where {a: Other}\n\
         bad x = rate ()",
    );
    assert!(result.is_err());
}

#[test]
fn phantom_and_non_phantom_methods_in_same_trait() {
    // A trait with both phantom and non-phantom methods.
    // convert uses the self type (non-phantom), rate doesn't (phantom).
    check(
        "trait ConvertTo a b {\n\
         fun rate : Unit -> Float\n\
         fun convert : a -> b\n\
         }\n\
         impl ConvertTo Int for Float {\n\
         rate () = 2.5\n\
         convert _ = 0\n\
         }\n\
         fun use_both : a -> Int where {a: ConvertTo Int}\n\
         use_both x = {\n\
         let _ = rate ()\n\
         convert x\n\
         }",
    )
    .unwrap();
}

#[test]
fn phantom_trait_method_concrete_call_resolves_impl() {
    // Calling a phantom trait method in a polymorphic function, then
    // invoking at concrete types should resolve the impl.
    check(
        "type USD = USD\n\
         type NOK = NOK\n\
         type Currency c = Currency(Float)\n\
         trait ConvertTo a b {\n\
         fun rate : Unit -> Float\n\
         }\n\
         impl ConvertTo NOK for USD {\n\
         rate () = 10.5\n\
         }\n\
         fun usd : Float -> Currency USD\n\
         usd amount = Currency amount\n\
         fun convert : Currency a -> Currency b where {a: ConvertTo b}\n\
         convert (Currency amount) = Currency (amount * rate ())\n\
         main () = {\n\
         let x : Currency NOK = convert (usd 5.0)\n\
         x\n\
         }",
    )
    .unwrap();
}

#[test]
fn phantom_trait_method_wrong_impl_type_args_fails() {
    // The where clause says ConvertTo Int, but we try to use the result
    // where ConvertTo Float is needed. This should fail.
    let result = check(
        "type USD = USD\n\
         type NOK = NOK\n\
         type EUR = EUR\n\
         type Currency c = Currency(Float)\n\
         trait ConvertTo a b {\n\
         fun rate : Unit -> Float\n\
         }\n\
         impl ConvertTo NOK for USD {\n\
         rate () = 10.5\n\
         }\n\
         fun convert : Currency a -> Currency b where {a: ConvertTo b}\n\
         convert (Currency amount) = Currency (amount * rate ())\n\
         main () = {\n\
         let x : Currency EUR = convert (Currency 5.0)\n\
         x\n\
         }",
    );
    assert!(result.is_err());
}

// --- Auto-load of canonical qualified-name references ---
//
// Together these pin down the contract documented in
// `docs/planning/plans/auto-load-qualified-modules.md`:
//
//   "Canonical is global; imports control aliases."
//
// Auto-loading a module on first canonical reference must register canonical
// keys (so `Module.name` resolves) without injecting any bare/alias entries
// into scope (so `name`/`Alias.name` still require an explicit `import`).

#[test]
fn auto_load_stdlib_qualified_typechecks_without_explicit_import() {
    // Std.IO.Unsafe is *not* in the prelude, so this used to fail with
    // "unknown qualified name". With auto-load it should typecheck.
    check(
        "main () = {\n\
         Std.IO.Unsafe.print_stdout \"hello\"\n\
         }",
    )
    .expect("Std.IO.Unsafe.print_stdout must resolve via auto-load");
}

#[test]
fn auto_load_project_module_qualified_typechecks_without_explicit_import() {
    let lib = "module Lib\n\
               pub fun foo : Unit -> Unit\n\
               foo () = ()\n";
    let main = "module Main\n\
                main () = Lib.foo ()\n";
    check_with_project_files(&[("src/Lib.saga", lib)], main)
        .expect("Lib.foo must resolve via auto-load when Lib is in the project module map");
}

#[test]
fn cyclic_imports_share_annotated_types_and_functions() {
    let a = r#"
module A
import B (BThing, make_b)

pub type AThing = AThing BThing

pub fun make_a : Unit -> AThing
make_a () = AThing (make_b ())
"#;
    let b = r#"
module B
import A (AThing, make_a)

pub type BThing = BThing

pub fun make_b : Unit -> BThing
make_b () = BThing

pub fun bounce : Unit -> AThing
bounce () = make_a ()
"#;
    let main = r#"
module Main
import A (make_a)
import B (bounce)

fun main : Unit -> Unit
main () = ()
"#;

    check_with_project_files(&[("src/A.saga", a), ("src/B.saga", b)], main)
        .expect("mutually importing modules should typecheck through headers");
}

#[test]
fn cyclic_imports_preserve_lsp_metadata_for_sibling_headers() {
    let a = r#"
module A
import B (BThing, make_b)

pub fun use_b : Unit -> BThing
use_b () = make_b ()

pub fun make_ctor : Unit -> BThing
make_ctor () = BThing
"#;
    let b = r#"
module B
import A (use_b)

#@ A cyclic test type.
pub type BThing = BThing

#@ Build a BThing.
pub fun make_b : Unit -> BThing
make_b () = BThing
"#;
    let main = r#"
module Main
import A (use_b)

fun main : Unit -> Unit
main () = ()
"#;

    let checker = check_with_project_files(&[("src/A.saga", a), ("src/B.saga", b)], main)
        .expect("mutually importing modules should typecheck through headers");
    let a_result = checker
        .modules
        .check_results
        .get("A")
        .expect("A check result");

    let make_b_def = a_result
        .env
        .def_id("B.make_b")
        .expect("B.make_b should carry a definition id");
    assert!(
        a_result
            .references
            .values()
            .any(|def_id| *def_id == make_b_def),
        "expected use of make_b to reference B.make_b's definition"
    );
    let bthing_def = a_result
        .constructor_def_ids
        .get("B.BThing")
        .copied()
        .expect("B.BThing constructor should carry a definition id");
    assert!(
        a_result
            .references
            .values()
            .any(|def_id| *def_id == bthing_def),
        "expected BThing constructor use to reference the imported definition"
    );
    assert!(
        a_result.constructor_def_ids.contains_key("BThing"),
        "expected exposed constructor surface name to carry a definition id"
    );

    assert_eq!(
        a_result.imported_docs.get("B.make_b"),
        Some(&vec!["Build a BThing.".to_string()])
    );
    assert_eq!(
        a_result.imported_docs.get("make_b"),
        Some(&vec!["Build a BThing.".to_string()])
    );
    assert_eq!(
        a_result.imported_docs.get("BThing"),
        Some(&vec!["A cyclic test type.".to_string()])
    );
}

#[test]
fn cyclic_imports_follow_re_exports_to_origin() {
    let a = r#"
module A
import B (pub BThing as SharedThing, make_b)

pub fun make_shared : Unit -> SharedThing
make_shared () = make_b ()
"#;
    let b = r#"
module B
import A (make_shared)

pub type BThing = BThing

pub fun make_b : Unit -> BThing
make_b () = BThing

pub fun bounce : Unit -> BThing
bounce () = make_shared ()
"#;
    let main = r#"
module Main
import A (SharedThing, make_shared)

fun main : Unit -> Unit
main () = ()
"#;

    check_with_project_files(&[("src/A.saga", a), ("src/B.saga", b)], main)
        .expect("re-exported names in a cycle should resolve to their origin header");
}

#[test]
fn type_reexport_carries_origin_trait_impls() {
    let query = r#"
module Kraken.Query

pub type DbError = DbError deriving (Debug)
"#;
    let db = r#"
module Kraken.Db
import Kraken.Query (pub DbError)
"#;
    let main = r#"
module Main
import Kraken.Db

fun render : Kraken.Db.DbError -> String
render e = debug e
"#;

    check_with_project_files(
        &[("src/Kraken/Query.saga", query), ("src/Kraken/Db.saga", db)],
        main,
    )
    .expect("type re-export should carry Debug impl from the origin module");
}

#[test]
fn cyclic_import_of_unannotated_function_requests_annotation() {
    let a = r#"
module A
import B (helper)

pub type AThing = AThing

pub fun make_a : Unit -> AThing
make_a () = helper ()
"#;
    let b = r#"
module B
import A (AThing)

helper () = AThing
"#;
    let main = "module Main\nimport A (make_a)\nmain () = ()\n";

    let err = match check_with_project_files(&[("src/A.saga", a), ("src/B.saga", b)], main) {
        Ok(_) => panic!("unannotated cross-cycle function must be rejected"),
        Err(err) => err,
    };
    assert!(
        err.to_string().contains("needs a type annotation"),
        "expected annotation diagnostic, got: {}",
        err
    );
}

#[test]
fn cyclic_import_rejects_unsupported_trait_effect_and_handler_surfaces() {
    let a_trait = "module A\nimport B (Describe)\npub type AThing = AThing\n";
    let b_trait = r#"
module B
import A (AThing)
pub trait Describe a {
  fun describe : a -> String
}
"#;
    let main = "module Main\nimport A\nmain () = ()\n";
    let err =
        match check_with_project_files(&[("src/A.saga", a_trait), ("src/B.saga", b_trait)], main) {
            Ok(_) => panic!("trait import across cycle must be rejected"),
            Err(err) => err,
        };
    assert!(
        err.to_string().contains("trait 'Describe'")
            && err.to_string().contains("circular import boundary"),
        "expected trait cycle-boundary diagnostic, got: {}",
        err
    );

    let a_effect = "module A\nimport B (Log)\npub type AThing = AThing\n";
    let b_effect = r#"
module B
import A (AThing)
pub effect Log {
  fun log : String -> Unit
}
"#;
    let err =
        match check_with_project_files(&[("src/A.saga", a_effect), ("src/B.saga", b_effect)], main)
        {
            Ok(_) => panic!("effect import across cycle must be rejected"),
            Err(err) => err,
        };
    assert!(
        err.to_string().contains("effect 'Log'")
            && err.to_string().contains("circular import boundary"),
        "expected effect cycle-boundary diagnostic, got: {}",
        err
    );

    let a_handler = "module A\nimport B (run_log)\npub type AThing = AThing\n";
    let b_handler = r#"
module B
import A (AThing)
pub effect Log {
  fun log : String -> Unit
}
pub handler run_log for Log {
  log _ = resume ()
}
"#;
    let err = match check_with_project_files(
        &[("src/A.saga", a_handler), ("src/B.saga", b_handler)],
        main,
    ) {
        Ok(_) => panic!("handler import across cycle must be rejected"),
        Err(err) => err,
    };
    assert!(
        err.to_string().contains("handler 'run_log'")
            && err.to_string().contains("circular import boundary"),
        "expected handler cycle-boundary diagnostic, got: {}",
        err
    );

    let a_trait_function = "module A\nimport B (describe_thing)\npub type AThing = AThing\n";
    let b_trait_function = r#"
module B
import A (AThing)
pub trait Describe a {
  fun describe : a -> String
}
pub fun describe_thing : a -> String where {a: Describe}
describe_thing _ = ""
"#;
    let err = match check_with_project_files(
        &[
            ("src/A.saga", a_trait_function),
            ("src/B.saga", b_trait_function),
        ],
        main,
    ) {
        Ok(_) => panic!("trait-constrained function import across cycle must be rejected"),
        Err(err) => err,
    };
    assert!(
        err.to_string().contains("function 'describe_thing'")
            && err.to_string().contains("trait constraints")
            && err.to_string().contains("circular import boundary"),
        "expected trait-constrained function diagnostic, got: {}",
        err
    );

    let a_effect_function = "module A\nimport B (accept)\npub type AThing = AThing\n";
    let b_effect_function = r#"
module B
import A (AThing)
pub effect Log {
  fun log : String -> Unit
}
pub fun accept : (Unit -> Unit needs {Log}) -> Unit
accept _ = ()
"#;
    let err = match check_with_project_files(
        &[
            ("src/A.saga", a_effect_function),
            ("src/B.saga", b_effect_function),
        ],
        main,
    ) {
        Ok(_) => panic!("effectful-signature function import across cycle must be rejected"),
        Err(err) => err,
    };
    assert!(
        err.to_string().contains("function 'accept'")
            && err.to_string().contains("uses effects")
            && err.to_string().contains("circular import boundary"),
        "expected effectful-signature function diagnostic, got: {}",
        err
    );
}

#[test]
fn cyclic_import_graph_reports_parse_errors() {
    let a = r#"
module A
import B (BThing)
pub type AThing = AThing
"#;
    let b = r#"
module B
import A (AThing)
import C
pub type BThing = BThing
"#;
    let c = r#"
module C
pub fun broken : Unit -> Unit
broken () =
"#;
    let main = "module Main\nimport A (AThing)\nmain () = ()\n";

    let err = match check_with_project_files(
        &[("src/A.saga", a), ("src/B.saga", b), ("src/C.saga", c)],
        main,
    ) {
        Ok(_) => panic!("parse error during graph construction must be reported"),
        Err(err) => err,
    };
    assert!(
        err.to_string().contains("parse error in module 'C'"),
        "expected graph parse diagnostic, got: {}",
        err
    );
}

#[test]
fn auto_load_does_not_inject_alias_prefix_into_scope() {
    // Pinned-down version of the scope-leak prevention. After a canonical
    // reference loads Std.IO.Unsafe, the alias-prefix form `Unsafe.print_stdout`
    // must NOT become resolvable — that would require an explicit
    // `import Std.IO.Unsafe` to merge the alias into scope_map.
    let result = check(
        "main () = {\n\
         let _ = Std.IO.Unsafe.print_stdout \"first\"\n\
         Unsafe.print_stdout \"second\"\n\
         }",
    );
    assert!(
        result.is_err(),
        "alias-prefix form 'Unsafe.print_stdout' must not resolve without an explicit import"
    );
}

#[test]
fn auto_load_does_not_inject_bare_name_into_scope() {
    // Same protection as the alias case but stricter: bare `print_stdout` must
    // not become resolvable just because a canonical sibling reference loaded
    // the module. The user must `import Std.IO.Unsafe (print_stdout)` to expose
    // the bare form.
    let result = check(
        "main () = {\n\
         let _ = Std.IO.Unsafe.print_stdout \"first\"\n\
         print_stdout \"second\"\n\
         }",
    );
    assert!(
        result.is_err(),
        "bare 'print_stdout' must not resolve without an exposing import"
    );
}

#[test]
fn restricted_import_does_not_expose_unlisted_type_bare() {
    let lib = r#"
module Lib

pub type HiddenErr = HiddenErr

pub type Visible = Visible

pub fun make_visible : Unit -> Visible
make_visible () = Visible
"#;
    let main = r#"
module Main
import Lib (make_visible)

fun bad : HiddenErr -> Unit
bad _ = ()
"#;

    let err = check_with_project_files(&[("src/Lib.saga", lib)], main)
        .err()
        .expect("unlisted imported type must not be bare-visible");
    assert!(
        err.to_string().contains("unknown type 'HiddenErr'"),
        "expected unknown type diagnostic, got: {}",
        err
    );
}

#[test]
fn qualified_import_does_not_expose_type_bare() {
    let lib = r#"
module Lib

pub type HiddenErr = HiddenErr

pub fun make_unit : Unit -> Unit
make_unit () = ()
"#;
    let main = r#"
module Main
import Lib

fun bad : HiddenErr -> Unit
bad _ = ()
"#;

    let err = check_with_project_files(&[("src/Lib.saga", lib)], main)
        .err()
        .expect("plain import must not make imported types bare-visible");
    assert!(
        err.to_string().contains("unknown type 'HiddenErr'"),
        "expected unknown type diagnostic, got: {}",
        err
    );
}

#[test]
fn restricted_import_keeps_unlisted_type_available_qualified() {
    let lib = r#"
module Lib

pub type HiddenErr = HiddenErr

pub fun make_visible : Unit -> Unit
make_visible () = ()
"#;
    let main = r#"
module Main
import Lib (make_visible)

fun ok : Lib.HiddenErr -> Unit
ok _ = ()
"#;

    check_with_project_files(&[("src/Lib.saga", lib)], main)
        .expect("unlisted imported type should remain available via module qualification");
}

#[test]
fn auto_load_skips_unknown_module_and_emits_existing_diagnostic() {
    // Auto-load should silently skip module names that aren't in the builtin
    // set or project module map; resolve/infer then emit the existing
    // diagnostic so error messages are unchanged for typos.
    let err = check(
        "main () = {\n\
         Bogus.Module.foo ()\n\
         }",
    )
    .err()
    .expect("unknown qualified name must still error");
    assert!(
        err.message.contains("unknown qualified name") || err.message.contains("Bogus.Module.foo"),
        "expected 'unknown qualified name' diagnostic, got: {}",
        err.message
    );
}

#[test]
fn auto_load_typo_does_not_block_real_canonical_reference_in_same_file() {
    // Mixed: a real auto-loadable canonical ref alongside a typo. The auto-
    // load step skipping the typo must not poison the real reference. The
    // typo errors; the real ref typechecks.
    let err = check(
        "main () = {\n\
         let _ = Std.IO.Unsafe.print_stdout \"real\"\n\
         Bogus.Module.foo ()\n\
         }",
    )
    .err()
    .expect("Bogus.Module.foo must still error");
    assert!(
        !err.message.contains("Std.IO.Unsafe"),
        "typo's diagnostic should be about Bogus.Module, not the real reference: {}",
        err.message
    );
}

// --- Row widening across multi-element forms ---
//
// When N effectful function values appear at the same row-polymorphic
// position (list elements, case arm bodies, if/else branches, tuple
// elements, anonymous record fields paired with a shared row variable),
// the row variable should solve to the UNION of element rows rather than
// pinning to the first one. The "Edda driver" case is a list of route
// handlers with heterogeneous effects passed to a dispatch combinator.

#[test]
fn list_literal_widens_row_across_heterogeneous_effects() {
    check(
        "effect Foo {\n  fun foo : Unit -> Unit\n}\n\
         effect Bar {\n  fun bar : Unit -> Unit\n}\n\
         fun do_foo : Unit -> Unit needs {Foo}\n\
         do_foo () = foo! ()\n\
         fun do_bar : Unit -> Unit needs {Bar}\n\
         do_bar () = bar! ()\n\
         fun pure_thing : Unit -> Unit\n\
         pure_thing () = ()\n\
         fun take_callbacks : List (Unit -> Unit needs {..e}) -> Unit needs {..e}\n\
         take_callbacks fs = case fs {\n  [] -> ()\n  f :: _ -> f ()\n}\n\
         fun caller : Unit -> Unit needs {Foo, Bar}\n\
         caller () = take_callbacks [pure_thing, do_foo, do_bar]",
    )
    .unwrap();
}

#[test]
fn list_literal_pure_only_stays_closed() {
    // Joining over only pure (closed empty) rows produces a closed empty
    // row — no spurious widening, no row variables leak.
    check(
        "fun a : Unit -> Unit\na () = ()\n\
         fun b : Unit -> Unit\nb () = ()\n\
         fun pure_only : Unit -> Unit\n\
         pure_only () = case [a, b] {\n  [] -> ()\n  f :: _ -> f ()\n}",
    )
    .unwrap();
}

#[test]
fn list_literal_single_element_still_typechecks() {
    // Regression for the path I/O of the new spine handler: a one-element
    // list literal (which exercises the spine detection's terminal Nil
    // branch on the first iteration) must still typecheck the same as
    // before. Joining over one element returns it unchanged.
    check(
        "effect Foo {\n  fun foo : Unit -> Unit\n}\n\
         fun do_foo : Unit -> Unit needs {Foo}\n\
         do_foo () = foo! ()\n\
         fun take_callbacks : List (Unit -> Unit needs {..e}) -> Unit needs {..e}\n\
         take_callbacks fs = case fs {\n  [] -> ()\n  f :: _ -> f ()\n}\n\
         fun caller : Unit -> Unit needs {Foo}\n\
         caller () = take_callbacks [do_foo]",
    )
    .unwrap();
}

#[test]
fn case_arms_widen_row_when_branches_return_callbacks() {
    check(
        "effect Foo {\n  fun foo : Unit -> Unit\n}\n\
         effect Bar {\n  fun bar : Unit -> Unit\n}\n\
         fun do_foo : Unit -> Unit needs {Foo}\n\
         do_foo () = foo! ()\n\
         fun do_bar : Unit -> Unit needs {Bar}\n\
         do_bar () = bar! ()\n\
         fun pick : Bool -> Unit -> Unit needs {Foo, Bar}\n\
         pick flag = case flag {\n  True -> do_foo\n  False -> do_bar\n}",
    )
    .unwrap();
}

#[test]
fn case_arms_non_function_result_unchanged() {
    // Case over non-function types still works (degrades to pairwise unify).
    check(
        "fun classify : Int -> String\n\
         classify n = case n {\n  0 -> \"zero\"\n  _ -> \"other\"\n}",
    )
    .unwrap();
}

#[test]
fn if_else_widens_row_when_branches_return_callbacks() {
    check(
        "effect Foo {\n  fun foo : Unit -> Unit\n}\n\
         effect Bar {\n  fun bar : Unit -> Unit\n}\n\
         fun do_foo : Unit -> Unit needs {Foo}\n\
         do_foo () = foo! ()\n\
         fun do_bar : Unit -> Unit needs {Bar}\n\
         do_bar () = bar! ()\n\
         fun pick : Bool -> Unit -> Unit needs {Foo, Bar}\n\
         pick flag = if flag then do_foo else do_bar",
    )
    .unwrap();
}

#[test]
fn tuple_widens_shared_row_var_at_expected_type() {
    check(
        "effect Foo {\n  fun foo : Unit -> Unit\n}\n\
         effect Bar {\n  fun bar : Unit -> Unit\n}\n\
         fun do_foo : Unit -> Unit needs {Foo}\n\
         do_foo () = foo! ()\n\
         fun do_bar : Unit -> Unit needs {Bar}\n\
         do_bar () = bar! ()\n\
         fun run_pair : (Unit -> Unit needs {..e}, Unit -> Unit needs {..e}) -> Unit needs {..e}\n\
         run_pair p = {\n  let (a, b) = p\n  a ()\n  b ()\n}\n\
         fun caller : Unit -> Unit needs {Foo, Bar}\n\
         caller () = run_pair (do_foo, do_bar)",
    )
    .unwrap();
}

#[test]
fn function_with_row_claiming_unavailable_effect_still_rejected() {
    // Row widening must not let a function "fabricate" effects it can't
    // actually require: if take_callbacks claims `needs {..e}` and the
    // caller provides no handler for an effect in the joined row, the
    // caller must declare the effect on its own signature.
    let err = check(
        "effect Foo {\n  fun foo : Unit -> Unit\n}\n\
         fun do_foo : Unit -> Unit needs {Foo}\n\
         do_foo () = foo! ()\n\
         fun take_callbacks : List (Unit -> Unit needs {..e}) -> Unit needs {..e}\n\
         take_callbacks fs = case fs {\n  [] -> ()\n  f :: _ -> f ()\n}\n\
         fun caller : Unit -> Unit\n\
         caller () = take_callbacks [do_foo]",
    )
    .err()
    .expect("caller without 'needs {Foo}' must be rejected");
    assert!(
        err.message.contains("Foo") || err.message.contains("needs"),
        "expected effect declaration diagnostic, got: {}",
        err.message
    );
}

#[test]
fn where_app_accepts_impl_type_parameter_as_old_bound_sugar() {
    check(
        "trait Pretty a { fun pretty : a -> String }\n\
         impl Pretty for Int { pretty n = show n }\n\
         record Box a { value: a }\n\
         impl Pretty for Box a where {Pretty a} {\n\
           pretty b = pretty b.value\n\
         }\n\
         fun go : Box Int -> String\n\
         go b = pretty b",
    )
    .unwrap();
}

#[test]
fn trait_default_body_fires_when_method_omitted() {
    let src = "trait Greet a {\n\
                 fun greet_with : String -> a -> String\n\
                 fun greet : a -> String\n\
                 greet x = greet_with \"hello\" x\n\
               }\n\
               record Person { name: String }\n\
               impl Greet for Person {\n\
                 greet_with prefix p = prefix\n\
               }\n\
               let p = Person { name: \"alice\" }\n\
               let msg = greet p\n";
    check(src).unwrap();
}

#[test]
fn trait_default_body_explicit_override_wins() {
    let src = "trait Greet a {\n\
                 fun greet_with : String -> a -> String\n\
                 fun greet : a -> String\n\
                 greet x = greet_with \"hello\" x\n\
               }\n\
               record Person { name: String }\n\
               impl Greet for Person {\n\
                 greet_with prefix p = prefix\n\
                 greet p = \"override\"\n\
               }\n\
               let p = Person { name: \"alice\" }\n\
               let msg = greet p\n";
    check(src).unwrap();
}

#[test]
fn trait_default_body_missing_required_method_still_errors() {
    let src = "trait Greet a {\n\
                 fun greet_with : String -> a -> String\n\
                 fun greet : a -> String\n\
                 greet x = greet_with \"hello\" x\n\
               }\n\
               record Person { name: String }\n\
               impl Greet for Person {\n\
               }\n";
    let err = match check(src) {
        Err(e) => e,
        Ok(_) => panic!("expected error, but check succeeded"),
    };
    assert!(
        err.message.contains("missing method 'greet_with'"),
        "unexpected error: {}",
        err.message
    );
}

#[test]
fn trait_with_multiple_defaults() {
    let src = "trait MultiDef a {\n\
                 fun root : a -> Int\n\
                 fun double : a -> Int\n\
                 double x = root x + root x\n\
                 fun triple : a -> Int\n\
                 triple x = root x + double x\n\
               }\n\
               record N { v: Int }\n\
               impl MultiDef for N {\n\
                 root n = 1\n\
               }\n\
               let v = triple (N { v: 0 })\n";
    check(src).unwrap();
}

#[test]
fn trait_default_body_parameterized_impl() {
    let src = "trait Wrap a {\n\
                 fun unwrap : a -> Int\n\
                 fun describe : a -> Int\n\
                 describe x = unwrap x + 1\n\
               }\n\
               record Box a { value: a }\n\
               impl Wrap for Box a where {a: Wrap} {\n\
                 unwrap (Box { value: v }) = unwrap v\n\
               }\n\
               impl Wrap for Int { unwrap n = n }\n\
               let n = describe (Box { value: Box { value: 5 } })\n";
    check(src).unwrap();
}

#[test]
fn trait_default_body_cross_module() {
    let lib = "module DefLib\n\
               pub trait Greet a {\n\
               fun greet_with : String -> a -> String\n\
               fun greet : a -> String\n\
               greet x = greet_with \"hi\" x\n\
               }\n";
    let main = "import DefLib (Greet)\n\
                record Person { name: String }\n\
                impl Greet for Person {\n\
                  greet_with prefix p = prefix\n\
                }\n\
                let msg = greet (Person { name: \"alice\" })\n";
    check_with_project_files(&[("lib/DefLib.saga", lib)], main).unwrap();
}

#[test]
fn trait_default_body_cross_module_references_own_constructor() {
    // A default body that constructs a value of a type declared (and exported)
    // alongside the trait: the constructor reference must be qualified to the
    // trait's module when the body is inlined into a downstream impl.
    let lib = "module BoxLib\n\
               pub type Boxed a = Boxed a\n\
               pub trait Boxable a {\n\
               fun box_it : a -> Boxed a\n\
               box_it x = Boxed x\n\
               }\n";
    let main = "import BoxLib (Boxable)\n\
                impl Boxable for Int {}\n\
                let b = box_it 42\n";
    check_with_project_files(&[("lib/BoxLib.saga", lib)], main).unwrap();
}

#[test]
fn trait_default_body_cross_module_references_private_constructor() {
    // Same as above, but the constructed type is NOT exported. The downstream
    // impl can never name the type, yet the inlined default body still needs
    // the constructor's scheme to typecheck.
    let lib = "module BoxLib\n\
               type Boxed a = Boxed a\n\
               pub trait Boxable a {\n\
               fun box_it : a -> Boxed a\n\
               box_it x = Boxed x\n\
               }\n";
    let main = "import BoxLib (Boxable)\n\
                impl Boxable for Int {}\n\
                let b = box_it 42\n";
    check_with_project_files(&[("lib/BoxLib.saga", lib)], main).unwrap();
}

#[test]
fn trait_default_body_with_where_constraint() {
    // The defaulted method's signature carries an extra constraint that the
    // default body must rely on (here implicitly through trait dispatch).
    let src = "trait Pretty a where {a: Show} {\n\
                 fun pretty_with : String -> a -> String\n\
                 fun pretty : a -> String\n\
                 pretty x = pretty_with \"-> \" x\n\
               }\n\
               impl Pretty for Int {\n\
                 pretty_with p n = p <> show n\n\
               }\n\
               let s = pretty 42\n";
    check(src).unwrap();
}

// --- Type aliases ---

#[test]
fn alias_primitive_is_interchangeable_with_underlying() {
    let src = "type alias UserId = Int\n\
               fun f : UserId -> Int\n\
               f x = x + 1\n\
               let y = f 5\n";
    check(src).expect("basic primitive alias should typecheck");
}

#[test]
fn alias_parameterized_is_interchangeable_with_underlying() {
    let src = "type alias Bag a = List a\n\
               fun first : Bag Int -> Maybe Int\n\
               first xs = case xs {\n\
                 [] -> Nothing\n\
                 x :: _ -> Just x\n\
               }\n";
    check(src).expect("parameterized alias should typecheck");
}

#[test]
fn alias_pattern_match_through_to_underlying_constructors() {
    let src = "type alias Outcome a = Result a String\n\
               fun handle : Outcome Int -> Int\n\
               handle r = case r {\n\
                 Ok n -> n\n\
                 Err _ -> 0\n\
               }\n";
    check(src).expect("alias should unfold for pattern matching");
}

#[test]
fn alias_cycle_self_reference_is_rejected() {
    let src = "type alias T = List T\n";
    let err = check(src).err().expect("expected cycle diagnostic");
    let msg = err.message.to_lowercase();
    assert!(
        msg.contains("recursive") && msg.contains("t"),
        "expected recursive-alias diagnostic, got: {}",
        err.message
    );
}

#[test]
fn alias_mutual_cycle_is_rejected() {
    let src = "type alias A = B\n\
               type alias B = A\n";
    let err = check(src).err().expect("expected cycle diagnostic");
    assert!(
        err.message.to_lowercase().contains("recursive"),
        "expected recursive-alias diagnostic, got: {}",
        err.message
    );
}

#[test]
fn alias_partial_application_is_rejected() {
    // Bag requires 1 arg; using it without an arg should fail.
    let src = "type alias Bag a = List a\n\
               fun bad : Bag -> Int\n\
               bad _ = 0\n";
    let err = check(src).err().expect("expected partial alias diagnostic");
    let msg = err.message.to_lowercase();
    assert!(
        msg.contains("alias") && msg.contains("bag"),
        "expected partial-alias diagnostic, got: {}",
        err.message
    );
}

#[test]
fn alias_over_application_is_rejected() {
    // UserId has arity 0; applying any arg should fail.
    let src = "type alias UserId = Int\n\
               fun bad : UserId Int -> Int\n\
               bad _ = 0\n";
    let err = check(src)
        .err()
        .expect("expected over-application diagnostic");
    assert!(
        err.message.to_lowercase().contains("argument"),
        "expected over-application diagnostic, got: {}",
        err.message
    );
}

#[test]
fn alias_impl_target_is_rejected() {
    let src = "type alias UserId = Int\n\
               trait Tagged a { fun tag : a -> Int }\n\
               impl Tagged for UserId { tag x = x }\n";
    let err = check(src).err().expect("expected impl-on-alias diagnostic");
    let msg = err.message.to_lowercase();
    assert!(
        msg.contains("alias") && msg.contains("userid"),
        "expected impl-on-alias diagnostic, got: {}",
        err.message
    );
}

#[test]
fn alias_cross_module_round_trips() {
    let lib = "module Lib\n\
               pub type alias UserId = Int\n";
    let main = "import Lib\n\
                fun consume : Lib.UserId -> Int\n\
                consume x = x + 1\n\
                let y = consume 7\n";
    check_with_project_files(&[("lib/Lib.saga", lib)], main)
        .expect("cross-module alias should resolve");
}

#[test]
fn alias_to_opaque_type_does_not_leak_constructors() {
    // Even though Lib exports a `pub type alias` over the opaque type,
    // the importer still cannot construct the opaque type because
    // constructor visibility is independent of type-name visibility.
    let lib = "module Lib\n\
               opaque type Secret = Hidden Int\n\
               pub type alias Token = Secret\n";
    let main = "import Lib\n\
                fun build : Int -> Lib.Token\n\
                build n = Hidden n\n";
    let err = check_with_project_files(&[("lib/Lib.saga", lib)], main)
        .err()
        .expect("constructor must not leak through alias");
    let msg = err.message.to_lowercase();
    assert!(
        msg.contains("hidden") || msg.contains("unknown") || msg.contains("constructor"),
        "expected unknown-constructor diagnostic, got: {}",
        err.message
    );
}

#[test]
fn alias_body_with_undeclared_type_var_is_rejected() {
    let src = "type alias Foo = Maybe b\n";
    let err = check(src)
        .err()
        .expect("expected undeclared-var diagnostic");
    let msg = err.message.to_lowercase();
    assert!(
        msg.contains("undeclared") && msg.contains("`b`"),
        "expected undeclared-var diagnostic, got: {}",
        err.message
    );
}

#[test]
fn alias_body_with_declared_type_var_is_accepted() {
    let src = "type alias Foo b = Maybe b\n\
               fun get : Foo Int -> Int\n\
               get _ = 0\n";
    check(src).expect("declared var in alias body should typecheck");
}

#[test]
fn alias_body_partial_use_is_rejected_at_declaration() {
    // Bag has arity 1; `Bag` without an arg in another alias body should
    // fail at the alias declaration, not be deferred to use sites.
    let src = "type alias Bag a = List a\n\
               type alias Bad = Bag\n";
    let err = check(src).err().expect("expected partial-alias diagnostic");
    let msg = err.message.to_lowercase();
    assert!(
        msg.contains("alias") && msg.contains("bag"),
        "expected partial-alias diagnostic at the declaration, got: {}",
        err.message
    );
}

#[test]
fn impl_for_tuple_pair_typechecks() {
    check(
        "trait ToJson a {\n\
           fun to_json : a -> String\n\
         }\n\
         impl ToJson for Int {\n\
           to_json n = show n\n\
         }\n\
         impl ToJson for (a, b) where {a: ToJson, b: ToJson} {\n\
           to_json p = {\n\
             let (x, y) = p\n\
             to_json x <> to_json y\n\
           }\n\
         }\n\
         fun use_it : Unit -> String\n\
         use_it () = to_json (1, 2)\n",
    )
    .unwrap();
}

#[test]
fn impl_for_structured_tuple_target_typechecks() {
    check(
        "trait PgType a { fun pg : a -> String }\n\
         impl PgType for Int { pg _ = \"int\" }\n\
         impl PgType for String { pg _ = \"string\" }\n\
         type Column source name a = Column a\n\
         type Projection row = Projection row\n\
         trait Selectable selection row {\n\
           fun to_projection : selection -> Projection row\n\
         }\n\
         impl Selectable (a, b) for (Column sa na a, Column sb nb b) where {a: PgType, b: PgType} {\n\
           to_projection pair = {\n\
             let (Column x, Column y) = pair\n\
             Projection (x, y)\n\
           }\n\
         }\n\
         fun use_it : Unit -> Projection (Int, String)\n\
         use_it () = to_projection (Column 1, Column \"title\")\n",
    )
    .unwrap();
}

#[test]
fn impl_for_structured_tuple_target_requires_nested_constraints() {
    let err = check(
        "trait PgType a { fun pg : a -> String }\n\
         impl PgType for Int { pg _ = \"int\" }\n\
         type Column source name a = Column a\n\
         type Projection row = Projection row\n\
         trait Selectable selection row {\n\
           fun to_projection : selection -> Projection row\n\
         }\n\
         impl Selectable (a, b) for (Column sa na a, Column sb nb b) where {a: PgType, b: PgType} {\n\
           to_projection pair = {\n\
             let (Column x, Column y) = pair\n\
             Projection (x, y)\n\
           }\n\
         }\n\
         fun use_it : Unit -> Projection (Int, String)\n\
         use_it () = to_projection (Column 1, Column \"title\")\n",
    )
    .err()
    .expect("expected missing PgType String");
    assert!(
        err.message.contains("no impl") && err.message.contains("PgType"),
        "expected missing PgType diagnostic, got: {}",
        err.message
    );
}

#[test]
fn impl_for_structured_tuple_target_overlaps_generic_tuple_impl() {
    let err = check(
        "trait Selectable selection row {\n\
           fun to_projection : selection -> row\n\
         }\n\
         type Column source name a = Column a\n\
         impl Selectable (a, b) for (a, b) {\n\
           to_projection pair = pair\n\
         }\n\
         impl Selectable (a, b) for (Column sa na a, Column sb nb b) {\n\
           to_projection pair = pair\n\
         }\n",
    )
    .err()
    .expect("expected overlapping impl diagnostic");
    assert!(
        err.message.contains("duplicate impl") || err.message.contains("already implemented"),
        "expected overlap/duplicate diagnostic, got: {}",
        err.message
    );
}

#[test]
fn impl_for_tuple_pair_and_triple_coexist() {
    check(
        "trait ToJson a {\n\
           fun to_json : a -> String\n\
         }\n\
         impl ToJson for Int {\n\
           to_json n = show n\n\
         }\n\
         impl ToJson for (a, b) where {a: ToJson, b: ToJson} {\n\
           to_json p = {\n\
             let (x, y) = p\n\
             to_json x <> to_json y\n\
           }\n\
         }\n\
         impl ToJson for (a, b, c) where {a: ToJson, b: ToJson, c: ToJson} {\n\
           to_json t = {\n\
             let (x, y, z) = t\n\
             to_json x <> to_json y <> to_json z\n\
           }\n\
         }\n",
    )
    .unwrap();
}

#[test]
fn impl_for_tuple_same_arity_is_duplicate() {
    let err = check(
        "trait ToJson a {\n\
           fun to_json : a -> String\n\
         }\n\
         impl ToJson for (a, b) where {a: ToJson, b: ToJson} {\n\
           to_json p = \"first\"\n\
         }\n\
         impl ToJson for (a, b) where {a: ToJson, b: ToJson} {\n\
           to_json p = \"second\"\n\
         }\n",
    )
    .err()
    .expect("expected duplicate impl diagnostic");
    assert!(
        err.message.contains("duplicate impl"),
        "expected duplicate-impl diagnostic, got: {}",
        err.message
    );
}

#[test]
fn impl_for_tuple_missing_element_constraint_is_error() {
    // Constraint resolution on `to_json (1, "hi")` requires impls for both
    // Int and String; without `impl ToJson for String` we should error.
    let err = check(
        "trait ToJson a {\n\
           fun to_json : a -> String\n\
         }\n\
         impl ToJson for Int {\n\
           to_json n = show n\n\
         }\n\
         impl ToJson for (a, b) where {a: ToJson, b: ToJson} {\n\
           to_json p = {\n\
             let (x, y) = p\n\
             to_json x <> to_json y\n\
           }\n\
         }\n\
         fun use_it : Unit -> String\n\
         use_it () = to_json (1, \"hi\")\n",
    )
    .err()
    .expect("expected no-impl diagnostic for String");
    assert!(
        err.message.contains("no impl of ToJson") && err.message.contains("String"),
        "expected missing-impl-of-ToJson-for-String, got: {}",
        err.message
    );
}

fn record_builder_fixture(body: &str) -> String {
    format!(
        "type Projection a = Projection a\n\
         fun projection_start : (a -> b) -> Projection (a -> b)\n\
         projection_start f = Projection f\n\
         fun projection_field : String -> Projection a -> Projection (a -> b) -> Projection b\n\
         projection_field _ arg ctor = case arg {{\n\
           Projection a -> case ctor {{\n\
             Projection f -> Projection (f a)\n\
           }}\n\
         }}\n\
         record builder Projection {{ start: projection_start, field: projection_field }}\n\
         record User {{ name: String, age: Int }}\n\
         let name_p = Projection \"Ada\"\n\
         let age_p = Projection 42\n\
         {}",
        body
    )
}

#[test]
fn record_build_named_typechecks_through_builder_functions() {
    check(&record_builder_fixture(
        "fun ok : Unit -> Projection User\n\
         ok () = build Projection User { age: age_p, name: name_p }\n",
    ))
    .unwrap();
}

#[test]
fn record_build_anonymous_typechecks_with_synthesized_constructor() {
    check(&record_builder_fixture(
        "fun ok : Unit -> Projection { age: Int, name: String }\n\
         ok () = build Projection { name: name_p, age: age_p }\n",
    ))
    .unwrap();
}

#[test]
fn record_build_named_reports_missing_field() {
    let err = check(&record_builder_fixture(
        "fun bad : Unit -> Projection User\n\
         bad () = build Projection User { name: name_p }\n",
    ))
    .err()
    .expect("expected missing-field diagnostic");
    assert!(
        err.message.contains("missing field") && err.message.contains("age"),
        "expected missing-field diagnostic, got: {}",
        err.message
    );
}

#[test]
fn record_build_named_reports_unknown_field() {
    let err = check(&record_builder_fixture(
        "fun bad : Unit -> Projection User\n\
         bad () = build Projection User { name: name_p, age: age_p, bogus: age_p }\n",
    ))
    .err()
    .expect("expected unknown-field diagnostic");
    assert!(
        err.message.contains("unknown field") && err.message.contains("bogus"),
        "expected unknown-field diagnostic, got: {}",
        err.message
    );
}

fn record_builder_module() -> &'static str {
    r#"
module Db

pub type Selection = Selection
pub type Projection a = Projection a

pub fun projection_start : (a -> b) -> Projection (a -> b)
projection_start f = Projection f

pub fun projection_field : String -> Projection a -> Projection (a -> b) -> Projection b
projection_field _ arg ctor = case arg {
  Projection a -> case ctor {
    Projection f -> Projection (f a)
  }
}

pub record builder Selection {
  start: projection_start,
  field: projection_field,
}

pub record User {
  name: String,
  age: Int,
}

pub fun name_p : Projection String
name_p = Projection "Ada"

pub fun age_p : Projection Int
age_p = Projection 42
"#
}

#[test]
fn record_builder_imported_with_context_type() {
    let main = r#"
module Main
import Db (Selection, Projection, User, name_p, age_p)

fun ok : Unit -> Projection User
ok () = build Selection User { name: name_p, age: age_p }
"#;

    check_with_project_files(&[("src/Db.saga", record_builder_module())], main).unwrap();
}

#[test]
fn record_builder_reexported_with_public_all_import() {
    let lib = r#"
module Lib
import Db (pub ..)
"#;
    let main = r#"
module Main
import Lib (Selection, Projection, User, name_p, age_p)

fun ok : Unit -> Projection User
ok () = build Selection User { name: name_p, age: age_p }
"#;

    check_with_project_files(
        &[
            ("src/Db.saga", record_builder_module()),
            ("src/Lib.saga", lib),
        ],
        main,
    )
    .unwrap();
}

#[test]
fn private_record_builder_is_not_imported_with_context_type() {
    let db = record_builder_module().replace("pub record builder", "record builder");
    let main = r#"
module Main
import Db (Selection, Projection, User, name_p, age_p)

fun bad : Unit -> Projection User
bad () = build Selection User { name: name_p, age: age_p }
"#;

    let err = check_with_project_files(&[("src/Db.saga", db.as_str())], main)
        .err()
        .expect("expected missing record builder diagnostic");
    assert!(
        err.message.contains("no record builder"),
        "expected missing record builder diagnostic, got: {}",
        err.message
    );
}
