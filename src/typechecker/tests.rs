use super::*;
use crate::lexer::Lexer;
use crate::parser::Parser;

fn check(src: &str) -> Result<Checker, Diagnostic> {
    let mut lexer = Lexer::new(src);
    let tokens = lexer.lex().expect("lex error");
    let mut parser = Parser::new(tokens);
    let mut program = parser.parse_program().expect("parse error");
    crate::derive::expand_derives(&mut program);
    let mut checker = Checker::new();
    // Load prelude (which imports Std first, then stdlib modules)
    let prelude_src = include_str!("../stdlib/prelude.dy");
    let prelude_tokens = Lexer::new(prelude_src).lex().expect("prelude lex error");
    let mut prelude_program = Parser::new(prelude_tokens)
        .parse_program()
        .expect("prelude parse error");
    crate::derive::expand_derives(&mut prelude_program);
    checker
        .check_program_inner(&prelude_program)
        .map_err(|e| e.into_iter().next().unwrap())?;
    checker
        .check_program_inner(&program)
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
        Type::Arrow(a, b) => assert_eq!(a, b),
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
    assert_eq!(
        ty,
        Type::Arrow(Box::new(Type::int()), Box::new(Type::int()))
    );
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
    let ty = infer_expr_type("case 5 {\n  x | x > 0 -> \"positive\"\n  _ -> \"non-positive\"\n}")
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
    assert_eq!(
        ty,
        Type::Arrow(Box::new(Type::int()), Box::new(Type::int()))
    );
}

#[test]
fn multi_clause_with_guards() {
    let checker = check("abs n | n < 0 = 0 - n\nabs n = n").unwrap();
    let scheme = checker.env.get("abs").unwrap();
    let ty = checker.sub.apply(&scheme.ty);
    assert_eq!(
        ty,
        Type::Arrow(Box::new(Type::int()), Box::new(Type::int()))
    );
}

#[test]
fn multi_clause_literal_patterns() {
    let checker = check("fib 0 = 0\nfib 1 = 1\nfib n = fib (n - 1) + fib (n - 2)").unwrap();
    let scheme = checker.env.get("fib").unwrap();
    let ty = checker.sub.apply(&scheme.ty);
    assert_eq!(
        ty,
        Type::Arrow(Box::new(Type::int()), Box::new(Type::int()))
    );
}

#[test]
fn mutual_recursion() {
    let checker = check("is_even n = if n == 0 then True else is_odd (n - 1)\nis_odd n = if n == 0 then False else is_even (n - 1)").unwrap();
    let even_ty = checker.sub.apply(&checker.env.get("is_even").unwrap().ty);
    assert_eq!(
        even_ty,
        Type::Arrow(Box::new(Type::int()), Box::new(Type::bool()))
    );
    let odd_ty = checker.sub.apply(&checker.env.get("is_odd").unwrap().ty);
    assert_eq!(
        odd_ty,
        Type::Arrow(Box::new(Type::int()), Box::new(Type::bool()))
    );
}

#[test]
fn list_cons_expression() {
    let checker = check("let xs = 1 :: 2 :: Nil").unwrap();
    let ty = checker.sub.apply(&checker.env.get("xs").unwrap().ty);
    assert_eq!(ty, Type::Con("List".into(), vec![Type::int()]));
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
        Type::Arrow(
            Box::new(Type::Con("Point".into(), vec![])),
            Box::new(Type::int())
        )
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
        Type::Arrow(
            Box::new(Type::Con("User".into(), vec![])),
            Box::new(Type::string())
        )
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
        Type::Arrow(arg, ret) => {
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
    assert_eq!(
        ty,
        Type::Arrow(Box::new(Type::int()), Box::new(Type::int()))
    );
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
        Type::Arrow(
            Box::new(Type::int()),
            Box::new(Type::Arrow(Box::new(Type::int()), Box::new(Type::int())))
        )
    );
}

#[test]
fn annotation_constrains_polymorphism() {
    // id without annotation is polymorphic; with annotation it's constrained to Int -> Int
    let checker = check("fun myid : (x: Int) -> Int\nmyid x = x").unwrap();
    let ty = checker.sub.apply(&checker.env.get("myid").unwrap().ty);
    assert_eq!(
        ty,
        Type::Arrow(Box::new(Type::int()), Box::new(Type::int()))
    );
}

#[test]
fn annotation_polymorphic() {
    // fun id : (x: a) -> a should work with the polymorphic identity
    let checker = check("fun id : (x: a) -> a\nid x = x").unwrap();
    let scheme = checker.env.get("id").unwrap();
    let ty = checker.sub.apply(&scheme.ty);
    match ty {
        Type::Arrow(a, b) => assert_eq!(a, b),
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

#[test]
fn effect_call_without_needs_is_error() {
    let result = check("effect Fail {\n  fun fail : (msg: String) -> a\n}\nfoo x = fail! \"oops\"");
    assert!(result.is_err());
    let err = result.err().expect("expected error");
    assert!(
        err.message.contains("needs"),
        "expected needs error, got: {}",
        err.message
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
    // Calling a function that needs {Fail} requires the caller to also declare needs {Fail}
    let result = check(
        "effect Fail {\n  fun fail : (msg: String) -> a\n}\nfun bar : (x: Int) -> Int needs {Fail}\nbar x = fail! \"oops\"\nfoo x = bar x",
    );
    assert!(result.is_err());
    let err = result.err().expect("expected error");
    assert!(
        err.message.contains("Fail"),
        "expected Fail propagation error, got: {}",
        err.message
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
fn handler_arm_body_effect_handled_by_sibling() {
    // An inline handler arm body uses Log, which is handled by a sibling
    // named handler in the same `with`. Should not require `needs` on caller.
    check(
        "effect Log {\n  fun log : (msg: String) -> Unit\n}\n\
         effect Fail {\n  fun fail : (msg: String) -> a\n}\n\
         handler silent for Log {\n  log msg = resume ()\n}\n\
         fun risky : Unit -> Int needs {Fail, Log}\n\
         risky () = fail! \"oops\"\n\
         main () = risky () with {\n  silent,\n  fail msg = {\n    log! (\"caught: \" <> msg)\n    0\n  }\n}",
    )
    .unwrap();
}

#[test]
fn handler_arm_body_unhandled_effect_propagates() {
    // An inline handler arm body uses Log, but Log is NOT handled by the `with`.
    // Should require `needs {Log}` on the enclosing function.
    let result = check(
        "effect Log {\n  fun log : (msg: String) -> Unit\n}\n\
         effect Fail {\n  fun fail : (msg: String) -> a\n}\n\
         fun risky : Unit -> Int needs {Fail}\n\
         risky () = fail! \"oops\"\n\
         foo () = risky () with {\n  fail msg = {\n    log! \"caught\"\n    0\n  }\n}",
    );
    assert!(result.is_err());
    let err = result.err().expect("expected error");
    assert!(
        err.message.contains("Log"),
        "expected Log propagation error, got: {}",
        err.message
    );
}

#[test]
fn lambda_effects_propagate_to_enclosing_function() {
    // Effects inside a lambda propagate up to the enclosing function boundary
    let result =
        check("effect Fail {\n  fun fail : (msg: String) -> a\n}\nfoo x = fun y -> fail! \"oops\"");
    assert!(result.is_err());
    let err = result.err().expect("expected error");
    assert!(
        err.message.contains("Fail"),
        "expected Fail in error, got: {}",
        err.message
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
        "effect Fail {\n  fun fail : (msg: String) -> a\n}\nfun run : (f: () -> Int needs {Fail}) -> Int\nrun f = f () with { fail msg = 0 }\nfoo x = run (fun () -> fail! \"oops\")",
    )
    .unwrap();
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
    // Handler handles Log but not Fail, so Fail still needs declaration
    let result = check(
        "effect Fail {\n  fun fail : (msg: String) -> a\n}\neffect Log {\n  fun log : (msg: String) -> Unit\n}\nhandler console for Log {\n  log msg = println msg\n}\nfoo x = {\n  log! \"hello\"\n  fail! \"oops\"\n} with console",
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
fn pure_function_no_needs_ok() {
    // Pure functions without effects don't need any annotation
    check("add a b = a + b").unwrap();
}

// --- Traits ---

#[test]
fn trait_method_in_env() {
    let checker = check("trait Greet a {\n  fun greet : (x: a) -> String\n}").unwrap();
    let scheme = checker.env.get("greet").unwrap();
    let ty = checker.sub.apply(&scheme.ty);
    match ty {
        Type::Arrow(_, ret) => assert_eq!(*ret, Type::string()),
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
  fun get : (x: a) -> String
}
impl Store for Redis needs {Fail} {
  get s = fail! \"oops\"
}",
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
record Bar { val: Int }
impl Show for Bar {
  show b = \"Bar\"
}
impl Eq for Bar {
  eq a b = a.val == b.val
}
impl Special for Bar {
  special b = show b
}
main () = special (Bar { val: 1 })",
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
record Bar { val: Int }
impl Show for Bar {
  show b = \"Bar\"
}
impl Special for Bar {
  special b = show b
}
main () = special (Bar { val: 1 })",
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
    check("main () = println (show 42)").unwrap();
    check("main () = println (show 1.5)").unwrap();
    check("main () = println \"hello\"").unwrap();
    check("main () = println (show True)").unwrap();
    check("main () = println (debug ())").unwrap();
    check("let x = show 42\nmain () = println x").unwrap();
}

#[test]
fn show_fails_for_custom_type_without_impl() {
    let result = check(
        "record Foo { x: Int }
main () = println (show (Foo { x: 1 }))",
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
main () = println (show (Foo { x: 1 }))",
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
fn mod_on_float_fails() {
    let result = check("main () = 1.0 % 2.0");
    assert!(result.is_err());
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
  Just(n) | n > 0 -> n
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
  Just(n) | n > 0 -> n
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
  Just(n) | n > 0 -> n
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

// Dict.put, Dict.keys, Dict.values, Dict.size, Dict.from_list, Dict.to_list,
// Dict.member are now defined in Std/Dict.dy via @external declarations.
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
  n | check! n -> n
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
filter x | check! x = x
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
  n | n < 0 -> 0
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
  fun put : (val: s) -> Unit
}

handler counter for State Int {
  get () = resume 0
  put val = resume ()
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
  fun put : (val: s) -> Unit
}

handler string_state for State String {
  get () = resume \"hello\"
  put val = resume ()
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
  fun put : (val: s) -> Unit
}

handler bad for State Int {
  get () = resume \"not an int\"
  put val = resume ()
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
  fun put : (val: s) -> Unit
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
  fun put : (val: s) -> Unit
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
  fun write : (key: k) -> (val: v) -> Unit
}

handler dict_store for Store String Int {
  read key = resume 0
  write key val = resume ()
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
  fun put : (val: s) -> Unit
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
  fun put : (val: s) -> Unit
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
  fun put : (val: s) -> Unit
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
  fun put : (val: s) -> Unit
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
  fun put : (val: s) -> Unit
}

type List a = Nil | Cons(a, List a)

handler list_state for State (List Int) {
  get () = resume Nil
  put val = resume ()
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
  fun put : (val: s) -> Unit
}

type Result a = Ok(a) | Err(String)

handler safe_state for State Int {
  get () = resume 0
  put val = resume ()
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
  fun put : (val: s) -> Unit
  fun modify : (f: s -> s) -> Unit
}

handler counter for State Int {
  get () = resume 0
  put val = resume ()
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
  fun put : (val: s) -> Unit
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
  fun write : (key: k) -> (val: v) -> Unit
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
  fun put : (val: s) -> Unit
}

handler int_state for State Int {
  get () = resume 0
  put val = resume ()
}

handler string_state for State String {
  get () = resume \"\"
  put val = resume ()
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

fun main : Unit -> Unit
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
  fun put : (val: s) -> Unit
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
  fun put : (val: s) -> Unit
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
  fun put : (val: s) -> Unit
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
  fun put : (val: s) -> Unit
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
  fun put : (val: s) -> Unit
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
  fun put : (val: s) -> Unit
}

fun run_state : (init: s) -> (f: () -> a needs {State s}) -> (a, s)
run_state init f = (f (), init)

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
}"
    );
    assert!(result.is_err());
}

#[test]
fn main_cannot_have_effects() {
    let result = check(
        "effect Log {
  fun log : (msg: String) -> Unit
}

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
import Std.Actor

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
import Std.Actor

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
    check("fun myAdd : Int -> Int -> Int\nmyAdd a b = a + b\nincrement = myAdd 1\nmain () = println (show (increment 6))").unwrap();
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
fn with_on_pure_call_is_error() {
    let result = check(
        "effect Boom {\n  fun boom : (msg: String) -> a\n}\nfun myAdd : Int -> Int -> Int\nmyAdd a b = a + b\nmain () = myAdd 1 2 with { boom msg = 0 }",
    );
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message.contains("unnecessary"),
        "expected unnecessary handler message, got: {}",
        err.message
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

// --- Effect row polymorphism ---

#[test]
fn effect_row_var_basic_hof() {
    // HOF with open effect row: lambda with extra effects is accepted.
    // The extra Log effect propagates through ..e to the caller.
    check(
        "effect Assert {\n  fun assert_ok : (ok: Bool) -> Unit\n}\neffect Log {\n  fun log : (msg: String) -> Unit\n}\nfun run : (f: () -> Unit needs {Assert, ..e}) -> Unit needs {..e}\nrun f = f () with { assert_ok ok = () }\nfun caller : Unit needs {Log}\ncaller = run (fun () -> {\n  assert_ok! True\n  log! \"hello\"\n})",
    )
    .unwrap();
}

#[test]
fn effect_row_var_pure_lambda_satisfies_open_row() {
    // A pure lambda satisfies a parameter with an open effect row
    check(
        "effect Chk {\n  fun chk : (ok: Bool) -> Unit\n}\nfun run : (f: () -> Unit needs {..e}) -> Unit needs {..e}\nrun f = f ()\nmain () = run (fun () -> ())",
    )
    .unwrap();
}

#[test]
fn effect_row_var_propagation() {
    // Extra effects from the lambda propagate through the row variable
    // to the caller's needs clause
    check(
        "effect Fail {\n  fun fail : (msg: String) -> a\n}\neffect Log {\n  fun log : (msg: String) -> Unit\n}\nfun run_with_fail : (f: () -> Int needs {Fail, ..e}) -> Int needs {..e}\nrun_with_fail f = f () with { fail msg = 0 }\nfun caller : Int needs {Log}\ncaller = run_with_fail (fun () -> {\n  log! \"hello\"\n  fail! \"oops\"\n})",
    )
    .unwrap();
}

#[test]
fn effect_row_var_only_row_var() {
    // `needs {..e}` with no concrete effects
    check(
        "fun apply : (f: () -> Int needs {..e}) -> Int needs {..e}\napply f = f ()\nmain () = apply (fun () -> 42)",
    )
    .unwrap();
}

#[test]
fn effect_row_var_closed_row_rejects_extra_effects() {
    // A lambda with extra effects should be rejected when the parameter has a closed row
    let result = check(
        "effect Assert {\n  fun assert_ok : (ok: Bool) -> Unit\n}\neffect Log {\n  fun log : (msg: String) -> Unit\n}\nfun run : (f: () -> Unit needs {Assert}) -> Unit\nrun f = f () with { assert_ok ok = () }\nmain () = run (fun () -> {\n  assert_ok! True\n  log! \"hello\"\n})",
    );
    assert!(result.is_err(), "expected error for extra effects in closed row");
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
        "effect Log {\n  fun log : (msg: String) -> Unit\n}\nfun run_pure : (f: () -> Int needs {}) -> Int\nrun_pure f = f ()\nmain () = run_pure (fun () -> {\n  log! \"hello\"\n  42\n})",
    );
    assert!(result.is_err(), "expected error: effectful lambda passed to pure parameter");
}

#[test]
fn needs_empty_accepts_pure_lambda() {
    // `needs {}` should accept a pure lambda
    check(
        "fun run_pure : (f: () -> Int needs {}) -> Int\nrun_pure f = f ()\nmain () = run_pure (fun () -> 42)",
    )
    .unwrap();
}
