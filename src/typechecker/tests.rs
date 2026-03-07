use super::*;
use crate::lexer::Lexer;
use crate::parser::Parser;

fn check(src: &str) -> Result<Checker, TypeError> {
    let mut lexer = Lexer::new(src);
    let tokens = lexer.lex().expect("lex error");
    let mut parser = Parser::new(tokens);
    let program = parser.parse_program().expect("parse error");
    let mut checker = Checker::new();
    checker.check_program(&program)?;
    Ok(checker)
}

fn infer_expr_type(src: &str) -> Result<Type, TypeError> {
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
    assert_eq!(ty, Type::Arrow(Box::new(Type::int()), Box::new(Type::int())));
}

#[test]
fn block_returns_last() {
    let ty = infer_expr_type("{\n  let x = 1\n  x + 2\n}").unwrap();
    assert_eq!(ty, Type::int());
}

#[test]
fn constructor_type() {
    let checker = check("type Maybe a {\n  Just(a)\n  Nothing\n}\nlet x = Just 42").unwrap();
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
        check("type Maybe a {\n  Just(a)\n  Nothing\n}\nlet x = case Just 42 {\n  Just(n) -> n + 1\n  Nothing -> 0\n}")
            .unwrap();
    let ty = checker.sub.apply(&checker.env.get("x").unwrap().ty);
    assert_eq!(ty, Type::int());
}

#[test]
fn case_branch_type_mismatch() {
    let result = check(
        "type Maybe a {\n  Just(a)\n  Nothing\n}\nlet x = case Just 42 {\n  Just(n) -> n\n  Nothing -> \"nope\"\n}",
    );
    assert!(result.is_err());
}

#[test]
fn case_binds_pattern_vars() {
    let checker =
        check("type Maybe a {\n  Just(a)\n  Nothing\n}\nlet x = case Just \"hello\" {\n  Just(s) -> s <> \" world\"\n  Nothing -> \"default\"\n}")
            .unwrap();
    let ty = checker.sub.apply(&checker.env.get("x").unwrap().ty);
    assert_eq!(ty, Type::string());
}

#[test]
fn case_with_guard() {
    let ty =
        infer_expr_type("case 5 {\n  x if x > 0 -> \"positive\"\n  _ -> \"non-positive\"\n}")
            .unwrap();
    assert_eq!(ty, Type::string());
}

#[test]
fn case_pattern_vars_dont_leak() {
    let result = check(
        "type Maybe a {\n  Just(a)\n  Nothing\n}\nlet x = case Just 42 {\n  Just(n) -> n\n  Nothing -> n\n}",
    );
    assert!(result.is_err());
}

#[test]
fn constructor_no_args() {
    let checker = check("type Maybe a {\n  Just(a)\n  Nothing\n}\nlet x = Nothing").unwrap();
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
    assert_eq!(ty, Type::Arrow(Box::new(Type::int()), Box::new(Type::int())));
}

#[test]
fn multi_clause_with_guards() {
    let checker = check("abs n | n < 0 = 0 - n\nabs n = n").unwrap();
    let scheme = checker.env.get("abs").unwrap();
    let ty = checker.sub.apply(&scheme.ty);
    assert_eq!(ty, Type::Arrow(Box::new(Type::int()), Box::new(Type::int())));
}

#[test]
fn multi_clause_literal_patterns() {
    let checker = check("fib 0 = 0\nfib 1 = 1\nfib n = fib (n - 1) + fib (n - 2)").unwrap();
    let scheme = checker.env.get("fib").unwrap();
    let ty = checker.sub.apply(&scheme.ty);
    assert_eq!(ty, Type::Arrow(Box::new(Type::int()), Box::new(Type::int())));
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
    let checker =
        check("record Point { x: Int, y: Int }\nlet p = Point { x: 3, y: 4 }").unwrap();
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
fn annotation_correct() {
    let checker = check(
        "fun fib (n: Int) -> Int\nfib 0 = 0\nfib 1 = 1\nfib n = fib (n - 1) + fib (n - 2)",
    )
    .unwrap();
    let ty = checker.sub.apply(&checker.env.get("fib").unwrap().ty);
    assert_eq!(ty, Type::Arrow(Box::new(Type::int()), Box::new(Type::int())));
}

#[test]
fn annotation_mismatch() {
    let result = check("fun add (a: Int) (b: Int) -> String\nadd a b = a + b");
    assert!(result.is_err());
}

#[test]
fn annotation_multi_param() {
    let checker = check("fun add (a: Int) (b: Int) -> Int\nadd a b = a + b").unwrap();
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
    let checker = check("fun myid (x: Int) -> Int\nmyid x = x").unwrap();
    let ty = checker.sub.apply(&checker.env.get("myid").unwrap().ty);
    assert_eq!(ty, Type::Arrow(Box::new(Type::int()), Box::new(Type::int())));
}

#[test]
fn annotation_polymorphic() {
    // fun id (x: a) -> a should work with the polymorphic identity
    let checker = check("fun id (x: a) -> a\nid x = x").unwrap();
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
    let result = check(
        "effect Fail {\n  fun fail (msg: String) -> a\n}\nfoo x = fail! \"oops\"",
    );
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
        "effect Fail {\n  fun fail (msg: String) -> a\n}\nfun foo (x: Int) -> Int needs {Fail}\nfoo x = fail! \"oops\"",
    )
    .unwrap();
}

#[test]
fn effect_call_with_wrong_needs() {
    let result = check(
        "effect Fail {\n  fun fail (msg: String) -> a\n}\neffect Log {\n  fun log (msg: String) -> Unit\n}\nfun foo (x: Int) -> Int needs {Log}\nfoo x = fail! \"oops\"",
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
        "effect Fail {\n  fun fail (msg: String) -> a\n}\nhandler catch_fail for Fail {\n  fail msg -> 0\n}\nmain x = (fail! \"oops\") with catch_fail",
    )
    .unwrap();
}

#[test]
fn effect_handled_with_inline_handler() {
    check(
        "effect Fail {\n  fun fail (msg: String) -> a\n}\nmain x = (fail! \"oops\") with {\n  fail msg -> 0\n}",
    )
    .unwrap();
}

#[test]
fn effect_propagates_through_function_call() {
    // Calling a function that needs {Fail} requires the caller to also declare needs {Fail}
    let result = check(
        "effect Fail {\n  fun fail (msg: String) -> a\n}\nfun bar (x: Int) -> Int needs {Fail}\nbar x = fail! \"oops\"\nfoo x = bar x",
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
        "effect Fail {\n  fun fail (msg: String) -> a\n}\nfun bar (x: Int) -> Int needs {Fail}\nbar x = fail! \"oops\"\nfun foo (x: Int) -> Int needs {Fail}\nfoo x = bar x",
    )
    .unwrap();
}

#[test]
fn effect_propagation_handled_by_caller() {
    // Caller handles the effect, so doesn't need to declare it
    check(
        "effect Fail {\n  fun fail (msg: String) -> a\n}\nfun bar (x: Int) -> Int needs {Fail}\nbar x = fail! \"oops\"\nfoo x = (bar x) with {\n  fail msg -> 0\n}",
    )
    .unwrap();
}

#[test]
fn lambda_effects_propagate_to_enclosing_function() {
    // Effects inside a lambda propagate up to the enclosing function boundary
    let result = check(
        "effect Fail {\n  fun fail (msg: String) -> a\n}\nfoo x = fun y -> fail! \"oops\"",
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
fn lambda_effects_covered_by_enclosing_needs() {
    // Lambda effects are fine when the enclosing function declares them
    check(
        "effect Fail {\n  fun fail (msg: String) -> a\n}\nfun foo (x: Int) -> Int needs {Fail}\nfoo x = (fun y -> fail! \"oops\") x",
    )
    .unwrap();
}

#[test]
fn lambda_effects_absorbed_by_hof_annotation() {
    // HOF parameter annotated with `needs {Fail}` absorbs the effect from the lambda
    check(
        "effect Fail {\n  fun fail (msg: String) -> a\n}\nfun run (f: () -> Int needs {Fail}) -> Int\nrun f = f () with { fail msg -> 0 }\nfoo x = run (fun () -> fail! \"oops\")",
    )
    .unwrap();
}

#[test]
fn multiple_effects_needs_all() {
    let result = check(
        "effect Fail {\n  fun fail (msg: String) -> a\n}\neffect Log {\n  fun log (msg: String) -> Unit\n}\nfun foo (x: Int) -> Int needs {Fail}\nfoo x = {\n  log! \"hello\"\n  fail! \"oops\"\n}",
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
        "effect Fail {\n  fun fail (msg: String) -> a\n}\neffect Log {\n  fun log (msg: String) -> Unit\n}\nfun foo (x: Int) -> Unit needs {Fail, Log}\nfoo x = {\n  log! \"hello\"\n  fail! \"oops\"\n}",
    )
    .unwrap();
}

#[test]
fn with_subtracts_only_handled_effect() {
    // Handler handles Log but not Fail, so Fail still needs declaration
    let result = check(
        "effect Fail {\n  fun fail (msg: String) -> a\n}\neffect Log {\n  fun log (msg: String) -> Unit\n}\nhandler console for Log {\n  log msg -> print msg\n}\nfoo x = {\n  log! \"hello\"\n  fail! \"oops\"\n} with console",
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
    let checker = check("trait Greet a {\n  fun greet (x: a) -> String\n}").unwrap();
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
        "record User { name: String }\ntrait Greet a {\n  fun greet (x: a) -> String\n}\nimpl Greet for User {\n}",
    );
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(err.message.contains("missing method"), "got: {}", err.message);
}

#[test]
fn impl_extra_method() {
    let result = check(
        "record User { name: String }\ntrait Greet a {\n  fun greet (x: a) -> String\n}\nimpl Greet for User {\n  greet u = u.name\n  bogus u = u.name\n}",
    );
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(err.message.contains("not defined in trait"), "got: {}", err.message);
}

#[test]
fn impl_wrong_return_type() {
    let result = check(
        "record User { name: String }\ntrait Greet a {\n  fun greet (x: a) -> String\n}\nimpl Greet for User {\n  greet u = 42\n}",
    );
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(err.message.contains("type mismatch"), "got: {}", err.message);
}

#[test]
fn impl_correct() {
    check(
        "record User { name: String }\ntrait Greet a {\n  fun greet (x: a) -> String\n}\nimpl Greet for User {\n  greet u = u.name\n}",
    )
    .unwrap();
}

#[test]
fn impl_for_undefined_trait() {
    let result = check(
        "record User { name: String }\nimpl Bogus for User {\n  foo u = u.name\n}",
    );
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(err.message.contains("undefined trait"), "got: {}", err.message);
}

#[test]
fn trait_constraint_no_impl() {
    // Calling a trait method on a type with no impl should fail
    let result = check(
        "record User { name: String }
trait Describe a {
  fun describe (x: a) -> String
}
main () = describe (User { name: \"Alice\" })",
    );
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(err.message.contains("no impl of Describe for User"), "got: {}", err.message);
}

#[test]
fn trait_constraint_with_impl_ok() {
    // Calling a trait method on a type with an impl should succeed
    check(
        "record User { name: String }
trait Describe a {
  fun describe (x: a) -> String
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
  fun describe (x: a) -> String
}
fun show_it (x: a) -> String where {a: Describe}
show_it x = describe x",
    )
    .unwrap();
}

#[test]
fn where_clause_missing_bound_fails() {
    let result = check(
        "trait Describe a {
  fun describe (x: a) -> String
}
fun show_it (x: a) -> String
show_it x = describe x",
    );
    assert!(result.is_err());
    let err = result.err().unwrap();
    assert!(
        err.message.contains("trait Describe required but not declared in where clause"),
        "got: {}",
        err.message
    );
}

#[test]
fn where_clause_propagates_to_callers() {
    check(
        "record User { name: String }
trait Describe a {
  fun describe (x: a) -> String
}
impl Describe for User {
  describe u = u.name
}
fun show_it (x: a) -> String where {a: Describe}
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
  fun describe (x: a) -> String
}
fun show_it (x: a) -> String where {a: Describe}
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
  fun describe (x: a) -> String
}
trait Greet a {
  fun greet (x: a) -> String
}
fun both (x: a) -> String where {a: Describe + Greet}
both x = describe x",
    )
    .unwrap();
}

#[test]
fn where_clause_unknown_type_var() {
    let result = check(
        "trait Describe a {
  fun describe (x: a) -> String
}
fun show_it (x: a) -> String where {b: Describe}
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
fn inferred_constraint_propagation() {
    // Function without where clause infers constraint; caller with impl succeeds
    check(
        "record User { name: String }
trait Describe a {
  fun describe (x: a) -> String
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
  fun describe (x: a) -> String
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
  fun eq (x: a) (y: a) -> Bool
}
trait Ord a where {a: Eq} {
  fun compare (x: a) (y: a) -> Int
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
  fun eq (x: a) (y: a) -> Bool
}
trait Ord a where {a: Eq} {
  fun compare (x: a) (y: a) -> Int
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
  fun show (x: a) -> String
}
trait Eq a {
  fun eq (x: a) (y: a) -> Bool
}
trait Special a where {a: Show + Eq} {
  fun special (x: a) -> String
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
  fun show (x: a) -> String
}
trait Eq a {
  fun eq (x: a) (y: a) -> Bool
}
trait Special a where {a: Show + Eq} {
  fun special (x: a) -> String
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
    check("main () = print 42").unwrap();
    check("main () = print 3.14").unwrap();
    check("main () = print \"hello\"").unwrap();
    check("main () = print True").unwrap();
    check("main () = print ()").unwrap();
    check("let x = show 42\nmain () = print x").unwrap();
}

#[test]
fn show_fails_for_custom_type_without_impl() {
    let result = check(
        "record Foo { x: Int }
main () = print (Foo { x: 1 })",
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
trait Describe a {
  fun describe (x: a) -> String
}
impl Show for Foo {
  show f = \"Foo\"
}
main () = print (Foo { x: 1 })",
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
    assert!(check(
        "smaller a b = if a < b then a else b
main () = smaller 1 2"
    )
    .is_ok());
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
fn show_list_of_ints() {
    assert!(check("main () = show [1, 2, 3]").is_ok());
}

#[test]
fn show_list_of_strings() {
    assert!(check("main () = show [\"a\", \"b\"]").is_ok());
}

#[test]
fn show_list_of_custom_type_fails() {
    let result = check(
        "record Foo { x: Int }
main () = show [Foo { x: 1 }]",
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
fn show_nested_list() {
    // List (List Int) -- Show propagates through both layers
    assert!(check("main () = show [[1, 2], [3]]").is_ok());
}

// --- User-defined conditional impl tests ---

#[test]
fn user_conditional_impl_satisfied() {
    // impl Show for Box a where {a: Show} -- show (Box 1) should work
    let result = check(
        "type Box a { Box(a) }
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
type Box a { Box(a) }
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
        "type Box a { Box(a) }
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
        "fun fst (p: (Int, String)) -> Int
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
        "effect Log { fun log (msg: String) -> Unit }
effect Http { fun get (url: String) -> String }
handler my_http for Http {
  get url -> {
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
        "effect Log { fun log (msg: String) -> Unit }
effect Http { fun get (url: String) -> String }
handler console for Log {
  log msg -> resume ()
}
handler my_http for Http needs {Log} {
  get url -> {
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
        "effect Http { fun get (url: String) -> String }
handler mock_http for Http {
  get url -> resume \"mocked\"
}",
    );
    assert!(result.is_ok(), "got: {}", result.err().unwrap().message);
}

#[test]
fn handler_needs_missing_one_effect_is_error() {
    // Handler uses Log and Http but only declares needs {Log}
    let result = check(
        "effect Log { fun log (msg: String) -> Unit }
effect Http { fun get (url: String) -> String }
effect Db { fun query (sql: String) -> String }
handler log_impl for Log { log msg -> resume () }
handler my_db for Db needs {Log} {
  query sql -> {
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
        "fun add (x: Int) -> Int
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
        r#"type Foo { Foo }
main () = $"val: {Foo}""#,
    );
    assert!(result.is_err());
}
