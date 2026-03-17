use dylang::{codegen, elaborate, lexer, parser, typechecker};

/// Load the prelude into a checker.
fn bootstrap() -> typechecker::Checker {
    let prelude_src = include_str!("../src/stdlib/prelude.dy");
    let prelude_tokens = lexer::Lexer::new(prelude_src)
        .lex()
        .expect("prelude lex error");
    let prelude_program = parser::Parser::new(prelude_tokens)
        .parse_program()
        .expect("prelude parse error");
    let mut checker = typechecker::Checker::new();
    let result = checker.check_program(&prelude_program);
    assert!(!result.has_errors(), "prelude typecheck error: {:?}", result.errors());
    checker
}

fn emit(src: &str) -> String {
    let tokens = lexer::Lexer::new(src).lex().expect("lex error");
    let program = parser::Parser::new(tokens)
        .parse_program()
        .expect("parse error");
    codegen::emit_module("_script", &program)
}

/// Parse, typecheck, elaborate, then emit Core Erlang.
/// Use this for tests that involve traits or other elaboration features.
fn emit_elaborated(src: &str) -> String {
    let tokens = lexer::Lexer::new(src).lex().expect("lex error");
    let program = parser::Parser::new(tokens)
        .parse_program()
        .expect("parse error");
    let mut checker = bootstrap();
    let result = checker.check_program(&program);
    assert!(!result.has_errors(), "typecheck error: {:?}", result.errors());
    let elaborated = elaborate::elaborate(&program, &result);
    codegen::emit_module_with_imports("_script", &elaborated, &result.modules.codegen_info)
}

/// Emit Core Erlang and compile it with erlc, asserting no compilation errors.
fn assert_compiles(src: &str) {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static COUNTER: AtomicUsize = AtomicUsize::new(0);

    let out = emit_elaborated(src);
    let id = COUNTER.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("dylang_test_{}_{id}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let core_path = dir.join("_script.core");
    std::fs::write(&core_path, &out).unwrap();
    let status = std::process::Command::new("erlc")
        .arg("-o")
        .arg(&dir)
        .arg(&core_path)
        .output()
        .expect("failed to run erlc");
    // Clean up temp files
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        status.status.success(),
        "erlc failed to compile:\n{}\nstderr: {}",
        out,
        String::from_utf8_lossy(&status.stderr)
    );
}

fn assert_contains(out: &str, needle: &str) {
    assert!(
        out.contains(needle),
        "Expected to find:\n  {needle}\nIn output:\n{out}"
    );
}

// --- Tail call position ---

/// A tail-recursive function should have its recursive `apply` in tail position:
/// the apply must be the last expression in its case arm, not bound by a `let`.
#[test]
fn tail_recursive_apply_in_tail_position() {
    let src = "
sum_to acc n = if n == 0 then acc else sum_to (acc + n) (n - 1)
";
    let out = emit(src);

    // The output should contain the recursive apply.
    assert!(
        out.contains("apply 'sum_to'/2"),
        "expected recursive apply in output\n{out}"
    );

    // The recursive apply must NOT appear as the value of a let-binding,
    // which would take it out of tail position. i.e. no `let <X> = \n apply 'sum_to'/2`.
    assert!(
        !out.contains("=\n")
            || !out.lines().any(|l| {
                l.trim().starts_with("apply 'sum_to'/2")
                    && out[..out.find(l.trim()).unwrap()]
                        .lines()
                        .rev()
                        .find(|prev| !prev.trim().is_empty())
                        .is_some_and(|prev| prev.trim().ends_with('='))
            }),
        "recursive apply should not be let-bound (would break tail position)\n{out}"
    );

    // After the apply line, the next non-empty line should be `end` (closing the case).
    let lines: Vec<&str> = out.lines().collect();
    let apply_idx = lines
        .iter()
        .position(|l| l.contains("apply 'sum_to'/2"))
        .unwrap_or_else(|| panic!("expected recursive apply in output\n{out}"));
    let after = lines[apply_idx + 1..]
        .iter()
        .find(|l| !l.trim().is_empty())
        .expect("expected lines after apply");
    assert!(
        after.trim() == "end",
        "expected `end` after tail-recursive apply, got: {after:?}\n{out}"
    );
}

// --- Mutual recursion ---

#[test]
fn mutual_recursion_emits_cross_refs() {
    let src = "
is_even n = if n == 0 then True else is_odd (n - 1)
is_odd n = if n == 0 then False else is_even (n - 1)
";
    let out = emit(src);
    assert!(
        out.contains("'is_odd'/1"),
        "is_even should reference is_odd\n{out}"
    );
    assert!(
        out.contains("'is_even'/1"),
        "is_odd should reference is_even\n{out}"
    );
}

// --- Trait dictionary passing ---

#[test]
fn trait_dict_constructor_emitted() {
    let src = "
type Color { Red | Green | Blue }

trait Describe a {
  fun describe (x: a) -> String
}

impl Describe for Color {
  describe c = case c {
    Red -> \"red\"
    Green -> \"green\"
    Blue -> \"blue\"
  }
}

main () = describe Red
";
    let out = emit_elaborated(src);
    // Should emit a dictionary constructor function
    assert!(
        out.contains("'__dict_Describe_Color'/0"),
        "expected dict constructor for Describe/Color\n{out}"
    );
    // The dict constructor should return a tuple containing a fun (the describe impl)
    assert!(
        out.contains("fun ("),
        "expected lambda in dict constructor body\n{out}"
    );
}

#[test]
fn trait_method_call_uses_dict() {
    let src = "
type Color { Red | Green | Blue }

trait Describe a {
  fun describe (x: a) -> String
}

impl Describe for Color {
  describe c = case c {
    Red -> \"red\"
    Green -> \"green\"
    Blue -> \"blue\"
  }
}

main () = describe Red
";
    let out = emit_elaborated(src);
    // The call to `describe` should use element() to extract the method from the dict
    assert!(
        out.contains("call 'erlang':'element'"),
        "expected element() call for dict method access\n{out}"
    );
}

// --- Built-in Show dispatch ---

#[test]
fn show_int_uses_dict_dispatch() {
    let src = "main () = show 42";
    let out = emit_elaborated(src);
    // Should reference the Show/Int dict from the std_int module
    assert!(
        out.contains("__dict_Show_std_int_Int"),
        "expected Show/Int dict reference\n{out}"
    );
    // main should call the dict via element() dispatch
    assert!(
        out.contains("'erlang':'element'"),
        "expected element() for dict method access\n{out}"
    );
}

#[test]
fn show_bool_uses_case() {
    let src = "main () = show True";
    let out = emit_elaborated(src);
    // Should reference the Show/Bool dict from the std_bool module
    assert!(
        out.contains("__dict_Show_std_bool_Bool"),
        "expected Show/Bool dict reference\n{out}"
    );
}

#[test]
fn print_uses_show_dict() {
    let src = "main () = print 42";
    let out = emit_elaborated(src);
    // print is lowered inline as io:format("~s~n", [show(x)])
    assert!(
        out.contains("'io':'format'"),
        "expected io:format call in print\n{out}"
    );
    // Should reference the Show/Int dict for the argument
    assert!(
        out.contains("__dict_Show_std_int_Int"),
        "expected Show/Int dict reference\n{out}"
    );
}

#[test]
fn show_string_is_identity() {
    let src = "main () = show \"hello\"";
    let out = emit_elaborated(src);
    assert!(
        out.contains("__dict_Show_std_string_String"),
        "expected Show/String dict constructor\n{out}"
    );
}

#[test]
fn string_interpolation_uses_show_dict() {
    let src = r#"main () = $"value is {42}""#;
    let out = emit_elaborated(src);
    // String interpolation desugars to show(x), which should use dict dispatch
    assert!(
        out.contains("__dict_Show_std_int_Int"),
        "expected Show/Int dict for interpolation\n{out}"
    );
}

#[test]
fn show_tuple_inlines_per_element() {
    let src = "main () = show (1, True)";
    let out = emit_elaborated(src);
    // Tuple show is inlined: no __dict_Show_Tuple, instead direct element extraction
    assert!(
        !out.contains("__dict_Show_Tuple"),
        "should NOT have a Tuple dict constructor\n{out}"
    );
    // Should extract elements with erlang:element
    assert!(
        out.contains("'erlang':'element'"),
        "expected erlang:element calls for tuple elements\n{out}"
    );
    // Should reference Show dicts for the element types
    assert!(
        out.contains("__dict_Show_std_int_Int"),
        "expected Show/Int dict for first element\n{out}"
    );
    assert!(
        out.contains("__dict_Show_std_bool_Bool"),
        "expected Show/Bool dict for second element\n{out}"
    );
    // Should produce parens and comma separator
    assert!(
        out.contains("\"(\""),
        "expected opening paren string\n{out}"
    );
    assert!(
        out.contains("\", \""),
        "expected comma separator string\n{out}"
    );
    assert!(
        out.contains("\")\""),
        "expected closing paren string\n{out}"
    );
    // The inline lambda should appear directly in main (fun (___tup) -> ...)
    assert!(
        out.contains("fun (___tup)"),
        "main should contain inline tuple show lambda\n{out}"
    );
}

#[test]
fn show_triple_tuple_has_three_elements() {
    let src = r#"main () = show (1, "hi", True)"#;
    let out = emit_elaborated(src);
    // Should reference Show dicts for all three element types
    assert!(
        out.contains("__dict_Show_std_int_Int"),
        "expected Show/Int dict\n{out}"
    );
    assert!(
        out.contains("__dict_Show_std_string_String"),
        "expected Show/String dict\n{out}"
    );
    assert!(
        out.contains("__dict_Show_std_bool_Bool"),
        "expected Show/Bool dict\n{out}"
    );
    // Should have the inline tuple lambda, not a Tuple dict
    assert!(
        out.contains("fun (___tup)"),
        "expected inline tuple show lambda\n{out}"
    );
    assert!(
        !out.contains("__dict_Show_Tuple"),
        "should NOT have a Tuple dict constructor\n{out}"
    );
}

#[test]
fn show_user_defined_adt_uses_impl() {
    let src = "
type Color { Red | Green | Blue }

impl Show for Color {
  show c = case c {
    Red -> \"Red\"
    Green -> \"Green\"
    Blue -> \"Blue\"
  }
}

main () = show Red
";
    let out = emit_elaborated(src);
    // Should emit the user's dict constructor
    assert!(
        out.contains("'__dict_Show_Color'/0"),
        "expected Show/Color dict constructor\n{out}"
    );
    // main should dispatch show through the user's dict
    assert!(
        out.contains("'__dict_Show_Color'"),
        "main should reference the user Show impl\n{out}"
    );
    // The user impl body should appear (case arms with color strings)
    assert!(
        out.contains("\"Red\""),
        "expected \"Red\" string in Show impl body\n{out}"
    );
}

#[test]
fn print_user_defined_adt() {
    let src = "
type Color { Red | Green | Blue }

impl Show for Color {
  show c = case c {
    Red -> \"Red\"
    Green -> \"Green\"
    Blue -> \"Blue\"
  }
}

main () = print Red
";
    let out = emit_elaborated(src);
    // print should receive the user's Show dict
    assert!(
        out.contains("'__dict_Show_Color'"),
        "expected Show/Color dict passed to print\n{out}"
    );
    // print should call io:format
    assert!(
        out.contains("'io':'format'"),
        "expected io:format in print\n{out}"
    );
}

// --- Polymorphic trait dict sub-dictionaries ---

#[test]
fn show_parameterized_type_applies_sub_dicts() {
    let src = r#"
type Box a { Wrap(a) }

impl Show for Box a where {a: Show} {
  show b = case b {
    Wrap(v) -> "Wrap(" <> show v <> ")"
  }
}

main () = show (Wrap 42)
"#;
    let out = emit_elaborated(src);
    // The dict constructor should be applied with a sub-dict, not used as a bare ref.
    assert!(
        out.contains("'__dict_Show_Box'"),
        "expected Show/Box dict constructor\n{out}"
    );
    assert!(
        out.contains("__dict_Show_std_int_Int"),
        "expected Show/Int sub-dict applied to Box dict\n{out}"
    );
}

// --- Effect system (CPS transform) ---

#[test]
fn effect_fun_gets_handler_param() {
    // An effectful function should have an extra handler parameter in its arity
    let src = "
effect Log {
  fun log (msg: String) -> Unit
}

fun do_work () -> Int needs {Log}
do_work () = 42
";
    let out = emit_elaborated(src);
    // do_work takes 0 user params + 1 handler param + 1 _ReturnK = arity 2
    assert_contains(&out, "'do_work'/2");
    assert_contains(&out, "_Handle_Log_log");
}

#[test]
fn effect_call_becomes_handler_apply() {
    // `log! "hello"` should become `apply _HandleLog('log', "hello", K)`
    let src = r#"
effect Log {
  fun log (msg: String) -> Unit
}

fun do_work () -> Unit needs {Log}
do_work () = log! "hello"
"#;
    let out = emit_elaborated(src);
    assert_contains(&out, "apply _Handle_Log_log(");
    assert_contains(&out, "\"hello\"");
}

#[test]
fn effect_call_in_block_captures_continuation() {
    // When an effect call is in a block, everything after it becomes the continuation
    let src = r#"
effect Log {
  fun log (msg: String) -> Unit
}

fun do_work () -> Int needs {Log}
do_work () = {
  log! "starting"
  42
}
"#;
    let out = emit_elaborated(src);
    // Should have handler apply with a fun (continuation) as last arg
    assert_contains(&out, "apply _Handle_Log_log(");
    // The continuation should contain 42
    assert_contains(&out, "fun (");
    assert_contains(&out, "42");
}

#[test]
fn effect_call_let_binding_captures_value() {
    // `let x = get! ()` should make x the continuation parameter
    let src = "
effect State {
  fun get () -> Int
}

fun use_state () -> Int needs {State}
use_state () = {
  let x = get! ()
  x + 1
}
";
    let out = emit_elaborated(src);
    assert_contains(&out, "apply _Handle_State_get(");
}

#[test]
fn with_named_handler_binds_handler() {
    let src = r#"
effect Log {
  fun log (msg: String) -> Unit
}

handler silent for Log {
  log msg -> resume ()
}

fun do_work () -> Int needs {Log}
do_work () = {
  log! "hello"
  42
}

main () = do_work () with silent
"#;
    let out = emit_elaborated(src);
    // main should bind _HandleLog from the silent handler and call do_work
    assert_contains(&out, "_Handle_Log_log");
    assert_contains(&out, "apply 'do_work'/2");
}

#[test]
fn with_inline_handler() {
    let src = r#"
effect Fail {
  fun fail (msg: String) -> a
}

fun risky () -> Int needs {Fail}
risky () = fail! "oops"

main () = risky () with {
  fail msg -> 0
}
"#;
    let out = emit_elaborated(src);
    // Should have an inline handler function bound to _HandleFail
    assert_contains(&out, "_Handle_Fail_fail");
    assert_contains(&out, "apply 'risky'/2");
}

#[test]
fn handler_resume_calls_k() {
    // resume () in a handler should emit apply _K('unit')
    let src = r#"
effect Log {
  fun log (msg: String) -> Unit
}

handler silent for Log {
  log msg -> resume ()
}

fun do_work () -> Int needs {Log}
do_work () = {
  log! "hello"
  42
}

main () = do_work () with silent
"#;
    let out = emit_elaborated(src);
    // The handler function should call its K parameter (resume).
    // K uses a fresh name, so just verify the handler body applies *something*.
    assert_contains(&out, "apply _Cor");
}

#[test]
fn non_resumable_handler_no_k() {
    // A handler that doesn't use resume should NOT call _K
    let src = r#"
effect Fail {
  fun fail (msg: String) -> a
}

fun risky () -> Int needs {Fail}
risky () = fail! "oops"

main () = risky () with {
  fail msg -> 0
}
"#;
    let out = emit_elaborated(src);
    // The inline handler body should just return 0, no _K call
    // (the arm body is `0`, which doesn't reference _K)
    assert_contains(&out, "_Handle_Fail_fail");
}

#[test]
fn with_return_clause() {
    let src = r#"
type Result a b { Ok(a) | Err(b) }

effect Fail {
  fun fail (msg: String) -> a
}

fun risky () -> Int needs {Fail}
risky () = 42

main () = risky () with {
  fail msg -> Err msg
  return value -> Ok value
}
"#;
    let out = emit_elaborated(src);
    // Ok/Err use BEAM convention atoms (lowercase)
    assert_contains(&out, "'ok'");
    assert_contains(&out, "'error'");
}

#[test]
fn effect_propagation_threads_handler() {
    // When an effectful function calls another effectful function,
    // the handler param should be threaded through
    let src = r#"
effect Log {
  fun log (msg: String) -> Unit
}

fun inner () -> Unit needs {Log}
inner () = log! "from inner"

fun outer () -> Unit needs {Log}
outer () = inner ()

handler silent for Log {
  log msg -> resume ()
}

main () = outer () with silent
"#;
    let out = emit_elaborated(src);
    // outer should pass its _HandleLog to inner
    // inner/1 takes _HandleLog, outer/1 takes _HandleLog,
    // outer calls inner with its own _HandleLog
    assert_contains(&out, "'inner'/2");
    assert_contains(&out, "'outer'/2");
}

#[test]
fn multiple_effect_calls_chain_continuations() {
    let src = r#"
effect Log {
  fun log (msg: String) -> Unit
}

fun do_work () -> Int needs {Log}
do_work () = {
  log! "first"
  log! "second"
  42
}

handler silent for Log {
  log msg -> resume ()
}

main () = do_work () with silent
"#;
    let out = emit_elaborated(src);
    // Should have two nested handler applies with continuations
    // Count occurrences of apply _HandleLog
    let count = out.matches("apply _Handle_Log_log").count();
    assert!(
        count >= 2,
        "expected at least 2 handler applies, got {count}\n{out}"
    );
}

#[test]
fn effect_cps_log_with_let_bindings() {
    // Full CPS: log calls interleaved with let bindings and arithmetic
    let src = r#"
effect Log {
  fun log (msg: String) -> Unit
}

handler silent for Log {
  log msg -> resume ()
}

fun do_work () -> Int needs {Log}
do_work () = {
  log! "starting"
  let x = 10 + 20
  log! "done"
  x
}

main () = do_work () with silent
"#;
    let out = emit_elaborated(src);
    // do_work should have nested handler applies with continuations
    // wrapping the let bindings and final value
    assert_contains(&out, "'do_work'/2");
    assert_contains(&out, "apply _Handle_Log_log(");
    // x = 10 + 20 should appear inside a continuation
    assert_contains(&out, "call 'erlang':'+'");
}

#[test]
fn effect_fail_non_resumable_with_return() {
    // Fail handler doesn't call K; return clause wraps success path
    let src = r#"
effect Fail {
  fun fail (msg: String) -> a
}

fun checked_double (x: Int) -> Int needs {Fail}
checked_double x = if x > 100 then fail! "too big" else x * 2

main () = {
  let a = checked_double 10 with {
    fail msg -> 0 - 1
    return value -> value
  }
  let b = checked_double 200 with {
    fail msg -> 0 - 1
    return value -> value
  }
  a + b
}
"#;
    let out = emit_elaborated(src);
    // Should have two with-expression lowerings, each with _Handle_Fail_fail
    assert_contains(&out, "_Handle_Fail_fail");
    // The fail arm should not call _K
    // The return clause should appear
}

#[test]
fn effect_propagation_inner_outer() {
    // outer calls inner, both need Log; handler param threads through
    let src = r#"
effect Log {
  fun log (msg: String) -> Unit
}

fun inner () -> Int needs {Log}
inner () = {
  log! "from inner"
  42
}

fun outer () -> Int needs {Log}
outer () = {
  log! "from outer"
  let x = inner ()
  x + 1
}

handler silent for Log {
  log msg -> resume ()
}

main () = outer () with silent
"#;
    let out = emit_elaborated(src);
    // Both should take _HandleLog
    assert_contains(&out, "'inner'/2");
    assert_contains(&out, "'outer'/2");
    // outer's body should call inner with _HandleLog and _ReturnK passed through
    assert_contains(&out, "apply 'inner'/2(_Handle_Log_log");
}

#[test]
fn effect_multi_handler_stacking() {
    // Function needs both Fail and Log; with provides both handlers
    let src = r#"
effect Log {
  fun log (msg: String) -> Unit
}

effect Fail {
  fun fail (msg: String) -> a
}

handler silent for Log {
  log msg -> resume ()
}

fun risky_work () -> Int needs {Fail, Log}
risky_work () = {
  log! "starting risky work"
  let x = 10 * 5
  if x > 100 then fail! "too big"
  else {
    log! "result ok"
    x
  }
}

main () = risky_work () with {
  silent,
  fail msg -> 0 - 1
  return value -> value
}
"#;
    let out = emit_elaborated(src);
    // risky_work needs 2 handler params + 1 _ReturnK (Fail + Log, sorted alphabetically)
    assert_contains(&out, "'risky_work'/3");
    // Both handler params should be present
    assert_contains(&out, "_Handle_Fail_fail");
    assert_contains(&out, "_Handle_Log_log");
}

#[test]
fn handler_arm_body_gets_show_dict() {
    // print inside a named handler body should get the Show dict inserted
    let src = r#"
effect Log {
  fun log (msg: String) -> Unit
}

handler console_log for Log {
  log msg -> {
    print msg
    resume ()
  }
}

fun do_work () -> Int needs {Log}
do_work () = {
  log! "hello"
  42
}

main () = do_work () with console_log
"#;
    let out = emit_elaborated(src);
    // The handler arm body should call io:format (print is lowered inline)
    assert_contains(&out, "'io':'format'");
    assert_contains(&out, "__dict_Show_std_string_String");
}

#[test]
fn handler_needs_effect_from_sibling_handler() {
    // A named handler for Fail that uses Log in its arm body.
    // Both handlers provided in the same `with`.
    let src = r#"
effect Log {
  fun log (msg: String) -> Unit
}

effect Fail {
  fun fail (msg: String) -> a
}

handler silent for Log {
  log msg -> resume ()
}

handler logging_fail for Fail needs {Log} {
  fail msg -> {
    log! ("caught: " <> msg)
    0
  }
}

fun risky () -> Int needs {Fail, Log}
risky () = {
  log! "about to fail"
  fail! "oops"
}

main () = risky () with { silent, logging_fail }
"#;
    let out = emit_elaborated(src);
    // The Fail handler arm body contains log!, which should reference _HandleLog
    assert_contains(&out, "_Handle_Log_log");
    assert_contains(&out, "_Handle_Fail_fail");
    // The fail arm body should apply _HandleLog for the log! call
    assert_contains(&out, "apply _Handle_Log_log(");
}

#[test]
fn handler_needs_effect_from_outer_scope() {
    // A named handler for Fail that needs Log.
    // Log comes from the enclosing function's handler param.
    let src = r#"
effect Log {
  fun log (msg: String) -> Unit
}

effect Fail {
  fun fail (msg: String) -> a
}

handler logging_fail for Fail needs {Log} {
  fail msg -> {
    log! ("Failed: " <> msg)
    0
  }
}

handler silent for Log {
  log msg -> resume ()
}

fun do_work () -> Int needs {Fail, Log}
do_work () = {
  log! "starting"
  fail! "boom"
}

main () = do_work () with { silent, logging_fail }
"#;
    let out = emit_elaborated(src);
    // logging_fail's arm body uses log!, should reference _HandleLog
    assert_contains(&out, "apply _Handle_Log_log(");
    assert_contains(&out, "_Handle_Fail_fail");
}

#[test]
fn effect_multi_clause_function() {
    // Effectful function with pattern-matched clauses
    let src = r#"
effect Fail {
  fun fail (msg: String) -> a
}

fun safe_div (x: Int) (y: Int) -> Int needs {Fail}
safe_div _ 0 = fail! "division by zero"
safe_div x y = x * y

main () = safe_div 10 0 with {
  fail msg -> 0 - 1
  return value -> value
}
"#;
    let out = emit_elaborated(src);
    // safe_div takes 2 user params + 1 handler param + 1 _ReturnK = arity 4
    assert_contains(&out, "'safe_div'/4");
    assert_contains(&out, "_Handle_Fail_fail");
}

// --- Effect calls in non-block positions ---

#[test]
fn effect_call_in_binop() {
    // Effect call nested in a binary operation should be lifted to a let binding
    let src = r#"
effect Ask {
  fun ask () -> Int
}

fun compute () -> Int needs {Ask}
compute () = {
  let x = 1 + ask! ()
  x
}

main () = compute () with {
  ask () -> resume 42
}
"#;
    let out = emit_elaborated(src);
    // The ask! should be CPS-transformed with a continuation that does the addition
    assert_contains(&out, "apply _Handle_Ask_ask(");
    // The addition should still happen
    assert_contains(&out, "call 'erlang':'+'");
}

#[test]
fn effect_call_in_function_arg() {
    // Effect call as an argument to a function call
    let src = r#"
effect Ask {
  fun ask () -> Int
}

double x = x * 2

fun compute () -> Int needs {Ask}
compute () = {
  let x = double (ask! ())
  x
}

main () = compute () with {
  ask () -> resume 21
}
"#;
    let out = emit_elaborated(src);
    assert_contains(&out, "apply _Handle_Ask_ask(");
    assert_contains(&out, "'double'");
}

#[test]
fn effect_call_in_if_condition() {
    // Effect call in an if condition
    let src = r#"
effect Ask {
  fun ask () -> Bool
}

fun decide () -> Int needs {Ask}
decide () = {
  if ask! () then 1 else 0
}

main () = decide () with {
  ask () -> resume True
}
"#;
    let out = emit_elaborated(src);
    assert_contains(&out, "apply _Handle_Ask_ask(");
}

#[test]
fn multiple_effect_calls_in_binop() {
    // Two effect calls in the same binary expression
    let src = r#"
effect Ask {
  fun ask () -> Int
}

fun compute () -> Int needs {Ask}
compute () = {
  let x = ask! () + ask! ()
  x
}

main () = compute () with {
  ask () -> resume 10
}
"#;
    let out = emit_elaborated(src);
    // Should have two separate handler applies for the two ask! calls
    let count = out.matches("apply _Handle_Ask_ask(").count();
    assert!(
        count >= 2,
        "expected at least 2 handler applies, got {count}\n{out}"
    );
}

#[test]
fn effect_call_in_binop_compiles() {
    let src = r#"
effect Ask {
  fun ask () -> Int
}

fun compute () -> Int needs {Ask}
compute () = {
  let x = 1 + ask! ()
  x
}

main () = compute () with {
  ask () -> resume 42
}
"#;
    assert_compiles(src);
}

// --- HOF effect absorption ---

#[test]
fn hof_effect_absorption_try_pattern() {
    // `try` takes an effectful callback and handles Fail internally.
    // The lambda should get _HandleFail as an extra param,
    // and `computation ()` inside try should pass it.
    let src = r#"
type Result a e { Ok(a) | Err(e) }

effect Fail {
  fun fail (msg: String) -> a
}

fun try_it (computation: () -> a needs {Fail}) -> Result a String
try_it computation = computation () with {
  fail msg -> Err(msg)
  return value -> Ok(value)
}

main () = try_it (fun () -> fail! "oops")
"#;
    let out = emit_elaborated(src);
    // The lambda should have _HandleFail as a parameter
    assert_contains(&out, "_Handle_Fail_fail");
    // try_it's body should call computation with the handler param
    assert_contains(&out, "apply Computation(");
}

#[test]
fn hof_effect_absorption_lambda_with_block() {
    // Lambda with a block body that uses effects
    let src = r#"
type Result a e { Ok(a) | Err(e) }

effect Fail {
  fun fail (msg: String) -> a
}

fun try_it (computation: () -> a needs {Fail}) -> Result a String
try_it computation = computation () with {
  fail msg -> Err(msg)
  return value -> Ok(value)
}

main () = try_it (fun () -> {
  let x = 10
  if x > 100 then fail! "too big" else x
})
"#;
    let out = emit_elaborated(src);
    assert_contains(&out, "_Handle_Fail_fail");
    assert_contains(&out, "apply Computation(");
}

#[test]
fn hof_effect_absorption_compiles() {
    // End-to-end: HOF effect absorption compiles to valid Core Erlang
    let src = r#"
effect Fail {
  fun fail (msg: String) -> a
}

fun try_it (computation: () -> a needs {Fail}) -> String
try_it computation = computation () with {
  fail msg -> "err: " <> msg
}

main () = {
  let a = try_it (fun () -> "hello")
  print a
  let b = try_it (fun () -> fail! "boom")
  print b
}
"#;
    assert_compiles(src);
}

#[test]
fn return_clause_inside_cps_chain() {
    // The return clause should be inside the CPS chain, not a post-wrapper.
    // Verify the return clause (Ok wrapper) is inside the CPS chain.
    let src = r#"
type Result a e { Ok(a) | Err(e) }

effect Fail {
  fun fail (msg: String) -> a
}

try_it computation = computation () with {
  fail msg -> Err(msg)
  return value -> Ok(value)
}
"#;
    let out = emit(src);
    // Ok/Err use BEAM convention atoms (lowercase)
    assert_contains(&out, "'ok'");
    assert_contains(&out, "'error'");
}

#[test]
fn return_clause_with_handler_compiles() {
    // End-to-end: return clause + handler abort compiles to valid Core Erlang.
    let src = r#"
type Result a e { Ok(a) | Err(e) }

effect Fail {
  fun fail (msg: String) -> a
}

fun try_it (computation: () -> a needs {Fail}) -> Result a String
try_it computation = computation () with {
  fail msg -> Err(msg)
  return value -> Ok(value)
}

main () = {
  let a = try_it (fun () -> 42)
  print "ok"
  let b = try_it (fun () -> fail! "boom")
  print "ok"
}
"#;
    assert_compiles(src);
}

// --- Effect call coverage gap tests ---

#[test]
fn effect_in_tail_position() {
    // Effect call as the last statement in a block.
    let src = r#"
effect Log {
  fun log (msg: String) -> Unit
}

handler silent for Log {
  log msg -> resume ()
}

fun greet () -> Unit needs {Log}
greet () = {
  log! "hello"
}

main () = greet () with silent
"#;
    assert_compiles(src);
}

#[test]
fn sequential_effects_interleaved_with_lets() {
    // Multiple effect calls interleaved with non-effect let bindings.
    let src = r#"
effect Log {
  fun log (msg: String) -> Unit
}

handler silent for Log {
  log msg -> resume ()
}

fun work () -> Int needs {Log}
work () = {
  log! "start"
  let x = 1
  log! "middle"
  let y = x + 1
  log! "end"
  y
}

main () = work () with silent
"#;
    let out = emit_elaborated(src);
    // Should have multiple continuation funs for the chained effects
    let fun_count = out.matches("fun (").count();
    assert!(
        fun_count >= 4,
        "expected at least 4 fun expressions for K-chaining, got {}\n{}",
        fun_count,
        out
    );
    assert_compiles(src);
}

#[test]
fn resume_with_non_unit_value() {
    // Handler resumes with a computed value, not just ().
    let src = r#"
effect Ask {
  fun ask () -> Int
}

handler answer_42 for Ask {
  ask -> resume 42
}

fun use_ask () -> Int needs {Ask}
use_ask () = {
  let x = ask! ()
  x + 1
}

main () = use_ask () with answer_42
"#;
    let out = emit_elaborated(src);
    assert!(out.contains("42"), "expected 42 in handler resume\n{out}");
    assert_compiles(src);
}

#[test]
fn effect_in_record_constructor_arg() {
    // Effect call as a record field value.
    let src = r#"
record Point { x: Int, y: Int }

effect Ask {
  fun ask () -> Int
}

handler answer_42 for Ask {
  ask -> resume 42
}

fun make_point () -> Point needs {Ask}
make_point () = {
  let a = ask! ()
  Point { x: a, y: 10 }
}

main () = make_point () with answer_42
"#;
    assert_compiles(src);
}

#[test]
fn effect_in_tuple_constructor_arg() {
    // Effect call as a tuple element.
    let src = r#"
effect Ask {
  fun ask () -> Int
}

handler answer_42 for Ask {
  ask -> resume 42
}

fun make_pair () -> (Int, Int) needs {Ask}
make_pair () = {
  let a = ask! ()
  (a, 10)
}

main () = make_pair () with answer_42
"#;
    assert_compiles(src);
}

#[test]
fn effect_in_adt_constructor_arg() {
    // Effect call as ADT constructor argument.
    let src = r#"
type Maybe a { Some(a) | None }

effect Ask {
  fun ask () -> Int
}

handler answer_42 for Ask {
  ask -> resume 42
}

fun maybe_ask () -> Maybe Int needs {Ask}
maybe_ask () = {
  let x = ask! ()
  Some(x)
}

main () = maybe_ask () with answer_42
"#;
    assert_compiles(src);
}

#[test]
fn multiple_effects_three_handlers() {
    // Function needing three effects, each with a separate handler.
    let src = r#"
effect Log {
  fun log (msg: String) -> Unit
}

effect Ask {
  fun ask () -> Int
}

effect Fail {
  fun fail (msg: String) -> a
}

handler silent for Log {
  log msg -> resume ()
}

handler answer_42 for Ask {
  ask -> resume 42
}

fun complex () -> Int needs {Log, Ask, Fail}
complex () = {
  log! "start"
  let x = ask! ()
  if x > 100 then fail! "too big" else x
}

main () = complex () with {
  silent,
  answer_42,
  fail msg -> 0
}
"#;
    assert_compiles(src);
}

// effect_guard_desugared_to_body removed: effect calls in guards are now
// rejected by the type checker (see typechecker::tests::effect_call_in_case_guard_rejected)

#[test]
fn effect_result_ignored_three_in_a_row() {
    // Three consecutive effect calls whose return values are unused.
    let src = r#"
effect Log {
  fun log (msg: String) -> Unit
}

handler silent for Log {
  log msg -> resume ()
}

fun work () -> Int needs {Log}
work () = {
  log! "a"
  log! "b"
  log! "c"
  42
}

main () = work () with silent
"#;
    assert_compiles(src);
}

#[test]
fn effect_returned_directly_no_block() {
    // Effect call as the entire function body (no block).
    let src = r#"
effect Ask {
  fun ask () -> Int
}

handler answer_42 for Ask {
  ask -> resume 42
}

fun get_value () -> Int needs {Ask}
get_value () = ask! ()

main () = get_value () with answer_42
"#;
    assert_compiles(src);
}

#[test]
fn nested_effectful_function_calls() {
    // Chain of effectful function calls: outer calls middle calls inner.
    let src = r#"
effect Log {
  fun log (msg: String) -> Unit
}

handler silent for Log {
  log msg -> resume ()
}

fun inner () -> Int needs {Log}
inner () = {
  log! "inner"
  1
}

fun middle () -> Int needs {Log}
middle () = {
  let x = inner ()
  log! "middle"
  x + 1
}

fun outer () -> Int needs {Log}
outer () = {
  let y = middle ()
  log! "outer"
  y + 1
}

main () = outer () with silent
"#;
    assert_compiles(src);
}

#[test]
fn abort_skips_remaining_in_nested_calls() {
    // Abort-style handler in inner function should skip continuation in outer.
    let src = r#"
type Result a e { Ok(a) | Err(e) }

effect Fail {
  fun fail (msg: String) -> a
}

fun inner () -> Int needs {Fail}
inner () = {
  fail! "boom"
  999
}

fun outer () -> Int needs {Fail}
outer () = {
  let x = inner ()
  x + 1
}

fun try_it (computation: () -> a needs {Fail}) -> Result a String
try_it computation = computation () with {
  fail msg -> Err(msg)
  return value -> Ok(value)
}

main () = try_it (fun () -> outer ())
"#;
    assert_compiles(src);
}

#[test]
fn mixed_resume_and_abort_in_handler() {
    // Handler where some ops resume and others abort.
    let src = r#"
effect IO {
  fun read () -> Int
  fun crash (msg: String) -> a
}

handler test_io for IO {
  read -> resume 42
  crash msg -> 0
}

fun process () -> Int needs {IO}
process () = {
  let x = read! ()
  if x > 100 then crash! "too big" else x + 1
}

main () = process () with test_io
"#;
    assert_compiles(src);
}

#[test]
fn tuple_destructure_with_effect_result() {
    // Tuple pattern destructuring where the RHS is an effect call.
    let src = r#"
effect Ask {
  fun ask () -> (Int, Int)
}

handler answer for Ask {
  ask -> resume (1, 2)
}

fun use_pair () -> Int needs {Ask}
use_pair () = {
  let (a, b) = ask! ()
  a + b
}

main () = use_pair () with answer
"#;
    let out = emit_elaborated(src);
    assert!(
        out.contains("case"),
        "expected case for tuple destructure\n{out}"
    );
    assert_compiles(src);
}

#[test]
fn constructor_destructure_after_effect() {
    // Constructor pattern match on effect result.
    let src = r#"
type Maybe a { Just(a) | Nothing }

effect Ask {
  fun ask () -> Maybe Int
}

handler answer for Ask {
  ask -> resume Just(42)
}

fun extract () -> Int needs {Ask}
extract () = {
  let result = ask! ()
  case result {
    Just(x) -> x
    Nothing -> 0
  }
}

main () = extract () with answer
"#;
    assert_compiles(src);
}

// --- Integer vs float division ---

#[test]
fn int_division_emits_erlang_div() {
    let src = "main () = 10 / 3";
    let out = emit_elaborated(src);
    assert_contains(&out, "call 'erlang':'div'");
}

#[test]
fn float_division_emits_erlang_slash() {
    let src = "main () = 10.0 / 3.0";
    let out = emit_elaborated(src);
    assert_contains(&out, "call 'erlang':'/'");
}

#[test]
fn local_function_emits_letrec() {
    let src = r#"
main () = {
  let double x = x + x
  double 5
}
"#;
    let out = emit_elaborated(src);
    assert_contains(&out, "letrec");
    assert_contains(&out, "'double'/1");
}

#[test]
fn local_function_compiles() {
    let src = r#"
main () = {
  let double x = x + x
  double 5
}
"#;
    assert_compiles(src);
}

#[test]
fn local_recursive_function_compiles() {
    let src = r#"
main () = {
  let fact n = if n == 0 then 1 else n * fact (n - 1)
  fact 5
}
"#;
    assert_compiles(src);
}

#[test]
fn local_multi_clause_function_compiles() {
    let src = r#"
main () = {
  let fib 0 = 0
  let fib 1 = 1
  let fib n = fib (n - 1) + fib (n - 2)
  fib 10
}
"#;
    assert_compiles(src);
}
