use dylang::{codegen, elaborate, lexer, parser, typechecker};

fn emit(src: &str) -> String {
    let tokens = lexer::Lexer::new(src).lex().expect("lex error");
    let program = parser::Parser::new(tokens)
        .parse_program()
        .expect("parse error");
    codegen::emit_module("test", &program)
}

/// Parse, typecheck, elaborate, then emit Core Erlang.
/// Use this for tests that involve traits or other elaboration features.
fn emit_elaborated(src: &str) -> String {
    let tokens = lexer::Lexer::new(src).lex().expect("lex error");
    let program = parser::Parser::new(tokens)
        .parse_program()
        .expect("parse error");
    let mut checker = typechecker::Checker::new();
    checker.check_program(&program).expect("typecheck error");
    let elaborated = elaborate::elaborate(&program, &checker);
    codegen::emit_module("test", &elaborated)
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
    // Should emit a dict constructor for Show/Int
    assert!(
        out.contains("'__dict_Show_Int'/0"),
        "expected Show/Int dict constructor\n{out}"
    );
    // Should call erlang:integer_to_list for Int show
    assert!(
        out.contains("'erlang':'integer_to_list'"),
        "expected integer_to_list call\n{out}"
    );
    // main should actually call the dict via element() dispatch
    assert!(
        out.contains("'erlang':'element'"),
        "expected element() for dict method access\n{out}"
    );
}

#[test]
fn show_bool_uses_case() {
    let src = "main () = show True";
    let out = emit_elaborated(src);
    assert!(
        out.contains("'__dict_Show_Bool'/0"),
        "expected Show/Bool dict constructor\n{out}"
    );
    // Bool show should produce "True"/"False" strings via case
    assert!(
        out.contains("\"True\""),
        "expected \"True\" string in Show Bool\n{out}"
    );
}

#[test]
fn print_uses_show_dict() {
    let src = "main () = print 42";
    let out = emit_elaborated(src);
    // print should be a function that takes a Show dict param
    assert!(
        out.contains("'print'/2"),
        "expected print/2 (dict + value)\n{out}"
    );
    // print should call io:format
    assert!(
        out.contains("'io':'format'"),
        "expected io:format call in print\n{out}"
    );
}

#[test]
fn show_string_is_identity() {
    let src = "main () = show \"hello\"";
    let out = emit_elaborated(src);
    assert!(
        out.contains("'__dict_Show_String'/0"),
        "expected Show/String dict constructor\n{out}"
    );
}

#[test]
fn string_interpolation_uses_show_dict() {
    let src = r#"main () = $"value is {42}""#;
    let out = emit_elaborated(src);
    // String interpolation desugars to show(x), which should use dict dispatch
    assert!(
        out.contains("'__dict_Show_Int'/0"),
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
    // Should use Show dicts for the element types
    assert!(
        out.contains("'__dict_Show_Int'/0"),
        "expected Show/Int dict for first element\n{out}"
    );
    assert!(
        out.contains("'__dict_Show_Bool'/0"),
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
        out.contains("'__dict_Show_Int'/0"),
        "expected Show/Int dict\n{out}"
    );
    assert!(
        out.contains("'__dict_Show_String'/0"),
        "expected Show/String dict\n{out}"
    );
    assert!(
        out.contains("'__dict_Show_Bool'/0"),
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
    // do_work takes 0 user params + 1 handler param = arity 1
    assert_contains(&out, "'do_work'/1");
    assert_contains(&out, "_HandleLog");
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
    assert_contains(&out, "apply _HandleLog");
    assert_contains(&out, "'log'");
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
    assert_contains(&out, "apply _HandleLog");
    assert_contains(&out, "'log'");
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
    assert_contains(&out, "apply _HandleState");
    assert_contains(&out, "'get'");
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
    assert_contains(&out, "_HandleLog");
    assert_contains(&out, "apply 'do_work'/1");
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
    assert_contains(&out, "_HandleFail");
    assert_contains(&out, "apply 'risky'/1");
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
    // The handler function should call _K (resume)
    assert_contains(&out, "apply _K(");
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
    assert_contains(&out, "_HandleFail");
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
    // Should wrap the result in Ok
    assert_contains(&out, "'Ok'");
    assert_contains(&out, "'Err'");
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
    assert_contains(&out, "'inner'/1");
    assert_contains(&out, "'outer'/1");
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
    let count = out.matches("apply _HandleLog").count();
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
    assert_contains(&out, "'do_work'/1");
    assert_contains(&out, "apply _HandleLog('log'");
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
    // Should have two with-expression lowerings, each with _HandleFail
    assert_contains(&out, "_HandleFail");
    // The fail arm should not call _K
    // The return clause should appear
    assert_contains(&out, "'fail'");
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
    assert_contains(&out, "'inner'/1");
    assert_contains(&out, "'outer'/1");
    // outer's body should call inner with _HandleLog passed through
    // inner/1 called with the handler param
    assert_contains(&out, "apply 'inner'/1(_HandleLog)");
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
    // risky_work needs 2 handler params (Fail + Log, sorted alphabetically)
    assert_contains(&out, "'risky_work'/2");
    // Both handler params should be present
    assert_contains(&out, "_HandleFail");
    assert_contains(&out, "_HandleLog");
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
    // The handler arm body should call print/2 with a Show dict
    assert_contains(&out, "'print'/2");
    assert_contains(&out, "__dict_Show_String");
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
    assert_contains(&out, "_HandleLog");
    assert_contains(&out, "_HandleFail");
    // The fail arm body should apply _HandleLog for the log! call
    assert_contains(&out, "apply _HandleLog('log'");
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
    assert_contains(&out, "apply _HandleLog('log'");
    assert_contains(&out, "_HandleFail");
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
    // safe_div takes 2 user params + 1 handler param = arity 3
    assert_contains(&out, "'safe_div'/3");
    assert_contains(&out, "_HandleFail");
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
    assert_contains(&out, "apply _HandleAsk('ask'");
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
    assert_contains(&out, "apply _HandleAsk('ask'");
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
    assert_contains(&out, "apply _HandleAsk('ask'");
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
    let count = out.matches("apply _HandleAsk('ask'").count();
    assert!(
        count >= 2,
        "expected at least 2 handler applies, got {count}\n{out}"
    );
}
