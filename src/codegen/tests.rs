use super::{CodegenContext, emit_module_with_context};
use crate::lexer::Lexer;
use crate::parser::Parser;
use crate::{derive, desugar, elaborate, typechecker};

/// Parse, typecheck, elaborate, and emit Core Erlang for a single-file script module.
fn emit(src: &str) -> String {
    emit_full(src)
}

/// Parse, typecheck, elaborate, and emit Core Erlang - mirrors the real compiler pipeline.
fn emit_full(src: &str) -> String {
    emit_full_with_source(src, None)
}

/// Like emit_full but with source file info for location annotations.
fn emit_full_with_source(src: &str, source_file: Option<&super::SourceFile>) -> String {
    let tokens = Lexer::new(src).lex().expect("lex error");
    let mut program = Parser::new(tokens).parse_program().expect("parse error");
    derive::expand_derives(&mut program);
    desugar::desugar_program(&mut program);

    let mut checker = typechecker::Checker::with_prelude(None).expect("prelude error");
    let result = checker.check_program(&mut program);
    assert!(!result.has_errors(), "Type errors: {:?}", result.errors());

    let elaborated = elaborate::elaborate(&program, &result);
    let ctx = CodegenContext {
        modules: std::collections::HashMap::new(),
        let_effect_bindings: result.let_effect_bindings.clone(),
        prelude_imports: result.prelude_imports.clone(),
    };
    emit_module_with_context("_script", &elaborated, &ctx, &result, source_file, None)
}

/// Assert that `emit(src)` contains `needle` as a substring.
/// On failure, prints the full output for easy debugging.
fn assert_contains(src: &str, needle: &str) {
    let out = emit(src);
    assert!(
        out.contains(needle),
        "Expected to find:\n  {needle}\nIn output:\n{out}"
    );
}

/// Assert that `emit_full(src)` contains `needle` as a substring.
/// On failure, prints the full output for easy debugging.
fn assert_contains_full(src: &str, needle: &str) {
    let out = emit_full(src);
    assert!(
        out.contains(needle),
        "Expected to find:\n  {needle}\nIn output:\n{out}"
    );
}

// --- Full pipeline smoke test ---

#[test]
fn full_pipeline_smoke() {
    assert_contains_full("main () = 42", "42");
}

#[test]
fn eta_reduced_effectful_callback_uses_lowered_fun_arity() {
    let src = r#"
effect State s {
  fun get : Unit -> s
  fun put : s -> Unit
}

fun run_state : s -> (Unit -> a needs {State s}) -> (a, s)
run_state init f = {
  let state_fn = f () with {
    get () = fun s -> (resume s) s
    put new_s = fun _ -> (resume ()) new_s
    return value = fun s -> (value, s)
  }
  state_fn init
}

fun build_msg : Unit -> String needs {State String}
build_msg () = get! ()

main () = {
  let (msg, _) = run_state "" build_msg
  msg
}
"#;
    let out = emit_full(src);
    assert!(
        out.contains("'build_msg'/4"),
        "expected eta-reduced effectful function ref to use lowered arity\n{out}"
    );
    assert!(
        !out.contains("'build_msg'/1"),
        "effectful function ref used source arity instead of lowered arity\n{out}"
    );
}

#[test]
fn alias_of_eta_reduced_effectful_callback_uses_lowered_fun_arity() {
    let src = r#"
effect State s {
  fun get : Unit -> s
  fun put : s -> Unit
}

fun run_state : s -> (Unit -> a needs {State s}) -> (a, s)
run_state init f = {
  let state_fn = f () with {
    get () = fun s -> (resume s) s
    put new_s = fun _ -> (resume ()) new_s
    return value = fun s -> (value, s)
  }
  state_fn init
}

fun build_msg : Unit -> String needs {State String}
build_msg () = get! ()

main () = {
  let f = build_msg
  let (msg, _) = run_state "" f
  msg
}
"#;
    let out = emit_full(src);
    assert!(
        out.contains("'build_msg'/4"),
        "expected aliased effectful function ref to use lowered arity\n{out}"
    );
    assert!(
        !out.contains("'build_msg'/1"),
        "aliased effectful function ref used source arity instead of lowered arity\n{out}"
    );
}

#[test]
fn effectful_callbacks_in_lists_get_lowered_handler_params() {
    let src = r#"
effect Reg {
  fun reg : String -> Unit
}

handler noop for Reg {
  reg _ = resume ()
}

fun run : (Unit -> Unit needs {Reg}) -> List String
run f = f () with {
  reg e = {
    let rest = resume ()
    e :: rest
  }
  return _ = []
}

fun run_all : List (Unit -> Unit needs {Reg}) -> Int
run_all fns = case fns {
  [] -> 0
  f :: rest -> List.length (run f) + run_all rest
}

main () = run_all [fun () -> reg! "a"] with noop
"#;
    let out = emit_full(src);
    assert!(
        out.contains("fun (_Arg0, _Handle__script_Reg_reg, _ReturnK) ->"),
        "expected list callback lambda to receive lowered handler params\n{out}"
    );
}

#[test]
fn handler_returned_lambdas_capture_outer_effect_handlers() {
    let src = r#"
effect Log {
  fun log : String -> Unit
}

effect Step {
  fun step : Unit -> Unit
}

handler noop for Log {
  log _ = resume ()
}

handler exec for Step needs {Log} {
  step () = {
    let k = resume ()
    fun state -> {
      log! "ok"
      k state
    }
  }
  return _ = fun state -> state
}

fun run : (Unit -> Unit needs {Step}) -> Unit
  needs {Log}
run body = {
  let state_fn = { body () } with exec
  state_fn ()
}

main () = run (fun () -> step! ()) with noop
"#;
    let out = emit_full(src);
    assert!(
        out.contains("fun (State) ->"),
        "expected handler-returned lambda to stay unary and capture outer handlers\n{out}"
    );
    assert!(
        !out.contains("fun (State, _Handle__script_Log_log"),
        "handler-returned lambda unexpectedly took outer effect handlers as params\n{out}"
    );
}

#[test]
fn effectful_callbacks_in_records_get_lowered_handler_params() {
    let src = r#"
effect Reg {
  fun reg : String -> Unit
}

record Holder {
  cb: Unit -> Unit needs {Reg}
}

handler noop for Reg {
  reg _ = resume ()
}

fun run : (Unit -> Unit needs {Reg}) -> List String
run f = f () with {
  reg e = {
    let rest = resume ()
    e :: rest
  }
  return _ = []
}

fun run_holder : Holder -> Int
run_holder h = List.length (run h.cb)

main () = run_holder (Holder { cb: fun () -> reg! "a" }) with noop
"#;
    let out = emit_full(src);
    assert!(
        out.contains("fun (_Arg0, _Handle__script_Reg_reg, _ReturnK) ->"),
        "expected record-contained callback lambda to receive lowered handler params\n{out}"
    );
}

#[test]
fn effectful_callbacks_in_adts_get_lowered_handler_params() {
    let src = r#"
effect Reg {
  fun reg : String -> Unit
}

type Wrap
  = Wrap (Unit -> Unit needs {Reg})

handler noop for Reg {
  reg _ = resume ()
}

fun run : (Unit -> Unit needs {Reg}) -> List String
run f = f () with {
  reg e = {
    let rest = resume ()
    e :: rest
  }
  return _ = []
}

fun run_wrap : Wrap -> Int
run_wrap w = case w {
  Wrap f -> List.length (run f)
}

main () = run_wrap (Wrap (fun () -> reg! "a")) with noop
"#;
    let out = emit_full(src);
    assert!(
        out.contains("fun (_Arg0, _Handle__script_Reg_reg, _ReturnK) ->"),
        "expected ADT-contained callback lambda to receive lowered handler params\n{out}"
    );
}

#[test]
fn block_local_effectful_let_fun_value_uses_lowered_fun_arity() {
    let src = r#"
effect State s {
  fun get : Unit -> s
  fun put : s -> Unit
}

fun run_state : s -> (Unit -> a needs {State s}) -> (a, s)
run_state init f = {
  let state_fn = f () with {
    get () = fun s -> (resume s) s
    put new_s = fun _ -> (resume ()) new_s
    return value = fun s -> (value, s)
  }
  state_fn init
}

main () = {
  let build_msg () = get! ()
  let (msg, _) = run_state "" build_msg
  msg
}
    "#;
    let out = emit_full(src);
    assert!(
        out.contains("'build_msg'/4"),
        "expected block-local effectful let-fun to use lowered arity\n{out}"
    );
    assert!(
        !out.contains("'build_msg'/1"),
        "block-local effectful let-fun used source arity instead of lowered arity\n{out}"
    );
}

#[test]
fn recursive_block_local_effectful_let_fun_uses_lowered_fun_arity() {
    let src = r#"
effect State s {
  fun get : Unit -> s
  fun put : s -> Unit
}

fun run_state : s -> (Unit -> a needs {State s}) -> (a, s)
run_state init f = {
  let state_fn = f () with {
    get () = fun s -> (resume s) s
    put new_s = fun _ -> (resume ()) new_s
    return value = fun s -> (value, s)
  }
  state_fn init
}

main () = {
  let count_down n =
    if n == 0 then get! ()
    else count_down (n - 1)

  let (value, _) = run_state 2 (fun () -> count_down 2)
  value
}
"#;
    let out = emit_full(src);
    assert!(
        out.contains("'count_down'/4"),
        "expected recursive block-local effectful let-fun to use lowered arity\n{out}"
    );
    assert!(
        !out.contains("'count_down'/2"),
        "recursive block-local effectful let-fun used source arity instead of lowered arity\n{out}"
    );
}

// --- Literals ---

#[test]
fn lit_int() {
    assert_contains("main () = 42", "42");
}

#[test]
fn lit_string() {
    // Strings are emitted as binaries: #{#<byte>(8,1,'integer',['unsigned'|['big']]),..}#
    assert_contains(
        r#"main () = "hello""#,
        "#{#<104>(8,1,'integer',['unsigned'|['big']])",
    );
}

#[test]
fn lit_bool_true() {
    assert_contains("main () = True", "'true'");
}

#[test]
fn lit_bool_false() {
    assert_contains("main () = False", "'false'");
}

// --- Arithmetic ---

#[test]
fn binop_add() {
    assert_contains("main () = 1 + 2", "call 'erlang':'+'");
}

#[test]
fn binop_concat() {
    // In the full pipeline, <> elaborates through the Semigroup dictionary for String.
    let out = emit(r#"main () = "a" <> "b""#);
    assert!(
        out.contains("___dict_Std_Base_Semigroup") || out.contains("__dict_Std_Base_Semigroup"),
        "expected Semigroup dictionary-based concat lowering\n{out}"
    );
    assert!(
        out.contains("#{#<97>"),
        "missing left string literal\n{out}"
    );
    assert!(
        out.contains("#{#<98>"),
        "missing right string literal\n{out}"
    );
}

// --- If/else ---

#[test]
fn if_else_arms() {
    let src = "main () = if True then 1 else 2";
    let out = emit(src);
    assert!(out.contains("'true'"), "missing true arm\n{out}");
    assert!(out.contains("'false'"), "missing false arm\n{out}");
}

// --- Functions and application ---

#[test]
fn fun_arity_zero_for_unit_param() {
    // `main ()` keeps its Unit parameter at the Saga lowering level.
    assert_contains("main () = 42", "'main'/1");
}

#[test]
fn fun_arity_one() {
    assert_contains("double x = x + x", "'double'/1");
}

#[test]
fn apply_curried() {
    let src = "
id x = x
main () = id 42
";
    let out = emit(src);
    assert!(out.contains("apply"), "expected apply\n{out}");
}

// --- ADT constructors ---

#[test]
fn nothing_is_tagged_tuple() {
    // `Nothing` -> {'nothing'} (tagged 1-tuple)
    assert_contains("main () = Nothing", "{'nothing'}");
}

#[test]
fn just_is_tagged_tuple() {
    // `Just(42)` -> {'just', 42} (tagged tuple)
    let out = emit("main () = Just(42)");
    assert!(out.contains("42"), "missing value\n{out}");
    assert!(out.contains("'just'"), "missing just tag\n{out}");
}

#[test]
fn ok_uses_lowercase_atom() {
    // `Ok(1)` -> {ok, 1}
    let out = emit("main () = Ok(1)");
    assert!(out.contains("'ok'"), "missing ok atom\n{out}");
    assert!(!out.contains("'Ok'"), "should not have uppercase Ok\n{out}");
}

#[test]
fn err_uses_error_atom() {
    // `Err(1)` -> {error, 1}
    let out = emit("main () = Err(1)");
    assert!(out.contains("'error'"), "missing error atom\n{out}");
    assert!(
        !out.contains("'Err'"),
        "should not have uppercase Err\n{out}"
    );
}

// --- Lists ---

#[test]
fn nil_literal() {
    assert_contains("main () = []", "[]");
}

#[test]
fn cons_is_native_list() {
    // [1, 2] desugars to Cons 1 (Cons 2 Nil) -> [1|[2|[]]]
    let out = emit("main () = [1, 2]");
    assert!(out.contains("["), "missing list cons\n{out}");
    assert!(out.contains("|"), "missing cons separator\n{out}");
}

// --- Tuples ---

#[test]
fn tuple_two_elements() {
    let out = emit("main () = (1, 2)");
    assert!(out.contains("{"), "missing tuple\n{out}");
}

// --- Case / pattern matching ---

#[test]
fn case_on_bool() {
    let src = "
main () = case True {
  True -> 1
  False -> 2
}
";
    let out = emit(src);
    assert!(out.contains("case"), "missing case\n{out}");
    assert!(out.contains("'true'"), "missing true arm\n{out}");
}

#[test]
fn case_maybe_patterns() {
    // Just(v) lowers to {'just', v}, Nothing to {'nothing'}.
    // Arms stay in source order -- no reordering needed.
    let src = "
unwrap opt = case opt {
  Just(v) -> v
  Nothing -> 0
}
";
    let out = emit(src);
    assert!(
        out.contains("'nothing'"),
        "missing nothing pattern for Nothing\n{out}"
    );
    assert!(
        out.contains("'just'"),
        "missing just tag for Just pattern\n{out}"
    );
}

// --- Records ---

#[test]
fn record_create_is_tagged_tuple() {
    let src = "
record Point { x: Int, y: Int }
main () = Point { x: 1, y: 2 }
";
    let out = emit(src);
    assert!(out.contains("'_script_Point'"), "missing tag\n{out}");
    assert!(out.contains("1"), "missing x\n{out}");
    assert!(out.contains("2"), "missing y\n{out}");
}

#[test]
fn field_access_uses_element() {
    let src = "
record Point { x: Int, y: Int }
get_x p = p.x
";
    assert_contains_full(src, "call 'erlang':'element'");
}

#[test]
fn record_update_on_variable() {
    // When the record expression is a variable (not a literal RecordCreate),
    // the lowerer must resolve the record name from elaboration's type info.
    let src = "
record Point { x: Int, y: Int }
translate p = { p | x: 10, y: 20 }
";
    let out = emit_full(src);
    // The tag is extracted at runtime via element(1, rec), not a literal atom.
    // Both updated field values must appear in the output.
    assert!(out.contains("10"), "missing updated x\n{out}");
    assert!(out.contains("20"), "missing updated y\n{out}");
    // The result should be a 3-element tuple (tag + 2 fields)
    assert!(out.contains("{_Cor"), "expected tuple construction\n{out}");
}

// --- do...else ---

#[test]
fn do_else_nested_cases() {
    // do { x <- expr; success } else { _ -> fallback }
    // should emit a case with a fallback arm routing to the else case
    let src = "
safe_head xs = do {
  h :: _ <- xs
  h
} else {
  _ -> 0
}
";
    let out = emit(src);
    assert!(out.contains("case"), "expected case\n{out}");
}

#[test]
fn do_else_multiple_bindings_with_wildcard_fallback_lowers() {
    let src = r#"
type Result = Ok | Err

one flag = if flag then Ok else Err
two flag = if flag then Ok else Err

main a b = do {
  Ok <- one a
  Ok <- two b
  1
} else {
  Err -> 2
  _ -> 3
}
"#;
    let out = emit(src);
    assert!(out.contains("case"), "expected nested case lowering\n{out}");
    assert!(
        out.contains("{'error'}"),
        "expected explicit else constructor arm in lowered Core\n{out}"
    );
}

// --- Guards ---

#[test]
fn simple_guard_emitted_directly() {
    // Comparison guards are safe and go directly into the Core Erlang arm guard.
    let src = "
clamp x = case x {
  n when n < 0 -> 0
  n -> n
}
";
    let out = emit(src);
    assert!(
        out.contains("when"),
        "simple guard should emit 'when'\n{out}"
    );
}

#[test]
fn complex_guard_desugared_to_body() {
    // A guard containing a function call can't be a Core Erlang guard.
    // It should be desugared into an if/case in the arm body instead.
    let src = "
is_pos x = x > 0
filter_pos n = case n {
  x when is_pos x -> x
  _ -> 0
}
";
    let out = emit(src);
    // The complex guard must NOT appear as a `when` clause -- only `when 'true'` is allowed.
    // Instead it becomes a nested case inside the arm body.
    // Verify: every `when` in the output is immediately followed by `'true'`.
    assert!(
        out.split("when")
            .skip(1)
            .all(|s| s.trim_start().starts_with("'true'")),
        "complex guard must only emit `when 'true'`, not a function call\n{out}"
    );
}

#[test]
fn complex_guard_suffix_lowered_once_per_arm() {
    let src = r#"
g1 x = x > 0
g2 x = x > 1
g3 x = x > 2

main n = case n {
  0 when g1 n -> 10
  1 when g2 n -> 20
  2 when g3 n -> 30
  _ -> 40
}
"#;
    let out = emit_full(src);
    for guard_fn in ["g1", "g2", "g3"] {
        let needle = format!("apply '{guard_fn}'/1(");
        let count = out.matches(&needle).count();
        assert_eq!(
            count, 1,
            "expected exactly one lowered call for {guard_fn}, got {count}\n{out}"
        );
    }
}

// --- Nested effect calls in branches (CPS outer-K threading) ---

#[test]
fn effect_in_if_branch_threads_outer_k() {
    // When an effect call is inside an if-branch and there are subsequent
    // statements, the outer continuation must be threaded through the branches.
    // The continuation K should appear as the effect call's last argument,
    // NOT an identity function.
    let src = "
effect Fail {
  fun fail : (msg: String) -> a
}

fun process : Unit -> Unit needs {Fail}
process () = {
  let x = if True then fail! \"oops\" else ()
  x
}
";
    let out = emit(src);
    // The if-branches should be inside a case, and the fail! should get a
    // non-identity continuation that captures the rest of the block (x).
    // Specifically, the continuation K should reference the variable bound
    // from the effect result, not just return it unchanged.
    assert!(out.contains("case"), "expected case for if-branch\n{out}");
    // The continuation for the non-effect branch should apply K to 42
    assert!(
        out.contains("apply"),
        "expected apply for K-threading\n{out}"
    );
}

#[test]
fn effect_in_case_branch_threads_outer_k() {
    // Same issue but with case expressions instead of if.
    let src = "
effect Fail {
  fun fail : (msg: String) -> a
}

fun dispatch : (n: Int) -> Int needs {Fail}
dispatch n = {
  let x = case n {
    0 -> fail! \"zero\"
    n -> n
  }
  x + 1
}
";
    let out = emit(src);
    // Both branches should thread K. The fail! branch passes K to the handler,
    // the normal branch applies K to n.
    assert!(
        out.contains("apply"),
        "expected apply for continuation\n{out}"
    );
}

#[test]
fn nested_if_effect_threads_k_recursively() {
    // Nested if/case: K should be threaded through multiple levels.
    let src = "
effect Fail {
  fun fail : (msg: String) -> a
}

fun deep : (a: Bool) -> (b: Bool) -> Int needs {Fail}
deep a b = {
  let x = if a then (if b then fail! \"inner\" else 1) else 2
  x + 10
}
";
    let out = emit(src);
    assert!(
        out.contains("apply"),
        "expected apply for nested K-threading\n{out}"
    );
}

#[test]
fn effect_in_if_branch_k_not_identity() {
    // The key correctness property: the continuation passed to the handler
    // should NOT be an identity function (fun (X) -> X). It should capture
    // the rest of the block.
    let src = "
effect Fail {
  fun fail : (msg: String) -> a
}

fun process : Unit -> Int needs {Fail}
process () = {
  let x = if True then fail! \"oops\" else 42
  x + 1
}
";
    let out = emit(src);
    // With the fix, K is built from `x + 1` and threaded into branches.
    // The non-effect branch (42) should apply K: `apply K(42)`.
    // The effect branch passes K to the handler: `apply _HandleFail('fail', "oops", K)`.
    // Without the fix, the effect gets an identity K and `x + 1` runs after the if.
    //
    // Check that there's a fun wrapping `x + 1` (the K closure):
    assert!(
        out.contains("call 'erlang':'+'"),
        "expected addition in output\n{out}"
    );
    // The output should NOT have a flat `let X = case ... in X + 1` pattern.
    // Instead, the + should be inside a fun (the K closure).
    // We can verify by checking the fun count increased (K closure exists).
    let fun_count = out.matches("fun (").count();
    assert!(
        fun_count >= 2, // at least the outer function + K closure
        "expected at least 2 fun expressions (outer + K closure), got {}\n{}",
        fun_count,
        out
    );
}

// --- Handler arm bodies must not leak function-level _ReturnK ---

#[test]
fn handler_arm_does_not_apply_outer_return_k() {
    // When a function handles one effect internally (with { ... }) and also
    // uses a different effect (needs), the handler arm body must NOT apply
    // the function-level _ReturnK. The handler arm's result is the with-block
    // value, which flows to the rest of the block via rest_k.
    let src = r#"
effect Inner {
  fun inner_op : Unit -> Unit
}

effect Outer {
  fun outer_op : Unit -> Unit
}

fun middle : (body: Unit -> Unit needs {Inner}) -> Unit needs {Outer}
middle body = {
  let result = { body () } with {
    inner_op () = { resume (); "handled" }
    return _ = "ok"
  }
  outer_op! ()
}
"#;
    let out = emit(src);
    // The handler function for inner_op should NOT reference _ReturnK.
    // If it does, the handler bypasses outer_op! and returns directly
    // from the function, which is wrong.
    //
    // Find the handler function body. It's bound to _Handle_Inner_inner_op.
    // The key check: _ReturnK must not appear inside the handler function.
    //
    // Strategy: split output at the handler binding, check the handler fun
    // doesn't contain _ReturnK.
    // With canonical effect names, "_script.Inner" becomes "_Handle__script_Inner_inner_op"
    assert!(
        out.contains("_Handle__script_Inner_inner_op"),
        "expected Inner handler param in output\n{out}"
    );
    // The handler function for inner_op is between the handler param binding
    // and the string literal "handled". _ReturnK must not appear in that region.
    if let Some(start) = out.find("_Handle__script_Inner_inner_op")
        && let Some(end) = out[start..].find("\"handled\"")
    {
        let handler_body = &out[start..start + end];
        assert!(
            !handler_body.contains("_ReturnK"),
            "handler arm body must not reference _ReturnK!\nHandler region:\n{handler_body}\n\nFull output:\n{out}"
        );
    }
}

#[test]
fn nested_named_handlers_use_distinct_local_handle_bindings() {
    let src = r#"
effect Counter {
  fun get : Unit -> Int
}

handler add_one for Counter {
  get () = resume 10
  return value = value + 1
}

handler times_two for Counter {
  get () = resume 20
  return value = value * 2
}

main () = {
  dbg (get! () with {add_one, times_two})
}
"#;
    let out = emit_full(src);
    let shadowed = "let <_Handle__script_Counter_get> =\n      fun";
    assert!(
        !out.contains(shadowed),
        "expected nested named handlers to use fresh local binding names\n{out}"
    );
    assert!(
        out.contains("_Handle__script_Counter_get__"),
        "expected fresh scoped handler binding suffix in output\n{out}"
    );
}

// --- Short-circuit operators ---

#[test]
fn and_short_circuits() {
    let src = "main () = True && False";
    let out = emit(src);
    assert!(out.contains("case"), "expected case for &&\n{out}");
    assert!(
        out.contains("'false'"),
        "expected false short-circuit\n{out}"
    );
}

#[test]
fn or_short_circuits() {
    let src = "main () = False || True";
    let out = emit(src);
    assert!(out.contains("case"), "expected case for ||\n{out}");
    assert!(out.contains("'true'"), "expected true short-circuit\n{out}");
}

// --- Non-trivial patterns in let-bindings ---

#[test]
fn tuple_destructure_in_block() {
    // `let (a, b) = (1, 2)` in a block should destructure via case,
    // not silently discard the pattern.
    let src = "
main () = {
  let (a, b) = (1, 2)
  a
}
";
    let out = emit(src);
    // The destructuring should produce a case on the tuple
    assert!(
        out.contains("case"),
        "expected case for tuple destructure\n{out}"
    );
    // Variable A (lowered from `a`) should appear in the output
    assert!(out.contains("A"), "expected bound variable A\n{out}");
}

// --- Conversion builtins ---

// Int.to_float, Float.trunc/round/floor/ceil are now @external in Std/Int.saga and Std/Float.saga.
// Their codegen is covered by module integration tests.

#[test]
fn int_parse() {
    let src = "import Std.Int\nmain () = Int.parse \"42\"";
    let out = emit_full(src);
    assert!(
        out.contains("call 'std_int':'parse'"),
        "expected std_int:parse\n{out}"
    );
}

#[test]
fn float_parse() {
    let src = "import Std.Float\nmain () = Float.parse \"2.5\"";
    let out = emit_full(src);
    assert!(
        out.contains("call 'std_float':'parse'"),
        "expected std_float:parse\n{out}"
    );
}

// --- Dict builtins ---

#[test]
fn dict_empty() {
    let src = "import Std.Dict\nmain () = Dict.new ()";
    let out = emit_full(src);
    assert!(
        out.contains("call 'std_dict':'new'") || out.contains("call 'std_dict_bridge':'new'"),
        "expected dict new call\n{out}"
    );
}

// Dict.put, Dict.remove, Dict.keys, Dict.values, Dict.size, Dict.from_list,
// Dict.to_list, Dict.member are now @external in Std/Dict.saga.

#[test]
fn dict_get() {
    let src = "import Std.Dict\nmain () = Dict.get \"a\" (Dict.new ())";
    let out = emit_full(src);
    assert!(
        out.contains("call 'std_dict':'get'"),
        "expected std_dict:get\n{out}"
    );
}

// List.head, List.tail, List.length, List.map, List.filter, List.foldl, List.foldr,
// List.reverse, List.append, List.flat_map are now defined in Std/List.saga.

// --- @external ---

#[test]
fn external_fun_generates_wrapper() {
    let src = r#"
@external("erlang", "lists", "reverse")
fun reverse : (list: List a) -> List a
main () = 42
"#;
    let out = emit(src);
    // Should generate a wrapper function that calls lists:reverse
    assert!(
        out.contains("call 'lists':'reverse'"),
        "Expected call to lists:reverse in:\n{out}"
    );
    // Wrapper should be exported
    assert!(
        out.contains("'reverse'/1"),
        "Expected reverse/1 export in:\n{out}"
    );
}

#[test]
fn external_fun_direct_call() {
    let src = r#"
@external("erlang", "lists", "reverse")
fun reverse : (list: List a) -> List a

main () = reverse [1, 2, 3]
"#;
    let out = emit(src);
    assert!(
        out.contains("call 'lists':'reverse'"),
        "Expected direct call to lists:reverse in:\n{out}"
    );
}

#[test]
fn external_fun_multi_param() {
    let src = r#"
@external("erlang", "maps", "get")
fun get : (key: a) -> (map: Dict a b) -> b

@external("erlang", "maps", "new")
fun empty : Unit -> Dict a b

main () = get "x" (empty ())
"#;
    let out = emit(src);
    assert!(
        out.contains("call 'maps':'get'"),
        "Expected call to maps:get in:\n{out}"
    );
}

#[test]
fn external_fun_value_preserves_surface_unit_arity() {
    let src = r#"
@external("erlang", "maps", "new")
fun empty : Unit -> Dict a b

main () = {
  let f = empty
  f ()
}
"#;
    let out = emit(src);
    assert!(
        out.contains("'empty'/1"),
        "Expected external wrapper to keep surface Unit arity\n{out}"
    );
    assert!(
        out.contains("call 'maps':'new'"),
        "Expected wrapper body to call maps:new\n{out}"
    );
}

#[test]
fn external_fun_returning_maybe() {
    // An external function returning Maybe needs a bridge wrapper to convert
    // Erlang's Value|undefined convention to {just, Value}|{nothing}.
    // For now, test that the pattern match uses the tagged tuple form.
    let src = r#"
@external("erlang", "os", "getenv")
fun getenv : (name: String) -> Maybe String

main () = case getenv "HOME" {
  Just(dir) -> dir
  Nothing -> "/tmp"
}
"#;
    let out = emit(src);
    // Direct call to the external function
    assert!(
        out.contains("call 'os':'getenv'"),
        "Expected direct call to os:getenv in:\n{out}"
    );
    // Pattern match should use tagged tuples
    assert!(
        out.contains("'just'"),
        "Expected just tag for Just pattern in:\n{out}"
    );
    assert!(
        out.contains("'nothing'"),
        "Expected nothing tag for Nothing pattern in:\n{out}"
    );
}

#[test]
fn external_fun_returning_result() {
    // An external function returning Result should need no wrapping --
    // Ok(v) is {ok, v} and Err(e) is {error, e}, matching Erlang conventions.
    let src = r#"
@external("erlang", "file", "read_file")
fun read_file : (path: String) -> Result String String

main () = case read_file "/etc/hostname" {
  Ok(contents) -> contents
  Err(reason) -> reason
}
"#;
    let out = emit(src);
    // Direct call, no wrapping logic
    assert!(
        out.contains("call 'file':'read_file'"),
        "Expected direct call to file:read_file in:\n{out}"
    );
    // Pattern match should use lowercase atoms
    assert!(
        out.contains("'ok'"),
        "Expected ok atom for Ok pattern in:\n{out}"
    );
    assert!(
        out.contains("'error'"),
        "Expected error atom for Err pattern in:\n{out}"
    );
}

// --- Error terms and source annotations ---

#[test]
fn panic_emits_structured_error_term() {
    let out = emit_full(r#"main () = panic "boom""#);
    assert!(
        out.contains("'saga_error'"),
        "Expected saga_error atom in:\n{out}"
    );
    assert!(
        out.contains("'panic'"),
        "Expected panic kind atom in:\n{out}"
    );
}

#[test]
fn todo_emits_structured_error_term() {
    let out = emit_full("main () = todo ()");
    assert!(
        out.contains("'saga_error'"),
        "Expected saga_error atom in:\n{out}"
    );
    assert!(out.contains("'todo'"), "Expected todo kind atom in:\n{out}");
}

#[test]
fn let_assert_emits_structured_error_term() {
    let out = emit_full("main () = {\n  let assert 1 = 2\n  1\n}");
    assert!(
        out.contains("'saga_error'"),
        "Expected saga_error atom in:\n{out}"
    );
    assert!(
        out.contains("'assert_fail'"),
        "Expected assert_fail kind atom in:\n{out}"
    );
}

#[test]
fn source_annotations_emitted_with_source_info() {
    let src = "fun add : Int -> Int -> Int\nadd x y = x + y\n\nmain () = add 1 2";
    let sf = super::SourceFile {
        path: "test.saga".to_string(),
        source: src.to_string(),
    };
    let out = emit_full_with_source(src, Some(&sf));
    // The add call on line 4 should have an annotation
    assert!(
        out.contains("-| [4, {'file', \"test.saga\"}]"),
        "Expected line annotation for add call in:\n{out}"
    );
}

#[test]
fn binop_annotation_on_inner_call() {
    let src = "main () = 1 + 2";
    let sf = super::SourceFile {
        path: "test.saga".to_string(),
        source: src.to_string(),
    };
    let out = emit_full_with_source(src, Some(&sf));
    // The + operation should produce an annotated erlang:'+' call
    assert!(
        out.contains("-| [1, {'file', \"test.saga\"}]"),
        "Expected line annotation on binop call in:\n{out}"
    );
}

#[test]
fn no_annotations_without_source_info() {
    let out = emit_full("main () = 1 + 2");
    assert!(
        !out.contains("-|"),
        "Expected no annotations without source info in:\n{out}"
    );
}
