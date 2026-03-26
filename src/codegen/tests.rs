#[cfg(test)]
use super::emit_module;
use super::{emit_module_with_context, CodegenContext};
use crate::lexer::Lexer;
use crate::parser::Parser;
use crate::{derive, desugar, elaborate, typechecker};

/// Parse `src` and emit Core Erlang for a single-file script module.
/// Skips typechecking and elaboration — only tests basic lowering.
fn emit(src: &str) -> String {
    let tokens = Lexer::new(src).lex().expect("lex error");
    let mut program = Parser::new(tokens).parse_program().expect("parse error");
    desugar::desugar_program(&mut program);
    emit_module("_script", &program)
}

/// Parse, typecheck, elaborate, and emit Core Erlang — mirrors the real compiler pipeline.
fn emit_full(src: &str) -> String {
    let tokens = Lexer::new(src).lex().expect("lex error");
    let mut program = Parser::new(tokens).parse_program().expect("parse error");
    derive::expand_derives(&mut program);
    desugar::desugar_program(&mut program);

    let mut checker = typechecker::Checker::with_prelude(None).expect("prelude error");
    let result = checker.check_program(&program);
    assert!(
        !result.has_errors(),
        "Type errors: {:?}",
        result.errors()
    );

    let elaborated = elaborate::elaborate(&program, &result);
    let ctx = CodegenContext {
        modules: std::collections::HashMap::new(),
        let_effect_bindings: result.let_effect_bindings.clone(),
        prelude_imports: result.prelude_imports.clone(),
    };
    emit_module_with_context("_script", &elaborated, &ctx)
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

// --- Literals ---

#[test]
fn lit_int() {
    assert_contains("main () = 42", "42");
}

#[test]
fn lit_string() {
    assert_contains(r#"main () = "hello""#, r#""hello""#);
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
    assert_contains(r#"main () = "a" <> "b""#, "call 'erlang':'++'");
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
    // `main ()` has a unit param -- should export as 'main'/0
    assert_contains("main () = 42", "'main'/0");
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
fn none_is_undefined_atom() {
    // `Nothing` -> 'undefined' (BEAM convention)
    assert_contains("main () = Nothing", "'undefined'");
}

#[test]
fn some_is_bare_value() {
    // `Just(42)` -> 42 (bare value, no tuple wrapping)
    let out = emit("main () = Just(42)");
    assert!(out.contains("42"), "missing value\n{out}");
    assert!(!out.contains("'Just'"), "should not have Just tag\n{out}");
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
    // Just(v) lowers to bare variable, Nothing to 'undefined'.
    // Nothing arm must come before Just arm (specific before wildcard).
    let src = "
unwrap opt = case opt {
  Just(v) -> v
  Nothing -> 0
}
";
    let out = emit(src);
    assert!(
        out.contains("'undefined'"),
        "missing undefined pattern for Nothing\n{out}"
    );
    // Just(v) becomes a bare variable pattern
    assert!(!out.contains("'Just'"), "should not have Just tag\n{out}");
    // undefined arm should come before the variable arm
    let undef_pos = out.find("'undefined'").unwrap();
    let v_pos = out.rfind("V").unwrap();
    assert!(
        undef_pos < v_pos,
        "undefined arm should come before variable arm\n{out}"
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
    assert_contains(src, "call 'erlang':'element'");
}

#[test]
fn record_update_on_variable() {
    // When the record expression is a variable (not a literal RecordCreate),
    // the lowerer must resolve the record name from the update's field names.
    let src = "
record Point { x: Int, y: Int }
translate p = { p | x: 10, y: 20 }
";
    let out = emit(src);
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

// --- Guards ---

#[test]
fn simple_guard_emitted_directly() {
    // Comparison guards are safe and go directly into the Core Erlang arm guard.
    let src = "
clamp x = case x {
  n | n < 0 -> 0
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
  x | is_pos x -> x
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
  let x = if True then fail! \"oops\" else 42
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

fun middle : (body: () -> Unit needs {Inner}) -> Unit needs {Outer}
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
    assert!(
        out.contains("_Handle_Inner_inner_op"),
        "expected Inner handler param in output\n{out}"
    );
    // The handler function for inner_op is between "_Handle_Inner_inner_op"
    // and the string literal "handled". _ReturnK must not appear in that region.
    if let Some(start) = out.find("_Handle_Inner_inner_op")
        && let Some(end) = out[start..].find("\"handled\"")
    {
        let handler_body = &out[start..start + end];
        assert!(
            !handler_body.contains("_ReturnK"),
            "handler arm body must not reference _ReturnK!\nHandler region:\n{handler_body}\n\nFull output:\n{out}"
        );
    }
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

// Int.to_float, Float.trunc/round/floor/ceil are now @external in Std/Int.dy and Std/Float.dy.
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
// Dict.to_list, Dict.member are now @external in Std/Dict.dy.

#[test]
fn dict_get() {
    let src = "import Std.Dict\nfun main : Unit -> Maybe Int\nmain () = Dict.get \"a\" (Dict.new ())";
    let out = emit_full(src);
    assert!(
        out.contains("call 'std_dict':'get'"),
        "expected std_dict:get\n{out}"
    );
}

// List.head, List.tail, List.length, List.map, List.filter, List.foldl, List.foldr,
// List.reverse, List.append, List.flat_map are now defined in Std/List.dy.

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
fn external_fun_returning_maybe() {
    // An external function returning Maybe should need no wrapping --
    // Some(v) is a bare value and None is 'undefined', matching Erlang conventions.
    let src = r#"
@external("erlang", "os", "getenv")
fun getenv : (name: String) -> Maybe String

main () = case getenv "HOME" {
  Just(dir) -> dir
  Nothing -> "/tmp"
}
"#;
    let out = emit(src);
    // Direct call, no wrapping logic
    assert!(
        out.contains("call 'os':'getenv'"),
        "Expected direct call to os:getenv in:\n{out}"
    );
    // No tuple wrapping around the result
    assert!(
        !out.contains("'Just'"),
        "Should not have Just tag in:\n{out}"
    );
    // Pattern match should use 'undefined' for None
    assert!(
        out.contains("'undefined'"),
        "Expected undefined pattern for None in:\n{out}"
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
