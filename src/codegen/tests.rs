#[cfg(test)]
use super::emit_module;
use crate::lexer::Lexer;
use crate::parser::Parser;

/// Parse `src` and emit Core Erlang for a module named "test".
fn emit(src: &str) -> String {
    let tokens = Lexer::new(src).lex().expect("lex error");
    let program = Parser::new(tokens).parse_program().expect("parse error");
    emit_module("test", &program)
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
fn adt_zero_arg_is_atom() {
    // `None` with no args -> bare atom 'None'
    assert_contains("main () = None", "'None'");
}

#[test]
fn adt_one_arg_is_tagged_tuple() {
    // `Some(42)` -> {'Some', 42}
    let out = emit("main () = Some(42)");
    assert!(out.contains("'Some'"), "missing tag\n{out}");
    assert!(out.contains("42"), "missing value\n{out}");
    assert!(out.contains("{"), "missing tuple\n{out}");
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
fn case_constructor_patterns() {
    let src = "
unwrap opt = case opt {
  Some(v) -> v
  None -> 0
}
";
    let out = emit(src);
    assert!(out.contains("'Some'"), "missing Some pattern\n{out}");
    assert!(out.contains("'None'"), "missing None pattern\n{out}");
}

// --- Records ---

#[test]
fn record_create_is_tagged_tuple() {
    let src = "
record Point { x: Int, y: Int }
main () = Point { x: 1, y: 2 }
";
    let out = emit(src);
    assert!(out.contains("'test_Point'"), "missing tag\n{out}");
    assert!(out.contains("1"), "missing x\n{out}");
    assert!(out.contains("2"), "missing y\n{out}");
}

#[test]
fn field_access_uses_element() {
    let src = "
record Point { x: Int, y: Int }
get_x p = p.x
";
    assert_contains(
        src,
        "call 'erlang':'element'",
    );
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
  n if n < 0 -> 0
  n -> n
}
";
    let out = emit(src);
    assert!(out.contains("when"), "simple guard should emit 'when'\n{out}");
}

#[test]
fn complex_guard_desugared_to_body() {
    // A guard containing a function call can't be a Core Erlang guard.
    // It should be desugared into an if/case in the arm body instead.
    let src = "
is_pos x = x > 0
filter_pos n = case n {
  x if is_pos x -> x
  _ -> 0
}
";
    let out = emit(src);
    // The complex guard must NOT appear as a `when` clause -- only `when 'true'` is allowed.
    // Instead it becomes a nested case inside the arm body.
    // Verify: every `when` in the output is immediately followed by `'true'`.
    assert!(
        out.split("when").skip(1).all(|s| s.trim_start().starts_with("'true'")),
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
  fun fail (msg: String) -> Never
}

fun process () -> Unit needs {Fail}
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
    assert!(
        out.contains("case"),
        "expected case for if-branch\n{out}"
    );
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
  fun fail (msg: String) -> Never
}

fun dispatch (n: Int) -> Int needs {Fail}
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
  fun fail (msg: String) -> Never
}

fun deep (a: Bool) (b: Bool) -> Int needs {Fail}
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
  fun fail (msg: String) -> Never
}

fun process () -> Int needs {Fail}
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

// --- Short-circuit operators ---

#[test]
fn and_short_circuits() {
    let src = "main () = True && False";
    let out = emit(src);
    assert!(out.contains("case"), "expected case for &&\n{out}");
    assert!(out.contains("'false'"), "expected false short-circuit\n{out}");
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
    assert!(out.contains("case"), "expected case for tuple destructure\n{out}");
    // Variable A (lowered from `a`) should appear in the output
    assert!(out.contains("A"), "expected bound variable A\n{out}");
}
