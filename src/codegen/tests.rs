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
    assert!(out.contains("'Point'"), "missing tag\n{out}");
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

// --- Builtins ---

#[test]
fn show_int_calls_io_lib() {
    assert_contains("main () = show 42", "call 'io_lib':'format'");
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
