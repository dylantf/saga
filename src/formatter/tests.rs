use crate::formatter;
use crate::lexer::Lexer;
use crate::parser::Parser;

/// Parse source, format at given width, return the formatted string.
fn fmt(source: &str, width: usize) -> String {
    let tokens = Lexer::new(source).lex().unwrap();
    let mut parser = Parser::new(tokens);
    let program = parser.parse_program_annotated().unwrap();
    formatter::format(&program, width)
}

/// Format at default width (80).
fn fmt80(source: &str) -> String {
    fmt(source, 80)
}

// --- Fun bindings ---

#[test]
fn fun_binding_short_stays_on_one_line() {
    assert_eq!(fmt80("add x y = x + y"), "add x y = x + y\n");
}

#[test]
fn fun_binding_long_breaks_after_eq() {
    let src = "process_all_the_things x y z = some_very_long_function_name x y z";
    let result = fmt(src, 40);
    assert_eq!(
        result,
        "process_all_the_things x y z =\n  some_very_long_function_name x y z\n"
    );
}

#[test]
fn fun_binding_block_body_stays_on_eq_line() {
    let src = "process path = {\n  log! path\n}";
    assert_eq!(fmt80(src), "process path = {\n  log! path\n}\n");
}

#[test]
fn fun_binding_case_body_stays_on_eq_line() {
    let src = "dispatch shape = case shape {\n  Circle(r) -> r\n  Point -> 0.0\n}";
    assert_eq!(
        fmt80(src),
        "dispatch shape = case shape {\n  Circle(r) -> r\n  Point -> 0.0\n}\n"
    );
}

// --- Let bindings (declarations) ---

#[test]
fn let_decl_short_stays_on_one_line() {
    assert_eq!(fmt80("let x = 42"), "let x = 42\n");
}

#[test]
fn let_decl_long_breaks_after_eq() {
    let src = "let some_very_long_name = some_very_long_expression_that_is_way_too_wide";
    let result = fmt(src, 50);
    assert_eq!(
        result,
        "let some_very_long_name =\n  some_very_long_expression_that_is_way_too_wide\n"
    );
}

// --- Let statements (inside blocks) ---

#[test]
fn let_stmt_short_stays_on_one_line() {
    let src = "main () = {\n  let x = 42\n}";
    assert_eq!(fmt80(src), "main () = {\n  let x = 42\n}\n");
}

#[test]
fn let_stmt_long_breaks_after_eq() {
    let src = "main () = {\n  let result = some_very_long_function applied_to arguments\n}";
    let result = fmt(src, 40);
    // Application doesn't break args yet, so the whole body stays as one chunk
    assert_eq!(
        result,
        "main () = {\n  let result =\n    some_very_long_function applied_to arguments\n}\n"
    );
}

// --- Pipes ---

#[test]
fn pipe_short_stays_on_one_line() {
    assert_eq!(fmt80("f x = x |> add 1"), "f x = x |> add 1\n");
}

#[test]
fn pipe_long_breaks_per_segment() {
    let src = "f x = x |> add 1 |> multiply 2 |> subtract 3 |> divide 4 |> negate";
    let result = fmt(src, 40);
    assert!(result.contains("|> add 1\n"));
    assert!(result.contains("|> multiply 2\n"));
}

#[test]
fn pipe_multiline_preserved() {
    // User explicitly put |> on new lines — should stay multi-line
    let src = "f x = x\n  |> add 1\n  |> double";
    let result = fmt80(src);
    assert!(result.contains("|> add 1\n"));
    assert!(result.contains("|> double\n"));
}

#[test]
fn pipe_with_comments_stays_multiline() {
    let src = "f x = x\n  # before pipe\n  |> add 1\n  |> double";
    let result = fmt80(src);
    assert!(result.contains("# before pipe\n"));
    assert!(result.contains("|> add 1\n"));
}

// --- If-then-else ---

#[test]
fn if_short_stays_on_one_line() {
    assert_eq!(
        fmt80("pick x = if x > 0 then x else -x"),
        "pick x = if x > 0 then x else -x\n"
    );
}

#[test]
fn if_long_breaks_before_else() {
    let src = "pick x = if some_long_condition x then some_long_result x else other_long_result x";
    let result = fmt(src, 50);
    assert!(result.contains("then"), "result: {}", result);
    assert!(
        result.contains("\n  else") || result.contains("\nelse"),
        "result: {}",
        result
    );
}

// --- Blocks ---

#[test]
fn block_preserves_braces() {
    let src = "main () = {\n  println \"hello\"\n}";
    assert_eq!(fmt80(src), "main () = {\n  println \"hello\"\n}\n");
}

#[test]
fn block_with_multiple_stmts() {
    let src = "main () = {\n  let x = 1\n  println x\n}";
    assert_eq!(fmt80(src), "main () = {\n  let x = 1\n  println x\n}\n");
}

// --- Comments ---

#[test]
fn trailing_comment_preserved() {
    assert_eq!(
        fmt80("let x = 42 # the answer"),
        "let x = 42 # the answer\n"
    );
}

#[test]
fn leading_comment_preserved() {
    assert_eq!(
        fmt80("# a comment\nlet x = 42"),
        "# a comment\nlet x = 42\n"
    );
}

// --- Fun signatures ---

#[test]
fn fun_sig_short_stays_on_one_line() {
    assert_eq!(
        fmt80("fun add : Int -> Int -> Int"),
        "fun add : Int -> Int -> Int\n"
    );
}

#[test]
fn fun_sig_with_needs_stays_on_one_line() {
    assert_eq!(
        fmt80("fun process : String -> Unit needs {Log}"),
        "fun process : String -> Unit needs {Log}\n"
    );
}

#[test]
fn fun_sig_long_breaks_needs() {
    let src =
        "fun process_everything : String -> Int -> Result String Error needs {Log, Actor, Process}";
    let result = fmt(src, 60);
    // needs clause should break to next line
    assert!(result.contains("\n  needs {"), "result: {}", result);
}

// --- Idempotency ---

#[test]
fn idempotent_scratch_file() {
    let source = std::fs::read_to_string("examples/scratch.dy").unwrap();
    let first = fmt80(&source);
    let second = fmt80(&first);
    assert_eq!(first, second, "Formatter is not idempotent");
}
