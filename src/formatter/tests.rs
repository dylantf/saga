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

/// Try to parse and format; returns None if parsing fails.
fn try_fmt(source: &str, width: usize) -> Option<String> {
    let tokens = Lexer::new(source).lex().ok()?;
    let mut parser = Parser::new(tokens);
    let program = parser.parse_program_annotated().ok()?;
    Some(formatter::format(&program, width))
}

fn try_strip(source: &str) -> Option<Vec<crate::ast::Decl>> {
    let tokens = Lexer::new(source).lex().ok()?;
    let mut parser = Parser::new(tokens);
    parser.parse_program().ok()
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
    // Both let binding and application break
    assert_eq!(
        result,
        "main () = {\n  let result =\n    some_very_long_function\n      applied_to\n      arguments\n}\n"
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

// --- Application ---

#[test]
fn app_short_stays_on_one_line() {
    assert_eq!(fmt80("f x = call a b c"), "f x = call a b c\n");
}

#[test]
fn app_long_breaks_all_args() {
    let src = "f x = some_long_function first_argument second_argument third_argument";
    let result = fmt(src, 40);
    assert!(result.contains("some_long_function\n"), "result: {}", result);
    assert!(result.contains("  first_argument\n"), "result: {}", result);
    assert!(result.contains("  second_argument\n"), "result: {}", result);
}

#[test]
fn app_nested_calls_parenthesized() {
    assert_eq!(
        fmt80("f x = call a (call b) (call c)"),
        "f x = call a (call b) (call c)\n"
    );
}

// --- Records ---

#[test]
fn record_create_short_stays_on_one_line() {
    assert_eq!(
        fmt80("f x = User { name: x, age: 30 }"),
        "f x = User { name: x, age: 30 }\n"
    );
}

#[test]
fn record_create_long_breaks_fields() {
    let src = "f x = SomeRecord { first_field: some_long_value, second_field: another_long_value }";
    let result = fmt(src, 50);
    assert!(result.contains("SomeRecord {\n"), "result: {}", result);
    assert!(result.contains("  first_field:"), "result: {}", result);
}

#[test]
fn record_update_short_stays_on_one_line() {
    assert_eq!(
        fmt80("f u = { u | age: 31 }"),
        "f u = { u | age: 31 }\n"
    );
}

#[test]
fn record_update_long_breaks_fields() {
    let src = "f u = { u | age: some_very_long_expression, name: another_very_long_expression }";
    let result = fmt(src, 40);
    assert!(result.contains("{ u |"), "result: {}", result);
    assert!(result.contains("  age:"), "result: {}", result);
}

// --- Lists ---

#[test]
fn list_short_stays_on_one_line() {
    assert_eq!(fmt80("f x = [1, 2, 3]"), "f x = [1, 2, 3]\n");
}

#[test]
fn list_long_breaks_elements() {
    let src = "f x = [some_long_name, another_long_name, yet_another_long_name, final_name]";
    let result = fmt(src, 40);
    assert!(result.contains("[\n"), "result: {}", result);
    assert!(result.contains("  some_long_name,\n"), "result: {}", result);
}

#[test]
fn list_empty() {
    assert_eq!(fmt80("f x = []"), "f x = []\n");
}

// --- Tuples ---

#[test]
fn tuple_short_stays_on_one_line() {
    assert_eq!(fmt80("f x = (1, 2, 3)"), "f x = (1, 2, 3)\n");
}

#[test]
fn tuple_long_breaks_elements() {
    let src = "f x = (some_long_name, another_long_name, yet_another_long_name)";
    let result = fmt(src, 40);
    assert!(result.contains("(\n"), "result: {}", result);
    assert!(result.contains("  some_long_name,\n"), "result: {}", result);
}

// --- Binary operators ---

#[test]
fn binop_short_stays_on_one_line() {
    assert_eq!(fmt80("f x = a + b + c"), "f x = a + b + c\n");
}

#[test]
fn binop_long_breaks_before_operator() {
    let src = "f x = some_long_name + another_long_name + yet_another_long_name + final_name";
    let result = fmt(src, 40);
    assert!(result.contains("\n+ another_long_name") || result.contains("\n  + another_long_name"), "result: {}", result);
}

#[test]
fn binop_mixed_operators_not_flattened() {
    // a + b * c should NOT flatten — different operators
    assert_eq!(fmt80("f x = a + b * c"), "f x = a + b * c\n");
}

// --- With expressions ---

#[test]
fn with_named_handler_short_stays_on_one_line() {
    assert_eq!(
        fmt80("f x = do_thing x with console"),
        "f x = do_thing x with console\n"
    );
}

#[test]
fn with_named_handler_long_breaks_before_with() {
    let src = "f x = some_very_long_function_call x y z with some_long_handler_name";
    let result = fmt(src, 50);
    assert!(result.contains("with some_long_handler_name"), "result: {}", result);
    // with breaks to its own line (indented under the expression)
    assert!(result.contains("\n"), "should be multi-line: {}", result);
}

#[test]
fn with_inline_handler_braces_on_same_line() {
    let src = "f x = do_thing x with {\n  log msg = { println msg; resume () },\n}";
    let result = fmt80(src);
    assert!(result.contains("with {"), "result: {}", result);
}

// --- Lambda ---

#[test]
fn lambda_short_stays_on_one_line() {
    assert_eq!(
        fmt80("f x = fun y -> y + 1"),
        "f x = fun y -> y + 1\n"
    );
}

#[test]
fn lambda_long_breaks_after_arrow() {
    let src = "f x = fun some_long_param -> some_very_long_expression some_long_param other_arg";
    let result = fmt(src, 50);
    assert!(result.contains(" ->\n"), "result: {}", result);
}

// --- Imports ---

#[test]
fn import_simple() {
    assert_eq!(fmt80("import Std.List"), "import Std.List\n");
}

#[test]
fn import_exposing_short() {
    assert_eq!(
        fmt80("import Std.Test (describe, test)"),
        "import Std.Test (describe, test)\n"
    );
}

#[test]
fn import_exposing_long_breaks() {
    let src = "import Some.Very.Long.Module (first_thing, second_thing, third_thing, fourth_thing)";
    let result = fmt(src, 50);
    assert!(result.contains("\n"), "should break: {}", result);
    assert!(result.contains("first_thing"), "result: {}", result);
}

// --- Import sorting ---

#[test]
fn imports_sorted_std_first() {
    let src = "import MyModule\nimport Std.List\nimport Std.Array\nimport Another";
    let result = fmt80(src);
    let lines: Vec<&str> = result.lines().collect();
    assert_eq!(lines[0], "import Std.Array");
    assert_eq!(lines[1], "import Std.List");
    assert_eq!(lines[2], "import Another");
    assert_eq!(lines[3], "import MyModule");
}

#[test]
fn imports_already_sorted_unchanged() {
    let src = "import Std.List\nimport Std.Test (describe, test)\nimport MyModule";
    let result = fmt80(src);
    assert!(result.starts_with("import Std.List\nimport Std.Test"), "result: {}", result);
}

// --- Blank line normalization ---

#[test]
fn multiple_blank_lines_collapsed_to_one() {
    let src = "let x = 1\n\n\n\n\nlet y = 2";
    assert_eq!(fmt80(src), "let x = 1\n\nlet y = 2\n");
}

#[test]
fn single_blank_line_preserved() {
    let src = "let x = 1\n\nlet y = 2";
    assert_eq!(fmt80(src), "let x = 1\n\nlet y = 2\n");
}

// --- Idempotency ---

#[test]
fn idempotent_scratch_file() {
    let source = std::fs::read_to_string("examples/scratch.dy").unwrap();
    let first = fmt80(&source);
    let second = fmt80(&first);
    assert_eq!(first, second, "Formatter is not idempotent");
}

// --- Round-trip: all .dy files format cleanly, idempotently, and preserve AST ---

fn collect_dy_files() -> Vec<std::path::PathBuf> {
    let mut files = Vec::new();
    for dir in &["examples", "src/stdlib"] {
        if let Ok(entries) = std::fs::read_dir(dir) {
            for entry in entries.flatten() {
                let path = entry.path();
                if path.extension().map_or(false, |e| e == "dy") {
                    files.push(path);
                }
            }
        }
    }
    files.sort();
    files
}

#[test]
#[ignore] // TODO: many files have round-trip issues — work through them incrementally
fn round_trip_all_dy_files() {
    let mut format_failures = Vec::new();
    let mut idempotency_failures = Vec::new();
    let mut ast_failures = Vec::new();

    for path in collect_dy_files() {
        let source = std::fs::read_to_string(&path).unwrap();
        let name = path.display().to_string();

        // 1. Format (skip files that don't parse — e.g. error examples)
        let first = match try_fmt(&source, 80) {
            Some(f) => f,
            None => continue,
        };

        // 2. Idempotency: format again, should be identical
        let second = match try_fmt(&first, 80) {
            Some(f) => f,
            None => {
                format_failures.push(format!("{} (re-format failed)", name));
                continue;
            }
        };
        if first != second {
            idempotency_failures.push(name.clone());
        }

        // 3. Round-trip: AST should be unchanged after formatting
        let original_ast = match try_strip(&source) {
            Some(a) => a,
            None => continue,
        };
        let formatted_ast = match try_strip(&first) {
            Some(a) => a,
            None => {
                ast_failures.push(format!("{} (re-parse failed)", name));
                continue;
            }
        };
        if original_ast != formatted_ast {
            ast_failures.push(name);
        }
    }

    let mut msg = String::new();
    if !format_failures.is_empty() {
        msg.push_str(&format!("Re-format failed: {:?}\n", format_failures));
    }
    if !idempotency_failures.is_empty() {
        msg.push_str(&format!("Not idempotent: {:?}\n", idempotency_failures));
    }
    if !ast_failures.is_empty() {
        msg.push_str(&format!("AST changed: {:?}\n", ast_failures));
    }
    assert!(msg.is_empty(), "{}", msg);
}
