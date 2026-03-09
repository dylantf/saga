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

// --- Effect handlers ---

#[test]
fn effect_call_lowers_to_throw() {
    let src = "
effect Fail {
    fun fail (msg: String) -> a
}

fun explode () -> Int needs {Fail}
explode () = fail! \"boom\"
";
    let out = emit_elaborated(src);
    // Should emit erlang:throw with __effect__ tag
    assert!(
        out.contains("'erlang':'throw'"),
        "expected erlang:throw for effect call\n{out}"
    );
    assert!(
        out.contains("'__effect__'"),
        "expected __effect__ tag in throw\n{out}"
    );
    assert!(
        out.contains("'fail'"),
        "expected 'fail' operation name in throw\n{out}"
    );
}

#[test]
fn with_inline_handler_lowers_to_try_catch() {
    let src = "
effect Fail {
    fun fail (msg: String) -> a
}

fun safe_div (x: Int) (y: Int) -> Int needs {Fail}
safe_div x y = if y == 0 then fail! \"division by zero\" else x / y

main () = {
    (safe_div 10 0) with {
        fail msg -> 0
    }
}
";
    let out = emit_elaborated(src);
    // Should emit try/catch structure
    assert!(out.contains("try"), "expected try in output\n{out}");
    assert!(out.contains("catch"), "expected catch in output\n{out}");
    // Catch body should match on __effect__ tag
    assert!(
        out.contains("'__effect__'"),
        "expected __effect__ pattern in catch\n{out}"
    );
    // Should have erlang:raise for re-throwing unhandled
    assert!(
        out.contains("'erlang':'raise'"),
        "expected erlang:raise for unhandled effects\n{out}"
    );
}

#[test]
fn with_return_clause() {
    let src = "
type Result a b { Ok(a) | Err(b) }

effect Fail {
    fun fail (msg: String) -> a
}

main () = {
    42 with {
        fail msg -> Err msg
        return value -> Ok value
    }
}
";
    let out = emit_elaborated(src);
    // Should have try with success path wrapping in Ok
    assert!(out.contains("try"), "expected try\n{out}");
    // The success path should produce Ok (tagged tuple)
    assert!(
        out.contains("'Ok'"),
        "expected Ok constructor in return clause\n{out}"
    );
    // The fail arm should produce Err
    assert!(
        out.contains("'Err'"),
        "expected Err constructor in fail handler\n{out}"
    );
}

#[test]
fn named_handler_lowers_to_try_catch() {
    let src = "
type Result a b { Ok(a) | Err(b) }

effect Fail {
    fun fail (msg: String) -> a
}

handler to_result for Fail {
    fail msg -> Err msg
    return value -> Ok value
}

main () = {
    42 with to_result
}
";
    let out = emit_elaborated(src);
    assert!(out.contains("try"), "expected try\n{out}");
    assert!(
        out.contains("'Ok'"),
        "expected Ok from return clause\n{out}"
    );
    assert!(
        out.contains("'Err'"),
        "expected Err from fail arm\n{out}"
    );
}

#[test]
fn effect_in_function_with_needs() {
    let src = "
type Result a b { Ok(a) | Err(b) }

effect Fail {
    fun fail (msg: String) -> a
}

fun safe_div (x: Int) (y: Int) -> Int needs {Fail}
safe_div x y = if y == 0 then fail! \"division by zero\" else x / y

handler to_result for Fail {
    fail msg -> Err msg
    return value -> Ok value
}

main () = (safe_div 10 2) with to_result
";
    let out = emit_elaborated(src);
    // safe_div should contain throw
    assert!(
        out.contains("'erlang':'throw'"),
        "expected throw in safe_div\n{out}"
    );
    // main should contain try/catch
    assert!(out.contains("try"), "expected try in main\n{out}");
}

#[test]
#[should_panic(expected = "Resumable handlers are not yet supported")]
fn resume_in_handler_panics() {
    let src = "
effect Log {
    fun log (msg: String) -> Unit
}

main () = {
    42 with {
        log msg -> resume ()
    }
}
";
    emit_elaborated(src);
}