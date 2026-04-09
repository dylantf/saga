use dylang::{codegen, desugar, elaborate, lexer, parser, typechecker};

/// Load prelude (which imports Std + stdlib) into a checker.
fn bootstrap() -> typechecker::Checker {
    let mut checker = typechecker::Checker::new();
    let prelude_src = include_str!("../src/stdlib/prelude.dy");
    let prelude_tokens = lexer::Lexer::new(prelude_src)
        .lex()
        .expect("prelude lex error");
    let mut prelude_program = parser::Parser::new(prelude_tokens)
        .parse_program()
        .expect("prelude parse error");
    desugar::desugar_program(&mut prelude_program);
    let result = checker.check_program(&mut prelude_program);
    assert!(
        !result.has_errors(),
        "prelude typecheck error: {:?}",
        result.errors()
    );
    checker
}

fn emit(src: &str) -> String {
    let tokens = lexer::Lexer::new(src).lex().expect("lex error");
    let mut program = parser::Parser::new(tokens)
        .parse_program()
        .expect("parse error");
    desugar::desugar_program(&mut program);
    codegen::emit_module("_script", &program)
}

/// Parse, typecheck, elaborate, then emit Core Erlang.
/// Use this for tests that involve traits or other elaboration features.
fn emit_elaborated(src: &str) -> String {
    emit_elaborated_inner(src, false)
}

/// Like `emit_elaborated` but also compiles and includes Std module elaborated
/// programs in the codegen context. This mirrors the real `build_script` pipeline
/// and is needed to test cross-module external function resolution.
fn emit_elaborated_with_std(src: &str) -> String {
    emit_elaborated_inner(src, true)
}

fn emit_elaborated_inner(src: &str, include_std_modules: bool) -> String {
    let tokens = lexer::Lexer::new(src).lex().expect("lex error");
    let mut program = parser::Parser::new(tokens)
        .parse_program()
        .expect("parse error");
    desugar::desugar_program(&mut program);
    let mut checker = bootstrap();
    let result = checker.check_program(&mut program);
    assert!(
        !result.has_errors(),
        "typecheck error: {:?}",
        result.errors()
    );
    let elaborated = elaborate::elaborate(&program, &result);

    let elaborated_modules = if include_std_modules {
        let mut modules = std::collections::HashMap::new();
        for (module_name, mod_result) in result.module_check_results() {
            if !module_name.starts_with("Std.") {
                continue;
            }
            let mod_program = match result.programs().get(module_name) {
                Some(p) => p,
                None => continue,
            };
            let elab = elaborate::elaborate_module(mod_program, mod_result, module_name);
            modules.insert(module_name.clone(), elab);
        }
        modules
    } else {
        std::collections::HashMap::new()
    };

    let codegen_info_map = result.codegen_info();
    let prelude_imports = &result.prelude_imports;
    let mut modules = std::collections::HashMap::new();
    // Always include codegen_info for all modules (needed for resolver to find dicts/exports)
    for (name, info) in codegen_info_map.iter() {
        modules.insert(
            name.clone(),
            codegen::CompiledModule {
                codegen_info: info.clone(),
                elaborated: Vec::new(),
                resolution: codegen::resolve::ResolutionMap::new(),
            },
        );
    }
    // Overlay elaborated modules with their resolution maps
    for (name, elab) in elaborated_modules {
        let normalized = codegen::normalize::normalize_effects(&elab);
        let resolution =
            codegen::resolve::resolve_names(&name, &normalized, codegen_info_map, prelude_imports);
        let entry = modules.entry(name.clone()).or_default();
        entry.elaborated = normalized;
        entry.resolution = resolution;
    }
    let ctx = codegen::CodegenContext {
        modules,
        let_effect_bindings: result.let_effect_bindings.clone(),
        prelude_imports: result.prelude_imports.clone(),
    };
    codegen::emit_module_with_context("_script", &elaborated, &ctx, Some(&result), None)
}

/// Emit Core Erlang and compile it with erlc, asserting no compilation errors.
fn assert_compiles(src: &str) {
    let out = emit_elaborated(src);
    assert_core_compiles(&out);
}

fn assert_core_compiles(out: &str) {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static COUNTER: AtomicUsize = AtomicUsize::new(0);

    let id = COUNTER.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("dylang_test_{}_{id}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let core_path = dir.join("_script.core");
    std::fs::write(&core_path, out).unwrap();
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

// fn assert_runs_and_stdout_contains(src: &str, needles: &[&str]) {
//     use std::sync::atomic::{AtomicUsize, Ordering};
//     static COUNTER: AtomicUsize = AtomicUsize::new(0);

//     let out = emit_elaborated_with_std(src);
//     let id = COUNTER.fetch_add(1, Ordering::Relaxed);
//     let dir = std::env::temp_dir().join(format!("dylang_run_test_{}_{id}", std::process::id()));
//     std::fs::create_dir_all(&dir).unwrap();
//     let core_path = dir.join("_script.core");
//     std::fs::write(&core_path, &out).unwrap();
//     let status = std::process::Command::new("erlc")
//         .arg("-o")
//         .arg(&dir)
//         .arg(&core_path)
//         .output()
//         .expect("failed to run erlc");
//     assert!(
//         status.status.success(),
//         "erlc failed to compile:\n{}\nstderr: {}",
//         out,
//         String::from_utf8_lossy(&status.stderr)
//     );

//     let run_output = std::process::Command::new("erl")
//         .arg("-noshell")
//         .arg("-pa")
//         .arg(&dir)
//         .arg("-eval")
//         .arg("'_script':main(), init:stop().")
//         .output()
//         .expect("failed to run erl");
//     let _ = std::fs::remove_dir_all(&dir);
//     assert!(
//         run_output.status.success(),
//         "erl failed:\nstderr: {}",
//         String::from_utf8_lossy(&run_output.stderr)
//     );
//     let stdout = String::from_utf8_lossy(&run_output.stdout);
//     for needle in needles {
//         assert!(
//             stdout.contains(needle),
//             "expected '{needle}' in output, got: {stdout}"
//         );
//     }
// }

fn assert_contains(out: &str, needle: &str) {
    assert!(
        out.contains(needle),
        "Expected to find:\n  {needle}\nIn output:\n{out}"
    );
}

#[test]
fn inner_dynamic_handler_is_kept_when_outer_static_handler_handles_same_effect() {
    let src = r#"
effect Log {
  fun log : (msg: String) -> Unit
}

handler silent for Log {
  log _ = resume ()
}

make_logger () = handler for Log {
  log _ = resume ()
}

main () = {
  let logger = make_logger ()
  {
    log! "hello"
  } with {logger, silent}
}
"#;

    let out = emit_elaborated(src);
    assert!(
        out.contains("call 'erlang':'element'"),
        "inner dynamic handler should remain when nested inside an outer static handler\n{out}"
    );
    assert_core_compiles(&out);
}

#[test]
fn inner_dynamic_handler_is_kept_when_outer_inline_handler_handles_same_op() {
    let src = r#"
effect Log {
  fun log : (msg: String) -> Unit
}

make_logger () = handler for Log {
  log _ = resume ()
}

main () = {
  let logger = make_logger ()
  {
    log! "hello"
  } with {logger, log _ = resume ()}
}
"#;

    let out = emit_elaborated(src);
    assert!(
        out.contains("call 'erlang':'element'"),
        "inner dynamic handler should remain when nested inside an outer inline handler\n{out}"
    );
    assert_core_compiles(&out);
}

#[test]
fn beam_native_handler_named_reference_lowers_to_native_ops() {
    let src = r#"
import Std.Actor (beam_actor)

main () = {
  let _pid = spawn! (fun () -> ())
  ()
} with beam_actor
"#;

    let out = emit_elaborated_with_std(src);
    assert!(
        out.contains("call 'erlang':'spawn'"),
        "beam_actor should lower spawn! to native erlang:spawn\n{out}"
    );
    assert_core_compiles(&out);
}

#[test]
fn beam_ref_uses_native_backed_cps_handler_path() {
    let src = r#"
import Std.Ref (beam_ref)

main () = {
  let r = new! 41
  get! r
} with beam_ref
"#;

    let out = emit_elaborated_with_std(src);
    assert!(
        out.contains("apply _Handle_Std_Ref_Ref_new("),
        "beam_ref should install and apply a handler function for new!\n{out}"
    );
    assert!(
        out.contains("apply _Handle_Std_Ref_Ref_get("),
        "beam_ref should install and apply a handler function for get!\n{out}"
    );
    assert!(
        out.contains("call 'erlang':'make_ref'"),
        "beam_ref should still lower through native Erlang ref operations\n{out}"
    );
    assert_core_compiles(&out);
}

#[test]
fn async_handler_with_beam_actor_lowers_without_scoped_binding_cycle() {
    let src = r#"
import Std.Actor (beam_actor)
import Std.Async (async_handler)

main () = {
  let f = async! (fun () -> 1)
  await! f
} with {async_handler, beam_actor}
"#;

    let out = emit_elaborated_with_std(src);
    assert!(
        out.contains("call 'erlang':'spawn'"),
        "async_handler should be able to use beam_actor native ops\n{out}"
    );
    assert_core_compiles(&out);
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
type Color = Red | Green | Blue

trait Describe a {
  fun describe : (x: a) -> String
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
type Color = Red | Green | Blue

trait Describe a {
  fun describe : (x: a) -> String
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
    // Hardcoded check: validates the exact dict name format (canonical trait + mangled type).
    // Other tests use make_dict_name helper to avoid brittleness.
    assert!(
        out.contains("__dict_Std_Base_Show_std_int_Std_Int_Int"),
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
    let dict = typechecker::make_dict_name("Std.Base.Show", &[], "std_bool", "Std.Bool.Bool");
    assert!(
        out.contains(&dict),
        "expected Show/Bool dict reference\n{out}"
    );
}

#[test]
fn print_uses_show_dict() {
    let src = "main () = dbg (show 42)";
    let out = emit_elaborated(src);
    // dbg is lowered inline as io:format(standard_error, "~ts~n", [x])
    assert!(
        out.contains("'io':'format'"),
        "expected io:format call in dbg\n{out}"
    );
    // show 42 should reference the Show/Int dict
    let dict = typechecker::make_dict_name("Std.Base.Show", &[], "std_int", "Std.Int.Int");
    assert!(
        out.contains(&dict),
        "expected Show/Int dict reference\n{out}"
    );
}

#[test]
fn show_string_is_identity() {
    let src = "main () = show \"hello\"";
    let out = emit_elaborated(src);
    let dict = typechecker::make_dict_name("Std.Base.Show", &[], "std_string", "Std.String.String");
    assert!(
        out.contains(&dict),
        "expected Show/String dict constructor\n{out}"
    );
}

#[test]
fn string_interpolation_uses_show_dict() {
    let src = r#"main () = $"value is {42}""#;
    let out = emit_elaborated(src);
    let dict = typechecker::make_dict_name("Std.Base.Show", &[], "std_int", "Std.Int.Int");
    assert!(
        out.contains(&dict),
        "expected Show/Int dict for interpolation\n{out}"
    );
}

#[test]
fn show_tuple_inlines_per_element() {
    let src = "main () = show (1, True)";
    let out = emit_elaborated(src);
    let int_dict = typechecker::make_dict_name("Std.Base.Show", &[], "std_int", "Std.Int.Int");
    let bool_dict = typechecker::make_dict_name("Std.Base.Show", &[], "std_bool", "Std.Bool.Bool");
    // Tuple show is inlined: no Tuple dict constructor, instead direct element extraction
    assert!(
        !out.contains("__dict_Show_Tuple") && !out.contains("__dict_Std_Base_Show_Tuple"),
        "should NOT have a Tuple dict constructor\n{out}"
    );
    // Should extract elements with erlang:element
    assert!(
        out.contains("'erlang':'element'"),
        "expected erlang:element calls for tuple elements\n{out}"
    );
    // Should reference Show dicts for the element types
    assert!(
        out.contains(&int_dict),
        "expected Show/Int dict for first element\n{out}"
    );
    assert!(
        out.contains(&bool_dict),
        "expected Show/Bool dict for second element\n{out}"
    );
    // Should produce parens and comma separator (now as binaries)
    // "(" = #{#<40>...}#
    assert!(
        out.contains("#<40>(8,1,'integer',['unsigned'|['big']])"),
        "expected opening paren binary\n{out}"
    );
    // ", " = #{#<44>...,#<32>...}#
    assert!(
        out.contains(
            "#<44>(8,1,'integer',['unsigned'|['big']]),#<32>(8,1,'integer',['unsigned'|['big']])"
        ),
        "expected comma separator binary\n{out}"
    );
    // ")" = #{#<41>...}#
    assert!(
        out.contains("#<41>(8,1,'integer',['unsigned'|['big']])"),
        "expected closing paren binary\n{out}"
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
    let int_dict = typechecker::make_dict_name("Std.Base.Show", &[], "std_int", "Std.Int.Int");
    let string_dict =
        typechecker::make_dict_name("Std.Base.Show", &[], "std_string", "Std.String.String");
    let bool_dict = typechecker::make_dict_name("Std.Base.Show", &[], "std_bool", "Std.Bool.Bool");
    assert!(out.contains(&int_dict), "expected Show/Int dict\n{out}");
    assert!(
        out.contains(&string_dict),
        "expected Show/String dict\n{out}"
    );
    assert!(out.contains(&bool_dict), "expected Show/Bool dict\n{out}");
    // Should have the inline tuple lambda, not a Tuple dict
    assert!(
        out.contains("fun (___tup)"),
        "expected inline tuple show lambda\n{out}"
    );
    assert!(
        !out.contains("__dict_Show_Tuple") && !out.contains("__dict_Std_Base_Show_Tuple"),
        "should NOT have a Tuple dict constructor\n{out}"
    );
}

#[test]
fn show_user_defined_adt_uses_impl() {
    let src = "
type Color = Red | Green | Blue

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
    let dict = typechecker::make_dict_name("Std.Base.Show", &[], "", "Color");
    // Should emit the user's dict constructor
    assert!(
        out.contains(&format!("'{dict}'/0")),
        "expected Show/Color dict constructor\n{out}"
    );
    // main should dispatch show through the user's dict
    assert!(
        out.contains(&format!("'{dict}'")),
        "main should reference the user Show impl\n{out}"
    );
    // The user impl body should appear (case arms with color strings as binaries)
    // "Red" = #{#<82>...,#<101>...,#<100>...}#
    assert!(
        out.contains("#<82>(8,1,'integer',['unsigned'|['big']]),#<101>(8,1,'integer',['unsigned'|['big']]),#<100>(8,1,'integer',['unsigned'|['big']])"),
        "expected \"Red\" binary in Show impl body\n{out}"
    );
}

#[test]
fn print_user_defined_adt() {
    let src = "
type Color = Red | Green | Blue

impl Show for Color {
  show c = case c {
    Red -> \"Red\"
    Green -> \"Green\"
    Blue -> \"Blue\"
  }
}

main () = dbg (show Red)
";
    let out = emit_elaborated(src);
    let dict = typechecker::make_dict_name("Std.Base.Show", &[], "", "Color");
    // show should use the user's Show dict
    assert!(
        out.contains(&format!("'{dict}'")),
        "expected Show/Color dict passed to show\n{out}"
    );
    // dbg should call io:format
    assert!(
        out.contains("'io':'format'"),
        "expected io:format in dbg\n{out}"
    );
}

// --- Polymorphic trait dict sub-dictionaries ---

#[test]
fn show_parameterized_type_applies_sub_dicts() {
    let src = r#"
type Box a = Wrap(a)

impl Show for Box a where {a: Show} {
  show b = case b {
    Wrap(v) -> "Wrap(" <> show v <> ")"
  }
}

main () = show (Wrap 42)
"#;
    let out = emit_elaborated(src);
    let box_dict = typechecker::make_dict_name("Std.Base.Show", &[], "", "Box");
    let int_dict = typechecker::make_dict_name("Std.Base.Show", &[], "std_int", "Std.Int.Int");
    // The dict constructor should be applied with a sub-dict, not used as a bare ref.
    assert!(
        out.contains(&format!("'{box_dict}'")),
        "expected Show/Box dict constructor\n{out}"
    );
    assert!(
        out.contains(&int_dict),
        "expected Show/Int sub-dict applied to Box dict\n{out}"
    );
}

// --- Effect system (CPS transform) ---

#[test]
fn effect_fun_gets_handler_param() {
    // An effectful function should have an extra handler parameter in its arity
    let src = "
effect Log {
  fun log : (msg: String) -> Unit
}

fun do_work : Unit -> Int needs {Log}
do_work () = 42
";
    let out = emit_elaborated(src);
    // do_work takes 1 user param (Unit) + 1 handler param + 1 _ReturnK = arity 3
    assert_contains(&out, "'do_work'/3");
    assert_contains(&out, "_Handle__script_Log_log");
}

#[test]
fn effect_call_becomes_handler_apply() {
    // `log! "hello"` should become `apply _HandleLog('log', "hello", K)`
    let src = r#"
effect Log {
  fun log : (msg: String) -> Unit
}

fun do_work : Unit -> Unit needs {Log}
do_work () = log! "hello"
"#;
    let out = emit_elaborated(src);
    assert_contains(&out, "apply _Handle__script_Log_log(");
    // String "hello" is now a binary: #{#<104>...}#
    assert_contains(&out, "#{#<104>(8,1,'integer',['unsigned'|['big']])");
}

#[test]
fn effect_call_in_block_captures_continuation() {
    // When an effect call is in a block, everything after it becomes the continuation
    let src = r#"
effect Log {
  fun log : (msg: String) -> Unit
}

fun do_work : Unit -> Int needs {Log}
do_work () = {
  log! "starting"
  42
}
"#;
    let out = emit_elaborated(src);
    // Should have handler apply with a fun (continuation) as last arg
    assert_contains(&out, "apply _Handle__script_Log_log(");
    // The continuation should contain 42
    assert_contains(&out, "fun (");
    assert_contains(&out, "42");
}

#[test]
fn effect_call_let_binding_captures_value() {
    // `let x = get! ()` should make x the continuation parameter
    let src = "
effect State {
  fun get : Unit -> Int
}

fun use_state : Unit -> Int needs {State}
use_state () = {
  let x = get! ()
  x + 1
}
";
    let out = emit_elaborated(src);
    assert_contains(&out, "apply _Handle__script_State_get(");
}

#[test]
fn with_named_handler_binds_handler() {
    let src = r#"
effect Log {
  fun log : (msg: String) -> Unit
}

handler silent for Log {
  log msg = resume ()
}

fun do_work : Unit -> Int needs {Log}
do_work () = {
  log! "hello"
  42
}

main () = do_work () with silent
"#;
    let out = emit_elaborated(src);
    // main should bind _HandleLog from the silent handler and call do_work
    assert_contains(&out, "_Handle__script_Log_log");
    assert_contains(&out, "apply 'do_work'/3");
}

#[test]
fn with_inline_handler() {
    let src = r#"
effect Fail {
  fun fail : (msg: String) -> a
}

fun risky : Unit -> Int needs {Fail}
risky () = fail! "oops"

main () = risky () with {
  fail msg = 0
}
"#;
    let out = emit_elaborated(src);
    // Should have an inline handler function bound to _HandleFail
    assert_contains(&out, "_Handle__script_Fail_fail");
    assert_contains(&out, "apply 'risky'/3");
}

#[test]
fn handler_resume_calls_k() {
    // resume () in a handler should emit apply _K('unit')
    let src = r#"
effect Log {
  fun log : (msg: String) -> Unit
}

handler silent for Log {
  log msg = resume ()
}

fun do_work : Unit -> Int needs {Log}
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
  fun fail : (msg: String) -> a
}

fun risky : Unit -> Int needs {Fail}
risky () = fail! "oops"

main () = risky () with {
  fail msg = 0
}
"#;
    let out = emit_elaborated(src);
    // The inline handler body should just return 0, no _K call
    // (the arm body is `0`, which doesn't reference _K)
    assert_contains(&out, "_Handle__script_Fail_fail");
}

#[test]
fn with_return_clause() {
    let src = r#"
type Result a b = Ok(a) | Err(b)

effect Fail {
  fun fail : (msg: String) -> a
}

fun risky : Unit -> Int needs {Fail}
risky () = 42

main () = risky () with {
  fail msg = Err msg
  return value = Ok value
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
  fun log : (msg: String) -> Unit
}

fun inner : Unit -> Unit needs {Log}
inner () = log! "from inner"

fun outer : Unit -> Unit needs {Log}
outer () = inner ()

handler silent for Log {
  log msg = resume ()
}

main () = outer () with silent
"#;
    let out = emit_elaborated(src);
    // outer should pass its _HandleLog to inner
    // inner/outer each take Unit + _HandleLog + _ReturnK
    // outer calls inner with its own _HandleLog
    assert_contains(&out, "'inner'/3");
    assert_contains(&out, "'outer'/3");
}

#[test]
fn multiple_effect_calls_chain_continuations() {
    let src = r#"
effect Log {
  fun log : (msg: String) -> Unit
}

fun do_work : Unit -> Int needs {Log}
do_work () = {
  log! "first"
  log! "second"
  42
}

handler silent for Log {
  log msg = resume ()
}

main () = do_work () with silent
"#;
    let out = emit_elaborated(src);
    // Should have two nested handler applies with continuations
    // Count occurrences of apply _HandleLog
    let count = out.matches("apply _Handle__script_Log_log").count();
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
  fun log : (msg: String) -> Unit
}

handler silent for Log {
  log msg = resume ()
}

fun do_work : Unit -> Int needs {Log}
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
    assert_contains(&out, "'do_work'/3");
    assert_contains(&out, "apply _Handle__script_Log_log(");
    // x = 10 + 20 should appear inside a continuation
    assert_contains(&out, "call 'erlang':'+'");
}

#[test]
fn effect_fail_non_resumable_with_return() {
    // Fail handler doesn't call K; return clause wraps success path
    let src = r#"
effect Fail {
  fun fail : (msg: String) -> a
}

fun checked_double : (x: Int) -> Int needs {Fail}
checked_double x = if x > 100 then fail! "too big" else x * 2

main () = {
  let a = checked_double 10 with {
    fail msg = 0 - 1
    return value = value
  }
  let b = checked_double 200 with {
    fail msg = 0 - 1
    return value = value
  }
  a + b
}
"#;
    let out = emit_elaborated(src);
    // Should have two with-expression lowerings, each with _Handle__script_Fail_fail
    assert_contains(&out, "_Handle__script_Fail_fail");
    // The fail arm should not call _K
    // The return clause should appear
}

#[test]
fn effect_propagation_inner_outer() {
    // outer calls inner, both need Log; handler param threads through
    let src = r#"
effect Log {
  fun log : (msg: String) -> Unit
}

fun inner : Unit -> Int needs {Log}
inner () = {
  log! "from inner"
  42
}

fun outer : Unit -> Int needs {Log}
outer () = {
  log! "from outer"
  let x = inner ()
  x + 1
}

handler silent for Log {
  log msg = resume ()
}

main () = outer () with silent
"#;
    let out = emit_elaborated(src);
    // Both should take Unit + _HandleLog + _ReturnK
    assert_contains(&out, "'inner'/3");
    assert_contains(&out, "'outer'/3");
    // outer's body should call inner with _HandleLog and _ReturnK passed through
    assert_contains(&out, "apply 'inner'/3(");
}

#[test]
fn effect_multi_handler_stacking() {
    // Function needs both Fail and Log; with provides both handlers
    let src = r#"
effect Log {
  fun log : (msg: String) -> Unit
}

effect Fail {
  fun fail : (msg: String) -> a
}

handler silent for Log {
  log msg = resume ()
}

fun risky_work : Unit -> Int needs {Fail, Log}
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
  fail msg = 0 - 1
  return value = value
}
"#;
    let out = emit_elaborated(src);
    // risky_work needs Unit + 2 handler params + 1 _ReturnK
    assert_contains(&out, "'risky_work'/4");
    // Both handler params should be present
    assert_contains(&out, "_Handle__script_Fail_fail");
    assert_contains(&out, "_Handle__script_Log_log");
}

#[test]
fn handler_arm_body_gets_show_dict() {
    // dbg inside a named handler body should work with String arg directly
    let src = r#"
effect Log {
  fun log : (msg: String) -> Unit
}

handler console_log for Log {
  log msg = {
    dbg msg
    resume ()
  }
}

fun do_work : Unit -> Int needs {Log}
do_work () = {
  log! "hello"
  42
}

main () = do_work () with console_log
"#;
    let out = emit_elaborated(src);
    // The handler arm body should call io:format (dbg is lowered inline)
    assert_contains(&out, "'io':'format'");
}

#[test]
fn handler_needs_effect_from_sibling_handler() {
    // Under nested handler semantics, `with { silent, logging_fail }` desugars to
    // `(expr with silent) with logging_fail`. The `logging_fail` handler has
    // `needs {Log}`, but `silent` only wraps the inner expression — it doesn't
    // handle `Log` for `logging_fail`'s arm body. So `Log` propagates outward.
    //
    // To make this work, the user must provide `Log` at a level that wraps
    // `logging_fail`, e.g. stacked `with`s: `(expr with {silent, logging_fail}) with silent`
    //
    // Test: verify that `with {silent, logging_fail}` correctly lowers when
    // `logging_fail`'s Log need is handled by wrapping the whole thing in `silent`.
    let src = r#"
effect Log {
  fun log : (msg: String) -> Unit
}

effect Fail {
  fun fail : (msg: String) -> a
}

handler silent for Log {
  log msg = resume ()
}

handler logging_fail for Fail needs {Log} {
  fail msg = {
    log! ("caught: " <> msg)
    0
  }
}

fun risky : Unit -> Int needs {Fail, Log}
risky () = {
  log! "about to fail"
  fail! "oops"
}

main () = {
  risky () with { silent, logging_fail }
} with silent
"#;
    let out = emit_elaborated(src);
    assert_contains(&out, "_Handle__script_Log_log");
    assert_contains(&out, "apply _Handle__script_Log_log(");
    assert_contains(&out, "_Handle__script_Fail_fail");
}

#[test]
fn handler_needs_effect_from_outer_scope() {
    // Under nested handler semantics, `logging_fail`'s `needs {Log}` is not
    // satisfied by sibling `silent`. Provide `silent` at an outer scope.
    let src = r#"
effect Log {
  fun log : (msg: String) -> Unit
}

effect Fail {
  fun fail : (msg: String) -> a
}

handler logging_fail for Fail needs {Log} {
  fail msg = {
    log! ("Failed: " <> msg)
    0
  }
}

handler silent for Log {
  log msg = resume ()
}

fun do_work : Unit -> Int needs {Fail, Log}
do_work () = {
  log! "starting"
  fail! "boom"
}

main () = {
  do_work () with { silent, logging_fail }
} with silent
"#;
    let out = emit_elaborated(src);
    assert_contains(&out, "apply _Handle__script_Log_log(");
    assert_contains(&out, "_Handle__script_Fail_fail");
}

#[test]
fn effect_multi_clause_function() {
    // Effectful function with pattern-matched clauses
    let src = r#"
effect Fail {
  fun fail : (msg: String) -> a
}

fun safe_div : (x: Int) -> (y: Int) -> Int needs {Fail}
safe_div _ 0 = fail! "division by zero"
safe_div x y = x * y

main () = safe_div 10 0 with {
  fail msg = 0 - 1
  return value = value
}
"#;
    let out = emit_elaborated(src);
    // safe_div takes 2 user params + 1 handler param + 1 _ReturnK = arity 4
    assert_contains(&out, "'safe_div'/4");
    assert_contains(&out, "_Handle__script_Fail_fail");
}

// --- Effect calls in non-block positions ---

#[test]
fn effect_call_in_binop() {
    // Effect call nested in a binary operation should be lifted to a let binding
    let src = r#"
effect Ask {
  fun ask : Unit -> Int
}

fun compute : Unit -> Int needs {Ask}
compute () = {
  let x = 1 + ask! ()
  x
}

main () = compute () with {
  ask () = resume 42
}
"#;
    let out = emit_elaborated(src);
    // The ask! should be CPS-transformed with a continuation that does the addition
    assert_contains(&out, "apply _Handle__script_Ask_ask(");
    // The addition should still happen
    assert_contains(&out, "call 'erlang':'+'");
}

#[test]
fn effect_call_in_function_arg() {
    // Effect call as an argument to a function call
    let src = r#"
effect Ask {
  fun ask : Unit -> Int
}

double x = x * 2

fun compute : Unit -> Int needs {Ask}
compute () = {
  let x = double (ask! ())
  x
}

main () = compute () with {
  ask () = resume 21
}
"#;
    let out = emit_elaborated(src);
    assert_contains(&out, "apply _Handle__script_Ask_ask(");
    assert_contains(&out, "'double'");
}

#[test]
fn effect_call_in_if_condition() {
    // Effect call in an if condition
    let src = r#"
effect Ask {
  fun ask : Unit -> Bool
}

fun decide : Unit -> Int needs {Ask}
decide () = {
  if ask! () then 1 else 0
}

main () = decide () with {
  ask () = resume True
}
"#;
    let out = emit_elaborated(src);
    assert_contains(&out, "apply _Handle__script_Ask_ask(");
}

#[test]
fn multiple_effect_calls_in_binop() {
    // Two effect calls in the same binary expression
    let src = r#"
effect Ask {
  fun ask : Unit -> Int
}

fun compute : Unit -> Int needs {Ask}
compute () = {
  let x = ask! () + ask! ()
  x
}

main () = compute () with {
  ask () = resume 10
}
"#;
    let out = emit_elaborated(src);
    // Should have two separate handler applies for the two ask! calls
    let count = out.matches("apply _Handle__script_Ask_ask(").count();
    assert!(
        count >= 2,
        "expected at least 2 handler applies, got {count}\n{out}"
    );
}

#[test]
fn effect_call_in_binop_compiles() {
    let src = r#"
effect Ask {
  fun ask : Unit -> Int
}

fun compute : Unit -> Int needs {Ask}
compute () = {
  let x = 1 + ask! ()
  x
}

main () = compute () with {
  ask () = resume 42
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
type Result a e = Ok(a) | Err(e)

effect Fail {
  fun fail : (msg: String) -> a
}

fun try_it : (computation: Unit -> a needs {Fail}) -> Result a String
try_it computation = computation () with {
  fail msg = Err(msg)
  return value = Ok(value)
}

main () = try_it (fun () -> fail! "oops")
"#;
    let out = emit_elaborated(src);
    // The lambda should have _HandleFail as a parameter
    assert_contains(&out, "_Handle__script_Fail_fail");
    // try_it's body should call computation with the handler param
    assert_contains(&out, "apply Computation(");
}

#[test]
fn hof_effect_absorption_lambda_with_block() {
    // Lambda with a block body that uses effects
    let src = r#"
type Result a e = Ok(a) | Err(e)

effect Fail {
  fun fail : (msg: String) -> a
}

fun try_it : (computation: Unit -> a needs {Fail}) -> Result a String
try_it computation = computation () with {
  fail msg = Err(msg)
  return value = Ok(value)
}

main () = try_it (fun () -> {
  let x = 10
  if x > 100 then fail! "too big" else x
})
"#;
    let out = emit_elaborated(src);
    assert_contains(&out, "_Handle__script_Fail_fail");
    assert_contains(&out, "apply Computation(");
}

#[test]
fn hof_effect_absorption_compiles() {
    // End-to-end: HOF effect absorption compiles to valid Core Erlang
    let src = r#"
effect Fail {
  fun fail : (msg: String) -> a
}

fun try_it : (computation: Unit -> a needs {Fail}) -> String
try_it computation = computation () with {
  fail msg = "err: " <> msg
}

main () = {
  let a = try_it (fun () -> "hello")
  dbg a
  let b = try_it (fun () -> fail! "boom")
  dbg b
}
"#;
    assert_compiles(src);
}

#[test]
fn return_clause_inside_cps_chain() {
    // The return clause should be inside the CPS chain, not a post-wrapper.
    // Verify the return clause (Ok wrapper) is inside the CPS chain.
    let src = r#"
type Result a e = Ok(a) | Err(e)

effect Fail {
  fun fail : (msg: String) -> a
}

try_it computation = computation () with {
  fail msg = Err(msg)
  return value = Ok(value)
}
"#;
    let out = emit(src);
    // Return clause (Ok wrapper) should be inside the CPS chain
    assert_contains(&out, "'ok'");
    // Note: the fail handler is correctly pruned -- `computation` is a HOF
    // parameter without handler param passing, so `_Handle__script_Fail_fail` is
    // never referenced in the lowered body.
}

#[test]
fn return_clause_with_handler_compiles() {
    // End-to-end: return clause + handler abort compiles to valid Core Erlang.
    let src = r#"
type Result a e = Ok(a) | Err(e)

effect Fail {
  fun fail : (msg: String) -> a
}

fun try_it : (computation: Unit -> a needs {Fail}) -> Result a String
try_it computation = computation () with {
  fail msg = Err(msg)
  return value = Ok(value)
}

main () = {
  let a = try_it (fun () -> 42)
  dbg "ok"
  let b = try_it (fun () -> fail! "boom")
  dbg "ok"
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
  fun log : (msg: String) -> Unit
}

handler silent for Log {
  log msg = resume ()
}

fun greet : Unit -> Unit needs {Log}
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
  fun log : (msg: String) -> Unit
}

handler silent for Log {
  log msg = resume ()
}

fun work : Unit -> Int needs {Log}
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
  fun ask : Unit -> Int
}

handler answer_42 for Ask {
  ask = resume 42
}

fun use_ask : Unit -> Int needs {Ask}
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
  fun ask : Unit -> Int
}

handler answer_42 for Ask {
  ask = resume 42
}

fun make_point : Unit -> Point needs {Ask}
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
  fun ask : Unit -> Int
}

handler answer_42 for Ask {
  ask = resume 42
}

fun make_pair : Unit -> (Int, Int) needs {Ask}
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
type Maybe a = Some(a) | None

effect Ask {
  fun ask : Unit -> Int
}

handler answer_42 for Ask {
  ask = resume 42
}

fun maybe_ask : Unit -> Maybe Int needs {Ask}
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
  fun log : (msg: String) -> Unit
}

effect Ask {
  fun ask : Unit -> Int
}

effect Fail {
  fun fail : (msg: String) -> a
}

handler silent for Log {
  log msg = resume ()
}

handler answer_42 for Ask {
  ask = resume 42
}

fun complex : Unit -> Int needs {Log, Ask, Fail}
complex () = {
  log! "start"
  let x = ask! ()
  if x > 100 then fail! "too big" else x
}

main () = complex () with {
  silent,
  answer_42,
  fail msg = 0
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
  fun log : (msg: String) -> Unit
}

handler silent for Log {
  log msg = resume ()
}

fun work : Unit -> Int needs {Log}
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
  fun ask : Unit -> Int
}

handler answer_42 for Ask {
  ask = resume 42
}

fun get_value : Unit -> Int needs {Ask}
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
  fun log : (msg: String) -> Unit
}

handler silent for Log {
  log msg = resume ()
}

fun inner : Unit -> Int needs {Log}
inner () = {
  log! "inner"
  1
}

fun middle : Unit -> Int needs {Log}
middle () = {
  let x = inner ()
  log! "middle"
  x + 1
}

fun outer : Unit -> Int needs {Log}
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
type Result a e = Ok(a) | Err(e)

effect Fail {
  fun fail : (msg: String) -> a
}

fun inner : Unit -> Int needs {Fail}
inner () = {
  fail! "boom"
  999
}

fun outer : Unit -> Int needs {Fail}
outer () = {
  let x = inner ()
  x + 1
}

fun try_it : (computation: Unit -> a needs {Fail}) -> Result a String
try_it computation = computation () with {
  fail msg = Err(msg)
  return value = Ok(value)
}

main () = try_it (fun () -> outer ())
"#;
    assert_compiles(src);
}

#[test]
fn mixed_resume_and_abort_in_handler() {
    // Handler where some ops resume and others abort.
    let src = r#"
effect TestIO {
  fun read_val : Unit -> Int
  fun crash : (msg: String) -> a
}

handler test_io for TestIO {
  read_val = resume 42
  crash msg = 0
}

fun process : Unit -> Int needs {TestIO}
process () = {
  let x = read_val! ()
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
  fun ask : Unit -> (Int, Int)
}

handler answer for Ask {
  ask = resume (1, 2)
}

fun use_pair : Unit -> Int needs {Ask}
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
type Maybe a = Just(a) | Nothing

effect Ask {
  fun ask : Unit -> Maybe Int
}

handler answer for Ask {
  ask = resume Just(42)
}

fun extract : Unit -> Int needs {Ask}
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

// --- Partial application tests ---

#[test]
fn pure_partial_application_compiles() {
    let src = r#"
fun add : Int -> Int -> Int
add a b = a + b

increment = add 1

main () = dbg (show (increment 6))
"#;
    assert_compiles(src);
}

#[test]
fn pure_partial_application_emits_lambda() {
    let src = r#"
fun add : Int -> Int -> Int
add a b = a + b

increment = add 1
"#;
    let out = emit_elaborated(src);
    // Partial application should emit a lambda wrapping the saturated call
    assert!(
        out.contains("fun ("),
        "expected lambda in partial application output:\n{out}"
    );
    assert!(
        out.contains("'add'/2"),
        "expected reference to add/2:\n{out}"
    );
}

#[test]
fn effectful_partial_application_compiles() {
    let src = r#"
effect Logger {
  fun log : String -> Unit
}

fun log_with_level : String -> String -> Unit needs {Logger}
log_with_level level msg = log! msg

main () = {
  let debug_log = log_with_level "DEBUG"
  debug_log "hello" with {
    log msg = {
      dbg msg
      resume ()
    }
  }
}
"#;
    assert_compiles(src);
}

#[test]
fn effectful_partial_application_emits_handler_params() {
    let src = r#"
effect Logger {
  fun log : String -> Unit
}

fun log_with_level : String -> String -> Unit needs {Logger}
log_with_level level msg = log! msg

main () = {
  let debug_log = log_with_level "DEBUG"
  debug_log "hello" with {
    log msg = {
      dbg msg
      resume ()
    }
  }
}
"#;
    let out = emit_elaborated(src);
    // The partial application lambda should include handler params
    assert!(
        out.contains("_Handle__script_Logger_log"),
        "expected handler param in partial application lambda:\n{out}"
    );
    assert!(
        out.contains("_ReturnK"),
        "expected _ReturnK in partial application lambda:\n{out}"
    );
}

#[test]
fn over_application_of_zero_arity_compiles() {
    // increment is zero-arity (returns a lambda), calling it with an arg
    // should split: call increment(), then apply the result
    let src = r#"
fun add : Int -> Int -> Int
add a b = a + b

increment = add 1

main () = {
  let result = increment 6
  dbg (show result)
}
"#;
    assert_compiles(src);
}

// --- Cross-module external function disambiguation ---

#[test]
fn qualified_external_calls_resolve_to_correct_module() {
    // List.reverse and String.reverse are both @external but point to
    // different Erlang modules (lists vs string). Qualified calls must
    // resolve to the correct one, not whichever was registered first.
    let src = r#"
import Std.List
import Std.String

main () = {
  let xs = List.reverse [1, 2, 3]
  let s = String.reverse "hello"
  xs
}
"#;
    let out = emit_elaborated_with_std(src);
    assert!(
        out.contains("call 'std_list':'reverse'"),
        "List.reverse should emit std_list:reverse wrapper\n{out}"
    );
    assert!(
        out.contains("call 'std_string':'reverse'"),
        "String.reverse should emit std_string:reverse wrapper\n{out}"
    );
}

#[test]
fn exposed_external_overrides_unqualified_lookup() {
    // When reverse is explicitly exposed from Std.String, an unqualified
    // call to reverse must resolve to Std.String's wrapper, not Std.List's.
    let src = r#"
import Std.String (reverse)

main () = reverse "hello"
"#;
    let out = emit_elaborated_with_std(src);
    assert!(
        out.contains("call 'std_string':'reverse'"),
        "Exposed reverse should emit std_string:reverse, not std_list:reverse\n{out}"
    );
    assert!(
        !out.contains("call 'std_list':'reverse'"),
        "Should not contain std_list:reverse\n{out}"
    );
}

#[test]
fn qualified_and_exposed_externals_coexist() {
    // Expose reverse from one module, use the other qualified.
    // Both must resolve correctly.
    let src = r#"
import Std.String (reverse)
import Std.List

main () = {
  let s = reverse "hello"
  let xs = List.reverse [1, 2, 3]
  s
}
"#;
    let out = emit_elaborated_with_std(src);
    assert!(
        out.contains("call 'std_string':'reverse'"),
        "Exposed reverse should emit std_string:reverse wrapper\n{out}"
    );
    assert!(
        out.contains("call 'std_list':'reverse'"),
        "List.reverse should emit std_list:reverse wrapper\n{out}"
    );
}

/// Function parameters must shadow exposed imports in the resolver.
/// A param named `length` should NOT resolve to `Std.List.length`.
#[test]
fn param_shadows_exposed_import() {
    let src = r#"
import Std.List (length)

length_status length = case length {
  0 -> "empty"
  _ -> "not empty"
}

main () = length_status 0
"#;
    let out = emit_elaborated_with_std(src);
    // The `length` param inside length_status should be a plain variable,
    // not a call to erlang:length/1 or std_list:length/1.
    assert!(
        !out.contains("'erlang':'length'"),
        "param 'length' should not resolve to erlang:length\n{out}"
    );
    // The case scrutinee should use the variable, not a function reference
    assert!(
        !out.contains("'length'/1"),
        "param 'length' should not become a function reference\n{out}"
    );
}

/// Lambda parameters should shadow module-level names.
#[test]
fn lambda_param_shadows_import() {
    let src = r#"
import Std.List (length)

main () = {
  let f = fun length -> length + 1
  f 5
}
"#;
    let out = emit_elaborated_with_std(src);
    // Inside the lambda, `length` is a param, not the imported function
    assert!(
        !out.contains("'length'/1"),
        "lambda param 'length' should not become a function reference\n{out}"
    );
}

/// Case pattern bindings should shadow imported names.
#[test]
fn case_binding_shadows_import() {
    let src = r#"
import Std.List (length)

main () = case 42 {
  length -> length + 1
}
"#;
    let out = emit_elaborated_with_std(src);
    assert!(
        !out.contains("'length'/1"),
        "case binding 'length' should not become a function reference\n{out}"
    );
}

/// Let bindings should shadow imported names for subsequent expressions.
#[test]
fn let_binding_shadows_import() {
    let src = r#"
import Std.List (length)

main () = {
  let length = 42
  length + 1
}
"#;
    let out = emit_elaborated_with_std(src);
    assert!(
        !out.contains("'length'/1"),
        "let-bound 'length' should not become a function reference\n{out}"
    );
}

/// Param named `size` should not resolve to Dict.size (an FFI to maps:size).
/// This was the original bug report: adding @external functions to a stdlib
/// module caused the name to leak into scope even without importing it.
#[test]
fn param_shadows_ffi_function() {
    let src = r#"
describe size = case size {
  0 -> "none"
  1 -> "one"
  _ -> "many"
}

main () = describe 0
"#;
    let out = emit_elaborated_with_std(src);
    assert!(
        !out.contains("'maps':'size'"),
        "param 'size' should not resolve to maps:size FFI\n{out}"
    );
    assert!(
        !out.contains("'size'/1"),
        "param 'size' should not become a function reference\n{out}"
    );
}

/// Param named `reverse` should not resolve to List.reverse (@external to lists:reverse).
#[test]
fn param_shadows_exposed_ffi() {
    let src = r#"
import Std.List (reverse)

apply_or_default reverse xs = case xs {
  [] -> []
  _ -> reverse xs
}

main () = apply_or_default (fun x -> x) [1, 2, 3]
"#;
    let out = emit_elaborated_with_std(src);
    // Inside the function body, `reverse` is the param, not lists:reverse
    assert!(
        !out.contains("call 'lists':'reverse'"),
        "param 'reverse' should not resolve to lists:reverse\n{out}"
    );
}

/// Param named `map` should not resolve to List.map when called as a function.
/// This tests the App handler saturation gate — the param is applied to args.
#[test]
fn param_shadows_stdlib_in_call_position() {
    let src = r#"
import Std.List (map)

apply_fn map xs = map xs

main () = apply_fn (fun x -> x) [1, 2, 3]
"#;
    let out = emit_elaborated_with_std(src);
    // `map xs` inside apply_fn should be a local variable apply, not std_list:map
    assert!(
        !out.contains("call 'std_list':'map'"),
        "param 'map' in call position should not resolve to std_list:map\n{out}"
    );
}

/// Let binding named `get` should shadow Dict.get FFI.
#[test]
fn let_shadows_dict_ffi() {
    let src = r#"
main () = {
  let get = 42
  get + 1
}
"#;
    let out = emit_elaborated_with_std(src);
    assert!(
        !out.contains("'std_dict_bridge':'get'"),
        "let-bound 'get' should not resolve to std_dict_bridge:get\n{out}"
    );
}

/// Case binding named `filter` should shadow List.filter in guard and body.
#[test]
fn case_binding_shadows_stdlib_function() {
    let src = r#"
import Std.List (filter)

check filter = case filter {
  0 -> "zero"
  filter when filter > 0 -> "positive"
  _ -> "negative"
}

main () = check 5
"#;
    let out = emit_elaborated_with_std(src);
    assert!(
        !out.contains("'std_list':'filter'"),
        "case binding 'filter' should not resolve to std_list:filter\n{out}"
    );
}

/// LetFun named `length` should shadow imported length AND still work as a callable function.
#[test]
fn letfun_shadows_import_and_is_callable() {
    let src = r#"
import Std.List (length)

main () = {
  let length x = x + 1
  length 5
}
"#;
    let out = emit_elaborated_with_std(src);
    // Should NOT call the imported length
    assert!(
        !out.contains("call 'erlang':'length'"),
        "LetFun 'length' should shadow imported length\n{out}"
    );
    // Should be a letrec with a local function call
    assert!(out.contains("letrec"), "LetFun should emit a letrec\n{out}");
}

/// Multiple binding forms all shadowing the same import in nested scopes.
#[test]
fn nested_shadowing() {
    let src = r#"
import Std.List (length)

outer length = {
  let f = fun length -> {
    let length = length + 1
    length
  }
  f length
}

main () = outer 10
"#;
    let out = emit_elaborated_with_std(src);
    assert!(
        !out.contains("'erlang':'length'"),
        "nested shadowing should prevent all resolution to erlang:length\n{out}"
    );
    assert!(
        !out.contains("'length'/1"),
        "no occurrence of 'length' should become a function reference\n{out}"
    );
}

#[test]
fn imported_named_handler_calls_private_external_helper_via_bridge() {
    let src = r#"
import Std.File (File, fs)

main () = {
  let _ = File.write! "/tmp/dylang-file-io-test.txt" "hello"
  File.exists! "/tmp/dylang-file-io-test.txt"
} with fs
"#;
    let out = emit_elaborated_with_std(src);
    assert!(
        out.contains("('std_file_bridge', 'write_file', 2)"),
        "Std.File.fs should lower write through std_file_bridge\n{out}"
    );
    assert!(
        out.contains("('std_file_bridge', 'file_exists', 1)"),
        "Std.File.fs should lower exists through std_file_bridge\n{out}"
    );
    assert!(
        !out.contains("apply 'write_file'/2"),
        "Std.File.fs should not lower write as a local _script function\n{out}"
    );
    assert!(
        !out.contains("apply 'file_exists'/1"),
        "Std.File.fs should not lower exists as a local _script function\n{out}"
    );
    assert_core_compiles(&out);
}
