use saga::{codegen, desugar, elaborate, lexer, parser, typechecker};

/// Load prelude (which imports Std + stdlib) into a checker.
fn bootstrap() -> typechecker::Checker {
    let mut checker = typechecker::Checker::new();
    let prelude_src = include_str!("../src/stdlib/prelude.saga");
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
    emit_elaborated(src)
}

/// Parse, typecheck, elaborate, then emit Core Erlang.
/// Use this for tests that involve traits or other elaboration features.
fn emit_elaborated(src: &str) -> String {
    emit_elaborated_inner(src, false)
}

fn emit_elaborated_entry(src: &str) -> String {
    emit_elaborated_inner_with_entry(src, false, Some("main"))
}

/// Like `emit_elaborated` but also compiles and includes Std module elaborated
/// programs in the codegen context. This mirrors the real `build_script` pipeline
/// and is needed to test cross-module external function resolution.
fn emit_elaborated_with_std(src: &str) -> String {
    emit_elaborated_inner(src, true)
}

fn emit_elaborated_inner(src: &str, include_std_modules: bool) -> String {
    emit_elaborated_inner_with_entry(src, include_std_modules, None)
}

fn emit_elaborated_inner_with_entry(
    src: &str,
    include_std_modules: bool,
    entry_export: Option<&str>,
) -> String {
    let tokens = lexer::Lexer::new(src).lex().expect("lex error");
    let mut program = parser::Parser::new(tokens)
        .parse_program()
        .expect("parse error");
    desugar::desugar_program(&mut program);
    let imported = saga::derive::collect_imported_decls(&program, None);
    let _ = saga::derive::expand_derives(&mut program, &imported);
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
                front_resolution: Default::default(),
            },
        );
    }
    // Overlay elaborated modules with their resolution maps. Keep these in the
    // same raw elaborated form as the real new-path pipeline; normalization is
    // old-lowerer input and changes the shape the monadic translator expects.
    for (name, elab) in elaborated_modules {
        let front_resolution = result
            .module_check_results()
            .get(&name)
            .map(|m| m.resolution.clone())
            .unwrap_or_default();
        let resolution = codegen::resolve::resolve_names(
            &name,
            &elab,
            codegen_info_map,
            prelude_imports,
            &front_resolution,
        );
        let entry = modules.entry(name.clone()).or_default();
        entry.elaborated = elab;
        entry.resolution = resolution;
        entry.front_resolution = front_resolution;
    }
    let ctx = codegen::CodegenContext {
        modules,
        let_effect_bindings: result.let_effect_bindings.clone(),
        prelude_imports: result.prelude_imports.clone(),
    };
    codegen::emit_module_with_context("_script", &elaborated, &ctx, &result, None, entry_export)
}

/// Emit Core Erlang and compile it with erlc, asserting no compilation errors.
fn assert_compiles(src: &str) {
    let out = emit_elaborated_entry(src);
    assert_core_compiles(&out);
}

fn assert_core_compiles(out: &str) {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static COUNTER: AtomicUsize = AtomicUsize::new(0);

    let id = COUNTER.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("saga_test_{}_{id}", std::process::id()));
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

/// Compile the Phase 1 evidence bridge module into `dir` so tests that
/// emit `std_evidence_bridge:*` calls (every `with`-boundary in 3b) can
/// resolve them at runtime.
fn compile_evidence_bridge_into(dir: &std::path::Path) {
    let bridge_src = include_str!("../src/stdlib/evidence.bridge.erl");
    let bridge_path = dir.join("std_evidence_bridge.erl");
    std::fs::write(&bridge_path, bridge_src).unwrap();
    let status = std::process::Command::new("erlc")
        .arg("-o")
        .arg(dir)
        .arg(&bridge_path)
        .output()
        .expect("failed to run erlc on evidence bridge");
    assert!(
        status.status.success(),
        "erlc failed on evidence bridge:\n{}",
        String::from_utf8_lossy(&status.stderr)
    );
}

fn assert_runs_and_stdout_contains(src: &str, needles: &[&str]) {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static COUNTER: AtomicUsize = AtomicUsize::new(0);

    let out = emit_elaborated_entry(src);
    let id = COUNTER.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("saga_run_test_{}_{id}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let core_path = dir.join("_script.core");
    std::fs::write(&core_path, &out).unwrap();
    let status = std::process::Command::new("erlc")
        .arg("-o")
        .arg(&dir)
        .arg(&core_path)
        .output()
        .expect("failed to run erlc");
    assert!(
        status.status.success(),
        "erlc failed to compile:\n{}\nstderr: {}",
        out,
        String::from_utf8_lossy(&status.stderr)
    );
    compile_evidence_bridge_into(&dir);

    let eval = if out.contains("'main'/3") {
        "Ev = case erlang:function_exported('_script', '__saga_initial_evidence', 0) of true -> '_script':'__saga_initial_evidence'(); false -> {} end, K = fun(V) -> V end, io:format(\"~p~n\", ['_script':main(unit, Ev, K)]), init:stop()."
    } else if out.contains("'main'/1") {
        "io:format(\"~p~n\", ['_script':main(unit)]), init:stop()."
    } else {
        "io:format(\"~p~n\", ['_script':main()]), init:stop()."
    };

    let run_output = std::process::Command::new("erl")
        .arg("-noshell")
        .arg("-pa")
        .arg(&dir)
        .arg("-eval")
        .arg(eval)
        .output()
        .expect("failed to run erl");
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        run_output.status.success(),
        "erl failed:\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&run_output.stdout),
        String::from_utf8_lossy(&run_output.stderr)
    );
    let stdout = String::from_utf8_lossy(&run_output.stdout);
    for needle in needles {
        assert!(
            stdout.contains(needle),
            "expected '{needle}' in output, got: {stdout}"
        );
    }
}

fn assert_contains(out: &str, needle: &str) {
    assert!(
        out.contains(needle),
        "Expected to find:\n  {needle}\nIn output:\n{out}"
    );
}

#[test]
fn let_bound_inner_handler_wins_over_outer_static_handler() {
    let src = r#"
effect Choose {
  fun get : Unit -> Int
}

handler outer for Choose {
  get () = resume 1
}

make_handler () = handler for Choose {
  get () = resume 2
}

main () = {
  let h = make_handler ()
  {
    get! ()
  } with {h, outer}
}
"#;

    assert_runs_and_stdout_contains(src, &["2"]);
}

#[test]
fn effectful_callback_forwarded_through_wrapper_runs() {
    let src = r#"
effect Inner {
  fun ping : Unit -> Int
}

effect Outer {
  fun wrap : (Unit -> Int needs {Inner}) -> Int
}

handler answer_inner for Inner {
  ping () = {
    resume 41
  }
}

handler my_wrap for Outer needs {Inner} {
  wrap f = {
    let value = f ()
    resume (value + 1)
  }
}

fun call_wrap : (Unit -> Int needs {Inner}) -> Int needs {Outer}
call_wrap f = wrap! f

main () = {
  call_wrap (fun () -> ping! ())
} with {my_wrap, answer_inner}
"#;

    assert_runs_and_stdout_contains(src, &["42"]);
}

#[test]
fn effectful_lambda_packed_in_adt_constructor_runs() {
    // Regression: a lambda with effects stored inside an ADT constructor
    // arg used to be lowered as a pure 1-arg closure (no handler params,
    // no _ReturnK), because lower_ctor didn't thread expected field types
    // into arg lowering. At the call site `producer () with h`, BEAM threw
    // badarity. Also, case-arm-bound effectful values weren't registered
    // in current_effectful_vars, so applications didn't CPS-expand.
    let src = r#"
effect Chunked {
  fun write_chunk : Int -> Unit
}

type ResponseBody =
  | Streamed (Unit -> Unit needs {Chunked})

fun chunked_handler : Unit -> Handler Chunked
chunked_handler () = handler for Chunked {
  write_chunk _n = resume ()
}

fun make_response : Unit -> ResponseBody
make_response () = Streamed (fun () -> {
  write_chunk! 1
  write_chunk! 2
})

fun run_response : ResponseBody -> Int
run_response resp = case resp {
  Streamed producer -> {
    let h = chunked_handler ()
    producer () with h
    99
  }
}

main () = run_response (make_response ())
"#;

    assert_runs_and_stdout_contains(src, &["99"]);
}

#[test]
fn case_arm_in_k_threaded_block_registers_effectful_var_and_handler_binding() {
    // Regression: when a case match on an ADT-packed effectful lambda lives
    // inside a K-threaded block (i.e., the case arm body is lowered via
    // `lower_block_with_k`/`ExprKind::Case` in K-threaded mode rather than
    // the return-K block path), the lowerer would (1) skip registering the
    // arm-bound `producer` in `current_effectful_vars` and (2) skip handler
    // registration for `let h = factory ()`. This caused either a runtime
    // arity mismatch (only 1 arg passed to a CPS-shaped lambda) or an ICE
    // about an unknown handler item 'h'.
    //
    // The test framework triggers this in real code: `test "name"` takes
    // an effectful lambda whose body holds the case match.
    let src = r#"
effect Chunked {
  fun write_chunk : Int -> Unit
}

effect Wrap {
  fun wrap : (Unit -> Int needs {Chunked}) -> Int
}

type Body =
  | Streamed (Unit -> Unit needs {Chunked})

fun mk : (Unit -> Unit needs {Chunked}) -> Body
mk producer = Streamed producer

fun named : Unit -> Handler Chunked
named () = handler for Chunked {
  write_chunk _ = resume ()
}

# wrapped_run is effectful (`needs {Wrap}`), so its body lowers in
# K-threaded mode. The case arm exercises both fixed paths.
fun wrapped_run : Unit -> Int needs {Wrap}
wrapped_run () = {
  let body = mk (fun () -> write_chunk! 1)
  case body {
    Streamed producer -> {
      let h = named ()
      let _ = producer () with h
      55
    }
  }
}

handler wrap_h for Wrap {
  wrap _ = resume 0
}

main () = wrapped_run () with wrap_h
"#;

    assert_runs_and_stdout_contains(src, &["55"]);
}

#[test]
fn handler_factory_let_binding_runs_return_clause() {
    // Regression: `let h = make_handler ()` registered the handler info in
    // the typechecker's `self.handlers["h"]`, but the per-clause save/restore
    // at check_decl.rs (around `saved_handlers = self.handlers.clone()`)
    // wiped the entry before the lowerer saw it. As a result, the lowerer
    // built the dynamic NamedHandlerItem with `has_return = false` and emitted
    // the identity `_ReturnK` instead of the handler's return-clause lambda.
    //
    // Now the typechecker also stores let-binding handler info in a persistent
    // map keyed by the pattern's NodeId, which the lowerer consults.
    let src = r#"
effect Chunked {
  fun write_chunk : Int -> Unit
}

type Body =
  | Streamed (Unit -> Unit needs {Chunked})

fun make_handler : Unit -> Handler Chunked
make_handler () = handler for Chunked {
  write_chunk _ = resume ()
  return _ = 777
}

main () = {
  let body = Streamed (fun () -> ())
  case body {
    Streamed producer -> {
      let h = make_handler ()
      producer () with h
    }
  }
}
"#;

    // The handler's `return` clause turns the success unit into 777.
    assert_runs_and_stdout_contains(src, &["777"]);
}

#[test]
fn eta_reduced_effect_op_callback_forwarded_through_wrapper_runs() {
    let src = r#"
effect Inner {
  fun ping : Unit -> Int
}

effect Outer {
  fun wrap : (Unit -> Int needs {Inner}) -> Int
}

handler answer_inner for Inner {
  ping () = {
    resume 41
  }
}

handler my_wrap for Outer needs {Inner} {
  wrap f = {
    let value = f ()
    resume (value + 1)
  }
}

fun call_wrap : (Unit -> Int needs {Inner}) -> Int needs {Outer}
call_wrap f = wrap! f

main () = {
  call_wrap (ping!)
} with {my_wrap, answer_inner}
"#;

    assert_runs_and_stdout_contains(src, &["42"]);
}

#[test]
fn complex_guard_case_runs_without_eager_fallthrough() {
    let src = r#"
g1 x = x == 0
g2 x = x == 1
g3 x = x == 2

main () = case 0 {
  0 when g1 0 -> 10
  1 when g2 1 -> 20
  2 when g3 2 -> 30
  _ -> 40
}
"#;

    assert_runs_and_stdout_contains(src, &["10"]);
}

#[test]
fn let_bound_inner_handler_wins_over_outer_inline_handler() {
    let src = r#"
effect Choose {
  fun get : Unit -> Int
}

make_handler () = handler for Choose {
  get () = resume 2
}

main () = {
  let h = make_handler ()
  {
    get! ()
  } with {h, get () = resume 1}
}
"#;

    assert_runs_and_stdout_contains(src, &["2"]);
}

#[test]
fn beam_native_handler_named_reference_lowers_to_native_ops() {
    let src = r#"
import Std.Actor (Process, beam_actor)

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
import Std.Ref (Ref, beam_ref)

main () = {
  let r = new! 41
  get! r
} with beam_ref
"#;

    let out = emit_elaborated_with_std(src);
    assert!(
        out.contains("'Std.Ref.Ref'") && out.contains("'std_evidence_bridge':'insert_canonical'"),
        "beam_ref should still install native evidence\n{out}"
    );
    assert!(
        out.contains("call 'erlang':'make_ref'")
            && out.contains("call 'erlang':'put'")
            && out.contains("call 'erlang':'get'"),
        "beam_ref new/get should direct-call native Erlang ref operations\n{out}"
    );
    assert!(
        !out.contains("'std_evidence_bridge':'find_evidence'"),
        "beam_ref new/get should not project evidence after native direct-call\n{out}"
    );
    assert_core_compiles(&out);
}

#[test]
fn beam_actor_monitor_uses_backend_atom_direct_call() {
    let src = r#"
import Std.Actor (Actor, Monitor, beam_actor)

main () = {
  let pid = self! ()
  let _ref = monitor! pid
  ()
} with beam_actor
"#;

    let out = emit_elaborated_with_std(src);
    assert!(
        out.contains("call 'erlang':'monitor'\n") && out.contains("'process'"),
        "monitor! should direct-call erlang:monitor(process, Pid)\n{out}"
    );
    assert_core_compiles(&out);
}

#[test]
fn async_handler_with_beam_actor_lowers_without_scoped_binding_cycle() {
    let src = r#"
import Std.Actor (Process, beam_actor)
import Std.Async (Async, async_handler)

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

/// A tail-recursive function must survive the uniform-CPS pipeline without
/// losing its tail-call property — otherwise deep recursion blows the BEAM
/// process stack.
///
/// The old selective-CPS path preserved tail position structurally (the
/// recursive `apply` was the last expression in its case arm). The new
/// uniform-monadic path lowers every call through `Bind`, producing a
/// `let <V> = apply f(...) in case V of ...` shape that's structurally
/// non-tail. BEAM's tail-call optimizer still handles this pattern because
/// the recursive call passes the outer `_ReturnK` directly (CPS-style tail
/// call) and each case arm either tail-calls `_ReturnK` or returns the bound
/// value unchanged. The behavioral guard below is what actually matters:
/// 10 million iterations must complete without a stack overflow.
#[test]
fn tail_recursive_apply_in_tail_position() {
    let src = "
sum_to acc n = if n == 0 then acc else sum_to (acc + n) (n - 1)

main () = sum_to 0 10000000
";
    // sum_to 0 10_000_000 = 10_000_000 * 10_000_001 / 2 = 50_000_005_000_000.
    // If tail recursion were broken, this would crash with stack_overflow long
    // before reaching the answer.
    assert_runs_and_stdout_contains(src, &["50000005000000"]);
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
        out.contains("'is_odd'/3"),
        "is_even should reference is_odd\n{out}"
    );
    assert!(
        out.contains("'is_even'/3"),
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
        out.contains("'__dict_Describe_Color'/2"),
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
    // dbg is provided by Std.IO in the new path.
    assert!(
        out.contains("'std_io', 'dbg'"),
        "expected Std.IO dbg call\n{out}"
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
    // The inline lambda should appear directly in main in uniform CPS shape.
    assert!(
        out.contains("fun (___tup, _Evidence, _ReturnK)"),
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
        out.contains("fun (___tup, _Evidence, _ReturnK)"),
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
        out.contains(&format!("'{dict}'/2")),
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
    // dbg should call through Std.IO.
    assert!(
        out.contains("'std_io', 'dbg'"),
        "expected Std.IO dbg call\n{out}"
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
    // do_work takes 1 user param (Unit) + _Evidence + _ReturnK = arity 3
    assert_contains(&out, "'do_work'/3");
    assert_contains(&out, "_Evidence");
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
    // Op call now goes through evidence projection.
    assert_contains(&out, "_Evidence");
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
    // Should have evidence-based op apply with a fun (continuation).
    assert_contains(&out, "_Evidence");
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
    assert_contains(&out, "_Evidence");
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
    // The optimizer can erase this simple handler install completely by
    // specializing the call under the named handler.
    assert_contains(&out, "'Log'");
    assert_contains(&out, "apply _ReturnK(42)");
    assert_core_compiles(&out);
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
    assert_contains(&out, "'std_evidence_bridge':'insert_canonical'");
    assert_contains(&out, "'Fail'");
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
  log msg = {
    resume ()
    resume ()
  }
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
    assert_contains(&out, "apply _K_arm");
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
    assert_contains(&out, "'std_evidence_bridge':'insert_canonical'");
    assert_contains(&out, "'Fail'");
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
    // Static tail-resumptive function variants can eliminate both handler
    // lookups from this shape.
    assert_contains(&out, "__saga_static_variant__do_work");
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
    // do_work is specialized away under the static handler, but the let-bound
    // arithmetic still appears in the generated variant.
    assert_contains(&out, "__saga_static_variant__do_work");
    assert_contains(&out, "_Evidence");
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
    // Should have evidence installation for the Fail handlers.
    assert_contains(&out, "'std_evidence_bridge':'insert_canonical'");
    assert_contains(&out, "'Fail'");
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
    // outer's body should call inner with _Evidence and _ReturnK passed through
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
    // risky_work takes Unit + _Evidence + _ReturnK = arity 3
    assert_contains(&out, "'risky_work'/3");
    // Both handler bindings should appear at the `with` site
    assert_contains(&out, "'Fail'");
    assert_contains(&out, "'Log'");
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
    // The handler arm body should call Std.IO dbg.
    assert_contains(&out, "'std_io', 'dbg'");
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
    assert_contains(&out, "'Log'");
    assert_contains(&out, "'Fail'");
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
    assert_contains(&out, "'Log'");
    assert_contains(&out, "'Fail'");
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
    // safe_div takes 2 user params + _Evidence + _ReturnK = arity 4
    assert_contains(&out, "'safe_div'/4");
    assert_contains(&out, "'Fail'");
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
    assert_contains(&out, "'Ask'");
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
    assert_contains(&out, "'Ask'");
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
    assert_contains(&out, "'Ask'");
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
    // The two tail-resumptive ask! calls collapse into a static variant.
    assert_contains(&out, "__saga_static_variant__compute");
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
    assert_contains(&out, "'Fail'");
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
    assert_contains(&out, "'Fail'");
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
fn handler_bindings_from_record_fields_compile() {
    let src = r#"
effect One {
  fun one : Unit -> Int
}

effect Two {
  fun two : Unit -> Int
}

fun run : Unit -> Int needs {One, Two}
run () = one! () + two! ()

fun connect : Unit -> { one_handler: Handler One, two_handler: Handler Two }
connect () = {
  {
    one_handler: handler for One {
      one () = resume 1
    },
    two_handler: handler for Two {
      two () = resume 2
    },
  }
}

main () = {
  let handlers = connect ()
  let one_handler = handlers.one_handler
  let two_handler = handlers.two_handler
  dbg (run () with {one_handler, two_handler})
}
"#;
    let out = emit_elaborated(src);
    assert_contains(&out, "call 'erlang':'element'");
    assert_contains(&out, "'One'");
    assert_contains(&out, "'Two'");
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
    assert_contains(&out, "'double'/3");
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
        out.contains("'add'/4"),
        "expected reference to add/4:\n{out}"
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
        out.contains("'Logger'"),
        "expected Logger evidence in partial application lambda:\n{out}"
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
        out.contains("call 'lists':'reverse'"),
        "List.reverse should emit lists:reverse\n{out}"
    );
    assert!(
        out.contains("call 'std_string_bridge':'reverse'"),
        "String.reverse should emit std_string_bridge:reverse\n{out}"
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
        out.contains("call 'std_string_bridge':'reverse'"),
        "Exposed reverse should emit std_string_bridge:reverse, not lists:reverse\n{out}"
    );
    assert!(
        !out.contains("call 'lists':'reverse'"),
        "Should not contain lists:reverse\n{out}"
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
        out.contains("call 'std_string_bridge':'reverse'"),
        "Exposed reverse should emit std_string_bridge:reverse\n{out}"
    );
    assert!(
        out.contains("call 'lists':'reverse'"),
        "List.reverse should emit lists:reverse\n{out}"
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
  let _ = File.write! "/tmp/saga-file-io-test.txt" "hello"
  File.exists! "/tmp/saga-file-io-test.txt"
} with fs
"#;
    let out = emit_elaborated_with_std(src);
    assert!(
        out.contains("call 'std_file_bridge':'write_file'"),
        "Std.File.fs should lower write through std_file_bridge\n{out}"
    );
    assert!(
        out.contains("call 'std_file_bridge':'file_exists'"),
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

#[test]
fn local_let_shadow_of_top_level_effectful_fn_calls_local_value() {
    // A `let` binding can shadow a top-level effectful function. The call site
    // must dispatch to the local value, not silently route through the
    // top-level function via raw-name lookup in fun_info / let_effect_bindings.
    let src = r#"
effect Echo {
  fun emit : String -> Unit
}

handler silent for Echo {
  emit _ = resume ()
}

fun shouter : String -> Int needs {Echo}
shouter msg = { emit! msg; 99 }

fun pure_lambda : String -> Int
pure_lambda _ = 42

main () = {
  let shouter = pure_lambda
  shouter "hi"
} with silent
"#;
    assert_runs_and_stdout_contains(src, &["42"]);
}

#[test]
fn symbol_intrinsic_lowers_to_binary_string_literal() {
    // `symbol_name (Proxy : Proxy 'Foo)` should monomorphize through the
    // KnownSymbol evidence and emit a Core Erlang binary containing "Foo".
    let src = r#"
main () = symbol_name (Proxy : Proxy 'Foo)
"#;
    let out = emit_elaborated(src);
    // Binary literal bytes for "Foo" -> 'F' = 70, 'o' = 111.
    assert!(
        out.contains("#<70>") && out.contains("#<111>"),
        "expected binary bytes for 'Foo' in output:\n{out}"
    );
    assert_runs_and_stdout_contains(src, &["Foo"]);
}

#[test]
fn known_symbol_polymorphic_dict_passing_e2e() {
    // A single polymorphic describe function multiplexes across three call
    // sites via dict passing: each call sees its own symbol string.
    let src = r#"
fun describe : Proxy n -> String where {n : KnownSymbol}
describe p = symbol_name p

main () = (
  describe (Proxy : Proxy 'admin),
  describe (Proxy : Proxy 'editor),
  describe (Proxy : Proxy 'viewer)
)
"#;
    assert_runs_and_stdout_contains(src, &["admin", "editor", "viewer"]);
}

#[test]
fn known_symbol_polymorphic_forwarding_e2e() {
    // Polymorphic-to-polymorphic forwarding: forward calls describe, both
    // with `where {n : KnownSymbol}`. The dict threads through both layers.
    let src = r#"
fun describe : Proxy n -> String where {n : KnownSymbol}
describe p = symbol_name p

fun forward : Proxy n -> String where {n : KnownSymbol}
forward p = describe p

main () = (
  forward (Proxy : Proxy 'forwarded),
  forward (Proxy : Proxy 'again)
)
"#;
    assert_runs_and_stdout_contains(src, &["forwarded", "again"]);
}

#[test]
fn known_symbol_direct_ascription_uses_enclosing_type_var_e2e() {
    let src = r#"
fun probe : Proxy n -> Proxy m -> (String, String) where {n : KnownSymbol, m : KnownSymbol}
probe _ q = (symbol_name (Proxy : Proxy n), symbol_name q)

main () = probe (Proxy : Proxy 'left) (Proxy : Proxy 'right)
"#;
    assert_runs_and_stdout_contains(src, &["left", "right"]);
}

#[test]
fn known_symbol_let_ascription_uses_enclosing_type_var_e2e() {
    let src = r#"
fun probe : Proxy n -> Proxy m -> (String, String) where {n : KnownSymbol, m : KnownSymbol}
probe _ q = {
  let p : Proxy n = Proxy
  (symbol_name p, symbol_name q)
}

main () = probe (Proxy : Proxy 'let_left) (Proxy : Proxy 'let_right)
"#;
    assert_runs_and_stdout_contains(src, &["let_left", "let_right"]);
}

#[test]
fn symbol_non_proxy_let_ascription_uses_enclosing_type_var_e2e() {
    let src = r#"
type Id (k : Symbol) = Id Int

fun tag_id : Id n -> String where {n : KnownSymbol}
tag_id _ = symbol_name (Proxy : Proxy n)

fun probe : Proxy n -> Proxy m -> (String, String) where {n : KnownSymbol, m : KnownSymbol}
probe _ q = {
  let x : Id n = Id 1
  (tag_id x, symbol_name q)
}

main () = probe (Proxy : Proxy 'id_left) (Proxy : Proxy 'id_right)
"#;
    assert_runs_and_stdout_contains(src, &["id_left", "id_right"]);
}

// Phase B sum-type FromJson bug repro lives in
// `tests/e2e/tests/generic_fromjson_test.saga` — it needs `<>`
// (Semigroup) and Std.Test, neither of which this harness links against.
