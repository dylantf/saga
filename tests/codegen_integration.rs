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
                call_effects: codegen::call_effects::CallEffectMap::new(),
                optimization: codegen::optimize::OptimizationFacts::default(),
            },
        );
    }
    // Overlay elaborated modules with their resolution maps
    for (name, elab) in elaborated_modules {
        let normalized = codegen::normalize::normalize_effects(&elab);
        let front_resolution = result
            .module_check_results()
            .get(&name)
            .map(|m| m.resolution.clone())
            .unwrap_or_default();
        let resolution = codegen::resolve::resolve_names(
            &name,
            &normalized,
            codegen_info_map,
            prelude_imports,
            &front_resolution,
            &std::collections::HashMap::new(),
        );
        let entry = modules.entry(name.clone()).or_default();
        entry.elaborated = normalized;
        entry.resolution = resolution;
        entry.front_resolution = front_resolution;
    }
    let ctx = codegen::CodegenContext {
        modules,
        let_effect_bindings: result.let_effect_bindings.clone(),
        prelude_imports: result.prelude_imports.clone(),
    };
    codegen::emit_module_with_context("_script", &elaborated, &ctx, &result, None, None)
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

    let out = emit_elaborated(src);
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

    let eval = if out.contains("'main'/1") {
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

fn emitted_function(out: &str, name: &str, arity: usize) -> String {
    let marker = format!("'{}'/{} =", name, arity);
    let start = out
        .find(&marker)
        .unwrap_or_else(|| panic!("missing function marker {marker}\n{out}"));
    let rest = &out[start..];
    let end = rest
        .find("\n\n")
        .map(|idx| start + idx)
        .unwrap_or_else(|| out.len());
    out[start..end].to_string()
}

#[test]
fn mixed_effect_trait_impl_keeps_pure_method_callable() {
    let src = r#"
effect Ask {
  fun ask : Unit -> String
}

handler ask_default for Ask {
  ask () = resume "x"
}

trait Payload a {
  fun payload : a -> String needs {Ask}
  fun is_unit : a -> Bool
}

type Leaf = Leaf String

impl Payload for Leaf needs {Ask} {
  payload (Leaf _) = ask! ()
  is_unit _ = False
}

fun render_payload : a -> String needs {Ask} where {a: Payload}
render_payload x = {
  let p = payload x
  if is_unit x then "bad" else p
}

main () = render_payload (Leaf "y") with ask_default
"#;

    assert_runs_and_stdout_contains(src, &["x"]);
}

#[test]
fn parameterized_mixed_effect_trait_impl_preserves_method_slots() {
    let src = r#"
effect Ask {
  fun ask : Unit -> String
}

handler ask_default for Ask {
  ask () = resume "inner"
}

trait Payload a {
  fun payload : a -> String needs {Ask}
  fun is_unit : a -> Bool
}

type Leaf = Leaf String
type Box a = Box a

impl Payload for Leaf needs {Ask} {
  payload (Leaf _) = ask! ()
  is_unit _ = False
}

impl Payload for Box a where {a: Payload} needs {Ask} {
  payload (Box x) = payload x
  is_unit (Box x) = is_unit x
}

fun render_payload : a -> String needs {Ask} where {a: Payload}
render_payload x = {
  let p = payload x
  if is_unit x then "bad" else p
}

main () = render_payload (Box (Leaf "y")) with ask_default
"#;

    assert_runs_and_stdout_contains(src, &["inner"]);
}

#[test]
fn adt_constructor_as_higher_order_function_runs() {
    let src = r#"
type Leaf a = Leaf a

fun map : (a -> b) -> a -> b
map f value = f value

main () = case map Leaf 42 {
  Leaf n -> n
}
"#;

    assert_runs_and_stdout_contains(src, &["42"]);
}

#[test]
fn anonymous_record_layout_from_function_signature_lowers_field_access() {
    let src = r#"
fun pick_id : { id: Int, name: String } -> Int
pick_id row = row.id

main () = pick_id { id: 42, name: "Alice" }
"#;

    assert_runs_and_stdout_contains(src, &["42"]);
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
    // The handler functions are bound locally at the `with beam_ref` site
    // with freshly-numbered suffixes (e.g. `_Handle_Std_Ref_Ref_new__2`),
    // so match the prefix with the `__` separator rather than a bare `(`.
    assert!(
        out.contains("_Handle_Std_Ref_Ref_new"),
        "beam_ref should install and apply a handler function for new!\n{out}"
    );
    assert!(
        out.contains("_Handle_Std_Ref_Ref_get"),
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
fn trait_method_call_specializes_known_local_impl() {
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
    // Phase 2 trait specialization: a saturated call to a statically-known
    // local, nullary impl is lowered to a direct call to the hoisted method
    // function, instead of building the dict tuple and extracting via
    // `element/2`.
    assert!(
        out.contains("apply '__saga_dictmethod"),
        "expected a direct hoisted-method call for the known impl\n{out}"
    );
    // The dict constructor is still emitted (its tuple now references the
    // hoisted method) so dynamic/polymorphic dispatch keeps working.
    assert!(
        out.contains("'__dict_Describe_Color'/0"),
        "expected the dict constructor to still be emitted\n{out}"
    );
}

#[test]
fn effectful_trait_method_specialization_threads_evidence() {
    // The effectful `encode` call is specialized to a direct hoisted-method
    // call, but the call must still thread `_Evidence`/`_ReturnK` (a 3-arity
    // call: one user arg plus the two CPS params). This pins the anchor that
    // specialization swaps only the callee, never the effect ABI.
    let src = "
effect Options { fun get_options : Unit -> Int }
handler options_10 for Options { get_options () = resume 10 }

trait Encodable a { fun encode : a -> Int needs {Options} }
impl Encodable for Int needs {Options} { encode x = x + get_options! () }

fun compute : (x: Int) -> Int needs {Options}
compute x = encode x

main () = compute 5 with options_10
";
    let out = emit_elaborated(src);
    assert!(
        out.contains("apply '__saga_dictmethod") && out.contains("_0'/3("),
        "expected a 3-arity direct hoisted-method call (arg + evidence + return_k)\n{out}"
    );
}

#[test]
fn nullary_dict_method_is_hoisted_and_exported_without_local_use() {
    // Supply-driven hoisting (Phase 3): a module exports a hoisted top-level
    // function for every nullary dict method so importers can call it directly
    // cross-module — even when the defining module never calls it itself.
    let src = "
type Color = Red | Green
trait Describe a { fun describe : (x: a) -> String }
impl Describe for Color {
  describe c = case c {
    Red -> \"r\"
    Green -> \"g\"
  }
}
main () = 1
";
    let out = emit_elaborated(src);
    let export_line = out.lines().next().expect("empty module");
    assert!(
        export_line.contains("__saga_dictmethod___dict_Describe_Color_0"),
        "expected the hoisted Describe/Color method to be exported\n{export_line}"
    );
}

#[test]
fn multi_arg_trait_method_specializes_with_correct_arity() {
    // A method with >1 user param specializes to a direct call of the matching
    // arity. Impl methods must carry the full parameter list (eta-reduced impls
    // are rejected at typecheck), so the trait-signature arity used for the
    // saturation guard always equals the hoisted function's arity — no risk of
    // a wrong-arity direct call from a point-free impl.
    let src = "
fun prepend : Int -> String -> String
prepend n s = show n <> s
trait Greet a { fun greet : (x: a) -> (s: String) -> String }
impl Greet for Int {
  greet n s = prepend n s
}
main () = greet 42 \"hi\"
";
    let out = emit_elaborated(src);
    assert!(
        out.contains("'__saga_dictmethod___dict_Greet_Std_Int_Int_0'/2"),
        "expected a 2-arity direct call to the hoisted Greet/Int method\n{out}"
    );
}

#[test]
fn parameterized_dict_chain_is_inlined_in_module() {
    // Phase 4a (generic fold): a statically-known *parameterized* dict-method
    // call on a local impl is inlined — the conditional impl's method body is
    // beta-reduced into a `case` over the argument whose body dispatches through
    // the concrete sub-dictionary, collapsing the dict chain. Here `encode b`
    // with `b : Box Int` dispatches `__dict_Encodable_Box(__dict_Encodable_Int)`;
    // after folding it becomes `case b of Box x -> <direct Int-method call>`,
    // with no dict tuple build and no `element/2` projection for the chain.
    let src = "
trait Encodable a { fun encode : (x: a) -> Int }
type Box a = Box a
impl Encodable for Int { encode x = x }
impl Encodable for Box a where {a: Encodable} { encode (Box x) = encode x }
fun run : (b: Box Int) -> Int
run b = encode b
main () = run (Box 5)
";
    let out = emit_elaborated(src);
    let run_fn = emitted_function(&out, "run", 1);
    assert!(
        run_fn.contains("_script_Box")
            && run_fn.contains("apply '__saga_dictmethod___dict_Encodable_Std_Int_Int_0'/1("),
        "expected `run` to destructure Box and call the Int method directly\n{run_fn}"
    );
    assert!(
        !run_fn.contains("element("),
        "expected no element/2 dict projection in the inlined chain\n{run_fn}"
    );
}

#[test]
fn routed_derive_with_fresh_rep_dict_does_not_fake_nullary_hoist() {
    // A routed `FromJson` derive generates:
    //
    //   impl FromJson for Boxed where {Boxed: Generic r, r: FromJson}
    //
    // The `r: FromJson` evidence is a fresh representation dictionary, not an
    // impl type parameter. The concrete `FromJson Boxed` dict therefore has one
    // captured sub-dict and must not lower as if it had a nullary hoisted method.
    let src = r#"
import Std.Generic (U1, Leaf, Variant, Adt)

trait FromJson a {
  fun from_json : String -> Result a String
}

impl FromJson for Int {
  from_json _ = Ok 7
}

impl FromJson for U1 {
  from_json _ = Ok U1
}

impl FromJson for Leaf a where {a: FromJson} {
  from_json s = case from_json s {
    Ok x -> Ok (Leaf x)
    Err e -> Err e
  }
}

impl FromJson for Variant (n : Symbol) a where {a: FromJson} {
  from_json s = case from_json s {
    Ok x -> Ok (Variant x)
    Err e -> Err e
  }
}

impl FromJson for Adt a where {a: FromJson} {
  from_json s = case from_json s {
    Ok x -> Ok (Adt "" x)
    Err e -> Err e
  }
}

type Boxed = Boxed Int
  deriving (FromJson)

main () = from_json "x" : Result Boxed String
"#;

    let out = emit_elaborated(src);
    assert!(
        out.contains("'__dict_FromJson_Boxed'/1"),
        "expected derived FromJson/Boxed dict to capture the Rep dictionary\n{out}"
    );
    assert!(
        !out.contains("__saga_dictmethod___dict_FromJson_Boxed_0"),
        "parameterized derived dict must not be lowered as a nullary hoist\n{out}"
    );
    assert_core_compiles(&out);
}

#[test]
fn effectful_parameterized_dict_chain_threads_evidence_through_inline() {
    // The inlined parameterized chain must still thread evidence: an effectful
    // conditional impl folded into nested cases keeps `_Evidence`/`_ReturnK`
    // flowing to the leaf call (Anchor 2: specialization swaps callees, never the
    // effect ABI). Runs on BEAM to prove the fold is sound, not just shaped right.
    let src = "
effect Options { fun get_options : Unit -> Int }
handler options_10 for Options { get_options () = resume 10 }
trait Encodable a { fun encode : (x: a) -> Int needs {Options} }
type Box a = Box a
impl Encodable for Int needs {Options} { encode x = x + get_options! () }
impl Encodable for Box a where {a: Encodable} needs {Options} { encode (Box x) = encode x }
fun run : (b: Box Int) -> Int needs {Options}
run b = encode b
main () = run (Box 5) with options_10
";
    assert_runs_and_stdout_contains(src, &["15"]);
}

// --- Built-in Show dispatch ---

#[test]
fn show_int_specializes_to_direct_cross_module_call() {
    let src = "main () = show 42";
    let out = emit_elaborated(src);
    // Phase 3: `show 42` on the imported `Show Int` impl is specialized to a
    // direct cross-module call to the hoisted dict method (the producer exports
    // `__saga_dictmethod_<dict>_<idx>`), instead of building the dict tuple and
    // dispatching via element/2. The canonical dict name is preserved as a
    // substring of the hoisted method name.
    assert!(
        out.contains("__saga_dictmethod___dict_Std_Base_Show_std_int_Std_Int_Int"),
        "expected a direct call to the hoisted Show/Int method\n{out}"
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
  log msg = resume () finally {
    ()
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
  log msg = resume () finally {
    ()
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
  log msg = resume () finally {
    ()
  }
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
  log msg = resume () finally {
    ()
  }
}

main () = do_work () with silent
"#;
    let out = emit_elaborated(src);
    // Should have two nested handler applies with continuations
    // Count occurrences of apply _HandleLog
    let count = out.matches("_Handle__script_Log_log").count();
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
    assert_contains(&out, "_Handle__script_Log_log");
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
    assert_contains(&out, "_Handle__script_Log_log");
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
    // safe_div takes 2 user params + _Evidence + _ReturnK = arity 4
    assert_contains(&out, "'safe_div'/4");
    assert_contains(&out, "_Handle__script_Fail_fail");
}

// --- Effect calls in non-block positions ---

#[test]
fn inline_static_tail_resume_effect_op_lowers_directly() {
    let src = r#"
effect Ask {
  fun ask : Unit -> Int
}

main () = {
  let x = 1 + ask! ()
  x
} with {
  ask () = resume 41
}
"#;
    let out = emit_elaborated(src);
    assert!(
        !out.contains("_Handle__script_Ask_ask"),
        "tail-resume op should not allocate/apply handler closure\n{out}"
    );
    assert_contains(&out, "call 'erlang':'+'");
    assert_core_compiles(&out);
}

#[test]
fn inline_static_tail_resume_effect_op_binds_runtime_args() {
    let src = r#"
effect Choose {
  fun choose : Int -> Int
}

main () = choose! 42 with {
  choose value = resume value
}
"#;
    let out = emit_elaborated(src);
    assert!(
        !out.contains("_Handle__script_Choose_choose"),
        "tail-resume op with direct arg should not use handler closure\n{out}"
    );
    assert_contains(&out, "42");
    assert_core_compiles(&out);
}

#[test]
fn inline_static_tail_resume_effect_op_allows_direct_prefix_block() {
    let src = r#"
effect Ask {
  fun ask : Unit -> Int
}

fun pure_fun1 : Unit -> Int
pure_fun1 () = 10

fun pure_fun2 : Unit -> Int
pure_fun2 () = 20

main () = ask! () with {
  ask () = {
    let _ = pure_fun1 ()
    let _ = pure_fun2 ()
    resume 42
  }
}
"#;
    let out = emit_elaborated(src);
    assert!(
        !out.contains("_Handle__script_Ask_ask"),
        "tail-resume op with direct prefix should not use handler closure\n{out}"
    );
    assert_contains(&out, "'pure_fun1'");
    assert_contains(&out, "'pure_fun2'");
    assert_contains(&out, "42");
    assert_core_compiles(&out);
}

#[test]
fn named_static_tail_resume_effect_op_lowers_directly() {
    let src = r#"
effect Ask {
  fun ask : Unit -> Int
}

handler forty_one for Ask {
  ask () = resume 41
}

main () = ask! () with forty_one
"#;
    let out = emit_elaborated(src);
    assert!(
        !out.contains("_Handle__script_Ask_ask"),
        "same-module named tail-resume handler should not use handler closure\n{out}"
    );
    assert_contains(&out, "41");
    assert_core_compiles(&out);
}

#[test]
fn multiple_matching_tail_resume_arms_stay_on_evidence_path() {
    let src = r#"
effect Choose {
  fun choose : Int -> Int
}

main () = choose! 1 with {
  choose 0 = resume 10
  choose _ = resume 20
}
"#;
    let out = emit_elaborated(src);
    assert_contains(&out, "_Handle__script_Choose_choose");
    assert_core_compiles(&out);
}

#[test]
fn abort_arm_stays_on_evidence_path() {
    let src = r#"
effect Fail {
  fun fail : Unit -> Int
}

main () = fail! () with {
  fail () = 0
}
"#;
    let out = emit_elaborated(src);
    assert_contains(&out, "_Handle__script_Fail_fail");
    assert_core_compiles(&out);
}

#[test]
fn conditional_tail_resume_handler_stays_on_evidence_path() {
    let src = r#"
effect Ask {
  fun ask : Unit -> Int
}

handler forty_one for Ask {
  ask () = resume 41
}

handler forty_two for Ask {
  ask () = resume 42
}

main () = {
  let h = if True then forty_one else forty_two
  ask! () with h
}
"#;
    let out = emit_elaborated(src);
    assert_contains(&out, "_Handle__script_Ask_ask");
    assert_core_compiles(&out);
}

#[test]
fn dynamic_tail_resume_handler_stays_on_evidence_path() {
    let src = r#"
effect Ask {
  fun ask : Unit -> Int
}

fun make_handler : Unit -> Handler Ask
make_handler () = handler for Ask {
  ask () = resume 41
}

main () = {
  let h = make_handler ()
  ask! () with h
}
"#;
    let out = emit_elaborated(src);
    assert_contains(&out, "_Handle__script_Ask_ask");
    assert_core_compiles(&out);
}

#[test]
fn nested_static_tail_resume_handlers_shadow_correctly() {
    let src = r#"
effect Ask {
  fun ask : Unit -> Int
}

main () = {
  let inner = ask! () with {
    ask () = resume 20
  }
  let outer = ask! ()
  inner + outer
} with {
  ask () = resume 10
}
"#;
    let out = emit_elaborated(src);
    assert!(
        !out.contains("_Handle__script_Ask_ask"),
        "nested static tail-resume handlers should both lower directly\n{out}"
    );
    assert_core_compiles(&out);
    assert_runs_and_stdout_contains(src, &["30"]);
}

#[test]
fn static_tail_resume_inside_direct_outer_code_lowers_directly() {
    let src = r#"
effect ReadInt {
  fun read : Unit -> Int
}

handler forty_one for ReadInt {
  read () = resume 41
}

main () = {
  let value = read! () with forty_one
  value + 1
}
"#;
    let out = emit_elaborated(src);
    assert!(
        !out.contains("_Handle__script_ReadInt_read"),
        "static handler inside direct outer code should lower op directly\n{out}"
    );
    assert_contains(&out, "call 'erlang':'+'");
    assert_core_compiles(&out);
}

#[test]
fn static_tail_resume_fact_survives_pure_body_lets() {
    let src = r#"
effect Ask {
  fun ask : Unit -> Int
}

main () = {
  let x = 40
  let y = x + 1
  ask! ()
} with {
  ask () = resume 42
}
"#;
    let out = emit_elaborated(src);
    assert!(
        !out.contains("_Handle__script_Ask_ask"),
        "pure lets in handled body should preserve static tail-resume facts\n{out}"
    );
    assert_contains(&out, "call 'erlang':'+'");
    assert_core_compiles(&out);
}

#[test]
fn multi_effect_static_handler_only_optimizes_proven_op() {
    let src = r#"
effect Ask {
  fun ask : Unit -> Int
}

effect Log {
  fun log : String -> Unit
}

handler mixed for Ask, Log {
  ask () = resume 41
  log _ = resume () finally {
    ()
  }
}

main () = {
  log! "x"
  ask! ()
} with mixed
"#;
    let out = emit_elaborated(src);
    assert_contains(&out, "_Handle__script_Log_log");
    let evidence_applies = out.matches("apply call 'erlang':'element'").count();
    assert_eq!(
        evidence_applies, 1,
        "only Log.log should use evidence lookup; Ask.ask should lower directly\n{out}"
    );
    assert_core_compiles(&out);
}

#[test]
fn return_clause_tail_resume_handler_stays_on_evidence_path() {
    let src = r#"
effect Ask {
  fun ask : Unit -> Int
}

handler add_one_return for Ask {
  ask () = resume 41
  return value = value + 1
}

main () = ask! () with add_one_return
"#;
    let out = emit_elaborated(src);
    assert_contains(&out, "_Handle__script_Ask_ask");
    assert_core_compiles(&out);
}

#[test]
fn let_bound_handler_expr_tail_resume_lowers_directly() {
    let src = r#"
effect Ask {
  fun ask : Unit -> Int
}

main () = {
  let h = handler for Ask {
    ask () = resume 41
  }
  ask! () with h
}
"#;
    let out = emit_elaborated(src);
    assert!(
        !out.contains("_Handle__script_Ask_ask"),
        "let-bound pure handler expression should recover static tail-resume facts\n{out}"
    );
    assert_contains(&out, "41");
    assert_core_compiles(&out);
}

#[test]
fn let_bound_handler_expr_finally_stays_on_evidence_path() {
    let src = r#"
effect Ask {
  fun ask : Unit -> Int
}

main () = {
  let h = handler for Ask {
    ask () = resume 41 finally {
      ()
    }
  }
  ask! () with h
}
"#;
    let out = emit_elaborated(src);
    assert_contains(&out, "_Handle__script_Ask_ask");
    assert_core_compiles(&out);
}

#[test]
fn let_bound_handler_expr_return_clause_stays_on_evidence_path() {
    let src = r#"
effect Ask {
  fun ask : Unit -> Int
}

main () = {
  let h = handler for Ask {
    ask () = resume 41
    return value = value + 1
  }
  ask! () with h
}
"#;
    let out = emit_elaborated(src);
    assert_contains(&out, "_Handle__script_Ask_ask");
    assert_core_compiles(&out);
}

#[test]
fn same_module_handler_factory_tail_resume_lowers_directly() {
    let src = r#"
effect Ask {
  fun ask : Unit -> Int
}

make_ask n = handler for Ask {
  ask () = resume n
}

main () = {
  let h = make_ask 41
  ask! () with h
}
"#;
    let out = emit_elaborated(src);
    assert!(
        !out.contains("_Handle__script_Ask_ask"),
        "same-module handler factory should recover static tail-resume facts\n{out}"
    );
    assert_contains(&out, "41");
    assert_core_compiles(&out);
    assert_runs_and_stdout_contains(src, &["41"]);
}

#[test]
fn handler_factory_return_clause_preserves_evidence_path() {
    let src = r#"
effect Ask {
  fun ask : Unit -> Int
}

make_ask n = handler for Ask {
  ask () = resume n
  return value = value + 1
}

main () = {
  let h = make_ask 41
  ask! () with h
}
"#;
    let out = emit_elaborated(src);
    assert_contains(&out, "apply call 'erlang':'element'");
    assert_core_compiles(&out);
    assert_runs_and_stdout_contains(src, &["42"]);
}

#[test]
fn handler_factory_with_prefix_stays_on_evidence_path_for_now() {
    let src = r#"
effect Ask {
  fun ask : Unit -> Int
}

make_ask n = {
  let m = n + 1
  handler for Ask {
    ask () = resume m
  }
}

main () = {
  let h = make_ask 41
  ask! () with h
}
"#;
    let out = emit_elaborated(src);
    assert_contains(&out, "apply call 'erlang':'element'");
    assert_core_compiles(&out);
    assert_runs_and_stdout_contains(src, &["42"]);
}

#[test]
fn same_module_helper_call_under_static_handler_inlines_direct_ops() {
    let src = r#"
effect ReadInt {
  fun read : Unit -> Int
}

fun read_value : Unit -> Int needs {ReadInt}
read_value () = read! ()

fun read_plus_two : Unit -> Int needs {ReadInt}
read_plus_two () = {
  let value = read_value ()
  value + 2
}

main () = read_plus_two () with {
  read () = resume 40
}
"#;
    let out = emit_elaborated(src);
    let main = emitted_function(&out, "main", 1);
    assert!(
        !main.contains("apply 'read_plus_two'/3"),
        "main should inline the covered helper call\n{main}"
    );
    assert!(
        !main.contains("apply 'read_value'/3"),
        "main should inline the nested covered helper call\n{main}"
    );
    assert_core_compiles(&out);
    assert_runs_and_stdout_contains(src, &["42"]);
}

#[test]
fn same_module_helper_if_under_static_handler_inlines_direct_ops() {
    let src = r#"
effect ReadInt {
  fun read : Unit -> Int
}

fun maybe_read : Bool -> Int needs {ReadInt}
maybe_read use_read =
  if use_read then read! () else 0

main () = maybe_read True with {
  read () = resume 42
}
"#;
    let out = emit_elaborated(src);
    let main = emitted_function(&out, "main", 1);
    assert!(
        !main.contains("apply 'maybe_read'/3"),
        "main should inline the covered helper if\n{main}"
    );
    assert_core_compiles(&out);
    assert_runs_and_stdout_contains(src, &["42"]);
}

#[test]
fn same_module_helper_case_under_static_handler_inlines_direct_ops() {
    let src = r#"
effect ReadInt {
  fun read : Unit -> Int
}

type Choice = UseEffect | UseDefault

fun choose_read : Choice -> Int needs {ReadInt}
choose_read choice = case choice {
  UseEffect -> read! ()
  UseDefault -> 0
}

main () = choose_read UseEffect with {
  read () = resume 42
}
"#;
    let out = emit_elaborated(src);
    let main = emitted_function(&out, "main", 1);
    assert!(
        !main.contains("apply 'choose_read'/3"),
        "main should inline the covered helper case\n{main}"
    );
    assert_core_compiles(&out);
    assert_runs_and_stdout_contains(src, &["42"]);
}

#[test]
fn multi_clause_helper_under_static_handler_stays_on_evidence_path() {
    let src = r#"
effect ReadInt {
  fun read : Unit -> Int
}

fun read_value : Bool -> Int needs {ReadInt}
read_value True = read! ()
read_value False = 0

main () = read_value True with {
  read () = resume 42
}
"#;
    let out = emit_elaborated(src);
    let main = emitted_function(&out, "main", 1);
    assert_contains(&main, "apply 'read_value'/3");
    assert_core_compiles(&out);
    assert_runs_and_stdout_contains(src, &["42"]);
}

#[test]
fn helper_with_residual_uncovered_effect_stays_on_evidence_path() {
    let src = r#"
effect ReadInt {
  fun read : Unit -> Int
}

effect Log {
  fun log : String -> Unit
}

fun helper : Unit -> Int needs {ReadInt, Log}
helper () = {
  log! "reading"
  read! ()
}

main () = (helper () with {
  read () = resume 42
}) with {
  log _ = resume () finally {
    ()
  }
}
"#;
    let out = emit_elaborated(src);
    let main = emitted_function(&out, "main", 1);
    assert_contains(&main, "apply 'helper'/3");
    assert_core_compiles(&out);
    assert_runs_and_stdout_contains(src, &["42"]);
}

#[test]
fn repeated_handler_binding_names_do_not_reuse_stale_conditional_facts() {
    let src = r#"
effect Log {
  fun log : String -> Unit
}

handler loud for Log {
  log _ = resume ()
}

handler quiet for Log {
  log _ = resume ()
}

do_work () = {
  log! "working"
  30
}

main () = {
  let conditional = fun () -> {
    let dev = False
    let logger = if dev then loud else quiet
    do_work () with logger
  }
  let static = fun () -> {
    let logger = quiet
    do_work () with logger
  }
  conditional () + static ()
}
"#;
    let out = emit_elaborated(src);
    assert_core_compiles(&out);
    assert_runs_and_stdout_contains(src, &["60"]);
}

#[test]
fn effectful_prefix_tail_resume_stays_on_evidence_path() {
    let src = r#"
effect Ask {
  fun ask : Unit -> Int
}

effect Ping {
  fun ping : Unit -> Unit
}

main () = (ask! () with {
  ask () = {
    ping! ()
    resume 42
  }
}) with {
  ping () = resume ()
}
"#;
    let out = emit_elaborated(src);
    assert_contains(&out, "_Handle__script_Ask_ask");
    assert_core_compiles(&out);
}

#[test]
fn non_tail_resume_stays_on_evidence_path() {
    let src = r#"
effect Ask {
  fun ask : Unit -> Int
}

main () = ask! () with {
  ask () = (resume 40) + 1
}
"#;
    let out = emit_elaborated(src);
    assert_contains(&out, "_Handle__script_Ask_ask");
    assert_core_compiles(&out);
}

#[test]
fn finally_tail_resume_stays_on_evidence_path() {
    let src = r#"
effect Ask {
  fun ask : Unit -> Int
}

main () = ask! () with {
  ask () = resume 41 finally {
    ()
  }
}
"#;
    let out = emit_elaborated(src);
    assert_contains(&out, "_Handle__script_Ask_ask");
    assert_core_compiles(&out);
}

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
  ask () = resume 42 finally {
    ()
  }
}
"#;
    let out = emit_elaborated(src);
    // The ask! should be CPS-transformed with a continuation that does the addition
    assert_contains(&out, "_Handle__script_Ask_ask");
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
  ask () = resume 21 finally {
    ()
  }
}
"#;
    let out = emit_elaborated(src);
    assert_contains(&out, "_Handle__script_Ask_ask");
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
  ask () = resume True finally {
    ()
  }
}
"#;
    let out = emit_elaborated(src);
    assert_contains(&out, "_Handle__script_Ask_ask");
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
  ask () = resume 10 finally {
    ()
  }
}
"#;
    let out = emit_elaborated(src);
    // Should have two separate handler applies for the two ask! calls
    let count = out.matches("_Handle__script_Ask_ask").count();
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
fn pure_callback_to_effect_capable_hof_uses_direct_specialization() {
    let src = r#"
effect ReadInt {
  fun read : Unit -> Int
}

fun pure_value : Unit -> Int
pure_value () = 41

fun apply_eff : (Unit -> Int needs {ReadInt}) -> Int needs {ReadInt}
apply_eff f = f ()

handler forty_one for ReadInt {
  read () = resume 41
}

main () = apply_eff pure_value with forty_one
"#;
    let out = emit_elaborated(src);
    assert_contains(&out, "'__saga_direct_hof_apply_eff'/1 =");
    let main = emitted_function(&out, "main", 1);
    assert_contains(&main, "apply '__saga_direct_hof_apply_eff'/1");
    assert!(
        !main.contains("apply 'apply_eff'/3"),
        "main should use the generated direct HOF entry\n{main}"
    );
}

#[test]
fn leaky_callback_to_effect_capable_hof_stays_on_cps_path() {
    let src = r#"
effect ReadInt {
  fun read : Unit -> Int
}

fun read_value : Unit -> Int needs {ReadInt}
read_value () = read! ()

fun apply_eff : (Unit -> Int needs {ReadInt}) -> Int needs {ReadInt}
apply_eff f = f ()

handler forty_one for ReadInt {
  read () = resume 41
}

main () = apply_eff read_value with forty_one
"#;
    let out = emit_elaborated(src);
    let main = emitted_function(&out, "main", 1);
    assert_contains(&main, "apply 'apply_eff'/3");
    assert!(
        !main.contains("apply '__saga_direct_hof_apply_eff'/1"),
        "leaky callback should not use the generated direct HOF entry\n{main}"
    );
}

#[test]
fn handled_callback_to_effect_capable_hof_uses_direct_specialization() {
    let src = r#"
effect ReadInt {
  fun read : Unit -> Int
}

handler forty_one for ReadInt {
  read () = resume 41
}

fun handled_value : Unit -> Int
handled_value () = read! () with forty_one

fun apply_eff : (Unit -> Int needs {ReadInt}) -> Int needs {ReadInt}
apply_eff f = f ()

main () = apply_eff handled_value with forty_one
"#;
    let out = emit_elaborated(src);
    let main = emitted_function(&out, "main", 1);
    assert_contains(&main, "apply '__saga_direct_hof_apply_eff'/1");
    assert!(
        !main.contains("apply 'apply_eff'/3"),
        "handled callback should use the generated direct HOF entry\n{main}"
    );
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
    assert_contains(&out, "_Handle__script_One_one");
    assert_contains(&out, "_Handle__script_Two_two");
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
fn anonymous_record_generic_to_lowers_and_runs() {
    let src = r#"
fun main : Unit -> Int
main () = (from (to { name: "alice", age: 42 }) : { age: Int, name: String }).age
"#;

    assert_runs_and_stdout_contains(src, &["42"]);
}

#[test]
fn symbol_name_proxy_closure_is_beta_reduced() {
    // `symbol_name (Proxy : …)` elaborates to an immediately-applied reflection
    // closure `(fun __proxy -> "Foo")(Proxy)`. The generic-fold β-reduction must
    // collapse it: the literal key is exposed and the phantom `Proxy` closure —
    // a per-field allocation in every derived record codec — is gone. (Item 1 of
    // the post-fusion runtime-cost work; precondition for folding `apply_name_style`.)
    //
    // The `deriving (Show)` is load-bearing for the test, not the assertion: the
    // generic fold (which carries the β-reduction) short-circuits in a module with
    // no dict constructors, and a derived record is the realistic setting where
    // these reflection closures actually occur.
    let src = r#"
record Tag { v: Int } deriving (Show)

main () = symbol_name (Proxy : Proxy 'Foo)
"#;
    let out = emit_elaborated(src);
    assert!(
        out.contains("#<70>") && out.contains("#<111>"),
        "expected the literal 'Foo' bytes to survive β-reduction:\n{out}"
    );
    assert!(
        !out.to_lowercase().contains("proxy"),
        "the `symbol_name` reflection closure should be β-reduced away, but a \
         residual proxy lambda/apply survived:\n{out}"
    );
}

#[test]
fn constant_record_field_projection_collapses_case() {
    // Blocker-2 Unit A: a field projected out of a *constant* record literal folds
    // to the field value, so `case (Opts {…}).fmt of { Tagged -> "T"; Untagged ->
    // "U" }` collapses to just `"T"` — no `element` projection, no dead `Untagged`
    // arm. The `deriving (Show)` record is only here so the generic fold runs at all
    // (it short-circuits in a module with no dict constructors).
    let src = r#"
type Fmt = | Tagged | Untagged

record Opts { fmt: Fmt, name: String }

record Tag { v: Int } deriving (Show)

main () = case (Opts { fmt: Tagged, name: "x" }).fmt {
  Tagged -> "T"
  Untagged -> "U"
}
"#;
    let main_fn = emitted_function(&emit_elaborated(src), "main", 1);
    // 'T' = 84 survives; 'U' = 85 (the dead Untagged arm) is gone; the field read
    // never lowers to element/2 because the projection folded first.
    assert!(
        main_fn.contains("#<84>"),
        "expected the folded 'T' result in main:\n{main_fn}"
    );
    assert!(
        !main_fn.contains("#<85>"),
        "the dead `Untagged -> \"U\"` arm should be gone (case collapsed):\n{main_fn}"
    );
    assert!(
        !main_fn.contains("element"),
        "the `.fmt` projection should fold, not lower to erlang:element:\n{main_fn}"
    );
}

#[test]
fn constant_record_substituted_through_lambda_then_projected() {
    // Blocker-2 Unit A: a record literal is now duplicable, so an immediately-applied
    // lambda binding it β-reduces (Item 1's machinery) and the body's `o.fmt` then
    // projects + collapses. This is the in-an-inlined-body path the real codec hits
    // (opts arrives as a substituted constant), exercised without dict machinery.
    let src = r#"
type Fmt = | Tagged | Untagged

record Opts { fmt: Fmt, name: String }

record Tag { v: Int } deriving (Show)

main () = (fun o -> case o.fmt { Tagged -> "T"; Untagged -> "U" }) (Opts { fmt: Tagged, name: "x" })
"#;
    let main_fn = emitted_function(&emit_elaborated(src), "main", 1);
    assert!(
        main_fn.contains("#<84>") && !main_fn.contains("#<85>"),
        "expected the lambda+projection chain to collapse to 'T':\n{main_fn}"
    );
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

#[test]
fn multi_row_var_forwards_union_e2e() {
    // A HOF forwards the union of two independent open effect rows
    // (`needs {..a, ..b}`); each callback's effects are handled by `main`.
    let src = r#"
effect Foo { fun foo : Unit -> Int }
effect Bar { fun bar : Unit -> Int }

fun do_work : (Unit -> Int needs {..a}) -> (Unit -> Int needs {..b}) -> Int
  needs {..a, ..b}
do_work a b = {
  let res_a = a ()
  let res_b = b ()
  res_a + res_b
}

main () = {
  do_work (fun () -> foo! ()) (fun () -> bar! ())
} with {
  foo () = resume 42
  bar () = resume 3
}
"#;
    assert_runs_and_stdout_contains(src, &["45"]);
}

#[test]
fn multi_row_var_with_named_callback_effects_e2e() {
    // Each callback also carries a named effect alongside its open tail.
    let src = r#"
effect Foo { fun foo : Unit -> Int }
effect Bar { fun bar : Unit -> Int }
effect Baz { fun baz : Unit -> Int }

fun do_work : (Unit -> Int needs {Foo, ..a}) -> (Unit -> Int needs {Bar, ..b}) -> Int
  needs {Foo, Bar, ..a, ..b}
do_work a b = {
  let res_a = a ()
  let res_b = b ()
  res_a + res_b
}

main () = {
  do_work (fun () -> foo! () + baz! ()) (fun () -> bar! ())
} with {
  foo () = resume 42
  bar () = resume 3
  baz () = resume 100
}
"#;
    assert_runs_and_stdout_contains(src, &["145"]);
}

#[test]
fn supertrait_bound_projects_parent_dictionary_e2e() {
    let src = r#"
trait Parent a {
  fun parent : a -> Int
}

trait Child a where {a: Parent} {
  fun child : a -> Int
}

impl Parent for Int {
  parent x = x + 1
}

impl Child for Int {
  child x = x + 10
}

type Box a = Box a

impl Parent for Box a where {a: Parent} {
  parent (Box x) = parent x + 100
}

impl Child for Box a where {a: Child} {
  child (Box x) = child x + 1000
}

fun both : a -> Int where {a: Child}
both x = parent x + child x

main () = both (Box 2)
"#;

    assert_runs_and_stdout_contains(src, &["1115"]);
}

// Phase B sum-type FromJson bug repro lives in
// `tests/e2e/tests/generic_fromjson_test.saga` — it needs `<>`
// (Semigroup) and Std.Test, neither of which this harness links against.
