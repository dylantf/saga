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
    derive::expand_derives(&mut program, &derive::ImportedDecls::empty());
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

fn emit_selective_core(src: &str) -> String {
    emit_selective_core_with_options(src, super::lower_selective::LoweringOptions::default())
}

fn emit_selective_core_with_options(
    src: &str,
    options: super::lower_selective::LoweringOptions,
) -> String {
    let tokens = Lexer::new(src).lex().expect("lex error");
    let mut program = Parser::new(tokens).parse_program().expect("parse error");
    derive::expand_derives(&mut program, &derive::ImportedDecls::empty());
    desugar::desugar_program(&mut program);

    let mut checker = typechecker::Checker::with_prelude(None).expect("prelude error");
    let result = checker.check_program(&mut program);
    assert!(!result.has_errors(), "Type errors: {:?}", result.errors());

    let module_name = "_script";
    let elaborated = elaborate::elaborate(&program, &result);
    let ctx = CodegenContext {
        modules: std::collections::HashMap::new(),
        let_effect_bindings: result.let_effect_bindings.clone(),
        prelude_imports: result.prelude_imports.clone(),
    };
    let codegen_info = result.codegen_info();
    let resolution_map = super::resolve::resolve_names(
        module_name,
        &elaborated,
        codegen_info,
        &ctx.prelude_imports,
        &result.resolution,
    );
    let constructor_atoms = super::resolve::build_constructor_atoms(
        module_name,
        &elaborated,
        codegen_info,
        &ctx.prelude_imports,
    );
    let handler_info = super::handler_analysis::analyze(&elaborated);
    let anf_program = super::anf::normalize(elaborated, Some(&resolution_map));
    let ops_storage = super::build_effect_ops_table(&result);
    let handler_effects_storage = super::build_handler_effects(&result);
    let let_handler_effects_storage = super::build_let_handler_effects(&result);
    let effect_info = super::build_effect_info(
        &result,
        &result,
        &ops_storage,
        &handler_effects_storage,
        &let_handler_effects_storage,
    );
    let imported_handler_decls = std::collections::HashMap::new();
    let (monadic_prog, _) = super::monadic::translate::translate_with_imports(
        &anf_program,
        &resolution_map,
        &effect_info,
        &imported_handler_decls,
    );
    let cmod = super::lower_selective::lower_module_with_options(
        module_name,
        &monadic_prog,
        &resolution_map,
        &constructor_atoms,
        &ctx,
        &handler_info,
        &effect_info,
        options,
    );
    super::cerl::print_module(&cmod)
}

fn erlang_tool_available(tool: &str) -> bool {
    std::process::Command::new(tool)
        .arg("--help")
        .output()
        .is_ok()
}

fn compile_evidence_bridge_into(dir: &std::path::Path) {
    let bridge_src = include_str!("../stdlib/evidence.bridge.erl");
    let bridge_path = dir.join("std_evidence_bridge.erl");
    std::fs::write(&bridge_path, bridge_src).unwrap();
    let erlc = std::process::Command::new("erlc")
        .arg("-o")
        .arg(dir)
        .arg(&bridge_path)
        .output()
        .expect("erlc evidence bridge spawn");
    assert!(
        erlc.status.success(),
        "erlc rejected evidence bridge:\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&erlc.stdout),
        String::from_utf8_lossy(&erlc.stderr)
    );
}

fn assert_selective_core_eval_stdout_contains(src: &str, eval: &str, needle: &str) {
    if !erlang_tool_available("erlc") || !erlang_tool_available("erl") {
        return;
    }

    use std::sync::atomic::{AtomicUsize, Ordering};
    static COUNTER: AtomicUsize = AtomicUsize::new(0);

    let core = emit_selective_core(src);
    let id = COUNTER.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!(
        "saga-selective-core-run-{}-{id}",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).unwrap();
    let core_path = dir.join("_script.core");
    std::fs::write(&core_path, &core).unwrap();

    let erlc = std::process::Command::new("erlc")
        .arg("+from_core")
        .arg("-o")
        .arg(&dir)
        .arg(&core_path)
        .output()
        .expect("erlc spawn");
    assert!(
        erlc.status.success(),
        "erlc rejected selective-core output:\nstdout: {}\nstderr: {}\ncore: {}",
        String::from_utf8_lossy(&erlc.stdout),
        String::from_utf8_lossy(&erlc.stderr),
        core
    );
    if core.contains("std_evidence_bridge") {
        compile_evidence_bridge_into(&dir);
    }

    let run = std::process::Command::new("erl")
        .arg("-noshell")
        .arg("-pa")
        .arg(&dir)
        .arg("-eval")
        .arg(eval)
        .output()
        .expect("erl spawn");
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        run.status.success(),
        "erl rejected selective-core output:\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&run.stdout),
        String::from_utf8_lossy(&run.stderr)
    );
    let stdout = String::from_utf8_lossy(&run.stdout);
    assert!(
        stdout.contains(needle),
        "expected '{needle}' in selective-core runtime output, got: {stdout}"
    );
}

fn assert_selective_core_compiles(src: &str) {
    if !erlang_tool_available("erlc") {
        return;
    }

    use std::sync::atomic::{AtomicUsize, Ordering};
    static COUNTER: AtomicUsize = AtomicUsize::new(0);

    let core = emit_selective_core(src);
    let id = COUNTER.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!(
        "saga-selective-core-compile-{}-{id}",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).unwrap();
    let core_path = dir.join("_script.core");
    std::fs::write(&core_path, &core).unwrap();

    let erlc = std::process::Command::new("erlc")
        .arg("+from_core")
        .arg("-o")
        .arg(&dir)
        .arg(&core_path)
        .output()
        .expect("erlc spawn");
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        erlc.status.success(),
        "erlc rejected selective-core output:\nstdout: {}\nstderr: {}\ncore: {}",
        String::from_utf8_lossy(&erlc.stdout),
        String::from_utf8_lossy(&erlc.stderr),
        core
    );
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
fn selective_core_lowers_pure_direct_calls() {
    let out = emit_selective_core(
        r#"
fun add1 : Int -> Int
add1 x = x + 1

fun twice : Int -> Int
twice x = add1 (add1 x)

fun main : Unit -> Int
main () = twice 40
"#,
    );
    assert!(out.contains("'add1'/1"), "{out}");
    assert!(out.contains("'twice'/1"), "{out}");
    assert!(out.contains("'main'/1"), "{out}");
    assert!(out.contains("apply 'twice'/1(40)"), "{out}");
}

#[test]
fn selective_core_lowers_recursive_pure_if() {
    let out = emit_selective_core(
        r#"
fun sum_to : Int -> Int
sum_to n =
  if n <= 0 then 0
  else n + sum_to (n - 1)

fun main : Unit -> Int
main () = sum_to 10
"#,
    );
    assert!(out.contains("'sum_to'/1"), "{out}");
    assert!(out.contains("apply 'sum_to'/1"), "{out}");
    assert!(out.contains("apply 'sum_to'/1(10)"), "{out}");
}

#[test]
fn selective_core_lowers_pure_top_level_val() {
    let out = emit_selective_core(
        r#"
val base = 20 + 1

fun double : Int -> Int
double x = x * 2

fun main : Unit -> Int
main () = double base
"#,
    );
    assert!(out.contains("'base'/0"), "{out}");
    assert!(out.contains("'double'/1"), "{out}");
    assert!(out.contains("apply 'base'/0()"), "{out}");
}

#[test]
fn selective_core_lowers_print_stdout_intrinsic_directly() {
    let out = emit_selective_core(
        r#"
import Std.IO.Unsafe (print_stdout)

fun main : Unit -> Unit
main () = print_stdout "hello\n"
"#,
    );
    assert!(out.contains("'main'/1"), "{out}");
    assert!(out.contains("call 'io':'format'"), "{out}");
    assert!(out.contains("'unit'"), "{out}");
}

#[test]
fn selective_core_lowers_monomorphic_trait_method_call() {
    let out = emit_selective_core(
        r#"
fun main : Unit -> String
main () = show 42
"#,
    );
    assert!(
        out.contains("call 'std_int':'__dict_Std_Base_Show_std_int_Std_Int_Int'"),
        "{out}"
    );
    assert!(out.contains("call 'erlang':'element'"), "{out}");
    assert!(out.contains("apply ___anf_v1(42)"), "{out}");
}

#[test]
fn selective_core_lowers_effectful_trait_method_call() {
    let src = r#"
effect ReadInt {
  fun read : Unit -> Int
}

handler forty_one for ReadInt {
  read () = resume 41
}

trait Readable a {
  fun read_it : a -> Int needs {ReadInt}
}

impl Readable for Unit needs {ReadInt} {
  read_it _ = read! () + 1
}

pub fun run_trait_method : Unit -> Int
run_trait_method () = read_it () with forty_one

fun main : Unit -> Unit
main () = ()
"#;
    let out = emit_selective_core(src);
    assert!(out.contains("'__dict_Readable_Std_Base_Unit'/0"), "{out}");
    assert!(
        !out.contains("apply ___anf_v2('unit', _CpsEvidence"),
        "{out}"
    );
    assert!(
        out.contains("let <___anf_v0> =\n                41"),
        "{out}"
    );
    assert_selective_core_eval_stdout_contains(
        src,
        "io:format(\"~p~n\", ['_script':run_trait_method(unit)]), init:stop().",
        "42",
    );
}

#[test]
fn selective_core_lowers_effectful_trait_method_value_as_cps_callback() {
    let src = r#"
effect ReadInt {
  fun read : Unit -> Int
}

handler forty_one for ReadInt {
  read () = resume 41
}

trait Readable a {
  fun read_it : a -> Int needs {ReadInt}
}

impl Readable for Unit needs {ReadInt} {
  read_it _ = read! () + 1
}

fun apply_eff : (Unit -> Int needs {ReadInt}) -> Int needs {ReadInt}
apply_eff f = f ()

pub fun run_trait_method_value : Unit -> Int
run_trait_method_value () = apply_eff read_it with forty_one

fun main : Unit -> Unit
main () = ()
"#;
    let out = emit_selective_core(src);
    assert!(out.contains("'apply_eff'/3"), "{out}");
    assert!(out.contains("call 'erlang':'element'"), "{out}");
    assert!(out.contains("apply 'apply_eff'/3(___anf_v2"), "{out}");
    assert_selective_core_eval_stdout_contains(
        src,
        "io:format(\"~p~n\", ['_script':run_trait_method_value(unit)]), init:stop().",
        "42",
    );
}

#[test]
fn selective_core_lowers_generic_effectful_trait_method_dispatch() {
    let src = r#"
type Box a = Box a

effect ReadInt {
  fun read : Unit -> Int
}

handler forty_one for ReadInt {
  read () = resume 41
}

trait Readable a {
  fun read_it : a -> Int needs {ReadInt}
}

impl Readable for Int needs {ReadInt} {
  read_it _ = read! () + 1
}

impl Readable for Box a where {a: Readable} needs {ReadInt} {
  read_it (Box x) = read_it x + 1
}

pub fun run_generic_trait_method : Unit -> Int
run_generic_trait_method () = read_it (Box 0) with forty_one

fun main : Unit -> Unit
main () = ()
"#;
    let out = emit_selective_core(src);
    assert!(out.contains("'__dict_Readable_Box'/1"), "{out}");
    assert!(out.contains("'__dict_Readable_Std_Int_Int'/0"), "{out}");
    assert!(out.contains("call 'erlang':'element'"), "{out}");
    assert!(
        out.contains("let <___anf_v0> =\n                        41"),
        "{out}"
    );
    assert_selective_core_eval_stdout_contains(
        src,
        "io:format(\"~p~n\", ['_script':run_generic_trait_method(unit)]), init:stop().",
        "43",
    );
}

#[test]
fn selective_core_elides_static_handler_around_non_intersecting_trait_method_call() {
    let src = r#"
effect ReadInt {
  fun read : Unit -> Int
}

effect DbConfig {
  fun db_url : Unit -> Int
}

handler forty_one for ReadInt {
  read () = resume 41
}

trait Readable a {
  fun read_it : a -> Int needs {ReadInt}
}

impl Readable for Unit needs {ReadInt} {
  read_it _ = read! () + 1
}

pub fun run_nested_trait_and_config : Unit -> Int
run_nested_trait_and_config () = {
  {
    let trait_value = read_it ()
    let db = db_url! ()
    trait_value + db
  } with {
    db_url () = resume 1
  }
} with forty_one

fun main : Unit -> Unit
main () = ()
"#;
    let out = emit_selective_core(src);
    assert!(out.contains("'ReadInt'"), "{out}");
    assert!(!out.contains("'DbConfig'"), "{out}");
    assert!(
        !out.contains("call 'std_evidence_bridge':'insert_canonical'\n              (_CpsEvidence"),
        "{out}"
    );
    assert_selective_core_eval_stdout_contains(
        src,
        "io:format(\"~p~n\", ['_script':run_nested_trait_and_config(unit)]), init:stop().",
        "43",
    );
}

#[test]
fn selective_core_lowers_dbg_intrinsic_with_direct_dictionary() {
    let out = emit_selective_core(
        r#"
fun main : Unit -> Unit
main () = dbg 42
"#,
    );
    assert!(
        out.contains("call 'std_int':'__dict_Std_Base_Debug_std_int_Std_Int_Int'"),
        "{out}"
    );
    assert!(out.contains("call 'erlang':'element'"), "{out}");
    assert!(out.contains("apply _DebugFn(42)"), "{out}");
    assert!(out.contains("call 'io':'format'"), "{out}");
    assert!(out.contains("'standard_error'"), "{out}");
}

#[test]
fn selective_core_lowers_named_record_field_access() {
    let out = emit_selective_core(
        r#"
record Point {
  x: Int,
  y: Int,
}

fun main : Unit -> Int
main () = {
  let p = Point { x: 3, y: 4 }
  p.x + p.y
}
"#,
    );
    assert!(out.contains("{'_script_Point', 3, 4}"), "{out}");
    assert!(out.contains("(2, P)"), "{out}");
    assert!(out.contains("(3, P)"), "{out}");
}

#[test]
fn selective_core_lowers_tuple_param_match() {
    let out = emit_selective_core(
        r#"
fun first : (Int, Int) -> Int
first (x, _) = x

fun main : Unit -> Int
main () = first (1, 2)
"#,
    );
    assert!(out.contains("'first'/1"), "{out}");
    assert!(out.contains("case {_Arg0} of"), "{out}");
    assert!(out.contains("<{{X, _W0}}>"), "{out}");
}

#[test]
fn selective_core_lowers_constructor_case_patterns() {
    let out = emit_selective_core(
        r#"
type Pick =
  | First Int
  | Second Int

fun score : Pick -> Int
score p = case p {
  First x -> x
  Second y -> y + 1
}

fun main : Unit -> Int
main () = score (Second 41)
"#,
    );
    assert!(out.contains("'score'/1"), "{out}");
    assert!(out.contains("'_script_First'"), "{out}");
    assert!(out.contains("'_script_Second'"), "{out}");
    assert!(out.contains("{'_script_Second', 41}"), "{out}");
    assert!(out.contains("apply 'score'/1(___anf_v0)"), "{out}");
}

#[test]
fn selective_core_lowers_imported_pure_direct_call() {
    let out = emit_selective_core(
        r#"
import Std.Maybe as Maybe

fun main : Unit -> Bool
main () = Maybe.is_just (Just 1)
"#,
    );
    assert!(out.contains("'main'/1"), "{out}");
    assert!(out.contains("{'std_maybe_Just', 1}"), "{out}");
    assert!(out.contains("call 'std_maybe':'is_just'"), "{out}");
    assert!(!out.contains("apply 'is_just'/1"), "{out}");
}

#[test]
fn selective_core_lowers_simple_yield_cps_island() {
    let src = r#"
effect Log {
  fun log : String -> Unit
}

pub fun do_log : Unit -> Unit needs {Log}
do_log () = log! "hello"

fun main : Unit -> Unit
main () = ()
"#;
    let out = emit_selective_core(src);
    assert!(out.contains("module '_script' ['do_log'/3"), "{out}");
    assert!(out.contains("'do_log'/3"), "{out}");
    assert!(!out.contains("__saga_direct_do_log"), "{out}");
    assert!(
        out.contains("call 'std_evidence_bridge':'find_evidence'"),
        "{out}"
    );
    assert!(out.contains("call 'erlang':'element'"), "{out}");
    assert!(out.contains("_Evidence, _ReturnK"), "{out}");
    assert_selective_core_compiles(src);
}

#[test]
fn selective_core_lowers_yield_then_return_cps_island() {
    let src = r#"
effect Log {
  fun log : String -> Unit
}

pub fun log_then_answer : Unit -> Int needs {Log}
log_then_answer () = {
  let _ignored = log! "hello"
  42
}

fun main : Unit -> Unit
main () = ()
"#;
    let out = emit_selective_core(src);
    assert!(out.contains("'log_then_answer'/3"), "{out}");
    assert!(!out.contains("__saga_direct_log_then_answer"), "{out}");
    assert!(
        out.contains("call 'std_evidence_bridge':'find_evidence'"),
        "{out}"
    );
    assert!(out.contains("fun (_CpsBindArg0) ->"), "{out}");
    assert!(out.contains("let <__ignored>"), "{out}");
    assert!(out.contains("apply _ReturnK(42)"), "{out}");
    assert_selective_core_compiles(src);
}

#[test]
fn selective_core_lowers_yield_result_used_cps_island() {
    let src = r#"
effect ReadInt {
  fun read : Unit -> Int
}

pub fun read_plus_one : Unit -> Int needs {ReadInt}
read_plus_one () = {
  let value = read! ()
  value + 1
}

fun main : Unit -> Unit
main () = ()
"#;
    let out = emit_selective_core(src);
    assert!(out.contains("'read_plus_one'/3"), "{out}");
    assert!(!out.contains("__saga_direct_read_plus_one"), "{out}");
    assert!(
        out.contains("call 'std_evidence_bridge':'find_evidence'"),
        "{out}"
    );
    assert!(out.contains("fun (_CpsBindArg0) ->"), "{out}");
    assert!(out.contains("let <Value>"), "{out}");
    assert!(out.contains("apply _ReturnK(call 'erlang':'+'"), "{out}");
    assert_selective_core_compiles(src);
}

#[test]
fn selective_core_lowers_local_cps_helper_call_in_cps_island() {
    let src = r#"
effect ReadInt {
  fun read : Unit -> Int
}

fun read_value : Unit -> Int needs {ReadInt}
read_value () = read! ()

pub fun read_plus_two : Unit -> Int needs {ReadInt}
read_plus_two () = {
  let value = read_value ()
  value + 2
}

fun main : Unit -> Unit
main () = ()
"#;
    let out = emit_selective_core(src);
    assert!(out.contains("'read_value'/3"), "{out}");
    assert!(out.contains("'read_plus_two'/3"), "{out}");
    assert!(
        out.contains("apply 'read_value'/3('unit', _Evidence, fun (_CpsBindArg0) ->"),
        "{out}"
    );
    assert!(out.contains("let <Value>"), "{out}");
    assert!(out.contains("apply _ReturnK(call 'erlang':'+'"), "{out}");
    assert_selective_core_compiles(src);
}

#[test]
fn selective_core_lowers_if_in_cps_island() {
    let src = r#"
effect ReadInt {
  fun read : Unit -> Int
}

pub fun maybe_read : Bool -> Int needs {ReadInt}
maybe_read use_read =
  if use_read then read! () else 0

fun main : Unit -> Unit
main () = ()
"#;
    let out = emit_selective_core(src);
    assert!(out.contains("'maybe_read'/3"), "{out}");
    assert!(out.contains("case Use_read of"), "{out}");
    assert!(
        out.contains("call 'std_evidence_bridge':'find_evidence'"),
        "{out}"
    );
    assert!(out.contains("('unit', _Evidence, _ReturnK)"), "{out}");
    assert!(out.contains("apply _ReturnK(0)"), "{out}");
    assert_selective_core_compiles(src);
}

#[test]
fn selective_core_lowers_case_in_cps_island() {
    let src = r#"
effect ReadInt {
  fun read : Unit -> Int
}

type Choice = UseEffect | UseDefault

pub fun choose_read : Choice -> Int needs {ReadInt}
choose_read choice = case choice {
  UseEffect -> read! ()
  UseDefault -> 0
}

fun main : Unit -> Unit
main () = ()
"#;
    let out = emit_selective_core(src);
    assert!(out.contains("'choose_read'/3"), "{out}");
    assert!(out.contains("case Choice of"), "{out}");
    assert!(out.contains("'_script_UseEffect'"), "{out}");
    assert!(out.contains("'_script_UseDefault'"), "{out}");
    assert!(
        out.contains("call 'std_evidence_bridge':'find_evidence'"),
        "{out}"
    );
    assert!(out.contains("apply _ReturnK(0)"), "{out}");
    assert_selective_core_compiles(src);
}

#[test]
fn selective_core_direct_calls_static_tail_resumptive_handler_op() {
    let src = r#"
effect ReadInt {
  fun read : Unit -> Int
}

handler forty_one for ReadInt {
  read () = resume 41
}

fun main : Unit -> Int
main () = {
  let value = read! ()
  value + 1
} with forty_one
"#;
    let out = emit_selective_core(src);
    assert!(
        !out.contains("call 'std_evidence_bridge':'find_evidence'"),
        "{out}"
    );
    assert!(
        !out.contains("call 'std_evidence_bridge':'insert_canonical'"),
        "{out}"
    );
    assert!(out.contains("let <Value>"), "{out}");
    assert!(out.contains("apply fun (_CpsResult"), "{out}");
    assert!(out.contains("call 'erlang':'+'"), "{out}");
    assert_selective_core_eval_stdout_contains(
        src,
        "io:format(\"~p~n\", ['_script':main(unit)]), init:stop().",
        "42",
    );
}

#[test]
fn selective_core_direct_calls_static_handler_with_captured_runtime_value() {
    let src = r#"
effect SystemConfig {
  fun read_config : Unit -> Int
}

effect DbConfig {
  fun db_url : Unit -> Int
}

handler system_config for SystemConfig {
  read_config () = resume 41
}

fun main : Unit -> Int
main () = {
  let config = read_config! () with system_config
  {
    let value = db_url! ()
    value + 1
  } with {
    db_url () = resume config
  }
}
"#;
    let out = emit_selective_core(src);
    assert!(
        !out.contains("call 'std_evidence_bridge':'find_evidence'"),
        "{out}"
    );
    assert!(
        !out.contains("call 'std_evidence_bridge':'insert_canonical'"),
        "{out}"
    );
    assert!(out.contains("let <Config>"), "{out}");
    assert!(out.contains("let <Value>"), "{out}");
    assert!(out.contains("call 'erlang':'+'"), "{out}");
    assert_selective_core_eval_stdout_contains(
        src,
        "io:format(\"~p~n\", ['_script':main(unit)]), init:stop().",
        "42",
    );
}

#[test]
fn selective_core_specializes_local_cps_helper_under_static_handler() {
    let src = r#"
effect SystemConfig {
  fun read_config : Unit -> Int
}

effect DbConfig {
  fun db_url : Unit -> Int
}

handler system_config for SystemConfig {
  read_config () = resume 41
}

fun query : Unit -> Int needs {DbConfig}
query () = {
  let value = db_url! ()
  value + 1
}

fun main : Unit -> Int
main () = {
  let config = read_config! () with system_config
  query () with {
    db_url () = resume config
  }
}
"#;
    let out = emit_selective_core(src);
    assert!(!out.contains("apply 'query'/3"), "{out}");
    assert!(
        !out.contains("call 'std_evidence_bridge':'insert_canonical'"),
        "{out}"
    );
    assert!(out.contains("let <Config>"), "{out}");
    assert!(out.contains("let <Value>"), "{out}");
    assert!(out.contains("call 'erlang':'+'"), "{out}");
    assert_selective_core_eval_stdout_contains(
        src,
        "io:format(\"~p~n\", ['_script':main(unit)]), init:stop().",
        "42",
    );
}

#[test]
fn selective_core_lowers_effect_row_function_with_direct_body() {
    let out = emit_selective_core(
        r#"
effect Log {
  fun log : String -> Unit
}

pub fun may_log : Unit -> Int needs {Log}
may_log () = 42

pub fun use_may_log : Unit -> Int needs {Log}
use_may_log () = may_log ()

fun main : Unit -> Unit
main () = ()
"#,
    );
    assert!(
        out.contains("['__saga_direct_may_log'/1, 'may_log'/3"),
        "{out}"
    );
    assert!(
        out.contains("'__saga_direct_use_may_log'/1, 'use_may_log'/3"),
        "{out}"
    );
    assert!(out.contains("'__saga_direct_may_log'/1"), "{out}");
    assert!(out.contains("'may_log'/3"), "{out}");
    assert!(
        out.contains("apply '__saga_direct_may_log'/1(_Arg0)"),
        "{out}"
    );
    assert!(out.contains("'__saga_direct_use_may_log'/1"), "{out}");
    assert!(out.contains("'use_may_log'/3"), "{out}");
    assert!(
        out.contains("apply '__saga_direct_may_log'/1('unit')"),
        "{out}"
    );
    assert!(
        out.contains("apply '__saga_direct_use_may_log'/1(_Arg0)"),
        "{out}"
    );
    assert!(out.contains("apply _ReturnK"), "{out}");
    assert!(out.contains("42"), "{out}");
}

#[test]
fn selective_core_effect_row_adapter_compiles_and_runs_on_beam() {
    assert_selective_core_eval_stdout_contains(
        r#"
effect Log {
  fun log : String -> Unit
}

pub fun may_log : Unit -> Int needs {Log}
may_log () = 42

fun main : Unit -> Unit
main () = ()
"#,
        "io:format(\"~p~n\", ['_script':may_log(unit, [], fun(X) -> X end)]), init:stop().",
        "42",
    );
}

#[test]
fn selective_core_handler_finally_runs_after_resume_continuation() {
    let src = r#"
import Std.IO.Unsafe (print_stdout)

effect ReadInt {
  fun read : Unit -> Int
}

handler read_with_cleanup for ReadInt {
  read () = resume 41 finally {
    print_stdout "cleanup\n"
  }
}

fun main : Unit -> Unit
main () = {
  let value = {
    let read_value = read! ()
    print_stdout "body\n"
    read_value + 1
  } with read_with_cleanup

  if value == 42 then print_stdout "after\n"
  else print_stdout "bad\n"
}
"#;
    let out = emit_selective_core(src);
    assert!(
        out.contains("call 'std_evidence_bridge':'find_evidence'"),
        "{out}"
    );
    assert!(
        out.contains("call 'std_evidence_bridge':'insert_canonical'"),
        "{out}"
    );
    assert!(out.contains("_FinallyValue"), "{out}");
    assert!(out.contains("_FinallyCleanup"), "{out}");
    assert!(out.contains("_WithResult"), "{out}");
    assert_selective_core_compiles(src);
}

#[test]
fn selective_core_handler_finally_runs_after_abort_arm() {
    let src = r#"
import Std.IO.Unsafe (print_stdout)

effect Fail {
  fun fail : Unit -> Int
}

handler abort_with_cleanup for Fail {
  fail () = 0 finally {
    print_stdout "cleanup\n"
  }
}

fun main : Unit -> Unit
main () = {
  let value = {
    let unreachable = fail! ()
    print_stdout "body\n"
    unreachable + 1
  } with abort_with_cleanup

  if value == 0 then print_stdout "after\n"
  else print_stdout "bad\n"
}
"#;
    let out = emit_selective_core(src);
    assert!(
        out.contains("call 'std_evidence_bridge':'insert_canonical'"),
        "{out}"
    );
    assert!(out.contains("_FinallyValue"), "{out}");
    assert!(out.contains("_FinallyCleanup"), "{out}");
    assert!(out.contains("_WithResult"), "{out}");
    assert_selective_core_compiles(src);
}

#[test]
fn selective_core_lowers_higher_order_direct_callback() {
    let src = r#"
fun apply_it : (Int -> Int) -> Int
apply_it f = f 1

fun inc : Int -> Int
inc x = x + 1

fun main : Unit -> Int
main () = apply_it inc
"#;
    let out = emit_selective_core(src);
    assert!(out.contains("'apply_it'/1"), "{out}");
    assert!(out.contains("'inc'/1"), "{out}");
    assert!(out.contains("apply F(1)"), "{out}");
    assert!(out.contains("apply 'apply_it'/1('inc'/1)"), "{out}");
    assert_selective_core_compiles(src);
}

#[test]
fn selective_core_lowers_effectful_callback_value_adapter() {
    let src = r#"
effect ReadInt {
  fun read : Unit -> Int
}

fun read_value : Unit -> Int needs {ReadInt}
read_value () = read! ()

fun apply_eff : (Unit -> Int needs {ReadInt}) -> Int needs {ReadInt}
apply_eff f = {
  let g = f
  g ()
}

handler forty_one for ReadInt {
  read () = resume 41
}

fun main : Unit -> Int
main () = {
  let f = read_value
  let g = f
  apply_eff g
} with forty_one
"#;
    let out = emit_selective_core(src);
    assert!(out.contains("'apply_eff'/3"), "{out}");
    assert!(
        out.contains("apply G('unit', _Evidence, _ReturnK)"),
        "{out}"
    );
    assert!(out.contains("let <G>"), "{out}");
    assert!(out.contains("apply 'apply_eff'/3(fun (_CpsFnArg"), "{out}");
    assert!(out.contains("apply 'read_value'/3"), "{out}");
    assert!(!out.contains("make_fun"), "{out}");
    assert_selective_core_compiles(src);
}

#[test]
fn selective_core_lowers_branch_shaped_effectful_callback_value() {
    let src = r#"
effect ReadInt {
  fun read : Unit -> Int
}

fun read_value : Unit -> Int needs {ReadInt}
read_value () = read! ()

fun read_again : Unit -> Int needs {ReadInt}
read_again () = read! ()

fun apply_eff : (Unit -> Int needs {ReadInt}) -> Int needs {ReadInt}
apply_eff f = f ()

handler forty_one for ReadInt {
  read () = resume 41
}

fun main : Unit -> Int
main () = {
  let choose = 1 == 1
  let f = if choose then read_value else read_again
  apply_eff f
} with forty_one
"#;
    let out = emit_selective_core(src);
    assert!(out.contains("'apply_eff'/3"), "{out}");
    assert!(out.contains("let <F> =\n"), "{out}");
    assert!(out.contains("case Choose of"), "{out}");
    assert!(out.contains("apply 'read_value'/3"), "{out}");
    assert!(out.contains("apply 'read_again'/3"), "{out}");
    assert!(out.contains("apply 'apply_eff'/3(F"), "{out}");
    assert!(!out.contains("make_fun"), "{out}");
    assert_selective_core_compiles(src);
}

#[test]
fn selective_core_lowers_mixed_pure_and_effectful_if_callback_value() {
    let src = r#"
effect ReadInt {
  fun read : Unit -> Int
}

fun read_value : Unit -> Int needs {ReadInt}
read_value () = read! ()

fun pure_value : Unit -> Int
pure_value () = 41

fun apply_eff : (Unit -> Int needs {ReadInt}) -> Int needs {ReadInt}
apply_eff f = f ()

handler forty_one for ReadInt {
  read () = resume 41
}

fun main : Unit -> Int
main () = {
  let choose = 1 == 1
  let f = if choose then read_value else pure_value
  apply_eff f
} with forty_one
"#;
    let out = emit_selective_core(src);
    assert!(out.contains("'apply_eff'/3"), "{out}");
    assert!(out.contains("case Choose of"), "{out}");
    assert!(out.contains("apply 'read_value'/3"), "{out}");
    assert!(out.contains("fun (_PureCpsArg"), "{out}");
    assert!(out.contains("apply 'pure_value'/1"), "{out}");
    assert!(out.contains("apply _PureCpsK"), "{out}");
    assert!(out.contains("apply 'apply_eff'/3(F"), "{out}");
    assert!(!out.contains("make_fun"), "{out}");
    assert_selective_core_compiles(src);
}

#[test]
fn selective_core_lowers_pure_callback_in_effectful_callback_slot() {
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

fun main : Unit -> Int
main () = apply_eff pure_value with forty_one
"#;
    let out = emit_selective_core(src);
    assert!(out.contains("'apply_eff'/3"), "{out}");
    assert!(out.contains("'__saga_direct_hof_apply_eff'/1"), "{out}");
    assert!(out.contains("apply F('unit')"), "{out}");
    assert!(
        out.contains("apply '__saga_direct_hof_apply_eff'/1('pure_value'/1)"),
        "{out}"
    );
    assert!(!out.contains("fun (_PureCpsArg"), "{out}");
    assert!(!out.contains("apply _PureCpsK"), "{out}");
    assert!(!out.contains("make_fun"), "{out}");
    assert_selective_core_eval_stdout_contains(
        src,
        "io:format(\"~p~n\", ['_script':main(unit)]), init:stop().",
        "41",
    );
}

#[test]
fn selective_core_specializes_aliased_hof_in_effectful_callback_slot() {
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

fun main : Unit -> Int
main () = {
  let hof = apply_eff
  hof pure_value
} with forty_one
"#;
    let out = emit_selective_core(src);
    assert!(out.contains("'__saga_direct_hof_apply_eff'/1"), "{out}");
    assert!(
        out.contains("apply '__saga_direct_hof_apply_eff'/1('pure_value'/1)"),
        "{out}"
    );
    assert!(!out.contains("fun (_PureCpsArg"), "{out}");
    assert!(!out.contains("make_fun"), "{out}");
    assert_selective_core_eval_stdout_contains(
        src,
        "io:format(\"~p~n\", ['_script':main(unit)]), init:stop().",
        "41",
    );
}

#[test]
fn selective_core_specializes_inline_handled_callback_in_effectful_callback_slot() {
    let src = r#"
effect ReadInt {
  fun read : Unit -> Int
}

fun apply_eff : (Unit -> Int needs {ReadInt}) -> Int needs {ReadInt}
apply_eff f = f ()

handler forty_one for ReadInt {
  read () = resume 41
}

fun main : Unit -> Int
main () =
  apply_eff (fun () -> read! () with forty_one) with forty_one
"#;
    let out = emit_selective_core(src);
    assert!(out.contains("'__saga_direct_hof_apply_eff'/1"), "{out}");
    assert!(
        out.contains("apply '__saga_direct_hof_apply_eff'/1(fun (_Arg0) ->"),
        "{out}"
    );
    assert!(!out.contains("fun (_PureCpsArg"), "{out}");
    assert!(!out.contains("apply _PureCpsK"), "{out}");
    assert_selective_core_eval_stdout_contains(
        src,
        "io:format(\"~p~n\", ['_script':main(unit)]), init:stop().",
        "41",
    );
}

#[test]
fn selective_core_specializes_handled_callback_in_effectful_callback_slot() {
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

fun main : Unit -> Int
main () = apply_eff handled_value with forty_one
"#;
    let out = emit_selective_core(src);
    assert!(out.contains("'handled_value'/1"), "{out}");
    assert!(out.contains("'__saga_direct_hof_apply_eff'/1"), "{out}");
    assert!(
        out.contains("apply '__saga_direct_hof_apply_eff'/1('handled_value'/1)"),
        "{out}"
    );
    assert!(!out.contains("fun (_PureCpsArg"), "{out}");
    assert_selective_core_eval_stdout_contains(
        src,
        "io:format(\"~p~n\", ['_script':main(unit)]), init:stop().",
        "41",
    );
}

#[test]
fn selective_core_lowers_effectful_lambda_as_cps_callback_arg() {
    let src = r#"
effect ReadInt {
  fun read : Unit -> Int
}

handler forty_one for ReadInt {
  read () = resume 41
}

fun apply_eff : (Unit -> Int needs {ReadInt}) -> Int needs {ReadInt}
apply_eff f = f ()

pub fun run_lambda_arg : Unit -> Int
run_lambda_arg () =
  apply_eff (fun () -> read! () + 1) with forty_one

fun main : Unit -> Unit
main () = ()
"#;

    let out = emit_selective_core(src);
    assert!(out.contains("_LambdaEvidence"), "{out}");
    assert!(out.contains("_LambdaK"), "{out}");
    assert!(out.contains("call 'erlang':'+'"), "{out}");
    assert!(
        !out.contains("apply '__saga_direct_hof_apply_eff'/1(fun (_Arg0) ->"),
        "{out}"
    );
    assert_selective_core_eval_stdout_contains(
        src,
        "io:format(\"~p~n\", ['_script':run_lambda_arg(unit)]), init:stop().",
        "42",
    );
}

#[test]
fn selective_core_lowers_let_bound_effectful_lambda_cps_value() {
    let src = r#"
effect ReadInt {
  fun read : Unit -> Int
}

handler forty_one for ReadInt {
  read () = resume 41
}

fun apply_eff : (Unit -> Int needs {ReadInt}) -> Int needs {ReadInt}
apply_eff f = f ()

pub fun run_bound_lambda : Unit -> Int
run_bound_lambda () = {
  let f = fun () -> read! () + 1
  apply_eff f
} with forty_one

fun main : Unit -> Unit
main () = ()
"#;

    let out = emit_selective_core(src);
    assert!(out.contains("let <F>"), "{out}");
    assert!(out.contains("_LambdaEvidence"), "{out}");
    assert!(out.contains("apply F('unit', _Evidence"), "{out}");
    assert_selective_core_eval_stdout_contains(
        src,
        "io:format(\"~p~n\", ['_script':run_bound_lambda(unit)]), init:stop().",
        "42",
    );
}

#[test]
fn selective_core_lowers_lambda_headed_cps_call() {
    let src = r#"
effect ReadInt {
  fun read : Unit -> Int
}

handler forty_one for ReadInt {
  read () = resume 41
}

pub fun run_lambda_head : Unit -> Int
run_lambda_head () =
  (fun () -> read! () + 1) () with forty_one

fun main : Unit -> Unit
main () = ()
"#;

    let out = emit_selective_core(src);
    assert!(out.contains("_LambdaEvidence"), "{out}");
    assert!(out.contains("apply _LambdaK"), "{out}");
    assert_selective_core_eval_stdout_contains(
        src,
        "io:format(\"~p~n\", ['_script':run_lambda_head(unit)]), init:stop().",
        "42",
    );
}

#[test]
#[should_panic(
    expected = "CPS-shaped function 'send_callback' is not lowered by selective-core yet"
)]
fn selective_core_rejects_cps_callback_value_as_yield_argument() {
    let _ = emit_selective_core(
        r#"
effect ReadInt {
  fun read : Unit -> Int
}

effect Sink {
  fun send : (Unit -> Int needs {ReadInt}) -> Unit
}

fun read_value : Unit -> Int needs {ReadInt}
read_value () = read! ()

pub fun send_callback : Unit -> Unit needs {ReadInt, Sink}
send_callback () = {
  let f = read_value
  send! f
}

fun main : Unit -> Unit
main () = ()
"#,
    );
}

#[test]
#[should_panic(expected = "direct function 'store_tuple' is outside the current direct subset")]
fn selective_core_rejects_cps_callback_value_in_tuple_storage() {
    let _ = emit_selective_core(
        r#"
effect ReadInt {
  fun read : Unit -> Int
}

fun read_value : Unit -> Int needs {ReadInt}
read_value () = read! ()

pub fun store_tuple : Unit -> (Unit -> Int needs {ReadInt}, Int)
store_tuple () = (read_value, 1)

fun main : Unit -> Unit
main () = ()
"#,
    );
}

#[test]
#[should_panic(expected = "direct function 'store_record' is outside the current direct subset")]
fn selective_core_rejects_cps_callback_value_in_record_storage() {
    let _ = emit_selective_core(
        r#"
effect ReadInt {
  fun read : Unit -> Int
}

record CallbackBox {
  cb: Unit -> Int needs {ReadInt},
  n: Int,
}

fun read_value : Unit -> Int needs {ReadInt}
read_value () = read! ()

pub fun store_record : Unit -> CallbackBox
store_record () = CallbackBox { cb: read_value, n: 1 }

fun main : Unit -> Unit
main () = ()
"#,
    );
}

#[test]
#[should_panic(
    expected = "direct function 'store_constructor' is outside the current direct subset"
)]
fn selective_core_rejects_cps_callback_value_in_constructor_storage() {
    let _ = emit_selective_core(
        r#"
effect ReadInt {
  fun read : Unit -> Int
}

type CallbackBox = CallbackBox(Unit -> Int needs {ReadInt})

fun read_value : Unit -> Int needs {ReadInt}
read_value () = read! ()

pub fun store_constructor : Unit -> CallbackBox
store_constructor () = CallbackBox(read_value)

fun main : Unit -> Unit
main () = ()
"#,
    );
}

#[test]
#[should_panic(
    expected = "CPS-shaped function 'resume_callback' is not lowered by selective-core yet"
)]
fn selective_core_rejects_cps_callback_value_as_resume_value() {
    let _ = emit_selective_core(
        r#"
effect ReadInt {
  fun read : Unit -> Int
}

effect AskCallback {
  fun ask : Unit -> (Unit -> Int needs {ReadInt})
}

fun read_value : Unit -> Int needs {ReadInt}
read_value () = read! ()

pub fun resume_callback : Unit -> Unit -> Int needs {ReadInt}
resume_callback () = ask! () with {
  ask () = resume read_value
}

fun main : Unit -> Unit
main () = ()
"#,
    );
}

#[test]
#[should_panic(
    expected = "CPS-shaped function 'return_callback' is not lowered by selective-core yet"
)]
fn selective_core_rejects_cps_callback_value_in_handler_return_clause() {
    let _ = emit_selective_core(
        r#"
effect ReadInt {
  fun read : Unit -> Int
}

fun read_value : Unit -> Int needs {ReadInt}
read_value () = read! ()

pub fun return_callback : Unit -> (Unit -> Int needs {ReadInt})
return_callback () = {
  let _ = read! ()
  read_value
} with {
  read () = resume 1
  return value = value
}

fun main : Unit -> Unit
main () = ()
"#,
    );
}

#[test]
fn selective_core_lowers_case_shaped_effectful_callback_value() {
    let src = r#"
effect ReadInt {
  fun read : Unit -> Int
}

fun read_value : Unit -> Int needs {ReadInt}
read_value () = read! ()

fun read_again : Unit -> Int needs {ReadInt}
read_again () = read! ()

fun apply_eff : (Unit -> Int needs {ReadInt}) -> Int needs {ReadInt}
apply_eff f = f ()

handler forty_one for ReadInt {
  read () = resume 41
}

fun main : Unit -> Int
main () = {
  let choose = 1 == 1
  let f = case choose {
    True -> read_value
    False -> read_again
  }
  apply_eff f
} with forty_one
"#;
    let out = emit_selective_core(src);
    assert!(out.contains("'apply_eff'/3"), "{out}");
    assert!(out.contains("let <F> =\n"), "{out}");
    assert!(out.contains("case Choose of"), "{out}");
    assert!(out.contains("apply 'read_value'/3"), "{out}");
    assert!(out.contains("apply 'read_again'/3"), "{out}");
    assert!(out.contains("apply 'apply_eff'/3(F"), "{out}");
    assert!(!out.contains("make_fun"), "{out}");
    assert_selective_core_compiles(src);
}

#[test]
fn selective_core_lowers_mixed_pure_and_effectful_case_callback_value() {
    let src = r#"
effect ReadInt {
  fun read : Unit -> Int
}

fun read_value : Unit -> Int needs {ReadInt}
read_value () = read! ()

fun pure_value : Unit -> Int
pure_value () = 41

fun apply_eff : (Unit -> Int needs {ReadInt}) -> Int needs {ReadInt}
apply_eff f = f ()

handler forty_one for ReadInt {
  read () = resume 41
}

fun main : Unit -> Int
main () = {
  let choose = 1 == 1
  let f = case choose {
    True -> read_value
    False -> pure_value
  }
  apply_eff f
} with forty_one
"#;
    let out = emit_selective_core(src);
    assert!(out.contains("'apply_eff'/3"), "{out}");
    assert!(out.contains("case Choose of"), "{out}");
    assert!(out.contains("apply 'read_value'/3"), "{out}");
    assert!(out.contains("fun (_PureCpsArg"), "{out}");
    assert!(out.contains("apply 'pure_value'/1"), "{out}");
    assert!(out.contains("apply _PureCpsK"), "{out}");
    assert!(out.contains("apply 'apply_eff'/3(F"), "{out}");
    assert!(!out.contains("make_fun"), "{out}");
    assert_selective_core_compiles(src);
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
        out.contains("'build_msg'/3"),
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
        out.contains("'build_msg'/3"),
        "expected aliased effectful function ref to use lowered arity\n{out}"
    );
    assert!(
        !out.contains("'build_msg'/1"),
        "aliased effectful function ref used source arity instead of lowered arity\n{out}"
    );
}

#[test]
fn effectful_callbacks_in_lists_get_evidence_threaded() {
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
        out.contains("fun (_Arg0, _Evidence, _ReturnK) ->"),
        "expected list callback lambda to receive threaded evidence\n{out}"
    );
}

#[test]
fn effectful_callbacks_in_records_get_evidence_threaded() {
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
        out.contains("fun (_Arg0, _Evidence, _ReturnK) ->"),
        "expected record-contained callback lambda to receive threaded evidence\n{out}"
    );
}

#[test]
fn effectful_callbacks_in_adts_get_evidence_threaded() {
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
        out.contains("fun (_Arg0, _Evidence, _ReturnK) ->"),
        "expected ADT-contained callback lambda to receive threaded evidence\n{out}"
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
        out.contains("'build_msg'/3"),
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
        out.contains("'count_down'/3"),
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
    // Uniform CPS lowers `main ()` as `(unit, evidence, return_k)`.
    assert_contains("main () = 42", "'main'/3");
}

#[test]
fn fun_arity_one() {
    assert_contains("double x = x + x", "'double'/3");
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
    // `Nothing` -> {'std_maybe_Nothing'} (tagged 1-tuple)
    assert_contains("main () = Nothing", "{'std_maybe_Nothing'}");
}

#[test]
fn just_is_tagged_tuple() {
    // `Just(42)` -> {'std_maybe_Just', 42} (tagged tuple)
    let out = emit("main () = Just(42)");
    assert!(out.contains("42"), "missing value\n{out}");
    assert!(out.contains("'std_maybe_Just'"), "missing just tag\n{out}");
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
    // Just(v) lowers to {'std_maybe_Just', v}, Nothing to {'std_maybe_Nothing'}.
    // Arms stay in source order -- no reordering needed.
    let src = "
unwrap opt = case opt {
  Just(v) -> v
  Nothing -> 0
}
";
    let out = emit(src);
    assert!(
        out.contains("'std_maybe_Nothing'"),
        "missing nothing pattern for Nothing\n{out}"
    );
    assert!(
        out.contains("'std_maybe_Just'"),
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
    // The result should be a tuple preserving the original tag and updated fields.
    assert!(
        out.contains("{call 'erlang':'element'"),
        "expected tuple construction preserving runtime tag\n{out}"
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
        let needle = format!("apply '{guard_fn}'/3(");
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

// Stdlib conversion and dictionary behavior is covered by the stdlib/e2e
// suites. These isolated codegen tests intentionally do not compile imported
// stdlib modules into a full CodegenContext, so they are the wrong harness for
// asserting imported @external lowering.

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
    // Wrapper should be exported under the uniform CPS ABI.
    assert!(
        out.contains("'reverse'/3"),
        "Expected reverse/3 export in:\n{out}"
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
        out.contains("'empty'/3"),
        "Expected external wrapper to use uniform CPS arity\n{out}"
    );
    assert!(
        out.contains("call 'maps':'new'"),
        "Expected wrapper body to call maps:new\n{out}"
    );
}

#[test]
fn external_fun_returning_maybe() {
    // The pattern match should use the new stdlib Maybe tags.
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
        out.contains("'std_maybe_Just'"),
        "Expected just tag for Just pattern in:\n{out}"
    );
    assert!(
        out.contains("'std_maybe_Nothing'"),
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

// -----------------------------------------------------------------------
// Phase 1, step 8 — new-path wiring tests.
//
// The new path is active in `emit_module_with_context`; these tests keep
// focused coverage for the entry-point wiring that originally guarded the
// path switch.
// -----------------------------------------------------------------------

fn check_program(src: &str) -> (crate::ast::Program, crate::typechecker::CheckResult) {
    let tokens = Lexer::new(src).lex().expect("lex error");
    let mut program = Parser::new(tokens).parse_program().expect("parse error");
    derive::expand_derives(&mut program, &derive::ImportedDecls::empty());
    desugar::desugar_program(&mut program);
    let mut checker = typechecker::Checker::with_prelude(None).expect("prelude error");
    let result = checker.check_program(&mut program);
    assert!(!result.has_errors(), "Type errors: {:?}", result.errors());
    let elaborated = elaborate::elaborate(&program, &result);
    (elaborated, result)
}

#[test]
fn build_effect_ops_table_includes_local_and_qualified_keys() {
    let src = "effect Log {\n  fun log : (msg: String) -> Unit\n  fun warn : (msg: String) -> Unit\n}\n\nmain () = ()";
    let (_, result) = check_program(src);
    let table = super::build_effect_ops_table(&result);
    // The effect is declared in the script body, source_module is None →
    // only the bare key is present.
    let ops = table
        .map
        .get("Log")
        .expect("expected `Log` entry in effect ops table");
    assert_eq!(ops, &vec!["log".to_string(), "warn".to_string()]);
}

#[test]
fn build_effect_ops_table_ops_sorted_alphabetically() {
    let src = "effect E {\n  fun z : Unit -> Unit\n  fun a : Unit -> Unit\n  fun m : Unit -> Unit\n}\n\nmain () = ()";
    let (_, result) = check_program(src);
    let table = super::build_effect_ops_table(&result);
    let ops = table.map.get("E").expect("E missing");
    assert_eq!(
        ops,
        &vec!["a".to_string(), "m".to_string(), "z".to_string()]
    );
}

#[test]
fn build_effect_ops_table_includes_imported_module_effect_defs() {
    let src = r#"import Std.Fail (Fail)

fun boom : Unit -> Int needs {Fail String}
boom () = fail! "boom"

main () = ()
"#;
    let (_, result) = check_program(src);
    let table = super::build_effect_ops_table(&result);
    assert_eq!(
        table.map.get("Std.Fail.Fail"),
        Some(&vec!["fail".to_string()])
    );
}

#[test]
fn module_effect_defs_can_extend_effect_ops_table_at_emit_boundary() {
    let mut map = std::collections::HashMap::new();
    let mut modules = std::collections::HashMap::new();
    modules.insert(
        "Dep.Effects".to_string(),
        crate::typechecker::ModuleCodegenInfo {
            effect_defs: vec![crate::typechecker::EffectDef {
                name: "Dep.Effects.Remote".to_string(),
                ops: vec![crate::typechecker::EffectOpDef {
                    name: "run".to_string(),
                    source_param_count: 1,
                    runtime_param_count: 1,
                    runtime_param_positions: vec![0],
                    param_absorbed_effects: std::collections::HashMap::new(),
                }],
                type_param_count: 0,
            }],
            ..Default::default()
        },
    );

    super::insert_module_effect_defs(&mut map, &modules);

    assert_eq!(
        map.get("Dep.Effects.Remote"),
        Some(&vec!["run".to_string()])
    );
}

#[test]
fn build_effect_info_populates_all_fields_from_check_result() {
    let src = "effect Log {\n  fun log : (msg: String) -> Unit\n}\n\nmain () = ()";
    let (_, result) = check_program(src);
    let ops_storage = super::build_effect_ops_table(&result);
    let handler_effects_storage = super::build_handler_effects(&result);
    let let_handler_effects_storage = super::build_let_handler_effects(&result);
    let info = super::build_effect_info(
        &result,
        &result,
        &ops_storage,
        &handler_effects_storage,
        &let_handler_effects_storage,
    );

    // type_at_node and fun_effects come from check_result.
    assert!(std::ptr::eq(info.type_at_node, &result.type_at_node));
    assert!(std::ptr::eq(info.fun_effects, &result.fun_effects));
    assert!(std::ptr::eq(info.traits, &result.traits));
    assert!(std::ptr::eq(
        info.let_effect_bindings,
        &result.let_effect_bindings
    ));
    // effect_calls / handler_arms come from the (per-module) resolution.
    assert!(std::ptr::eq(
        info.effect_calls,
        &result.resolution.effect_calls
    ));
    assert!(std::ptr::eq(
        info.handler_arms,
        &result.resolution.handler_arms
    ));
    // effect_ops borrows from the supplied storage.
    assert!(std::ptr::eq(info.effect_ops, &ops_storage.map));
    // And actually carries the declared op.
    assert_eq!(info.effect_ops.get("Log"), Some(&vec!["log".to_string()]));
}

/// Smoke test the full new path on a trivial program. Kept as a default test
/// now that the new path is active.
#[test]
fn new_path_smoke_hello_world() {
    let src = "main () = ()";
    let (elaborated, result) = check_program(src);
    let ctx = super::CodegenContext {
        modules: std::collections::HashMap::new(),
        let_effect_bindings: result.let_effect_bindings.clone(),
        prelude_imports: result.prelude_imports.clone(),
    };
    let core = super::emit_module_via_new_path(
        "_script",
        &elaborated,
        &ctx,
        &result,
        None,
        Some("main"),
        &crate::compiler_options::CompileOptions::default(),
    )
    .core_src;
    assert!(
        core.contains("module '_script'"),
        "Core Erlang module header missing:\n{core}"
    );
    assert!(
        core.contains("__saga_initial_evidence"),
        "Bootstrap function should be emitted for entry-point module:\n{core}"
    );

    // erlc-accept check. Writes the .core to a tempdir and shells out to
    // erlc; skips silently if erlc isn't on PATH (sandbox / CI variant).
    if std::process::Command::new("erlc")
        .arg("--help")
        .output()
        .is_ok()
    {
        let tmp = std::env::temp_dir().join("saga-new-path-smoke");
        std::fs::create_dir_all(&tmp).unwrap();
        let core_path = tmp.join("_script.core");
        std::fs::write(&core_path, &core).unwrap();
        let out = std::process::Command::new("erlc")
            .arg("+from_core")
            .arg("-o")
            .arg(&tmp)
            .arg(&core_path)
            .output()
            .expect("erlc spawn");
        assert!(
            out.status.success(),
            "erlc rejected new-path output:\nstdout: {}\nstderr: {}\ncore: {}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr),
            core
        );
    }
}

/// Smoke test the new path on a program that has both a `main` fn and a
/// `val` whose body is a non-trivial pure computation (not just `Pure(atom)`
/// post-translation). Regression for the val identity-K wrapper fix —
/// `lower_val` must thread `lower_expr` through with a synthesized
/// `_ReturnK = fun(X) -> X` so `Bind` / `If` / etc. inside the body lower
/// cleanly.
#[test]
fn new_path_smoke_val_with_computation() {
    let src = "\
val answer = 1 + 2
main () = ()
";
    let (elaborated, result) = check_program(src);
    let ctx = super::CodegenContext {
        modules: std::collections::HashMap::new(),
        let_effect_bindings: result.let_effect_bindings.clone(),
        prelude_imports: result.prelude_imports.clone(),
    };
    let core = super::emit_module_via_new_path(
        "_script",
        &elaborated,
        &ctx,
        &result,
        None,
        Some("main"),
        &crate::compiler_options::CompileOptions::default(),
    )
    .core_src;
    assert!(
        core.contains("module '_script'"),
        "Core Erlang module header missing:\n{core}"
    );
    assert!(
        core.contains("'answer'/0"),
        "val 'answer' must be emitted as a /0 function:\n{core}"
    );

    if std::process::Command::new("erlc")
        .arg("--help")
        .output()
        .is_ok()
    {
        let tmp = std::env::temp_dir().join("saga-new-path-smoke-val");
        std::fs::create_dir_all(&tmp).unwrap();
        let core_path = tmp.join("_script.core");
        std::fs::write(&core_path, &core).unwrap();
        let out = std::process::Command::new("erlc")
            .arg("+from_core")
            .arg("-o")
            .arg(&tmp)
            .arg(&core_path)
            .output()
            .expect("erlc spawn");
        assert!(
            out.status.success(),
            "erlc rejected new-path val output:\nstdout: {}\nstderr: {}\ncore: {}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr),
            core
        );
    }
}
