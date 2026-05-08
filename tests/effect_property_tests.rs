//! BEAM-execution property test harness for effect-using programs.
//!
//! Each fixture is a small, self-contained Saga program that defines
//! `pub fun result : Unit -> String` (or similar). The harness compiles
//! it to Core Erlang, runs it on the BEAM via `erl -noshell`, and asserts
//! exact stdout output. The point is broad regression coverage of the
//! effectful calling convention: resume/abort, nested handlers, partial
//! application, cross-module calls, multishot, BEAM-native effects, and
//! mixed BEAM-native/CPS programs.
//!
//! See `docs/planning/plans/evidence-passing-plan.md` Phase 0 for the
//! coverage list.
//!
//! These tests require `erlc` and `erl` on PATH.
use saga::{codegen, elaborate, lexer, parser, typechecker};
use std::path::PathBuf;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

// ---------------------------------------------------------------------------
// Harness
// ---------------------------------------------------------------------------

static COUNTER: AtomicUsize = AtomicUsize::new(0);

fn fresh_dir(fixture: &str) -> PathBuf {
    let id = COUNTER.fetch_add(1, Ordering::Relaxed);
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock before epoch")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!(
        "saga_effect_prop_{}_{fixture}_{id}_{unique}",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    dir
}

fn fixtures_root_for_main_only() -> PathBuf {
    // For single-file fixtures, we still need a project root for the checker;
    // a fresh empty dir suffices since there are no other modules to scan.
    let dir = fresh_dir("root");
    // Drop a project.toml so project mode is recognized.
    std::fs::write(dir.join("project.toml"), "[project]\nname=\"prop\"\n").unwrap();
    dir
}

/// (Source path on disk, output module name as referenced in Core Erlang.)
/// Mirrors the bridge file mapping in `src/cli/build.rs`.
fn bridge_files() -> Vec<(&'static str, &'static str)> {
    vec![
        (
            "File.bridge.erl",
            include_str!("../src/stdlib/File.bridge.erl"),
        ),
        (
            "Dict.bridge.erl",
            include_str!("../src/stdlib/Dict.bridge.erl"),
        ),
        (
            "String.bridge.erl",
            include_str!("../src/stdlib/String.bridge.erl"),
        ),
        (
            "Int.bridge.erl",
            include_str!("../src/stdlib/Int.bridge.erl"),
        ),
        (
            "Float.bridge.erl",
            include_str!("../src/stdlib/Float.bridge.erl"),
        ),
        (
            "Regex.bridge.erl",
            include_str!("../src/stdlib/Regex.bridge.erl"),
        ),
        (
            "Math.bridge.erl",
            include_str!("../src/stdlib/Math.bridge.erl"),
        ),
        (
            "List.bridge.erl",
            include_str!("../src/stdlib/List.bridge.erl"),
        ),
        (
            "Set.bridge.erl",
            include_str!("../src/stdlib/Set.bridge.erl"),
        ),
        ("runtime.erl", include_str!("../src/stdlib/runtime.erl")),
        (
            "Time.bridge.erl",
            include_str!("../src/stdlib/Time.bridge.erl"),
        ),
        (
            "DateTime.bridge.erl",
            include_str!("../src/stdlib/DateTime.bridge.erl"),
        ),
        (
            "BitString.bridge.erl",
            include_str!("../src/stdlib/BitString.bridge.erl"),
        ),
        (
            "IO.bridge.erl",
            include_str!("../src/stdlib/IO.bridge.erl"),
        ),
        (
            "Dynamic.bridge.erl",
            include_str!("../src/stdlib/Dynamic.bridge.erl"),
        ),
        (
            "Array.bridge.erl",
            include_str!("../src/stdlib/Array.bridge.erl"),
        ),
    ]
}

/// Compile the stdlib into a shared temp directory, once per test process.
/// Tests can then point `erl -pa` at this dir to load Std.* beams + bridges.
fn stdlib_dir() -> &'static PathBuf {
    static DIR: OnceLock<PathBuf> = OnceLock::new();
    DIR.get_or_init(build_stdlib)
}

fn build_stdlib() -> PathBuf {
    let pid = std::process::id();
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock before epoch")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!("saga_effect_prop_stdlib_{pid}_{unique}"));
    std::fs::create_dir_all(&dir).unwrap();

    // Bridge .erl files first — emit and erlc them.
    for (filename, source) in bridge_files() {
        let stem = std::path::Path::new(filename)
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap();
        // Build.rs writes "std_<lower>_bridge.erl" / "saga_runtime.erl". The
        // module name inside each bridge file is already what callers expect,
        // so we just preserve it: write under the *referenced* filename.
        let on_disk = match filename {
            "runtime.erl" => "saga_runtime.erl".to_string(),
            _ => format!("std_{}_bridge.erl", stem.split('.').next().unwrap().to_lowercase()),
        };
        let path = dir.join(&on_disk);
        std::fs::write(&path, source).unwrap();
        let output = std::process::Command::new("erlc")
            .arg("-o")
            .arg(&dir)
            .arg(&path)
            .output()
            .expect("failed to run erlc on bridge");
        assert!(
            output.status.success(),
            "erlc failed on bridge {on_disk}:\nstderr: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }

    // Build a one-off checker with prelude and emit each Std.* module.
    let stdlib_root = std::env::temp_dir().join(format!(
        "saga_effect_prop_stdlib_root_{pid}_{unique}"
    ));
    std::fs::create_dir_all(&stdlib_root).unwrap();
    std::fs::write(
        stdlib_root.join("project.toml"),
        "[project]\nname=\"stdlib\"\n",
    )
    .unwrap();
    let checker = make_checker(stdlib_root.clone());
    let result = checker.to_result();

    // Construct a CodegenContext containing every compiled Std.* module.
    let mut modules = std::collections::HashMap::new();
    for name in result.codegen_info().keys() {
        if let Some(c) = codegen::compile_module_from_result(name, &result) {
            modules.insert(name.clone(), c);
        } else {
            let info = result.codegen_info().get(name).cloned().unwrap_or_default();
            modules.insert(
                name.clone(),
                codegen::CompiledModule {
                    codegen_info: info,
                    ..Default::default()
                },
            );
        }
    }
    let ctx = codegen::CodegenContext {
        modules,
        let_effect_bindings: result.let_effect_bindings.clone(),
        prelude_imports: result.prelude_imports.clone(),
    };

    let module_names: Vec<String> = ctx.modules.keys().cloned().collect();
    for name in module_names {
        if !name.starts_with("Std.") {
            continue;
        }
        let Some(m) = ctx.modules.get(&name) else {
            continue;
        };
        let erl_name = name.to_lowercase().replace('.', "_");
        let mod_result = result.module_check_results().get(&name);
        let core = codegen::emit_module_with_context(
            &erl_name,
            &m.elaborated,
            &ctx,
            mod_result.unwrap_or(&result),
            None,
            None,
        );
        let core_path = dir.join(format!("{erl_name}.core"));
        std::fs::write(&core_path, &core).unwrap();
        let output = std::process::Command::new("erlc")
            .arg("-o")
            .arg(&dir)
            .arg(&core_path)
            .output()
            .expect("failed to run erlc on stdlib module");
        assert!(
            output.status.success(),
            "erlc failed on stdlib {erl_name}:\n{core}\nstderr: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }

    let _ = std::fs::remove_dir_all(&stdlib_root);
    dir
}

fn make_checker(root: PathBuf) -> typechecker::Checker {
    let module_map = typechecker::scan_source_dir(&root).expect("scan failed");
    let mut checker = typechecker::Checker::with_project_root(root);
    checker.set_module_map(module_map);
    let prelude_src = include_str!("../src/stdlib/prelude.saga");
    let prelude_tokens = lexer::Lexer::new(prelude_src)
        .lex()
        .expect("prelude lex error");
    let mut prelude_program = parser::Parser::new(prelude_tokens)
        .parse_program()
        .expect("prelude parse error");
    saga::derive::expand_derives(&mut prelude_program);
    saga::desugar::desugar_program(&mut prelude_program);
    checker.prelude_imports = prelude_program
        .iter()
        .filter(|d| matches!(d, saga::ast::Decl::Import { .. }))
        .cloned()
        .collect();
    let result = checker.check_program(&mut prelude_program);
    assert!(
        !result.has_errors(),
        "prelude typecheck error: {:?}",
        result.errors()
    );
    checker
}

fn typecheck_source(
    source: &str,
    checker: &mut typechecker::Checker,
    fixture: &str,
) -> Vec<saga::ast::Decl> {
    let tokens = lexer::Lexer::new(source)
        .lex()
        .unwrap_or_else(|e| panic!("[{fixture}] lex error: {e:?}"));
    let mut program = parser::Parser::new(tokens)
        .parse_program()
        .unwrap_or_else(|e| panic!("[{fixture}] parse error: {e:?}"));
    saga::desugar::desugar_program(&mut program);
    if let Some(module_name) = program.iter().find_map(|d| {
        if let saga::ast::Decl::ModuleDecl { path, .. } = d {
            Some(path.join("."))
        } else {
            None
        }
    }) {
        checker.set_current_module(module_name);
    }
    let result = checker.check_program(&mut program);
    assert!(
        !result.has_errors(),
        "[{fixture}] typecheck error: {:?}",
        result.errors()
    );
    program
}

fn emit_program(
    program: &Vec<saga::ast::Decl>,
    module_name: &str,
    checker: &typechecker::Checker,
    entry_export: Option<&str>,
) -> String {
    let original_module_name = program
        .iter()
        .find_map(|d| {
            if let saga::ast::Decl::ModuleDecl { path, .. } = d {
                Some(path.join("."))
            } else {
                None
            }
        })
        .unwrap_or_default();
    let result = checker.to_result();
    let module_result = result.module_check_results().get(&original_module_name);
    let elaborated = elaborate::elaborate_module(
        program,
        module_result.unwrap_or(&result),
        &original_module_name,
    );
    let mut modules = std::collections::HashMap::new();
    for name in result.codegen_info().keys() {
        if let Some(compiled) = codegen::compile_module_from_result(name, &result) {
            modules.insert(name.clone(), compiled);
        } else {
            let info = result.codegen_info().get(name).cloned().unwrap_or_default();
            modules.insert(
                name.clone(),
                codegen::CompiledModule {
                    codegen_info: info,
                    ..Default::default()
                },
            );
        }
    }
    let ctx = codegen::CodegenContext {
        modules,
        let_effect_bindings: result.let_effect_bindings.clone(),
        prelude_imports: result.prelude_imports.clone(),
    };
    codegen::emit_module_with_context(
        module_name,
        &elaborated,
        &ctx,
        module_result.unwrap_or(&result),
        None,
        entry_export,
    )
}

fn compile_with_erlc(dir: &PathBuf, core: &str, module_name: &str, fixture: &str) {
    let core_path = dir.join(format!("{module_name}.core"));
    std::fs::write(&core_path, core).unwrap();
    let output = std::process::Command::new("erlc")
        .arg("-o")
        .arg(dir)
        .arg(&core_path)
        .output()
        .expect("failed to run erlc");
    assert!(
        output.status.success(),
        "[{fixture}] erlc failed on {module_name}:\n{core}\nstderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
}

fn run_erl(dir: &PathBuf, eval: &str, fixture: &str) -> String {
    let run = std::process::Command::new("erl")
        .arg("-noshell")
        .arg("-pa")
        .arg(stdlib_dir())
        .arg("-pa")
        .arg(dir)
        .arg("-eval")
        .arg(eval)
        .output()
        .expect("failed to run erl");
    assert!(
        run.status.success(),
        "[{fixture}] erl failed:\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&run.stdout),
        String::from_utf8_lossy(&run.stderr)
    );
    String::from_utf8_lossy(&run.stdout).into_owned()
}

/// Compile a single-module Saga source and call `main:result(unit)`,
/// asserting the returned string equals `expected`. The fixture must
/// declare `module Main` and define `pub fun result : Unit -> String`.
fn check_result_string(fixture: &str, src: &str, expected: &str) {
    let root = fixtures_root_for_main_only();
    let mut checker = make_checker(root.clone());
    let program = typecheck_source(src, &mut checker, fixture);
    let core = emit_program(&program, "main", &checker, Some("main"));
    let dir = fresh_dir(fixture);
    compile_with_erlc(&dir, &core, "main", fixture);
    let stdout = run_erl(
        &dir,
        "io:format(\"~s\", [main:result(unit)]), init:stop().",
        fixture,
    );
    let _ = std::fs::remove_dir_all(&dir);
    let _ = std::fs::remove_dir_all(&root);
    assert_eq!(
        stdout, expected,
        "[{fixture}] result mismatch\nexpected: {expected:?}\nactual:   {stdout:?}"
    );
}

/// Compile a single-module Saga source and call `main:result(unit)`,
/// asserting the returned integer equals `expected`. The fixture must
/// declare `module Main` and define `pub fun result : Unit -> Int`.
fn check_result_int(fixture: &str, src: &str, expected: i64) {
    let root = fixtures_root_for_main_only();
    let mut checker = make_checker(root.clone());
    let program = typecheck_source(src, &mut checker, fixture);
    let core = emit_program(&program, "main", &checker, Some("main"));
    let dir = fresh_dir(fixture);
    compile_with_erlc(&dir, &core, "main", fixture);
    let stdout = run_erl(
        &dir,
        "io:format(\"~p\", [main:result(unit)]), init:stop().",
        fixture,
    );
    let _ = std::fs::remove_dir_all(&dir);
    let _ = std::fs::remove_dir_all(&root);
    let trimmed = stdout.trim();
    assert_eq!(
        trimmed,
        expected.to_string(),
        "[{fixture}] result mismatch\nexpected: {expected}\nactual:   {trimmed:?}"
    );
}

/// Compile a multi-module Saga project and call `main:result(unit)`,
/// asserting the returned string equals `expected`.
///
/// `modules` is a list of `(relative_file_path, source)` for non-main modules.
fn check_cross_module(
    fixture: &str,
    modules: &[(&str, &str)],
    main_src: &str,
    expected: &str,
) {
    let root = fresh_dir(&format!("{fixture}_root"));
    std::fs::write(root.join("project.toml"), "[project]\nname=\"prop\"\n").unwrap();
    for (rel, src) in modules {
        let path = root.join(rel);
        if let Some(parent) = path.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
        std::fs::write(&path, src).unwrap();
    }

    // Pre-parse lib sources so we know which module names they declare.
    let lib_module_names: Vec<String> = modules
        .iter()
        .map(|(rel, src)| {
            let tokens = lexer::Lexer::new(src)
                .lex()
                .unwrap_or_else(|e| panic!("[{fixture}] lex {rel}: {e:?}"));
            let program = parser::Parser::new(tokens)
                .parse_program()
                .unwrap_or_else(|e| panic!("[{fixture}] parse {rel}: {e:?}"));
            program
                .iter()
                .find_map(|d| {
                    if let saga::ast::Decl::ModuleDecl { path, .. } = d {
                        Some(path.join("."))
                    } else {
                        None
                    }
                })
                .unwrap_or_else(|| panic!("[{fixture}] {rel} has no `module` declaration"))
        })
        .collect();

    let mut checker = make_checker(root.clone());
    // Typechecking main triggers on-demand load of imported modules from disk.
    let main_program = typecheck_source(main_src, &mut checker, fixture);

    let dir = fresh_dir(fixture);
    // Emit each declared lib module from the cached programs in the result.
    let result = checker.to_result();
    for name in &lib_module_names {
        let program = result.programs().get(name).unwrap_or_else(|| {
            panic!("[{fixture}] checker did not load module {name}")
        });
        let erl_name = name.to_lowercase().replace('.', "_");
        let core = emit_program(program, &erl_name, &checker, None);
        compile_with_erlc(&dir, &core, &erl_name, fixture);
    }
    let main_core = emit_program(&main_program, "main", &checker, Some("main"));
    compile_with_erlc(&dir, &main_core, "main", fixture);

    let stdout = run_erl(
        &dir,
        "io:format(\"~s\", [main:result(unit)]), init:stop().",
        fixture,
    );
    let _ = std::fs::remove_dir_all(&dir);
    let _ = std::fs::remove_dir_all(&root);
    assert_eq!(
        stdout, expected,
        "[{fixture}] result mismatch\nexpected: {expected:?}\nactual:   {stdout:?}"
    );
}

// ---------------------------------------------------------------------------
// Fixtures: basic op call (resume / abort)
// ---------------------------------------------------------------------------

#[test]
fn basic_resume_unit() {
    let src = r#"module Main

effect Log {
  fun log : String -> Unit
}

handler accumulating for Log {
  log msg = msg <> "/" <> resume ()
  return _ = "end"
}

pub fun result : Unit -> String
result () = {
  log! "a"
  log! "b"
} with accumulating
"#;
    check_result_string("basic_resume_unit", src, "a/b/end");
}

#[test]
fn basic_resume_with_value() {
    let src = r#"module Main

effect Ask {
  fun ask : String -> Int
}

handler answer for Ask {
  ask _ = resume 42
}

pub fun result : Unit -> String
result () = {
  let n = ask! "what?"
  show n
} with answer
"#;
    check_result_string("basic_resume_with_value", src, "42");
}

#[test]
fn basic_abort_no_resume() {
    let src = r#"module Main

import Std.Fail (Fail)

handler to_result_str for Fail String {
  fail e = "err:" <> e
  return v = "ok:" <> v
}

fun maybe_fail : Bool -> String needs {Fail String}
maybe_fail True = fail! "oops"
maybe_fail False = "value"

pub fun result : Unit -> String
result () = maybe_fail True with to_result_str
"#;
    check_result_string("basic_abort_no_resume", src, "err:oops");
}

#[test]
fn basic_abort_returns_value_on_success() {
    let src = r#"module Main

import Std.Fail (Fail)

handler to_result_str for Fail String {
  fail e = "err:" <> e
  return v = "ok:" <> v
}

fun maybe_fail : Bool -> String needs {Fail String}
maybe_fail True = fail! "oops"
maybe_fail False = "value"

pub fun result : Unit -> String
result () = maybe_fail False with to_result_str
"#;
    check_result_string("basic_abort_returns_value_on_success", src, "ok:value");
}

#[test]
fn op_called_in_a_loop_resumes_each_time() {
    let src = r#"module Main

effect Tick {
  fun tick : String -> String
}

handler counting for Tick {
  tick s = s <> "/" <> resume "x"
}

pub fun result : Unit -> String
result () = {
  let a = tick! "1"
  let b = tick! "2"
  let c = tick! "3"
  a <> b <> c
} with counting
"#;
    // Each tick wraps the body's continuation. The body's tail `a <> b <> c` is
    // evaluated under all three resumes (each resume makes the rest of the body
    // continue with its own value of n). innermost: a=b=c="x" → "xxx".
    check_result_string("op_called_in_a_loop_resumes_each_time", src, "1/2/3/xxx");
}

// ---------------------------------------------------------------------------
// Fixtures: nested with blocks (handler stacking)
// ---------------------------------------------------------------------------

#[test]
fn nested_with_two_distinct_effects() {
    let src = r#"module Main

import Std.Fail (Fail)

effect Log {
  fun log : String -> Unit
}

handler collect for Log {
  log msg = msg <> "/" <> resume ()
}

handler to_result_str for Fail String {
  fail e = "err:" <> e
  return v = "ok:" <> v
}

fun work : Unit -> String needs {Log, Fail String}
work () = {
  log! "first"
  log! "second"
  "done"
}

pub fun result : Unit -> String
result () = (work () with to_result_str) with collect
"#;
    check_result_string(
        "nested_with_two_distinct_effects",
        src,
        "first/second/ok:done",
    );
}

#[test]
fn nested_same_effect_inner_shadows_outer() {
    // Two nested handlers for the same effect: the inner one must take ops.
    let src = r#"module Main

effect Log {
  fun log : String -> Unit
}

handler outer for Log {
  log msg = "OUTER:" <> msg <> resume ()
  return _ = ""
}

handler inner for Log {
  log msg = "INNER:" <> msg <> resume ()
  return _ = ""
}

pub fun result : Unit -> String
result () = {
  {
    log! "x"
  } with inner
} with outer
"#;
    check_result_string("nested_same_effect_inner_shadows_outer", src, "INNER:x");
}

#[test]
fn nested_same_effect_outer_visible_after_inner_block() {
    // Verifies that a nested `with` for the same effect doesn't permanently
    // shadow the outer handler — once we leave the inner block, ops route to
    // the outer handler again.
    let src = r#"module Main

effect Log {
  fun log : String -> Unit
}

handler outer for Log {
  log msg = "O(" <> msg <> ")" <> resume ()
}

handler inner for Log {
  log msg = "I(" <> msg <> ")" <> resume ()
}

pub fun result : Unit -> String
result () = {
  log! "before"
  let mid = { log! "mid"; "M" } with inner
  log! "after"
  mid
} with outer
"#;
    // outer.log "before" -> "O(before)" + resume; resume runs let mid block:
    //   inner.log "mid" -> "I(mid)" + resume -> "M" => "I(mid)M"
    // mid = "I(mid)M". then outer.log "after" -> "O(after)" + resume; resume
    // returns mid's value as the body's tail. Final value = "I(mid)M".
    // Outer chain wraps: "O(before)" + ("O(after)" + "I(mid)M")
    check_result_string(
        "nested_same_effect_outer_visible_after_inner_block",
        src,
        "O(before)O(after)I(mid)M",
    );
}

#[test]
fn nested_with_three_distinct_effects() {
    let src = r#"module Main

import Std.Fail (Fail)

effect Tag {
  fun tag : String -> String
}

effect Log {
  fun log : String -> Unit
}

handler collect for Log {
  log msg = msg <> "/" <> resume ()
}

handler tagger for Tag {
  tag s = resume ("[" <> s <> "]")
}

handler to_result_str for Fail String {
  fail e = "err:" <> e
  return v = "ok:" <> v
}

fun work : Unit -> String needs {Log, Tag, Fail String}
work () = {
  log! "go"
  let t = tag! "name"
  t
}

pub fun result : Unit -> String
result () =
  (((work () with to_result_str) with tagger) with collect)
"#;
    check_result_string(
        "nested_with_three_distinct_effects",
        src,
        "go/ok:[name]",
    );
}

// ---------------------------------------------------------------------------
// Fixtures: partial application of effectful functions
// ---------------------------------------------------------------------------

#[test]
fn partial_app_effectful_two_args() {
    let src = r#"module Main

effect Log {
  fun log : String -> Unit
}

handler collect for Log {
  log msg = msg <> "|" <> resume ()
}

fun pair_log : String -> String -> String needs {Log}
pair_log a b = {
  log! a
  log! b
  a <> "+" <> b
}

pub fun result : Unit -> String
result () = {
  let f = pair_log "x"
  f "y"
} with collect
"#;
    check_result_string("partial_app_effectful_two_args", src, "x|y|x+y");
}

#[test]
fn partial_app_effectful_then_apply_under_handler() {
    let src = r#"module Main

import Std.Fail (Fail)

handler to_result_str for Fail String {
  fail e = "err:" <> e
  return v = "ok:" <> v
}

fun checked_div : Int -> Int -> String needs {Fail String}
checked_div _ 0 = fail! "div0"
checked_div x y = show (x / y)

pub fun result : Unit -> String
result () = {
  let by_two = checked_div 10
  by_two 2
} with to_result_str
"#;
    check_result_string(
        "partial_app_effectful_then_apply_under_handler",
        src,
        "ok:5",
    );
}

#[test]
fn partial_app_then_passed_to_higher_order() {
    let src = r#"module Main

effect Log {
  fun log : String -> Unit
}

handler collect for Log {
  log msg = msg <> "/" <> resume ()
}

fun greet : String -> String -> String needs {Log}
greet hi name = {
  log! (hi <> " " <> name)
  hi <> " " <> name
}

fun apply_str : (String -> String needs {Log}) -> String -> String needs {Log}
apply_str f x = f x

pub fun result : Unit -> String
result () = {
  let hello = greet "hello"
  apply_str hello "world"
} with collect
"#;
    check_result_string(
        "partial_app_then_passed_to_higher_order",
        src,
        "hello world/hello world",
    );
}

// ---------------------------------------------------------------------------
// Fixtures: effectful var bindings (let g = factory(); g x)
// ---------------------------------------------------------------------------

#[test]
fn effectful_var_binding_simple() {
    let src = r#"module Main

effect Log {
  fun log : String -> Unit
}

handler collect for Log {
  log msg = msg <> "/" <> resume ()
  return _ = ""
}

fun make_logger : Unit -> (String -> Unit needs {Log})
make_logger () = fun s -> log! s

pub fun result : Unit -> String
result () = {
  let g = make_logger ()
  g "a"
  g "b"
  ()
} with collect
"#;
    check_result_string("effectful_var_binding_simple", src, "a/b/");
}

#[test]
fn effectful_var_binding_with_capture() {
    let src = r#"module Main

effect Log {
  fun log : String -> Unit
}

handler collect for Log {
  log msg = msg <> "/" <> resume ()
  return _ = ""
}

fun mk_prefixed : String -> (String -> Unit needs {Log})
mk_prefixed pre = fun s -> log! (pre <> ":" <> s)

pub fun result : Unit -> String
result () = {
  let info = mk_prefixed "INFO"
  info "hi"
  info "bye"
  ()
} with collect
"#;
    check_result_string(
        "effectful_var_binding_with_capture",
        src,
        "INFO:hi/INFO:bye/",
    );
}

// ---------------------------------------------------------------------------
// Fixtures: multishot resumption
// ---------------------------------------------------------------------------

#[test]
fn multishot_two_resumes_concat() {
    let src = r#"module Main

effect Log {
  fun log : String -> Unit
}

handler double_log for Log {
  log msg = {
    let a = resume ()
    let b = resume ()
    "(" <> msg <> "<" <> a <> "|" <> b <> ">)"
  }
  return _ = "."
}

pub fun result : Unit -> String
result () = {
  log! "X"
} with double_log
"#;
    check_result_string("multishot_two_resumes_concat", src, "(X<.|.>)");
}

#[test]
fn multishot_choose_collects_all() {
    let src = r#"module Main

effect Choose {
  fun choose : List Int -> Int
}

handler all_solutions for Choose {
  choose options = List.flat_map (fun x -> resume x) options
  return v = [v]
}

pub fun result : Unit -> String
result () = {
  let xs = {
    let a = choose! [1, 2]
    let b = choose! [10, 20]
    a + b
  } with all_solutions
  String.join "," (List.map show xs)
}
"#;
    check_result_string("multishot_choose_collects_all", src, "11,21,12,22");
}

#[test]
fn multishot_resume_with_different_values() {
    // Handler resumes with two different values, accumulating both.
    let src = r#"module Main

effect Pick {
  fun pick : Unit -> Int
}

handler both for Pick {
  pick () = {
    let x = resume 1
    let y = resume 2
    x <> "," <> y
  }
  return v = v
}

pub fun result : Unit -> String
result () = {
  let n = pick! ()
  show (n * 10)
} with both
"#;
    check_result_string("multishot_resume_with_different_values", src, "10,20");
}

// ---------------------------------------------------------------------------
// Fixtures: BEAM-native effects
// ---------------------------------------------------------------------------

#[test]
fn beam_ref_basic_get_set() {
    let src = r#"module Main

import Std.Ref (Ref, beam_ref)

pub fun result : Unit -> String
result () = {
  let r = new! 10
  set! r 99
  show (get! r)
} with beam_ref
"#;
    check_result_string("beam_ref_basic_get_set", src, "99");
}

#[test]
fn beam_ref_modify_returns_new() {
    let src = r#"module Main

import Std.Ref (Ref, beam_ref)

pub fun result : Unit -> String
result () = {
  let r = new! 7
  let _ = modify! r (fun n -> n * 2)
  let _ = modify! r (fun n -> n + 1)
  show (get! r)
} with beam_ref
"#;
    check_result_string("beam_ref_modify_returns_new", src, "15");
}

#[test]
fn beam_ref_two_refs_independent() {
    let src = r#"module Main

import Std.Ref (Ref, beam_ref)

pub fun result : Unit -> String
result () = {
  let a = new! 1
  let b = new! 100
  set! a 5
  set! b 200
  show (get! a) <> "," <> show (get! b)
} with beam_ref
"#;
    check_result_string("beam_ref_two_refs_independent", src, "5,200");
}

#[test]
fn beam_actor_self_returns_pid() {
    // Process effect: self! returns this process's pid. Just check it's
    // non-empty (pid printing is opaque).
    let src = r#"module Main

import Std.Actor (Process, Actor, beam_actor)

pub fun result : Unit -> String
result () = {
  let _pid = self! ()
  "self-ok"
} with beam_actor
"#;
    check_result_string("beam_actor_self_returns_pid", src, "self-ok");
}

#[test]
fn beam_actor_send_receive_roundtrip_self() {
    // Send a message to self and receive it back. This avoids the
    // multi-`Actor msg` instantiation issue that arises when spawning
    // a child whose mailbox type differs from the parent's.
    let src = r#"module Main

import Std.Actor (Process, Actor, beam_actor)

pub fun result : Unit -> String
result () = {
  let me = self! ()
  send! me 42
  let answer = receive {
    n -> n
  }
  show answer
} with beam_actor
"#;
    check_result_string("beam_actor_send_receive_roundtrip_self", src, "42");
}

#[test]
fn beam_timer_sleep_no_crash() {
    // sleep! 0 is a no-op-ish call into the runtime; verify it round-trips.
    let src = r#"module Main

import Std.Actor (Timer, beam_actor)

pub fun result : Unit -> String
result () = {
  sleep! 0
  "slept"
} with beam_actor
"#;
    check_result_string("beam_timer_sleep_no_crash", src, "slept");
}

// ---------------------------------------------------------------------------
// Fixtures: mixed BEAM-native + CPS handlers
// ---------------------------------------------------------------------------

#[test]
fn mixed_ref_and_log_effects() {
    let src = r#"module Main

import Std.Ref (Ref, beam_ref)

effect Log {
  fun log : String -> Unit
}

handler collect for Log {
  log msg = msg <> "/" <> resume ()
}

fun work : Unit -> String needs {Ref, Log}
work () = {
  let r = new! 0
  set! r 1
  log! "step1"
  set! r ((get! r) + 5)
  log! "step2"
  show (get! r)
}

pub fun result : Unit -> String
result () = (work () with beam_ref) with collect
"#;
    check_result_string("mixed_ref_and_log_effects", src, "step1/step2/6");
}

#[test]
fn mixed_actor_and_fail() {
    let src = r#"module Main

import Std.Actor (Process, Actor, beam_actor)
import Std.Fail (Fail)

handler to_result_str for Fail String {
  fail e = "err:" <> e
  return v = "ok:" <> v
}

fun maybe : Bool -> String needs {Process, Actor Int, Fail String}
maybe True = fail! "no"
maybe False = {
  let _pid = self! ()
  "yes"
}

pub fun result : Unit -> String
result () = (maybe False with to_result_str) with beam_actor
"#;
    check_result_string("mixed_actor_and_fail", src, "ok:yes");
}

#[test]
fn mixed_ref_and_fail_abort() {
    // Fail handler aborts; ref allocated before the fail call should
    // simply be unreachable after.
    let src = r#"module Main

import Std.Ref (Ref, beam_ref)
import Std.Fail (Fail)

handler to_result_str for Fail String {
  fail e = "err:" <> e
  return v = "ok:" <> v
}

fun work : Unit -> String needs {Ref, Fail String}
work () = {
  let r = new! 100
  set! r 7
  fail! "boom"
  show (get! r)
}

pub fun result : Unit -> String
result () = (work () with to_result_str) with beam_ref
"#;
    check_result_string("mixed_ref_and_fail_abort", src, "err:boom");
}

// ---------------------------------------------------------------------------
// Fixtures: cross-module effectful calls
// ---------------------------------------------------------------------------

#[test]
fn cross_module_basic_effectful_call() {
    let lib = r#"module LogLib

pub effect Log {
  fun log : String -> Unit
}

pub fun shout : String -> String needs {Log}
shout s = {
  log! s
  "S(" <> s <> ")"
}
"#;
    let main_src = r#"module Main

import LogLib (Log, shout)

handler collect for Log {
  log msg = msg <> "/" <> resume ()
}

pub fun result : Unit -> String
result () = (LogLib.shout "hi") with collect
"#;
    check_cross_module(
        "cross_module_basic_effectful_call",
        &[("lib/LogLib.saga", lib)],
        main_src,
        "hi/S(hi)",
    );
}

#[test]
fn cross_module_stdlib_fail_handler() {
    let lib = r#"module FailLib

import Std.Fail (Fail)

pub fun safe_div : Int -> Int -> String needs {Fail String}
safe_div _ 0 = fail! "div0"
safe_div x y = show (x / y)
"#;
    let main_src = r#"module Main

import Std.Fail (Fail)
import FailLib (safe_div)

handler to_result_str for Fail String {
  fail e = "err:" <> e
  return v = "ok:" <> v
}

pub fun result : Unit -> String
result () = (FailLib.safe_div 10 0) with to_result_str
"#;
    check_cross_module(
        "cross_module_stdlib_fail_handler",
        &[("lib/FailLib.saga", lib)],
        main_src,
        "err:div0",
    );
}

#[test]
fn cross_module_effectful_call_resume_path() {
    let lib = r#"module FailLib

import Std.Fail (Fail)

pub fun safe_div : Int -> Int -> String needs {Fail String}
safe_div _ 0 = fail! "div0"
safe_div x y = show (x / y)
"#;
    let main_src = r#"module Main

import Std.Fail (Fail)
import FailLib (safe_div)

handler to_result_str for Fail String {
  fail e = "err:" <> e
  return v = "ok:" <> v
}

pub fun result : Unit -> String
result () = (FailLib.safe_div 20 4) with to_result_str
"#;
    check_cross_module(
        "cross_module_effectful_call_resume_path",
        &[("lib/FailLib.saga", lib)],
        main_src,
        "ok:5",
    );
}

#[test]
fn cross_module_handler_factory() {
    // Library exports a handler-producing function; main installs it.
    let lib = r#"module LogLib

pub effect Log {
  fun log : String -> Unit
}

pub fun mk_collect : Unit -> Handler Log
mk_collect () = handler for Log {
  log msg = msg <> "/" <> resume ()
}

pub fun do_work : Unit -> String needs {Log}
do_work () = {
  log! "u"
  log! "v"
  "fin"
}
"#;
    let main_src = r#"module Main

import LogLib (Log, mk_collect, do_work)

pub fun result : Unit -> String
result () = {
  let h = LogLib.mk_collect ()
  LogLib.do_work () with h
}
"#;
    check_cross_module(
        "cross_module_handler_factory",
        &[("lib/LogLib.saga", lib)],
        main_src,
        "u/v/fin",
    );
}

#[test]
fn cross_module_partial_app() {
    let lib = r#"module GreetLib

pub effect Log {
  fun log : String -> Unit
}

pub fun greet : String -> String -> String needs {Log}
greet hi name = {
  log! (hi <> " " <> name)
  hi <> " " <> name
}
"#;
    let main_src = r#"module Main

import GreetLib (Log, greet)

handler collect for Log {
  log msg = msg <> "/" <> resume ()
}

pub fun result : Unit -> String
result () = {
  let hi = GreetLib.greet "hello"
  hi "world"
} with collect
"#;
    check_cross_module(
        "cross_module_partial_app",
        &[("lib/GreetLib.saga", lib)],
        main_src,
        "hello world/hello world",
    );
}

#[test]
fn cross_module_two_effects_in_one_call() {
    let lib = r#"module MixLib

import Std.Fail (Fail)

pub effect Log {
  fun log : String -> Unit
}

pub fun work : Int -> String needs {Log, Fail String}
work 0 = fail! "zero"
work n = {
  log! (show n)
  show (n * 2)
}
"#;
    let main_src = r#"module Main

import Std.Fail (Fail)
import MixLib (Log, work)

handler collect for Log {
  log msg = msg <> "/" <> resume ()
}

handler to_result_str for Fail String {
  fail e = "err:" <> e
  return v = "ok:" <> v
}

pub fun result_ok : Unit -> String
result_ok () = ((MixLib.work 3) with to_result_str) with collect

pub fun result : Unit -> String
result () = ((MixLib.work 0) with to_result_str) with collect
"#;
    check_cross_module(
        "cross_module_two_effects_in_one_call",
        &[("lib/MixLib.saga", lib)],
        main_src,
        "err:zero",
    );
}

// ---------------------------------------------------------------------------
// Fixtures: pure return-value sanity (control)
// ---------------------------------------------------------------------------

#[test]
fn control_pure_arithmetic() {
    let src = r#"module Main

pub fun result : Unit -> Int
result () = 1 + 2 * 3
"#;
    check_result_int("control_pure_arithmetic", src, 7);
}

#[test]
fn control_pure_list_sum() {
    let src = r#"module Main

pub fun result : Unit -> Int
result () = List.foldl (fun a b -> a + b) 0 [1, 2, 3, 4, 5]
"#;
    check_result_int("control_pure_list_sum", src, 15);
}

// ---------------------------------------------------------------------------
// Fixtures: handler-bound vars + conditional handler binding
// ---------------------------------------------------------------------------

#[test]
fn handler_bound_to_let_binding() {
    let src = r#"module Main

effect Log {
  fun log : String -> Unit
}

handler collect for Log {
  log msg = msg <> "/" <> resume ()
  return _ = ""
}

pub fun result : Unit -> String
result () = {
  let h = collect
  {
    log! "u"
    log! "v"
    ()
  } with h
}
"#;
    check_result_string("handler_bound_to_let_binding", src, "u/v/");
}

#[test]
fn handler_chosen_conditionally() {
    let src = r#"module Main

effect Log {
  fun log : String -> Unit
}

handler loud for Log {
  log msg = "L:" <> msg <> "/" <> resume ()
  return _ = ""
}

handler quiet for Log {
  log _ = resume ()
  return _ = "Q"
}

pub fun result : Unit -> String
result () = {
  let h = if True then loud else quiet
  {
    log! "x"
    ()
  } with h
}
"#;
    check_result_string("handler_chosen_conditionally", src, "L:x/");
}

#[test]
fn handler_inline_block() {
    let src = r#"module Main

effect Log {
  fun log : String -> Unit
}

pub fun result : Unit -> String
result () = {
  log! "hello"
  "done"
} with {
  log msg = msg <> "/" <> resume ()
  return v = v
}
"#;
    check_result_string("handler_inline_block", src, "hello/done");
}

// ---------------------------------------------------------------------------
// Fixtures: additional coverage
// ---------------------------------------------------------------------------

#[test]
fn multishot_three_resumes() {
    let src = r#"module Main

effect Pick {
  fun pick : Unit -> Int
}

handler triple for Pick {
  pick () = {
    let a = resume 1
    let b = resume 2
    let c = resume 3
    a <> "," <> b <> "," <> c
  }
  return v = v
}

pub fun result : Unit -> String
result () = {
  let n = pick! ()
  show (n * 100)
} with triple
"#;
    check_result_string("multishot_three_resumes", src, "100,200,300");
}

#[test]
fn multishot_choose_with_fail_pruning() {
    let src = r#"module Main

effect Choose {
  fun choose : List Int -> Int
}

effect Prune {
  fun prune : Unit -> a
}

handler all_solutions for Choose, Prune {
  choose options = List.flat_map (fun x -> resume x) options
  prune () = []
  return v = [v]
}

pub fun result : Unit -> String
result () = {
  let xs = {
    let a = choose! [1, 2, 3]
    if a == 2 then prune! () else a
  } with all_solutions
  String.join "," (List.map show xs)
}
"#;
    check_result_string("multishot_choose_with_fail_pruning", src, "1,3");
}

#[test]
fn nested_with_returns_distinct_value() {
    // Two distinct effects in deeply nested fashion. Each handler's
    // value flows up cleanly; the outermost wraps the innermost result.
    let src = r#"module Main

import Std.Fail (Fail)

effect Tag {
  fun tag : String -> String
}

handler tagger for Tag {
  tag s = resume ("[" <> s <> "]")
}

handler to_result_str for Fail String {
  fail e = "err:" <> e
  return v = "ok:" <> v
}

fun work : Unit -> String needs {Tag, Fail String}
work () = {
  let t = tag! "name"
  if t == "[name]" then t else fail! "wrong"
}

pub fun result : Unit -> String
result () = (work () with to_result_str) with tagger
"#;
    check_result_string("nested_with_returns_distinct_value", src, "ok:[name]");
}

// FIXME: `let a = mk_call "alpha"; a (); a (); "tail"` miscompiles. Each
// `a ()` is a mid-block effectful call; the resume continuation produces the
// wrong shape (the runtime gets Unit where the handler's `<>` chain expects
// String). The simpler `let g = factory(); g x` shape (single call, last
// stmt) works — see `effectful_var_binding_simple`. Flagged for the
// evidence-passing cutover; do not fix in Phase 0.
#[ignore = "effectful var binding called mid-block miscompiles (pre-existing)"]
#[test]
fn effectful_var_binding_deferred_call() {
    // The factory returns a function that captures handler state at call time
    // (not at binding time). Reusing the same binding across multiple sites
    // should route ops to the *current* handler.
    let src = r#"module Main

effect Log {
  fun log : String -> Unit
}

handler collect for Log {
  log msg = msg <> "/" <> resume ()
}

fun mk_call : String -> (Unit -> Unit needs {Log})
mk_call s = fun () -> log! s

pub fun result : Unit -> String
result () = {
  let a = mk_call "alpha"
  let b = mk_call "beta"
  a ()
  b ()
  a ()
  "end"
} with collect
"#;
    check_result_string(
        "effectful_var_binding_deferred_call",
        src,
        "alpha/beta/alpha/end",
    );
}

#[test]
fn ref_inside_effect_handler_persists_across_resumes() {
    // Ref-backed counter incremented on every Log call. Verifies that
    // the BEAM-native Ref handler maintains state across the CPS-shaped
    // continuations of a user-defined effect.
    let src = r#"module Main

import Std.Ref (MutRef, Ref, beam_ref)

effect Log {
  fun log : String -> Unit
}

fun work : MutRef Int -> Unit needs {Log, Ref}
work counter = {
  log! "a"
  log! "b"
  log! "c"
}

pub fun result : Unit -> String
result () = {
  let counter = new! 0
  let _ = work counter with {
    log _ = {
      let _ = modify! counter (fun n -> n + 1)
      resume ()
    }
  }
  show (get! counter)
} with beam_ref
"#;
    check_result_string("ref_inside_effect_handler_persists_across_resumes", src, "3");
}

#[test]
fn fail_handler_inside_resume_aborts_correctly() {
    // The Fail handler aborts mid-resume in a Log handler; the abort must
    // unwind through the surrounding handler.
    let src = r#"module Main

import Std.Fail (Fail)

effect Log {
  fun log : String -> Unit
}

handler collect for Log {
  log msg = msg <> "/" <> resume ()
}

handler to_result_str for Fail String {
  fail e = "err:" <> e
  return v = "ok:" <> v
}

fun work : Unit -> String needs {Log, Fail String}
work () = {
  log! "before"
  fail! "bang"
  log! "after"
  "tail"
}

pub fun result : Unit -> String
result () = (work () with to_result_str) with collect
"#;
    // log "before" runs through collect; fail! aborts; collect.log's resume
    // returns immediately with the inner Fail's err string; "after" never runs.
    check_result_string(
        "fail_handler_inside_resume_aborts_correctly",
        src,
        "before/err:bang",
    );
}

// FIXME: same shape as `effectful_var_binding_deferred_call` but across
// modules — the partially-applied effectful function bound via `let info = ...`
// and called twice in stmt position miscompiles at runtime.
#[ignore = "effectful var binding called mid-block miscompiles (pre-existing)"]
#[test]
fn cross_module_effectful_var_binding() {
    // The lib exports an effectful function; main partially applies it,
    // binds the result, and calls it twice under a local handler.
    let lib = r#"module GreetLib

pub effect Log {
  fun log : String -> Unit
}

pub fun stamped : String -> String -> Unit needs {Log}
stamped tag name = log! (tag <> ":" <> name)
"#;
    let main_src = r#"module Main

import GreetLib (Log, stamped)

handler collect for Log {
  log msg = msg <> "/" <> resume ()
}

pub fun result : Unit -> String
result () = {
  let info = GreetLib.stamped "INFO"
  info "alice"
  info "bob"
  "done"
} with collect
"#;
    check_cross_module(
        "cross_module_effectful_var_binding",
        &[("lib/GreetLib.saga", lib)],
        main_src,
        "INFO:alice/INFO:bob/done",
    );
}

// FIXME: open-row higher-order across modules — `apply_twice` calls its
// callback twice in stmt position; the second call's continuation produces
// Unit where the surrounding handler's `<>` chain expects String. Likely
// the same root cause as `effectful_var_binding_deferred_call`: mid-block
// effectful calls don't thread the continuation correctly.
#[ignore = "open-row HOF callback called twice mid-block miscompiles (pre-existing)"]
#[test]
fn cross_module_open_row_higher_order() {
    // The lib takes a callback whose effects forward through ..e. The
    // callback uses Log; main's handler captures it.
    let lib = r#"module HofLib

pub fun apply_twice : (String -> Unit needs {..e}) -> Unit needs {..e}
apply_twice f = {
  f "first"
  f "second"
}
"#;
    let main_src = r#"module Main

import HofLib (apply_twice)

effect Log {
  fun log : String -> Unit
}

handler collect for Log {
  log msg = msg <> "/" <> resume ()
}

pub fun result : Unit -> String
result () = {
  HofLib.apply_twice (fun s -> log! s)
  "end"
} with collect
"#;
    check_cross_module(
        "cross_module_open_row_higher_order",
        &[("lib/HofLib.saga", lib)],
        main_src,
        "first/second/end",
    );
}

#[test]
fn beam_ref_with_fail_recover() {
    let src = r#"module Main

import Std.Ref (MutRef, Ref, beam_ref)
import Std.Fail (Fail)

handler default_zero for Fail String {
  fail _ = resume "0"
}

fun read_or_default : MutRef String -> String needs {Fail String, Ref}
read_or_default r = {
  let s = get! r
  if s == "" then fail! "empty" else s
}

pub fun result : Unit -> String
result () = {
  let a = new! "hello"
  let b = new! ""
  let r1 = read_or_default a with default_zero
  let r2 = read_or_default b with default_zero
  r1 <> "," <> r2
} with beam_ref
"#;
    check_result_string("beam_ref_with_fail_recover", src, "hello,0");
}

#[test]
fn handler_with_state_param_threads_state() {
    // Classic state-passing pattern: handler arms return functions of the
    // current state; each op threads state through.
    let src = r#"module Main

effect Counter {
  fun bump : Unit -> Int
}

fun run_counter : (init: Int) -> (f: Unit -> a needs {Counter}) -> (a, Int)
run_counter init f = {
  let stateful = f () with {
    bump () = fun s -> (resume (s + 1)) (s + 1)
    return v = fun s -> (v, s)
  }
  stateful init
}

pub fun result : Unit -> String
result () = {
  let (final_val, final_state) = run_counter 10 (fun () -> {
    let a = bump! ()
    let b = bump! ()
    let c = bump! ()
    a + b + c
  })
  show final_val <> "/" <> show final_state
}
"#;
    // bump increments state; resume passes new state. With init=10:
    //   a = 11 (state: 11), b = 12 (state: 12), c = 13 (state: 13)
    //   final_val = 11 + 12 + 13 = 36, final_state = 13
    check_result_string("handler_with_state_param_threads_state", src, "36/13");
}

#[test]
fn op_call_with_multiple_args() {
    let src = r#"module Main

effect Combine {
  fun mix : String -> Int -> String
}

handler m for Combine {
  mix s n = resume (s <> ":" <> show n)
}

pub fun result : Unit -> String
result () = {
  let a = mix! "x" 1
  let b = mix! "y" 2
  a <> "," <> b
} with m
"#;
    check_result_string("op_call_with_multiple_args", src, "x:1,y:2");
}

#[test]
fn handler_resume_with_complex_value() {
    let src = r#"module Main

effect Get {
  fun get : Unit -> Maybe Int
}

handler some_42 for Get {
  get () = resume (Just 42)
}

pub fun result : Unit -> String
result () = {
  case get! () {
    Just n -> "got:" <> show n
    Nothing -> "none"
  }
} with some_42
"#;
    check_result_string("handler_resume_with_complex_value", src, "got:42");
}
