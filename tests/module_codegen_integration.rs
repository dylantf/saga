use dylang::{codegen, elaborate, lexer, parser, typechecker};
use std::path::PathBuf;

fn fixtures_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/modules")
}

/// Parse, typecheck, elaborate, and emit Core Erlang for a module in project mode.
/// Returns (core_output, checker) so tests can chain module compilations.
fn emit_project_module(
    source: &str,
    module_name: &str,
    checker: &typechecker::Checker,
) -> String {
    let tokens = lexer::Lexer::new(source).lex().expect("lex error");
    let program = parser::Parser::new(tokens)
        .parse_program()
        .expect("parse error");
    let elaborated = elaborate::elaborate(&program, checker);
    codegen::emit_module_with_imports(module_name, &elaborated, &checker.tc_codegen_info)
}

/// Parse and typecheck a source file with the given checker (project mode).
fn typecheck_source(source: &str, checker: &mut typechecker::Checker) {
    let tokens = lexer::Lexer::new(source).lex().expect("lex error");
    let program = parser::Parser::new(tokens)
        .parse_program()
        .expect("parse error");
    checker.check_program(&program).expect("typecheck error");
}

/// Create a project-mode checker pointed at the test fixtures directory,
/// with prelude loaded.
fn make_project_checker() -> typechecker::Checker {
    let mut checker = typechecker::Checker::with_project_root(fixtures_root());
    let prelude_src = include_str!("../src/prelude/prelude.dy");
    let prelude_tokens = lexer::Lexer::new(prelude_src)
        .lex()
        .expect("prelude lex error");
    let prelude_program = parser::Parser::new(prelude_tokens)
        .parse_program()
        .expect("prelude parse error");
    checker
        .check_program(&prelude_program)
        .expect("prelude typecheck error");
    checker
}

/// Compile Core Erlang to .beam with erlc, asserting success.
fn assert_erlc_compiles(core_src: &str, module_name: &str) -> PathBuf {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static COUNTER: AtomicUsize = AtomicUsize::new(0);

    let id = COUNTER.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("dylang_modtest_{}_{id}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let core_path = dir.join(format!("{module_name}.core"));
    std::fs::write(&core_path, core_src).unwrap();
    let output = std::process::Command::new("erlc")
        .arg("-o")
        .arg(&dir)
        .arg(&core_path)
        .output()
        .expect("failed to run erlc");
    assert!(
        output.status.success(),
        "erlc failed on {module_name}:\n{core_src}\nstderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    dir
}

fn assert_contains(out: &str, needle: &str) {
    assert!(
        out.contains(needle),
        "Expected to find:\n  {needle}\nIn output:\n{out}"
    );
}

// ---- Qualified call emission ----

#[test]
fn qualified_call_emits_inter_module_call() {
    let main_src = "
module Main
import Math
pub fun main () -> Int
main () = Math.add 10 20
";
    let mut checker = make_project_checker();
    typecheck_source(main_src, &mut checker);
    let out = emit_project_module(main_src, "main", &checker);

    // Should emit call 'math':'add'(...)
    assert_contains(&out, "call 'math':'add'");
    // Should NOT use apply (local call)
    assert!(
        !out.contains("apply 'add'"),
        "should use inter-module call, not local apply\n{out}"
    );
}

#[test]
fn qualified_call_with_alias() {
    let main_src = "
module Main
import Math as M
pub fun main () -> Int
main () = M.add 1 2
";
    let mut checker = make_project_checker();
    typecheck_source(main_src, &mut checker);
    let out = emit_project_module(main_src, "main", &checker);

    // Alias 'M' should still resolve to erlang module 'math'
    assert_contains(&out, "call 'math':'add'");
}

// ---- Exposed (unqualified) imports ----

#[test]
fn exposed_import_emits_inter_module_call() {
    let main_src = "
module Main
import Math (add)
pub fun main () -> Int
main () = add 10 20
";
    let mut checker = make_project_checker();
    typecheck_source(main_src, &mut checker);
    let out = emit_project_module(main_src, "main", &checker);

    // Even though 'add' is unqualified, it should still emit an inter-module call
    assert_contains(&out, "call 'math':'add'");
}

#[test]
fn exposed_and_qualified_same_module() {
    let main_src = "
module Main
import Math (add)
pub fun main () -> Int
main () = add 1 (Math.double 3)
";
    let mut checker = make_project_checker();
    typecheck_source(main_src, &mut checker);
    let out = emit_project_module(main_src, "main", &checker);

    // Both should be inter-module calls
    assert_contains(&out, "call 'math':'add'");
    assert_contains(&out, "call 'math':'double'");
}

// ---- Export filtering ----

#[test]
fn pub_functions_exported() {
    let math_src = std::fs::read_to_string(fixtures_root().join("Math.dy")).unwrap();
    let mut checker = make_project_checker();
    typecheck_source(&math_src, &mut checker);
    let out = emit_project_module(&math_src, "math", &checker);

    // pub functions should be in the export list
    assert_contains(&out, "'add'/2");
    assert_contains(&out, "'double'/1");
}

#[test]
fn private_functions_not_exported() {
    let math_src = std::fs::read_to_string(fixtures_root().join("Math.dy")).unwrap();
    let mut checker = make_project_checker();
    typecheck_source(&math_src, &mut checker);
    let out = emit_project_module(&math_src, "math", &checker);

    // 'secret' is private -- should be defined but not exported
    // The export list is on the first line between [ ]
    let export_line = out.lines().next().unwrap();
    assert!(
        !export_line.contains("'secret'"),
        "private function 'secret' should not be in exports\n{export_line}"
    );
    // But it should still be defined in the module body
    assert_contains(&out, "'secret'/");
}

#[test]
fn no_module_decl_exports_everything() {
    // Single-file (no module declaration) should export all functions
    let src = "
add a b = a + b
double x = x * 2
main () = add 1 2
";
    let tokens = lexer::Lexer::new(src).lex().unwrap();
    let program = parser::Parser::new(tokens).parse_program().unwrap();
    let out = codegen::emit_module("test", &program);

    let export_line = out.lines().next().unwrap();
    assert!(export_line.contains("'add'/2"), "add should be exported\n{export_line}");
    assert!(export_line.contains("'double'/1"), "double should be exported\n{export_line}");
    assert!(export_line.contains("'main'/0"), "main should be exported\n{export_line}");
}

// ---- Module name mapping ----

#[test]
fn module_name_lowercased_in_output() {
    let src = "
module MathLib
pub fun add (a: Int) (b: Int) -> Int
add a b = a + b
";
    let mut checker = make_project_checker();
    typecheck_source(src, &mut checker);
    let out = emit_project_module(src, "mathlib", &checker);

    assert!(
        out.starts_with("module 'mathlib'"),
        "module name should be lowercased\n{out}"
    );
}

// ---- Multi-module compilation ----

#[test]
fn two_module_qualified_call_compiles() {
    let math_src = std::fs::read_to_string(fixtures_root().join("Math.dy")).unwrap();
    let main_src = "
module Main
import Math
pub fun main () -> Int
main () = Math.add 10 20
";

    let mut checker = make_project_checker();
    // Typecheck main (which transitively typechecks Math)
    typecheck_source(main_src, &mut checker);

    // Emit both modules
    let math_core = emit_project_module(&math_src, "math", &checker);
    let main_core = emit_project_module(main_src, "main", &checker);

    // Both should compile with erlc
    let dir = assert_erlc_compiles(&math_core, "math");
    let main_core_path = dir.join("main.core");
    std::fs::write(&main_core_path, &main_core).unwrap();
    let output = std::process::Command::new("erlc")
        .arg("-o")
        .arg(&dir)
        .arg(&main_core_path)
        .output()
        .expect("failed to run erlc");
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        output.status.success(),
        "erlc failed on main:\n{main_core}\nstderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn two_module_exposed_import_compiles() {
    let math_src = std::fs::read_to_string(fixtures_root().join("Math.dy")).unwrap();
    let main_src = "
module Main
import Math (add, double)
pub fun main () -> Int
main () = add 1 (double 10)
";

    let mut checker = make_project_checker();
    typecheck_source(main_src, &mut checker);

    let math_core = emit_project_module(&math_src, "math", &checker);
    let main_core = emit_project_module(main_src, "main", &checker);

    let dir = assert_erlc_compiles(&math_core, "math");
    let main_core_path = dir.join("main.core");
    std::fs::write(&main_core_path, &main_core).unwrap();
    let output = std::process::Command::new("erlc")
        .arg("-o")
        .arg(&dir)
        .arg(&main_core_path)
        .output()
        .expect("failed to run erlc");
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        output.status.success(),
        "erlc failed on main:\n{main_core}\nstderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
}

// ---- Imported record field orders ----

#[test]
fn imported_record_fields_available() {
    let main_src = "
module Main
import Animals (Animal)
pub fun main () -> String
main () = {
  let a = Animal { name: \"Rex\", species: \"Dog\" }
  a.name
}
";
    let mut checker = make_project_checker();
    typecheck_source(main_src, &mut checker);
    let out = emit_project_module(main_src, "main", &checker);

    // Should compile without errors about unknown record fields
    // The record creates a tagged tuple with fields in correct order
    assert_contains(&out, "'Animal'");
}

// ---- Multiple imports from different modules ----

#[test]
fn imports_from_multiple_modules() {
    let main_src = "
module Main
import Math
import Shapes (area, Circle)
pub fun main () -> Int
main () = {
  let _ = area (Circle 5.0)
  Math.add 1 2
}
";
    let mut checker = make_project_checker();
    typecheck_source(main_src, &mut checker);
    let out = emit_project_module(main_src, "main", &checker);

    // Should have inter-module calls to both modules
    assert_contains(&out, "call 'math':'add'");
    assert_contains(&out, "call 'shapes':'area'");
}

// ---- Calling imported function that calls another imported function ----

#[test]
fn imported_function_calling_local() {
    // Math.double internally calls Math.add -- verify this still works
    let math_src = std::fs::read_to_string(fixtures_root().join("Math.dy")).unwrap();
    let mut checker = make_project_checker();
    typecheck_source(&math_src, &mut checker);
    let out = emit_project_module(&math_src, "math", &checker);

    // double uses `a * 2`, so it should emit an erlang multiply call
    assert_contains(&out, "call 'erlang':'*'");
}

// ---- Edge: import with no codegen info (Std modules) ----

#[test]
fn stdlib_import_does_not_crash_lowerer() {
    // Std modules are builtins and won't have codegen info.
    // The lowerer should handle this gracefully.
    let main_src = "
module Main
import Std.List as List
pub fun main () -> String
main () = show (List.map (fun x -> x + 1) [1, 2, 3])
";
    let mut checker = make_project_checker();
    typecheck_source(main_src, &mut checker);
    // Should not panic
    let _out = emit_project_module(main_src, "main", &checker);
}

// ---- Exposing a type + constructors ----

#[test]
fn exposed_constructor_emits_correctly() {
    let main_src = "
module Main
import Shapes (Circle, Rect, area)
pub fun main () -> Float
main () = area (Circle 5.0) + area (Rect 3.0 4.0)
";
    // Note: this won't emit inter-module calls for constructors since
    // constructors are values (atoms/tuples), not function calls.
    // But it should not crash.
    let mut checker = make_project_checker();
    typecheck_source(main_src, &mut checker);
    let _out = emit_project_module(main_src, "main", &checker);
}

// ---- Cross-module effectful calls ----

#[test]
fn cross_module_effectful_qualified_call() {
    // Logger.greet needs {Log}, so the call should thread _HandleLog + _ReturnK
    let main_src = "
module Main
import Logger

effect Log {
  fun log (msg: String) -> Unit
}

handler console_log for Log {
  log msg -> print msg
}

pub fun main () -> String
main () = Logger.greet \"world\" with console_log
";
    let mut checker = make_project_checker();
    typecheck_source(main_src, &mut checker);
    let out = emit_project_module(main_src, "main", &checker);

    // Should emit inter-module call with handler params
    assert_contains(&out, "call 'logger':'greet'");
    // The call should have 3 args: name, _HandleLog, _ReturnK
    // (not just 1 arg like a pure function)
}

#[test]
fn cross_module_effectful_exposed_call() {
    // Same as above but with exposed import
    let main_src = "
module Main
import Logger (greet)

effect Log {
  fun log (msg: String) -> Unit
}

handler console_log for Log {
  log msg -> print msg
}

pub fun main () -> String
main () = greet \"world\" with console_log
";
    let mut checker = make_project_checker();
    typecheck_source(main_src, &mut checker);
    let out = emit_project_module(main_src, "main", &checker);

    // Exposed effectful call should still be inter-module
    assert_contains(&out, "call 'logger':'greet'");
}

#[test]
fn cross_module_effectful_export_arity() {
    // Logger.greet should be exported with expanded arity (1 + 1 handler + 1 ReturnK = 3)
    let logger_src = std::fs::read_to_string(fixtures_root().join("Logger.dy")).unwrap();
    let mut checker = make_project_checker();
    typecheck_source(&logger_src, &mut checker);
    let out = emit_project_module(&logger_src, "logger", &checker);

    // greet should be exported with arity 3 (name, _HandleLog, _ReturnK)
    assert_contains(&out, "'greet'/3");
}

#[test]
fn cross_module_effectful_compiles_with_erlc() {
    let logger_src = std::fs::read_to_string(fixtures_root().join("Logger.dy")).unwrap();
    let main_src = "
module Main
import Logger

effect Log {
  fun log (msg: String) -> Unit
}

handler console_log for Log {
  log msg -> print msg
}

pub fun main () -> String
main () = Logger.greet \"world\" with console_log
";
    let mut checker = make_project_checker();
    typecheck_source(main_src, &mut checker);

    let logger_core = emit_project_module(&logger_src, "logger", &checker);
    let main_core = emit_project_module(main_src, "main", &checker);

    // Both should compile with erlc
    let dir = assert_erlc_compiles(&logger_core, "logger");
    let main_core_path = dir.join("main.core");
    std::fs::write(&main_core_path, &main_core).unwrap();
    let output = std::process::Command::new("erlc")
        .arg("-o")
        .arg(&dir)
        .arg(&main_core_path)
        .output()
        .expect("failed to run erlc");
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        output.status.success(),
        "erlc failed on main:\n{main_core}\nstderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
}
