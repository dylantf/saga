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
    // Extract original module name (e.g. "Animals") from ModuleDecl for elaboration
    let original_module_name = program.iter().find_map(|d| {
        if let dylang::ast::Decl::ModuleDecl { path, .. } = d {
            Some(path.join("."))
        } else {
            None
        }
    }).unwrap_or_default();
    let elaborated = elaborate::elaborate_module(&program, checker, &original_module_name);
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
    let root = fixtures_root();
    let module_map = typechecker::scan_project_modules(&root).expect("scan failed");
    let mut checker = typechecker::Checker::with_project_root(root);
    checker.set_module_map(module_map);
    let prelude_src = include_str!("../src/stdlib/prelude.dy");
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
    assert_contains(&out, "'animals_Animal'");
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

// ---- Cross-module trait dicts ----

#[test]
fn cross_module_trait_dict_show_animal() {
    // Animals.dy defines `impl Show for Animal`.
    // Importing Animals should make the Show dict available for Animal.
    let main_src = "
module Main
import Animals (Animal)
pub fun main () -> String
main () = show (Animal { name: \"Rex\", species: \"Dog\" })
";
    let mut checker = make_project_checker();
    typecheck_source(main_src, &mut checker);
    let out = emit_project_module(main_src, "main", &checker);

    // The dict should be referenced as a cross-module call to animals module
    assert_contains(&out, "call 'animals':'__dict_Show_animals_Animal'");
}

#[test]
fn cross_module_trait_dict_compiles_with_erlc() {
    let animals_src = std::fs::read_to_string(fixtures_root().join("Animals.dy")).unwrap();
    let main_src = "
module Main
import Animals (Animal)
pub fun main () -> String
main () = show (Animal { name: \"Rex\", species: \"Dog\" })
";
    let mut checker = make_project_checker();
    typecheck_source(main_src, &mut checker);

    let animals_core = emit_project_module(&animals_src, "animals", &checker);
    let main_core = emit_project_module(main_src, "main", &checker);

    let dir = assert_erlc_compiles(&animals_core, "animals");
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
fn local_dict_names_are_module_qualified() {
    // When Animals.dy defines impl Show for Animal, the dict should be
    // named __dict_Show_animals_Animal (not __dict_Show_Animal)
    let animals_src = std::fs::read_to_string(fixtures_root().join("Animals.dy")).unwrap();
    let mut checker = make_project_checker();
    typecheck_source(&animals_src, &mut checker);
    let out = emit_project_module(&animals_src, "animals", &checker);

    assert_contains(&out, "'__dict_Show_animals_Animal'");
    assert!(
        !out.contains("'__dict_Show_Animal'"),
        "dict name should be module-qualified\n{out}"
    );
}

// ---- Constructor atom mangling ----

#[test]
fn local_adt_constructors_mangled_with_module_name() {
    let shapes_src = std::fs::read_to_string(fixtures_root().join("Shapes.dy")).unwrap();
    let mut checker = make_project_checker();
    typecheck_source(&shapes_src, &mut checker);
    let out = emit_project_module(&shapes_src, "shapes", &checker);

    // Constructors should be prefixed with module name
    assert_contains(&out, "'shapes_Circle'");
    assert_contains(&out, "'shapes_Rect'");
    // Unmangled names should not appear as constructor atoms
    assert!(!out.contains("{'Circle'"), "unmangled Circle found\n{out}");
    assert!(!out.contains("{'Rect'"), "unmangled Rect found\n{out}");
}

#[test]
fn imported_constructors_mangled_with_source_module() {
    let main_src = "
module Main
import Shapes (Circle, Rect, area)
pub fun main () -> Float
main () = area (Circle 5.0) + area (Rect 3.0 4.0)
";
    let mut checker = make_project_checker();
    typecheck_source(main_src, &mut checker);
    let out = emit_project_module(main_src, "main", &checker);

    // Imported constructors should use the source module's prefix
    assert_contains(&out, "'shapes_Circle'");
    assert_contains(&out, "'shapes_Rect'");
}

#[test]
fn record_constructors_mangled() {
    // Test that record constructors get mangled when used in expressions
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

    // Record constructor should be mangled with source module prefix
    assert_contains(&out, "'animals_Animal'");
}

#[test]
fn prelude_constructors_mangled_with_std_prefix() {
    let main_src = "
module Main
pub fun main () -> Int
main () = case Just(42) {
  Just(x) -> x
  Nothing -> 0
}
";
    let mut checker = make_project_checker();
    typecheck_source(main_src, &mut checker);
    let out = emit_project_module(main_src, "main", &checker);

    // Just(v) compiles to bare value, Nothing compiles to 'undefined' (BEAM convention)
    assert_contains(&out, "'undefined'");
    // Just(42) should compile to just 42 (bare value, no tag tuple)
    assert!(!out.contains("'std_maybe_Just'"), "Just should not produce a tagged tuple");
    assert!(!out.contains("'std_maybe_Nothing'"), "Nothing should use 'undefined' not a tagged tuple");
}

#[test]
fn cross_module_constructor_consistency() {
    // Constructor atoms must match between the defining module and the importing module
    let shapes_src = std::fs::read_to_string(fixtures_root().join("Shapes.dy")).unwrap();
    let main_src = "
module Main
import Shapes (Circle, area)
pub fun main () -> Float
main () = area (Circle 5.0)
";
    let mut checker = make_project_checker();
    typecheck_source(main_src, &mut checker);

    let shapes_out = emit_project_module(&shapes_src, "shapes", &checker);
    let main_out = emit_project_module(main_src, "main", &checker);

    // Both modules should use the same mangled atom
    assert_contains(&shapes_out, "'shapes_Circle'");
    assert_contains(&main_out, "'shapes_Circle'");
}

#[test]
fn mangled_constructors_compile_with_erlc() {
    let shapes_src = std::fs::read_to_string(fixtures_root().join("Shapes.dy")).unwrap();
    let main_src = "
module Main
import Shapes (Circle, Rect, area)
pub fun main () -> Float
main () = area (Circle 5.0) + area (Rect 3.0 4.0)
";
    let mut checker = make_project_checker();
    typecheck_source(main_src, &mut checker);

    let shapes_core = emit_project_module(&shapes_src, "shapes", &checker);
    let main_core = emit_project_module(main_src, "main", &checker);

    let dir = assert_erlc_compiles(&shapes_core, "shapes");
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

// ---- Prelude functions (fst, snd) in project mode ----

#[test]
fn prelude_fst_snd_compile_in_project_mode() {
    let main_src = "
module Main
pub fun main () -> Int
main () = {
  let pair = (10, 20)
  let x = fst pair
  let y = snd pair
  x + y
}
";
    let mut checker = make_project_checker();
    typecheck_source(main_src, &mut checker);
    let out = emit_project_module(main_src, "main", &checker);
    assert_erlc_compiles(&out, "main");
}

// ---- Opaque types ----

#[test]
fn opaque_type_exports_name_but_not_constructors() {
    let lib_src = "
module OpaqueLib
opaque type Token { Secret(String) }
pub fun make_token (s: String) -> Token
make_token s = Secret s
";
    let main_src = "
module Main
import OpaqueLib (Token, make_token)
pub fun main () -> Token
main () = make_token \"abc\"
";
    let mut checker = make_project_checker();
    let lib_path = fixtures_root().join("OpaqueLib.dy");
    std::fs::write(&lib_path, lib_src).unwrap();
    typecheck_source(main_src, &mut checker);
    let _out = emit_project_module(main_src, "main", &checker);
    let _ = std::fs::remove_file(&lib_path);
}

#[test]
fn opaque_type_constructor_rejected_by_importer() {
    let lib_src = "
module OpaqueLib2
opaque type Token { Secret(String) }
pub fun make_token (s: String) -> Token
make_token s = Secret s
";
    let main_src = "
module Main
import OpaqueLib2 (Token, Secret)
pub fun main () -> Token
main () = Secret \"abc\"
";
    let mut checker = make_project_checker();
    let lib_path = fixtures_root().join("OpaqueLib2.dy");
    std::fs::write(&lib_path, lib_src).unwrap();
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        typecheck_source(main_src, &mut checker);
    }));
    let _ = std::fs::remove_file(&lib_path);
    assert!(result.is_err(), "importing opaque constructor should fail");
}

#[test]
fn opaque_type_compiles_and_runs_on_beam() {
    let lib_src = "
module OpaqueLib3
opaque type Token { Secret(String) }
pub fun make_token (s: String) -> Token
make_token s = Secret s

pub fun reveal (t: Token) -> String
reveal t = case t { Secret(s) -> s }
";
    let main_src = "
module Main
import OpaqueLib3 (Token, make_token, reveal)
pub fun main () -> String
main () = reveal (make_token \"hello\")
";
    let mut checker = make_project_checker();
    let lib_path = fixtures_root().join("OpaqueLib3.dy");
    std::fs::write(&lib_path, lib_src).unwrap();
    typecheck_source(main_src, &mut checker);

    let lib_core = emit_project_module(lib_src, "opaquelib3", &checker);
    let main_core = emit_project_module(main_src, "main", &checker);
    let _ = std::fs::remove_file(&lib_path);

    let dir = assert_erlc_compiles(&lib_core, "opaquelib3");
    let main_core_path = dir.join("main.core");
    std::fs::write(&main_core_path, &main_core).unwrap();
    let output = std::process::Command::new("erlc")
        .arg("-o")
        .arg(&dir)
        .arg(&main_core_path)
        .output()
        .expect("failed to run erlc");
    assert!(
        output.status.success(),
        "erlc failed on main:\n{main_core}\nstderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );

    // Actually run it on the BEAM
    let run_output = std::process::Command::new("erl")
        .arg("-noshell")
        .arg("-pa")
        .arg(&dir)
        .arg("-eval")
        .arg("io:format(\"~s~n\", [main:main()]), init:stop().")
        .output()
        .expect("failed to run erl");
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        run_output.status.success(),
        "erl failed:\nstderr: {}",
        String::from_utf8_lossy(&run_output.stderr)
    );
    let stdout = String::from_utf8_lossy(&run_output.stdout);
    assert!(
        stdout.contains("hello"),
        "expected 'hello' in output, got: {stdout}"
    );
}
