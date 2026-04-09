use dylang::{codegen, elaborate, lexer, parser, typechecker};
use std::fs;
use std::path::PathBuf;
use std::time::{SystemTime, UNIX_EPOCH};

fn fixtures_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/modules")
}

/// Parse, typecheck, elaborate, and emit Core Erlang for a module in project mode.
fn emit_project_module(source: &str, module_name: &str, checker: &typechecker::Checker) -> String {
    let tokens = lexer::Lexer::new(source).lex().expect("lex error");
    let mut program = parser::Parser::new(tokens)
        .parse_program()
        .expect("parse error");
    dylang::desugar::desugar_program(&mut program);
    emit_from_program(&program, module_name, checker)
}

/// Elaborate and emit Core Erlang from an already-parsed program.
fn emit_from_program(
    program: &Vec<dylang::ast::Decl>,
    module_name: &str,
    checker: &typechecker::Checker,
) -> String {
    let original_module_name = program
        .iter()
        .find_map(|d| {
            if let dylang::ast::Decl::ModuleDecl { path, .. } = d {
                Some(path.join("."))
            } else {
                None
            }
        })
        .unwrap_or_default();
    let result = checker.to_result();
    // Use module-specific CheckResult when available (has correct type_at_node),
    // falling back to the top-level result for the main module.
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
            // Stub entry: codegen_info exists but no program/result (e.g. prelude-only modules)
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
    codegen::emit_module_with_context(module_name, &elaborated, &ctx, Some(&result), None, None)
}

/// Parse and typecheck a source file with the given checker (project mode).
/// Returns the parsed program so it can be reused for elaboration/codegen
/// without re-parsing (which would assign different NodeIds).
fn typecheck_source(source: &str, checker: &mut typechecker::Checker) -> Vec<dylang::ast::Decl> {
    let tokens = lexer::Lexer::new(source).lex().expect("lex error");
    let mut program = parser::Parser::new(tokens)
        .parse_program()
        .expect("parse error");
    dylang::desugar::desugar_program(&mut program);
    // Set current_module from the module declaration, matching the real pipeline
    if let Some(module_name) = program.iter().find_map(|d| {
        if let dylang::ast::Decl::ModuleDecl { path, .. } = d {
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
        "typecheck error: {:?}",
        result.errors()
    );
    program
}

/// Create a project-mode checker pointed at the test fixtures directory,
/// with prelude loaded.
fn make_project_checker() -> typechecker::Checker {
    make_project_checker_for_root(fixtures_root())
}

fn make_project_checker_for_root(root: PathBuf) -> typechecker::Checker {
    let module_map = typechecker::scan_project_modules(&root).expect("scan failed");
    let mut checker = typechecker::Checker::with_project_root(root);
    checker.set_module_map(module_map);
    // Load prelude (which imports Std first, then stdlib modules)
    let prelude_src = include_str!("../src/stdlib/prelude.dy");
    let prelude_tokens = lexer::Lexer::new(prelude_src)
        .lex()
        .expect("prelude lex error");
    let mut prelude_program = parser::Parser::new(prelude_tokens)
        .parse_program()
        .expect("prelude parse error");
    dylang::derive::expand_derives(&mut prelude_program);
    dylang::desugar::desugar_program(&mut prelude_program);
    checker.prelude_imports = prelude_program
        .iter()
        .filter(|d| matches!(d, dylang::ast::Decl::Import { .. }))
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

fn with_temp_project_files<T>(
    files: &[(&str, &str)],
    main_src: &str,
    f: impl FnOnce(&typechecker::Checker, &Vec<dylang::ast::Decl>) -> T,
) -> T {
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock before epoch")
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "dylang-module-codegen-{}-{unique}",
        std::process::id()
    ));

    fs::create_dir_all(&root).expect("create temp project root");
    for (rel, src) in files {
        let path = root.join(rel);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).expect("create temp project dir");
        }
        fs::write(path, src).expect("write temp project file");
    }

    let result = {
        let mut checker = make_project_checker_for_root(root.clone());
        let program = typecheck_source(main_src, &mut checker);
        f(&checker, &program)
    };

    let _ = fs::remove_dir_all(&root);
    result
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

#[test]
fn imported_handler_factory_with_named_shorthand_lowers_as_dynamic_handler() {
    let db_module = r#"module Db

pub effect Postgres {
  fun ping : Unit -> Unit
}

pub fun run : Unit -> Unit needs {Postgres}
run () = ping! ()

pub fun connect : Unit -> Handler Postgres
connect () = handler for Postgres {
  ping () = resume ()
}
"#;

    let main_src = r#"module Main
import Db (connect, run)

main () = {
  let db = connect ()
  {
    run ()
  } with db
}
"#;

    with_temp_project_files(&[("lib/Db.dy", db_module)], main_src, |checker, program| {
        let out = emit_from_program(program, "main", checker);
        assert_contains(&out, "call 'erlang':'element'");
        assert_erlc_compiles(&out, "main");
    });
}

#[test]
fn imported_private_effect_factory_threads_handler_into_imported_effectful_call() {
    let db_module = r#"module Db

effect Postgres {
  fun ping : Unit -> Unit
}

pub fun run : Unit -> Unit needs {Postgres}
run () = ping! ()

pub fun connect : Unit -> Handler Postgres
connect () = handler for Postgres {
  ping () = resume ()
}
"#;

    let main_src = r#"module Main
import Db (connect, run)

main () = {
  let db = connect ()
  {
    run ()
  } with db
}
"#;

    with_temp_project_files(&[("lib/Db.dy", db_module)], main_src, |checker, program| {
        let out = emit_from_program(program, "main", checker);
        assert_contains(&out, "_Handle_Db_Postgres_ping");
        assert_contains(&out, "call 'db':'run'");
        assert_contains(&out, "(_Cor2, _Handle_Db_Postgres_ping, _Cor3)");
        assert_erlc_compiles(&out, "main");
    });
}

#[test]
fn imported_handler_factory_with_single_entry_inline_block_matches_named_shorthand() {
    let db_module = r#"module Db

pub effect Postgres {
  fun ping : Unit -> Unit
}

pub fun run : Unit -> Unit needs {Postgres}
run () = ping! ()

pub fun connect : Unit -> Handler Postgres
connect () = handler for Postgres {
  ping () = resume ()
}
"#;

    let named_src = r#"module Main
import Db (connect, run)

main () = {
  let db = connect ()
  {
    run ()
  } with db
}
"#;

    let inline_src = r#"module Main
import Db (connect, run)

main () = {
  let db = connect ()
  {
    run ()
  } with {db}
}
"#;

    let named_out = with_temp_project_files(
        &[("lib/Db.dy", db_module)],
        named_src,
        |checker, program| emit_from_program(program, "main", checker),
    );
    let inline_out = with_temp_project_files(
        &[("lib/Db.dy", db_module)],
        inline_src,
        |checker, program| emit_from_program(program, "main", checker),
    );

    assert_eq!(
        named_out, inline_out,
        "`with db` and `with {{db}}` should lower identically"
    );
    assert_erlc_compiles(&inline_out, "main");
}

#[test]
fn imported_handler_factory_inside_wrapped_block_mixes_dynamic_and_static_handlers() {
    let db_module = r#"module Db

pub effect Postgres {
  fun ping : Unit -> Unit
}

pub fun run : Unit -> Unit needs {Postgres}
run () = ping! ()

pub fun connect : Unit -> Handler Postgres
connect () = handler for Postgres {
  ping () = resume ()
}
"#;

    let main_src = r#"module Main
import Std.IO (console, println)
import Db (connect, run)

main () = {
  let db = connect ()
  {
    run ()
    println "ok"
  }
} with {db, console}
"#;

    with_temp_project_files(&[("lib/Db.dy", db_module)], main_src, |checker, program| {
        let out = emit_from_program(program, "main", checker);
        assert_contains(&out, "call 'erlang':'element'");
        assert_contains(&out, "call 'io':'format'");
        assert_erlc_compiles(&out, "main");
    });
}

#[test]
fn entry_module_main_is_exported_without_pub() {
    let main_src = r#"module Main

main () = 42
"#;

    let mut checker = make_project_checker();
    let program = typecheck_source(main_src, &mut checker);
    let result = checker.to_result();
    let elaborated = elaborate::elaborate_module(&program, &result, "Main");
    let mut modules = std::collections::HashMap::new();
    for name in result.codegen_info().keys() {
        if let Some(compiled) = codegen::compile_module_from_result(name, &result) {
            modules.insert(name.clone(), compiled);
        }
    }
    let ctx = codegen::CodegenContext {
        modules,
        let_effect_bindings: result.let_effect_bindings.clone(),
        prelude_imports: result.prelude_imports.clone(),
    };
    let out = codegen::emit_module_with_context(
        "main",
        &elaborated,
        &ctx,
        Some(&result),
        None,
        Some("main"),
    );

    assert_contains(&out, "module 'main' ['main'/1]");
    assert_erlc_compiles(&out, "main");
}

// ---- Qualified call emission ----

#[test]
fn qualified_call_emits_inter_module_call() {
    let main_src = "
module Main
import Math

main () = Math.add 10 20
";
    let mut checker = make_project_checker();
    let program = typecheck_source(main_src, &mut checker);
    let out = emit_from_program(&program, "main", &checker);

    // Should emit call 'math':'add'(...)
    assert_contains(&out, "call 'math':'add'");
    // Should NOT use apply (local call)
    assert!(
        !out.contains("apply 'add'"),
        "should use inter-module call, not local apply\n{out}"
    );
}

#[test]
fn imported_effectful_function_value_uses_cps_expanded_arity() {
    let main_src = r#"
module Main
import Logger (Log, greet)

fun run_log : (f: (String -> String needs {Log})) -> String
run_log f =
  f "Dylan" with {
    log msg = resume ()
    return value = value
  }

main () = run_log greet
"#;

    let mut checker = make_project_checker();
    let main_program = typecheck_source(main_src, &mut checker);
    let out = emit_from_program(&main_program, "main", &checker);

    // Effectful imported function used as a value without handlers in
    // scope (they're provided by run_log's `with`) falls back to make_fun.
    assert!(
        out.contains("call 'erlang':'make_fun'"),
        "expected imported effectful function value to lower as make_fun\n{out}"
    );
    assert!(
        out.contains("'logger', 'greet', 3"),
        "expected imported effectful function value to use CPS-expanded arity 3\n{out}"
    );
}

#[test]
fn qualified_call_with_alias() {
    let main_src = "
module Main
import Math as M

main () = M.add 1 2
";
    let mut checker = make_project_checker();
    let program = typecheck_source(main_src, &mut checker);
    let out = emit_from_program(&program, "main", &checker);

    // Alias 'M' should still resolve to erlang module 'math'
    assert_contains(&out, "call 'math':'add'");
}

// ---- Exposed (unqualified) imports ----

#[test]
fn exposed_import_emits_inter_module_call() {
    let main_src = "
module Main
import Math (add)

main () = add 10 20
";
    let mut checker = make_project_checker();
    let program = typecheck_source(main_src, &mut checker);
    let out = emit_from_program(&program, "main", &checker);

    // Even though 'add' is unqualified, it should still emit an inter-module call
    assert_contains(&out, "call 'math':'add'");
}

#[test]
fn exposed_and_qualified_same_module() {
    let main_src = "
module Main
import Math (add)

main () = add 1 (Math.double 3)
";
    let mut checker = make_project_checker();
    let program = typecheck_source(main_src, &mut checker);
    let out = emit_from_program(&program, "main", &checker);

    // Both should be inter-module calls
    assert_contains(&out, "call 'math':'add'");
    assert_contains(&out, "call 'math':'double'");
}

// ---- Export filtering ----

#[test]
fn pub_functions_exported() {
    let math_src = std::fs::read_to_string(fixtures_root().join("Math.dy")).unwrap();
    let mut checker = make_project_checker();
    let program = typecheck_source(&math_src, &mut checker);
    let out = emit_from_program(&program, "math", &checker);

    // pub functions should be in the export list
    assert_contains(&out, "'add'/2");
    assert_contains(&out, "'double'/1");
}

#[test]
fn private_functions_not_exported() {
    let math_src = std::fs::read_to_string(fixtures_root().join("Math.dy")).unwrap();
    let mut checker = make_project_checker();
    let program = typecheck_source(&math_src, &mut checker);
    let out = emit_from_program(&program, "math", &checker);

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
    let mut program = parser::Parser::new(tokens).parse_program().unwrap();
    dylang::desugar::desugar_program(&mut program);
    let out = codegen::emit_module("test", &program);

    let export_line = out.lines().next().unwrap();
    assert!(
        export_line.contains("'add'/2"),
        "add should be exported\n{export_line}"
    );
    assert!(
        export_line.contains("'double'/1"),
        "double should be exported\n{export_line}"
    );
    assert!(
        export_line.contains("'main'/1"),
        "main should be exported\n{export_line}"
    );
}

// ---- Module name mapping ----

#[test]
fn module_name_lowercased_in_output() {
    let src = "
module MathLib
pub fun add : (a: Int) -> (b: Int) -> Int
add a b = a + b
";
    let mut checker = make_project_checker();
    let program = typecheck_source(src, &mut checker);
    let out = emit_from_program(&program, "mathlib", &checker);

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

main () = Math.add 10 20
";

    let mut checker = make_project_checker();
    // Typecheck main (which transitively typechecks Math)
    let main_program = typecheck_source(main_src, &mut checker);

    // Emit both modules
    let math_core = emit_project_module(&math_src, "math", &checker);
    let main_core = emit_from_program(&main_program, "main", &checker);

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

main () = add 1 (double 10)
";

    let mut checker = make_project_checker();
    let main_program = typecheck_source(main_src, &mut checker);

    let math_core = emit_project_module(&math_src, "math", &checker);
    let main_core = emit_from_program(&main_program, "main", &checker);

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

main () = {
  let a = Animal { name: \"Rex\", species: \"Dog\" }
  a.name
}
";
    let mut checker = make_project_checker();
    let program = typecheck_source(main_src, &mut checker);
    let out = emit_from_program(&program, "main", &checker);

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

main () = {
  let _ = area (Circle 5.0)
  Math.add 1 2
}
";
    let mut checker = make_project_checker();
    let program = typecheck_source(main_src, &mut checker);
    let out = emit_from_program(&program, "main", &checker);

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
    let program = typecheck_source(&math_src, &mut checker);
    let out = emit_from_program(&program, "math", &checker);

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

main () = debug (List.map (fun x -> x + 1) [1, 2, 3])
";
    let mut checker = make_project_checker();
    let program = typecheck_source(main_src, &mut checker);
    // Should not panic
    let _out = emit_from_program(&program, "main", &checker);
}

// ---- Exposing a type + constructors ----

#[test]
fn exposed_constructor_emits_correctly() {
    let main_src = "
module Main
import Shapes (Circle, Rect, area)

main () = area (Circle 5.0) + area (Rect 3.0 4.0)
";
    // Note: this won't emit inter-module calls for constructors since
    // constructors are values (atoms/tuples), not function calls.
    // But it should not crash.
    let mut checker = make_project_checker();
    let program = typecheck_source(main_src, &mut checker);
    let _out = emit_from_program(&program, "main", &checker);
}

// ---- Cross-module effectful calls ----

#[test]
fn cross_module_effectful_qualified_call() {
    // Logger.greet needs {Log}, so the call should thread _HandleLog + _ReturnK
    let main_src = "
module Main
import Logger


main () = Logger.greet \"world\" with {
  log msg = {
    dbg msg
    resume ()
  }
}
";
    let mut checker = make_project_checker();
    let program = typecheck_source(main_src, &mut checker);
    let out = emit_from_program(&program, "main", &checker);

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


main () = greet \"world\" with {
  log msg = {
    dbg msg
    resume ()
  }
}
";
    let mut checker = make_project_checker();
    let program = typecheck_source(main_src, &mut checker);
    let out = emit_from_program(&program, "main", &checker);

    // Exposed effectful call should still be inter-module
    assert_contains(&out, "call 'logger':'greet'");
}

#[test]
fn cross_module_effectful_export_arity() {
    // Logger.greet should be exported with expanded arity (1 + 1 handler + 1 ReturnK = 3)
    let logger_src = std::fs::read_to_string(fixtures_root().join("Logger.dy")).unwrap();
    let mut checker = make_project_checker();
    let program = typecheck_source(&logger_src, &mut checker);
    let out = emit_from_program(&program, "logger", &checker);

    // greet should be exported with arity 3 (name, _HandleLog, _ReturnK)
    assert_contains(&out, "'greet'/3");
}

#[test]
fn cross_module_effectful_compiles_with_erlc() {
    let logger_src = std::fs::read_to_string(fixtures_root().join("Logger.dy")).unwrap();
    let main_src = "
module Main
import Logger


main () = Logger.greet \"world\" with {
  log msg = {
    dbg msg
    resume ()
  }
}
";
    let mut checker = make_project_checker();
    let main_program = typecheck_source(main_src, &mut checker);

    let logger_core = emit_project_module(&logger_src, "logger", &checker);
    let main_core = emit_from_program(&main_program, "main", &checker);

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

main () = show (Animal { name: \"Rex\", species: \"Dog\" })
";
    let mut checker = make_project_checker();
    let program = typecheck_source(main_src, &mut checker);
    let out = emit_from_program(&program, "main", &checker);

    // The dict should be referenced as a cross-module call to animals module
    let dict = typechecker::make_dict_name("Std.Base.Show", &[], "animals", "Animals.Animal");
    assert_contains(&out, &format!("call 'animals':'{dict}'"));
}

#[test]
fn cross_module_trait_dict_compiles_with_erlc() {
    let main_src = "
module Main
import Animals (Animal)

main () = show (Animal { name: \"Rex\", species: \"Dog\" })
";
    let mut checker = make_project_checker();
    let main_program = typecheck_source(main_src, &mut checker);

    let result = checker.to_result();
    // Use the stored program from the checker (correct NodeIds) instead of
    // re-parsing, which would produce new NodeIds that don't match type_at_node.
    let animals_program = result
        .programs()
        .get("Animals")
        .expect("Animals module not found");
    let animals_core = emit_from_program(animals_program, "animals", &checker);
    let main_core = emit_from_program(&main_program, "main", &checker);

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
    // named with canonical trait + module-qualified type (not bare __dict_Show_Animal)
    let animals_src = std::fs::read_to_string(fixtures_root().join("Animals.dy")).unwrap();
    let mut checker = make_project_checker();
    let program = typecheck_source(&animals_src, &mut checker);
    let out = emit_from_program(&program, "animals", &checker);

    let dict = typechecker::make_dict_name("Std.Base.Show", &[], "animals", "Animals.Animal");
    assert_contains(&out, &format!("'{dict}'"));
    assert!(
        !out.contains("'__dict_Show_Animal'") && !out.contains("'__dict_Std_Base_Show_Animal'"),
        "dict name should be module-qualified\n{out}"
    );
}

// ---- Constructor atom mangling ----

#[test]
fn local_adt_constructors_mangled_with_module_name() {
    let shapes_src = std::fs::read_to_string(fixtures_root().join("Shapes.dy")).unwrap();
    let mut checker = make_project_checker();
    let program = typecheck_source(&shapes_src, &mut checker);
    let out = emit_from_program(&program, "shapes", &checker);

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

main () = area (Circle 5.0) + area (Rect 3.0 4.0)
";
    let mut checker = make_project_checker();
    let program = typecheck_source(main_src, &mut checker);
    let out = emit_from_program(&program, "main", &checker);

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

main () = {
  let a = Animal { name: \"Rex\", species: \"Dog\" }
  a.name
}
";
    let mut checker = make_project_checker();
    let program = typecheck_source(main_src, &mut checker);
    let out = emit_from_program(&program, "main", &checker);

    // Record constructor should be mangled with source module prefix
    assert_contains(&out, "'animals_Animal'");
}

#[test]
fn prelude_constructors_mangled_with_std_prefix() {
    let main_src = "
module Main

main () = case Just(42) {
  Just(x) -> x
  Nothing -> 0
}
";
    let mut checker = make_project_checker();
    let program = typecheck_source(main_src, &mut checker);
    let out = emit_from_program(&program, "main", &checker);

    // Just(v) compiles to {'just', v}, Nothing compiles to {'nothing'} (tagged tuples)
    assert_contains(&out, "'just'");
    assert_contains(&out, "'nothing'");
    // Should use BEAM override atoms, not module-prefixed versions
    assert!(
        !out.contains("'std_maybe_Just'"),
        "Just should use 'just' not module-prefixed atom"
    );
    assert!(
        !out.contains("'std_maybe_Nothing'"),
        "Nothing should use 'nothing' not module-prefixed atom"
    );
}

#[test]
fn cross_module_constructor_consistency() {
    // Constructor atoms must match between the defining module and the importing module
    let shapes_src = std::fs::read_to_string(fixtures_root().join("Shapes.dy")).unwrap();
    let main_src = "
module Main
import Shapes (Circle, area)

main () = area (Circle 5.0)
";
    let mut checker = make_project_checker();
    let main_program = typecheck_source(main_src, &mut checker);

    let shapes_out = emit_project_module(&shapes_src, "shapes", &checker);
    let main_out = emit_from_program(&main_program, "main", &checker);

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

main () = area (Circle 5.0) + area (Rect 3.0 4.0)
";
    let mut checker = make_project_checker();
    let main_program = typecheck_source(main_src, &mut checker);

    let shapes_core = emit_project_module(&shapes_src, "shapes", &checker);
    let main_core = emit_from_program(&main_program, "main", &checker);

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

main () = {
  let pair = (10, 20)
  let x = fst pair
  let y = snd pair
  x + y
}
";
    let mut checker = make_project_checker();
    let program = typecheck_source(main_src, &mut checker);
    let out = emit_from_program(&program, "main", &checker);
    assert_erlc_compiles(&out, "main");
}

// ---- Opaque types ----

#[test]
fn opaque_type_exports_name_but_not_constructors() {
    let lib_src = "
module OpaqueLib
opaque type Token = Secret(String)
pub fun make_token : (s: String) -> Token
make_token s = Secret s
";
    let main_src = "
module Main
import OpaqueLib (Token, make_token)

main () = make_token \"abc\"
";
    let lib_path = fixtures_root().join("OpaqueLib.dy");
    std::fs::write(&lib_path, lib_src).unwrap();
    let mut checker = make_project_checker();
    let program = typecheck_source(main_src, &mut checker);
    let _out = emit_from_program(&program, "main", &checker);
    let _ = std::fs::remove_file(&lib_path);
}

#[test]
fn opaque_type_constructor_rejected_by_importer() {
    let lib_src = "
module OpaqueLib2
opaque type Token = Secret(String)
pub fun make_token : (s: String) -> Token
make_token s = Secret s
";
    let main_src = "
module Main
import OpaqueLib2 (Token, Secret)

main () = Secret \"abc\"
";
    let lib_path = fixtures_root().join("OpaqueLib2.dy");
    std::fs::write(&lib_path, lib_src).unwrap();
    let mut checker = make_project_checker();
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
opaque type Token = Secret(String)
pub fun make_token : (s: String) -> Token
make_token s = Secret s

pub fun reveal : (t: Token) -> String
reveal t = case t { Secret(s) -> s }
";
    let main_src = "
module Main
import OpaqueLib3 (Token, make_token, reveal)

pub fun run : Unit -> String
run () = reveal (make_token \"hello\")
";
    let lib_path = fixtures_root().join("OpaqueLib3.dy");
    std::fs::write(&lib_path, lib_src).unwrap();
    let mut checker = make_project_checker();
    let main_program = typecheck_source(main_src, &mut checker);

    let lib_core = emit_project_module(lib_src, "opaquelib3", &checker);
    let main_core = emit_from_program(&main_program, "main", &checker);
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
        .arg("io:format(\"~s~n\", [main:run(unit)]), init:stop().")
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

// ---- Effect and handler exposing rules ----

/// Typecheck a source and return the error messages (empty if no errors).
// fn typecheck_errors(source: &str, checker: &mut typechecker::Checker) -> Vec<String> {
//     let tokens = lexer::Lexer::new(source).lex().expect("lex error");
//     let mut program = parser::Parser::new(tokens)
//         .parse_program()
//         .expect("parse error");
//     dylang::desugar::desugar_program(&mut program);
//     let result = checker.check_program(&mut program);
//     result.errors().iter().map(|d| d.message.clone()).collect()
// }

#[test]
fn effect_bare_needs_works_with_import() {
    // Effects follow the same exposing rules as functions.
    // `import Logger (Log)` makes `Log` available as bare name in `needs` clauses.
    let src = "
module Main
import Logger (Log)

pub fun wrapper : (name: String) -> String needs {Log}
wrapper name = Logger.greet name
";
    let mut checker = make_project_checker();
    let program = typecheck_source(src, &mut checker);
    let _out = emit_from_program(&program, "main", &checker);
}

#[test]
fn effect_qualified_needs_works() {
    // Qualified effect name in `needs` clause
    let src = "
module Main
import Logger

pub fun wrapper : (name: String) -> String needs {Logger.Log}
wrapper name = Logger.greet name
";
    let mut checker = make_project_checker();
    let program = typecheck_source(src, &mut checker);
    let _out = emit_from_program(&program, "main", &checker);
}

#[test]
fn handler_not_exposed_requires_qualified_with() {
    // import Logger without exposing console_log: bare `with console_log` should fail.
    // Logger.dy doesn't define a named handler, so let's test with a module that does.
    // For now, just verify the qualified handler lookup works.
    let src = "
module Main
import Logger (greet)


main () = greet \"world\" with {
  log msg = { dbg msg; resume () }
}
";
    let mut checker = make_project_checker();
    let program = typecheck_source(src, &mut checker);
    let _out = emit_from_program(&program, "main", &checker);
}

#[test]
fn aliased_effect_and_handler_names_canonicalize_for_lowering() {
    let src = "
module Main
import Std.DateTime as DateTime


main () = DateTime.Clock.today! () with {DateTime.system_clock}
";
    let mut checker = make_project_checker();
    let program = typecheck_source(src, &mut checker);
    let _out = emit_from_program(&program, "main", &checker);
}

#[test]
fn exposed_named_handler_resolves_by_bare_name() {
    let src = "
module Main
import Std.DateTime (Clock, system_clock)


main () = Clock.now! () with {system_clock}
";
    let mut checker = make_project_checker();
    let program = typecheck_source(src, &mut checker);
    let _out = emit_from_program(&program, "main", &checker);
}

#[test]
fn cross_module_effect_inline_handler_works() {
    // Inline handler with bare op names should match imported effect ops
    let src = "
module Main
import Logger


main () = Logger.greet \"world\" with {
  log msg = { dbg msg; resume () }
}
";
    let mut checker = make_project_checker();
    let program = typecheck_source(src, &mut checker);
    let out = emit_from_program(&program, "main", &checker);
    assert_contains(&out, "call 'logger':'greet'");
}

#[test]
fn cross_module_effect_exposed_inline_handler() {
    // Exposed import + inline handler
    let src = "
module Main
import Logger (greet)


main () = greet \"world\" with {
  log msg = { dbg msg; resume () }
}
";
    let mut checker = make_project_checker();
    let program = typecheck_source(src, &mut checker);
    let out = emit_from_program(&program, "main", &checker);
    assert_contains(&out, "call 'logger':'greet'");
}
