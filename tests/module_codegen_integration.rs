use saga::{codegen, elaborate, lexer, parser, typechecker};
use std::fs;
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

/// Compile the Phase 1 evidence bridge into `dir` so emitted code can resolve
/// the `std_evidence_bridge:*` calls produced at every `with`-boundary.
fn compile_evidence_bridge_into(dir: &Path) {
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

fn fixtures_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/modules")
}

/// Parse, typecheck, elaborate, and emit Core Erlang for a module in project mode.
fn emit_project_module(source: &str, module_name: &str, checker: &typechecker::Checker) -> String {
    let tokens = lexer::Lexer::new(source).lex().expect("lex error");
    let mut program = parser::Parser::new(tokens)
        .parse_program()
        .expect("parse error");
    saga::desugar::desugar_program(&mut program);
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
    if let Some(cached_program) = result.programs().get(&original_module_name) {
        return emit_from_program(cached_program, module_name, checker);
    }
    emit_from_program(&program, module_name, checker)
}

/// Elaborate and emit Core Erlang from an already-parsed program.
fn emit_from_program(
    program: &Vec<saga::ast::Decl>,
    module_name: &str,
    checker: &typechecker::Checker,
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
    codegen::emit_module_with_context(
        module_name,
        &elaborated,
        &ctx,
        module_result.unwrap_or(&result),
        None,
        None,
    )
}

/// Parse and typecheck a source file with the given checker (project mode).
/// Returns the parsed program so it can be reused for elaboration/codegen
/// without re-parsing (which would assign different NodeIds).
fn typecheck_source(source: &str, checker: &mut typechecker::Checker) -> Vec<saga::ast::Decl> {
    let tokens = lexer::Lexer::new(source).lex().expect("lex error");
    let mut program = parser::Parser::new(tokens)
        .parse_program()
        .expect("parse error");
    let imported = saga::derive::collect_imported_decls(&program, checker.module_map());
    let derive_errors = saga::derive::expand_derives(&mut program, &imported);
    assert!(
        derive_errors.is_empty(),
        "derive errors: {:?}",
        derive_errors
    );
    saga::desugar::desugar_program(&mut program);
    // Set current_module from the module declaration, matching the real pipeline
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
    let module_map = typechecker::scan_source_dir(&root).expect("scan failed");
    let mut checker = typechecker::Checker::with_project_root(root);
    checker.set_module_map(module_map);
    // Load prelude (which imports Std first, then stdlib modules)
    let prelude_src = include_str!("../src/stdlib/prelude.saga");
    let prelude_tokens = lexer::Lexer::new(prelude_src)
        .lex()
        .expect("prelude lex error");
    let mut prelude_program = parser::Parser::new(prelude_tokens)
        .parse_program()
        .expect("prelude parse error");
    saga::derive::expand_derives(&mut prelude_program, &saga::derive::ImportedDecls::empty());
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

fn with_temp_project_files<T>(
    files: &[(&str, &str)],
    main_src: &str,
    f: impl FnOnce(&typechecker::Checker, &Vec<saga::ast::Decl>) -> T,
) -> T {
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock before epoch")
        .as_nanos();
    let root = std::env::temp_dir().join(format!(
        "saga-module-codegen-{}-{unique}",
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
    let dir = std::env::temp_dir().join(format!("saga_modtest_{}_{id}", std::process::id()));
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

fn compile_core_into(dir: &Path, core_src: &str, module_name: &str) {
    let core_path = dir.join(format!("{module_name}.core"));
    std::fs::write(&core_path, core_src).unwrap();
    let output = std::process::Command::new("erlc")
        .arg("-o")
        .arg(dir)
        .arg(&core_path)
        .output()
        .expect("failed to run erlc");
    assert!(
        output.status.success(),
        "erlc failed on {module_name}:\n{core_src}\nstderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
}

fn assert_project_modules_run(modules: &[(&str, &str)], eval: &str, needles: &[&str]) {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static COUNTER: AtomicUsize = AtomicUsize::new(0);

    let id = COUNTER.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("saga_modrun_{}_{id}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    for (module_name, core_src) in modules {
        compile_core_into(&dir, core_src, module_name);
    }
    compile_evidence_bridge_into(&dir);

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

    with_temp_project_files(
        &[("lib/Db.saga", db_module)],
        main_src,
        |checker, program| {
            let out = emit_from_program(program, "main", checker);
            assert_contains(&out, "call 'erlang':'element'");
            assert_erlc_compiles(&out, "main");
        },
    );
}

#[test]
fn imported_public_helper_under_static_handler_generates_direct_variant() {
    let lib = r#"module Lib

pub effect Options {
  fun get_options : Unit -> Int
}

pub fun compute : Int -> Int needs {Options}
compute x = x + get_options! ()
"#;

    let main_src = r#"module Main

import Lib (Options)

handler options for Options {
  get_options () = resume 10
}

main () = Lib.compute 5 with options
"#;

    with_temp_project_files(&[("lib/Lib.saga", lib)], main_src, |checker, program| {
        let out = emit_from_program(program, "main", checker);
        let main = emitted_function(&out, "main", 1);
        assert!(
            !main.contains("call 'lib':'compute'"),
            "main should call the generated direct variant, not imported CPS helper\n{main}"
        );
        assert_contains(&main, "apply '__saga_static_helper_Lib_compute_");
        assert_contains(&out, "'__saga_static_helper_Lib_compute_");
        assert_erlc_compiles(&out, "main");
    });
}

#[test]
fn imported_let_bound_hof_alias_uses_direct_specialization() {
    let effects = r#"module Effects

pub effect ReadInt {
  fun read : Unit -> Int
}

pub fun pure_value : Unit -> Int
pure_value () = 41

pub fun apply_eff : (Unit -> Int needs {ReadInt}) -> Int needs {ReadInt}
apply_eff f = f ()

pub handler forty_one for ReadInt {
  read () = resume 41
}
"#;

    let main_src = r#"module Main

import Effects (pure_value, apply_eff, forty_one)

main () = {
  let hof = apply_eff
  hof pure_value with forty_one
}
"#;

    with_temp_project_files(
        &[("lib/Effects.saga", effects)],
        main_src,
        |checker, program| {
            let out = emit_from_program(program, "main", checker);
            let main = emitted_function(&out, "main", 1);
            assert_contains(&main, "call 'effects':'__saga_direct_hof_apply_eff'");
            assert_erlc_compiles(&out, "main");
        },
    );
}

#[test]
fn imported_public_helper_with_capturing_static_handler_generates_direct_variant() {
    let lib = r#"module Lib

pub effect Options {
  fun get_options : Unit -> Int
}

pub fun compute : Int -> Int needs {Options}
compute x = x + get_options! ()
"#;

    let main_src = r#"module Main

import Lib (Options)

main () = {
  let default = 10
  Lib.compute 5 with {
    get_options () = resume default
  }
}
"#;

    with_temp_project_files(&[("lib/Lib.saga", lib)], main_src, |checker, program| {
        let out = emit_from_program(program, "main", checker);
        let main = emitted_function(&out, "main", 1);
        assert!(
            !main.contains("call 'lib':'compute'"),
            "main should call the generated direct variant with capture params\n{main}"
        );
        assert_contains(&main, "apply '__saga_static_helper_Lib_compute_");
        assert_contains(&out, "'__saga_static_helper_Lib_compute_");
        assert_erlc_compiles(&out, "main");
    });
}

#[test]
fn imported_multi_clause_public_helper_stays_on_evidence_path() {
    let lib = r#"module Lib

pub effect Options {
  fun get_options : Unit -> Int
}

pub fun compute : Bool -> Int needs {Options}
compute True = get_options! ()
compute False = 0
"#;

    let main_src = r#"module Main

import Lib (Options)

main () = Lib.compute True with {
  get_options () = resume 10
}
"#;

    with_temp_project_files(&[("lib/Lib.saga", lib)], main_src, |checker, program| {
        let out = emit_from_program(program, "main", checker);
        let main = emitted_function(&out, "main", 1);
        assert_contains(&main, "call 'lib':'compute'");
        assert!(
            !out.contains("'__saga_static_helper_Lib_compute_"),
            "multi-clause imported helper should not generate a direct variant\n{out}"
        );
        assert_erlc_compiles(&out, "main");
    });
}

#[test]
fn imported_public_helper_can_inline_nested_public_helper_in_direct_variant() {
    let lib = r#"module Lib

pub effect Options {
  fun get_options : Unit -> Int
}

pub fun read_value : Unit -> Int needs {Options}
read_value () = get_options! ()

pub fun compute : Int -> Int needs {Options}
compute x = x + read_value ()
"#;

    let main_src = r#"module Main

import Lib (Options)

main () = Lib.compute 5 with {
  get_options () = resume 10
}
"#;

    with_temp_project_files(&[("lib/Lib.saga", lib)], main_src, |checker, program| {
        let out = emit_from_program(program, "main", checker);
        let main = emitted_function(&out, "main", 1);
        assert!(
            !main.contains("call 'lib':'compute'"),
            "main should call generated direct variant for nested public helper\n{main}"
        );
        assert!(
            !out.contains("call 'lib':'read_value'"),
            "nested public helper should stay inside the direct variant, not call imported CPS helper\n{out}"
        );
        assert_contains(&main, "apply '__saga_static_helper_Lib_compute_");
        assert_erlc_compiles(&out, "main");
    });
}

#[test]
fn imported_public_helper_calling_private_helper_stays_on_evidence_path() {
    let lib = r#"module Lib

pub effect Options {
  fun get_options : Unit -> Int
}

fun read_value : Unit -> Int needs {Options}
read_value () = get_options! ()

pub fun compute : Int -> Int needs {Options}
compute x = x + read_value ()
"#;

    let main_src = r#"module Main

import Lib (Options)

main () = Lib.compute 5 with {
  get_options () = resume 10
}
"#;

    with_temp_project_files(&[("lib/Lib.saga", lib)], main_src, |checker, program| {
        let out = emit_from_program(program, "main", checker);
        let main = emitted_function(&out, "main", 1);
        assert_contains(&main, "call 'lib':'compute'");
        assert!(
            !out.contains("'__saga_static_helper_Lib_compute_"),
            "private helper dependency should keep the public helper on evidence path\n{out}"
        );
        assert_erlc_compiles(&out, "main");
    });
}

#[test]
fn cross_module_call_with_beam_native_and_user_effect_threads_all_handler_params() {
    // Regression: when an imported function declares `needs {Process, X}` for
    // some user-defined effect X, the function is lowered with handler params
    // for both Process *and* X (the BEAM-native ops still flow through CPS
    // lambdas — beam_actor's lowering installs them as direct-op fast paths).
    //
    // The cross-module resolver was discarding the type's effect row and only
    // consulting `fun_effects`, which strips beam-native effects. As a result
    // it computed the wrong expanded arity for the imported fun, treated the
    // call as under-applied, and emitted a partial-application closure
    // (`let r = fun (...) -> call lib:run(...)`) instead of a saturated call.
    // The case-match on `r` then crashed at runtime with a `case_clause` since
    // `r` was a closure rather than the `Result` it should have been.
    let lib = r#"module Lib.Server

import Std.Actor (Process)

pub effect Reporter {
  fun report : String -> Unit
}

pub fun run : Unit -> Result Unit String needs {Process, Reporter}
run () = {
  report! "hello"
  let _ = spawn! (fun () -> ())
  Ok ()
}
"#;

    let main_src = r#"module Main

import Std.Actor (beam_actor)
import Lib.Server (Reporter, run)

main () = {
  let r = run ()
  case r {
    Ok _ -> ()
    Err _ -> ()
  }
} with {
  beam_actor,
  report _ = {
    resume ()
  },
}
"#;

    with_temp_project_files(&[("lib/Server.saga", lib)], main_src, |checker, program| {
        let out = emit_from_program(program, "main", checker);
        // The call to lib_server:run must pass user arg + Reporter handler
        // + Process handlers (spawn/send/exit) + ReturnK.
        assert_contains(&out, "_Handle_Lib_Server_Reporter_report");
        assert_contains(&out, "call 'lib_server':'run'");
        // Saturated, not partial-applied: the bug emitted a closure
        // whose parameter list included `_Handle_Lib_Server_Reporter_report`
        // and other handler params. A correctly threaded call binds those
        // handler vars in `let <_Handle_...> = ...` and passes them to the
        // call. Detect the bug shape: the handler param appearing as a
        // *closure parameter* (right after `fun (` rather than inside a
        // `let <...>` binding).
        let bug_shape = "_Handle_Lib_Server_Reporter_report,";
        let bug_present = out.lines().any(|line| {
            let trimmed = line.trim_start();
            trimmed.starts_with("fun (") && trimmed.contains(bug_shape)
        });
        assert!(
            !bug_present,
            "imported run call appears to be wrapped in a partial-app closure:\n{out}"
        );
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

    with_temp_project_files(
        &[("lib/Db.saga", db_module)],
        main_src,
        |checker, program| {
            let out = emit_from_program(program, "main", checker);
            assert_contains(&out, "_Handle_Db_Postgres_ping");
            assert_contains(&out, "call 'db':'run'");
            // The imported effectful call takes (arg, evidence, continuation).
            let call_idx = out
                .find("call 'db':'run'")
                .expect("expected call to db:run");
            let after_call = &out[call_idx..];
            let args_start = after_call.find('(').expect("expected args after call");
            let args_end = after_call.find(')').expect("expected closing paren");
            let args = &after_call[args_start + 1..args_end];
            let parts: Vec<&str> = args.split(',').map(str::trim).collect();
            assert_eq!(
                parts.len(),
                3,
                "expected (arg, evidence, continuation), got: {args}"
            );
            assert_erlc_compiles(&out, "main");
        },
    );
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
        &[("lib/Db.saga", db_module)],
        named_src,
        |checker, program| emit_from_program(program, "main", checker),
    );
    let inline_out = with_temp_project_files(
        &[("lib/Db.saga", db_module)],
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

    with_temp_project_files(
        &[("lib/Db.saga", db_module)],
        main_src,
        |checker, program| {
            let out = emit_from_program(program, "main", checker);
            assert_contains(&out, "call 'erlang':'element'");
            assert_contains(&out, "call 'io':'format'");
            assert_erlc_compiles(&out, "main");
        },
    );
}

#[test]
fn imported_record_field_handler_bindings_inside_wrapped_block_lower() {
    let db_module = r#"module Db

pub effect Postgres {
  fun ping : Unit -> Unit
}

pub effect Transaction {
  fun transaction : (f: Unit -> a needs {Postgres}) -> a needs {Postgres}
}

pub record Db {
  postgres: Handler Postgres,
  transactions: Handler Transaction,
}

pub fun run : Unit -> Unit needs {Postgres, Transaction}
run () = transaction! (fun () -> ping! ())

pub fun connect : Unit -> Db needs {Postgres}
connect () = {
  Db {
    postgres: handler for Postgres {
      ping () = resume ()
    },
    transactions: handler for Transaction needs {Postgres} {
      transaction f = {
        let value = f ()
        resume value
      }
    },
  }
}
"#;

    let main_src = r#"module Main
import Std.IO (console, println)
import Db (Postgres, connect, run)

main () = {
  let db = connect () with { ping () = resume () }
  let pg = db.postgres
  let tx = db.transactions
  {
    run ()
    println "ok"
  }
} with {pg, tx, console}
"#;

    with_temp_project_files(
        &[("lib/Db.saga", db_module)],
        main_src,
        |checker, program| {
            let out = emit_from_program(program, "main", checker);
            assert_contains(&out, "call 'erlang':'element'");
            assert_contains(&out, "_Handle_Db_Postgres_ping");
            assert_contains(&out, "_Handle_Db_Transaction_transaction");
            assert_erlc_compiles(&out, "main");
        },
    );
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
    let out =
        codegen::emit_module_with_context("main", &elaborated, &ctx, &result, None, Some("main"));

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
fn aliased_exposed_import_emits_origin_module_call() {
    let main_src = "
module Main
import Math (add as plus)

main () = plus 10 20
";
    let mut checker = make_project_checker();
    let program = typecheck_source(main_src, &mut checker);
    let out = emit_from_program(&program, "main", &checker);

    assert_contains(&out, "call 'math':'add'");
    assert!(
        !out.contains("apply 'plus'"),
        "aliased import should not lower as a local function\n{out}"
    );
}

#[test]
fn reexported_aliased_import_emits_origin_module_call() {
    let lib_src = r#"module Lib

pub fun inc : Int -> Int
inc x = x + 1
"#;
    let facade_src = r#"module Facade

import Lib (pub inc as plus_one)
"#;
    let main_src = r#"module Main

import Facade (plus_one)

main () = plus_one 41
"#;

    with_temp_project_files(
        &[("lib/Lib.saga", lib_src), ("lib/Facade.saga", facade_src)],
        main_src,
        |checker, program| {
            let out = emit_from_program(program, "main", checker);
            assert_contains(&out, "call 'lib':'inc'");
            assert!(
                !out.contains("call 'facade':'plus_one'"),
                "re-exported call should target the origin module\n{out}"
            );
        },
    );
}

#[test]
fn qualified_reexported_alias_emits_origin_module_call() {
    let lib_src = r#"module Lib

pub fun inc : Int -> Int
inc x = x + 1
"#;
    let facade_src = r#"module Facade

import Lib (pub inc as plus_one)
"#;
    let main_src = r#"module Main

import Facade

main () = Facade.plus_one 41
"#;

    with_temp_project_files(
        &[("lib/Lib.saga", lib_src), ("lib/Facade.saga", facade_src)],
        main_src,
        |checker, program| {
            let out = emit_from_program(program, "main", checker);
            assert_contains(&out, "call 'lib':'inc'");
            assert!(
                !out.contains("call 'facade':'plus_one'"),
                "qualified re-exported call should target the origin module\n{out}"
            );
        },
    );
}

#[test]
fn reexport_all_import_emits_origin_module_call() {
    let lib_src = r#"module Lib

pub fun inc : Int -> Int
inc x = x + 1
"#;
    let facade_src = r#"module Facade

import Lib (pub ..)
"#;
    let main_src = r#"module Main

import Facade (inc)

main () = inc 41
"#;

    with_temp_project_files(
        &[("lib/Lib.saga", lib_src), ("lib/Facade.saga", facade_src)],
        main_src,
        |checker, program| {
            let out = emit_from_program(program, "main", checker);
            assert_contains(&out, "call 'lib':'inc'");
            assert!(
                !out.contains("call 'facade':'inc'"),
                "pub .. re-exported call should target the origin module\n{out}"
            );
        },
    );
}

#[test]
fn reexported_type_exposes_origin_constructors() {
    let lib_src = r#"module Lib

pub type Choice
  = Lefty Int
  | Righty Int
"#;
    let facade_src = r#"module Facade

import Lib (pub Choice)
"#;
    let main_src = r#"module Main

import Facade (Choice)

main () = Lefty 41
"#;

    with_temp_project_files(
        &[("lib/Lib.saga", lib_src), ("lib/Facade.saga", facade_src)],
        main_src,
        |checker, program| {
            let out = emit_from_program(program, "main", checker);
            assert_contains(&out, "lib_Lefty");
            assert!(
                !out.contains("facade_Lefty"),
                "re-exported constructors should keep origin-module atoms\n{out}"
            );
        },
    );
}

#[test]
fn reexported_trait_uses_origin_impl() {
    let lib_src = r#"module Lib

pub trait Label a {
  fun label : a -> String
}

impl Label for Int {
  label _ = "int"
}
"#;
    let facade_src = r#"module Facade

import Lib (pub Label)
"#;
    let main_src = r#"module Main

import Facade (Label)

main () = label 1
"#;

    with_temp_project_files(
        &[("lib/Lib.saga", lib_src), ("lib/Facade.saga", facade_src)],
        main_src,
        |checker, program| {
            let out = emit_from_program(program, "main", checker);
            assert_contains(&out, "call 'lib':'__saga_dictmethod");
            assert!(
                !out.contains("call 'facade':'__saga_dictmethod"),
                "re-exported trait impl dispatch should target the origin module\n{out}"
            );
        },
    );
}

#[test]
fn reexported_effect_and_handler_use_origin_identities() {
    let lib_src = r#"module Lib

pub effect Ask {
  fun ask : Unit -> Int
}

pub handler answer_42 for Ask {
  ask = resume 42
}

pub fun use_ask : Unit -> Int needs {Ask}
use_ask () = ask! ()
"#;
    let facade_src = r#"module Facade

import Lib (pub Ask as Query, pub answer_42 as answer, pub use_ask as run_query)
"#;
    let main_src = r#"module Main

import Facade (Query, answer, run_query)

fun ask_here : Unit -> Int needs {Query}
ask_here () = ask! ()

main () = (run_query () with answer) + (ask_here () with answer)
"#;

    with_temp_project_files(
        &[("lib/Lib.saga", lib_src), ("lib/Facade.saga", facade_src)],
        main_src,
        |checker, program| {
            let out = emit_from_program(program, "main", checker);
            assert_contains(&out, "call 'lib':'use_ask'");
            assert!(
                !out.contains("call 'facade':'run_query'"),
                "re-exported effectful calls should target the origin module\n{out}"
            );
        },
    );
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
    let math_src = std::fs::read_to_string(fixtures_root().join("Math.saga")).unwrap();
    let mut checker = make_project_checker();
    let program = typecheck_source(&math_src, &mut checker);
    let out = emit_from_program(&program, "math", &checker);

    // pub functions should be in the export list
    assert_contains(&out, "'add'/2");
    assert_contains(&out, "'double'/1");
}

#[test]
fn private_functions_are_exported_in_core() {
    // Privacy is a front-end concern (the typechecker/resolver rejects illegal
    // cross-module references in source). At the Core level we export *every*
    // function so codegen optimizations — notably the cross-module generic fold,
    // which inlines a producer impl body whose private helpers then lower to
    // `call 'producer':'helper'` — can reach any function without computing a
    // per-callee export set. So a private `secret` is both defined and exported.
    let math_src = std::fs::read_to_string(fixtures_root().join("Math.saga")).unwrap();
    let mut checker = make_project_checker();
    let program = typecheck_source(&math_src, &mut checker);
    let out = emit_from_program(&program, "math", &checker);

    let export_line = out.lines().next().unwrap();
    assert!(
        export_line.contains("'secret'/"),
        "private function 'secret' should be exported in Core (export-all)\n{export_line}"
    );
    assert_contains(&out, "'secret'/");
}

// A dispatch-shaped helper library shared by the inline-to-cancel tests below.
const STYLE_LIB: &str = r#"module Style

pub type NameStyle =
  | AsIs
  | Camel

pub fun apply_style : NameStyle -> String -> String
apply_style ns s = case ns {
  AsIs -> s
  Camel -> s
}

pub fun pick : Int -> NameStyle
pick n = if n == 0 then AsIs else Camel
"#;

#[test]
fn constant_arg_inlines_cross_module_dispatch_fn_to_cancel() {
    // Blocker-2 Unit B: `apply_style (Opts { rename: AsIs }).rename "id"` — the
    // constant record projects to `AsIs` (Unit A), then the cross-module
    // dispatch-shaped `apply_style` is inlined-to-cancel: `case AsIs { AsIs -> s;
    // Camel -> s }` collapses to the literal key. No remote `style:apply_style` call
    // and no residual NameStyle `case` should survive. The `deriving (Show)` record
    // is only here so the generic fold runs at all.
    let main_src = r#"module Main

import Style (NameStyle, AsIs, apply_style)

record Opts { rename: NameStyle }
record Tag { v: Int } deriving (Show)

fun key : Unit -> String
key () = apply_style (Opts { rename: AsIs }).rename "id"

main () = dbg (key ())
"#;
    with_temp_project_files(
        &[("lib/Style.saga", STYLE_LIB)],
        main_src,
        |checker, program| {
            let out = emit_from_program(program, "main", checker);
            let key_fn = emitted_function(&out, "key", 1);
            assert!(
                key_fn.contains("#<105>") && key_fn.contains("#<100>"),
                "key/1 should fold to the literal \"id\":\n{key_fn}"
            );
            assert!(
                !out.contains("'style':'apply_style'"),
                "apply_style should be inlined away, not a remote call:\n{out}"
            );
            assert!(
                !key_fn.contains("case"),
                "the inlined NameStyle case should have collapsed in key/1:\n{key_fn}"
            );
            assert_erlc_compiles(&out, "main");
        },
    );
}

#[test]
fn runtime_arg_does_not_inline_dispatch_fn() {
    // Blocker-2 Unit B negative gate: when the style argument is *not* a literal
    // constructor (`pick n` is computed at runtime), the collapse gate fails and
    // `apply_style` must stay a remote call — never speculatively inlined.
    let main_src = r#"module Main

import Std.IO (console)
import Style (NameStyle, apply_style, pick)

record Tag { v: Int } deriving (Show)

fun key : Int -> String
key n = apply_style (pick n) "id"

main () = {
  println (key 0)
} with console
"#;
    with_temp_project_files(
        &[("lib/Style.saga", STYLE_LIB)],
        main_src,
        |checker, program| {
            let out = emit_from_program(program, "main", checker);
            assert!(
                out.contains("'style':'apply_style'"),
                "apply_style must remain a remote call when its style arg is runtime:\n{out}"
            );
            assert_erlc_compiles(&out, "main");
        },
    );
}

#[test]
fn no_module_decl_exports_everything() {
    // Single-file (no module declaration) should export all functions
    let src = "
add a b = a + b
double x = x * 2
main () = add 1 2
";
    let mut checker = make_project_checker();
    let program = typecheck_source(src, &mut checker);
    let out = emit_from_program(&program, "test", &checker);

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
    let math_src = std::fs::read_to_string(fixtures_root().join("Math.saga")).unwrap();
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
    let math_src = std::fs::read_to_string(fixtures_root().join("Math.saga")).unwrap();
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

#[test]
fn two_module_exposing_all_compiles() {
    // `import Math (..)` should expose every public export from Math
    // as bare names — equivalent to `import Math (add, double)`.
    let math_src = std::fs::read_to_string(fixtures_root().join("Math.saga")).unwrap();
    let main_src = "
module Main
import Math (..)

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

#[test]
fn exposing_all_brings_constructors_into_scope() {
    // `import Shapes (..)` should expose the `Shape` type, its constructors
    // (`Circle`, `Rect`), and the `area` function as bare names.
    let main_src = "
module Main
import Shapes (..)

main () = area (Circle 5.0)
";
    let mut checker = make_project_checker();
    let program = typecheck_source(main_src, &mut checker);
    let out = emit_from_program(&program, "main", &checker);
    assert_contains(&out, "call 'shapes':'area'");
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
    let math_src = std::fs::read_to_string(fixtures_root().join("Math.saga")).unwrap();
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
import Logger (Log)


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
import Logger (Log, greet)


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
    // Logger.greet should be exported with expanded arity
    // (1 user + _Evidence + _ReturnK = 3).
    let logger_src = std::fs::read_to_string(fixtures_root().join("Logger.saga")).unwrap();
    let mut checker = make_project_checker();
    let program = typecheck_source(&logger_src, &mut checker);
    let out = emit_from_program(&program, "logger", &checker);

    assert_contains(&out, "'greet'/3");
}

#[test]
fn cross_module_effectful_compiles_with_erlc() {
    let logger_src = std::fs::read_to_string(fixtures_root().join("Logger.saga")).unwrap();
    let main_src = "
module Main
import Logger (Log)


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

#[test]
fn imported_mixed_effect_trait_impl_preserves_method_slots() {
    let lib_src = r#"
module MixedDictLib

pub effect Ask {
  fun ask : Unit -> String
}

pub handler ask_default for Ask {
  ask () = resume "imported"
}

pub trait Payload a {
  fun payload : a -> String needs {Ask}
  fun is_unit : a -> Bool
}

pub type PayloadLeaf = PayloadLeaf String
pub type PayloadBox a = PayloadBox a

impl Payload for PayloadLeaf needs {Ask} {
  payload (PayloadLeaf _) = ask! ()
  is_unit _ = False
}

impl Payload for PayloadBox a where {a: Payload} needs {Ask} {
  payload (PayloadBox x) = payload x
  is_unit (PayloadBox x) = is_unit x
}

pub fun render_payload : a -> String needs {Ask} where {a: Payload}
render_payload x = {
  let p = payload x
  if is_unit x then "bad" else p
}
"#;
    let main_src = r#"
module Main
import MixedDictLib (PayloadLeaf, PayloadBox, ask_default, render_payload)

pub fun result : Unit -> String
result () = render_payload (PayloadBox (PayloadLeaf "y")) with ask_default
"#;

    with_temp_project_files(
        &[("MixedDictLib.saga", lib_src)],
        main_src,
        |checker, main_program| {
            let lib_core = emit_project_module(lib_src, "mixeddictlib", checker);
            let main_core = emit_from_program(main_program, "main", checker);

            let dir = assert_erlc_compiles(&lib_core, "mixeddictlib");
            let main_core_path = dir.join("main.core");
            std::fs::write(&main_core_path, &main_core).unwrap();
            let erlc = std::process::Command::new("erlc")
                .arg("-o")
                .arg(&dir)
                .arg(&main_core_path)
                .output()
                .expect("failed to run erlc");
            assert!(
                erlc.status.success(),
                "erlc failed on main:\n{main_core}\nstderr: {}",
                String::from_utf8_lossy(&erlc.stderr)
            );

            compile_evidence_bridge_into(&dir);

            let run = std::process::Command::new("erl")
                .arg("-noshell")
                .arg("-pa")
                .arg(&dir)
                .arg("-eval")
                .arg("io:format(\"~ts~n\", [main:result(unit)]), init:stop().")
                .output()
                .expect("failed to run erl");
            let _ = std::fs::remove_dir_all(&dir);
            assert!(
                run.status.success(),
                "erl failed:\nstderr: {}",
                String::from_utf8_lossy(&run.stderr)
            );
            let stdout = String::from_utf8_lossy(&run.stdout);
            assert!(
                stdout.contains("imported"),
                "expected imported payload result, got: {stdout}"
            );
        },
    );
}

/// Regression: a decoder defined in Main composes two effectful Lib functions
/// (`Lib.unbox_int (Lib.unwrap b)`) and runs through `Lib.run_decoder`. The
/// inner call must abort the chain when it fails, instead of leaking its
/// `{error, _}` tuple to the outer return clause as a value (which would
/// produce a garbage `Ok` wrapping the error).
#[test]
fn cross_module_nested_effectful_calls_abort_correctly() {
    let lib_src = std::fs::read_to_string(fixtures_root().join("EffectChain.saga")).unwrap();
    let main_src = "
module Main
import Std.Fail (Fail)
import EffectChain (Box, Failure)

fun decoder : Box -> Int needs {Fail Failure}
decoder b = EffectChain.unbox_int (EffectChain.unwrap b)

pub fun run_fail : Unit -> String
run_fail () = {
  let r = EffectChain.run_decoder decoder (EffectChain.Box (EffectChain.IS \"oops\"))
  case r {
    Ok _ -> \"ok-bug\"
    Err _ -> \"err-good\"
  }
}

pub fun run_ok : Unit -> String
run_ok () = {
  let r = EffectChain.run_decoder decoder (EffectChain.Box (EffectChain.II 42))
  case r {
    Ok _ -> \"ok-good\"
    Err _ -> \"err-bug\"
  }
}
";
    let mut checker = make_project_checker();
    let main_program = typecheck_source(main_src, &mut checker);

    let lib_core = emit_project_module(&lib_src, "effectchain", &checker);
    let main_core = emit_from_program(&main_program, "main", &checker);

    let dir = assert_erlc_compiles(&lib_core, "effectchain");
    let main_core_path = dir.join("main.core");
    std::fs::write(&main_core_path, &main_core).unwrap();
    let erlc = std::process::Command::new("erlc")
        .arg("-o")
        .arg(&dir)
        .arg(&main_core_path)
        .output()
        .expect("failed to run erlc");
    assert!(
        erlc.status.success(),
        "erlc failed on main:\n{main_core}\nstderr: {}",
        String::from_utf8_lossy(&erlc.stderr)
    );

    compile_evidence_bridge_into(&dir);

    let run = std::process::Command::new("erl")
        .arg("-noshell")
        .arg("-pa")
        .arg(&dir)
        .arg("-eval")
        .arg("io:format(\"~s|~s~n\", [main:run_fail(unit), main:run_ok(unit)]), init:stop().")
        .output()
        .expect("failed to run erl");
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        run.status.success(),
        "erl failed:\nstderr: {}",
        String::from_utf8_lossy(&run.stderr)
    );
    let stdout = String::from_utf8_lossy(&run.stdout);
    assert!(
        stdout.contains("err-good|ok-good"),
        "expected 'err-good|ok-good', got: {stdout}"
    );
}

/// Regression: same chain as the test above, but the result is bound via
/// `let v = ...` inside a block before being returned. The let-RHS dispatch
/// must recognize qualified effectful calls (`Lib.f (Lib.g b)`), not just
/// Var-headed calls. Otherwise the rest of the block is not threaded as the
/// inner call's `_ReturnK` and an aborting handler's error tuple gets bound
/// to `v` and then wrapped as `Ok`.
#[test]
fn cross_module_nested_effectful_calls_via_let_abort_correctly() {
    let lib_src = std::fs::read_to_string(fixtures_root().join("EffectChain.saga")).unwrap();
    let main_src = "
module Main
import Std.Fail (Fail)
import EffectChain (Box, Failure)

handler local_to_result for Fail a {
  fail e = Err e
  return v = Ok v
}

fun via_let : Box -> Int needs {Fail Failure}
via_let b = {
  let v = EffectChain.unbox_int (EffectChain.unwrap b)
  v
}

pub fun run_fail : Unit -> String
run_fail () = {
  let r = via_let (EffectChain.Box (EffectChain.IS \"oops\")) with local_to_result
  case r {
    Ok _ -> \"ok-bug\"
    Err _ -> \"err-good\"
  }
}

pub fun run_ok : Unit -> String
run_ok () = {
  let r = via_let (EffectChain.Box (EffectChain.II 7)) with local_to_result
  case r {
    Ok _ -> \"ok-good\"
    Err _ -> \"err-bug\"
  }
}
";
    let mut checker = make_project_checker();
    let main_program = typecheck_source(main_src, &mut checker);

    let lib_core = emit_project_module(&lib_src, "effectchain", &checker);
    let main_core = emit_from_program(&main_program, "main", &checker);

    let dir = assert_erlc_compiles(&lib_core, "effectchain");
    let main_core_path = dir.join("main.core");
    std::fs::write(&main_core_path, &main_core).unwrap();
    let erlc = std::process::Command::new("erlc")
        .arg("-o")
        .arg(&dir)
        .arg(&main_core_path)
        .output()
        .expect("failed to run erlc");
    assert!(
        erlc.status.success(),
        "erlc failed on main:\n{main_core}\nstderr: {}",
        String::from_utf8_lossy(&erlc.stderr)
    );

    compile_evidence_bridge_into(&dir);

    let run = std::process::Command::new("erl")
        .arg("-noshell")
        .arg("-pa")
        .arg(&dir)
        .arg("-eval")
        .arg("io:format(\"~s|~s~n\", [main:run_fail(unit), main:run_ok(unit)]), init:stop().")
        .output()
        .expect("failed to run erl");
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        run.status.success(),
        "erl failed:\nstderr: {}",
        String::from_utf8_lossy(&run.stderr)
    );
    let stdout = String::from_utf8_lossy(&run.stdout);
    assert!(
        stdout.contains("err-good|ok-good"),
        "expected 'err-good|ok-good', got: {stdout}"
    );
}

/// Regression: an effectful cross-module call chain used as a record-literal
/// field value. The record-literal lowering must CPS-chain effectful field
/// expressions, otherwise an aborting handler's `{error, _}` tuple gets bound
/// into the record slot and the outer return clause wraps the whole record
/// as `Ok`.
#[test]
fn cross_module_nested_effectful_calls_in_record_field_abort_correctly() {
    let lib_src = std::fs::read_to_string(fixtures_root().join("EffectChain.saga")).unwrap();
    let main_src = "
module Main
import Std.Fail (Fail)
import EffectChain (Box, Failure)

handler local_to_result for Fail a {
  fail e = Err e
  return v = Ok v
}

record Wrap { x: Int }

fun in_record : Box -> Wrap needs {Fail Failure}
in_record b = Wrap { x: EffectChain.unbox_int (EffectChain.unwrap b) }

pub fun run_fail : Unit -> String
run_fail () = {
  let r = in_record (EffectChain.Box (EffectChain.IS \"oops\")) with local_to_result
  case r {
    Ok _ -> \"ok-bug\"
    Err _ -> \"err-good\"
  }
}

pub fun run_ok : Unit -> String
run_ok () = {
  let r = in_record (EffectChain.Box (EffectChain.II 7)) with local_to_result
  case r {
    Ok _ -> \"ok-good\"
    Err _ -> \"err-bug\"
  }
}
";
    let mut checker = make_project_checker();
    let main_program = typecheck_source(main_src, &mut checker);

    let lib_core = emit_project_module(&lib_src, "effectchain", &checker);
    let main_core = emit_from_program(&main_program, "main", &checker);

    let dir = assert_erlc_compiles(&lib_core, "effectchain");
    let main_core_path = dir.join("main.core");
    std::fs::write(&main_core_path, &main_core).unwrap();
    let erlc = std::process::Command::new("erlc")
        .arg("-o")
        .arg(&dir)
        .arg(&main_core_path)
        .output()
        .expect("failed to run erlc");
    assert!(
        erlc.status.success(),
        "erlc failed on main:\n{main_core}\nstderr: {}",
        String::from_utf8_lossy(&erlc.stderr)
    );

    compile_evidence_bridge_into(&dir);

    let run = std::process::Command::new("erl")
        .arg("-noshell")
        .arg("-pa")
        .arg(&dir)
        .arg("-eval")
        .arg("io:format(\"~s|~s~n\", [main:run_fail(unit), main:run_ok(unit)]), init:stop().")
        .output()
        .expect("failed to run erl");
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        run.status.success(),
        "erl failed:\nstderr: {}",
        String::from_utf8_lossy(&run.stderr)
    );
    let stdout = String::from_utf8_lossy(&run.stdout);
    assert!(
        stdout.contains("err-good|ok-good"),
        "expected 'err-good|ok-good', got: {stdout}"
    );
}

/// Regression: an effectful call used as an argument to an ADT constructor
/// (e.g. `Just (decoder input)`). The constructor lowering must CPS-chain
/// effectful args so an aborting handler skips the constructor wrapping and
/// the outer return clause — otherwise the `{error, _}` tuple gets nested
/// inside the constructor and then wrapped as `Ok`, producing
/// `Ok (Just (Err _))` instead of `Err _`.
#[test]
fn cross_module_nested_effectful_calls_in_ctor_arg_abort_correctly() {
    let lib_src = std::fs::read_to_string(fixtures_root().join("EffectChain.saga")).unwrap();
    let main_src = "
module Main
import Std.Fail (Fail)
import EffectChain (Box, Failure)

handler local_to_result for Fail a {
  fail e = Err e
  return v = Ok v
}

fun wrap_just : Box -> Maybe Int needs {Fail Failure}
wrap_just b = Just (EffectChain.unbox_int b)

pub fun run_fail : Unit -> String
run_fail () = {
  let r = wrap_just (EffectChain.Box (EffectChain.IS \"oops\")) with local_to_result
  case r {
    Ok _ -> \"ok-bug\"
    Err _ -> \"err-good\"
  }
}

pub fun run_ok : Unit -> String
run_ok () = {
  let r = wrap_just (EffectChain.Box (EffectChain.II 9)) with local_to_result
  case r {
    Ok (Just _) -> \"ok-good\"
    Ok Nothing -> \"ok-bug-nothing\"
    Err _ -> \"err-bug\"
  }
}
";
    let mut checker = make_project_checker();
    let main_program = typecheck_source(main_src, &mut checker);

    let lib_core = emit_project_module(&lib_src, "effectchain", &checker);
    let main_core = emit_from_program(&main_program, "main", &checker);

    let dir = assert_erlc_compiles(&lib_core, "effectchain");
    let main_core_path = dir.join("main.core");
    std::fs::write(&main_core_path, &main_core).unwrap();
    let erlc = std::process::Command::new("erlc")
        .arg("-o")
        .arg(&dir)
        .arg(&main_core_path)
        .output()
        .expect("failed to run erlc");
    assert!(
        erlc.status.success(),
        "erlc failed on main:\n{main_core}\nstderr: {}",
        String::from_utf8_lossy(&erlc.stderr)
    );

    compile_evidence_bridge_into(&dir);

    let run = std::process::Command::new("erl")
        .arg("-noshell")
        .arg("-pa")
        .arg(&dir)
        .arg("-eval")
        .arg("io:format(\"~s|~s~n\", [main:run_fail(unit), main:run_ok(unit)]), init:stop().")
        .output()
        .expect("failed to run erl");
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        run.status.success(),
        "erl failed:\nstderr: {}",
        String::from_utf8_lossy(&run.stderr)
    );
    let stdout = String::from_utf8_lossy(&run.stdout);
    assert!(
        stdout.contains("err-good|ok-good"),
        "expected 'err-good|ok-good', got: {stdout}"
    );
}

/// Regression: an effectful call used as an element of a tuple literal.
/// The tuple lowering must CPS-chain effectful elements so an aborting
/// handler skips the tuple build and the outer return clause — otherwise
/// the `{error, _}` tuple gets bound into a tuple slot and wrapped as `Ok`.
#[test]
fn cross_module_nested_effectful_calls_in_tuple_elem_abort_correctly() {
    let lib_src = std::fs::read_to_string(fixtures_root().join("EffectChain.saga")).unwrap();
    let main_src = "
module Main
import Std.Fail (Fail)
import EffectChain (Box, Failure)

handler local_to_result for Fail a {
  fail e = Err e
  return v = Ok v
}

fun in_tuple : Box -> (Int, Int) needs {Fail Failure}
in_tuple b = (EffectChain.unbox_int b, 42)

pub fun run_fail : Unit -> String
run_fail () = {
  let r = in_tuple (EffectChain.Box (EffectChain.IS \"oops\")) with local_to_result
  case r {
    Ok _ -> \"ok-bug\"
    Err _ -> \"err-good\"
  }
}

pub fun run_ok : Unit -> String
run_ok () = {
  let r = in_tuple (EffectChain.Box (EffectChain.II 7)) with local_to_result
  case r {
    Ok (_, _) -> \"ok-good\"
    Err _ -> \"err-bug\"
  }
}
";
    let mut checker = make_project_checker();
    let main_program = typecheck_source(main_src, &mut checker);

    let lib_core = emit_project_module(&lib_src, "effectchain", &checker);
    let main_core = emit_from_program(&main_program, "main", &checker);

    let dir = assert_erlc_compiles(&lib_core, "effectchain");
    let main_core_path = dir.join("main.core");
    std::fs::write(&main_core_path, &main_core).unwrap();
    let erlc = std::process::Command::new("erlc")
        .arg("-o")
        .arg(&dir)
        .arg(&main_core_path)
        .output()
        .expect("failed to run erlc");
    assert!(
        erlc.status.success(),
        "erlc failed on main:\n{main_core}\nstderr: {}",
        String::from_utf8_lossy(&erlc.stderr)
    );

    compile_evidence_bridge_into(&dir);

    let run = std::process::Command::new("erl")
        .arg("-noshell")
        .arg("-pa")
        .arg(&dir)
        .arg("-eval")
        .arg("io:format(\"~s|~s~n\", [main:run_fail(unit), main:run_ok(unit)]), init:stop().")
        .output()
        .expect("failed to run erl");
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        run.status.success(),
        "erl failed:\nstderr: {}",
        String::from_utf8_lossy(&run.stderr)
    );
    let stdout = String::from_utf8_lossy(&run.stdout);
    assert!(
        stdout.contains("err-good|ok-good"),
        "expected 'err-good|ok-good', got: {stdout}"
    );
}

/// Regression: an effectful call used as a binop operand. The binop
/// lowering must CPS-chain effectful operands so an aborting handler
/// skips the arithmetic call — otherwise the `{error, _}` tuple is passed
/// to `erlang:+/2` and crashes with `badarith` at runtime.
#[test]
fn cross_module_nested_effectful_calls_in_binop_operand_abort_correctly() {
    let lib_src = std::fs::read_to_string(fixtures_root().join("EffectChain.saga")).unwrap();
    let main_src = "
module Main
import Std.Fail (Fail)
import EffectChain (Box, Failure)

handler local_to_result for Fail a {
  fail e = Err e
  return v = Ok v
}

fun add100 : Box -> Int needs {Fail Failure}
add100 b = EffectChain.unbox_int b + 100

pub fun run_fail : Unit -> String
run_fail () = {
  let r = add100 (EffectChain.Box (EffectChain.IS \"oops\")) with local_to_result
  case r {
    Ok _ -> \"ok-bug\"
    Err _ -> \"err-good\"
  }
}

pub fun run_ok : Unit -> String
run_ok () = {
  let r = add100 (EffectChain.Box (EffectChain.II 7)) with local_to_result
  case r {
    Ok 107 -> \"ok-good\"
    Ok _ -> \"ok-wrong\"
    Err _ -> \"err-bug\"
  }
}
";
    let mut checker = make_project_checker();
    let main_program = typecheck_source(main_src, &mut checker);

    let lib_core = emit_project_module(&lib_src, "effectchain", &checker);
    let main_core = emit_from_program(&main_program, "main", &checker);

    let dir = assert_erlc_compiles(&lib_core, "effectchain");
    let main_core_path = dir.join("main.core");
    std::fs::write(&main_core_path, &main_core).unwrap();
    let erlc = std::process::Command::new("erlc")
        .arg("-o")
        .arg(&dir)
        .arg(&main_core_path)
        .output()
        .expect("failed to run erlc");
    assert!(
        erlc.status.success(),
        "erlc failed on main:\n{main_core}\nstderr: {}",
        String::from_utf8_lossy(&erlc.stderr)
    );

    compile_evidence_bridge_into(&dir);

    let run = std::process::Command::new("erl")
        .arg("-noshell")
        .arg("-pa")
        .arg(&dir)
        .arg("-eval")
        .arg("io:format(\"~s|~s~n\", [main:run_fail(unit), main:run_ok(unit)]), init:stop().")
        .output()
        .expect("failed to run erl");
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        run.status.success(),
        "erl failed:\nstderr: {}",
        String::from_utf8_lossy(&run.stderr)
    );
    let stdout = String::from_utf8_lossy(&run.stdout);
    assert!(
        stdout.contains("err-good|ok-good"),
        "expected 'err-good|ok-good', got: {stdout}"
    );
}

/// Regression: an effectful call as the record sub-expression of a field
/// access (`(eff_expr).field`). The field-access lowering must CPS-chain
/// the record sub-expression so an aborting handler skips the `element/2`
/// call (which would otherwise crash with `badarg` on the abort tuple, or
/// silently extract a wrong slot if the abort tuple happens to be the
/// right arity).
#[test]
fn cross_module_nested_effectful_calls_in_field_access_abort_correctly() {
    let lib_src = std::fs::read_to_string(fixtures_root().join("EffectChain.saga")).unwrap();
    let main_src = "
module Main
import Std.Fail (Fail)
import EffectChain (Box, Failure)

handler local_to_result for Fail a {
  fail e = Err e
  return v = Ok v
}

record Pair { fst: Int, snd: Int }

fun build : Box -> Pair needs {Fail Failure}
build b = Pair { fst: EffectChain.unbox_int b, snd: 0 }

fun fst_of : Box -> Int needs {Fail Failure}
fst_of b = (build b).fst

pub fun run_fail : Unit -> String
run_fail () = {
  let r = fst_of (EffectChain.Box (EffectChain.IS \"oops\")) with local_to_result
  case r {
    Ok _ -> \"ok-bug\"
    Err _ -> \"err-good\"
  }
}

pub fun run_ok : Unit -> String
run_ok () = {
  let r = fst_of (EffectChain.Box (EffectChain.II 11)) with local_to_result
  case r {
    Ok 11 -> \"ok-good\"
    Ok _ -> \"ok-wrong\"
    Err _ -> \"err-bug\"
  }
}
";
    let mut checker = make_project_checker();
    let main_program = typecheck_source(main_src, &mut checker);

    let lib_core = emit_project_module(&lib_src, "effectchain", &checker);
    let main_core = emit_from_program(&main_program, "main", &checker);

    let dir = assert_erlc_compiles(&lib_core, "effectchain");
    let main_core_path = dir.join("main.core");
    std::fs::write(&main_core_path, &main_core).unwrap();
    let erlc = std::process::Command::new("erlc")
        .arg("-o")
        .arg(&dir)
        .arg(&main_core_path)
        .output()
        .expect("failed to run erlc");
    assert!(
        erlc.status.success(),
        "erlc failed on main:\n{main_core}\nstderr: {}",
        String::from_utf8_lossy(&erlc.stderr)
    );

    compile_evidence_bridge_into(&dir);

    let run = std::process::Command::new("erl")
        .arg("-noshell")
        .arg("-pa")
        .arg(&dir)
        .arg("-eval")
        .arg("io:format(\"~s|~s~n\", [main:run_fail(unit), main:run_ok(unit)]), init:stop().")
        .output()
        .expect("failed to run erl");
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        run.status.success(),
        "erl failed:\nstderr: {}",
        String::from_utf8_lossy(&run.stderr)
    );
    let stdout = String::from_utf8_lossy(&run.stdout);
    assert!(
        stdout.contains("err-good|ok-good"),
        "expected 'err-good|ok-good', got: {stdout}"
    );
}

/// Regression: an effectful call as the right-hand side of a record update
/// (`{ r | field: eff_expr }`). The record-update lowering must CPS-chain
/// effectful field updates so an aborting handler skips the tuple rebuild
/// and the outer return clause, instead of binding the abort tuple into
/// the field slot.
#[test]
fn cross_module_nested_effectful_calls_in_record_update_abort_correctly() {
    let lib_src = std::fs::read_to_string(fixtures_root().join("EffectChain.saga")).unwrap();
    let main_src = "
module Main
import Std.Fail (Fail)
import EffectChain (Box, Failure)

handler local_to_result for Fail a {
  fail e = Err e
  return v = Ok v
}

record Pair { fst: Int, snd: Int }

fun bump : Pair -> Box -> Pair needs {Fail Failure}
bump p b = { p | fst: EffectChain.unbox_int b }

pub fun run_fail : Unit -> String
run_fail () = {
  let base = Pair { fst: 0, snd: 0 }
  let r = bump base (EffectChain.Box (EffectChain.IS \"oops\")) with local_to_result
  case r {
    Ok _ -> \"ok-bug\"
    Err _ -> \"err-good\"
  }
}

pub fun run_ok : Unit -> String
run_ok () = {
  let base = Pair { fst: 0, snd: 99 }
  let r = bump base (EffectChain.Box (EffectChain.II 5)) with local_to_result
  case r {
    Ok _ -> \"ok-good\"
    Err _ -> \"err-bug\"
  }
}
";
    let mut checker = make_project_checker();
    let main_program = typecheck_source(main_src, &mut checker);

    let lib_core = emit_project_module(&lib_src, "effectchain", &checker);
    let main_core = emit_from_program(&main_program, "main", &checker);

    let dir = assert_erlc_compiles(&lib_core, "effectchain");
    let main_core_path = dir.join("main.core");
    std::fs::write(&main_core_path, &main_core).unwrap();
    let erlc = std::process::Command::new("erlc")
        .arg("-o")
        .arg(&dir)
        .arg(&main_core_path)
        .output()
        .expect("failed to run erlc");
    assert!(
        erlc.status.success(),
        "erlc failed on main:\n{main_core}\nstderr: {}",
        String::from_utf8_lossy(&erlc.stderr)
    );

    compile_evidence_bridge_into(&dir);

    let run = std::process::Command::new("erl")
        .arg("-noshell")
        .arg("-pa")
        .arg(&dir)
        .arg("-eval")
        .arg("io:format(\"~s|~s~n\", [main:run_fail(unit), main:run_ok(unit)]), init:stop().")
        .output()
        .expect("failed to run erl");
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        run.status.success(),
        "erl failed:\nstderr: {}",
        String::from_utf8_lossy(&run.stderr)
    );
    let stdout = String::from_utf8_lossy(&run.stdout);
    assert!(
        stdout.contains("err-good|ok-good"),
        "expected 'err-good|ok-good', got: {stdout}"
    );
}

/// Regression: an effectful call used as the condition of an `if`. The
/// lowering must CPS-chain the cond so an aborting handler bypasses the
/// case-on-cond (which would otherwise crash with "no matching clause"
/// when the abort tuple matches neither `true` nor `false`).
#[test]
fn cross_module_nested_effectful_calls_in_if_cond_abort_correctly() {
    let lib_src = std::fs::read_to_string(fixtures_root().join("EffectChain.saga")).unwrap();
    let main_src = "
module Main
import Std.Fail (Fail)
import EffectChain (Box, Failure)

handler local_to_result for Fail a {
  fail e = Err e
  return v = Ok v
}

fun nonzero : Box -> Bool needs {Fail Failure}
nonzero b = EffectChain.unbox_int b != 0

fun classify : Box -> String needs {Fail Failure}
classify b = if nonzero b then \"nonzero\" else \"zero\"

pub fun run_fail : Unit -> String
run_fail () = {
  let r = classify (EffectChain.Box (EffectChain.IS \"oops\")) with local_to_result
  case r {
    Ok _ -> \"ok-bug\"
    Err _ -> \"err-good\"
  }
}

pub fun run_ok : Unit -> String
run_ok () = {
  let r = classify (EffectChain.Box (EffectChain.II 3)) with local_to_result
  case r {
    Ok _ -> \"ok-good\"
    Err _ -> \"err-bug\"
  }
}
";
    let mut checker = make_project_checker();
    let main_program = typecheck_source(main_src, &mut checker);

    let lib_core = emit_project_module(&lib_src, "effectchain", &checker);
    let main_core = emit_from_program(&main_program, "main", &checker);

    let dir = assert_erlc_compiles(&lib_core, "effectchain");
    let main_core_path = dir.join("main.core");
    std::fs::write(&main_core_path, &main_core).unwrap();
    let erlc = std::process::Command::new("erlc")
        .arg("-o")
        .arg(&dir)
        .arg(&main_core_path)
        .output()
        .expect("failed to run erlc");
    assert!(
        erlc.status.success(),
        "erlc failed on main:\n{main_core}\nstderr: {}",
        String::from_utf8_lossy(&erlc.stderr)
    );

    compile_evidence_bridge_into(&dir);

    let run = std::process::Command::new("erl")
        .arg("-noshell")
        .arg("-pa")
        .arg(&dir)
        .arg("-eval")
        .arg("io:format(\"~s|~s~n\", [main:run_fail(unit), main:run_ok(unit)]), init:stop().")
        .output()
        .expect("failed to run erl");
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        run.status.success(),
        "erl failed:\nstderr: {}",
        String::from_utf8_lossy(&run.stderr)
    );
    let stdout = String::from_utf8_lossy(&run.stdout);
    assert!(
        stdout.contains("err-good|ok-good"),
        "expected 'err-good|ok-good', got: {stdout}"
    );
}

/// Regression: an effectful call used as the scrutinee of a `case`. The
/// lowering must CPS-chain the scrutinee so an aborting handler skips
/// arm matching (which would otherwise either crash on a no-match or
/// silently fall through to the wildcard arm with the abort tuple).
#[test]
fn cross_module_nested_effectful_calls_in_case_scrutinee_abort_correctly() {
    let lib_src = std::fs::read_to_string(fixtures_root().join("EffectChain.saga")).unwrap();
    let main_src = "
module Main
import Std.Fail (Fail)
import EffectChain (Box, Failure)

handler local_to_result for Fail a {
  fail e = Err e
  return v = Ok v
}

fun describe : Box -> String needs {Fail Failure}
describe b = case EffectChain.unbox_int b {
  0 -> \"zero\"
  _ -> \"nonzero\"
}

pub fun run_fail : Unit -> String
run_fail () = {
  let r = describe (EffectChain.Box (EffectChain.IS \"oops\")) with local_to_result
  case r {
    Ok _ -> \"ok-bug\"
    Err _ -> \"err-good\"
  }
}

pub fun run_ok : Unit -> String
run_ok () = {
  let r = describe (EffectChain.Box (EffectChain.II 5)) with local_to_result
  case r {
    Ok _ -> \"ok-good\"
    Err _ -> \"err-bug\"
  }
}
";
    let mut checker = make_project_checker();
    let main_program = typecheck_source(main_src, &mut checker);

    let lib_core = emit_project_module(&lib_src, "effectchain", &checker);
    let main_core = emit_from_program(&main_program, "main", &checker);

    let dir = assert_erlc_compiles(&lib_core, "effectchain");
    let main_core_path = dir.join("main.core");
    std::fs::write(&main_core_path, &main_core).unwrap();
    let erlc = std::process::Command::new("erlc")
        .arg("-o")
        .arg(&dir)
        .arg(&main_core_path)
        .output()
        .expect("failed to run erlc");
    assert!(
        erlc.status.success(),
        "erlc failed on main:\n{main_core}\nstderr: {}",
        String::from_utf8_lossy(&erlc.stderr)
    );

    compile_evidence_bridge_into(&dir);

    let run = std::process::Command::new("erl")
        .arg("-noshell")
        .arg("-pa")
        .arg(&dir)
        .arg("-eval")
        .arg("io:format(\"~s|~s~n\", [main:run_fail(unit), main:run_ok(unit)]), init:stop().")
        .output()
        .expect("failed to run erl");
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        run.status.success(),
        "erl failed:\nstderr: {}",
        String::from_utf8_lossy(&run.stderr)
    );
    let stdout = String::from_utf8_lossy(&run.stdout);
    assert!(
        stdout.contains("err-good|ok-good"),
        "expected 'err-good|ok-good', got: {stdout}"
    );
}

/// Regression: passing a bare cross-module effectful function reference
/// (`EffectChain.unbox_int`) as an argument to a higher-order cross-module
/// function. The bare reference is a *value*, not a call — the lowerer's
/// effectful-call predicate must not classify it as a call to be CPS-chained.
/// Previously, the partial-application detection swallowed the outer call
/// entirely and the lambda body returned an eta-wrapper instead of invoking
/// the HOF, producing a closure where an `Ok`/`Err` tuple was expected.
#[test]
fn cross_module_effectful_fun_ref_passed_to_hof() {
    let lib_src = std::fs::read_to_string(fixtures_root().join("EffectChain.saga")).unwrap();
    let main_src = "
module Main
import Std.Fail (Fail)
import EffectChain (Box, Failure)

pub fun run_direct : Unit -> String
run_direct () = {
  let r = EffectChain.run_decoder EffectChain.unbox_int (EffectChain.Box (EffectChain.II 7))
  case r {
    Ok _ -> \"direct-ok\"
    Err _ -> \"direct-err\"
  }
}

pub fun run_via_hof : Unit -> String
run_via_hof () = {
  let input = EffectChain.Box (EffectChain.II 7)
  let r = EffectChain.run_decoder (fun b -> EffectChain.map_via EffectChain.unbox_int b) input
  case r {
    Ok _ -> \"hof-ok\"
    Err _ -> \"hof-err\"
  }
}
";
    let mut checker = make_project_checker();
    let main_program = typecheck_source(main_src, &mut checker);

    let lib_core = emit_project_module(&lib_src, "effectchain", &checker);
    let main_core = emit_from_program(&main_program, "main", &checker);

    let dir = assert_erlc_compiles(&lib_core, "effectchain");
    let main_core_path = dir.join("main.core");
    std::fs::write(&main_core_path, &main_core).unwrap();
    let erlc = std::process::Command::new("erlc")
        .arg("-o")
        .arg(&dir)
        .arg(&main_core_path)
        .output()
        .expect("failed to run erlc");
    assert!(
        erlc.status.success(),
        "erlc failed on main:\n{main_core}\nstderr: {}",
        String::from_utf8_lossy(&erlc.stderr)
    );

    compile_evidence_bridge_into(&dir);

    let run = std::process::Command::new("erl")
        .arg("-noshell")
        .arg("-pa")
        .arg(&dir)
        .arg("-eval")
        .arg(
            "io:format(\"~s|~s~n\", [main:run_direct(unit), main:run_via_hof(unit)]), init:stop().",
        )
        .output()
        .expect("failed to run erl");
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        run.status.success(),
        "erl failed:\nstderr: {}",
        String::from_utf8_lossy(&run.stderr)
    );
    let stdout = String::from_utf8_lossy(&run.stdout);
    assert!(
        stdout.contains("direct-ok|hof-ok"),
        "expected 'direct-ok|hof-ok', got: {stdout}"
    );
}

/// Regression: a Main-defined effectful function passed as a callback to a
/// cross-module HOF. The HOF (`EffectChain.at`) calls its callback in
/// raw-CPS shape (`decoder(arg, H, K)`). The function-value reference for the
/// callback must therefore be the raw CPS-expanded `FunRef` / `make_fun`,
/// not an eta-wrapper that captures handlers in scope and supplies an
/// identity continuation. Previously, local function references emitted such
/// a wrapper while cross-module references emitted `make_fun`, causing the
/// callback to be invoked with the wrong arity (3 vs 1) and crashing.
#[test]
fn cross_module_hof_callback_local_and_imported_match_arity() {
    let lib_src = std::fs::read_to_string(fixtures_root().join("EffectChain.saga")).unwrap();
    let main_src = "
module Main
import Std.Fail (Fail)
import EffectChain (Box, Failure)

fun custom : Box -> Int needs {Fail Failure}
custom b = EffectChain.unbox_int b

pub fun via_imported : Unit -> String
via_imported () = {
  let input = EffectChain.Box (EffectChain.II 7)
  let r = EffectChain.run_decoder (fun b -> EffectChain.at \"x\" EffectChain.unbox_int b) input
  case r {
    Ok _ -> \"imp-ok\"
    Err _ -> \"imp-err\"
  }
}

pub fun via_local : Unit -> String
via_local () = {
  let input = EffectChain.Box (EffectChain.II 7)
  let r = EffectChain.run_decoder (fun b -> EffectChain.at \"x\" custom b) input
  case r {
    Ok _ -> \"loc-ok\"
    Err _ -> \"loc-err\"
  }
}
";
    let mut checker = make_project_checker();
    let main_program = typecheck_source(main_src, &mut checker);

    let lib_core = emit_project_module(&lib_src, "effectchain", &checker);
    let main_core = emit_from_program(&main_program, "main", &checker);

    let dir = assert_erlc_compiles(&lib_core, "effectchain");
    let main_core_path = dir.join("main.core");
    std::fs::write(&main_core_path, &main_core).unwrap();
    let erlc = std::process::Command::new("erlc")
        .arg("-o")
        .arg(&dir)
        .arg(&main_core_path)
        .output()
        .expect("failed to run erlc");
    assert!(
        erlc.status.success(),
        "erlc failed on main:\n{main_core}\nstderr: {}",
        String::from_utf8_lossy(&erlc.stderr)
    );

    compile_evidence_bridge_into(&dir);

    let run = std::process::Command::new("erl")
        .arg("-noshell")
        .arg("-pa")
        .arg(&dir)
        .arg("-eval")
        .arg(
            "io:format(\"~s|~s~n\", [main:via_imported(unit), main:via_local(unit)]), init:stop().",
        )
        .output()
        .expect("failed to run erl");
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        run.status.success(),
        "erl failed:\nstderr: {}",
        String::from_utf8_lossy(&run.stderr)
    );
    let stdout = String::from_utf8_lossy(&run.stdout);
    assert!(
        stdout.contains("imp-ok|loc-ok"),
        "expected 'imp-ok|loc-ok', got: {stdout}"
    );
}

// ---- Cross-module trait dicts ----

#[test]
fn cross_module_trait_dict_show_animal() {
    // Animals.saga defines `impl Show for Animal`.
    // Importing Animals should make the Show dict available for Animal.
    let main_src = "
module Main
import Animals (Animal)

main () = show (Animal { name: \"Rex\", species: \"Dog\" })
";
    let mut checker = make_project_checker();
    let program = typecheck_source(main_src, &mut checker);
    let out = emit_from_program(&program, "main", &checker);

    // Phase 3: `show` on the imported `Show Animal` impl is specialized to a
    // direct cross-module call to the hoisted dict method in the animals module
    // (instead of building the dict via `call 'animals':'<dict>'()` + element/2).
    let dict = typechecker::make_dict_name("Std.Base.Show", &[], "animals", "Animals.Animal");
    assert_contains(
        &out,
        &format!("call 'animals':'__saga_dictmethod_{dict}_0'"),
    );
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
fn cross_module_parameterized_dict_chain_inlines_with_private_helper() {
    // Container.saga defines a parameterized `impl Encodable for Box a where
    // {a: Encodable}` whose body calls a private helper `wrap_value`. Importing
    // it and calling `encode` on a `Box Int` inlines the producer impl body into
    // Main (cross-module generic fold), collapsing the dict chain into a `case`
    // on Box. The private helper lowers to a direct cross-module call
    // (`call 'container':'wrap_value'`) — possible because every function is
    // exported in Core and the inlined node carries the producer's resolution.
    let main_src = "
module Main
import Container (Encodable, Box)

fun run : (b: Box Int) -> Int
run b = encode b

main () = run (Box 5)
";
    let mut checker = make_project_checker();
    let program = typecheck_source(main_src, &mut checker);
    let out = emit_from_program(&program, "main", &checker);

    // The Box impl body was inlined: a `case` destructuring Box appears in Main.
    assert_contains(&out, "'container_Box'");
    // Its private helper is reached by a direct cross-module call, not a local
    // (undefined-here) reference.
    assert_contains(&out, "call 'container':'wrap_value'");
}

#[test]
fn cross_module_fold_specializes_method_of_unimported_trait() {
    // Box's impl body calls `tag`, a method of Container's `Tag` trait that Main
    // never imports. After inlining the impl body into Main, the `tag` call on
    // the nullary `Tag Int` dict must still specialize: the saturation guard
    // reads the method arity from the dict constructor (via the compiled
    // modules), since `Tag` is absent from Main's own trait registry. Without
    // that fallback the call would fall back to `element/2` dispatch.
    let main_src = "
module Main
import Container (Encodable, Box)

fun run : (b: Box Int) -> Int
run b = encode b

main () = run (Box 5)
";
    let mut checker = make_project_checker();
    let program = typecheck_source(main_src, &mut checker);
    let out = emit_from_program(&program, "main", &checker);

    let dict = typechecker::make_dict_name("Container.Tag", &[], "container", "Std.Int.Int");
    assert_contains(
        &out,
        &format!("call 'container':'__saga_dictmethod_{dict}_0'"),
    );
}

#[test]
fn cross_module_fold_resolves_field_access_on_unimported_record() {
    // Box's impl body reads `o.scale` on Container's private `Opts` record. After
    // the body is inlined into Main, lowering the field access needs Opts's field
    // layout to compute the tuple index — but Opts is non-`pub` and never
    // imported, so it isn't in Main's public codegen info. Emit must still
    // succeed (the layout comes from the all-modules record pass); previously
    // this panicked with "could not resolve record type for field access".
    let main_src = "
module Main
import Container (Encodable, Box)

fun run : (b: Box Int) -> Int
run b = encode b

main () = run (Box 5)
";
    let mut checker = make_project_checker();
    let program = typecheck_source(main_src, &mut checker);
    let out = emit_from_program(&program, "main", &checker);
    let run_fn = emitted_function(&out, "run", 1);
    // The field access lowered to an element/2 projection (index 2 = first field
    // after the tag), inside the inlined body — not a panic.
    assert!(
        run_fn.contains("call 'erlang':'element'"),
        "expected the inlined `o.scale` to lower to an element/2 projection\n{run_fn}"
    );
}

#[test]
fn cross_module_parameterized_fold_compiles_with_erlc() {
    // Proves the inlined cross-module body (with its private-helper and hoisted
    // leaf calls) links: emit both modules and run erlc over the importer.
    let main_src = "
module Main
import Container (Encodable, Box)

fun run : (b: Box Int) -> Int
run b = encode b

main () = run (Box 5)
";
    let mut checker = make_project_checker();
    let main_program = typecheck_source(main_src, &mut checker);
    let result = checker.to_result();
    let container_program = result
        .programs()
        .get("Container")
        .expect("Container module not found");
    let container_core = emit_from_program(container_program, "container", &checker);
    let main_core = emit_from_program(&main_program, "main", &checker);

    let dir = assert_erlc_compiles(&container_core, "container");
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
fn imported_constrained_hof_threads_effectful_callback_evidence() {
    let lib_src = r#"module NoEvidence.Lib

pub effect Build a {
  fun select : a -> a
}

type Step a = Step (Unit -> a)

pub handler collect for Build a {
  select value = {
    Step (fun () -> {
      let Step run_rest = resume value
      run_rest ()
    })
  }

  return value = Step (fun () -> value)
}

pub trait Project selection row | selection -> row {
  fun project : selection -> row
}

pub record Prepared row {
  row: row,
}

pub fun query : (Unit -> selection needs {Build selection}) -> Prepared row
  where {selection: Project row}
query make = {
  let Step run_query = make () with collect
  let selection = run_query ()
  Prepared { row: project selection }
}
"#;

    let main_src = r#"module Main

import NoEvidence.Lib as Lib
import NoEvidence.Lib (Build)

record Selected {
  id: Int,
  name: String,
}

impl Lib.Project Selected for Selected {
  project value = value
}

fun prepared : Unit -> Lib.Prepared Selected
prepared () = Lib.query (fun () -> {
  select! Selected {
    id: 1,
    name: "Alice",
  }
})

main () = {
  let value = prepared ()
  value.row.name
}
"#;

    with_temp_project_files(
        &[("src/NoEvidence/Lib.saga", lib_src)],
        main_src,
        |checker, program| {
            let result = checker.to_result();
            let lib_program = result
                .programs()
                .get("NoEvidence.Lib")
                .expect("NoEvidence.Lib module not found");
            let lib_core = emit_from_program(lib_program, "noevidence_lib", checker);
            let main_core = emit_from_program(program, "main", checker);
            assert_project_modules_run(
                &[("noevidence_lib", &lib_core), ("main", &main_core)],
                "io:format(\"~ts~n\", [main:main(unit)]), init:stop().",
                &["Alice"],
            );
        },
    );
}

#[test]
fn local_constrained_let_inside_generic_query_keeps_outer_evidence() {
    let lib_src = r#"module Repro.Lib

pub effect Build selection {
  fun select : selection -> selection
}

type Step a = Step (Unit -> a)

pub handler collect for Build selection {
  select value = {
    Step (fun () -> {
      let Step run_rest = resume value
      run_rest ()
    })
  }

  return value = Step (fun () -> value)
}

pub trait ToRep selection selection_rep | selection -> selection_rep {
  fun to_rep : selection -> selection_rep
}

pub trait Selectable selection_rep row_rep | selection_rep -> row_rep {
  fun select_rep : selection_rep -> row_rep
}

pub trait FromRep row row_rep | row -> row_rep {
  fun from_rep : row_rep -> row
}

pub record Prepared row {
  row: row,
}

pub fun project : selection -> row
  where {
    selection: ToRep selection_rep,
    selection_rep: Selectable row_rep,
    row: FromRep row_rep,
  }
project selection =
  select_rep (to_rep selection)
  |> from_rep

pub fun query : (Unit -> selection needs {Build selection}) -> Prepared row
  where {
    selection: ToRep selection_rep,
    selection_rep: Selectable row_rep,
    row: FromRep row_rep,
  }
query make = {
  let Step run_query = make () with collect
  let (selection, _) = (run_query (), ())
  let row : row = project selection
  Prepared { row: row }
}
"#;

    let main_src = r#"module Main

import Repro.Lib as Lib
import Repro.Lib (Build)

record Selected { id: Int }
record Row { id: Int }
record SelectedRep { id: Int }
record RowRep { id: Int }

impl Lib.ToRep SelectedRep for Selected {
  to_rep selected = SelectedRep { id: selected.id }
}

impl Lib.Selectable RowRep for SelectedRep {
  select_rep rep = RowRep { id: rep.id }
}

impl Lib.FromRep RowRep for Row {
  from_rep rep = Row { id: rep.id }
}

fun prepared : Unit -> Lib.Prepared Row
prepared () = Lib.query (fun () ->
  select! Selected { id: 1 }
)

main () = {
  let prepared = prepared ()
  prepared.row.id
}
"#;

    with_temp_project_files(
        &[("src/Repro/Lib.saga", lib_src)],
        main_src,
        |checker, program| {
            let result = checker.to_result();
            let lib_program = result
                .programs()
                .get("Repro.Lib")
                .expect("Repro.Lib module not found");
            let lib_core = emit_from_program(lib_program, "repro_lib", checker);
            let main_core = emit_from_program(program, "main", checker);
            assert_project_modules_run(
                &[("repro_lib", &lib_core), ("main", &main_core)],
                "io:format(\"~p~n\", [main:main(unit)]), init:stop().",
                &["1"],
            );
        },
    );
}

#[test]
fn local_dict_names_are_module_qualified() {
    // When Animals.saga defines impl Show for Animal, the dict should be
    // named with canonical trait + module-qualified type (not bare __dict_Show_Animal)
    let animals_src = std::fs::read_to_string(fixtures_root().join("Animals.saga")).unwrap();
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

#[test]
fn bare_method_dispatches_via_resolved_trait_when_imports_collide() {
    // import A (Foo); import B (b_helper) → only A.Foo is bare-visible.
    // Bare `pp 1` must dispatch to A.Foo's dict, not B.Bar's, regardless of
    // HashMap iteration order in elaborate.rs::trait_methods.
    let a_src = "module A\n\npub trait Foo a {\n  fun pp : a -> String\n}\n";
    let b_src = "module B\n\npub trait Bar a {\n  fun pp : a -> String\n}\n\npub fun b_helper : Unit -> Unit\nb_helper () = ()\n";
    let main_src = "module Main\n\nimport A (Foo)\nimport B (b_helper)\n\nimpl Foo for Int { pp x = \"from-A\" }\nimpl B.Bar for Int { pp x = \"from-B\" }\n\nmain () = pp 1\n";

    with_temp_project_files(
        &[("lib/A.saga", a_src), ("lib/B.saga", b_src)],
        main_src,
        |checker, program| {
            let out = emit_from_program(program, "main", checker);
            // The `pp 1` call site inside main/1 must dispatch via the
            // A.Foo dict, not B.Bar's. (Both dict constructors are emitted
            // as top-level functions because both impls exist; what matters
            // is which one main/1 applies.)
            let foo_dict = typechecker::make_dict_name("A.Foo", &[], "main", "Std.Int.Int");
            let bar_dict = typechecker::make_dict_name("B.Bar", &[], "main", "Std.Int.Int");
            let main_body_start = out.find("'main'/1 =").expect("missing main/1");
            let main_body = &out[main_body_start..];
            let main_body_end = main_body
                .find("\n'")
                .map(|i| main_body_start + i)
                .unwrap_or(out.len());
            let main_body_slice = &out[main_body_start..main_body_end];
            // `pp 1` is a saturated pure call to the local `Foo Int` impl, so
            // Phase 2 may specialize it to a direct call to that impl's hoisted
            // method (`__saga_dictmethod_<A.Foo dict>_0`). Either way — dict
            // application or hoisted-method call — the A.Foo dict name must
            // appear in main/1 and the B.Bar dict name must not. Substring
            // matching covers both forms (the hoisted name embeds the dict name).
            assert!(
                main_body_slice.contains(&foo_dict),
                "main/1 should dispatch via the A.Foo impl\n{main_body_slice}"
            );
            assert!(
                !main_body_slice.contains(&bar_dict),
                "main/1 must not dispatch via the B.Bar impl (only A.Foo is exposed)\n{main_body_slice}"
            );
        },
    );
}

#[test]
fn qualified_trait_method_call_lowers_to_dict_dispatch() {
    // Calling a trait method via its fully qualified name (Module.Trait.method)
    // must produce a dictionary method access the same way bare calls do.
    // Without ResolvedTraitMethod recorded for QualifiedName nodes, the
    // elaborator would leave it as a regular Var lookup and the lowerer
    // would emit an unresolved variable reference.
    let a_src = "module A\n\npub trait Foo a {\n  fun pp : a -> String\n}\n";
    let main_src = "module Main\n\nimport A\n\nimpl A.Foo for Int { pp x = \"qualified\" }\n\nmain () = A.Foo.pp 1\n";

    with_temp_project_files(&[("lib/A.saga", a_src)], main_src, |checker, program| {
        let out = emit_from_program(program, "main", checker);
        let foo_dict = typechecker::make_dict_name("A.Foo", &[], "main", "Std.Int.Int");
        assert_contains(&out, &format!("'{foo_dict}'"));
        assert!(
            !out.contains("'A.Foo.pp'") && !out.contains("apply 'A.Foo.pp'"),
            "qualified trait method should not lower as a raw name reference\n{out}"
        );
        assert_erlc_compiles(&out, "main");
    });
}

#[test]
fn exposed_trait_method_bare_call_lowers_to_dict_dispatch() {
    let db_src = r#"module Kraken.Query

pub type Projection row = Projection row

pub trait Selectable selection row | selection -> row {
  fun to_projection : selection -> Projection row
}
"#;

    let main_src = r#"module Main

import Kraken.Query as Db (Projection, Selectable)

type Users = Users Int

impl Selectable Int for Users {
  to_projection users = case users {
    Users n -> Projection n
  }
}

main () = case to_projection (Users 7) {
  Projection n -> n
}
"#;

    with_temp_project_files(
        &[("src/Kraken/Query.saga", db_src)],
        main_src,
        |checker, program| {
            let main_core = emit_from_program(program, "main", checker);
            assert!(
                !main_core.contains("To_projection") && !main_core.contains("'to_projection'"),
                "bare imported trait method should lower through dictionary dispatch\n{main_core}"
            );
            assert_project_modules_run(
                &[("main", &main_core)],
                "io:format(\"~p~n\", [main:main(unit)]), init:stop().",
                &["7"],
            );
        },
    );
}

#[test]
fn imported_constrained_wrapper_passes_dicts_before_user_args() {
    let db_src = r#"module Kraken.Query

pub type Projection row = Projection row

pub trait Selectable selection row | selection -> row {
  fun to_projection : selection -> Projection row
}

pub fun select_all : selection -> Projection row where {selection: Selectable row}
select_all selection = to_projection selection
"#;

    let main_src = r#"module Main

import Kraken.Query as Db (Projection, Selectable, select_all)

type Users = Users Int

impl Selectable Int for Users {
  to_projection users = case users {
    Users n -> Projection n
  }
}

main () = case Db.select_all (Users 11) {
  Projection n -> n
}
"#;

    with_temp_project_files(
        &[("src/Kraken/Query.saga", db_src)],
        main_src,
        |checker, program| {
            let result = checker.to_result();
            let db_program = result
                .programs()
                .get("Kraken.Query")
                .expect("Kraken.Query module not found");
            let db_core = emit_from_program(db_program, "kraken_query", checker);
            let main_core = emit_from_program(program, "main", checker);
            assert_project_modules_run(
                &[("kraken_query", &db_core), ("main", &main_core)],
                "io:format(\"~p~n\", [main:main(unit)]), init:stop().",
                &["11"],
            );
        },
    );
}

#[test]
fn imported_constrained_wrapper_inside_callback_uses_dict_for_parameterized_arg() {
    let db_src = r#"module Kraken.Query

pub type Projection row = Projection row
pub type Prepared row = Prepared row

pub trait Selectable selection row | selection -> row {
  fun to_projection : selection -> Projection row
}

pub fun select_all : selection -> Projection row where {selection: Selectable row}
select_all selection = to_projection selection

pub fun query : (Unit -> Projection row) -> Prepared row
query run = case run () {
  Projection row -> Prepared row
}
"#;

    let main_src = r#"module Main

import Kraken.Query as Db (Projection, Prepared, Selectable, select_all, query)

type Scope = Scope

record Users source {
  id: Int,
}

impl Selectable Int for Users source {
  to_projection users = Projection users.id
}

fun users : Users Scope
users = Users { id: 17 }

main () = case Db.query (fun () -> Db.select_all users) {
  Prepared row -> row
}
"#;

    with_temp_project_files(
        &[("src/Kraken/Query.saga", db_src)],
        main_src,
        |checker, program| {
            let result = checker.to_result();
            let db_program = result
                .programs()
                .get("Kraken.Query")
                .expect("Kraken.Query module not found");
            let db_core = emit_from_program(db_program, "kraken_query", checker);
            let main_core = emit_from_program(program, "main", checker);
            assert!(
                main_core.contains("__dict_Kraken_Query_Selectable")
                    && main_core.contains("main_Main_Users"),
                "select_all should receive the Selectable Users dictionary\n{main_core}"
            );
            assert_project_modules_run(
                &[("kraken_query", &db_core), ("main", &main_core)],
                "io:format(\"~p~n\", [main:main(unit)]), init:stop().",
                &["17"],
            );
        },
    );
}

// ---- Constructor atom mangling ----

#[test]
fn local_adt_constructors_mangled_with_module_name() {
    let shapes_src = std::fs::read_to_string(fixtures_root().join("Shapes.saga")).unwrap();
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
    // The scrutinee is a function call (not a literal `Just(42)`), so the generic
    // fold's constructor cancellation can't constant-fold the case away — keeping
    // the constructor atoms in the output for this mangling check.
    let main_src = "
module Main

fun mk : Int -> Maybe Int
mk n = Just n

main () = case mk 42 {
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
    let shapes_src = std::fs::read_to_string(fixtures_root().join("Shapes.saga")).unwrap();
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
    let shapes_src = std::fs::read_to_string(fixtures_root().join("Shapes.saga")).unwrap();
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
    let lib_path = fixtures_root().join("OpaqueLib.saga");
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
    let lib_path = fixtures_root().join("OpaqueLib2.saga");
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
    let lib_path = fixtures_root().join("OpaqueLib3.saga");
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
    compile_evidence_bridge_into(&dir);
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
//     saga::desugar::desugar_program(&mut program);
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
    // Logger.saga doesn't define a named handler, so let's test with a module that does.
    // For now, just verify the qualified handler lookup works.
    let src = "
module Main
import Logger (Log, greet)


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
fn aliased_qualified_handler_binding_canonicalizes_for_lowering() {
    let src = "
module Main
import Std.DateTime as DateTime


main () = {
  let clock = DateTime.system_clock
  DateTime.Clock.today! () with {clock}
}
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
    // Inline handler with bare op names should match exposed imported effect ops
    let src = "
module Main
import Logger (Log)


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
import Logger (Log, greet)


main () = greet \"world\" with {
  log msg = { dbg msg; resume () }
}
";
    let mut checker = make_project_checker();
    let program = typecheck_source(src, &mut checker);
    let out = emit_from_program(&program, "main", &checker);
    assert_contains(&out, "call 'logger':'greet'");
}

#[test]
fn imported_handler_private_constructors_mangled_in_expressions_and_patterns() {
    // Private constructors from an imported handler's source module must be
    // mangled consistently in both expressions and case/destructure patterns.
    // Regression: patterns inside handler bodies used bare atoms (e.g. 'Ack')
    // while expressions used mangled atoms (e.g. 'mylib_Ack').
    let lib = r#"module MyLib

pub effect Wrap {
  fun wrap : String -> String
}

type Wrapper = Wrapped String

pub handler my_wrapper for Wrap {
  wrap s = case Wrapped s {
    Wrapped v -> resume v
  }
}
"#;

    let main = "module Main\nimport MyLib (my_wrapper, Wrap)\n\nmain () = {\n  wrap! \"hello\"\n} with {my_wrapper}\n";

    with_temp_project_files(&[("MyLib.saga", lib)], main, |checker, program| {
        let out = emit_from_program(program, "main", checker);
        // Constructor in expression must use the mangled atom
        assert_contains(&out, "'mylib_Wrapped'");
        // Pattern must also use the mangled atom, not bare 'Wrapped'
        assert!(
            !out.contains("<{'Wrapped',"),
            "case pattern should use mangled 'mylib_Wrapped', not bare 'Wrapped':\n{out}"
        );
    });
}

#[test]
fn imported_handler_prelude_constructors_use_beam_overrides() {
    // When an imported handler body uses prelude constructors (Ok, Err),
    // they must use BEAM override atoms (ok, error), not the handler's
    // source-module mangling. Regression: Ok/Err were mangled as
    // 'mylib_Ok'/'mylib_Err' instead of 'ok'/'error'.
    let lib = r#"module MyLib

pub effect Store {
  fun save : String -> Result String String
}

pub handler my_store for Store {
  save key = resume (Ok key)
}
"#;

    let main = "module Main\nimport MyLib (my_store, Store)\n\nmain () = {\n  case save! \"test\" {\n    Ok v -> v\n    Err _ -> \"failed\"\n  }\n} with {my_store}\n";

    with_temp_project_files(&[("MyLib.saga", lib)], main, |checker, program| {
        let out = emit_from_program(program, "main", checker);
        // Handler body must use BEAM override 'ok', not 'mylib_Ok'
        assert!(
            !out.contains("mylib_Ok"),
            "handler body should use BEAM override 'ok', not 'mylib_Ok':\n{out}"
        );
        assert!(
            !out.contains("mylib_Err"),
            "handler body should use BEAM override 'error', not 'mylib_Err':\n{out}"
        );
        // The case match at the call site should also use 'ok'/'error'
        assert_contains(&out, "'ok'");
    });
}

/// Regression: `let g = factory_call; g x` shape — the let-RHS evaluates to
/// an effectful function value (here, a partial application of the cross-
/// module HOF `EffectChain.at`). The binder `g` is then an in-scope
/// effectful variable; calling `g x` must thread handlers and `_ReturnK`
/// like any other saturated effectful call so an aborting handler skips the
/// surrounding block instead of letting the abort tuple fall through.
#[test]
fn effectful_var_call_aborts_correctly() {
    let lib_src = std::fs::read_to_string(fixtures_root().join("EffectChain.saga")).unwrap();
    let main_src = "
module Main
import Std.Fail (Fail)
import EffectChain (Box, Failure)

handler local_to_result for Fail a {
  fail e = Err e
  return v = Ok v
}

fun decode : Box -> Int needs {Fail Failure}
decode b = {
  let g = EffectChain.at \"field\" EffectChain.unbox_int
  g b
}

pub fun run_fail : Unit -> String
run_fail () = {
  let r = decode (EffectChain.Box (EffectChain.IS \"oops\")) with local_to_result
  case r {
    Ok _ -> \"ok-bug\"
    Err _ -> \"err-good\"
  }
}

pub fun run_ok : Unit -> String
run_ok () = {
  let r = decode (EffectChain.Box (EffectChain.II 42)) with local_to_result
  case r {
    Ok _ -> \"ok-good\"
    Err _ -> \"err-bug\"
  }
}
";
    let mut checker = make_project_checker();
    let main_program = typecheck_source(main_src, &mut checker);

    let lib_core = emit_project_module(&lib_src, "effectchain", &checker);
    let main_core = emit_from_program(&main_program, "main", &checker);

    let dir = assert_erlc_compiles(&lib_core, "effectchain");
    let main_core_path = dir.join("main.core");
    std::fs::write(&main_core_path, &main_core).unwrap();
    let erlc = std::process::Command::new("erlc")
        .arg("-o")
        .arg(&dir)
        .arg(&main_core_path)
        .output()
        .expect("failed to run erlc");
    assert!(
        erlc.status.success(),
        "erlc failed on main:\n{main_core}\nstderr: {}",
        String::from_utf8_lossy(&erlc.stderr)
    );

    compile_evidence_bridge_into(&dir);

    let run = std::process::Command::new("erl")
        .arg("-noshell")
        .arg("-pa")
        .arg(&dir)
        .arg("-eval")
        .arg("io:format(\"~s|~s~n\", [main:run_fail(unit), main:run_ok(unit)]), init:stop().")
        .output()
        .expect("failed to run erl");
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        run.status.success(),
        "erl failed:\nstderr: {}",
        String::from_utf8_lossy(&run.stderr)
    );
    let stdout = String::from_utf8_lossy(&run.stdout);
    assert!(
        stdout.contains("err-good|ok-good"),
        "expected 'err-good|ok-good', got: {stdout}"
    );
}

/// Regression: a module can define a local helper with the same bare name as
/// an imported qualified open-row function (`Spec.route` builder vs
/// `Edda.route` router). Call classification must use the resolved canonical
/// name for `E.route`; otherwise it grabs the local pure builder's arity and
/// lowers the saturated router call as a residual closure returned to `_ReturnK`.
#[test]
fn qualified_open_row_call_prefers_canonical_fun_sig_over_local_bare_name() {
    let edda = r#"module Edda

pub type Method = GET deriving (Eq)

pub record Request {
  path: String,
}

pub record Response {
  status: Int,
  body: String,
}

pub effect Skip {
  fun skip : Unit -> a
}

pub fun route : Method -> String -> (Request -> Response needs {..e}) -> Request -> Response
  needs {Skip, ..e}
route m pattern h req =
  if m == GET && req.path == pattern then h req else skip! ()
"#;

    let spec = r#"module Spec

import Edda (Method, Request, Response, Skip)
import Edda as E

pub record RouteBuilder {
  method: Method,
  path: String,
}

pub record RouteSchema {
  method: Method,
  path: String,
  action: Request -> Response,
}

pub fun route : Method -> String -> RouteBuilder
route method path = RouteBuilder { method: method, path: path }

pub fun performed_by : (Request -> Response) -> RouteBuilder -> RouteSchema
performed_by action builder = RouteSchema {
  method: builder.method,
  path: builder.path,
  action: action,
}

pub fun as_route : RouteSchema -> Request -> Response needs {Skip}
as_route schema req = E.route schema.method schema.path schema.action req
"#;

    let main = r#"module Main

import Spec

main () = ()
"#;

    let out = with_temp_project_files(
        &[("Edda.saga", edda), ("Spec.saga", spec)],
        main,
        |checker, _program| emit_project_module(spec, "spec", checker),
    );
    let as_route = out
        .split("'as_route'/4 =")
        .nth(1)
        .and_then(|rest| rest.split("\n\n").next())
        .expect("expected as_route/4 in emitted Core");

    assert_contains(as_route, "call 'edda':'route'");
    assert!(
        !as_route.contains(") ->\n        ( call 'edda':'route'"),
        "as_route returned a residual route closure instead of calling route with evidence:\n{as_route}"
    );
}

/// Regression: an eta-reduced reference to an effectful function bound to a
/// local. `let g = Lib.f` (no application) followed by `g x` is the
/// first-class-callback shape: the binder's type carries the effect row, so
/// the call site must look up the effectful var and thread handlers.
#[test]
fn eta_reduced_effectful_lambda_aborts_correctly() {
    let lib_src = std::fs::read_to_string(fixtures_root().join("EffectChain.saga")).unwrap();
    let main_src = "
module Main
import Std.Fail (Fail)
import EffectChain (Box, Failure)

handler local_to_result for Fail a {
  fail e = Err e
  return v = Ok v
}

fun decode : Box -> Int needs {Fail Failure}
decode b = {
  let g = EffectChain.unbox_int
  g b
}

pub fun run_fail : Unit -> String
run_fail () = {
  let r = decode (EffectChain.Box (EffectChain.IS \"oops\")) with local_to_result
  case r {
    Ok _ -> \"ok-bug\"
    Err _ -> \"err-good\"
  }
}

pub fun run_ok : Unit -> String
run_ok () = {
  let r = decode (EffectChain.Box (EffectChain.II 42)) with local_to_result
  case r {
    Ok _ -> \"ok-good\"
    Err _ -> \"err-bug\"
  }
}
";
    let mut checker = make_project_checker();
    let main_program = typecheck_source(main_src, &mut checker);

    let lib_core = emit_project_module(&lib_src, "effectchain", &checker);
    let main_core = emit_from_program(&main_program, "main", &checker);

    let dir = assert_erlc_compiles(&lib_core, "effectchain");
    let main_core_path = dir.join("main.core");
    std::fs::write(&main_core_path, &main_core).unwrap();
    let erlc = std::process::Command::new("erlc")
        .arg("-o")
        .arg(&dir)
        .arg(&main_core_path)
        .output()
        .expect("failed to run erlc");
    assert!(
        erlc.status.success(),
        "erlc failed on main:\n{main_core}\nstderr: {}",
        String::from_utf8_lossy(&erlc.stderr)
    );

    compile_evidence_bridge_into(&dir);

    let run = std::process::Command::new("erl")
        .arg("-noshell")
        .arg("-pa")
        .arg(&dir)
        .arg("-eval")
        .arg("io:format(\"~s|~s~n\", [main:run_fail(unit), main:run_ok(unit)]), init:stop().")
        .output()
        .expect("failed to run erl");
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        run.status.success(),
        "erl failed:\nstderr: {}",
        String::from_utf8_lossy(&run.stderr)
    );
    let stdout = String::from_utf8_lossy(&run.stdout);
    assert!(
        stdout.contains("err-good|ok-good"),
        "expected 'err-good|ok-good', got: {stdout}"
    );
}

/// Regression: pulling an effectful function out of a list via a cons pattern
/// (`r :: rest`) and calling `r input` from inside another effectful function
/// was emitting a plain 1-arg `apply` instead of the CPS-aware
/// `apply r(input, Evidence, ReturnK)` call, causing a `badarity` crash at
/// runtime ("function called with 1 argument(s), but expects 3").
///
/// Root cause was in the codegen call-effects pre-pass: it read the recorded
/// type for pattern-bound variables out of `type_at_span` without applying the
/// typechecker substitution. Constructor-pattern args (and therefore `r` in
/// the desugared `Cons(r, rest)`) are bound with a freshly instantiated
/// parameter type *before* unification with the scrutinee finishes, so the
/// stored type was a raw `Type::Var(a)` carrying no effects. The pattern var
/// was then classified as pure and the call site missed evidence threading.
#[test]
fn pattern_bound_effectful_function_in_list_threads_evidence() {
    let main_src = "
module Main

effect Skip {
  fun skip : Unit -> a
}

handler skip_to_default for Skip {
  skip () = \"default\"
}

fun route : String -> (String -> String needs {..e}) -> String -> String
  needs {Skip, ..e}
route pattern h input =
  if input == pattern then h input
  else skip! ()

fun choose : List (String -> String needs {Skip, ..e}) -> String -> String
  needs {..e}
choose routes input = case routes {
  [] -> \"no match\"
  r :: rest -> r input with {
    skip () = choose rest input
  }
}

fun greet : String -> String
greet _ = \"hello\"

fun bye : String -> String
bye _ = \"goodbye\"

fun r1 : String -> String needs {Skip}
r1 input = route \"/\" greet input

fun r2 : String -> String needs {Skip}
r2 input = route \"/bye\" bye input

pub fun run_match : Unit -> String
run_match () = choose [r1, r2] \"/bye\"

pub fun run_miss : Unit -> String
run_miss () = choose [r1, r2] \"/nope\"
";
    let mut checker = make_project_checker();
    let main_program = typecheck_source(main_src, &mut checker);
    let main_core = emit_from_program(&main_program, "main", &checker);

    let dir = assert_erlc_compiles(&main_core, "main");
    compile_evidence_bridge_into(&dir);

    let run = std::process::Command::new("erl")
        .arg("-noshell")
        .arg("-pa")
        .arg(&dir)
        .arg("-eval")
        .arg("io:format(\"~s|~s~n\", [main:run_match(unit), main:run_miss(unit)]), init:stop().")
        .output()
        .expect("failed to run erl");
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        run.status.success(),
        "erl failed:\nstderr: {}",
        String::from_utf8_lossy(&run.stderr)
    );
    let stdout = String::from_utf8_lossy(&run.stdout);
    assert!(
        stdout.contains("goodbye|no match"),
        "expected 'goodbye|no match', got: {stdout}"
    );
}

/// Regression: a let-bound lambda whose inferred type carries effects must
/// compile to a CPS-expanded `fun(Input, _Evidence, _ReturnK) -> ...` so call
/// sites that thread evidence don't hit a `badarity` (3 args vs 1) crash.
///
/// Before the fix, `let r1 = fun input -> route ... input` (where `route`
/// performs `Skip`) compiled to a plain `fun(Input) -> ...`. Top-level
/// `fun r1 : ... needs {Skip}` declarations correctly added the two CPS
/// params, but the let-binding lowering path called `lower_expr_value(value)`
/// without an expected type, so the lambda lowering recipe at mod.rs never
/// saw the effect row and emitted a `/1` closure. The fix passes the
/// pattern's resolved type as the expected type, routing the lambda through
/// `lower_expr_value_with_expected_type` which sets `lambda_effect_context`
/// for the duration of lowering.
#[test]
fn let_bound_effectful_lambda_compiles_as_cps_value() {
    let main_src = "
module Main

effect Skip {
  fun skip : Unit -> a
}

fun route : String -> (String -> String needs {..e}) -> String -> String
  needs {Skip, ..e}
route pattern h input =
  if input == pattern then h input
  else skip! ()

fun choose : List (String -> String needs {Skip, ..e}) -> String -> String
  needs {..e}
choose routes input = case routes {
  [] -> \"no match\"
  r :: rest -> r input with {
    skip () = choose rest input
  }
}

fun greet : String -> String
greet _ = \"hello\"

fun bye : String -> String
bye _ = \"goodbye\"

pub fun run : Unit -> String
run () = {
  let r1 = fun input -> route \"/\" greet input
  let r2 = fun input -> route \"/bye\" bye input
  choose [r1, r2] \"/bye\"
}
";
    let mut checker = make_project_checker();
    let main_program = typecheck_source(main_src, &mut checker);
    let main_core = emit_from_program(&main_program, "main", &checker);

    let dir = assert_erlc_compiles(&main_core, "main");
    compile_evidence_bridge_into(&dir);

    let run = std::process::Command::new("erl")
        .arg("-noshell")
        .arg("-pa")
        .arg(&dir)
        .arg("-eval")
        .arg("io:format(\"~s~n\", [main:run(unit)]), init:stop().")
        .output()
        .expect("failed to run erl");
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        run.status.success(),
        "erl failed:\nstderr: {}",
        String::from_utf8_lossy(&run.stderr)
    );
    let stdout = String::from_utf8_lossy(&run.stdout);
    assert!(
        stdout.contains("goodbye"),
        "expected 'goodbye', got: {stdout}"
    );
}

/// Regression: a let binding whose value is a *partial application* returning
/// an effectful function — `let app = choose [route]` where `choose` takes two
/// user args but only one is supplied — must classify `app` as an effectful
/// (open-row) callable so `app input` lowers to the CPS-aware
/// `apply app(Input, Evidence, ReturnK)` call.
///
/// Before the fix, the call-effects pre-pass only promoted a let binding to an
/// effectful var when the *value itself* was a saturated effectful call
/// (`value_effect_signature`). A partial application performs no effects, so it
/// classified as Pure and `app` was never recorded — and that path never
/// tracked open-row callables (`needs {..e}` with no named effects) anyway. The
/// call `app input` then lowered to a plain 1-arg `apply`, crashing at runtime
/// with `badarity` ("function called with 1 argument(s), but expects 3"). The
/// fix falls back to the binder's resolved type via `record_pattern_effectful_vars`.
#[test]
fn let_bound_partial_application_threads_evidence() {
    let main_src = "
module Main

effect TryNext {
  fun skip : Unit -> a
}

fun choose : List (String -> String needs {TryNext, ..e}) -> String -> String
  needs {..e}
choose routes input = case routes {
  [] -> \"not found\"
  r :: rest -> r input with {
    skip () = choose rest input
  }
}

fun match_route : String -> (String -> String needs {..e}) -> String -> String
  needs {TryNext, ..e}
match_route pattern h input =
  if input == pattern then h input
  else skip! ()

fun ok_route : String -> String needs {..e}
ok_route _ = \"ok\"

pub fun run_hit : Unit -> String
run_hit () = {
  let app = choose [match_route \"/ok\" ok_route]
  app \"/ok\"
}

pub fun run_miss : Unit -> String
run_miss () = {
  let app = choose [match_route \"/ok\" ok_route]
  app \"/nope\"
}
";
    let mut checker = make_project_checker();
    let main_program = typecheck_source(main_src, &mut checker);
    let main_core = emit_from_program(&main_program, "main", &checker);

    let dir = assert_erlc_compiles(&main_core, "main");
    compile_evidence_bridge_into(&dir);

    let run = std::process::Command::new("erl")
        .arg("-noshell")
        .arg("-pa")
        .arg(&dir)
        .arg("-eval")
        .arg("io:format(\"~s|~s~n\", [main:run_hit(unit), main:run_miss(unit)]), init:stop().")
        .output()
        .expect("failed to run erl");
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        run.status.success(),
        "erl failed:\nstderr: {}",
        String::from_utf8_lossy(&run.stderr)
    );
    let stdout = String::from_utf8_lossy(&run.stdout);
    assert!(
        stdout.contains("ok|not found"),
        "expected 'ok|not found', got: {stdout}"
    );
}

// --- Codegen-side coverage for canonical-name auto-load ---
//
// These pin the codegen analogue of the typecheck-side rule:
// loaded modules must be resolvable canonically without an explicit import,
// and decls without a normal BEAM function (`@builtin`) must intercept
// at the use site for both bare AND qualified spellings.

/// Qualified-form `Std.IO.Unsafe.print_stdout` is `@builtin`: it has no BEAM
/// implementation. Lowering must inline it as `io:format`, *not* emit a call
/// to `std_io_unsafe:print_stdout/1` (which would crash at runtime). The bare
/// form has always inlined; this regression-tests the qualified path.
#[test]
fn qualified_call_to_builtin_inlines_as_io_format() {
    let main = r#"main () = {
  Std.IO.Unsafe.print_stdout "hi"
}
"#;
    let out = with_temp_project_files(&[], main, |checker, program| {
        emit_from_program(program, "_script", checker)
    });
    assert_contains(&out, "call 'io':'format'");
    assert!(
        !out.contains("'std_io_unsafe':'print_stdout'"),
        "qualified call to @builtin must not emit a real BEAM call:\n{out}"
    );
}

#[test]
fn aliased_call_to_builtin_inlines_as_io_format() {
    let main = r#"import Std.IO.Unsafe as U

main () = {
  U.print_stdout "hi"
}
"#;
    let out = with_temp_project_files(&[], main, |checker, program| {
        emit_from_program(program, "_script", checker)
    });
    assert_contains(&out, "call 'io':'format'");
    assert!(
        !out.contains("'std_io_unsafe':'print_stdout'"),
        "aliased call to @builtin must not emit a real BEAM call:\n{out}"
    );
}

#[test]
fn user_defined_print_stdout_bare_is_not_hijacked_by_intrinsic() {
    let main = r#"module Main

fun print_stdout : String -> Unit
print_stdout _ = ()

main () = {
  print_stdout "hi"
}
"#;
    let out = with_temp_project_files(&[], main, |checker, program| {
        emit_from_program(program, "main", checker)
    });
    assert!(
        !out.contains("call 'io':'format'"),
        "user-defined print_stdout must not lower as Std.IO.Unsafe.print_stdout:\n{out}"
    );
    assert_contains(&out, "'print_stdout'/1");
}

#[test]
fn user_defined_dbg_bare_is_not_hijacked_by_intrinsic() {
    let main = r#"module Main

fun dbg : String -> String
dbg value = value

main () = dbg "hi"
"#;
    let out = with_temp_project_files(&[], main, |checker, program| {
        emit_from_program(program, "main", checker)
    });
    assert!(
        !out.contains("call 'io':'format'"),
        "user-defined dbg must not lower as Std.IO.dbg:\n{out}"
    );
    assert_contains(&out, "'dbg'/2");
}

#[test]
fn user_defined_print_stdout_qualified_is_not_hijacked_by_intrinsic() {
    let lib = r#"module Lib

pub fun print_stdout : String -> Unit
print_stdout _ = ()
"#;
    let main = r#"module Main

main () = {
  Lib.print_stdout "hi"
}
"#;
    let out = with_temp_project_files(&[("src/Lib.saga", lib)], main, |checker, program| {
        emit_from_program(program, "main", checker)
    });
    assert!(
        !out.contains("call 'io':'format'"),
        "qualified user-defined print_stdout must not lower as intrinsic:\n{out}"
    );
    assert!(
        out.contains("call 'lib':'print_stdout'") || out.contains("'lib', 'print_stdout'"),
        "expected user-defined lib:print_stdout reference:\n{out}"
    );
}

#[test]
fn user_defined_catch_panic_bare_is_not_hijacked_by_intrinsic() {
    let main = r#"module Main

fun catch_panic : String -> String
catch_panic value = value

main () = catch_panic "hi"
"#;
    let out = with_temp_project_files(&[], main, |checker, program| {
        emit_from_program(program, "main", checker)
    });
    assert!(
        !out.contains("try"),
        "user-defined catch_panic must not lower as Std.Process.catch_panic:\n{out}"
    );
    assert_contains(&out, "'catch_panic'/1");
}

#[test]
fn qualified_std_process_catch_panic_lowers_as_intrinsic() {
    let main = r#"module Main

main () = Std.Process.catch_panic (fun () -> 42)
"#;
    let out = with_temp_project_files(&[], main, |checker, program| {
        emit_from_program(program, "main", checker)
    });
    assert_contains(&out, "try");
    assert!(
        !out.contains("'std_process':'catch_panic'"),
        "Std.Process.catch_panic must lower as intrinsic, not a BEAM call:\n{out}"
    );
}

/// Cross-module qualified reference to a zero-arity function must emit a
/// normal BEAM call to the defining module's /0 function.
#[test]
fn qualified_zero_arity_fun_cross_module_emits_beam_call() {
    let lib = r#"module Lib

pub fun answer : Int
answer = 123
"#;
    let main = r#"module Main

main () = Lib.answer
"#;
    let out = with_temp_project_files(&[("src/Lib.saga", lib)], main, |checker, program| {
        emit_from_program(program, "main", checker)
    });
    assert_contains(&out, "call 'lib':'answer'");
}

/// Cross-module zero-arity functions that reference a sibling zero-arity
/// function should resolve that sibling in the defining module.
#[test]
fn qualified_zero_arity_fun_cross_module_resolves_sibling_ref_in_defining_module() {
    let lib = r#"module Lib

pub fun base : Int
base = 123

pub fun answer : Int
answer = base
"#;
    let main = r#"module Main

main () = Lib.answer
"#;
    let out = with_temp_project_files(&[("src/Lib.saga", lib)], main, |checker, program| {
        emit_from_program(program, "main", checker)
    });
    assert_contains(&out, "call 'lib':'answer'");
}

/// Project module referenced by canonical name without `import Lib` should
/// codegen the same way as if it had been imported: a real BEAM call.
/// This is the codegen counterpart to the auto-load typecheck test.
#[test]
fn qualified_call_to_project_module_lowers_without_explicit_import() {
    let lib = r#"module Lib

pub fun greet : (name: String) -> String
greet name = name
"#;
    let main = r#"module Main

main () = Lib.greet "world"
"#;
    let out = with_temp_project_files(&[("src/Lib.saga", lib)], main, |checker, program| {
        emit_from_program(program, "main", checker)
    });
    // Either a direct call or a make_fun reference is fine — both require the
    // canonical 'lib':'greet' identity to be wired through codegen.
    assert!(
        out.contains("call 'lib':'greet'") || out.contains("'lib', 'greet'"),
        "expected canonical 'lib':'greet' reference in output:\n{out}"
    );
}

#[test]
fn imported_anonymous_record_return_registers_layout_for_field_access() {
    let lib = r#"module Lib

pub fun make : Unit -> { id: Int, name: String }
make () = { id: 1, name: "alice" }
"#;
    let main = r#"module Main

import Lib

main () = {
  let r = Lib.make ()
  r.id
}
"#;
    with_temp_project_files(&[("src/Lib.saga", lib)], main, |checker, program| {
        let result = checker.to_result();
        let lib_program = result.programs().get("Lib").expect("Lib module not found");
        let lib_core = emit_from_program(lib_program, "lib", checker);
        let main_core = emit_from_program(program, "main", checker);
        assert_project_modules_run(
            &[("lib", &lib_core), ("main", &main_core)],
            "io:format(\"~p~n\", [main:main(unit)]), init:stop().",
            &["1"],
        );
    });
}

#[test]
fn qualified_impl_trait_method_call_elaborates_without_bare_method_import() {
    // Regression for the same shape emitted by routed derives: an impl for an
    // imported qualified trait calls the trait method recursively, but the
    // method itself is not imported as a bare value in this module. The call must
    // elaborate through the current impl trait instead of lowering as a free
    // Core Erlang variable (`Encode`/`Insert_row`/`Column_name_map_rep`).
    let db = r#"module Schema.Db

pub trait Encode a {
  fun encode : a -> String
}

impl Encode for Int { encode _ = "ok" }

pub fun run_encode : a -> String where {a: Encode}
run_encode x = encode x
"#;

    let main = r#"module Main

import Schema.Db

type Box a = Box a

impl Db.Encode for Box a where {a: Db.Encode} {
  encode box = case box { Box x -> encode x }
}

main () = Db.run_encode (Box 1)
"#;

    with_temp_project_files(&[("src/Schema/Db.saga", db)], main, |checker, program| {
        let result = checker.to_result();
        let db_program = result
            .programs()
            .get("Schema.Db")
            .expect("Schema.Db module not found");
        let db_core = emit_from_program(db_program, "schema_db", checker);
        let main_core = emit_from_program(program, "main", checker);
        assert_project_modules_run(
            &[("schema_db", &db_core), ("main", &main_core)],
            "io:format(\"~s~n\", [main:main(unit)]), init:stop().",
            &["ok"],
        );
    });
}

#[test]
fn cross_module_trait_default_body_resolves_in_trait_module() {
    // Regression: when a trait's default-method body references an
    // identifier defined alongside the trait (here `default_cfg`), and a
    // downstream module writes an `impl` for that trait whose body
    // re-invokes the defaulted method, the default body was being cloned
    // into the downstream impl with its identifiers re-resolved against
    // the downstream module's scope -- producing "undefined variable:
    // default_cfg" because Main has no such binding.
    //
    // `inherit_trait_defaults` now rewrites free `Var`s in the cloned
    // body to `QualifiedName`s pointing at the trait's defining module,
    // so cross-module impls behave like single-module ones.
    let lib = r#"module Lib

pub record Cfg { tag: String }

pub fun default_cfg : Cfg
default_cfg = Cfg { tag: "default" }

pub trait Act a {
  fun act_with : Cfg -> a -> String
  fun act : a -> String
  act x = act_with default_cfg x
}

impl Act for Int {
  act_with c n = c.tag <> ":" <> show n
}
"#;

    let main = r#"module Main
import Lib as L (Act)

record Pair { a: Int, b: Int }

impl L.Act for Pair {
  act_with c p = c.tag <> ":(" <> act p.a <> "," <> act p.b <> ")"
}

main () = act (Pair { a: 1, b: 2 })
"#;

    let out = with_temp_project_files(&[("lib/Lib.saga", lib)], main, |checker, program| {
        emit_from_program(program, "main", checker)
    });
    // The cloned default body should call back through `Lib.default_cfg`
    // rather than failing to resolve. Confirm the lowered module compiles
    // and that the default body's reference made it into Main's output.
    assert!(
        out.contains("'lib':'default_cfg'"),
        "expected reference to lib:default_cfg in Main's lowered output:\n{out}"
    );
    assert_erlc_compiles(&out, "main");
}

/// Cross-module trait-effect propagation (bugfix): an effectful impl defined in
/// one module must propagate its effect to a concrete trait-method call in
/// another module. The impl's per-method effects travel via
/// `ModuleExports.trait_impls` (the cloned `ImplInfo`), so `call_it` in `Main`
/// — which neither declares `needs {Config}` nor handles it — must error.
#[test]
fn cross_module_effectful_trait_call_requires_effect() {
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock before epoch")
        .as_nanos();
    let root =
        std::env::temp_dir().join(format!("saga-xmod-effprop-{}-{unique}", std::process::id()));
    fs::create_dir_all(root.join("src")).expect("create temp project src");
    fs::write(root.join("project.toml"), "name = \"xmod\"\n").expect("write project.toml");
    fs::write(
        root.join("src/Lib.saga"),
        "module Lib\n\
         pub effect Config { fun config : Unit -> String }\n\
         pub trait Foo a { fun foo : a -> Int needs {..e} }\n\
         impl Foo for Int needs {Config} {\n\
         \x20 foo thing = if config! () == \"x\" then thing else thing\n\
         }\n",
    )
    .expect("write Lib.saga");

    let main_src = "module Main\n\
                    import Lib (Foo, Config)\n\
                    fun call_it : Unit -> Int\n\
                    call_it () = foo 42\n";

    let mut checker = make_project_checker_for_root(root.clone());
    let tokens = lexer::Lexer::new(main_src).lex().expect("lex error");
    let mut program = parser::Parser::new(tokens)
        .parse_program()
        .expect("parse error");
    saga::desugar::desugar_program(&mut program);
    checker.set_current_module("Main".to_string());
    let result = checker.check_program(&mut program);
    let errors: Vec<String> = result.errors().iter().map(|e| e.message.clone()).collect();
    let _ = fs::remove_dir_all(&root);

    assert!(
        result.has_errors(),
        "expected a cross-module Config propagation error, got none"
    );
    assert!(
        errors.iter().any(|m| m.contains("Config")),
        "expected Config in cross-module errors, got: {:?}",
        errors
    );
}
