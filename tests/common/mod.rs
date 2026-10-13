//! Shared BEAM-execution harness for integration tests.
//!
//! Compiles Saga sources to Core Erlang, builds the stdlib once per test
//! process, and runs the result with `erl -noshell`. Used by
//! `effect_property_tests.rs` and `function_shape_matrix.rs` via `mod common;`.
//!
//! The `check_*` helpers panic on any failure, which is what an ordinary
//! `#[test]` wants. The `try_*` helpers return a `Result` instead, for callers
//! that run many programs and must survive one of them failing.
//!
//! These helpers require `erlc` and `erl` on PATH.
#![allow(dead_code)]

use saga::{codegen, elaborate, lexer, parser, typechecker};
use std::collections::BTreeSet;
use std::path::PathBuf;
use std::process::Stdio;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Mutex, OnceLock};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

// ---------------------------------------------------------------------------
// Bounded subprocesses
// ---------------------------------------------------------------------------

/// Wall-clock limit for the `erlc`/`erl` calls made by the panicking helpers.
/// Generous: it only exists so a stuck child cannot hang the test run.
pub const SUBPROCESS_LIMIT: Duration = Duration::from_secs(120);

/// Process groups of children that are currently running, so a watchdog can
/// kill them all.
static LIVE_GROUPS: Mutex<BTreeSet<u32>> = Mutex::new(BTreeSet::new());

/// Kill a child's whole process group. `erl` and `erlc` are launchers; the
/// `beam.smp` they start must go too.
fn kill_group(pid: u32) {
    let _ = std::process::Command::new("kill")
        .arg("-KILL")
        .arg(format!("-{pid}"))
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status();
}

/// Kill every child started through `run_bounded*` that is still running.
pub fn kill_live_children() {
    let groups: Vec<u32> = LIVE_GROUPS.lock().unwrap().iter().copied().collect();
    for pid in groups {
        kill_group(pid);
    }
}

pub struct BoundedOutput {
    /// `None` when the child was killed at the limit.
    pub status: Option<std::process::ExitStatus>,
    /// Whatever the child wrote before it exited or was killed.
    pub stdout: String,
    pub stderr: String,
    pub timed_out: bool,
}

/// Run `cmd` in its own process group with a wall-clock limit, calling
/// `on_stdout_line` for each line as it arrives. On expiry the whole group
/// is killed and the output so far is returned with `timed_out` set.
pub fn run_bounded_streaming(
    cmd: &mut std::process::Command,
    limit: Duration,
    on_stdout_line: &(dyn Fn(&str) + Sync),
) -> std::io::Result<BoundedOutput> {
    use std::io::{BufRead, Read};
    use std::os::unix::process::CommandExt;

    let mut child = cmd
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .process_group(0)
        .spawn()?;
    let pid = child.id();
    LIVE_GROUPS.lock().unwrap().insert(pid);
    let child_stdout = child.stdout.take().expect("piped stdout");
    let mut child_stderr = child.stderr.take().expect("piped stderr");
    let deadline = Instant::now() + limit;

    let (status, stdout, stderr, timed_out) = std::thread::scope(|scope| {
        // Drain both pipes on their own threads so a chatty child cannot
        // block on a full pipe while we poll.
        let out = scope.spawn(move || {
            // Keep the bytes exactly as written; lines are only for the
            // callback.
            let mut reader = std::io::BufReader::new(child_stdout);
            let mut bytes = Vec::new();
            loop {
                let start = bytes.len();
                match reader.read_until(b'\n', &mut bytes) {
                    Ok(0) | Err(_) => break,
                    Ok(_) => {
                        let line = String::from_utf8_lossy(&bytes[start..]);
                        on_stdout_line(line.trim_end_matches(['\n', '\r']));
                    }
                }
            }
            String::from_utf8_lossy(&bytes).into_owned()
        });
        let err = scope.spawn(move || {
            let mut bytes = Vec::new();
            let _ = child_stderr.read_to_end(&mut bytes);
            String::from_utf8_lossy(&bytes).into_owned()
        });
        let mut timed_out = false;
        let status = loop {
            match child.try_wait() {
                Ok(Some(status)) => break Some(status),
                Ok(None) if Instant::now() >= deadline => {
                    timed_out = true;
                    kill_group(pid);
                    let _ = child.kill();
                    let _ = child.wait();
                    break None;
                }
                Ok(None) => std::thread::sleep(Duration::from_millis(5)),
                Err(_) => {
                    kill_group(pid);
                    let _ = child.kill();
                    let _ = child.wait();
                    break None;
                }
            }
        };
        // A grandchild holding the pipes open would block the readers, so
        // make sure the group is gone before joining them.
        kill_group(pid);
        (
            status,
            out.join().unwrap_or_default(),
            err.join().unwrap_or_default(),
            timed_out,
        )
    });
    LIVE_GROUPS.lock().unwrap().remove(&pid);
    Ok(BoundedOutput {
        status,
        stdout,
        stderr,
        timed_out,
    })
}

/// `Command::output` with a wall-clock limit. A child that is still running
/// at the limit is killed with its process group and reported as `Err`.
pub fn run_bounded(
    cmd: &mut std::process::Command,
    limit: Duration,
) -> Result<std::process::Output, String> {
    let program = cmd.get_program().to_string_lossy().into_owned();
    let out = run_bounded_streaming(cmd, limit, &|_| {})
        .map_err(|e| format!("could not start `{program}`: {e}"))?;
    match out.status {
        Some(status) if !out.timed_out => Ok(std::process::Output {
            status,
            stdout: out.stdout.into_bytes(),
            stderr: out.stderr.into_bytes(),
        }),
        _ => Err(format!(
            "`{program}` did not finish within {}s and was killed",
            limit.as_secs()
        )),
    }
}

pub static COUNTER: AtomicUsize = AtomicUsize::new(0);

pub fn fresh_dir(fixture: &str) -> PathBuf {
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

pub fn fixtures_root_for_main_only() -> PathBuf {
    // For single-file fixtures, we still need a project root for the checker;
    // a fresh empty dir suffices since there are no other modules to scan.
    let dir = fresh_dir("root");
    // Drop a project.toml so project mode is recognized.
    std::fs::write(dir.join("project.toml"), "[project]\nname=\"prop\"\n").unwrap();
    dir
}

/// (Source path on disk, output module name as referenced in Core Erlang.)
/// Mirrors the bridge file mapping in `src/cli/build.rs`.
pub fn bridge_files() -> Vec<(&'static str, &'static str)> {
    vec![
        (
            "File.bridge.erl",
            include_str!("../../src/stdlib/File.bridge.erl"),
        ),
        (
            "Dict.bridge.erl",
            include_str!("../../src/stdlib/Dict.bridge.erl"),
        ),
        (
            "String.bridge.erl",
            include_str!("../../src/stdlib/String.bridge.erl"),
        ),
        (
            "Int.bridge.erl",
            include_str!("../../src/stdlib/Int.bridge.erl"),
        ),
        (
            "Float.bridge.erl",
            include_str!("../../src/stdlib/Float.bridge.erl"),
        ),
        (
            "Regex.bridge.erl",
            include_str!("../../src/stdlib/Regex.bridge.erl"),
        ),
        (
            "Math.bridge.erl",
            include_str!("../../src/stdlib/Math.bridge.erl"),
        ),
        (
            "List.bridge.erl",
            include_str!("../../src/stdlib/List.bridge.erl"),
        ),
        (
            "Set.bridge.erl",
            include_str!("../../src/stdlib/Set.bridge.erl"),
        ),
        ("runtime.erl", include_str!("../../src/stdlib/runtime.erl")),
        (
            "Time.bridge.erl",
            include_str!("../../src/stdlib/Time.bridge.erl"),
        ),
        (
            "DateTime.bridge.erl",
            include_str!("../../src/stdlib/DateTime.bridge.erl"),
        ),
        (
            "BitString.bridge.erl",
            include_str!("../../src/stdlib/BitString.bridge.erl"),
        ),
        (
            "IO.bridge.erl",
            include_str!("../../src/stdlib/IO.bridge.erl"),
        ),
        (
            "Dynamic.bridge.erl",
            include_str!("../../src/stdlib/Dynamic.bridge.erl"),
        ),
        (
            "Array.bridge.erl",
            include_str!("../../src/stdlib/Array.bridge.erl"),
        ),
        (
            "evidence.bridge.erl",
            include_str!("../../src/stdlib/evidence.bridge.erl"),
        ),
    ]
}

/// Compile the stdlib into a shared temp directory, once per test process.
/// Tests can then point `erl -pa` at this dir to load Std.* beams + bridges.
pub fn stdlib_dir() -> &'static PathBuf {
    static DIR: OnceLock<PathBuf> = OnceLock::new();
    DIR.get_or_init(build_stdlib)
}

pub fn build_stdlib() -> PathBuf {
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
            _ => format!(
                "std_{}_bridge.erl",
                stem.split('.').next().unwrap().to_lowercase()
            ),
        };
        let path = dir.join(&on_disk);
        std::fs::write(&path, source).unwrap();
        let output = run_bounded(
            std::process::Command::new("erlc")
                .arg("-o")
                .arg(&dir)
                .arg(&path),
            SUBPROCESS_LIMIT,
        )
        .expect("failed to run erlc on bridge");
        assert!(
            output.status.success(),
            "erlc failed on bridge {on_disk}:\nstderr: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }

    // Build a one-off checker with prelude and emit each Std.* module.
    let stdlib_root =
        std::env::temp_dir().join(format!("saga_effect_prop_stdlib_root_{pid}_{unique}"));
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
    let mut ctx = codegen::CodegenContext {
        modules,
        let_effect_bindings: result.let_effect_bindings.clone(),
        prelude_imports: result.prelude_imports.clone(),
    };
    codegen::precompute_context_call_effects(&mut ctx, &result);

    let module_names: Vec<String> = ctx.modules.keys().cloned().collect();
    for name in module_names {
        if !name.starts_with("Std.") {
            continue;
        }
        let Some(m) = ctx.modules.get(&name) else {
            continue;
        };
        let erl_name = name.to_lowercase().replace('.', "_");
        let mod_result = result.module_check_results().get(&name).map(|r| r.as_ref());
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
        let output = run_bounded(
            std::process::Command::new("erlc")
                .arg("-o")
                .arg(&dir)
                .arg(&core_path),
            SUBPROCESS_LIMIT,
        )
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

pub fn make_checker(root: PathBuf) -> typechecker::Checker {
    let module_map = typechecker::scan_source_dir(&root).expect("scan failed");
    let mut checker = typechecker::Checker::with_project_root(root);
    checker.set_module_map(module_map);
    let prelude_src = include_str!("../../src/stdlib/prelude.saga");
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

/// Why a source was rejected before code generation.
#[derive(Debug, Clone)]
pub enum FrontendError {
    Lex(String),
    Parse(String),
    Derive(String),
    Typecheck(String),
}

impl std::fmt::Display for FrontendError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FrontendError::Lex(e) => write!(f, "lex error: {e}"),
            FrontendError::Parse(e) => write!(f, "parse error: {e}"),
            FrontendError::Derive(e) => write!(f, "derive error: {e}"),
            FrontendError::Typecheck(e) => write!(f, "typecheck error: {e}"),
        }
    }
}

/// Lex, parse, derive, desugar and typecheck `source`, returning the checked
/// program or the first stage that rejected it. Does not catch panics.
pub fn try_typecheck_source(
    source: &str,
    checker: &mut typechecker::Checker,
) -> Result<Vec<saga::ast::Decl>, FrontendError> {
    let tokens = lexer::Lexer::new(source)
        .lex()
        .map_err(|e| FrontendError::Lex(format!("{e:?}")))?;
    let mut program = parser::Parser::new(tokens)
        .parse_program()
        .map_err(|e| FrontendError::Parse(format!("{e:?}")))?;
    let imported = saga::derive::collect_imported_decls(&program, checker.module_map());
    let derive_errors = saga::derive::expand_derives(&mut program, &imported);
    if !derive_errors.is_empty() {
        return Err(FrontendError::Derive(format!("{derive_errors:?}")));
    }
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
    if result.has_errors() {
        return Err(FrontendError::Typecheck(format!("{:?}", result.errors())));
    }
    Ok(program)
}

/// Render a `catch_unwind` payload as text.
pub fn panic_message(payload: Box<dyn std::any::Any + Send>) -> String {
    if let Some(s) = payload.downcast_ref::<&str>() {
        (*s).to_string()
    } else if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else {
        "<non-string panic payload>".to_string()
    }
}

/// `emit_program`, with a compiler panic turned into `Err(message)`.
pub fn try_emit_program(
    program: &Vec<saga::ast::Decl>,
    module_name: &str,
    checker: &typechecker::Checker,
    entry_export: Option<&str>,
) -> Result<String, String> {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        emit_program(program, module_name, checker, entry_export)
    }))
    .map_err(panic_message)
}

pub fn typecheck_source(
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
    let imported = saga::derive::collect_imported_decls(&program, checker.module_map());
    let derive_errors = saga::derive::expand_derives(&mut program, &imported);
    assert!(
        derive_errors.is_empty(),
        "[{fixture}] derive error: {:?}",
        derive_errors
    );
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

pub fn emit_program(
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
    let module_result = result
        .module_check_results()
        .get(&original_module_name)
        .map(|r| r.as_ref());
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
    let mut ctx = codegen::CodegenContext {
        modules,
        let_effect_bindings: result.let_effect_bindings.clone(),
        prelude_imports: result.prelude_imports.clone(),
    };
    // As the build does: plan every module against its own check result. A
    // module's own result does not hold the results of its siblings.
    codegen::precompute_context_call_effects(&mut ctx, &result);
    codegen::emit_module_with_context(
        module_name,
        &elaborated,
        &ctx,
        module_result.unwrap_or(&result),
        None,
        entry_export,
    )
}

pub fn compile_with_erlc(dir: &PathBuf, core: &str, module_name: &str, fixture: &str) {
    let core_path = dir.join(format!("{module_name}.core"));
    std::fs::write(&core_path, core).unwrap();
    let output = run_bounded(
        std::process::Command::new("erlc")
            .arg("-o")
            .arg(dir)
            .arg(&core_path),
        SUBPROCESS_LIMIT,
    )
    .expect("failed to run erlc");
    assert!(
        output.status.success(),
        "[{fixture}] erlc failed on {module_name}:\n{core}\nstderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
}

pub fn run_erl(dir: &PathBuf, eval: &str, fixture: &str) -> String {
    let run = run_bounded(
        std::process::Command::new("erl")
            .arg("-noshell")
            .arg("-pa")
            .arg(stdlib_dir())
            .arg("-pa")
            .arg(dir)
            .arg("-eval")
            .arg(eval),
        SUBPROCESS_LIMIT,
    )
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
pub fn check_result_string(fixture: &str, src: &str, expected: &str) {
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
pub fn check_result_int(fixture: &str, src: &str, expected: i64) {
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
pub fn check_cross_module(fixture: &str, modules: &[(&str, &str)], main_src: &str, expected: &str) {
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
        let program = result
            .programs()
            .get(name)
            .unwrap_or_else(|| panic!("[{fixture}] checker did not load module {name}"));
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
