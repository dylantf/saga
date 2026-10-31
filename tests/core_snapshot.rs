//! Snapshot of the Core Erlang the compiler emits.
//!
//! Compiles a fixed corpus through the same calls the build makes and
//! compares one hash per emitted module with the checked-in list
//! `tests/fixtures/core_snapshot.txt`. Nothing is run and `erlc` is not
//! invoked: the test says whether emitted code changed, not whether it is
//! right. A change that is meant to leave emitted code alone must leave this
//! test green; a change that is meant to alter it is reviewed by dumping the
//! text before and after and reading the diff, then blessed.
//!
//! The corpus:
//!
//! - `stdlib/<Module>`: every builtin `Std.*` module, compiled together as
//!   the stdlib cache build does (`ensure_stdlib_cache` in `cli/build.rs`).
//! - `examples/.../<file>.saga`: every single-file program directly inside
//!   one of `SCRIPT_DIRS` (the examples, and the programs written to pin the
//!   optimizer's fast paths), each compiled as a script (`build_script`).
//! - `fixtures/modules/<Module>`: the multi-module project the module
//!   integration tests use, each module typechecked by name and emitted as a
//!   project build emits a library module.
//!
//! A unit the front end rejects is recorded as `rejected`, and one the back
//! end panics on as `panic`, so those are pinned too.
//!
//! Environment variables:
//!
//! - `SAGA_SNAPSHOT_BLESS=1` rewrites the fixture file from this run.
//! - `SAGA_SNAPSHOT_DUMP=<dir>` writes the emitted text of every unit to
//!   `<dir>/<key with '/' replaced by '__'>.core`.
//! - `SAGA_SNAPSHOT_FILTER=<text>` (comma separated alternatives) limits the
//!   dump to keys containing one of the texts. It does not change what is
//!   compared.

use saga::{ast, codegen, derive, desugar, elaborate, lexer, parser, typechecker};
use std::collections::{BTreeMap, HashMap};
use std::path::{Path, PathBuf};

const FIXTURE: &str = "tests/fixtures/core_snapshot.txt";

const HEADER: &str = "Hash of the Core Erlang emitted for each unit of tests/core_snapshot.rs: `<key> <hash>`.\n\
Generated. Regenerate with `SAGA_SNAPSHOT_BLESS=1 cargo test --test core_snapshot`.";

/// Directories of single-file programs, relative to the repository.
const SCRIPT_DIRS: &[&str] = &[
    "examples",
    "examples/bugs",
    "examples/optimization/selective-uniform",
    "examples/optimization/static-tail-resume",
    "examples/optimization/trait-method-specialization",
];

fn repo_path(rel: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(rel)
}

/// What one unit of the corpus produced.
enum Emitted {
    Core(String),
    /// The front end rejected the source.
    Rejected(String),
    /// The back end panicked.
    Panic(String),
}

impl Emitted {
    fn fingerprint(&self) -> String {
        match self {
            Emitted::Core(text) => format!("{:016x}", fnv1a(text.as_bytes())),
            Emitted::Rejected(_) => "rejected".to_string(),
            Emitted::Panic(_) => "panic".to_string(),
        }
    }

    fn text(&self) -> String {
        match self {
            Emitted::Core(text) => text.clone(),
            Emitted::Rejected(why) => format!("%% rejected by the front end\n%% {why}\n"),
            Emitted::Panic(why) => format!("%% the back end panicked\n%% {why}\n"),
        }
    }
}

/// FNV-1a, 64 bit. Stable across runs, platforms and toolchains, which
/// `std`'s hashers do not promise.
fn fnv1a(bytes: &[u8]) -> u64 {
    let mut hash: u64 = 0xcbf2_9ce4_8422_2325;
    for byte in bytes {
        hash ^= u64::from(*byte);
        hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
    }
    hash
}

fn panic_message(payload: Box<dyn std::any::Any + Send>) -> String {
    if let Some(s) = payload.downcast_ref::<&str>() {
        (*s).to_string()
    } else if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else {
        "<non-string panic payload>".to_string()
    }
}

/// Run one emission, turning a compiler panic into `Emitted::Panic`.
fn guarded(emit: impl FnOnce() -> String) -> Emitted {
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(emit)) {
        Ok(core) => Emitted::Core(core),
        Err(payload) => Emitted::Panic(panic_message(payload)),
    }
}

fn erlang_name(module_name: &str) -> String {
    module_name.to_lowercase().replace('.', "_")
}

/// The context the build makes from a set of compiled modules: every module
/// planned against its own check result.
fn planned_context(
    modules: HashMap<String, codegen::CompiledModule>,
    result: &typechecker::CheckResult,
) -> codegen::CodegenContext {
    let mut ctx = codegen::CodegenContext {
        modules,
        prelude_imports: result.prelude_imports.clone(),
    };
    codegen::precompute_context_call_effects(&mut ctx, result);
    ctx
}

/// As `compile_std_modules` in `cli/build.rs`.
fn compile_std_modules(
    result: &typechecker::CheckResult,
) -> HashMap<String, codegen::CompiledModule> {
    result
        .module_check_results()
        .keys()
        .filter(|name| name.starts_with("Std."))
        .filter_map(|name| {
            Some((
                name.clone(),
                codegen::compile_module_from_result(name, result)?,
            ))
        })
        .collect()
}

/// Emit every module of `names` that `ctx` holds, each against its own check
/// result, as a library module (no source locations, no entry export).
fn emit_library_modules(
    prefix: &str,
    names: &[String],
    ctx: &codegen::CodegenContext,
    result: &typechecker::CheckResult,
    out: &mut BTreeMap<String, Emitted>,
) {
    let prepared = ctx.prepare_emit();
    for name in names {
        let key = format!("{prefix}/{name}");
        let (Some(compiled), Some(check_result)) =
            (ctx.modules.get(name), result.module_check_results().get(name))
        else {
            out.insert(key, Emitted::Rejected("module was not compiled".to_string()));
            continue;
        };
        let emitted = guarded(|| {
            codegen::emit_module_with_prepared_context(
                &erlang_name(name),
                &compiled.elaborated,
                &prepared,
                check_result,
                None,
                None,
            )
        });
        out.insert(key, emitted);
    }
}

/// Every builtin module, as the stdlib cache build compiles them.
fn snapshot_stdlib(out: &mut BTreeMap<String, Emitted>) {
    let mut checker = typechecker::Checker::with_prelude(None).expect("prelude");
    for (module_name, _) in typechecker::BUILTIN_MODULES {
        checker
            .try_typecheck_import_by_name(module_name)
            .unwrap_or_else(|e| panic!("stdlib module {module_name}: {}", e.message));
    }
    let result = checker.to_result();
    let ctx = planned_context(compile_std_modules(&result), &result);
    let mut names: Vec<String> = ctx.modules.keys().cloned().collect();
    names.sort();
    emit_library_modules("stdlib", &names, &ctx, &result, out);
}

/// One single-file example, as `build_script` compiles it.
fn snapshot_script(path: &Path, display_path: &str) -> Emitted {
    let source = std::fs::read_to_string(path).expect("read example");
    let tokens = match lexer::Lexer::new(&source).lex() {
        Ok(tokens) => tokens,
        Err(e) => return Emitted::Rejected(format!("lex: {}", e.message)),
    };
    let mut program = match parser::Parser::new(tokens).parse_program() {
        Ok(program) => program,
        Err(e) => return Emitted::Rejected(format!("parse: {}", e.message)),
    };
    let mut checker = typechecker::Checker::with_prelude(None).expect("prelude");
    let imported = derive::collect_imported_decls(&program, checker.module_map());
    let derive_errors = derive::expand_derives(&mut program, &imported);
    desugar::desugar_program(&mut program);
    if let Some(error) = derive_errors.first() {
        return Emitted::Rejected(format!("derive: {}", error.message));
    }
    let checked = checker.check_program(&mut program);
    if let Some(error) = checked.errors().first() {
        return Emitted::Rejected(format!("typecheck: {}", error.message));
    }
    let result = checker.to_result();

    let module_name = program
        .iter()
        .find_map(|decl| match decl {
            ast::Decl::ModuleDecl { path, .. } => Some(path.join(".")),
            _ => None,
        })
        .unwrap_or_else(|| "_script".to_string());
    guarded(|| {
        let mut modules = compile_std_modules(&result);
        let elaborated = elaborate::elaborate(&program, &result);
        modules.insert(
            module_name.clone(),
            codegen::CompiledModule::entry(elaborated, &result),
        );
        let ctx = planned_context(modules, &result);
        let source_file = codegen::SourceFile {
            path: display_path.to_string(),
            source: source.clone(),
        };
        codegen::emit_module_with_context(
            &erlang_name(&module_name),
            &ctx.modules[&module_name].elaborated,
            &ctx,
            &result,
            Some(&source_file),
            Some("main"),
        )
    })
}

/// Every `.saga` file directly inside `dir` (a path relative to the
/// repository), each as a script.
fn snapshot_scripts(dir: &str, out: &mut BTreeMap<String, Emitted>) {
    let mut files: Vec<PathBuf> = std::fs::read_dir(repo_path(dir))
        .unwrap_or_else(|e| panic!("{dir}: {e}"))
        .filter_map(|entry| entry.ok().map(|e| e.path()))
        .filter(|path| path.extension().is_some_and(|ext| ext == "saga"))
        .collect();
    files.sort();
    for path in files {
        let name = path.file_name().unwrap().to_string_lossy().into_owned();
        let key = format!("{dir}/{name}");
        let emitted = snapshot_script(&path, &key);
        out.insert(key, emitted);
    }
}

/// The modules of a project directory, each typechecked by name and emitted
/// as a project build emits a library module.
fn snapshot_project(prefix: &str, root: &Path, out: &mut BTreeMap<String, Emitted>) {
    let module_map = typechecker::scan_source_dir(root).expect("scan project");
    let mut names: Vec<String> = module_map.keys().cloned().collect();
    names.sort();
    let mut checker =
        typechecker::Checker::with_prelude(Some(root.to_path_buf())).expect("prelude");
    checker.set_module_map(module_map);
    let mut accepted = Vec::new();
    for name in &names {
        match checker.try_typecheck_import_by_name(name) {
            Ok(()) => accepted.push(name.clone()),
            Err(e) => {
                out.insert(
                    format!("{prefix}/{name}"),
                    Emitted::Rejected(format!("typecheck: {}", e.message)),
                );
            }
        }
    }
    let result = checker.to_result();
    let mut modules = compile_std_modules(&result);
    for name in &accepted {
        if let Some(compiled) = codegen::compile_module_from_result(name, &result) {
            modules.insert(name.clone(), compiled);
        }
    }
    let ctx = planned_context(modules, &result);
    emit_library_modules(prefix, &accepted, &ctx, &result, out);
}

fn read_fixture() -> BTreeMap<String, String> {
    let text = std::fs::read_to_string(repo_path(FIXTURE)).unwrap_or_default();
    text.lines()
        .filter(|line| !line.starts_with('#') && !line.trim().is_empty())
        .filter_map(|line| {
            let (key, hash) = line.rsplit_once(' ')?;
            Some((key.to_string(), hash.to_string()))
        })
        .collect()
}

fn write_fixture(actual: &BTreeMap<String, String>) {
    let mut text = String::new();
    for line in HEADER.lines() {
        text.push_str(&format!("# {line}\n"));
    }
    for (key, hash) in actual {
        text.push_str(&format!("{key} {hash}\n"));
    }
    std::fs::write(repo_path(FIXTURE), text).expect("write snapshot fixture");
}

fn env_flag(name: &str) -> bool {
    std::env::var(name).is_ok_and(|v| !v.is_empty() && v != "0")
}

fn dump(dir: &str, units: &BTreeMap<String, Emitted>) {
    let filter: Vec<String> = std::env::var("SAGA_SNAPSHOT_FILTER")
        .map(|v| v.split(',').map(|s| s.trim().to_string()).collect())
        .unwrap_or_default();
    let dir = PathBuf::from(dir);
    std::fs::create_dir_all(&dir).expect("create dump directory");
    for (key, emitted) in units {
        if !filter.is_empty() && !filter.iter().any(|f| key.contains(f.as_str())) {
            continue;
        }
        let file = dir.join(format!("{}.core", key.replace('/', "__")));
        std::fs::write(&file, emitted.text()).expect("write dumped module");
    }
}

#[test]
fn emitted_core_erlang_matches_the_snapshot() {
    let started = std::time::Instant::now();
    let mut units = BTreeMap::new();
    snapshot_stdlib(&mut units);
    for dir in SCRIPT_DIRS {
        snapshot_scripts(dir, &mut units);
    }
    snapshot_project(
        "fixtures/modules",
        &repo_path("tests/fixtures/modules"),
        &mut units,
    );
    println!(
        "core snapshot: {} units in {:.1}s",
        units.len(),
        started.elapsed().as_secs_f64()
    );

    if let Ok(dir) = std::env::var("SAGA_SNAPSHOT_DUMP")
        && !dir.is_empty()
    {
        dump(&dir, &units);
    }

    let actual: BTreeMap<String, String> = units
        .iter()
        .map(|(key, emitted)| (key.clone(), emitted.fingerprint()))
        .collect();

    if env_flag("SAGA_SNAPSHOT_BLESS") {
        write_fixture(&actual);
        println!("blessed: {} units", actual.len());
        return;
    }

    let expected = read_fixture();
    let mut problems = Vec::new();
    for (key, hash) in &actual {
        match expected.get(key) {
            None => problems.push(format!("new unit, not in the snapshot: {key}")),
            Some(old) if old != hash => {
                problems.push(format!("changed: {key} ({old} -> {hash})"))
            }
            Some(_) => {}
        }
    }
    for key in expected.keys() {
        if !actual.contains_key(key) {
            problems.push(format!("gone, still in the snapshot: {key}"));
        }
    }
    assert!(
        problems.is_empty(),
        "emitted Core Erlang differs from {FIXTURE} in {} of {} units:\n  {}\n\
         Dump the text with SAGA_SNAPSHOT_DUMP=<dir> (before and after) to read the \
         difference; if it is intended, rerun with SAGA_SNAPSHOT_BLESS=1.",
        problems.len(),
        actual.len(),
        problems.join("\n  ")
    );
}
