use project_config::ProjectConfig;
use saga::{ast, codegen, derive, desugar, elaborate, lexer, parser, project_config, typechecker};

use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Instant;

use super::cache::{
    BuildInputFingerprint, BuildManifest, BuildManifestInput, BuildModuleArtifact,
    compare_dependency_fingerprints, compare_input_fingerprints, content_hash, file_mtime,
    input_fingerprint_changes, missing_output_artifact, module_artifacts_ready,
    module_interface_fingerprint, project_dependency_fingerprints, project_input_fingerprints,
    relative_source_path, script_input_fingerprints, unexpected_output_artifact,
    write_build_manifest,
};
use super::color;
use super::diagnostics::{byte_offset_to_line_col, print_tc_diagnostic};

const BUILD_HASH: &str = env!("SAGA_BUILD_HASH");

fn build_trace_enabled() -> bool {
    std::env::var_os("SAGA_BUILD_TRACE").is_some()
}

fn trace_build_phase(scope: &str, phase: &str, duration: std::time::Duration) {
    if build_trace_enabled() {
        eprintln!(
            "[saga-build] scope={} phase={} elapsed={:.1}ms",
            scope,
            phase,
            duration.as_secs_f64() * 1000.0
        );
    }
}

fn timed_build_phase<T>(scope: &str, phase: &str, f: impl FnOnce() -> T) -> T {
    if !build_trace_enabled() {
        return f();
    }
    let start = Instant::now();
    let out = f();
    trace_build_phase(scope, phase, start.elapsed());
    out
}

fn trace_cache_event(scope: &str, profile: &str, outcome: &str, reason: &str) {
    if build_trace_enabled() {
        eprintln!(
            "[saga-build] scope={} profile={} cache={} reason={}",
            scope, profile, outcome, reason
        );
    }
}

/// Compute a hash of the embedded stdlib sources and bridge files.
fn stdlib_content_hash() -> String {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    for (name, source) in typechecker::BUILTIN_MODULES {
        name.hash(&mut hasher);
        source.hash(&mut hasher);
    }
    for (name, source) in stdlib_bridge_files() {
        name.hash(&mut hasher);
        source.hash(&mut hasher);
    }
    format!("{:016x}", hasher.finish())
}

/// Compute the stdlib artifact fingerprint for this compiler build.
/// This intentionally includes the compiler build hash so stdlib beams are
/// never reused across different compiler binaries.
fn stdlib_fingerprint() -> String {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    BUILD_HASH.hash(&mut hasher);
    stdlib_content_hash().hash(&mut hasher);
    format!("{:016x}", hasher.finish())
}

#[derive(serde::Serialize, serde::Deserialize)]
struct StdlibManifest {
    fingerprint: String,
    compiler_version: String,
    content_hash: String,
}

impl StdlibManifest {
    fn path(stdlib_dir: &Path) -> PathBuf {
        stdlib_dir.join(".manifest")
    }

    fn write(&self, stdlib_dir: &Path) {
        let path = Self::path(stdlib_dir);
        let content = toml::to_string(self).expect("failed to serialize stdlib manifest");
        super::cache::write_atomic(&path, content.as_bytes(), "stdlib manifest");
    }

    fn read(stdlib_dir: &Path) -> Option<Self> {
        let path = Self::path(stdlib_dir);
        let content = fs::read_to_string(&path).ok()?;
        toml::from_str(&content).ok()
    }
}

/// Check if a cached build is still valid for the given script file.
/// Returns a `ScriptBuild` if the cache is fresh.
pub fn check_script_cache(file: &str, profile: &str) -> Option<ScriptBuild> {
    let build_root = Path::new(file)
        .parent()
        .unwrap_or(Path::new("."))
        .join("_build");
    let build_dir = build_root.join(profile);
    let stdlib_fingerprint = stdlib_fingerprint();
    let stdlib_dir = stdlib_cache_dir(&build_root, &stdlib_fingerprint);

    let Some(manifest) = BuildManifest::read(&build_dir) else {
        trace_cache_event("script", profile, "miss", "manifest missing or unreadable");
        return None;
    };
    if manifest.compiler_version != BUILD_HASH {
        trace_cache_event("script", profile, "miss", "compiler hash changed");
        return None;
    }
    if manifest.manifest_version != super::cache::BUILD_MANIFEST_VERSION {
        trace_cache_event("script", profile, "miss", "manifest version changed");
        return None;
    }
    if manifest.profile != profile {
        trace_cache_event("script", profile, "miss", "profile changed");
        return None;
    }
    if manifest.stdlib_fingerprint != stdlib_fingerprint {
        trace_cache_event("script", profile, "miss", "stdlib fingerprint changed");
        return None;
    }

    let rel_source = relative_source_path(file);
    if manifest.source_file != rel_source {
        trace_cache_event("script", profile, "miss", "source file changed");
        return None;
    }

    let current_inputs = script_input_fingerprints(file);
    if let Err(reason) = compare_input_fingerprints(&manifest.input_fingerprints, &current_inputs) {
        trace_cache_event("script", profile, "miss", &reason);
        return None;
    }

    if let Some(missing) = missing_output_artifact(&build_dir, &manifest) {
        trace_cache_event(
            "script",
            profile,
            "miss",
            &format!("artifact missing: {missing}"),
        );
        return None;
    }
    if let Some(unexpected) = unexpected_output_artifact(&build_dir, &manifest) {
        trace_cache_event(
            "script",
            profile,
            "miss",
            &format!("unexpected artifact: {unexpected}"),
        );
        return None;
    }
    if !stdlib_cache_is_complete(&stdlib_dir, &stdlib_fingerprint) {
        trace_cache_event("script", profile, "miss", "stdlib cache incomplete");
        return None;
    }

    trace_cache_event("script", profile, "hit", "manifest and artifacts valid");
    Some(ScriptBuild {
        build_dir,
        stdlib_dir,
        erlang_name: manifest.entry_module,
    })
}

/// Check if a cached build is still valid for a project.
/// Returns `Some((build_dir, stdlib_dir))` if the cache is fresh.
pub fn check_project_cache(project_root: &Path, profile: &str) -> Option<(PathBuf, PathBuf)> {
    let build_dir = project_root.join("_build").join(profile);
    let build_root = project_root.join("_build");
    let stdlib_fingerprint = stdlib_fingerprint();
    let stdlib_dir = stdlib_cache_dir(&build_root, &stdlib_fingerprint);

    let Some(manifest) = BuildManifest::read(&build_dir) else {
        trace_cache_event("project", profile, "miss", "manifest missing or unreadable");
        return None;
    };
    let config = ProjectConfig::load(project_root);
    if manifest.compiler_version != BUILD_HASH {
        trace_cache_event("project", profile, "miss", "compiler hash changed");
        return None;
    }
    if manifest.manifest_version != super::cache::BUILD_MANIFEST_VERSION {
        trace_cache_event("project", profile, "miss", "manifest version changed");
        return None;
    }
    if manifest.profile != profile {
        trace_cache_event("project", profile, "miss", "profile changed");
        return None;
    }
    if manifest.stdlib_fingerprint != stdlib_fingerprint {
        trace_cache_event("project", profile, "miss", "stdlib fingerprint changed");
        return None;
    }

    let current_dependencies = project_dependency_fingerprints(project_root, &config);
    if let Err(reason) =
        compare_dependency_fingerprints(&manifest.dependency_fingerprints, &current_dependencies)
    {
        trace_cache_event("project", profile, "miss", &reason);
        return None;
    }

    let current_inputs = project_input_fingerprints(project_root, &config);
    if let Err(reason) = compare_input_fingerprints(&manifest.input_fingerprints, &current_inputs) {
        trace_cache_event("project", profile, "miss", &reason);
        return None;
    }

    if let Some(missing) = missing_output_artifact(&build_dir, &manifest) {
        trace_cache_event(
            "project",
            profile,
            "miss",
            &format!("artifact missing: {missing}"),
        );
        return None;
    }
    if let Some(unexpected) = unexpected_output_artifact(&build_dir, &manifest) {
        trace_cache_event(
            "project",
            profile,
            "miss",
            &format!("unexpected artifact: {unexpected}"),
        );
        return None;
    }
    if !stdlib_cache_is_complete(&stdlib_dir, &stdlib_fingerprint) {
        trace_cache_event("project", profile, "miss", "stdlib cache incomplete");
        return None;
    }

    trace_cache_event("project", profile, "hit", "manifest and artifacts valid");
    Some((build_dir, stdlib_dir))
}

/// Find the maximum mtime across all .saga files and project.toml in a project.
fn max_project_mtime(root: &Path) -> u64 {
    let mut max = file_mtime(&root.join("project.toml"));
    collect_dy_mtimes(root, &mut max);
    max
}

fn collect_dy_mtimes(dir: &Path, max: &mut u64) {
    let Ok(entries) = fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            if path
                .file_name()
                .is_some_and(|n| n == "_build" || n == "tests")
            {
                continue;
            }
            collect_dy_mtimes(&path, max);
        } else if path.extension().is_some_and(|ext| ext == "saga") {
            let mtime = file_mtime(&path);
            if mtime > *max {
                *max = mtime;
            }
        }
    }
}

pub fn parse_and_typecheck(
    source: &str,
    source_path: &str,
    checker: &mut typechecker::Checker,
) -> (ast::Program, typechecker::CheckResult) {
    parse_and_typecheck_inner(source, source_path, checker)
}

pub fn parse_and_typecheck_inner(
    source: &str,
    source_path: &str,
    checker: &mut typechecker::Checker,
) -> (ast::Program, typechecker::CheckResult) {
    let tokens = match lexer::Lexer::new(source).lex() {
        Ok(t) => t,
        Err(e) => {
            let (line, col) = byte_offset_to_line_col(source, e.pos);
            eprintln!(
                "Lex error at {}:{}:{}: {}",
                source_path, line, col, e.message
            );
            std::process::exit(1);
        }
    };
    let mut parser = parser::Parser::new(tokens);
    let mut program = match parser.parse_program() {
        Ok(p) => p,
        Err(e) => {
            let (line, col) = byte_offset_to_line_col(source, e.span.start);
            eprintln!(
                "Parse error at {}:{}:{}: {}",
                source_path, line, col, e.message
            );
            std::process::exit(1);
        }
    };
    let imported = derive::collect_imported_decls(&program, checker.module_map());
    let derive_errors = derive::expand_derives(&mut program, &imported);
    desugar::desugar_program(&mut program);
    for d in &derive_errors {
        print_tc_diagnostic(source, source_path, d);
    }
    let result = checker.check_program(&mut program);
    for w in result.warnings() {
        print_tc_diagnostic(source, source_path, w);
    }
    if result.has_errors() {
        for e in result.errors() {
            print_tc_diagnostic(source, source_path, e);
        }
        std::process::exit(1);
    }
    (program, result)
}

pub fn make_checker(project_root: Option<PathBuf>) -> typechecker::Checker {
    typechecker::Checker::with_prelude(project_root).unwrap_or_else(|e| {
        eprintln!("Prelude type error: {}", e);
        std::process::exit(1);
    })
}

/// Lower an elaborated module using a prepared cross-module emit context.
pub fn emit_module_prepared(
    module_name: &str,
    elaborated: &ast::Program,
    prepared: &codegen::PreparedEmitContext<'_>,
    check_result: &typechecker::CheckResult,
    build_dir: &Path,
    source_file: Option<&codegen::SourceFile>,
    entry_export: Option<&str>,
) {
    let erlang_name = module_name.to_lowercase().replace('.', "_");
    let core_src = codegen::emit_module_with_prepared_context(
        &erlang_name,
        elaborated,
        prepared,
        check_result,
        source_file,
        entry_export,
    );
    let core_path = build_dir.join(format!("{}.core", erlang_name));
    fs::write(&core_path, &core_src).unwrap_or_else(|e| {
        eprintln!("Error writing {}: {}", core_path.display(), e);
        std::process::exit(1);
    });
}

/// Typecheck and elaborate Std modules. Returns compiled module bundles.
pub fn compile_std_modules(
    result: &typechecker::CheckResult,
) -> HashMap<String, codegen::CompiledModule> {
    let mut modules = HashMap::new();
    for module_name in result.module_check_results().keys() {
        if !module_name.starts_with("Std.") {
            continue;
        }
        if let Some(compiled) = codegen::compile_module_from_result(module_name, result) {
            modules.insert(module_name.clone(), compiled);
        }
    }
    modules
}

/// Returns embedded stdlib bridge (.erl) files as (filename, source) pairs.
fn stdlib_bridge_files() -> Vec<(&'static str, &'static str)> {
    vec![
        (
            "std_evidence_bridge.erl",
            include_str!("../stdlib/evidence.bridge.erl"),
        ),
        (
            "std_file_bridge.erl",
            include_str!("../stdlib/File.bridge.erl"),
        ),
        (
            "std_dict_bridge.erl",
            include_str!("../stdlib/Dict.bridge.erl"),
        ),
        (
            "std_string_bridge.erl",
            include_str!("../stdlib/String.bridge.erl"),
        ),
        (
            "std_crypto_bridge.erl",
            include_str!("../stdlib/Crypto.bridge.erl"),
        ),
        (
            "std_int_bridge.erl",
            include_str!("../stdlib/Int.bridge.erl"),
        ),
        (
            "std_float_bridge.erl",
            include_str!("../stdlib/Float.bridge.erl"),
        ),
        (
            "std_regex_bridge.erl",
            include_str!("../stdlib/Regex.bridge.erl"),
        ),
        (
            "std_math_bridge.erl",
            include_str!("../stdlib/Math.bridge.erl"),
        ),
        (
            "std_list_bridge.erl",
            include_str!("../stdlib/List.bridge.erl"),
        ),
        (
            "std_set_bridge.erl",
            include_str!("../stdlib/Set.bridge.erl"),
        ),
        ("saga_runtime.erl", include_str!("../stdlib/runtime.erl")),
        (
            "std_time_bridge.erl",
            include_str!("../stdlib/Time.bridge.erl"),
        ),
        (
            "std_datetime_bridge.erl",
            include_str!("../stdlib/DateTime.bridge.erl"),
        ),
        (
            "std_bitstring_bridge.erl",
            include_str!("../stdlib/BitString.bridge.erl"),
        ),
        ("std_io_bridge.erl", include_str!("../stdlib/IO.bridge.erl")),
        (
            "std_dynamic_bridge.erl",
            include_str!("../stdlib/Dynamic.bridge.erl"),
        ),
        (
            "std_array_bridge.erl",
            include_str!("../stdlib/Array.bridge.erl"),
        ),
        (
            "std_env_bridge.erl",
            include_str!("../stdlib/Env.bridge.erl"),
        ),
    ]
}

/// Write stdlib bridge .erl files into the build directory.
fn write_stdlib_bridges(build_dir: &Path) {
    for (filename, source) in stdlib_bridge_files() {
        let path = build_dir.join(filename);
        fs::write(&path, source).unwrap_or_else(|e| {
            eprintln!("Error writing bridge file {}: {}", path.display(), e);
            std::process::exit(1);
        });
    }
}

fn stdlib_cache_root(build_root: &Path) -> PathBuf {
    build_root.join(".stdlib")
}

fn stdlib_cache_dir(build_root: &Path, fingerprint: &str) -> PathBuf {
    stdlib_cache_root(build_root).join(fingerprint)
}

fn expected_stdlib_beams() -> Vec<String> {
    let mut beams = Vec::new();
    for (module_name, _) in typechecker::BUILTIN_MODULES {
        beams.push(format!(
            "{}.beam",
            module_name.to_lowercase().replace('.', "_")
        ));
    }
    for (filename, _) in stdlib_bridge_files() {
        let stem = Path::new(filename)
            .file_stem()
            .and_then(|s| s.to_str())
            .expect("stdlib bridge file must have stem");
        beams.push(format!("{}.beam", stem));
    }
    beams
}

fn stdlib_cache_is_complete(stdlib_dir: &Path, fingerprint: &str) -> bool {
    let Some(manifest) = StdlibManifest::read(stdlib_dir) else {
        return false;
    };
    if manifest.fingerprint != fingerprint {
        return false;
    }
    if manifest.compiler_version != BUILD_HASH {
        return false;
    }
    if manifest.content_hash != stdlib_content_hash() {
        return false;
    }
    expected_stdlib_beams()
        .into_iter()
        .all(|beam| stdlib_dir.join(beam).exists())
}

/// Ensure precompiled stdlib beams exist in the project's _build/.stdlib/ directory.
/// Returns the stdlib directory path. On a cold cache, creates a fresh checker,
/// imports ALL builtin modules, elaborates, and compiles them.
pub fn ensure_stdlib_cache(build_root: &Path) -> PathBuf {
    let fingerprint = stdlib_fingerprint();
    let cache_root = stdlib_cache_root(build_root);
    let cache_dir = stdlib_cache_dir(build_root, &fingerprint);

    if stdlib_cache_is_complete(&cache_dir, &fingerprint) {
        return cache_dir;
    }

    eprintln!("  {} stdlib...", color::dim("Compiling"));

    fs::create_dir_all(&cache_root).unwrap_or_else(|e| {
        eprintln!("Error creating stdlib cache root: {}", e);
        std::process::exit(1);
    });
    let temp_dir = cache_root.join(format!(".tmp-{}-{}", fingerprint, std::process::id()));
    let _ = fs::remove_dir_all(&temp_dir);
    fs::create_dir_all(&temp_dir).unwrap_or_else(|e| {
        eprintln!("Error creating stdlib cache dir: {}", e);
        std::process::exit(1);
    });

    let result = timed_build_phase("stdlib", "typecheck", || {
        // Create a dedicated checker and force-import all builtin modules
        let mut checker = make_checker(None);
        for (module_name, _) in typechecker::BUILTIN_MODULES {
            checker.typecheck_import_by_name(module_name);
        }
        checker.to_result()
    });

    // Elaborate all Std modules
    let compiled_modules = timed_build_phase("stdlib", "compile_std_modules", || {
        compile_std_modules(&result)
    });

    // Build CodegenContext and emit .core files
    let mut ctx = codegen::CodegenContext {
        modules: compiled_modules.clone(),
        let_effect_bindings: HashMap::new(),
        prelude_imports: result.prelude_imports.clone(),
    };
    timed_build_phase("stdlib", "precompute_call_effects", || {
        codegen::precompute_context_call_effects(&mut ctx, &result);
    });
    let prepared = timed_build_phase("stdlib", "prepare_emit_context", || ctx.prepare_emit());
    for (module_name, compiled) in &compiled_modules {
        let check_result = result
            .module_check_results()
            .get(module_name)
            .expect("compiled std module missing module check result");
        timed_build_phase(module_name, "emit_std_module", || {
            emit_module_prepared(
                module_name,
                &compiled.elaborated,
                &prepared,
                check_result,
                &temp_dir,
                None,
                None,
            );
        });
    }

    // Write bridge .erl files
    write_stdlib_bridges(&temp_dir);

    // Compile everything with erlc
    let compilable_files: Vec<_> = fs::read_dir(&temp_dir)
        .unwrap()
        .filter_map(|e| e.ok())
        .filter(|e| {
            e.path()
                .extension()
                .is_some_and(|ext| ext == "core" || ext == "erl")
        })
        .map(|e| e.path())
        .collect();

    timed_build_phase("stdlib", "erlc", || {
        run_erlc_batch(&compilable_files, &temp_dir);
    });

    // Clean up source files — only keep .beam
    // for file in &compilable_files {
    //     let _ = fs::remove_file(file);
    // }

    StdlibManifest {
        fingerprint: fingerprint.clone(),
        compiler_version: BUILD_HASH.to_string(),
        content_hash: stdlib_content_hash(),
    }
    .write(&temp_dir);

    match fs::rename(&temp_dir, &cache_dir) {
        Ok(()) => {}
        Err(_) if stdlib_cache_is_complete(&cache_dir, &fingerprint) => {
            let _ = fs::remove_dir_all(&temp_dir);
        }
        Err(e) => {
            eprintln!("Error finalizing stdlib cache: {}", e);
            std::process::exit(1);
        }
    }

    if !stdlib_cache_is_complete(&cache_dir, &fingerprint) {
        eprintln!("Error: stdlib cache is incomplete after build");
        std::process::exit(1);
    }

    cache_dir
}

/// Scan project and dependency directories for .erl bridge files and copy them to the build directory.
/// Only descends into the conventional source roots (`src/`, `lib/`, `tests/`), mirroring the module
/// scanner. Anything outside those is invisible by definition, which keeps us from tripping over
/// unrelated `.erl` files in places like `.direnv` or `.git`.
fn copy_project_bridges(roots: &[&Path], build_dir: &Path) {
    let mut count = 0;
    for root in roots {
        for source_dir in ["src", "lib", "tests"] {
            let dir = root.join(source_dir);
            if !dir.is_dir() {
                continue;
            }
            if let Err(e) = copy_bridges_from_dir(&dir, build_dir, &mut count) {
                eprintln!(
                    "Error scanning for bridge files in {}: {}",
                    dir.display(),
                    e
                );
                std::process::exit(1);
            }
        }
    }
    // Bridge file count is an internal detail -- don't show to user.
}

fn copy_bridges_from_dir(dir: &Path, build_dir: &Path, count: &mut usize) -> Result<(), String> {
    let entries = fs::read_dir(dir).map_err(|e| format!("cannot read {}: {}", dir.display(), e))?;
    for entry in entries {
        let entry = entry.map_err(|e| format!("read_dir error: {}", e))?;
        let path = entry.path();
        if path.is_dir() {
            copy_bridges_from_dir(&path, build_dir, count)?;
        } else if path.extension().is_some_and(|ext| ext == "erl") {
            let filename = path.file_name().unwrap();
            let dest = build_dir.join(filename);
            fs::copy(&path, &dest).map_err(|e| {
                format!(
                    "cannot copy {} to {}: {}",
                    path.display(),
                    dest.display(),
                    e
                )
            })?;
            *count += 1;
        }
    }
    Ok(())
}

fn copy_bridge_input(project_root: &Path, input_path: &str, build_dir: &Path) -> PathBuf {
    let source = project_root.join(input_path);
    let Some(filename) = source.file_name() else {
        eprintln!("Invalid bridge path: {}", input_path);
        std::process::exit(1);
    };
    let dest = build_dir.join(filename);
    fs::copy(&source, &dest).unwrap_or_else(|e| {
        eprintln!(
            "Error copying bridge file {} to {}: {}",
            source.display(),
            dest.display(),
            e
        );
        std::process::exit(1);
    });
    dest
}

fn copy_bridge_inputs(
    project_root: &Path,
    bridge_inputs: &[String],
    build_dir: &Path,
) -> Vec<PathBuf> {
    bridge_inputs
        .iter()
        .map(|input_path| copy_bridge_input(project_root, input_path, build_dir))
        .collect()
}

/// Max files per erlc invocation. Chunked to stay well under OS ARG_MAX
/// (~2MB on Linux); at ~60 bytes/path this leaves ample headroom.
const ERLC_BATCH_CHUNK: usize = 1000;

/// Compile a batch of .core/.erl files with as few erlc invocations as possible.
/// One BEAM startup is amortized across each chunk.
pub fn run_erlc_batch(files: &[PathBuf], out_dir: &Path) {
    for chunk in files.chunks(ERLC_BATCH_CHUNK) {
        run_erlc_chunk(chunk, out_dir);
    }
}

fn run_erlc_chunk(files: &[PathBuf], out_dir: &Path) {
    if files.is_empty() {
        return;
    }
    let verbose = super::is_verbose();
    let output = std::process::Command::new("erlc")
        .arg("-o")
        .arg(out_dir)
        .args(files)
        .output()
        .unwrap_or_else(|e| {
            eprintln!("Failed to run erlc: {}", e);
            std::process::exit(1);
        });

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    if !output.status.success() {
        if !stdout.is_empty() {
            eprintln!("{}", stdout.trim());
        }
        if !stderr.is_empty() {
            eprintln!("{}", stderr.trim());
        }
        eprintln!("erlc failed");
        std::process::exit(1);
    }

    if verbose {
        let has_output = !stdout.trim().is_empty() || !stderr.trim().is_empty();
        if has_output {
            eprintln!("  erlc ({} files)", files.len());
        }
        if !stdout.is_empty() {
            eprintln!("{}", stdout.trim());
        }
        if !stderr.is_empty() {
            eprintln!("{}", stderr.trim());
        }
    }
}

/// Compile all .core and .erl files in a directory with erlc.
pub fn run_erlc(build_dir: &Path, build_start: Instant) {
    let compilable_files: Vec<_> = fs::read_dir(build_dir)
        .unwrap()
        .filter_map(|e| e.ok())
        .filter(|e| {
            e.path()
                .extension()
                .is_some_and(|ext| ext == "core" || ext == "erl")
        })
        .map(|e| e.path())
        .collect();

    run_erlc_batch(&compilable_files, build_dir);

    let elapsed = build_start.elapsed();
    eprintln!(
        "  {} in {:.2}s",
        color::green("Built"),
        elapsed.as_secs_f64()
    );
}

/// Run a compiled module on the BEAM.
pub fn exec_erl(build_dir: &Path, stdlib_dir: &Path, extra_pa: &[PathBuf], entry_module: &str) {
    exec_erl_with_timeout(build_dir, stdlib_dir, extra_pa, entry_module, None);
}

/// Run a compiled module on the BEAM, optionally enforcing a wall-clock timeout.
pub fn exec_erl_with_timeout(
    build_dir: &Path,
    stdlib_dir: &Path,
    extra_pa: &[PathBuf],
    entry_module: &str,
    timeout: Option<std::time::Duration>,
) {
    let eval = format!(
        "try '{}':main(unit) of _ -> init:stop() catch C:R:S -> saga_runtime:format_crash(C, R, S), init:stop(1) end",
        entry_module
    );
    let mut cmd = std::process::Command::new("erl");
    cmd.arg("+Bd")
        .arg("-noshell")
        .arg("-pa")
        .arg(stdlib_dir)
        .arg("-pa")
        .arg(build_dir);

    for dir in extra_pa {
        cmd.arg("-pa").arg(dir);
    }

    cmd.arg("-eval").arg(&eval);

    let mut child = cmd.spawn().unwrap_or_else(|e| {
        eprintln!("Failed to run erl: {}", e);
        std::process::exit(1);
    });

    let status = if let Some(timeout) = timeout {
        let deadline = std::time::Instant::now() + timeout;
        loop {
            if let Some(status) = child.try_wait().unwrap_or_else(|e| {
                eprintln!("Failed while waiting for erl: {}", e);
                std::process::exit(1);
            }) {
                break status;
            }
            if std::time::Instant::now() >= deadline {
                let _ = child.kill();
                let _ = child.wait();
                eprintln!(
                    "Test run timed out after {}s while executing module '{}'",
                    timeout.as_secs(),
                    entry_module
                );
                std::process::exit(124);
            }
            std::thread::sleep(std::time::Duration::from_millis(50));
        }
    } else {
        child.wait().unwrap_or_else(|e| {
            eprintln!("Failed while waiting for erl: {}", e);
            std::process::exit(1);
        })
    };

    if !status.success() {
        std::process::exit(status.code().unwrap_or(1));
    }
}

pub struct ProjectBuild {
    pub build_dir: PathBuf,
    pub stdlib_dir: PathBuf,
    pub extra_ebin_dirs: Vec<PathBuf>,
}

enum ProjectRebuildPlan {
    Full,
    Partial {
        modules: HashSet<String>,
        bridges: Vec<String>,
    },
}

struct ProjectRebuildOptions<'a> {
    stdlib_fingerprint: &'a str,
    profile: &'a str,
    dependency_fingerprints: &'a [super::cache::BuildDependencyFingerprint],
    custom_main: bool,
}

impl ProjectRebuildPlan {
    fn should_emit(&self, module_name: &str) -> bool {
        match self {
            ProjectRebuildPlan::Full => true,
            ProjectRebuildPlan::Partial { modules, .. } => modules.contains(module_name),
        }
    }

    fn is_full(&self) -> bool {
        matches!(self, ProjectRebuildPlan::Full)
    }

    fn bridge_inputs(&self) -> &[String] {
        match self {
            ProjectRebuildPlan::Full => &[],
            ProjectRebuildPlan::Partial { bridges, .. } => bridges,
        }
    }
}

fn erlang_module_name(module_name: &str) -> String {
    if module_name == "Main" {
        "main".to_string()
    } else {
        module_name.to_lowercase().replace('.', "_")
    }
}

fn module_imports(program: &ast::Program) -> Vec<String> {
    program
        .iter()
        .filter_map(|decl| match decl {
            ast::Decl::Import { module_path, .. } => Some(module_path.join(".")),
            _ => None,
        })
        .collect()
}

fn reverse_dependent_closure(
    imports_by_module: &HashMap<String, Vec<String>>,
    roots: HashSet<String>,
) -> HashSet<String> {
    let mut affected = roots;
    let mut changed = true;
    while changed {
        changed = false;
        for (module_name, imports) in imports_by_module {
            if affected.contains(module_name) {
                continue;
            }
            if imports.iter().any(|import| affected.contains(import)) {
                affected.insert(module_name.clone());
                changed = true;
            }
        }
    }
    affected
}

fn reachable_imports(
    imports_by_module: &HashMap<String, Vec<String>>,
    root: &str,
) -> HashSet<String> {
    let mut reachable = HashSet::new();
    let mut stack = imports_by_module.get(root).cloned().unwrap_or_default();
    while let Some(module_name) = stack.pop() {
        if !reachable.insert(module_name.clone()) {
            continue;
        }
        if let Some(imports) = imports_by_module.get(&module_name) {
            stack.extend(imports.iter().cloned());
        }
    }
    reachable
}

fn scc_members_for_roots(
    imports_by_module: &HashMap<String, Vec<String>>,
    roots: &HashSet<String>,
) -> HashSet<String> {
    let mut all_modules: HashSet<String> = imports_by_module.keys().cloned().collect();
    for imports in imports_by_module.values() {
        all_modules.extend(imports.iter().cloned());
    }

    let mut members = HashSet::new();
    for root in roots {
        members.insert(root.clone());
        let reachable_from_root = reachable_imports(imports_by_module, root);
        for candidate in &all_modules {
            if candidate == root {
                continue;
            }
            if !reachable_from_root.contains(candidate) {
                continue;
            }
            if reachable_imports(imports_by_module, candidate).contains(root) {
                members.insert(candidate.clone());
            }
        }
    }
    members
}

fn module_artifact_for_source(
    module_name: &str,
    source_file: &codegen::SourceFile,
    exports: Option<&typechecker::ModuleExports>,
) -> BuildModuleArtifact {
    let erlang_name = erlang_module_name(module_name);
    BuildModuleArtifact {
        module_name: module_name.to_string(),
        source_path: source_file.path.clone(),
        source_hash: content_hash(source_file.source.as_bytes()),
        interface_fingerprint: exports
            .map(module_interface_fingerprint)
            .unwrap_or_else(
                || module_interface_fingerprint(&typechecker::ModuleExports::default()),
            ),
        core: format!("{erlang_name}.core"),
        beam: format!("{erlang_name}.beam"),
    }
}

fn bridge_output_artifacts(inputs: &[BuildInputFingerprint]) -> Vec<String> {
    let mut artifacts: Vec<String> = inputs
        .iter()
        .filter(|input| input.path.ends_with(".erl"))
        .filter_map(|input| {
            Path::new(&input.path)
                .file_stem()
                .and_then(|stem| stem.to_str())
                .map(|stem| format!("{stem}.beam"))
        })
        .collect();
    artifacts.sort();
    artifacts.dedup();
    artifacts
}

fn plan_project_rebuild(
    build_dir: &Path,
    previous_manifest: Option<&BuildManifest>,
    current_inputs: &[BuildInputFingerprint],
    current_module_artifacts: &[BuildModuleArtifact],
    imports_by_module: &HashMap<String, Vec<String>>,
    options: ProjectRebuildOptions<'_>,
) -> ProjectRebuildPlan {
    if options.custom_main {
        return ProjectRebuildPlan::Full;
    }
    let Some(previous) = previous_manifest else {
        return ProjectRebuildPlan::Full;
    };
    if previous.compiler_version != BUILD_HASH
        || previous.manifest_version != super::cache::BUILD_MANIFEST_VERSION
        || previous.profile != options.profile
        || previous.stdlib_fingerprint != options.stdlib_fingerprint
        || previous.dependency_fingerprints != options.dependency_fingerprints
        || previous.module_artifacts.is_empty()
    {
        return ProjectRebuildPlan::Full;
    }
    if unexpected_output_artifact(build_dir, previous).is_some() {
        return ProjectRebuildPlan::Full;
    }

    let changes = input_fingerprint_changes(&previous.input_fingerprints, current_inputs);
    if !changes.added.is_empty() || !changes.removed.is_empty() {
        return ProjectRebuildPlan::Full;
    }

    let source_to_module: HashMap<&str, &str> = current_module_artifacts
        .iter()
        .map(|artifact| (artifact.source_path.as_str(), artifact.module_name.as_str()))
        .collect();
    let previous_by_module: HashMap<&str, &BuildModuleArtifact> = previous
        .module_artifacts
        .iter()
        .map(|artifact| (artifact.module_name.as_str(), artifact))
        .collect();
    let current_by_module: HashMap<&str, &BuildModuleArtifact> = current_module_artifacts
        .iter()
        .map(|artifact| (artifact.module_name.as_str(), artifact))
        .collect();
    let previous_module_names: HashSet<&str> = previous_by_module.keys().copied().collect();
    let current_module_names: HashSet<&str> = current_by_module.keys().copied().collect();
    if previous_module_names != current_module_names {
        return ProjectRebuildPlan::Full;
    }
    let mut emit_modules = HashSet::new();
    let mut changed_modules = HashSet::new();
    let mut bridge_inputs = Vec::new();
    let mut propagation_roots = HashSet::new();

    for changed_path in changes.changed {
        if changed_path.ends_with(".erl") {
            bridge_inputs.push(changed_path);
            continue;
        }
        let Some(module_name) = source_to_module.get(changed_path.as_str()) else {
            return ProjectRebuildPlan::Full;
        };
        if !changed_path.ends_with(".saga") {
            return ProjectRebuildPlan::Full;
        }
        emit_modules.insert((*module_name).to_string());
        changed_modules.insert((*module_name).to_string());

        let Some(current_artifact) = current_by_module.get(module_name) else {
            return ProjectRebuildPlan::Full;
        };
        let interface_changed =
            previous_by_module
                .get(module_name)
                .is_none_or(|previous_artifact| {
                    previous_artifact.interface_fingerprint
                        != current_artifact.interface_fingerprint
                });
        if interface_changed {
            propagation_roots.insert((*module_name).to_string());
        }
    }

    for artifact in current_module_artifacts {
        if !previous_by_module.contains_key(artifact.module_name.as_str())
            || !module_artifacts_ready(build_dir, previous, &artifact.module_name)
        {
            emit_modules.insert(artifact.module_name.clone());
        }
    }

    emit_modules.extend(scc_members_for_roots(imports_by_module, &changed_modules));
    emit_modules.extend(reverse_dependent_closure(
        imports_by_module,
        propagation_roots,
    ));
    bridge_inputs.sort();
    ProjectRebuildPlan::Partial {
        modules: emit_modules,
        bridges: bridge_inputs,
    }
}

fn print_build_elapsed(build_start: Instant) {
    let elapsed = build_start.elapsed();
    eprintln!(
        "  {} in {:.2}s",
        color::green("Built"),
        elapsed.as_secs_f64()
    );
}

/// Build a project (with project.toml) into the given build directory.
pub fn build_project(profile: &str) -> ProjectBuild {
    build_project_ext(profile, &[], None)
}

/// Build a project with optional extra source directories and a custom main.
pub fn build_project_ext(
    profile: &str,
    extra_source_dirs: &[PathBuf],
    custom_main: Option<(&str, &str)>,
) -> ProjectBuild {
    let build_start = Instant::now();
    let project_root = super::find_project_root().unwrap_or_else(|| {
        eprintln!("No project.toml found. Use `saga build <file.saga>` for single files.");
        std::process::exit(1);
    });

    let config = ProjectConfig::load(&project_root);
    if let Err(e) = config.validate() {
        eprintln!("Error in project.toml: {}", e);
        std::process::exit(1);
    }

    let has_bin = config.is_bin();

    // Phase 1: Typecheck
    let mut checker = timed_build_phase("project", "make_checker", || {
        make_checker(Some(project_root.clone()))
    });

    // Add extra source directories to the module map (e.g. tests/)
    for extra_dir in extra_source_dirs {
        match typechecker::scan_source_dir(extra_dir) {
            Ok(extra_map) => {
                if let Some(map) = checker.module_map_mut() {
                    map.extend(extra_map);
                }
            }
            Err(e) => {
                eprintln!("Error scanning {}: {}", extra_dir.display(), e);
                std::process::exit(1);
            }
        }
    }

    // Resolve dependencies and merge their modules into the module map
    timed_build_phase("project", "resolve_deps", || {
        if let Some(deps) = &config.deps
            && let Err(e) = project_config::resolve_deps(&mut checker, &project_root, deps)
        {
            eprintln!("Error resolving dependencies: {}", e);
            std::process::exit(1);
        }
    });

    let main_source = if let Some((display_path, source)) = custom_main {
        Some(codegen::SourceFile {
            path: display_path.to_string(),
            source: source.to_string(),
        })
    } else if has_bin {
        let main_file = config.main_file();
        let main_path = project_root.join(main_file);
        let source = fs::read_to_string(&main_path).unwrap_or_else(|e| {
            eprintln!("Error reading {}: {}", main_file, e);
            std::process::exit(1);
        });
        Some(codegen::SourceFile {
            path: main_file.to_string(),
            source,
        })
    } else {
        None
    };

    // If a custom main is provided, use that. Otherwise typecheck the project's
    // main module for bin projects, or exposed modules for library projects.
    let main_program = if let Some(source_file) = &main_source {
        let (program, _) = timed_build_phase("project", "parse_and_typecheck_entry", || {
            parse_and_typecheck(&source_file.source, &source_file.path, &mut checker)
        });
        Some(program)
    } else {
        // Library-only: typecheck all exposed modules to trigger the dependency walk
        if let Some(lib) = &config.library {
            let module_map = checker.module_map().cloned().unwrap_or_default();
            for exposed in &lib.expose {
                if module_map.contains_key(exposed) {
                    timed_build_phase(exposed, "typecheck_exposed_module", || {
                        checker.typecheck_import_by_name(exposed);
                    });
                } else {
                    eprintln!("Error: exposed module '{}' not found in project", exposed);
                    std::process::exit(1);
                }
            }
        }
        None
    };

    let result = timed_build_phase("project", "to_result", || checker.to_result());

    let build_dir = project_root.join("_build").join(profile);
    let previous_manifest = BuildManifest::read(&build_dir);

    // Phase 2: Elaborate all modules
    let mut compiled_modules = timed_build_phase("project", "compile_std_modules", || {
        compile_std_modules(&result)
    });

    // Ensure stdlib beams are cached in _build/
    let build_root = project_root.join("_build");
    let stdlib_dir = timed_build_phase("project", "ensure_stdlib_cache", || {
        ensure_stdlib_cache(&build_root)
    });

    // Elaborate user modules
    let codegen_info_map = result.codegen_info();
    let user_modules: Vec<String> = codegen_info_map
        .keys()
        .filter(|name| !name.starts_with("Std."))
        .cloned()
        .collect();

    let mut source_files: HashMap<String, codegen::SourceFile> = HashMap::new();
    let mut imports_by_module: HashMap<String, Vec<String>> = HashMap::new();

    for module_name in &user_modules {
        // Resolve file path for this module (needed for source info and fresh parse)
        let file_path = result.resolve_module_path(module_name).unwrap_or_else(|| {
            eprintln!("Module '{}' not found in module map", module_name);
            std::process::exit(1);
        });

        // Cached programs were already expanded, desugared, and typechecked
        // during Phase 1 (inside typecheck_import). Re-running expand_derives
        // on them would append a second copy of each synthetic ImplDef, and
        // rechecking them here duplicates the import walk work the front end
        // already paid for.
        let (mut program, from_cache) = if let Some(cached) = result.programs().get(module_name) {
            (cached.clone(), true)
        } else {
            let source = fs::read_to_string(&file_path).unwrap_or_else(|e| {
                eprintln!("Error reading {}: {}", file_path.display(), e);
                std::process::exit(1);
            });
            let tokens = lexer::Lexer::new(&source).lex().unwrap_or_else(|e| {
                eprintln!("Lex error in module {}: {:?}", module_name, e);
                std::process::exit(1);
            });
            let program = parser::Parser::new(tokens)
                .parse_program()
                .unwrap_or_else(|e| {
                    eprintln!("Parse error in module {}: {:?}", module_name, e);
                    std::process::exit(1);
                });
            (program, false)
        };
        imports_by_module.insert(module_name.clone(), module_imports(&program));

        // Read source for error location tracking
        let source_text = fs::read_to_string(&file_path).unwrap_or_default();
        let display_path = file_path
            .strip_prefix(&project_root)
            .unwrap_or(&file_path)
            .to_string_lossy()
            .to_string();
        source_files.insert(
            module_name.clone(),
            codegen::SourceFile {
                path: display_path,
                source: source_text,
            },
        );
        if !from_cache {
            let imported = derive::collect_imported_decls(&program, result.module_map());
            let derive_errors = derive::expand_derives(&mut program, &imported);
            desugar::desugar_program(&mut program);

            for d in &derive_errors {
                eprintln!("Error in module {}: {}", module_name, d.message);
            }
        }
        let cached_result = result.module_check_results().get(module_name);
        let fallback_result = if cached_result.is_none() {
            let mut mod_checker = timed_build_phase(module_name, "seed_module_checker", || {
                checker.seeded_module_checker(Some(project_root.clone()), false)
            });
            Some(timed_build_phase(module_name, "recheck_module", || {
                mod_checker.check_program(&mut program)
            }))
        } else {
            None
        };
        let mod_result = cached_result
            .or(fallback_result.as_ref())
            .expect("module result should be cached or recomputed");
        for w in mod_result.warnings() {
            eprintln!("Warning in module {}: {}", module_name, w);
        }
        if mod_result.has_errors() {
            for e in mod_result.errors() {
                eprintln!("Type error in module {}: {}", module_name, e);
            }
            std::process::exit(1);
        }

        let elaborated = timed_build_phase(module_name, "elaborate_module", || {
            elaborate::elaborate_module(&program, mod_result, module_name)
        });
        // Local-only fold here; the cross-module fold runs at emit with the full
        // set of compiled modules supplied as externals.
        let normalized_effects = timed_build_phase(module_name, "normalize_effects_local", || {
            codegen::normalize::normalize_effects(&elaborated)
        });
        let normalized = timed_build_phase(module_name, "generic_fold_local", || {
            codegen::generic_fold::fold_program(
                &normalized_effects,
                &codegen::generic_fold::ExternalCtors::new(),
                &codegen::generic_fold::ExternalFuns::new(),
            )
            .program
        });
        let resolution = timed_build_phase(module_name, "resolve_codegen_names", || {
            codegen::resolve::resolve_names(
                module_name,
                &normalized,
                codegen_info_map,
                &result.prelude_imports,
                &mod_result.resolution,
                &std::collections::HashMap::new(),
            )
        });
        let optimization = timed_build_phase(module_name, "analyze_optimization", || {
            codegen::optimize::analyze(module_name, &normalized, &resolution)
        });
        compiled_modules.insert(
            module_name.clone(),
            codegen::CompiledModule {
                codegen_info: codegen_info_map
                    .get(module_name)
                    .cloned()
                    .unwrap_or_default(),
                elaborated: normalized,
                resolution,
                front_resolution: mod_result.resolution.clone(),
                call_effects: codegen::call_effects::CallEffectMap::new(),
                call_effects_ready: false,
                optimization,
            },
        );
    }

    // Elaborate Main (if this is a bin project)
    if let Some(main_program) = &main_program {
        let main_elaborated = timed_build_phase("Main", "elaborate_module", || {
            elaborate::elaborate_module(main_program, &result, "Main")
        });
        imports_by_module.insert("Main".to_string(), module_imports(main_program));
        compiled_modules.insert(
            "Main".to_string(),
            codegen::CompiledModule {
                codegen_info: Default::default(),
                elaborated: main_elaborated,
                resolution: codegen::resolve::ResolutionMap::new(),
                front_resolution: result.resolution.clone(),
                call_effects: codegen::call_effects::CallEffectMap::new(),
                call_effects_ready: false,
                optimization: codegen::optimize::OptimizationFacts::default(),
            },
        );
        let source_file = main_source
            .as_ref()
            .expect("main source must exist for Main");
        source_files.insert(
            "Main".to_string(),
            codegen::SourceFile {
                path: source_file.path.clone(),
                source: source_file.source.clone(),
            },
        );
    }

    // Phase 3: Lower and emit user modules only (stdlib beams are cached globally)
    // user_modules + Main are the modules we need to emit; std modules are in the
    // CodegenContext for cross-module resolution but their beams come from the cache.
    let mut ctx = codegen::CodegenContext {
        modules: compiled_modules.clone(),
        let_effect_bindings: HashMap::new(),
        prelude_imports: result.prelude_imports.clone(),
    };
    timed_build_phase("project", "precompute_call_effects", || {
        codegen::precompute_context_call_effects(&mut ctx, &result);
    });
    let prepared = timed_build_phase("project", "prepare_emit_context", || ctx.prepare_emit());

    let mut modules_to_emit: Vec<&str> = user_modules.iter().map(|s| s.as_str()).collect();
    if has_bin || custom_main.is_some() {
        modules_to_emit.push("Main");
    }

    let current_inputs = project_input_fingerprints(&project_root, &config);
    let current_dependencies = project_dependency_fingerprints(&project_root, &config);
    let mut current_module_artifacts: Vec<BuildModuleArtifact> = modules_to_emit
        .iter()
        .filter_map(|module_name| {
            source_files.get(*module_name).map(|source_file| {
                module_artifact_for_source(
                    module_name,
                    source_file,
                    result.module_exports().get(*module_name),
                )
            })
        })
        .collect();
    current_module_artifacts.sort_by(|a, b| a.module_name.cmp(&b.module_name));
    let mut output_artifacts: Vec<String> = current_module_artifacts
        .iter()
        .map(|artifact| artifact.beam.clone())
        .collect();
    output_artifacts.extend(bridge_output_artifacts(&current_inputs));
    output_artifacts.sort();

    let current_stdlib_fingerprint = stdlib_fingerprint();
    let rebuild_plan = plan_project_rebuild(
        &build_dir,
        previous_manifest.as_ref(),
        &current_inputs,
        &current_module_artifacts,
        &imports_by_module,
        ProjectRebuildOptions {
            stdlib_fingerprint: &current_stdlib_fingerprint,
            profile,
            dependency_fingerprints: &current_dependencies,
            custom_main: custom_main.is_some(),
        },
    );

    if rebuild_plan.is_full() {
        let _ = fs::remove_dir_all(&build_dir);
    }
    fs::create_dir_all(&build_dir).unwrap_or_else(|e| {
        eprintln!("Error creating build dir: {}", e);
        std::process::exit(1);
    });

    let mut emitted_core_files = Vec::new();
    for module_name in &modules_to_emit {
        if !rebuild_plan.should_emit(module_name) {
            if build_trace_enabled() {
                eprintln!("[saga-build] scope={} phase=reuse_artifact", module_name);
            }
            continue;
        }
        eprintln!("  {} {}...", color::dim("Compiling"), module_name);
        let compiled = &compiled_modules[*module_name];
        let erlang_name = erlang_module_name(module_name);
        let sf = source_files.get(*module_name);
        let check_result =
            result
                .module_check_results()
                .get(*module_name)
                .or(if *module_name == "Main" {
                    Some(&result)
                } else {
                    None
                });
        timed_build_phase(module_name, "emit_module", || {
            emit_module_prepared(
                &erlang_name,
                &compiled.elaborated,
                &prepared,
                check_result.unwrap_or(&result),
                &build_dir,
                sf,
                if *module_name == "Main" {
                    Some("main")
                } else {
                    None
                },
            );
        });
        emitted_core_files.push(build_dir.join(format!("{erlang_name}.core")));
    }

    if rebuild_plan.is_full() {
        // Copy project-specific bridge (.erl) files into build dir.
        // Skip deps that have their own ebin/ — they're already on the code path.
        // Copy bridge (.erl) files from project root and deps without their own ebin/
        let mut bridge_roots: Vec<&Path> = vec![&project_root];
        let dep_roots = config
            .deps
            .as_ref()
            .map(|deps| project_config::dep_root_paths(&project_root, deps))
            .unwrap_or_default();
        for dep_root in &dep_roots {
            if !dep_root.join("ebin").exists() {
                bridge_roots.push(dep_root);
            }
        }
        timed_build_phase("project", "copy_project_bridges", || {
            copy_project_bridges(&bridge_roots, &build_dir);
        });
    } else if !rebuild_plan.bridge_inputs().is_empty() {
        let copied_bridges = timed_build_phase("project", "copy_changed_bridges", || {
            copy_bridge_inputs(&project_root, rebuild_plan.bridge_inputs(), &build_dir)
        });
        emitted_core_files.extend(copied_bridges);
    }

    if rebuild_plan.is_full() {
        timed_build_phase("project", "erlc", || {
            run_erlc(&build_dir, build_start);
        });
    } else {
        timed_build_phase("project", "erlc_partial", || {
            run_erlc_batch(&emitted_core_files, &build_dir);
            print_build_elapsed(build_start);
        });
    }

    // Write manifest for cache invalidation
    if has_bin || custom_main.is_some() {
        write_build_manifest(
            &build_dir,
            BuildManifestInput {
                entry_module: "main".to_string(),
                source_file: "project.toml".to_string(),
                source_mtime: max_project_mtime(&project_root),
                profile: profile.to_string(),
                stdlib_fingerprint: current_stdlib_fingerprint,
                input_fingerprints: current_inputs,
                dependency_fingerprints: current_dependencies,
                output_artifacts,
                module_artifacts: current_module_artifacts,
            },
        );
    }

    let extra_ebin_dirs = project_config::extra_ebin_dirs(&project_root, config.deps.as_ref());

    ProjectBuild {
        build_dir,
        stdlib_dir,
        extra_ebin_dirs,
    }
}

/// Extract the module name from a parsed program, if it has a `module` declaration.
pub fn declared_module_name(program: &ast::Program) -> Option<String> {
    program.iter().find_map(|decl| match decl {
        ast::Decl::ModuleDecl { path, .. } => Some(path.join(".")),
        _ => None,
    })
}

/// Build a single script file into the given build directory.
/// Returns (build_dir, stdlib_cache_dir, erlang_name).
pub fn build_script(file: &str, profile: &str) -> ScriptBuild {
    let build_start = Instant::now();
    let source = fs::read_to_string(file).unwrap_or_else(|e| {
        eprintln!("Error reading {}: {}", file, e);
        std::process::exit(1);
    });
    let display_path = std::env::current_dir()
        .ok()
        .and_then(|cwd| {
            Path::new(file)
                .strip_prefix(&cwd)
                .ok()
                .map(|p| p.to_path_buf())
        })
        .unwrap_or_else(|| PathBuf::from(file));
    eprintln!(
        "  {} {}...",
        color::dim("Compiling"),
        display_path.display()
    );
    let mut checker = timed_build_phase("script", "make_checker", || make_checker(None));
    let (program, _) = timed_build_phase("script", "parse_and_typecheck_entry", || {
        parse_and_typecheck(&source, file, &mut checker)
    });
    let result = timed_build_phase("script", "to_result", || checker.to_result());

    let build_root = Path::new(file)
        .parent()
        .unwrap_or(Path::new("."))
        .join("_build");
    let build_dir = build_root.join(profile);
    let _ = fs::remove_dir_all(&build_dir);
    fs::create_dir_all(&build_dir).unwrap_or_else(|e| {
        eprintln!("Error creating build dir: {}", e);
        std::process::exit(1);
    });

    // Resolve module name: use declared name if present, otherwise "_script"
    let module_name = declared_module_name(&program).unwrap_or_else(|| "_script".to_string());
    let erlang_name = module_name.to_lowercase().replace('.', "_");

    // Phase 2: Elaborate all modules (std modules needed for CodegenContext)
    let mut compiled_modules = timed_build_phase("script", "compile_std_modules", || {
        compile_std_modules(&result)
    });

    // Ensure stdlib beams are cached in _build/
    let stdlib_dir = timed_build_phase("script", "ensure_stdlib_cache", || {
        ensure_stdlib_cache(&build_root)
    });

    let elaborated = timed_build_phase("script", "elaborate_module", || {
        elaborate::elaborate(&program, &result)
    });
    compiled_modules.insert(
        module_name.clone(),
        codegen::CompiledModule {
            codegen_info: Default::default(),
            elaborated,
            resolution: codegen::resolve::ResolutionMap::new(),
            front_resolution: result.resolution.clone(),
            call_effects: codegen::call_effects::CallEffectMap::new(),
            call_effects_ready: false,
            optimization: codegen::optimize::OptimizationFacts::default(),
        },
    );

    // Phase 3: Emit only the user module
    let mut ctx = codegen::CodegenContext {
        modules: compiled_modules.clone(),
        let_effect_bindings: result.let_effect_bindings.clone(),
        prelude_imports: result.prelude_imports.clone(),
    };
    timed_build_phase("script", "precompute_call_effects", || {
        codegen::precompute_context_call_effects(&mut ctx, &result);
    });
    let prepared = timed_build_phase("script", "prepare_emit_context", || ctx.prepare_emit());
    let script_source = codegen::SourceFile {
        path: file.to_string(),
        source: source.clone(),
    };
    timed_build_phase("script", "emit_module", || {
        emit_module_prepared(
            &module_name,
            &compiled_modules[&module_name].elaborated,
            &prepared,
            &result,
            &build_dir,
            Some(&script_source),
            Some("main"),
        );
    });

    timed_build_phase("script", "erlc", || {
        run_erlc(&build_dir, build_start);
    });

    // Write manifest for cache invalidation
    write_build_manifest(
        &build_dir,
        BuildManifestInput {
            entry_module: erlang_name.clone(),
            source_file: relative_source_path(file),
            source_mtime: file_mtime(Path::new(file)),
            profile: profile.to_string(),
            stdlib_fingerprint: stdlib_fingerprint(),
            input_fingerprints: script_input_fingerprints(file),
            dependency_fingerprints: Vec::new(),
            output_artifacts: vec![format!("{erlang_name}.beam")],
            module_artifacts: vec![BuildModuleArtifact {
                module_name,
                source_path: relative_source_path(file),
                source_hash: content_hash(source.as_bytes()),
                interface_fingerprint: module_interface_fingerprint(
                    &typechecker::ModuleExports::default(),
                ),
                core: format!("{erlang_name}.core"),
                beam: format!("{erlang_name}.beam"),
            }],
        },
    );

    ScriptBuild {
        build_dir,
        stdlib_dir,
        erlang_name,
    }
}

pub struct ScriptBuild {
    pub build_dir: PathBuf,
    pub stdlib_dir: PathBuf,
    pub erlang_name: String,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_root(name: &str) -> PathBuf {
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let root = std::env::temp_dir().join(format!(
            "saga-build-plan-{}-{}-{}",
            name,
            std::process::id(),
            nanos
        ));
        fs::create_dir_all(&root).unwrap();
        root
    }

    fn input(path: &str, hash: &str) -> BuildInputFingerprint {
        BuildInputFingerprint {
            path: path.to_string(),
            hash: hash.to_string(),
        }
    }

    fn artifact(
        module_name: &str,
        source_path: &str,
        source_hash: &str,
        iface: &str,
    ) -> BuildModuleArtifact {
        let erlang_name = erlang_module_name(module_name);
        BuildModuleArtifact {
            module_name: module_name.to_string(),
            source_path: source_path.to_string(),
            source_hash: source_hash.to_string(),
            interface_fingerprint: iface.to_string(),
            core: format!("{erlang_name}.core"),
            beam: format!("{erlang_name}.beam"),
        }
    }

    fn manifest(
        inputs: Vec<BuildInputFingerprint>,
        artifacts: Vec<BuildModuleArtifact>,
    ) -> BuildManifest {
        BuildManifest {
            manifest_version: super::super::cache::BUILD_MANIFEST_VERSION,
            entry_module: "main".to_string(),
            source_file: "project.toml".to_string(),
            source_mtime: 0,
            compiler_version: BUILD_HASH.to_string(),
            profile: "dev".to_string(),
            stdlib_fingerprint: "stdlib".to_string(),
            output_artifacts: artifacts
                .iter()
                .map(|artifact| artifact.beam.clone())
                .collect(),
            input_fingerprints: inputs,
            dependency_fingerprints: Vec::new(),
            module_artifacts: artifacts,
        }
    }

    fn write_artifacts(build_dir: &Path, artifacts: &[BuildModuleArtifact]) {
        for artifact in artifacts {
            fs::write(build_dir.join(&artifact.core), "").unwrap();
            fs::write(build_dir.join(&artifact.beam), "").unwrap();
        }
    }

    fn imports(edges: &[(&str, &[&str])]) -> HashMap<String, Vec<String>> {
        edges
            .iter()
            .map(|(module, imports)| {
                (
                    (*module).to_string(),
                    imports.iter().map(|import| (*import).to_string()).collect(),
                )
            })
            .collect()
    }

    fn partial_work(plan: ProjectRebuildPlan) -> (HashSet<String>, Vec<String>) {
        match plan {
            ProjectRebuildPlan::Partial { modules, bridges } => (modules, bridges),
            ProjectRebuildPlan::Full => panic!("expected partial rebuild plan"),
        }
    }

    #[test]
    fn bridge_output_artifacts_are_derived_from_erl_inputs() {
        assert_eq!(
            bridge_output_artifacts(&[
                input("src/native.erl", "one"),
                input("lib/other.erl", "two"),
                input("src/Main.saga", "three"),
                input("src/native.erl", "one"),
            ]),
            vec!["native.beam".to_string(), "other.beam".to_string()]
        );
    }

    fn write_all_stdlib_beams(stdlib_dir: &Path) {
        for beam in expected_stdlib_beams() {
            fs::write(stdlib_dir.join(beam), "").unwrap();
        }
    }

    #[test]
    fn stdlib_cache_completeness_requires_manifest_metadata_and_beams() {
        let stdlib_dir = test_root("stdlib-cache");
        let fingerprint = stdlib_fingerprint();

        assert!(!stdlib_cache_is_complete(&stdlib_dir, &fingerprint));

        write_all_stdlib_beams(&stdlib_dir);
        StdlibManifest {
            fingerprint: "wrong-fingerprint".to_string(),
            compiler_version: BUILD_HASH.to_string(),
            content_hash: stdlib_content_hash(),
        }
        .write(&stdlib_dir);
        assert!(!stdlib_cache_is_complete(&stdlib_dir, &fingerprint));

        StdlibManifest {
            fingerprint: fingerprint.clone(),
            compiler_version: BUILD_HASH.to_string(),
            content_hash: "wrong-content".to_string(),
        }
        .write(&stdlib_dir);
        assert!(!stdlib_cache_is_complete(&stdlib_dir, &fingerprint));

        let first_beam = expected_stdlib_beams()
            .into_iter()
            .next()
            .expect("stdlib should have at least one expected beam");
        fs::remove_file(stdlib_dir.join(&first_beam)).unwrap();
        StdlibManifest {
            fingerprint: fingerprint.clone(),
            compiler_version: BUILD_HASH.to_string(),
            content_hash: stdlib_content_hash(),
        }
        .write(&stdlib_dir);
        assert!(!stdlib_cache_is_complete(&stdlib_dir, &fingerprint));

        fs::write(stdlib_dir.join(first_beam), "").unwrap();
        assert!(stdlib_cache_is_complete(&stdlib_dir, &fingerprint));

        let _ = fs::remove_dir_all(stdlib_dir);
    }

    #[test]
    fn project_rebuild_plan_emits_only_changed_module_when_interface_is_same() {
        let build_dir = test_root("same-interface");
        let previous_artifacts = vec![
            artifact("Helper", "src/Helper.saga", "old-helper", "helper-iface"),
            artifact("Main", "src/Main.saga", "main", "main-iface"),
        ];
        write_artifacts(&build_dir, &previous_artifacts);
        let previous = manifest(
            vec![
                input("project.toml", "config"),
                input("src/Helper.saga", "old-helper"),
                input("src/Main.saga", "main"),
            ],
            previous_artifacts,
        );
        let current_inputs = vec![
            input("project.toml", "config"),
            input("src/Helper.saga", "new-helper"),
            input("src/Main.saga", "main"),
        ];
        let current_artifacts = vec![
            artifact("Helper", "src/Helper.saga", "new-helper", "helper-iface"),
            artifact("Main", "src/Main.saga", "main", "main-iface"),
        ];

        let (modules, bridges) = partial_work(plan_project_rebuild(
            &build_dir,
            Some(&previous),
            &current_inputs,
            &current_artifacts,
            &imports(&[("Helper", &[]), ("Main", &["Helper"])]),
            ProjectRebuildOptions {
                stdlib_fingerprint: "stdlib",
                profile: "dev",
                dependency_fingerprints: &[],
                custom_main: false,
            },
        ));

        assert_eq!(modules, HashSet::from(["Helper".to_string()]));
        assert!(bridges.is_empty());
        let _ = fs::remove_dir_all(build_dir);
    }

    #[test]
    fn project_rebuild_plan_propagates_interface_changes_to_dependents() {
        let build_dir = test_root("changed-interface");
        let previous_artifacts = vec![
            artifact("Model", "src/Model.saga", "old-model", "model-iface-old"),
            artifact("View", "src/View.saga", "view", "view-iface"),
            artifact("Main", "src/Main.saga", "main", "main-iface"),
        ];
        write_artifacts(&build_dir, &previous_artifacts);
        let previous = manifest(
            vec![
                input("project.toml", "config"),
                input("src/Model.saga", "old-model"),
                input("src/View.saga", "view"),
                input("src/Main.saga", "main"),
            ],
            previous_artifacts,
        );
        let current_inputs = vec![
            input("project.toml", "config"),
            input("src/Model.saga", "new-model"),
            input("src/View.saga", "view"),
            input("src/Main.saga", "main"),
        ];
        let current_artifacts = vec![
            artifact("Model", "src/Model.saga", "new-model", "model-iface-new"),
            artifact("View", "src/View.saga", "view", "view-iface"),
            artifact("Main", "src/Main.saga", "main", "main-iface"),
        ];

        let (modules, bridges) = partial_work(plan_project_rebuild(
            &build_dir,
            Some(&previous),
            &current_inputs,
            &current_artifacts,
            &imports(&[("Model", &[]), ("View", &["Model"]), ("Main", &["View"])]),
            ProjectRebuildOptions {
                stdlib_fingerprint: "stdlib",
                profile: "dev",
                dependency_fingerprints: &[],
                custom_main: false,
            },
        ));

        assert_eq!(
            modules,
            HashSet::from(["Model".to_string(), "View".to_string(), "Main".to_string()])
        );
        assert!(bridges.is_empty());
        let _ = fs::remove_dir_all(build_dir);
    }

    #[test]
    fn project_rebuild_plan_reemits_missing_artifact_without_propagation() {
        let build_dir = test_root("missing-artifact");
        let previous_artifacts = vec![
            artifact("Helper", "src/Helper.saga", "helper", "helper-iface"),
            artifact("Main", "src/Main.saga", "main", "main-iface"),
        ];
        write_artifacts(&build_dir, &previous_artifacts[..1]);
        let previous = manifest(
            vec![
                input("project.toml", "config"),
                input("src/Helper.saga", "helper"),
                input("src/Main.saga", "main"),
            ],
            previous_artifacts,
        );
        let current_inputs = vec![
            input("project.toml", "config"),
            input("src/Helper.saga", "helper"),
            input("src/Main.saga", "main"),
        ];
        let current_artifacts = vec![
            artifact("Helper", "src/Helper.saga", "helper", "helper-iface"),
            artifact("Main", "src/Main.saga", "main", "main-iface"),
        ];

        let (modules, bridges) = partial_work(plan_project_rebuild(
            &build_dir,
            Some(&previous),
            &current_inputs,
            &current_artifacts,
            &imports(&[("Helper", &[]), ("Main", &["Helper"])]),
            ProjectRebuildOptions {
                stdlib_fingerprint: "stdlib",
                profile: "dev",
                dependency_fingerprints: &[],
                custom_main: false,
            },
        ));

        assert_eq!(modules, HashSet::from(["Main".to_string()]));
        assert!(bridges.is_empty());
        let _ = fs::remove_dir_all(build_dir);
    }

    #[test]
    fn project_rebuild_plan_treats_cycles_as_invalidation_units() {
        let build_dir = test_root("cycle");
        let previous_artifacts = vec![
            artifact("A", "src/A.saga", "old-a", "a-iface"),
            artifact("B", "src/B.saga", "b", "b-iface"),
            artifact("Main", "src/Main.saga", "main", "main-iface"),
        ];
        write_artifacts(&build_dir, &previous_artifacts);
        let previous = manifest(
            vec![
                input("project.toml", "config"),
                input("src/A.saga", "old-a"),
                input("src/B.saga", "b"),
                input("src/Main.saga", "main"),
            ],
            previous_artifacts,
        );
        let current_inputs = vec![
            input("project.toml", "config"),
            input("src/A.saga", "new-a"),
            input("src/B.saga", "b"),
            input("src/Main.saga", "main"),
        ];
        let current_artifacts = vec![
            artifact("A", "src/A.saga", "new-a", "a-iface"),
            artifact("B", "src/B.saga", "b", "b-iface"),
            artifact("Main", "src/Main.saga", "main", "main-iface"),
        ];

        let (modules, bridges) = partial_work(plan_project_rebuild(
            &build_dir,
            Some(&previous),
            &current_inputs,
            &current_artifacts,
            &imports(&[("A", &["B"]), ("B", &["A"]), ("Main", &["B"])]),
            ProjectRebuildOptions {
                stdlib_fingerprint: "stdlib",
                profile: "dev",
                dependency_fingerprints: &[],
                custom_main: false,
            },
        ));

        assert_eq!(modules, HashSet::from(["A".to_string(), "B".to_string()]));
        assert!(bridges.is_empty());
        let _ = fs::remove_dir_all(build_dir);
    }

    #[test]
    fn project_rebuild_plan_compiles_changed_bridges_without_full_rebuild() {
        let build_dir = test_root("changed-bridge");
        let previous_artifacts = vec![artifact("Main", "src/Main.saga", "main", "main-iface")];
        write_artifacts(&build_dir, &previous_artifacts);
        let previous = manifest(
            vec![
                input("project.toml", "config"),
                input("src/Main.saga", "main"),
                input("src/native.erl", "old-native"),
            ],
            previous_artifacts,
        );
        let current_inputs = vec![
            input("project.toml", "config"),
            input("src/Main.saga", "main"),
            input("src/native.erl", "new-native"),
        ];
        let current_artifacts = vec![artifact("Main", "src/Main.saga", "main", "main-iface")];

        let (modules, bridges) = partial_work(plan_project_rebuild(
            &build_dir,
            Some(&previous),
            &current_inputs,
            &current_artifacts,
            &imports(&[("Main", &[])]),
            ProjectRebuildOptions {
                stdlib_fingerprint: "stdlib",
                profile: "dev",
                dependency_fingerprints: &[],
                custom_main: false,
            },
        ));

        assert!(modules.is_empty());
        assert_eq!(bridges, vec!["src/native.erl".to_string()]);
        let _ = fs::remove_dir_all(build_dir);
    }

    #[test]
    fn project_rebuild_plan_falls_back_to_full_for_profile_mismatch() {
        let build_dir = test_root("profile-mismatch");
        let previous_artifacts = vec![artifact("Main", "src/Main.saga", "main", "main-iface")];
        write_artifacts(&build_dir, &previous_artifacts);
        let mut previous = manifest(
            vec![
                input("project.toml", "config"),
                input("src/Main.saga", "main"),
            ],
            previous_artifacts,
        );
        previous.profile = "release".to_string();
        let current_inputs = vec![
            input("project.toml", "config"),
            input("src/Main.saga", "main"),
        ];
        let current_artifacts = vec![artifact("Main", "src/Main.saga", "main", "main-iface")];

        assert!(matches!(
            plan_project_rebuild(
                &build_dir,
                Some(&previous),
                &current_inputs,
                &current_artifacts,
                &imports(&[("Main", &[])]),
                ProjectRebuildOptions {
                    stdlib_fingerprint: "stdlib",
                    profile: "dev",
                    dependency_fingerprints: &[],
                    custom_main: false,
                },
            ),
            ProjectRebuildPlan::Full
        ));
        let _ = fs::remove_dir_all(build_dir);
    }

    #[test]
    fn project_rebuild_plan_falls_back_to_full_for_dependency_changes() {
        let build_dir = test_root("dependency-change");
        let previous_artifacts = vec![artifact("Main", "src/Main.saga", "main", "main-iface")];
        write_artifacts(&build_dir, &previous_artifacts);
        let mut previous = manifest(
            vec![
                input("project.toml", "config"),
                input("src/Main.saga", "main"),
            ],
            previous_artifacts,
        );
        previous.dependency_fingerprints = vec![super::super::cache::BuildDependencyFingerprint {
            id: "path:dep:deps/dep".to_string(),
            name: "dep".to_string(),
            kind: "path".to_string(),
            fingerprint: "old".to_string(),
        }];
        let current_inputs = vec![
            input("project.toml", "config"),
            input("src/Main.saga", "main"),
        ];
        let current_artifacts = vec![artifact("Main", "src/Main.saga", "main", "main-iface")];
        let current_deps = vec![super::super::cache::BuildDependencyFingerprint {
            id: "path:dep:deps/dep".to_string(),
            name: "dep".to_string(),
            kind: "path".to_string(),
            fingerprint: "new".to_string(),
        }];

        assert!(matches!(
            plan_project_rebuild(
                &build_dir,
                Some(&previous),
                &current_inputs,
                &current_artifacts,
                &imports(&[("Main", &[])]),
                ProjectRebuildOptions {
                    stdlib_fingerprint: "stdlib",
                    profile: "dev",
                    dependency_fingerprints: &current_deps,
                    custom_main: false,
                },
            ),
            ProjectRebuildPlan::Full
        ));
        let _ = fs::remove_dir_all(build_dir);
    }

    #[test]
    fn project_rebuild_plan_falls_back_to_full_when_module_set_changes() {
        let build_dir = test_root("module-set-change");
        let previous_artifacts = vec![
            artifact("OldName", "src/Renamed.saga", "old", "old-iface"),
            artifact("Main", "src/Main.saga", "main", "main-iface"),
        ];
        write_artifacts(&build_dir, &previous_artifacts);
        let previous = manifest(
            vec![
                input("project.toml", "config"),
                input("src/Renamed.saga", "old"),
                input("src/Main.saga", "main"),
            ],
            previous_artifacts,
        );
        let current_inputs = vec![
            input("project.toml", "config"),
            input("src/Renamed.saga", "new"),
            input("src/Main.saga", "main"),
        ];
        let current_artifacts = vec![
            artifact("NewName", "src/Renamed.saga", "new", "new-iface"),
            artifact("Main", "src/Main.saga", "main", "main-iface"),
        ];

        assert!(matches!(
            plan_project_rebuild(
                &build_dir,
                Some(&previous),
                &current_inputs,
                &current_artifacts,
                &imports(&[("NewName", &[]), ("Main", &["NewName"])]),
                ProjectRebuildOptions {
                    stdlib_fingerprint: "stdlib",
                    profile: "dev",
                    dependency_fingerprints: &[],
                    custom_main: false,
                },
            ),
            ProjectRebuildPlan::Full
        ));
        let _ = fs::remove_dir_all(build_dir);
    }

    #[test]
    fn project_rebuild_plan_falls_back_to_full_for_unexpected_beams() {
        let build_dir = test_root("unexpected-beam");
        let previous_artifacts = vec![artifact("Main", "src/Main.saga", "main", "main-iface")];
        write_artifacts(&build_dir, &previous_artifacts);
        fs::write(build_dir.join("old_module.beam"), "").unwrap();
        let previous = manifest(
            vec![
                input("project.toml", "config"),
                input("src/Main.saga", "main"),
            ],
            previous_artifacts,
        );
        let current_inputs = vec![
            input("project.toml", "config"),
            input("src/Main.saga", "main"),
        ];
        let current_artifacts = vec![artifact("Main", "src/Main.saga", "main", "main-iface")];

        assert!(matches!(
            plan_project_rebuild(
                &build_dir,
                Some(&previous),
                &current_inputs,
                &current_artifacts,
                &imports(&[("Main", &[])]),
                ProjectRebuildOptions {
                    stdlib_fingerprint: "stdlib",
                    profile: "dev",
                    dependency_fingerprints: &[],
                    custom_main: false,
                },
            ),
            ProjectRebuildPlan::Full
        ));
        let _ = fs::remove_dir_all(build_dir);
    }

    #[test]
    fn project_rebuild_plan_falls_back_to_full_for_added_inputs() {
        let build_dir = test_root("added-input");
        let previous_artifacts = vec![artifact("Main", "src/Main.saga", "main", "main-iface")];
        write_artifacts(&build_dir, &previous_artifacts);
        let previous = manifest(
            vec![
                input("project.toml", "config"),
                input("src/Main.saga", "main"),
            ],
            previous_artifacts,
        );
        let current_inputs = vec![
            input("project.toml", "config"),
            input("src/Main.saga", "main"),
            input("src/New.saga", "new"),
        ];
        let current_artifacts = vec![artifact("Main", "src/Main.saga", "main", "main-iface")];

        assert!(matches!(
            plan_project_rebuild(
                &build_dir,
                Some(&previous),
                &current_inputs,
                &current_artifacts,
                &imports(&[("Main", &[])]),
                ProjectRebuildOptions {
                    stdlib_fingerprint: "stdlib",
                    profile: "dev",
                    dependency_fingerprints: &[],
                    custom_main: false,
                },
            ),
            ProjectRebuildPlan::Full
        ));
        let _ = fs::remove_dir_all(build_dir);
    }
}
