use dylang::{
    ast, codegen, derive, desugar, elaborate, lexer, parser, project_config, token, typechecker,
};
use project_config::ProjectConfig;

use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Instant;

use super::color;
use super::diagnostics::{byte_offset_to_line_col, print_tc_diagnostic};

const BUILD_HASH: &str = env!("DYLANG_BUILD_HASH");
/// Compute stdlib hash at runtime from the embedded sources.
/// This is more reliable than the build-time hash because it always
/// reflects the actual content compiled into the binary.
fn stdlib_hash() -> String {
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

/// Build manifest written to `_build/<profile>/.manifest` for cache invalidation.
#[derive(serde::Serialize, serde::Deserialize)]
struct BuildManifest {
    entry_module: String,
    source_file: String,
    source_mtime: u64,
    compiler_version: String,
}

impl BuildManifest {
    fn path(build_dir: &Path) -> PathBuf {
        build_dir.join(".manifest")
    }

    fn write(&self, build_dir: &Path) {
        let path = Self::path(build_dir);
        let content = toml::to_string(self).expect("failed to serialize manifest");
        fs::write(&path, content).unwrap_or_else(|e| {
            eprintln!("Error writing manifest: {}", e);
        });
    }

    fn read(build_dir: &Path) -> Option<Self> {
        let path = Self::path(build_dir);
        let content = fs::read_to_string(&path).ok()?;
        toml::from_str(&content).ok()
    }
}

fn file_mtime(path: &Path) -> u64 {
    fs::metadata(path)
        .and_then(|m| m.modified())
        .ok()
        .and_then(|t| t.duration_since(std::time::UNIX_EPOCH).ok())
        .map(|d| d.as_secs())
        .unwrap_or(0)
}

/// Check if a cached build is still valid for the given script file.
/// Returns a `ScriptBuild` if the cache is fresh.
pub fn check_script_cache(file: &str, profile: &str) -> Option<ScriptBuild> {
    let build_root = Path::new(file)
        .parent()
        .unwrap_or(Path::new("."))
        .join("_build");
    let build_dir = build_root.join(profile);

    let manifest = BuildManifest::read(&build_dir)?;
    if manifest.compiler_version != BUILD_HASH {
        return None;
    }

    let rel_source = relative_source_path(file);
    if manifest.source_file != rel_source {
        return None;
    }

    let current_mtime = file_mtime(Path::new(file));
    if manifest.source_mtime != current_mtime {
        return None;
    }

    if !build_dir
        .join(format!("{}.beam", manifest.entry_module))
        .exists()
    {
        return None;
    }

    let stdlib_dir = build_root.join(".stdlib").join(stdlib_hash());
    if !stdlib_dir.join(".complete").exists() {
        return None;
    }

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

    let manifest = BuildManifest::read(&build_dir)?;
    if manifest.compiler_version != BUILD_HASH {
        return None;
    }

    // Check if any .dy file or project.toml has been modified
    let current_mtime = max_project_mtime(project_root);
    if manifest.source_mtime != current_mtime {
        return None;
    }

    if !build_dir
        .join(format!("{}.beam", manifest.entry_module))
        .exists()
    {
        return None;
    }

    let build_root = project_root.join("_build");
    let stdlib_dir = build_root.join(".stdlib").join(stdlib_hash());
    if !stdlib_dir.join(".complete").exists() {
        return None;
    }

    Some((build_dir, stdlib_dir))
}

/// Find the maximum mtime across all .dy files and project.toml in a project.
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
        } else if path.extension().is_some_and(|ext| ext == "dy") {
            let mtime = file_mtime(&path);
            if mtime > *max {
                *max = mtime;
            }
        }
    }
}

fn relative_source_path(file: &str) -> String {
    std::env::current_dir()
        .ok()
        .and_then(|cwd| {
            Path::new(file)
                .strip_prefix(&cwd)
                .ok()
                .map(|p| p.to_string_lossy().to_string())
        })
        .unwrap_or_else(|| file.to_string())
}

pub fn parse_and_typecheck(
    source: &str,
    source_path: &str,
    checker: &mut typechecker::Checker,
) -> (ast::Program, typechecker::CheckResult) {
    parse_and_typecheck_inner(source, source_path, checker, false)
}

pub fn parse_and_typecheck_inner(
    source: &str,
    source_path: &str,
    checker: &mut typechecker::Checker,
    test_mode: bool,
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
    parser.test_mode = test_mode;
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
    derive::expand_derives(&mut program);
    desugar::desugar_program(&mut program);
    if test_mode {
        synthesize_test_main(&mut program);
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

/// Lower an elaborated module to Core Erlang and write it to the build directory.
pub fn emit_module(
    module_name: &str,
    elaborated: &ast::Program,
    ctx: &codegen::CodegenContext,
    check_result: Option<&typechecker::CheckResult>,
    build_dir: &Path,
    source_file: Option<&codegen::SourceFile>,
) {
    let erlang_name = module_name.to_lowercase().replace('.', "_");
    let core_src =
        codegen::emit_module_with_context(&erlang_name, elaborated, ctx, check_result, source_file);
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
    let codegen_info = result.codegen_info();
    let prelude_imports = &result.prelude_imports;

    for (module_name, mod_result) in result.module_check_results() {
        if !module_name.starts_with("Std.") {
            continue;
        }
        let program = match result.programs().get(module_name) {
            Some(p) => p,
            None => continue,
        };
        let info = codegen_info.get(module_name).cloned().unwrap_or_default();
        let elaborated = elaborate::elaborate_module(program, mod_result, module_name);
        let normalized = codegen::normalize::normalize_effects(&elaborated);
        let resolution =
            codegen::resolve::resolve_names(&normalized, codegen_info, prelude_imports);
        modules.insert(
            module_name.clone(),
            codegen::CompiledModule {
                codegen_info: info,
                elaborated,
                resolution,
            },
        );
    }

    modules
}

/// Returns embedded stdlib bridge (.erl) files as (filename, source) pairs.
fn stdlib_bridge_files() -> Vec<(&'static str, &'static str)> {
    vec![
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
        ("dylang_runtime.erl", include_str!("../stdlib/runtime.erl")),
        (
            "std_time_bridge.erl",
            include_str!("../stdlib/Time.bridge.erl"),
        ),
        (
            "std_bitstring_bridge.erl",
            include_str!("../stdlib/BitString.bridge.erl"),
        ),
        ("std_io_bridge.erl", include_str!("../stdlib/IO.bridge.erl")),
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

/// Ensure precompiled stdlib beams exist in the project's _build/.stdlib/ directory.
/// Returns the stdlib directory path. On a cold cache, creates a fresh checker,
/// imports ALL builtin modules, elaborates, and compiles them.
pub fn ensure_stdlib_cache(build_root: &Path) -> PathBuf {
    let cache_dir = build_root.join(".stdlib").join(stdlib_hash());

    // If marker exists, cache is warm
    if cache_dir.join(".complete").exists() {
        return cache_dir;
    }

    eprintln!("  {} stdlib...", color::dim("Compiling"));

    let _ = fs::remove_dir_all(&cache_dir);
    fs::create_dir_all(&cache_dir).unwrap_or_else(|e| {
        eprintln!("Error creating stdlib cache dir: {}", e);
        std::process::exit(1);
    });

    // Create a dedicated checker and force-import all builtin modules
    let mut checker = make_checker(None);
    for (module_name, _) in typechecker::BUILTIN_MODULES {
        checker.typecheck_import_by_name(module_name);
    }
    let result = checker.to_result();

    // Elaborate all Std modules
    let compiled_modules = compile_std_modules(&result);

    // Build CodegenContext and emit .core files
    let ctx = codegen::CodegenContext {
        modules: compiled_modules.clone(),
        let_effect_bindings: HashMap::new(),
        prelude_imports: result.prelude_imports.clone(),
    };
    for (module_name, compiled) in &compiled_modules {
        let check_result = result.module_check_results().get(module_name);
        emit_module(
            module_name,
            &compiled.elaborated,
            &ctx,
            check_result,
            &cache_dir,
            None,
        );
    }

    // Write bridge .erl files
    write_stdlib_bridges(&cache_dir);

    // Compile everything with erlc
    let compilable_files: Vec<_> = fs::read_dir(&cache_dir)
        .unwrap()
        .filter_map(|e| e.ok())
        .filter(|e| {
            e.path()
                .extension()
                .is_some_and(|ext| ext == "core" || ext == "erl")
        })
        .map(|e| e.path())
        .collect();

    for file in &compilable_files {
        run_erlc_file(file, &cache_dir);
    }

    // Clean up source files — only keep .beam
    for file in &compilable_files {
        let _ = fs::remove_file(file);
    }

    // Write marker so we know the cache is complete
    fs::write(cache_dir.join(".complete"), "").unwrap_or_else(|e| {
        eprintln!("Error writing stdlib cache marker: {}", e);
        std::process::exit(1);
    });

    cache_dir
}

/// Scan project and dependency directories for .erl bridge files and copy them to the build directory.
fn copy_project_bridges(roots: &[&Path], build_dir: &Path) {
    let mut count = 0;
    for root in roots {
        if let Err(e) = copy_bridges_from_dir(root, build_dir, &mut count) {
            eprintln!(
                "Error scanning for bridge files in {}: {}",
                root.display(),
                e
            );
            std::process::exit(1);
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
            if path
                .file_name()
                .is_some_and(|n| n == "_build" || n == "tests")
            {
                continue;
            }
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

/// Compile a single .core file with erlc, suppressing warnings.
pub fn run_erlc_file(core_file: &Path, build_dir: &Path) {
    let output = std::process::Command::new("erlc")
        .arg("-o")
        .arg(build_dir)
        .arg(core_file)
        .stderr(std::process::Stdio::piped())
        .output()
        .unwrap_or_else(|e| {
            eprintln!("Failed to run erlc: {}", e);
            std::process::exit(1);
        });

    if !output.status.success() {
        // Show erlc stderr only on failure
        let stderr = String::from_utf8_lossy(&output.stderr);
        if !stderr.is_empty() {
            eprintln!("{}", stderr.trim());
        }
        eprintln!("erlc failed on {}", core_file.display());
        std::process::exit(1);
    }
    // Warnings on success are suppressed -- they're either redundant with
    // our own diagnostics or refer to BEAM internals the user can't act on.
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

    for file in &compilable_files {
        run_erlc_file(file, build_dir);
    }

    let elapsed = build_start.elapsed();
    eprintln!(
        "  {} in {:.2}s",
        color::green("Built"),
        elapsed.as_secs_f64()
    );
}

/// Run a compiled module on the BEAM.
pub fn exec_erl(build_dir: &Path, stdlib_dir: &Path, extra_pa: &[PathBuf], entry_module: &str) {
    let eval = format!(
        "try '{}':main() of _ -> init:stop() catch C:R:S -> dylang_runtime:format_crash(C, R, S), init:stop(1) end",
        entry_module
    );
    let mut cmd = std::process::Command::new("erl");
    cmd.arg("-noshell")
        .arg("-pa")
        .arg(stdlib_dir)
        .arg("-pa")
        .arg(build_dir);

    for dir in extra_pa {
        cmd.arg("-pa").arg(dir);
    }

    cmd.arg("-eval").arg(&eval);

    let status = cmd.status().unwrap_or_else(|e| {
        eprintln!("Failed to run erl: {}", e);
        std::process::exit(1);
    });

    if !status.success() {
        std::process::exit(status.code().unwrap_or(1));
    }
}

pub struct ProjectBuild {
    pub build_dir: PathBuf,
    pub stdlib_dir: PathBuf,
    pub compiled_modules: HashMap<String, codegen::CompiledModule>,
    pub extra_ebin_dirs: Vec<PathBuf>,
}

/// Build a project (with project.toml) into the given build directory.
pub fn build_project(profile: &str) -> ProjectBuild {
    let build_start = Instant::now();
    let project_root = super::find_project_root().unwrap_or_else(|| {
        eprintln!("No project.toml found. Use `dylang build <file.dy>` for single files.");
        std::process::exit(1);
    });

    let config = ProjectConfig::load(&project_root);
    if let Err(e) = config.validate() {
        eprintln!("Error in project.toml: {}", e);
        std::process::exit(1);
    }

    let has_bin = config.is_bin();

    // Phase 1: Typecheck
    let mut checker = make_checker(Some(project_root.clone()));

    // Resolve dependencies and merge their modules into the module map
    if let Some(deps) = &config.deps
        && let Err(e) = project_config::resolve_deps(&mut checker, &project_root, deps)
    {
        eprintln!("Error resolving dependencies: {}", e);
        std::process::exit(1);
    }

    // If this project has a binary entry point, typecheck Main
    let main_program = if has_bin {
        let main_file = config.main_file();
        let main_path = project_root.join(main_file);
        let main_source = fs::read_to_string(&main_path).unwrap_or_else(|e| {
            eprintln!("Error reading {}: {}", main_file, e);
            std::process::exit(1);
        });
        let (program, _) = parse_and_typecheck(&main_source, main_file, &mut checker);
        Some(program)
    } else {
        // Library-only: typecheck all exposed modules to trigger the dependency walk
        if let Some(lib) = &config.library {
            let module_map = checker.module_map().cloned().unwrap_or_default();
            for exposed in &lib.expose {
                if module_map.contains_key(exposed) {
                    checker.typecheck_import_by_name(exposed);
                } else {
                    eprintln!("Error: exposed module '{}' not found in project", exposed);
                    std::process::exit(1);
                }
            }
        }
        None
    };

    let result = checker.to_result();

    let build_dir = project_root.join("_build").join(profile);
    let _ = fs::remove_dir_all(&build_dir);
    fs::create_dir_all(&build_dir).unwrap_or_else(|e| {
        eprintln!("Error creating build dir: {}", e);
        std::process::exit(1);
    });

    // Phase 2: Elaborate all modules
    let mut compiled_modules = compile_std_modules(&result);

    // Ensure stdlib beams are cached in _build/
    let build_root = project_root.join("_build");
    let stdlib_dir = ensure_stdlib_cache(&build_root);

    // Elaborate user modules
    let codegen_info_map = result.codegen_info();
    let user_modules: Vec<String> = codegen_info_map
        .keys()
        .filter(|name| !name.starts_with("Std."))
        .cloned()
        .collect();

    let mut source_files: HashMap<String, codegen::SourceFile> = HashMap::new();

    for module_name in &user_modules {
        eprintln!("  {} {}...", color::dim("Compiling"), module_name);

        // Resolve file path for this module (needed for source info and fresh parse)
        let file_path = result
            .module_map()
            .and_then(|m| m.get(module_name))
            .unwrap_or_else(|| {
                eprintln!("Module '{}' not found in module map", module_name);
                std::process::exit(1);
            })
            .clone();

        let mut program = if let Some(cached) = result.programs().get(module_name) {
            cached.clone()
        } else {
            let source = fs::read_to_string(&file_path).unwrap_or_else(|e| {
                eprintln!("Error reading {}: {}", file_path.display(), e);
                std::process::exit(1);
            });
            let tokens = lexer::Lexer::new(&source).lex().unwrap_or_else(|e| {
                eprintln!("Lex error in module {}: {:?}", module_name, e);
                std::process::exit(1);
            });
            parser::Parser::new(tokens)
                .parse_program()
                .unwrap_or_else(|e| {
                    eprintln!("Parse error in module {}: {:?}", module_name, e);
                    std::process::exit(1);
                })
        };

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
        derive::expand_derives(&mut program);
        desugar::desugar_program(&mut program);

        let mut mod_checker = checker.seeded_module_checker(Some(project_root.clone()), false);
        let mod_result = mod_checker.check_program(&mut program);
        for w in mod_result.warnings() {
            eprintln!("Warning in module {}: {}", module_name, w);
        }
        if mod_result.has_errors() {
            for e in mod_result.errors() {
                eprintln!("Type error in module {}: {}", module_name, e);
            }
            std::process::exit(1);
        }

        let elaborated = elaborate::elaborate_module(&program, &mod_result, module_name);
        let normalized = codegen::normalize::normalize_effects(&elaborated);
        let resolution =
            codegen::resolve::resolve_names(&normalized, codegen_info_map, &result.prelude_imports);
        compiled_modules.insert(
            module_name.clone(),
            codegen::CompiledModule {
                codegen_info: codegen_info_map
                    .get(module_name)
                    .cloned()
                    .unwrap_or_default(),
                elaborated,
                resolution,
            },
        );
    }

    // Elaborate Main (if this is a bin project)
    if let Some(main_program) = &main_program {
        eprintln!("  {} Main...", color::dim("Compiling"));
        let main_elaborated = elaborate::elaborate_module(main_program, &result, "Main");
        compiled_modules.insert(
            "Main".to_string(),
            codegen::CompiledModule {
                codegen_info: Default::default(),
                elaborated: main_elaborated,
                resolution: codegen::resolve::ResolutionMap::new(),
            },
        );
        let main_file = config.main_file();
        let main_path = project_root.join(main_file);
        let main_source = fs::read_to_string(&main_path).unwrap_or_default();
        source_files.insert(
            "Main".to_string(),
            codegen::SourceFile {
                path: main_file.to_string(),
                source: main_source,
            },
        );
    }

    // Phase 3: Lower and emit user modules only (stdlib beams are cached globally)
    // user_modules + Main are the modules we need to emit; std modules are in the
    // CodegenContext for cross-module resolution but their beams come from the cache.
    let ctx = codegen::CodegenContext {
        modules: compiled_modules.clone(),
        let_effect_bindings: HashMap::new(),
        prelude_imports: result.prelude_imports.clone(),
    };

    let mut modules_to_emit: Vec<&str> = user_modules.iter().map(|s| s.as_str()).collect();
    if has_bin {
        modules_to_emit.push("Main");
    }

    for module_name in &modules_to_emit {
        let compiled = &compiled_modules[*module_name];
        let erlang_name = if *module_name == "Main" {
            "main".to_string()
        } else {
            module_name.to_lowercase().replace('.', "_")
        };
        let sf = source_files.get(*module_name);
        let check_result = if *module_name == "Main" {
            Some(&result)
        } else {
            result.module_check_results().get(*module_name)
        };
        emit_module(
            &erlang_name,
            &compiled.elaborated,
            &ctx,
            check_result,
            &build_dir,
            sf,
        );
    }

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
    copy_project_bridges(&bridge_roots, &build_dir);

    run_erlc(&build_dir, build_start);

    // Write manifest for cache invalidation
    if has_bin {
        BuildManifest {
            entry_module: "main".to_string(),
            source_file: "project.toml".to_string(),
            source_mtime: max_project_mtime(&project_root),
            compiler_version: BUILD_HASH.to_string(),
        }
        .write(&build_dir);
    }

    let extra_ebin_dirs = project_config::extra_ebin_dirs(&project_root, config.deps.as_ref());

    ProjectBuild {
        build_dir,
        stdlib_dir,
        compiled_modules,
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
    let mut checker = make_checker(None);
    let (program, _) = parse_and_typecheck(&source, file, &mut checker);
    let result = checker.to_result();

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
    let mut compiled_modules = compile_std_modules(&result);

    // Ensure stdlib beams are cached in _build/
    let stdlib_dir = ensure_stdlib_cache(&build_root);

    let elaborated = elaborate::elaborate(&program, &result);
    compiled_modules.insert(
        module_name.clone(),
        codegen::CompiledModule {
            codegen_info: Default::default(),
            elaborated,
            resolution: codegen::resolve::ResolutionMap::new(),
        },
    );

    // Phase 3: Emit only the user module
    let ctx = codegen::CodegenContext {
        modules: compiled_modules.clone(),
        let_effect_bindings: result.let_effect_bindings.clone(),
        prelude_imports: result.prelude_imports.clone(),
    };
    let script_source = codegen::SourceFile {
        path: file.to_string(),
        source: source.clone(),
    };
    emit_module(
        &module_name,
        &compiled_modules[&module_name].elaborated,
        &ctx,
        Some(&result),
        &build_dir,
        Some(&script_source),
    );

    run_erlc(&build_dir, build_start);

    // Write manifest for cache invalidation
    BuildManifest {
        entry_module: erlang_name.clone(),
        source_file: relative_source_path(file),
        source_mtime: file_mtime(Path::new(file)),
        compiler_version: BUILD_HASH.to_string(),
    }
    .write(&build_dir);

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

/// Check if a desugared Let { name: "_" } is a test/describe call.
fn is_test_decl(decl: &ast::Decl) -> bool {
    let ast::Decl::Let { name, value, .. } = decl else {
        return false;
    };
    if name != "_" {
        return false;
    }
    // Walk App chain to find head Var
    let mut e = value;
    loop {
        match &e.kind {
            ast::ExprKind::App { func, .. } => e = func,
            ast::ExprKind::Var { name } => {
                return name == "test" || name == "describe" || name == "skip" || name == "only";
            }
            _ => return false,
        }
    }
}

/// If a test file has no explicit `main`, synthesize one at the AST level.
/// Partitions declarations into top-level (functions, types, etc.) and test
/// expressions, then wraps the test expressions in:
///   main () = run_collected (fun () -> { <test exprs> })
fn synthesize_test_main(program: &mut ast::Program) {
    let has_main = program.iter().any(|d| {
        matches!(d, ast::Decl::FunBinding { name, .. } if name == "main")
            || matches!(d, ast::Decl::FunSignature { name, .. } if name == "main")
    });
    if has_main {
        return;
    }

    let s = token::Span { start: 0, end: 0 };

    let mut top_level = Vec::new();
    let mut test_exprs = Vec::new();

    for decl in std::mem::take(program) {
        if is_test_decl(&decl) {
            if let ast::Decl::Let { value, .. } = decl {
                test_exprs.push(value);
            }
        } else {
            top_level.push(decl);
        }
    }

    if test_exprs.is_empty() {
        *program = top_level;
        return;
    }

    // Auto-import run_collected if not already imported
    let has_run_collected = top_level.iter().any(|d| {
        if let ast::Decl::Import {
            exposing: Some(items),
            ..
        } = d
        {
            items.iter().any(|item| item == "run_collected")
        } else {
            false
        }
    });
    if !has_run_collected {
        top_level.push(ast::Decl::Import {
            id: ast::NodeId::fresh(),
            module_path: vec!["Std".to_string(), "Test".to_string()],
            alias: None,
            exposing: Some(vec!["run_collected".to_string()]),
            span: s,
        });
    }

    // Build: main () = run_collected (fun () -> { <test exprs> })
    let stmts: Vec<ast::Annotated<ast::Stmt>> = test_exprs
        .into_iter()
        .map(|e| ast::Annotated {
            node: ast::Stmt::Expr(e),
            leading_trivia: vec![],
            trailing_comment: None,
            trailing_trivia: vec![],
        })
        .collect();

    let block = ast::Expr::synth(
        s,
        ast::ExprKind::Block {
            stmts,
            dangling_trivia: vec![],
        },
    );

    let lambda = ast::Expr::synth(
        s,
        ast::ExprKind::Lambda {
            params: vec![ast::Pat::Lit {
                id: ast::NodeId::fresh(),
                value: ast::Lit::Unit,
                span: s,
            }],
            body: Box::new(block),
        },
    );

    let run_collected = ast::Expr::synth(
        s,
        ast::ExprKind::Var {
            name: "run_collected".to_string(),
        },
    );

    let body = ast::Expr::synth(
        s,
        ast::ExprKind::App {
            func: Box::new(run_collected),
            arg: Box::new(lambda),
        },
    );

    top_level.push(ast::Decl::FunBinding {
        id: ast::NodeId::fresh(),
        name: "main".to_string(),
        name_span: s,
        params: vec![ast::Pat::Lit {
            id: ast::NodeId::fresh(),
            value: ast::Lit::Unit,
            span: s,
        }],
        guard: None,
        body,
        span: s,
    });

    *program = top_level;
}
