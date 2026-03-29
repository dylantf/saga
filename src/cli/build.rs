use dylang::{
    ast, codegen, derive, desugar, elaborate, lexer, parser, project_config, typechecker,
};
use project_config::ProjectConfig;

use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};

use super::diagnostics::{byte_offset_to_line_col, print_tc_diagnostic};

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
    let result = checker.check_program(&program);
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
    build_dir: &Path,
) {
    let erlang_name = module_name.to_lowercase().replace('.', "_");
    let core_src = codegen::emit_module_with_context(&erlang_name, elaborated, ctx);
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
    if count > 0 {
        eprintln!("Copied {} bridge file(s)", count);
    }
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

/// Compile a single .core file with erlc.
pub fn run_erlc_file(core_file: &Path, build_dir: &Path) {
    let status = std::process::Command::new("erlc")
        .arg("-o")
        .arg(build_dir)
        .arg(core_file)
        .status()
        .unwrap_or_else(|e| {
            eprintln!("Failed to run erlc: {}", e);
            std::process::exit(1);
        });

    if !status.success() {
        eprintln!("erlc failed on {}", core_file.display());
        std::process::exit(1);
    }
}

/// Compile all .core and .erl files in a directory with erlc.
pub fn run_erlc(build_dir: &Path) {
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

    eprintln!(
        "Built {} module(s) in {}",
        compilable_files.len(),
        build_dir.display()
    );
}

/// Run a compiled module on the BEAM.
pub fn exec_erl(build_dir: &Path, entry_module: &str) {
    let eval = format!(
        "try '{}':main() of _ -> init:stop() catch error:{{dylang_panic, Msg}} -> io:format(standard_error, \"~ts~n\", [Msg]), init:stop(1); C:R:S -> io:format(\"~p: ~p~n~p~n\", [C,R,S]), init:stop(1) end",
        entry_module
    );
    let status = std::process::Command::new("erl")
        .arg("-noshell")
        .arg("-pa")
        .arg(build_dir)
        .arg("-eval")
        .arg(&eval)
        .status()
        .unwrap_or_else(|e| {
            eprintln!("Failed to run erl: {}", e);
            std::process::exit(1);
        });

    if !status.success() {
        std::process::exit(status.code().unwrap_or(1));
    }
}

/// Build a project (with project.toml) into the given build directory.
/// Returns the build directory path, elaborated modules, and codegen info.
pub fn build_project(profile: &str) -> (PathBuf, HashMap<String, codegen::CompiledModule>) {
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

    // Elaborate user modules
    let user_modules: Vec<String> = result
        .codegen_info()
        .keys()
        .filter(|name| !name.starts_with("Std."))
        .cloned()
        .collect();

    for module_name in &user_modules {
        let mut program = if let Some(cached) = result.programs().get(module_name) {
            cached.clone()
        } else {
            let file_path = result
                .module_map()
                .and_then(|m| m.get(module_name))
                .unwrap_or_else(|| {
                    eprintln!("Module '{}' not found in module map", module_name);
                    std::process::exit(1);
                });
            let source = fs::read_to_string(file_path).unwrap_or_else(|e| {
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
        derive::expand_derives(&mut program);
        desugar::desugar_program(&mut program);

        let mut mod_checker = checker.seeded_module_checker(Some(project_root.clone()), false);
        let mod_result = mod_checker.check_program(&program);
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
        compiled_modules.insert(
            module_name.clone(),
            codegen::CompiledModule {
                codegen_info: result
                    .codegen_info()
                    .get(module_name)
                    .cloned()
                    .unwrap_or_default(),
                elaborated,
                resolution: codegen::resolve::ResolutionMap::new(),
            },
        );
    }

    // Elaborate Main (if this is a bin project)
    if let Some(main_program) = &main_program {
        let main_elaborated = elaborate::elaborate_module(main_program, &result, "Main");
        compiled_modules.insert(
            "Main".to_string(),
            codegen::CompiledModule {
                codegen_info: Default::default(),
                elaborated: main_elaborated,
                resolution: codegen::resolve::ResolutionMap::new(),
            },
        );
    }

    // Phase 3: Lower and emit all modules
    let ctx = codegen::CodegenContext {
        modules: compiled_modules.clone(),
        let_effect_bindings: HashMap::new(),
        prelude_imports: result.prelude_imports.clone(),
    };
    for (module_name, compiled) in &compiled_modules {
        let erlang_name = if module_name == "Main" {
            "main".to_string()
        } else {
            module_name.to_lowercase().replace('.', "_")
        };
        emit_module(&erlang_name, &compiled.elaborated, &ctx, &build_dir);
    }

    // Copy bridge (.erl) files into build dir
    write_stdlib_bridges(&build_dir);
    let mut bridge_roots: Vec<&Path> = vec![&project_root];
    let dep_roots = config
        .deps
        .as_ref()
        .map(|deps| project_config::dep_root_paths(&project_root, deps))
        .unwrap_or_default();
    bridge_roots.extend(dep_roots.iter().map(|p| p.as_path()));
    copy_project_bridges(&bridge_roots, &build_dir);

    run_erlc(&build_dir);
    (build_dir, compiled_modules)
}

/// Build a single script file into the given build directory.
/// Returns the build directory path.
pub fn build_script(file: &str, profile: &str) -> PathBuf {
    let source = fs::read_to_string(file).unwrap_or_else(|e| {
        eprintln!("Error reading {}: {}", file, e);
        std::process::exit(1);
    });
    let mut checker = make_checker(None);
    let (program, _) = parse_and_typecheck(&source, file, &mut checker);
    let result = checker.to_result();

    let build_dir = Path::new(file)
        .parent()
        .unwrap_or(Path::new("."))
        .join("_build")
        .join(profile);
    let _ = fs::remove_dir_all(&build_dir);
    fs::create_dir_all(&build_dir).unwrap_or_else(|e| {
        eprintln!("Error creating build dir: {}", e);
        std::process::exit(1);
    });

    // Phase 2: Elaborate all modules
    let mut compiled_modules = compile_std_modules(&result);
    let elaborated = elaborate::elaborate(&program, &result);
    compiled_modules.insert(
        "_script".to_string(),
        codegen::CompiledModule {
            codegen_info: Default::default(),
            elaborated,
            resolution: codegen::resolve::ResolutionMap::new(),
        },
    );

    // Phase 3: Emit all modules
    let ctx = codegen::CodegenContext {
        modules: compiled_modules.clone(),
        let_effect_bindings: result.let_effect_bindings.clone(),
        prelude_imports: result.prelude_imports.clone(),
    };
    for (module_name, compiled) in &compiled_modules {
        emit_module(module_name, &compiled.elaborated, &ctx, &build_dir);
    }

    // Copy stdlib bridge (.erl) files into build dir
    write_stdlib_bridges(&build_dir);

    run_erlc(&build_dir);
    build_dir
}

/// Get the build directory for a script without building.
pub fn script_build_dir(file: &str, profile: &str) -> PathBuf {
    Path::new(file)
        .parent()
        .unwrap_or(Path::new("."))
        .join("_build")
        .join(profile)
}
