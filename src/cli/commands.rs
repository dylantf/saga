use saga::{
    codegen, compiler_options::CompileOptions, elaborate, project_config,
    project_config::ProjectConfig, typechecker,
};

use std::fs;
use std::path::PathBuf;
use std::time::Duration;

use super::build::*;
use super::color;

fn test_timeout() -> Duration {
    let secs = std::env::var("SAGA_TEST_TIMEOUT_SECS")
        .ok()
        .and_then(|s| s.parse::<u64>().ok())
        .filter(|&s| s > 0)
        .unwrap_or(30);
    Duration::from_secs(secs)
}

pub fn cmd_run(file: Option<&str>, release: bool, options: &CompileOptions) {
    if release {
        // --release: use cached build if still valid, otherwise rebuild
        if let Some(f) = file {
            let sb = if options.diagnostics.monadic_stats.is_enabled() {
                build_script_with_options(f, "release", options)
            } else {
                check_script_cache(f, "release").unwrap_or_else(|| build_script(f, "release"))
            };
            exec_erl(&sb.build_dir, &sb.stdlib_dir, &[], &sb.erlang_name);
        } else {
            let project_root = super::find_project_root().unwrap_or_else(|| {
                eprintln!("No project.toml found.");
                std::process::exit(1);
            });
            let config = ProjectConfig::load(&project_root);
            if !config.is_bin() {
                eprintln!("This project is a library and cannot be run. Use `saga build` instead.");
                std::process::exit(1);
            }
            let extra_dirs = project_config::extra_ebin_dirs(&project_root, config.deps.as_ref());
            let (build_dir, stdlib_dir) = if options.diagnostics.monadic_stats.is_enabled() {
                let pb = build_project_with_options("release", options);
                (pb.build_dir, pb.stdlib_dir)
            } else {
                check_project_cache(&project_root, "release").unwrap_or_else(|| {
                    let pb = build_project("release");
                    (pb.build_dir, pb.stdlib_dir)
                })
            };
            exec_erl(&build_dir, &stdlib_dir, &extra_dirs, "main");
        }
    } else {
        // dev: always clean rebuild
        if let Some(f) = file {
            let sb = build_script_with_options(f, "dev", options);
            exec_erl(&sb.build_dir, &sb.stdlib_dir, &[], &sb.erlang_name);
        } else {
            let project_root = super::find_project_root().unwrap_or_else(|| {
                eprintln!("No project.toml found.");
                std::process::exit(1);
            });
            let config = ProjectConfig::load(&project_root);
            if !config.is_bin() {
                eprintln!("This project is a library and cannot be run. Use `saga build` instead.");
                std::process::exit(1);
            }
            let pb = build_project_with_options("dev", options);
            exec_erl(&pb.build_dir, &pb.stdlib_dir, &pb.extra_ebin_dirs, "main");
        }
    }
}

pub fn cmd_build(file: Option<&str>, release: bool, options: &CompileOptions) {
    let profile = if release { "release" } else { "dev" };

    if let Some(f) = file {
        let _sb = build_script_with_options(f, profile, options);
    } else {
        let _pb = build_project_with_options(profile, options);
    }
}

pub fn cmd_check(file: Option<&str>) {
    match file {
        Some(f) => {
            let source = fs::read_to_string(f).unwrap_or_else(|e| {
                eprintln!("Error reading {}: {}", f, e);
                std::process::exit(1);
            });
            let mut checker = make_checker(None);
            let (_, result) = parse_and_typecheck(&source, f, &mut checker);
            let warning_count = result.warnings().len();
            if warning_count > 0 {
                eprintln!(
                    "{}",
                    color::yellow(&format!("OK with {} warning(s)", warning_count))
                );
            } else {
                eprintln!("{}", color::green("OK"));
            }
        }
        None => {
            let project_root = super::find_project_root().unwrap_or_else(|| {
                eprintln!("No project.toml found. Run with a filename to check a single file.");
                std::process::exit(1);
            });
            let config = ProjectConfig::load(&project_root);
            if let Err(e) = config.validate() {
                eprintln!("Error in project.toml: {}", e);
                std::process::exit(1);
            }
            let mut checker = make_checker(Some(project_root.clone()));
            if let Some(deps) = &config.deps
                && let Err(e) =
                    saga::project_config::resolve_deps(&mut checker, &project_root, deps)
            {
                eprintln!("Error resolving dependencies: {}", e);
                std::process::exit(1);
            }
            if config.is_bin() {
                let main_file = config.main_file();
                let main_path = project_root.join(main_file);
                let source = fs::read_to_string(&main_path).unwrap_or_else(|e| {
                    eprintln!("Error reading {}: {}", main_file, e);
                    std::process::exit(1);
                });
                parse_and_typecheck(&source, main_file, &mut checker);
            } else if let Some(lib) = &config.library {
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
            let result = checker.to_result();
            let warning_count = result.warnings().len();
            if warning_count > 0 {
                eprintln!(
                    "{}",
                    color::yellow(&format!("OK with {} warning(s)", warning_count))
                );
            } else {
                eprintln!("{}", color::green("OK"));
            }
        }
    }
}

pub fn cmd_new(name: &str, lib: bool) {
    let dir = std::path::PathBuf::from(name);
    if dir.exists() {
        eprintln!("Error: directory '{}' already exists", name);
        std::process::exit(1);
    }

    fs::create_dir_all(&dir).unwrap_or_else(|e| {
        eprintln!("Error creating directory: {}", e);
        std::process::exit(1);
    });

    // Convert project name to PascalCase module name (e.g. "my-project" -> "MyProject")
    let module_name: String = name
        .split(['-', '_'])
        .map(|word| {
            let mut chars = word.chars();
            match chars.next() {
                Some(c) => c.to_uppercase().to_string() + chars.as_str(),
                None => String::new(),
            }
        })
        .collect();

    // Write .gitignore
    fs::write(
        dir.join(".gitignore"),
        "_build/\ndeps/\n.DS_Store\nerl_crash.dump",
    )
    .unwrap();

    let src_dir = dir.join("src");
    fs::create_dir_all(&src_dir).unwrap_or_else(|e| {
        eprintln!("Error creating src directory: {}", e);
        std::process::exit(1);
    });

    if lib {
        let project_toml = format!(
            r#"[project]
name = "{name}"

[library]
module = "{module_name}"
expose = []

# [bin]
# main = "src/Main.saga"

# [deps]
# saga_pgo = {{ git = "https://github.com/dylantf/saga_pgo" }}
"#
        );
        fs::write(dir.join("project.toml"), project_toml).unwrap();
        fs::write(
            src_dir.join(format!("{module_name}.saga")),
            format!("module {module_name}\n"),
        )
        .unwrap();
    } else {
        let project_toml = format!(
            r#"[project]
name = "{name}"

[bin]
main = "src/Main.saga"

# [library]
# module = "{module_name}"
# expose = []

# [deps]
# some-lib = {{ path = "../some-lib" }}
"#
        );
        fs::write(dir.join("project.toml"), project_toml).unwrap();
        fs::write(
            src_dir.join("Main.saga"),
            "module Main\n\nimport Std.IO (console)\n\nmain () = {\n  println \"Hello, world!\"\n} with console\n",
        )
        .unwrap();
    }

    // Initialize git repo
    let _ = std::process::Command::new("git")
        .arg("init")
        .arg(&dir)
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status();

    eprintln!(
        "  {} {} project '{}'",
        super::color::green("Created"),
        if lib { "library" } else { "binary" },
        name
    );
}

pub fn cmd_install() {
    let project_root = super::find_project_root().unwrap_or_else(|| {
        eprintln!("No project.toml found.");
        std::process::exit(1);
    });

    if let Err(e) = saga::project_config::install_deps(&project_root) {
        eprintln!("Error: {}", e);
        std::process::exit(1);
    }
}

pub fn cmd_emit(file: &str, options: &CompileOptions) {
    let source = fs::read_to_string(file).unwrap_or_else(|e| {
        eprintln!("Error reading {}: {}", file, e);
        std::process::exit(1);
    });
    let project_root = super::find_project_root();
    let mut checker = make_checker(project_root.clone());
    if let Some(root) = &project_root {
        let config = ProjectConfig::load(root);
        if let Err(e) = config.validate() {
            eprintln!("Error in project.toml: {}", e);
            std::process::exit(1);
        }
        if let Some(deps) = &config.deps
            && let Err(e) = saga::project_config::resolve_deps(&mut checker, root, deps)
        {
            eprintln!("Error resolving dependencies: {}", e);
            std::process::exit(1);
        }
    }
    let (program, _) = parse_and_typecheck(&source, file, &mut checker);
    let result = checker.to_result();

    let module_name = declared_module_name(&program).unwrap_or_else(|| "_script".to_string());
    let erlang_name = module_name.to_lowercase().replace('.', "_");

    // Full pipeline: compile Std modules + elaborate user code
    let mut compiled_modules = compile_std_modules(&result);
    let elaborated = elaborate::elaborate(&program, &result);
    compiled_modules.insert(
        module_name,
        codegen::CompiledModule {
            codegen_info: Default::default(),
            elaborated: elaborated.clone(),
            resolution: codegen::resolve::ResolutionMap::new(),
            front_resolution: result.resolution.clone(),
        },
    );
    let ctx = codegen::CodegenContext {
        modules: compiled_modules,
        let_effect_bindings: result.let_effect_bindings.clone(),
        prelude_imports: result.prelude_imports.clone(),
    };
    let source_file = codegen::SourceFile {
        path: file.to_string(),
        source: source.clone(),
    };
    let output = codegen::emit_module_with_context_options(
        &erlang_name,
        &elaborated,
        &ctx,
        &result,
        Some(&source_file),
        Some("main"),
        options,
    );
    print!("{}", output.core_src);
}

/// Dump an intermediate IR stage for a single `.saga` file.
///
/// Bypasses the codegen toggle for `anf` / `monadic` / `monadic-opt` /
/// `monadic-stats` / `selective-core`: those
/// always run the new path (uniform-effect-translation), regardless of the
/// active `emit_module_with_context` block. `elaborated` and `core` go through
/// shared code and therefore observe the toggle.
pub fn cmd_inspect(file: &str, stage: &str) {
    use saga::codegen::monadic;

    let source = fs::read_to_string(file).unwrap_or_else(|e| {
        eprintln!("Error reading {}: {}", file, e);
        std::process::exit(1);
    });
    let project_root = super::find_project_root();
    let mut checker = make_checker(project_root.clone());
    if let Some(root) = &project_root {
        let config = ProjectConfig::load(root);
        if let Err(e) = config.validate() {
            eprintln!("Error in project.toml: {}", e);
            std::process::exit(1);
        }
        if let Some(deps) = &config.deps
            && let Err(e) = saga::project_config::resolve_deps(&mut checker, root, deps)
        {
            eprintln!("Error resolving dependencies: {}", e);
            std::process::exit(1);
        }
    }
    let (program, _) = parse_and_typecheck(&source, file, &mut checker);
    let result = checker.to_result();

    let elaborated = elaborate::elaborate(&program, &result);

    match stage {
        "elaborated" => {
            println!("{:#?}", elaborated);
        }
        "anf" => {
            let anf_program = codegen::anf::normalize(elaborated, None);
            println!("{:#?}", anf_program);
        }
        "monadic" | "monadic-opt" | "monadic-stats" | "selective-core" => {
            // Build a minimal CodegenContext (std modules + this user module)
            // so resolve/effect-info match what the new path sees in production.
            let module_name =
                declared_module_name(&program).unwrap_or_else(|| "_script".to_string());
            let mut compiled_modules = compile_std_modules(&result);
            for (name, info) in result.codegen_info() {
                if name == &module_name {
                    continue;
                }
                let compiled =
                    codegen::compile_module_from_result(name, &result).unwrap_or_else(|| {
                        codegen::CompiledModule {
                            codegen_info: info.clone(),
                            elaborated: Vec::new(),
                            resolution: codegen::resolve::ResolutionMap::new(),
                            front_resolution: Default::default(),
                        }
                    });
                compiled_modules.entry(name.clone()).or_insert(compiled);
            }
            compiled_modules.insert(
                module_name.clone(),
                codegen::CompiledModule {
                    codegen_info: result
                        .codegen_info()
                        .get(&module_name)
                        .cloned()
                        .unwrap_or_default(),
                    elaborated: elaborated.clone(),
                    resolution: codegen::resolve::ResolutionMap::new(),
                    front_resolution: result.resolution.clone(),
                },
            );
            let ctx = codegen::CodegenContext {
                modules: compiled_modules,
                let_effect_bindings: result.let_effect_bindings.clone(),
                prelude_imports: result.prelude_imports.clone(),
            };

            let codegen_info = ctx.codegen_info();
            let front_resolution = result
                .module_check_results()
                .get(&module_name)
                .map(|m| &m.resolution)
                .unwrap_or(&result.resolution);
            let mut resolution_map = codegen::resolve::resolve_names(
                &module_name,
                &elaborated,
                &codegen_info,
                &ctx.prelude_imports,
                front_resolution,
            );
            for compiled in ctx.modules.values() {
                resolution_map.extend(compiled.resolution.iter().map(|(k, v)| (*k, v.clone())));
            }

            let anf_program = codegen::anf::normalize(elaborated.clone(), Some(&resolution_map));

            let ops_storage = codegen::build_effect_ops_table(&result);
            let mod_check_ref = result
                .module_check_results()
                .get(&module_name)
                .unwrap_or(&result);
            let handler_effects_storage = codegen::build_handler_effects(&result);
            let let_handler_effects_storage = codegen::build_let_handler_effects(&result);
            let effect_info = codegen::build_effect_info(
                &result,
                mod_check_ref,
                &ops_storage,
                &handler_effects_storage,
                &let_handler_effects_storage,
            );

            // Collect imported handler bodies (matches new-path emit behavior).
            let mut imported_handler_decls: std::collections::HashMap<
                String,
                saga::ast::HandlerBody,
            > = std::collections::HashMap::new();
            for compiled in ctx.modules.values() {
                let anf_imported = codegen::anf::normalize(
                    compiled.elaborated.clone(),
                    Some(&compiled.resolution),
                );
                for decl in &anf_imported {
                    if let saga::ast::Decl::HandlerDef { name, body, .. } = decl {
                        imported_handler_decls
                            .entry(name.clone())
                            .or_insert_with(|| body.clone());
                    }
                }
            }

            let (monadic_prog, _handler_value_map) = monadic::translate::translate_with_imports(
                &anf_program,
                &resolution_map,
                &effect_info,
                &imported_handler_decls,
            );

            if stage == "selective-core" {
                let constructor_atoms = codegen::resolve::build_constructor_atoms(
                    &module_name,
                    &elaborated,
                    &codegen_info,
                    &ctx.prelude_imports,
                );
                let cmod = codegen::lower_selective::lower_module(
                    &module_name,
                    &monadic_prog,
                    &resolution_map,
                    &constructor_atoms,
                    &ctx,
                    &effect_info,
                );
                println!("{}", codegen::cerl::print_module(&cmod));
                return;
            }

            if stage == "monadic-stats" {
                let before = monadic::stats::Stats::collect_program(&monadic_prog);
                let before_reachable = monadic::stats::Stats::collect_reachable_program(
                    &monadic_prog,
                    &["main", "tests"],
                );
                let handler_info = codegen::handler_analysis::analyze(&elaborated);
                let after_program =
                    monadic::effect_opt::run(monadic_prog, &handler_info, &effect_info);
                let after = monadic::stats::Stats::collect_program(&after_program);
                let after_reachable = monadic::stats::Stats::collect_reachable_program(
                    &after_program,
                    &["main", "tests"],
                );
                let reachable = (before_reachable.decls > 0 || after_reachable.decls > 0)
                    .then(|| monadic::stats::StatsDiff::new(before_reachable, after_reachable));
                println!(
                    "{}",
                    monadic::stats::StatsReport::new(
                        monadic::stats::StatsDiff::new(before, after),
                        reachable,
                    )
                );
                return;
            }

            let to_print = if stage == "monadic-opt" {
                let handler_info = codegen::handler_analysis::analyze(&elaborated);
                monadic::effect_opt::run(monadic_prog, &handler_info, &effect_info)
            } else {
                monadic_prog
            };

            println!("{}", monadic::print::print_program(&to_print));
        }
        "core" => {
            cmd_emit(file, &CompileOptions::default());
        }
        other => {
            eprintln!(
                "Unknown stage: '{}'. Expected one of: elaborated, anf, monadic, monadic-opt, monadic-stats, selective-core, core",
                other
            );
            std::process::exit(1);
        }
    }
}

pub fn cmd_fmt(file: &str, write_mode: bool, debug_mode: bool, cli_width: Option<usize>) {
    // CLI --width overrides project.toml [formatter] width
    let width = cli_width.unwrap_or_else(|| {
        super::find_project_root()
            .map(|root| ProjectConfig::load(&root).formatter.width)
            .unwrap_or(saga::formatter::DEFAULT_WIDTH)
    });

    let source = fs::read_to_string(file).unwrap_or_else(|e| {
        eprintln!("Error reading {}: {}", file, e);
        std::process::exit(1);
    });
    let tokens = saga::lexer::Lexer::new(&source).lex().unwrap_or_else(|e| {
        eprintln!("Lex error in {}: {:?}", file, e);
        std::process::exit(1);
    });
    let mut parser = saga::parser::Parser::new(tokens);
    let program = parser.parse_program_annotated().unwrap_or_else(|e| {
        eprintln!("Parse error in {}: {} at {:?}", file, e.message, e.span);
        std::process::exit(1);
    });

    if debug_mode {
        println!("{:#?}", program);
        return;
    }

    let formatted = saga::formatter::format(&program, width);

    if write_mode {
        fs::write(file, &formatted).unwrap_or_else(|e| {
            eprintln!("Error writing {}: {}", file, e);
            std::process::exit(1);
        });
    } else {
        print!("{}", formatted);
    }
}

pub fn cmd_test(filter: Option<&str>, options: &CompileOptions) {
    let project_root = super::find_project_root().unwrap_or_else(|| {
        eprintln!("No project.toml found. Tests require a project.");
        std::process::exit(1);
    });

    let config = ProjectConfig::load(&project_root);
    let tests_dir = project_root.join(config.tests_dir());

    if !tests_dir.exists() {
        eprintln!("No tests directory found at {}", tests_dir.display());
        std::process::exit(1);
    }

    // Discover test files
    let all_test_files: Vec<PathBuf> = discover_test_files(&tests_dir);
    if all_test_files.is_empty() {
        eprintln!("No test files found in {}", tests_dir.display());
        std::process::exit(1);
    }

    // Filter test files if a pattern argument was provided
    let test_files: Vec<PathBuf> = if let Some(pattern) = filter {
        let pattern_path = PathBuf::from(pattern);

        // If it's an exact file path (absolute or relative), use it directly
        if pattern_path.is_file() {
            vec![pattern_path.canonicalize().unwrap_or(pattern_path)]
        } else {
            // Try resolving relative to the tests directory
            let in_tests_dir = tests_dir.join(pattern);
            if in_tests_dir.is_file() {
                vec![in_tests_dir]
            } else {
                // Substring match against file names (without extension)
                let matched: Vec<PathBuf> = all_test_files
                    .into_iter()
                    .filter(|f| {
                        let name = f.file_stem().and_then(|s| s.to_str()).unwrap_or("");
                        let rel = f.strip_prefix(&project_root).unwrap_or(f).to_string_lossy();
                        name.contains(pattern) || rel.contains(pattern)
                    })
                    .collect();

                if matched.is_empty() {
                    eprintln!("No test files matching \"{}\"", pattern);
                    std::process::exit(1);
                }
                matched
            }
        }
    } else {
        all_test_files
    };

    let test_module_map = typechecker::scan_source_dir(&tests_dir).unwrap_or_else(|e| {
        eprintln!("Error scanning test files: {}", e);
        std::process::exit(1);
    });

    let test_files: Vec<PathBuf> = test_files
        .iter()
        .map(|path| path.canonicalize().unwrap_or_else(|_| path.clone()))
        .collect();

    let test_modules: Vec<String> = test_files
        .iter()
        .map(|path| {
            test_module_map
                .iter()
                .find_map(|(name, module_path)| {
                    let module_path = module_path
                        .canonicalize()
                        .unwrap_or_else(|_| module_path.clone());
                    if module_path == *path {
                        Some(name.clone())
                    } else {
                        None
                    }
                })
                .unwrap_or_else(|| {
                    let rel = path.strip_prefix(&project_root).unwrap_or(path);
                    eprintln!(
                        "Test file '{}' must declare a module to be used with `saga test`",
                        rel.display()
                    );
                    std::process::exit(1);
                })
        })
        .collect();

    let entry_source = generate_test_entry_source(&test_modules);
    let pb = build_project_ext_with_options(
        "test",
        std::slice::from_ref(&tests_dir),
        Some(("_test_entry.saga", &entry_source)),
        options,
    );

    exec_erl_with_timeout(
        &pb.build_dir,
        &pb.stdlib_dir,
        &pb.extra_ebin_dirs,
        "main",
        Some(test_timeout()),
    );
}

fn generate_test_entry_source(test_modules: &[String]) -> String {
    let mut source = String::new();
    source.push_str("import Std.Test (run_modules)\n");
    for module_name in test_modules {
        source.push_str(&format!("import {}\n", module_name));
    }
    source.push_str("\nmain () = run_modules [\n");
    for (idx, module_name) in test_modules.iter().enumerate() {
        let comma = if idx + 1 < test_modules.len() {
            ","
        } else {
            ""
        };
        source.push_str(&format!(
            "  (\"{}\", {}.tests){}\n",
            module_name, module_name, comma
        ));
    }
    source.push_str("]\n");
    source
}

fn discover_test_files(dir: &std::path::Path) -> Vec<PathBuf> {
    let mut files = Vec::new();
    if let Ok(entries) = fs::read_dir(dir) {
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                files.extend(discover_test_files(&path));
            } else if path.extension().is_some_and(|ext| ext == "saga") {
                files.push(path);
            }
        }
    }
    files.sort();
    files
}

pub fn cmd_docs(output: Option<&str>, dir: Option<&str>) {
    let output_dir = output
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("_build/docs"));

    let modules: Vec<super::docs::DocModule> = match dir {
        Some(dir_str) => {
            let dir_path = PathBuf::from(dir_str);
            if !dir_path.is_dir() {
                eprintln!("Error: --dir path '{}' is not a directory", dir_str);
                std::process::exit(1);
            }
            let map = typechecker::scan_source_dir(&dir_path).unwrap_or_else(|e| {
                eprintln!("Error scanning {}: {}", dir_path.display(), e);
                std::process::exit(1);
            });
            map.into_iter()
                .map(|(name, path)| super::docs::DocModule { name, path })
                .collect()
        }
        None => {
            let project_root = super::find_project_root().unwrap_or_else(|| {
                eprintln!(
                    "No project.toml found. Use `saga docs --dir <path>` to document an arbitrary directory."
                );
                std::process::exit(1);
            });
            let config = ProjectConfig::load(&project_root);
            if let Err(e) = config.validate() {
                eprintln!("Error in project.toml: {}", e);
                std::process::exit(1);
            }
            let lib = config.library.as_ref().unwrap_or_else(|| {
                eprintln!(
                    "Project has no [library] section to document. Use `saga docs --dir <path>` to document an arbitrary directory."
                );
                std::process::exit(1);
            });
            let map = typechecker::scan_project_modules(&project_root).unwrap_or_else(|e| {
                eprintln!("Error scanning project: {}", e);
                std::process::exit(1);
            });
            let mut modules = Vec::with_capacity(lib.expose.len());
            for exposed in &lib.expose {
                match map.get(exposed) {
                    Some(path) => modules.push(super::docs::DocModule {
                        name: exposed.clone(),
                        path: path.clone(),
                    }),
                    None => {
                        eprintln!("Error: exposed module '{}' not found in project", exposed);
                        std::process::exit(1);
                    }
                }
            }
            modules
        }
    };

    super::docs::generate_docs(&modules, &output_dir);
}
