use dylang::{codegen, elaborate, project_config::ProjectConfig};

use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;

use super::build::*;

pub fn cmd_run(args: &[String]) {
    let release = args.contains(&"--release".to_string());
    let file = args.iter().find(|a| a.ends_with(".dy"));

    if release {
        // --release: use existing build if present, build only if missing
        if let Some(f) = file {
            let build_dir = script_build_dir(f, "release");
            if !build_dir.join("_script.beam").exists() {
                build_script(f, "release");
            }
            exec_erl(&build_dir, "_script");
        } else {
            let project_root = super::find_project_root().unwrap_or_else(|| {
                eprintln!("No project.toml found.");
                std::process::exit(1);
            });
            let config = ProjectConfig::load(&project_root);
            if !config.is_bin() {
                eprintln!(
                    "This project is a library and cannot be run. Use `dylang build` instead."
                );
                std::process::exit(1);
            }
            let build_dir = project_root.join("_build").join("release");
            if !build_dir.join("main.beam").exists() {
                build_project("release");
            }
            exec_erl(&build_dir, "main");
        }
    } else {
        // dev: always clean rebuild
        if let Some(f) = file {
            let build_dir = build_script(f, "dev");
            exec_erl(&build_dir, "_script");
        } else {
            let project_root = super::find_project_root().unwrap_or_else(|| {
                eprintln!("No project.toml found.");
                std::process::exit(1);
            });
            let config = ProjectConfig::load(&project_root);
            if !config.is_bin() {
                eprintln!(
                    "This project is a library and cannot be run. Use `dylang build` instead."
                );
                std::process::exit(1);
            }
            let (build_dir, _, _) = build_project("dev");
            exec_erl(&build_dir, "main");
        }
    }
}

pub fn cmd_build(args: &[String]) {
    let profile = if args.contains(&"--release".to_string()) {
        "release"
    } else {
        "dev"
    };

    if let Some(file) = args.iter().find(|a| a.ends_with(".dy")) {
        build_script(file, profile);
    } else {
        build_project(profile);
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
            let _ = parse_and_typecheck(&source, f, &mut checker);
            eprintln!("OK");
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
            let main_file = config.main_file();
            let main_path = project_root.join(main_file);
            let source = fs::read_to_string(&main_path).unwrap_or_else(|e| {
                eprintln!("Error reading {}: {}", main_file, e);
                std::process::exit(1);
            });
            let mut checker = make_checker(Some(project_root.clone()));
            if let Some(deps) = &config.deps
                && let Err(e) =
                    dylang::project_config::resolve_deps(&mut checker, &project_root, deps)
            {
                eprintln!("Error resolving dependencies: {}", e);
                std::process::exit(1);
            }
            let _ = parse_and_typecheck(&source, main_file, &mut checker);
            eprintln!("OK");
        }
    }
}

pub fn cmd_install() {
    let project_root = super::find_project_root().unwrap_or_else(|| {
        eprintln!("No project.toml found.");
        std::process::exit(1);
    });

    if let Err(e) = dylang::project_config::install_deps(&project_root) {
        eprintln!("Error: {}", e);
        std::process::exit(1);
    }
}

pub fn cmd_emit(file: &str) {
    let source = fs::read_to_string(file).unwrap_or_else(|e| {
        eprintln!("Error reading {}: {}", file, e);
        std::process::exit(1);
    });
    let mut checker = make_checker(None);
    let (program, result) = parse_and_typecheck(&source, file, &mut checker);

    let elaborated = elaborate::elaborate(&program, &result);
    let ctx = codegen::CodegenContext {
        codegen_info: result.codegen_info().clone(),
        elaborated_modules: HashMap::new(),
        let_effect_bindings: result.let_effect_bindings.clone(),
        prelude_imports: result.prelude_imports.clone(),
    };
    let core_src = codegen::emit_module_with_context("_script", &elaborated, &ctx);
    print!("{}", core_src);
}

pub fn cmd_fmt(args: &[String]) {
    let write_mode = args.contains(&"--write".to_string());
    let file = args.iter().find(|a| a.ends_with(".dy"));

    let Some(file) = file else {
        eprintln!("Usage: dylang fmt [--write] <file.dy>");
        std::process::exit(1);
    };

    let source = fs::read_to_string(file).unwrap_or_else(|e| {
        eprintln!("Error reading {}: {}", file, e);
        std::process::exit(1);
    });
    let tokens = dylang::lexer::Lexer::new(&source)
        .lex()
        .unwrap_or_else(|e| {
            eprintln!("Lex error in {}: {:?}", file, e);
            std::process::exit(1);
        });
    let mut parser = dylang::parser::Parser::new(tokens);
    let program = parser.parse_program_annotated().unwrap_or_else(|e| {
        eprintln!("Parse error in {}: {} at {:?}", file, e.message, e.span);
        std::process::exit(1);
    });

    let formatted = dylang::formatter::format(&program, 80);

    if write_mode {
        fs::write(file, &formatted).unwrap_or_else(|e| {
            eprintln!("Error writing {}: {}", file, e);
            std::process::exit(1);
        });
    } else {
        print!("{}", formatted);
    }
}

pub fn cmd_test(args: &[String]) {
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
    let filter = args.iter().find(|a| !a.starts_with('-'));
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
                        name.contains(pattern.as_str()) || rel.contains(pattern.as_str())
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

    // Build the main project first (compiles all non-test modules)
    let (build_dir, elaborated_modules, codegen_info) = build_project("test");

    // Build and run each test file, reusing the project's compiled modules.
    for test_file in &test_files {
        let source = fs::read_to_string(test_file).unwrap_or_else(|e| {
            eprintln!("Error reading {}: {}", test_file.display(), e);
            std::process::exit(1);
        });
        let source_path = test_file.to_string_lossy().to_string();

        let mut checker = make_checker(Some(project_root.clone()));

        // If test file has no main, synthesize one:
        // imports stay at top, everything else goes into main () = run (fun () -> { ... })
        let source = inject_test_main(&source);

        let (program, _) = parse_and_typecheck_inner(&source, &source_path, &mut checker, true);
        let result = checker.to_result();

        // Compile any std modules the test file needs that weren't in the project build
        let test_std_modules = compile_std_modules(&result);
        let mut all_modules = elaborated_modules.clone();
        let mut all_codegen = codegen_info.clone();
        all_codegen.extend(result.codegen_info().clone());
        let std_ctx = codegen::CodegenContext {
            codegen_info: all_codegen.clone(),
            elaborated_modules: test_std_modules.clone(),
            let_effect_bindings: HashMap::new(),
            prelude_imports: result.prelude_imports.clone(),
        };
        for (name, elab) in &test_std_modules {
            if !all_modules.contains_key(name) {
                let erlang_name = name.to_lowercase().replace('.', "_");
                emit_module(&erlang_name, elab, &std_ctx, &build_dir);
                run_erlc_file(&build_dir.join(format!("{}.core", erlang_name)), &build_dir);
                all_modules.insert(name.clone(), elab.clone());
            }
        }

        // Elaborate only the test file
        let elaborated = elaborate::elaborate(&program, &result);
        all_modules.insert("_test".to_string(), elaborated.clone());

        // Emit only the test module
        let test_ctx = codegen::CodegenContext {
            codegen_info: all_codegen,
            elaborated_modules: all_modules.clone(),
            let_effect_bindings: result.let_effect_bindings.clone(),
            prelude_imports: result.prelude_imports.clone(),
        };
        let core_src = codegen::emit_module_with_context("_test", &elaborated, &test_ctx);
        let core_path = build_dir.join("_test.core");
        fs::write(&core_path, &core_src).unwrap_or_else(|e| {
            eprintln!("Error writing {}: {}", core_path.display(), e);
            std::process::exit(1);
        });

        run_erlc_file(&core_path, &build_dir);
        exec_erl(&build_dir, "_test");
    }
}

/// If a test file has no `main` function, synthesize one by wrapping all
/// non-import declarations in `main () = run_collected (fun () -> { ... })`.
/// Also auto-imports Std.Test if not already imported.
fn inject_test_main(source: &str) -> String {
    // Check if there's already a main
    if source.lines().any(|line| {
        let trimmed = line.trim();
        trimmed.starts_with("main ")
            || trimmed.starts_with("pub fun main")
            || trimmed.starts_with("fun main")
    }) {
        return source.to_string();
    }

    let mut imports = Vec::new();
    let mut body = Vec::new();

    for line in source.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("import ") || trimmed.starts_with("module ") {
            imports.push(line.to_string());
        } else {
            body.push(line.to_string());
        }
    }

    let mut result = String::new();

    result.push_str("import Std.Test (run_collected)\n");

    for line in &imports {
        result.push_str(line);
        result.push('\n');
    }

    result.push_str("\nmain () = run_collected (fun () -> {\n");
    for line in &body {
        result.push_str(line);
        result.push('\n');
    }
    result.push_str("})\n");

    result
}

fn discover_test_files(dir: &std::path::Path) -> Vec<PathBuf> {
    let mut files = Vec::new();
    if let Ok(entries) = fs::read_dir(dir) {
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                files.extend(discover_test_files(&path));
            } else if path.extension().is_some_and(|ext| ext == "dy") {
                files.push(path);
            }
        }
    }
    files.sort();
    files
}
