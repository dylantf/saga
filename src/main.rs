use dylang::{ast, codegen, derive, elaborate, lexer, parser, token, typechecker};
use serde::Deserialize;

use std::env;
use std::fs;
use std::path::PathBuf;

fn byte_offset_to_line_col(source: &str, offset: usize) -> (usize, usize) {
    let mut line = 1;
    let mut col = 1;
    for (i, ch) in source.char_indices() {
        if i >= offset {
            break;
        }
        if ch == '\n' {
            line += 1;
            col = 1;
        } else {
            col += 1;
        }
    }
    (line, col)
}

/// Get the source line at a 1-based line number.
fn get_source_line(source: &str, line_num: usize) -> Option<&str> {
    source.lines().nth(line_num - 1)
}

/// Print a diagnostic (error or warning) with source context and underline.
fn print_diagnostic(source: &str, source_path: &str, label: &str, span: Option<token::Span>, message: &str) {
    let (start_line, start_col) = if let Some(span) = span {
        byte_offset_to_line_col(source, span.start)
    } else {
        (1, 1)
    };
    let end_col = if let Some(span) = span {
        byte_offset_to_line_col(source, span.end).1
    } else {
        start_col + 1
    };

    eprintln!(
        "{} at {}:{}:{}: {}",
        label, source_path, start_line, start_col, message
    );

    if let Some(line_text) = get_source_line(source, start_line) {
        let line_num_width = start_line.to_string().len();
        eprintln!("  {} | {}", start_line, line_text);
        let underline_len = if end_col > start_col {
            end_col - start_col
        } else {
            1
        };
        eprintln!(
            "  {} | {}{}",
            " ".repeat(line_num_width),
            " ".repeat(start_col - 1),
            "^".repeat(underline_len)
        );
    }
}

fn print_tc_diagnostic(source: &str, source_path: &str, d: &typechecker::Diagnostic) {
    let label = match d.severity {
        typechecker::Severity::Error => "Type error",
        typechecker::Severity::Warning => "Warning",
    };
    print_diagnostic(source, source_path, label, d.span, &d.message);
}

/// Parsed project.toml configuration.
#[derive(Debug, Deserialize, Default)]
struct ProjectConfig {
    #[serde(default)]
    project: ProjectSection,
}

#[derive(Debug, Deserialize, Default)]
#[allow(dead_code)]
struct ProjectSection {
    #[serde(default)]
    name: Option<String>,
    #[serde(default)]
    tests_dir: Option<String>,
}

impl ProjectConfig {
    fn load(project_root: &std::path::Path) -> Self {
        let path = project_root.join("project.toml");
        match fs::read_to_string(&path) {
            Ok(contents) => toml::from_str(&contents).unwrap_or_else(|e| {
                eprintln!("Warning: failed to parse project.toml: {}", e);
                ProjectConfig::default()
            }),
            Err(_) => ProjectConfig::default(),
        }
    }

    fn tests_dir(&self) -> &str {
        self.project.tests_dir.as_deref().unwrap_or("tests")
    }
}

fn print_usage() {
    eprintln!("Usage:");
    eprintln!("  dylang run              Build and run project (requires project.toml)");
    eprintln!("  dylang run <file.dy>    Build and run a single file");
    eprintln!("  dylang run --release    Run existing release build");
    eprintln!("  dylang build            Build project to _build/dev/");
    eprintln!("  dylang build <file.dy>  Build a single file to _build/dev/");
    eprintln!("  dylang build --release  Build project to _build/release/");
    eprintln!("  dylang check            Typecheck project without building");
    eprintln!("  dylang check <file.dy>  Typecheck a single file");
    eprintln!("  dylang emit <file.dy>   Print generated Core Erlang to stdout");
    eprintln!("  dylang test             Run tests (requires project.toml)");
    eprintln!("  dylang test <pattern>   Run tests matching pattern");
}

fn parse_and_typecheck(
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
    let mut program = match parser::Parser::new(tokens).parse_program() {
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

fn make_checker(project_root: Option<PathBuf>) -> typechecker::Checker {
    typechecker::Checker::with_prelude(project_root).unwrap_or_else(|e| {
        eprintln!("Prelude type error: {}", e);
        std::process::exit(1);
    })
}

/// Compile all Std.* modules referenced in codegen_info into the build directory.
/// Lower an elaborated module to Core Erlang and write it to the build directory.
fn emit_module(
    module_name: &str,
    elaborated: &ast::Program,
    codegen_info: &std::collections::HashMap<String, typechecker::ModuleCodegenInfo>,
    elaborated_modules: &std::collections::HashMap<String, ast::Program>,
    build_dir: &std::path::Path,
) {
    let erlang_name = module_name.to_lowercase().replace('.', "_");
    let core_src =
        codegen::emit_module_with_imports(&erlang_name, elaborated, codegen_info, elaborated_modules);
    let core_path = build_dir.join(format!("{}.core", erlang_name));
    fs::write(&core_path, &core_src).unwrap_or_else(|e| {
        eprintln!("Error writing {}: {}", core_path.display(), e);
        std::process::exit(1);
    });
}

/// Typecheck and elaborate Std modules. Returns their elaborated programs.
fn compile_std_modules(
    result: &typechecker::CheckResult,
) -> std::collections::HashMap<String, ast::Program> {
    let mut elaborated_modules = std::collections::HashMap::new();

    for (module_name, mod_result) in result.module_check_results() {
        if !module_name.starts_with("Std.") {
            continue;
        }
        let program = match result.programs().get(module_name) {
            Some(p) => p,
            None => continue,
        };
        let elaborated = elaborate::elaborate_module(program, mod_result, module_name);
        elaborated_modules.insert(module_name.clone(), elaborated);
    }

    elaborated_modules
}

/// Compile all .core files in a directory with erlc.
fn run_erlc_file(core_file: &std::path::Path, build_dir: &std::path::Path) {
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

fn run_erlc(build_dir: &std::path::Path) {
    let core_files: Vec<_> = fs::read_dir(build_dir)
        .unwrap()
        .filter_map(|e| e.ok())
        .filter(|e| e.path().extension().is_some_and(|ext| ext == "core"))
        .map(|e| e.path())
        .collect();

    for core_file in &core_files {
        run_erlc_file(core_file, build_dir);
    }

    eprintln!(
        "Built {} module(s) in {}",
        core_files.len(),
        build_dir.display()
    );
}

/// Run a compiled module on the BEAM.
fn exec_erl(build_dir: &std::path::Path, entry_module: &str) {
    let eval = format!(
        "try '{}':main() of _ -> init:stop() catch C:R:S -> io:format(\"~p: ~p~n~p~n\", [C,R,S]), init:stop(1) end",
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

// --- Build functions ---

/// Build a project (with project.toml) into the given build directory.
/// Returns the build directory path, elaborated modules, and codegen info.
fn build_project(
    profile: &str,
) -> (
    PathBuf,
    std::collections::HashMap<String, ast::Program>,
    std::collections::HashMap<String, typechecker::ModuleCodegenInfo>,
) {
    let project_root = find_project_root().unwrap_or_else(|| {
        eprintln!("No project.toml found. Use `dylang build <file.dy>` for single files.");
        std::process::exit(1);
    });

    let main_path = project_root.join("Main.dy");
    let main_source = fs::read_to_string(&main_path).unwrap_or_else(|e| {
        eprintln!("Error reading Main.dy: {}", e);
        std::process::exit(1);
    });

    // Phase 1: Typecheck
    let mut checker = make_checker(Some(project_root.clone()));
    let (main_program, _) = parse_and_typecheck(&main_source, "Main.dy", &mut checker);
    let result = checker.to_result();

    let build_dir = project_root.join("_build").join(profile);
    let _ = fs::remove_dir_all(&build_dir);
    fs::create_dir_all(&build_dir).unwrap_or_else(|e| {
        eprintln!("Error creating build dir: {}", e);
        std::process::exit(1);
    });

    // Phase 2: Elaborate all modules
    let mut elaborated_modules = compile_std_modules(&result);

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
        elaborated_modules.insert(module_name.clone(), elaborated);
    }

    // Elaborate Main
    let main_elaborated = elaborate::elaborate_module(&main_program, &result, "Main");
    elaborated_modules.insert("Main".to_string(), main_elaborated);

    // Phase 3: Lower and emit all modules
    for (module_name, elaborated) in &elaborated_modules {
        let erlang_name = if module_name == "Main" {
            "main".to_string()
        } else {
            module_name.to_lowercase().replace('.', "_")
        };
        emit_module(
            &erlang_name,
            elaborated,
            result.codegen_info(),
            &elaborated_modules,
            &build_dir,
        );
    }

    run_erlc(&build_dir);
    let codegen_info = result.codegen_info().clone();
    (build_dir, elaborated_modules, codegen_info)
}

/// Build a single script file into the given build directory.
/// Returns the build directory path.
fn build_script(file: &str, profile: &str) -> PathBuf {
    let source = fs::read_to_string(file).unwrap_or_else(|e| {
        eprintln!("Error reading {}: {}", file, e);
        std::process::exit(1);
    });
    let mut checker = make_checker(None);
    let (program, _) = parse_and_typecheck(&source, file, &mut checker);
    let result = checker.to_result();

    let build_dir = std::path::Path::new(file)
        .parent()
        .unwrap_or(std::path::Path::new("."))
        .join("_build")
        .join(profile);
    let _ = fs::remove_dir_all(&build_dir);
    fs::create_dir_all(&build_dir).unwrap_or_else(|e| {
        eprintln!("Error creating build dir: {}", e);
        std::process::exit(1);
    });

    // Phase 2: Elaborate all modules
    let mut elaborated_modules = compile_std_modules(&result);
    let elaborated = elaborate::elaborate(&program, &result);
    elaborated_modules.insert("_script".to_string(), elaborated);

    // Phase 3: Emit all modules
    for (module_name, elaborated) in &elaborated_modules {
        let erlang_name = module_name.to_lowercase().replace('.', "_");
        emit_module(
            &erlang_name,
            elaborated,
            result.codegen_info(),
            &elaborated_modules,
            &build_dir,
        );
    }

    run_erlc(&build_dir);
    build_dir
}

/// Get the build directory for a script without building.
fn script_build_dir(file: &str, profile: &str) -> PathBuf {
    std::path::Path::new(file)
        .parent()
        .unwrap_or(std::path::Path::new("."))
        .join("_build")
        .join(profile)
}

// --- Commands ---

fn cmd_run(args: &[String]) {
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
            let project_root = find_project_root().unwrap_or_else(|| {
                eprintln!("No project.toml found.");
                std::process::exit(1);
            });
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
            let (build_dir, _, _) = build_project("dev");
            exec_erl(&build_dir, "main");
        }
    }
}

fn cmd_build(args: &[String]) {
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

fn cmd_check(file: Option<&str>) {
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
            let project_root = find_project_root().unwrap_or_else(|| {
                eprintln!("No project.toml found. Run with a filename to check a single file.");
                std::process::exit(1);
            });
            let main_path = project_root.join("Main.dy");
            let source = fs::read_to_string(&main_path).unwrap_or_else(|e| {
                eprintln!("Error reading Main.dy: {}", e);
                std::process::exit(1);
            });
            let mut checker = make_checker(Some(project_root));
            let _ = parse_and_typecheck(&source, "Main.dy", &mut checker);
            eprintln!("OK");
        }
    }
}

fn cmd_emit(file: &str) {
    let source = fs::read_to_string(file).unwrap_or_else(|e| {
        eprintln!("Error reading {}: {}", file, e);
        std::process::exit(1);
    });
    let mut checker = make_checker(None);
    let (program, result) = parse_and_typecheck(&source, file, &mut checker);

    let elaborated = elaborate::elaborate(&program, &result);
    let elaborated_modules = std::collections::HashMap::new();
    let core_src = codegen::emit_module_with_imports(
        "_script",
        &elaborated,
        result.codegen_info(),
        &elaborated_modules,
    );
    print!("{}", core_src);
}

fn cmd_test(_args: &[String]) {
    let project_root = find_project_root().unwrap_or_else(|| {
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
    let test_files: Vec<PathBuf> = discover_test_files(&tests_dir);
    if test_files.is_empty() {
        eprintln!("No test files found in {}", tests_dir.display());
        std::process::exit(1);
    }

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

        let (program, _) = parse_and_typecheck(&source, &source_path, &mut checker);
        let result = checker.to_result();

        // Compile any std modules the test file needs that weren't in the project build
        let test_std_modules = compile_std_modules(&result);
        let mut all_modules = elaborated_modules.clone();
        let mut all_codegen = codegen_info.clone();
        all_codegen.extend(result.codegen_info().clone());
        for (name, elab) in &test_std_modules {
            if !all_modules.contains_key(name) {
                let erlang_name = name.to_lowercase().replace('.', "_");
                emit_module(&erlang_name, elab, &all_codegen, &test_std_modules, &build_dir);
                run_erlc_file(&build_dir.join(format!("{}.core", erlang_name)), &build_dir);
                all_modules.insert(name.clone(), elab.clone());
            }
        }

        // Elaborate only the test file
        let elaborated = elaborate::elaborate(&program, &result);
        all_modules.insert("_test".to_string(), elaborated.clone());

        // Emit only the test module
        let core_src = codegen::emit_module_with_imports(
            "_test",
            &elaborated,
            &all_codegen,
            &all_modules,
        );
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
/// non-import declarations in `main () = Std.Test.run (fun () -> { ... })`.
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
    let mut has_test_import = false;

    for line in source.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("import ") || trimmed.starts_with("module ") {
            if trimmed.contains("Std.Test") {
                has_test_import = true;
            }
            imports.push(line.to_string());
        } else {
            body.push(line.to_string());
        }
    }

    let mut result = String::new();

    // Auto-import Std.Test.run if not already imported
    if !has_test_import {
        result.push_str("import Std.Test (run)\n");
    } else {
        // Ensure run is available even if user imported specific items
        result.push_str("import Std.Test (run)\n");
    }

    for line in &imports {
        result.push_str(line);
        result.push('\n');
    }

    result.push_str("\nmain () = run (fun () -> {\n");
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

/// Walk up from cwd looking for project.toml.
fn find_project_root() -> Option<PathBuf> {
    let mut dir = env::current_dir().ok()?;
    loop {
        if dir.join("project.toml").exists() {
            return Some(dir);
        }
        if !dir.pop() {
            return None;
        }
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();

    match args.get(1).map(|s| s.as_str()) {
        Some("run") => cmd_run(&args[2..]),
        Some("build") => cmd_build(&args[2..]),
        Some("check") => cmd_check(args.get(2).map(|s| s.as_str())),
        Some("test") => cmd_test(&args[2..]),
        Some("emit") => match args.get(2).map(|s| s.as_str()) {
            Some(file) => cmd_emit(file),
            None => {
                eprintln!("Usage: dylang emit <file.dy>");
                std::process::exit(1);
            }
        },
        _ => {
            print_usage();
            std::process::exit(1);
        }
    }
}
