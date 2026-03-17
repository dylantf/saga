use dylang::{ast, codegen, derive, elaborate, lexer, parser, token, typechecker};

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
/// Elaborate, lower, and write a module's Core Erlang to the build directory.
/// Also updates handler bodies in codegen_info so cross-module named handlers
/// have elaborated (ForeignCall) AST nodes.
fn elaborate_and_emit(
    module_name: &str,
    program: &ast::Program,
    result: &typechecker::CheckResult,
    codegen_info: &mut std::collections::HashMap<String, typechecker::ModuleCodegenInfo>,
    build_dir: &std::path::Path,
) {
    let elaborated = elaborate::elaborate_module(program, result, module_name);
    if let Some(info) = codegen_info.get_mut(module_name) {
        info.update_handler_bodies(&elaborated);
    }
    let erlang_name = module_name.to_lowercase().replace('.', "_");
    let core_src = codegen::emit_module_with_imports(&erlang_name, &elaborated, codegen_info);
    let core_path = build_dir.join(format!("{}.core", erlang_name));
    fs::write(&core_path, &core_src).unwrap_or_else(|e| {
        eprintln!("Error writing {}: {}", core_path.display(), e);
        std::process::exit(1);
    });
}

fn compile_std_modules(checker: &mut typechecker::Checker, build_dir: &std::path::Path) {
    let std_modules: Vec<String> = checker
        .modules.codegen_info
        .keys()
        .filter(|name| name.starts_with("Std."))
        .cloned()
        .collect();

    for module_name in &std_modules {
        let module_path: Vec<String> = module_name.split('.').map(String::from).collect();

        let mut program = if let Some(cached) = checker.modules.programs.get(module_name) {
            cached.clone()
        } else {
            let source = typechecker::builtin_module_source(&module_path)
                .expect("Std module missing from embedded sources");
            let tokens = lexer::Lexer::new(source).lex().unwrap_or_else(|e| {
                eprintln!("Std module {} lex error: {:?}", module_name, e);
                std::process::exit(1);
            });
            parser::Parser::new(tokens)
                .parse_program()
                .unwrap_or_else(|e| {
                    eprintln!("Std module {} parse error: {:?}", module_name, e);
                    std::process::exit(1);
                })
        };
        derive::expand_derives(&mut program);

        let mut mod_checker = checker.seeded_module_checker(None, true);
        let mod_result = mod_checker.check_program(&program);
        if mod_result.has_errors() {
            for e in mod_result.errors() {
                eprintln!("Std module {} type error: {}", module_name, e);
            }
            std::process::exit(1);
        }

        elaborate_and_emit(
            module_name,
            &program,
            &mod_result,
            &mut checker.modules.codegen_info,
            build_dir,
        );
    }
}

/// Compile all .core files in a directory with erlc.
fn run_erlc(build_dir: &std::path::Path) {
    let core_files: Vec<_> = fs::read_dir(build_dir)
        .unwrap()
        .filter_map(|e| e.ok())
        .filter(|e| e.path().extension().is_some_and(|ext| ext == "core"))
        .map(|e| e.path())
        .collect();

    for core_file in &core_files {
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
/// Returns the build directory path.
fn build_project(profile: &str) -> PathBuf {
    let project_root = find_project_root().unwrap_or_else(|| {
        eprintln!("No project.toml found. Use `dylang build <file.dy>` for single files.");
        std::process::exit(1);
    });

    let main_path = project_root.join("Main.dy");
    let main_source = fs::read_to_string(&main_path).unwrap_or_else(|e| {
        eprintln!("Error reading Main.dy: {}", e);
        std::process::exit(1);
    });

    let mut checker = make_checker(Some(project_root.clone()));
    let (main_program, _) = parse_and_typecheck(&main_source, "Main.dy", &mut checker);

    let build_dir = project_root.join("_build").join(profile);
    // Clean and recreate build dir to remove stale artifacts
    let _ = fs::remove_dir_all(&build_dir);
    fs::create_dir_all(&build_dir).unwrap_or_else(|e| {
        eprintln!("Error creating build dir: {}", e);
        std::process::exit(1);
    });

    compile_std_modules(&mut checker, &build_dir);

    // Compile each imported user module
    let module_names: Vec<String> = checker
        .modules.codegen_info
        .keys()
        .filter(|name| !name.starts_with("Std."))
        .cloned()
        .collect();

    for module_name in &module_names {
        let mut program = if let Some(cached) = checker.modules.programs.get(module_name) {
            cached.clone()
        } else {
            let file_path = checker
                .modules.map
                .as_ref()
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

        elaborate_and_emit(
            module_name,
            &program,
            &mod_result,
            &mut checker.modules.codegen_info,
            &build_dir,
        );
    }

    // Compile Main module
    let main_result = checker.to_result();
    let elaborated = elaborate::elaborate_module(&main_program, &main_result, "Main");
    if let Some(info) = checker.modules.codegen_info.get_mut("Main") {
        info.update_handler_bodies(&elaborated)
    }
    let core_src = codegen::emit_module_with_imports("main", &elaborated, &checker.modules.codegen_info);
    let core_path = build_dir.join("main.core");
    fs::write(&core_path, &core_src).unwrap_or_else(|e| {
        eprintln!("Error writing {}: {}", core_path.display(), e);
        std::process::exit(1);
    });

    run_erlc(&build_dir);
    build_dir
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

    let build_dir = std::path::Path::new(file)
        .parent()
        .unwrap_or(std::path::Path::new("."))
        .join("_build")
        .join(profile);
    // Clean and recreate build dir to remove stale artifacts
    let _ = fs::remove_dir_all(&build_dir);
    fs::create_dir_all(&build_dir).unwrap_or_else(|e| {
        eprintln!("Error creating build dir: {}", e);
        std::process::exit(1);
    });

    // Compile Std modules first so handler bodies are elaborated
    // before the script references them
    compile_std_modules(&mut checker, &build_dir);

    // Script doesn't export handlers, so we can elaborate without updating codegen_info
    let result = checker.to_result();
    let elaborated = elaborate::elaborate(&program, &result);
    let core_src =
        codegen::emit_module_with_imports("_script", &elaborated, &result.modules.codegen_info);
    let core_path = build_dir.join("_script.core");
    fs::write(&core_path, &core_src).unwrap_or_else(|e| {
        eprintln!("Error writing {}: {}", core_path.display(), e);
        std::process::exit(1);
    });
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
            let build_dir = build_project("dev");
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
    let core_src =
        codegen::emit_module_with_imports("_script", &elaborated, &result.modules.codegen_info);
    print!("{}", core_src);
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
