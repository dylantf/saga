use dylang::{ast, codegen, elaborate, eval, lexer, parser, typechecker};

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

fn print_usage() {
    eprintln!("Usage:");
    eprintln!("  dylang run              Run project (requires project.toml, runs Main.main)");
    eprintln!("  dylang run <file.dy>    Run a single file (no module resolution)");
    eprintln!("  dylang check            Typecheck project without running");
    eprintln!("  dylang check <file.dy>  Typecheck a single file");
    eprintln!("  dylang build            Build project (not yet implemented)");
    eprintln!("  dylang emit <file.dy>   Print generated Core Erlang to stdout");
}

fn parse_and_typecheck(
    source: &str,
    source_path: &str,
    checker: &mut typechecker::Checker,
) -> ast::Program {
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
    let program = match parser::Parser::new(tokens).parse_program() {
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
    if let Err(e) = checker.check_program(&program) {
        if let Some(span) = e.span {
            let (line, col) = byte_offset_to_line_col(source, span.start);
            eprintln!("Type error at {}:{}:{}: {}", source_path, line, col, e);
        } else {
            eprintln!("Type error: {}", e);
        }
        std::process::exit(1);
    }
    program
}

fn make_checker(project_root: Option<PathBuf>) -> typechecker::Checker {
    let mut checker = match project_root {
        Some(root) => typechecker::Checker::with_project_root(root),
        None => typechecker::Checker::new(),
    };
    let prelude_src = include_str!("prelude/prelude.dy");
    let prelude_tokens = lexer::Lexer::new(prelude_src)
        .lex()
        .expect("prelude lex error");
    let prelude_program = parser::Parser::new(prelude_tokens)
        .parse_program()
        .expect("prelude parse error");
    if let Err(e) = checker.check_program(&prelude_program) {
        eprintln!("Prelude type error: {}", e);
        std::process::exit(1);
    }
    checker
}

fn run_program(program: &ast::Program, loader: &eval::ModuleLoader) {
    match eval::eval_program(program, loader) {
        eval::EvalResult::Ok(_) => {}
        eval::EvalResult::Error(err) => {
            eprintln!("Runtime error: {}", err.message);
            std::process::exit(1);
        }
        eval::EvalResult::Effect { name, .. } => {
            eprintln!("Unhandled effect: {}", name);
            std::process::exit(1);
        }
    }
}

fn cmd_run_script(file: &str) {
    let source = fs::read_to_string(file).unwrap_or_else(|e| {
        eprintln!("Error reading {}: {}", file, e);
        std::process::exit(1);
    });
    let mut checker = make_checker(None);
    let program = parse_and_typecheck(&source, file, &mut checker);
    let loader = eval::ModuleLoader::script();
    run_program(&program, &loader);
}

fn cmd_run_project() {
    let project_root = find_project_root().unwrap_or_else(|| {
        eprintln!("No project.toml found. Run with a filename to use script mode.");
        std::process::exit(1);
    });

    let main_path = project_root.join("Main.dy");
    let source = fs::read_to_string(&main_path).unwrap_or_else(|e| {
        eprintln!("Error reading Main.dy: {}", e);
        std::process::exit(1);
    });

    let mut checker = make_checker(Some(project_root.clone()));
    let program = parse_and_typecheck(&source, "Main.dy", &mut checker);
    let loader = eval::ModuleLoader::project(project_root);
    run_program(&program, &loader);
}

fn cmd_build(file: &str) {
    let source = fs::read_to_string(file).unwrap_or_else(|e| {
        eprintln!("Error reading {}: {}", file, e);
        std::process::exit(1);
    });
    let mut checker = make_checker(None);
    let program = parse_and_typecheck(&source, file, &mut checker);

    // Derive module name from filename (e.g. "01-hello-world.dy" -> "hello_world")
    let raw_stem = std::path::Path::new(file)
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("main");
    // Sanitize: replace hyphens with underscores, strip leading digits/underscores
    let sanitized: String = raw_stem.replace('-', "_");
    let module_name = sanitized.trim_start_matches(|c: char| c.is_ascii_digit() || c == '_');

    let elaborated = elaborate::elaborate(&program, &checker);
    let core_src = codegen::emit_module(module_name, &elaborated);

    let build_dir = std::path::Path::new(file)
        .parent()
        .unwrap_or(std::path::Path::new("."))
        .join("_build");
    fs::create_dir_all(&build_dir).unwrap_or_else(|e| {
        eprintln!("Error creating _build dir: {}", e);
        std::process::exit(1);
    });

    let core_path = build_dir.join(format!("{}.core", module_name));
    fs::write(&core_path, &core_src).unwrap_or_else(|e| {
        eprintln!("Error writing {}: {}", core_path.display(), e);
        std::process::exit(1);
    });

    // Invoke erlc to compile to .beam, outputting into _build/
    let status = std::process::Command::new("erlc")
        .arg("-o")
        .arg(&build_dir)
        .arg(&core_path)
        .status()
        .unwrap_or_else(|e| {
            eprintln!("Failed to run erlc: {}", e);
            std::process::exit(1);
        });

    if !status.success() {
        eprintln!("erlc failed");
        std::process::exit(1);
    }

    eprintln!("Built {}/{}.beam", build_dir.display(), module_name);
    eprintln!(
        "Run with: erl -noshell -pa {} -s {} main -s init stop",
        build_dir.display(),
        module_name
    );
}

fn cmd_emit(file: &str) {
    let source = fs::read_to_string(file).unwrap_or_else(|e| {
        eprintln!("Error reading {}: {}", file, e);
        std::process::exit(1);
    });
    let mut checker = make_checker(None);
    let program = parse_and_typecheck(&source, file, &mut checker);

    let raw_stem = std::path::Path::new(file)
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("main");
    let sanitized: String = raw_stem.replace('-', "_");
    let module_name = sanitized.trim_start_matches(|c: char| c.is_ascii_digit() || c == '_');

    let elaborated = elaborate::elaborate(&program, &checker);
    let core_src = codegen::emit_module(module_name, &elaborated);
    print!("{}", core_src);
}

fn cmd_check(file: Option<&str>) {
    match file {
        Some(f) => {
            let source = fs::read_to_string(f).unwrap_or_else(|e| {
                eprintln!("Error reading {}: {}", f, e);
                std::process::exit(1);
            });
            let mut checker = make_checker(None);
            parse_and_typecheck(&source, f, &mut checker);
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
            parse_and_typecheck(&source, "Main.dy", &mut checker);
            eprintln!("OK");
        }
    }
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
        Some("run") => match args.get(2).map(|s| s.as_str()) {
            Some(file) => cmd_run_script(file),
            None => cmd_run_project(),
        },
        Some("check") => match args.get(2).map(|s| s.as_str()) {
            Some(file) => cmd_check(Some(file)),
            None => cmd_check(None),
        },
        Some("build") => match args.get(2).map(|s| s.as_str()) {
            Some(file) => cmd_build(file),
            None => {
                eprintln!("Usage: dylang build <file.dy>");
                std::process::exit(1);
            }
        },
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
