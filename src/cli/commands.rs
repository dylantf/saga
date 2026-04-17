use saga::{codegen, elaborate, project_config, project_config::ProjectConfig, typechecker};

use std::fs;
use std::path::PathBuf;
use std::time::Duration;

use super::build::*;
use super::color;

fn test_timeout() -> Duration {
    let secs = std::env::var("DYLANG_TEST_TIMEOUT_SECS")
        .ok()
        .and_then(|s| s.parse::<u64>().ok())
        .filter(|&s| s > 0)
        .unwrap_or(30);
    Duration::from_secs(secs)
}

pub fn cmd_run(file: Option<&str>, release: bool) {
    if release {
        // --release: use cached build if still valid, otherwise rebuild
        if let Some(f) = file {
            let sb = check_script_cache(f, "release").unwrap_or_else(|| build_script(f, "release"));
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
            let (build_dir, stdlib_dir) = check_project_cache(&project_root, "release")
                .unwrap_or_else(|| {
                    let pb = build_project("release");
                    (pb.build_dir, pb.stdlib_dir)
                });
            exec_erl(&build_dir, &stdlib_dir, &extra_dirs, "main");
        }
    } else {
        // dev: always clean rebuild
        if let Some(f) = file {
            let sb = build_script(f, "dev");
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
            let pb = build_project("dev");
            exec_erl(&pb.build_dir, &pb.stdlib_dir, &pb.extra_ebin_dirs, "main");
        }
    }
}

pub fn cmd_build(file: Option<&str>, release: bool) {
    let profile = if release { "release" } else { "dev" };

    if let Some(f) = file {
        let _sb = build_script(f, profile);
    } else {
        let _pb = build_project(profile);
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

pub fn cmd_emit(file: &str) {
    let source = fs::read_to_string(file).unwrap_or_else(|e| {
        eprintln!("Error reading {}: {}", file, e);
        std::process::exit(1);
    });
    let mut checker = make_checker(None);
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
    let core_src = codegen::emit_module_with_context(
        &erlang_name,
        &elaborated,
        &ctx,
        &result,
        Some(&source_file),
        Some("main"),
    );
    print!("{}", core_src);
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

pub fn cmd_test(filter: Option<&str>) {
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
    let pb = build_project_ext(
        "test",
        std::slice::from_ref(&tests_dir),
        Some(("_test_entry.saga", &entry_source)),
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
