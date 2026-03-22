mod cli;

use std::env;

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
    eprintln!("  dylang install          Fetch and cache git dependencies");
}

fn main() {
    let args: Vec<String> = env::args().collect();

    match args.get(1).map(|s| s.as_str()) {
        Some("run") => cli::commands::cmd_run(&args[2..]),
        Some("build") => cli::commands::cmd_build(&args[2..]),
        Some("check") => cli::commands::cmd_check(args.get(2).map(|s| s.as_str())),
        Some("test") => cli::commands::cmd_test(&args[2..]),
        Some("install") => cli::commands::cmd_install(),
        Some("emit") => match args.get(2).map(|s| s.as_str()) {
            Some(file) => cli::commands::cmd_emit(file),
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
