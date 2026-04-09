mod cli;

use clap::{Parser, Subcommand};

#[derive(Parser)]
#[command(name = "dylang", about = "The dylang compiler")]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Build and run a project or single file
    Run {
        /// A .dy source file (omit for project mode)
        file: Option<String>,
        /// Use release profile
        #[arg(long)]
        release: bool,
        /// Show full erlc/erl output
        #[arg(short, long)]
        verbose: bool,
    },
    /// Build a project or single file
    Build {
        /// A .dy source file (omit for project mode)
        file: Option<String>,
        /// Use release profile
        #[arg(long)]
        release: bool,
        /// Show full erlc/erl output
        #[arg(short, long)]
        verbose: bool,
    },
    /// Typecheck without building
    Check {
        /// A .dy source file (omit for project mode)
        file: Option<String>,
    },
    /// Print generated Core Erlang to stdout
    Emit {
        /// The .dy source file
        file: String,
    },
    /// Run tests
    Test {
        /// Filter pattern (file path or substring match)
        filter: Option<String>,
        /// Show full erlc/erl output
        #[arg(short, long)]
        verbose: bool,
    },
    /// Create a new project
    New {
        /// Project name (also the directory name)
        name: String,
        /// Create a library project instead of a binary
        #[arg(long)]
        lib: bool,
    },
    /// Fetch and cache git dependencies
    Install,
    /// Format a source file
    Fmt {
        /// The .dy source file to format
        file: String,
        /// Format file in place instead of printing to stdout
        #[arg(long)]
        write: bool,
        /// Print the parsed AST instead of formatting
        #[arg(long)]
        debug: bool,
        /// Line width (overrides project.toml setting)
        #[arg(long)]
        width: Option<usize>,
    },
}

fn main() {
    let cli = Cli::parse();

    match cli.command {
        Command::Run {
            file,
            release,
            verbose,
        } => {
            cli::set_verbose(verbose);
            cli::commands::cmd_run(file.as_deref(), release);
        }
        Command::Build {
            file,
            release,
            verbose,
        } => {
            cli::set_verbose(verbose);
            cli::commands::cmd_build(file.as_deref(), release);
        }
        Command::Check { file } => {
            cli::commands::cmd_check(file.as_deref());
        }
        Command::Emit { file } => {
            cli::commands::cmd_emit(&file);
        }
        Command::Test { filter, verbose } => {
            cli::set_verbose(verbose);
            cli::commands::cmd_test(filter.as_deref());
        }
        Command::New { name, lib } => {
            cli::commands::cmd_new(&name, lib);
        }
        Command::Install => {
            cli::commands::cmd_install();
        }
        Command::Fmt {
            file,
            write,
            debug,
            width,
        } => {
            cli::commands::cmd_fmt(&file, write, debug, width);
        }
    }
}
