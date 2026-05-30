mod cli;

use clap::{Parser, Subcommand};

#[derive(Parser)]
#[command(name = "saga", about = "The saga compiler", version)]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Build and run a project or single file
    Run {
        /// A .saga source file (omit for project mode)
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
        /// A .saga source file (omit for project mode)
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
        /// A .saga source file (omit for project mode)
        file: Option<String>,
    },
    /// Print generated Core Erlang to stdout
    Emit {
        /// The .saga source file
        file: String,
    },
    /// Dump an intermediate IR stage for a single .saga file (new-path debugging)
    Inspect {
        /// The .saga source file
        file: String,
        /// Stage to dump: elaborated | anf | monadic | monadic-opt | monadic-stats | core
        #[arg(long)]
        stage: String,
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
        /// The .saga source file to format
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
    /// Generate markdown documentation for a project's public API
    ///
    /// Default (no `--dir`): runs in the current project. Requires a
    /// `project.toml` with a `[library]` section, and documents the modules
    /// listed in `expose`.
    ///
    /// With `--dir <path>`: documents every `.saga` module found under that
    /// directory, ignoring any project.toml. Used to render the stdlib's
    /// own docs, or any directory of modules outside a project.
    ///
    /// Output: one `<ModuleName>.md` per module plus an `index.md` linking
    /// them with one-line summaries pulled from each module's doc comment.
    Docs {
        /// Output directory (default: _build/docs/)
        #[arg(long, short)]
        output: Option<String>,
        /// Document every module under this directory instead of the current
        /// project's exposed modules. No project.toml is required.
        #[arg(long)]
        dir: Option<String>,
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
        Command::Inspect { file, stage } => {
            cli::commands::cmd_inspect(&file, &stage);
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
        Command::Docs { output, dir } => {
            cli::commands::cmd_docs(output.as_deref(), dir.as_deref());
        }
    }
}
