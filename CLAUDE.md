# CLAUDE.md

This file provides guidance to Claude Code when working with code in this repository.

## What is this?

A functional programming language (ML/Elm-inspired) with algebraic effects and handlers, compiling to Core Erlang (BEAM). Implemented in Rust.

## Build & Test Commands

```bash
cargo build                    # Build compiler
cargo build-lsp                # Build LSP server (alias in .cargo/config.toml)
cargo test                     # Run all Rust tests
cargo test -p dylang parser    # Run parser tests
cargo test -p dylang typechecker  # Run typechecker tests
cargo test -p dylang codegen   # Run codegen tests
cargo test --test codegen_integration  # Integration tests
cargo clippy                   # Lint

cargo run --bin dylang -- run file.dy       # Compile and run a .dy file on BEAM
cargo run --bin dylang -- build file.dy     # Compile without running
cargo run --bin dylang -- check file.dy     # Type check only
cargo run --bin dylang -- emit file.dy      # Print Core Erlang to stdout
cargo run --bin dylang -- test              # Run project test suite (tests/*.dy)
```

Requires `erlc` and `erl` on PATH (Erlang/OTP) for `run`/`build`/`test` commands.

## Architecture

### Compiler Pipeline

```
Source (.dy) -> Lexer -> Parser -> AST -> Derive Expansion -> Typechecker -> Elaboration -> Normalization -> Lowering -> Core Erlang (.core) -> erlc -> BEAM (.beam) -> erl
```

Key phases:

1. **Parse**: Hand-written Pratt parser produces AST
2. **Derive expansion**: Generates trait impls from `deriving` clauses
3. **Typecheck**: HM-style inference with traits, effects, and exhaustiveness checking
4. **Elaborate**: Transforms trait method calls into explicit dictionary passing
5. **Lower**: Converts to Core Erlang IR with CPS transform for effect handlers. BEAM-native effects (e.g. Actor, Supervisor) skip CPS transformation and directly call foreign code, wrapped in Effect syntax
6. **Emit**: Pretty-prints Core Erlang, invokes `erlc`, runs via `erl -noshell`

### Source Layout

- `src/lexer.rs` - Tokenizer
- `src/parser/` - Pratt parser (mod.rs=core, decl.rs=declarations, expr.rs=expressions, pat.rs=patterns)
- `src/ast.rs` - AST node types
- `src/typechecker/` - Type inference and checking (~15 files, largest subsystem)
  - `mod.rs` - Core types: Type, Scheme, Substitution, TypeEnv, Checker
  - `infer.rs` - Expression inference
  - `check_decl.rs` - Declaration checking
  - `check_module.rs` - Multi-module checking with module map
  - `unify.rs` - Unification algorithm
  - `effects.rs`, `handlers.rs`, `patterns.rs`, `records.rs`, `check_traits.rs`, `exhaustiveness.rs` - Specialized subsystems
- `src/elaborate.rs` - Dictionary passing transform
- `src/derive.rs` - Trait deriving (Show, Debug, Eq, Ord, Enum)
- `src/codegen/` - Core Erlang emission
  - `cerl.rs` - Core Erlang AST and pretty-printer
  - `normalize.rs` - Effect normalization pre-pass
  - `lower/` - Main lowering (exprs.rs, effects.rs, builtins.rs, pats.rs, init.rs, util.rs)
- `src/lsp/` - Language server (hover, completion, diagnostics, go-to-def, etc.)
- `src/stdlib/` - Standard library (.dy files); `prelude.dy` is auto-loaded
- `examples/` - Example programs, sort of doubles as E2E testing but purpose is for structured examples of features

### Module System

Files declare `module Foo.Bar` and are imported with `import Foo.Bar`. Projects use `project.toml` to mark root. The compiler scans all `.dy` files to build a module map, then resolves imports by declared module name (not file path).

### Testing Patterns

Typechecker tests use `check(src)` which loads the prelude then checks the source. Codegen tests use `emit(src)` (lowering only, no typechecking) and `emit_full(src)` (full pipeline). To test codegen changes end-to-end, build and run via `cargo run -- run` rather than the Rust interpreter.

### Build Output

- Single files: `<parent>/_build/{dev,release}/`
- Projects: `<project_root>/_build/{dev,release}/`

## Code Conventions

- Never use `3.14` as a float literal in tests (clippy warning); use `std::f64::consts::PI` or simple values like `1.5`
- Run `cargo clippy` when finishing tasks
- Language docs live in `docs/`; `docs/roadmap.md` is the source of truth for project status
