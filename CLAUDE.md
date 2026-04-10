# CLAUDE.md

This file provides guidance to Claude Code when working with code in this repository.

## What is this?

A functional programming language (ML/Elm-inspired) with algebraic effects and handlers, compiling to Core Erlang (BEAM). Implemented in Rust.

## Build & Test Commands

```bash
cargo build                    # Build compiler
cargo build-lsp                # Build LSP server (alias in .cargo/config.toml)
cargo test                     # Run all Rust tests
cargo test -p saga parser    # Run parser tests
cargo test -p saga typechecker  # Run typechecker tests
cargo test -p saga codegen   # Run codegen tests
cargo test --test codegen_integration  # Integration tests
cargo clippy                   # Lint

cargo run --bin saga -- run file.saga       # Compile and run a .saga file on BEAM
cargo run --bin saga -- build file.saga     # Compile without running
cargo run --bin saga -- check file.saga     # Type check only
cargo run --bin saga -- emit file.saga      # Print Core Erlang to stdout
cargo run --bin saga -- test              # Run project test suite (tests/*.saga)
cargo run --bin saga -- install           # Fetch and compile Hex/git dependencies
```

Requires `erlc` and `erl` on PATH (Erlang/OTP) for `run`/`build`/`test` commands. Hex packages with NIFs require `rebar3` on PATH.

## Architecture

### Compiler Pipeline

```
Source (.saga) -> Lexer -> Parser -> AST -> Derive Expansion -> Typechecker -> Elaboration -> Normalization -> Lowering -> Core Erlang (.core) -> erlc -> BEAM (.beam) -> erl
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
  - `mod.rs` - Core types (Type, Scheme, Substitution, TypeEnv), Checker struct and sub-structs
  - `infer.rs` - Expression inference dispatch (infer_expr, infer_block, infer_lambda)
  - `check_decl.rs` - Declaration checking and multi-pass registration
  - `check_module.rs` - Multi-module checking, module map, ModuleExports/ModuleCodegenInfo
  - `unify.rs` - Unification, instantiation, generalization, convert_type_expr
  - `builtins.rs` - Built-in type/trait registration
  - `effects.rs` - Effect tracking, lookup, instantiation
  - `handlers.rs` - With-expression and handler arm inference
  - `patterns.rs` - Pattern binding and exhaustiveness checking
  - `records.rs` - Record create/update/field access inference
  - `check_traits.rs` - Trait/impl registration and checking
  - `exhaustiveness.rs` - Maranget usefulness algorithm
  - The Checker struct groups related fields into sub-structs: `lsp: LspState` (type info, references, go-to-def targets), `effect_state: EffectState` (current effects, caches, annotations), `trait_state: TraitState` (definitions, impls, constraints, where bounds)
- `src/elaborate.rs` - Dictionary passing transform
- `src/derive.rs` - Trait deriving (Show, Debug, Eq, Ord, Enum)
- `src/codegen/` - Core Erlang emission
  - `cerl.rs` - Core Erlang AST and pretty-printer
  - `normalize.rs` - Effect normalization pre-pass
  - `lower/` - Main lowering (exprs.rs, effects.rs, builtins.rs, pats.rs, init.rs, util.rs)
- `src/cli/` - CLI entry point (arg parsing, build orchestration, commands)
  - `mod.rs` - Submodule declarations, `find_project_root`
  - `diagnostics.rs` - Error/warning formatting with source underlines
  - `build.rs` - Build pipeline (parse+typecheck, elaborate, emit, erlc/erl invocation)
  - `commands.rs` - Command implementations (run, build, check, emit, test)
- `src/lsp/` - Language server (hover, completion, diagnostics, go-to-def, etc.)
- `src/stdlib/` - Standard library (.saga files); `prelude.saga` is auto-loaded
- `examples/` - Example programs, sort of doubles as E2E testing but purpose is for structured examples of features

### Module System

Files declare `module Foo.Bar` and are imported with `import Foo.Bar`. Projects use `project.toml` to mark root. The compiler scans all `.saga` files to build a module map, then resolves imports by declared module name (not file path).

### Testing Patterns

Typechecker tests use `check(src)` which loads the prelude then checks the source. Codegen tests use `emit(src)` (lowering only, no typechecking) and `emit_full(src)` (full pipeline). To test codegen changes end-to-end, build and run via `cargo run -- run` rather than the Rust interpreter.

### Build Output

- `_build/{dev,release}/` — compiled project beams
- `_build/.stdlib/{fingerprint}/` — precompiled stdlib beams (per-project, keyed by compiler build + embedded stdlib contents)
- `deps/{name}/` — installed dependencies (Hex and git), with `ebin/` and `priv/`
- `~/.saga/cache/` — global download cache (Hex tarballs, git bare clones)

## Language Design Notes

- **There are no zero-argument functions.** Every function takes at least one parameter. If a function has no meaningful input, it takes `Unit`: `fun foo : Unit -> Unit` / `foo () = ...`, called as `foo ()`. Think of `()` as the value that triggers execution. Do NOT add zero-arity cases in the compiler - this is intentional, not a gap. See `docs/const-bindings.md` for the design rationale.

## Code Conventions

- Never use `3.14` as a float literal in tests (clippy warning); use `std::f64::consts::PI` or simple values like `1.5`
- Run `cargo clippy` when finishing tasks
- Language docs live in `docs/`; `docs/roadmap.md` is the source of truth for project status
