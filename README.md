# Saga

A functional programming language with algebraic effects and handlers, compiling to Core Erlang (BEAM). ML-inspired syntax, Hindley-Milner type inference, traits, and pattern matching with exhaustiveness checking.

> **This project is a work in progress.** Saga is under active development and not yet stable. Expect breaking changes, incomplete features, and rough edges. It is not ready for production use. See the [LICENSE](LICENSE) for warranty and liability terms.

Website: [saga-lang.org](https://saga-lang.org)

## Building

Saga is implemented in Rust. To build:

```bash
cargo build                # Debug build
cargo build --release      # Release build
cargo build-lsp            # Build the LSP server (alias for cargo build --bin saga-lsp)
```

### Requirements

- Rust (stable)
- [Erlang/OTP](https://www.erlang.org/) with `erlc` and `erl` on PATH, required for compiling and running Saga programs
- [rebar3](https://rebar3.org/) if using Hex packages with NIFs

## CLI commands

```bash
saga run file.saga         # Compile and run a .saga file on the BEAM
saga build file.saga       # Compile without running
saga check file.saga       # Type check only
saga emit file.saga        # Print generated Core Erlang to stdout
saga test                  # Run project test suite (tests/*.saga)
saga install               # Fetch and compile Hex/git dependencies
saga docs                  # Generate markdown docs for the current project's exposed modules
saga docs --dir <path>     # Document every .saga module under <path> (no project.toml needed)
```

## Diagnostics

Set environment variables on any command that lowers (`run`/`build`/`emit`) to
print compiler diagnostics to stderr.

```bash
# Trait specialization stats: per module, how many statically-known trait
# dictionary-method dispatch sites were specialized to direct calls vs left on
# the runtime element/2 dict-passing path (with a reason for each fallback).
SAGA_STATS=trait-spec saga emit file.saga
```

Example output (one line per module):

```text
trait-spec[MyModule]: 32 known site(s) | 8 specialized | 24 fell back (14 imported, 10 parameterized)
```

`SAGA_STATS` accepts `trait-spec`/`1`/`all` for every module, or a module-name
substring to filter (e.g. `SAGA_STATS=MyModule`). Stats print to stderr, so the
emitted Core on stdout is unaffected:

```bash
SAGA_STATS=trait-spec saga emit file.saga 2>&1 >/dev/null | grep trait-spec
```

Related tracing flags (`SAGA_DEBUG_TRAIT_DISPATCH`, `SAGA_DEBUG_EFFECT_SHAPES`)
are described in [docs/planning/trait-specialization.md](docs/planning/trait-specialization.md)
and [docs/planning/direct-first-effect-lowering.md](docs/planning/direct-first-effect-lowering.md).

## Running tests

```bash
cargo test                                     # All Rust tests
cargo test -p saga parser                      # Parser tests only
cargo test -p saga typechecker                 # Typechecker tests only
cargo test -p saga codegen                     # Codegen unit tests only
cargo test --test codegen_integration          # Integration tests (full pipeline, requires Erlang)
cargo test --test module_codegen_integration   # Multi-module integration tests
cargo test --test e2e                          # End-to-end tests
cargo test --test stdlib_tests                 # Stdlib tests
cargo clippy                                   # Lint
```

### Compiler internals

- [Compiler Overview](docs/compiler-overview.md) -- start here
- [Typechecking](docs/typechecking.md) -- per-module pass structure and inference flow
- [Name Resolution](docs/name-resolution.md)
- [Effect Implementation](docs/effect-implementation.md) -- effect rows, handler checking, CPS
- [Trait Dictionary Passing](docs/trait-dict-passing.md)

## License

GPL-3.0 -- see [LICENSE](LICENSE).
