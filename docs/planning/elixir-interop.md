# Elixir Package Interop

Enabling Hex packages built with Mix (Elixir) alongside the existing rebar3/erlc support. The primary motivation is accessing Bandit (HTTP server), but this unblocks the entire Elixir Hex ecosystem.

## Current State

- Hex tarballs are already downloaded, cached, and extracted
- `metadata.config` from the tarball is already parsed (used for rebar3 detection)
- Erlang packages compile via `erlc` (pure) or `rebar3 bare compile` (NIFs/hooks)
- The `build_tools` field in `metadata.config` already distinguishes package types

## Detection

The `build_tools` field in the Hex tarball's `metadata.config` indicates the build system:

| Value      | Language | Current support |
|------------|----------|-----------------|
| `"rebar3"` | Erlang   | Yes             |
| `"rebar"`  | Erlang   | Yes             |
| `"mix"`    | Elixir   | No (proposed)   |
| `"make"`   | Either   | No              |

No new metadata parsing is needed. A `"mix"` value triggers the Elixir compilation path.

## Compilation Strategy

Same architecture as the existing rebar3 path — delegate to the language's own build tool, extract `.beam` files.

### Invocation

```
elixir -S mix compile --no-deps-check --no-load-deps --no-protocol-consolidation
```

Environment variables:

| Variable         | Value                          | Purpose                                    |
|------------------|--------------------------------|--------------------------------------------|
| `MIX_BUILD_PATH` | `_build/deps/{name}`           | Direct output to our build dir             |
| `MIX_ENV`        | `"prod"`                       | Standard production compilation            |
| `MIX_QUIET`      | `"1"`                          | Suppress noisy Mix output                  |
| `TERM`           | `"dumb"`                       | Prevent ANSI escape codes in error output  |

### Key flags

- `--no-deps-check` — don't let Mix try to resolve/fetch deps (we handle that)
- `--no-load-deps` — don't load dep code at compile time (we provide beams on the code path)
- `--no-protocol-consolidation` — skip protocol consolidation pass (not needed for library use, avoids complications)

### Dependency wiring

Elixir packages have transitive deps (both Elixir and Erlang). These are already resolved by our Hex dependency resolver. To make them visible to Mix during compilation:

- Symlink each already-compiled dependency's `ebin/` directory into `_build/deps/{name}/lib/{dep}/ebin/` (where Mix expects to find them)
- Or pass them via `-pa {ebin_paths}` on the `elixir` command line

This mirrors the rebar3 approach where we set `ERL_LIBS` or pass `--paths` to make sibling deps visible.

### Elixir core libraries

Elixir's own standard libraries (`elixir`, `logger`, `eex`, `mix`) must be on the code path. These ship with the Elixir installation. Discovery:

1. Run `elixir -e "IO.puts(:code.lib_dir(:elixir))"` (or similar) once
2. Cache the paths for the duration of the build
3. Add them to the code path when running compiled Elixir code

This is a one-time probe per build, same as checking for `rebar3` on PATH.

## Runtime Requirements

- `elixir` (and by extension `erlang`) on PATH
- Same requirement pattern as rebar3 — only needed if the project actually has Elixir deps
- Error message if missing: "Elixir is required to compile {package}. Install from https://elixir-lang.org/install.html"

## FFI Usage (Bandit Example)

Once Elixir packages compile, they're just `.beam` files on the code path. Existing `@external` and bridge file mechanisms work unchanged.

Elixir modules use `Elixir.`-prefixed atoms at the BEAM level (`Elixir.Bandit`, `Elixir.Plug.Conn`), so FFI declarations reference those:

```
@external("erlang", "Elixir.Bandit", "start_link")
fun start_link : (opts: List (String, Dynamic)) -> Result Pid String
```

In practice, a bridge `.erl` file is more ergonomic for adapting Elixir conventions:

```erlang
-module(bandit_bridge).
-export([start/2]).

start(Handler, Port) ->
    'Elixir.Bandit':start_link([{plug, Handler}, {port, Port}]).
```

Elixir structs (like `Plug.Conn`) are maps with a `__struct__` key at the BEAM level, readable with normal map operations. No special handling needed in the compiler.

## Scope

### In scope

- Detect `"mix"` in `build_tools` metadata
- Compile Elixir Hex packages via `elixir -S mix compile`
- Wire transitive deps for Mix compilation
- Discover and cache Elixir core library paths
- Clear error when `elixir` is not on PATH

### Out of scope (for now)

- Elixir path/git dependencies (just Hex)
- Protocol consolidation
- Publishing dylang packages as Elixir-compatible
- Any special type system support for Elixir types

## Reference: Gleam's Approach

Gleam solves the same problem identically — `elixir -S mix compile` with the same flags, symlinked deps, cached core lib paths. This is a validated approach running in production across the Gleam ecosystem.
