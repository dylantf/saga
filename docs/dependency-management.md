# Dependency Management

This document covers how dylang projects consume dependencies: library configuration, dependency sources (path, git, Hex), resolution, and the lockfile.

---

## project.toml Format

```toml
[project]
name = "my-app"

# Optional: declares this project as a library
[library]
module = "Math"                                    # root namespace, required
expose = ["Math", "Math.Vector", "Math.Matrix"]    # public modules, required

# Optional: declares this project as a runnable binary
[bin]
main = "Main.dy"   # entry point, defaults to Main.dy

# Optional: dependencies
[deps]
mathlib = { path = "../math-lib" }                                  # local path
http = { git = "https://github.com/someone/http", tag = "v1.0.0" } # git
base64url = { version = "1.0.1" }                                   # hex package
```

- A project can have `[library]`, `[bin]`, or both.
- `[library].module` is the root namespace. All modules in `expose` must be prefixed by it.
- `[library].expose` is required when `[library]` is present. Only listed modules are importable by consumers. Unlisted modules are compiled (needed at runtime) but invisible to the type system.
- `[bin].main` defaults to `Main.dy`. The main file must define a `main` function.

---

## Dependency Sources

### Path Dependencies

Local filesystem dependencies. Must have a `project.toml` with a `[library]` section.

```toml
[deps]
mathlib = { path = "../math-lib" }
http = { path = "deps/http", as = "Net" }   # alias remaps the module prefix
```

`as` remaps the library's `module` prefix. If a dep has `module = "HTTP"` and the consumer says `as = "Net"`, then `HTTP.Client` becomes `Net.Client` in the consumer's code.

### Git Dependencies

Clone from a git repository. Requires `dylang install` to fetch.

```toml
[deps]
math = { git = "https://github.com/someone/math-lib", tag = "v1.0.0" }
utils = { git = "https://github.com/someone/utils", branch = "main" }
http = { git = "https://github.com/someone/http", rev = "abc123f" }
```

Specify exactly one of `tag`, `branch`, or `rev`. If none is given, defaults to `HEAD`.

Git repo source is cached globally in `~/.dylang/cache/git/` (bare clones, shared across projects). Compiled output goes to the project's `_build/deps/{name}/`.

### Hex Dependencies (Erlang packages)

Dependencies from the [Hex package registry](https://hex.pm). These are Erlang (BEAM) packages — they're compiled and made available on the code path, but not typechecked by dylang.

```toml
[deps]
base64url = { version = "1.0.1" }
argon2 = { version = "1.2.0" }
```

Hex is the default source: if a dep has no `path` or `git`, it's treated as a Hex package. The dep key is the Hex package name.

`dylang install` fetches the tarball from `repo.hex.pm`, extracts it, compiles it, and installs into the project's `deps/` directory. Tarballs are cached globally in `~/.dylang/cache/hex/` to avoid re-downloading. Transitive Hex dependencies are resolved and installed automatically.

#### Compilation

Hex packages are compiled with one of two strategies:

- **Pure Erlang packages** (no native code): compiled directly with `erlc`. Fast, no extra tools needed.
- **Packages with NIFs or build hooks**: detected by the presence of `c_src/`, `native/`, or `pre_hooks`/`port_specs` in `rebar.config`. These are compiled with `rebar3 bare compile`, which handles native code compilation (C, Rust, etc.) via the package's build hooks. Requires `rebar3` on PATH.

#### Wrapping Hex packages

Hex deps are opaque to the type system. To use them from dylang, wrap the Erlang functions with `@external` annotations (see `docs/ffi-design.md`):

```
# Direct FFI — types map cleanly
@external("erlang", "base64url", "encode")
pub fun encode : String -> String
```

For more complex cases where types need conversion, write a bridge `.erl` file. Bridge files can call into Hex deps because Erlang module calls are late-bound (resolved at runtime, not compile time):

```erlang
%% argon2_bridge.erl
-module(argon2_bridge).
-export([hash/1]).

hash(Password) ->
    {ok, Hash} = argon2:hash(Password),
    Hash.
```

```
@external("erlang", "argon2_bridge", "hash")
fun argon2_hash : String -> String
```

#### Version requirements

For now, Hex deps use exact versions. Transitive dependencies from Hex packages may specify `~>` requirements (e.g., `~> 1.0`), which are resolved to the latest compatible version.

#### Install location

Hex and git dependencies are installed into the project's `deps/` directory (e.g., `deps/base64url/ebin/`). This keeps builds isolated per project. To reinstall all deps, delete `deps/` and run `dylang install` again.

Source downloads are cached globally to avoid re-downloading:
- Hex tarballs: `~/.dylang/cache/hex/`
- Git repos: `~/.dylang/cache/git/` (bare clones)

---

## Dependency Resolution

### dylang dependencies (path, git)

When the compiler encounters `[deps]`:

1. For each dep, read its `project.toml`
2. Validate it has a `[library]` section
3. Scan its modules via `scan_project_modules`
4. Filter to only the modules in its `expose` list
5. Apply `as` prefix remapping if present
6. Add the resulting modules to the parent project's `ModuleMap`

### Transitive Dependencies

If dep A depends on dep B, the compiler recursively resolves B first. The parent project does not automatically get access to B's modules (they'd need to be in A's `expose` list, or the parent must depend on B directly). This prevents leaking transitive implementation details.

Transitive Hex dependencies are handled automatically — if a Hex package lists requirements, they are fetched and compiled during `dylang install`.

### Collision Detection

If two deps expose the same module name (after aliasing), it's a compile error telling the user to add an `as` alias to one of them.

---

## Lockfile

`dylang.lock` pins each dependency to an exact resolved state, ensuring reproducible builds.

```toml
# dylang.lock (auto-generated, do not edit)

[deps.math]
git = "https://github.com/someone/math-lib"
ref = "v1.0.0"
commit = "abc123def456789..."

[deps.base64url]
hex = "base64url"
version = "1.0.1"
checksum = "f9b3add4731a02a9..."
```

Workflow:

- `dylang install`: resolve all deps, write `dylang.lock`
- Subsequent builds: use pinned versions, skip resolution
- `dylang update`: re-resolve refs, write new lockfile
- The lockfile should be committed to version control

---

## Library Build

`dylang build` on a library project (no `[bin]`) compiles all modules to BEAM files in `_build/` but does not look for a `main` function or invoke `erl`. The output is a directory of `.beam` files ready to be consumed as a dep.

---

## What Doesn't Change

- The typechecker and codegen pipelines are unchanged. Modules are modules regardless of origin.
- `pub` remains the visibility keyword for definitions within a module.
- `import` syntax is unchanged. Consumers import dep modules by their (possibly aliased) names like any other module.
- Script mode is unaffected.

---

## Future Work

### Re-exports / `export` syntax

A mechanism for a module to surface imported names as part of its own public API without wrapper functions. Deferred until the pain point is hit in practice.

### Version Constraints for dylang deps

Semver-based version constraints for git dependencies, similar to what Hex deps use.

### Publishing to Hex

Publishing dylang packages to Hex. Would allow `version` deps to resolve dylang libraries, not just Erlang packages.

### Elixir Hex Packages

Support for Hex packages written in Elixir. Requires `elixirc` on PATH. The main complication is Elixir's macro system — packages that define or use compile-time macros need the Elixir compiler.
