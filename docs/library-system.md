# Library System Design

This document covers the design and implementation plan for library support: building libraries, consuming dependencies, and controlling public API surface.

## project.toml Format

```toml
[project]
name = "math-lib"

# Optional: declares this project as a library
[library]
module = "Math"                              # root namespace, required
expose = ["Math", "Math.Vector", "Math.Matrix"]  # public modules, required

# Optional: declares this project as a runnable binary
[bin]
main = "Main.dy"   # entry point, defaults to Main.dy

# Optional: external dependencies
[deps]
math = { path = "deps/math-lib" }
http = { path = "deps/http", as = "Net" }   # alias remaps the module prefix
```

- A project can have `[library]`, `[bin]`, or both.
- `[library].module` is the root namespace. All modules in `expose` must be prefixed by it.
- `[library].expose` is required when `[library]` is present. Only listed modules are importable by consumers. Unlisted modules are compiled (they're needed at runtime) but not surfaceable through the type system.
- `[bin].main` defaults to `Main.dy`. The main file must define a `main` function.
- `[deps]` entries point to local paths. Each dep must itself be a project with a `project.toml`.
- `as` on a dep remaps the library's `module` prefix. If a dep has `module = "HTTP"` and the consumer says `as = "Net"`, then `HTTP.Client` becomes `Net.Client` in the consumer's code.

## Dependency Resolution

When the compiler encounters `[deps]`:

1. For each dep, read its `project.toml`
2. Validate it has a `[library]` section
3. Scan its modules via `scan_project_modules`
4. Filter to only the modules in its `expose` list
5. Apply `as` prefix remapping if present
6. Add the resulting modules to the parent project's `ModuleMap`

### Transitive Dependencies

If dep A depends on dep B, the compiler recursively resolves B first. The parent project does not automatically get access to B's modules (they'd need to be in A's `expose` list, or the parent must depend on B directly). This prevents leaking transitive implementation details.

### Collision Detection

If two deps expose the same module name (after aliasing), it's a compile error telling the user to add an `as` alias to one of them.

## Library Build

`dylang build` on a library project (no `[bin]`) compiles all modules to BEAM files in `_build/` but does not look for a `main` function or invoke `erl`. The output is a directory of `.beam` files ready to be consumed as a dep.

## What Doesn't Change

- The typechecker and codegen pipelines are unchanged. Modules are modules regardless of origin.
- `pub` remains the visibility keyword for definitions within a module.
- `import` syntax is unchanged. Consumers import dep modules by their (possibly aliased) names like any other module.
- Script mode is unaffected.

## Future Work (Not in Scope)

- **Re-exports / `export` syntax**: A mechanism for a module to surface imported names as part of its own public API without wrapper functions. Useful for building flat facade modules over complex internal structures. Deferred until the pain point is hit in practice.
- **Remote dependencies**: The dep entry structure is designed to extend to other sources. `path` is one variant; `hex` and `github` are natural additions that resolve to a cached local directory, then follow the same pipeline (read project.toml, filter expose, scan modules). Adding remote deps requires a fetch/cache layer and a lockfile, but no changes to module resolution.
  ```toml
  json = { hex = "jason", version = "~> 1.4" }
  utils = { github = "dylan/utils", ref = "main" }
  ```

---

## Implementation Plan

### Phase 1: Expand project.toml Parsing

Extend `ProjectConfig` in `src/main.rs` to parse the new fields:

```rust
struct ProjectConfig {
    project: ProjectSection,
    library: Option<LibrarySection>,
    bin: Option<BinSection>,
    deps: Option<HashMap<String, DepEntry>>,
}

struct LibrarySection {
    module: String,
    expose: Vec<String>,
}

struct BinSection {
    main: Option<String>,  // defaults to "Main.dy"
}

enum DepSource {
    Path { path: String },
    // Future: Hex { package: String, version: String },
    // Future: Github { repo: String, ref: Option<String> },
}

struct DepEntry {
    source: DepSource,
    r#as: Option<String>,  // alias
}
```

Validation:
- At least one of `[library]` or `[bin]` must be present
- If `[library]`, `module` and `expose` are required
- All `expose` entries must be prefixed by `module`
- Warn on unknown fields

Existing projects with only `[project]` should continue to work (backward compatible, treated as `[bin]` with `main = "Main.dy"`).

### Phase 2: Dep Resolution in Module Scanning

Extend `scan_project_modules` (in `src/typechecker/check_module.rs`) to:

1. Accept deps config as input
2. For each dep:
   - Read dep's `project.toml`, validate it has `[library]`
   - Recursively resolve the dep's own `[deps]` first (with cycle detection)
   - Call `scan_project_modules` on the dep's root
   - Filter results to only modules in the dep's `expose` list
   - Apply `as` prefix remapping
   - Merge into the parent's `ModuleMap`
3. Detect and error on module name collisions between deps

### Phase 3: Library Build Path

Add a library build mode to the CLI:

- When a project has `[library]` but no `[bin]`, `dylang build` compiles all modules but skips the main-function check and `erl` invocation.
- When a project has both, `dylang build` compiles everything and `dylang run` executes the binary entry point as usual.
- Library-only projects error on `dylang run` with a clear message.

### Phase 4: Expose Filtering

During dep resolution, ensure that only `expose`-listed modules are added to the consumer's module map. Internal modules are compiled (they exist as `.beam` files) but the type system refuses to resolve imports to them.

Validation: if a consumer tries to `import Math.Internal` and it's not in the dep's expose list, the error message should say the module exists but is not exposed, rather than "module not found."
