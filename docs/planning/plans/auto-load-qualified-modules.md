# Auto-Load Modules Referenced by Fully-Qualified Names

Plan for fixing a regression where fully-qualified canonical names like
`Std.IO.Unsafe.print_stdout` or `Lib.foo` fail with "unknown qualified name"
unless the containing module is explicitly imported.

## Bug

Reproducers:

- [examples/scratch.saga](../../../examples/scratch.saga) — stdlib case.
- [examples/bugs/fully-qualified-import/src/Main.saga](../../../examples/bugs/fully-qualified-import/src/Main.saga)
  — project-module case.

```
Type error: unknown qualified name 'Std.IO.Unsafe.print_stdout'
```

Adding `import Std.IO.Unsafe` (even without `exposing`) makes the error go
away. Same shape with project modules: `Lib.foo` fails until `import Lib` is
added, even though `Lib` is in the project module map.

`Std.Int.add` works only because the prelude transitively imports `Std.Int`.

## Root Cause

`typecheck_import` ([check_module.rs:554](../../../src/typechecker/check_module.rs#L554))
bundles two distinct concerns:

1. **Loading + canonical registration**: parse/check the imported module and
   register its exports under canonical keys (`Std.IO.Unsafe.print_stdout`)
   in `self.env`, `self.trait_state`, `self.effects`, etc.
2. **Scope injection**: populate `scope_map` with bare/aliased forms so
   unqualified or alias-prefixed references resolve to canonical names.

`inject_exports` ([check_module.rs:851](../../../src/typechecker/check_module.rs#L851))
does both today:

- The `resolve_import(...)` + `scope_map.merge(...)` calls at
  [check_module.rs:860-862](../../../src/typechecker/check_module.rs#L860-L862)
  are concern #2.
- Everything from [check_module.rs:864](../../../src/typechecker/check_module.rs#L864)
  onward is concern #1.

`process_imports` ([check_decl.rs:98](../../../src/typechecker/check_decl.rs#L98))
only walks `Decl::Import` nodes, so concern #1 only happens for explicit
imports (plus prelude transitively). Without #1, the canonical key isn't in
`self.env`, so `infer.rs::QualifiedName`
([infer.rs:391](../../../src/typechecker/infer.rs#L391)) emits "unknown
qualified name".

The contract implied by the resolver/codegen split is that **canonical names
should be a stable identity** — but today they only resolve if the module
was loaded for an unrelated reason.

## Fix Strategy

Treat module *loading + canonical registration* (concern #1) as triggerable
by canonical-name reference, separately from *scope injection* (concern #2,
which still requires an explicit `import`).

Discovery happens before resolution, so resolve+infer see a fully-loaded env
in their normal single pass.

### Pipeline change

In `check_program_inner` ([check_decl.rs:66](../../../src/typechecker/check_decl.rs#L66)):

```
process_imports                              # unchanged: explicit imports
collect_referenced_qualified_modules(...)    # NEW: discovery walker
for each module not yet loaded:
    if known (builtin OR in project module map):
        load_module_canonical(path, span)    # NEW: load WITHOUT scope inject
resolve_names                                # unchanged: runs once
register_definitions, ...                    # unchanged
```

### Critical: load without scope injection

`typecheck_import(path, alias=None, exposing=None, ...)` defaults the prefix
to the last path segment ([check_module.rs:562-564](../../../src/typechecker/check_module.rs#L562-L564))
and calls `inject_exports`, which merges bare-prefix scope entries into
`scope_map`. Calling it directly from auto-load would silently make
`Unsafe.print_stdout` resolve as a bare form even though the user never
wrote `import Std.IO.Unsafe`. That contradicts the goal — only the
*canonical* form should work for unimported modules.

The fix is a small refactor of `inject_exports`:

```rust
// New: skip the resolve_import + scope_map.merge step.
fn register_module_canonical_exports(
    &mut self,
    exports: &ModuleExports,
    module_name: &str,
) -> Result<(), Diagnostic>;

// Existing: still does both. Now implemented as:
//   register_module_canonical_exports(...)?;
//   merge_import_scope(exports, module_name, prefix, exposing, span)
fn inject_exports(...) { ... }
```

`merge_import_scope` is just the `resolve_import` + `scope_map.merge` block
from [check_module.rs:860-862](../../../src/typechecker/check_module.rs#L860-L862),
extracted verbatim.

Auto-load also needs the loading half of `typecheck_import` (parse, check,
cache, recurse) without the inject_exports call. Approach: introduce a
private helper

```rust
fn load_module(&mut self, module_path: &[String], span: Span)
    -> Result<ModuleExports, Diagnostic>;
```

that contains everything from `typecheck_import`'s prelude/circularity
checks through `self.modules.exports.insert(...)`, returning the exports
without injecting anything. `typecheck_import` becomes:

```rust
let exports = self.load_module(module_path, span)?;
self.inject_exports(&exports, &module_name, &prefix, exposing, span)
```

Auto-load calls `load_module` followed by `register_module_canonical_exports`
— never `merge_import_scope`.

### Why this isn't brittle

- The discovery walker only collects strings. It can't desync from real
  resolution because it makes no resolution decisions.
- `load_module` is idempotent: the cache check at
  [check_module.rs:590](../../../src/typechecker/check_module.rs#L590)
  short-circuits if `self.modules.exports` already has the module. A later
  explicit `import` of the same module returns the cached exports and runs
  `inject_exports` (which is also idempotent on the canonical side via
  `entry().or_insert_with`).
- Unknown module strings (typos, refs to non-existent modules) are skipped
  at the auto-load step and fail at resolve/infer time with the existing
  diagnostic. No new failure modes.
- Splitting `inject_exports` is mechanical: the existing function already
  has a clear seam at [check_module.rs:862](../../../src/typechecker/check_module.rs#L862)
  between scope merging and canonical registration.

### Why not the alternatives

- **Run resolve_names twice (resolve → discover misses → load → resolve
  again)**: brittle. Two resolver invocations whose outputs must agree;
  any future side-effect in resolution would silently misbehave on the
  second pass.
- **Lazy load inside `resolve.rs::QualifiedName`**: resolver doesn't have
  `Checker` access. Threading `&mut self` or a callback into the resolver
  conflates resolution with module loading.
- **Auto-load every known module up-front**: wastes work typechecking
  modules the user never references, and inflates the diagnostics surface
  with errors from unused modules.
- **Call `typecheck_import` directly from auto-load**: simpler in the short
  term, but leaks bare-prefix scope entries (see above), violating the
  "bare names still require explicit import" contract.
- **Better diagnostic suggesting `import X`**: doesn't fix the friction;
  canonical names should just work.

## Implementation Plan

### Phase 1: Split `inject_exports`

Mechanical refactor of [check_module.rs:851](../../../src/typechecker/check_module.rs#L851).
No behavior change.

1. Extract lines 860–862 into `merge_import_scope(&mut self, exports,
   module_name, prefix, exposing, span)`.
2. Rename the remainder (line 864 onward) to
   `register_module_canonical_exports(&mut self, exports, module_name)`.
3. `inject_exports` becomes a two-line wrapper: register canonical, then
   merge scope.
4. Extract the loading half of `typecheck_import` into
   `load_module(&mut self, module_path, span) -> Result<ModuleExports, _>`,
   returning the cached/freshly-built exports without injecting them.
   `typecheck_import` becomes: `let exports = self.load_module(...)?;
   self.inject_exports(&exports, ...)`.

Verify with `cargo test` before moving on. This phase alone should be a
no-op for all existing tests.

### Phase 2: Discovery walker

Add to [resolve.rs](../../../src/typechecker/resolve.rs):

```rust
pub(crate) fn referenced_qualified_modules(
    program: &[Decl],
) -> HashMap<String, Span>;
```

Walks every `Decl` and recurses into expressions, types, and patterns. For
each `ExprKind::QualifiedName { module, span, .. }` (and any equivalent
type/pattern variants), inserts `module.clone()` into the map keyed on
first-occurrence span. Returning `HashMap<String, Span>` (not `HashSet`)
lets auto-load report errors against user code rather than synthetic spans.

Single-purpose walker: mechanical match arms covering all `Decl` and `Expr`
variants, no scope tracking, no resolution decisions. Mirrors the structure
of `Resolver::resolve_decl`/`resolve_expr` but only collects strings. The
duplication is intentional — sharing code with `Resolver` would re-couple
the two concerns we're separating.

### Phase 3: Auto-load step

In `check_program_inner` ([check_decl.rs:98](../../../src/typechecker/check_decl.rs#L98)),
between `process_imports` and `resolve_names`:

```rust
let referenced = referenced_qualified_modules(program);
for (module_name, ref_span) in &referenced {
    if self.modules.exports.contains_key(module_name) {
        continue; // already loaded by an explicit import or transitively
    }
    let path: Vec<String> = module_name.split('.').map(str::to_string).collect();
    let known = builtin_module_source(&path).is_some()
        || self
            .modules
            .map
            .as_ref()
            .is_some_and(|m| m.contains_key(module_name));
    if !known {
        continue; // typo / nonexistent — let resolve/infer emit the existing diagnostic
    }
    match self.load_module(&path, *ref_span) {
        Ok(exports) => {
            if let Err(d) = self.register_module_canonical_exports(&exports, module_name) {
                self.collected_diagnostics.push(d);
            }
            // Note: deliberately do NOT call merge_import_scope — bare/alias
            // scope visibility still requires an explicit `import` decl.
        }
        Err(d) => self.collected_diagnostics.push(d),
    }
}
```

Failures from `load_module` (e.g. parse errors in the auto-loaded module)
surface as diagnostics through the normal collected-errors path, the same
way explicit-import failures do. Spans point at the user's first reference
site, so error messages stay actionable.

### Phase 4: Tests

Cover both the positive and the scope-leak cases.

**Positive — qualified form works without explicit import:**

1. **Stdlib**: `Std.IO.Unsafe.print_stdout "hello"` typechecks without
   `import Std.IO.Unsafe`. Mirrors `examples/scratch.saga`.
2. **Project module**: a two-file project where `Main` references `Lib.foo`
   without `import Lib` typechecks and runs end-to-end via `cargo run -- run`.
   Mirrors `examples/bugs/fully-qualified-import/`.

**Negative — scope must NOT leak:**

3. **No bare-form leak**: a file references `Std.IO.Unsafe.print_stdout`
   (qualified) and then writes `Unsafe.print_stdout "x"` (alias-prefix).
   The first call typechecks; the second must fail with the existing
   "unknown name" / unresolved-reference diagnostic. This is the test that
   pins down concern #2 — auto-load makes the canonical key resolvable but
   does *not* make any bare/alias form resolvable.
4. **No bare-name leak**: same idea but with `print_stdout "x"` (fully
   bare). Must fail.

**Negative — typo behavior unchanged:**

5. `Bogus.Module.foo` still produces the existing "unknown qualified name"
   diagnostic. Auto-load skips unknown modules; resolve/infer fail as today.
6. **Mixed file**: a typo (`Bogus.Module.foo`) and a real auto-loadable ref
   (`Std.IO.Unsafe.print_stdout`) in the same file. Only the typo errors;
   the real reference still works. Confirms unknown-module skipping doesn't
   poison the rest of auto-load.

**Negative — module-with-errors propagation:**

7. A project module that exists in the module map but has a parse or type
   error, referenced via `Foo.bar`. The module's diagnostic must surface
   through the auto-load path with a span pointing at the user's reference.

### Phase 5: Verify no regressions

- `cargo test` (full suite — typechecker, codegen, integration).
- `cargo clippy`.
- Build and run the two example reproducers via
  `cargo run --bin saga -- run`.

## Out of Scope

- Changing the *scope-injection* semantics. Bare names and alias prefixes
  still require explicit `import` decls. This plan only addresses
  fully-qualified canonical references. (Phase 4 tests #3 and #4 enforce
  this.)
- LSP behavior (completion, hover, code actions). The auto-load happens on
  the same path the LSP already drives, so it should benefit transparently,
  but no LSP-specific work is planned here.
- Generalizing the `inject_exports` split beyond what's needed here. The
  three new helpers (`load_module`, `register_module_canonical_exports`,
  `merge_import_scope`) are sufficient; further refactoring of the import
  pipeline is deferred until other use cases emerge.

## Files Touched

- [src/typechecker/check_module.rs](../../../src/typechecker/check_module.rs)
  — split `inject_exports` and `typecheck_import` into the helpers above.
- [src/typechecker/resolve.rs](../../../src/typechecker/resolve.rs)
  — add `referenced_qualified_modules` discovery walker.
- [src/typechecker/check_decl.rs](../../../src/typechecker/check_decl.rs)
  — call walker + auto-load loop in `check_program_inner`.
- New tests under `tests/` (integration), covering the seven cases above.
