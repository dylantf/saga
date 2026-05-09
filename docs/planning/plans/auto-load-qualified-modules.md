# Auto-Load Modules Referenced by Fully-Qualified Names

Plan for fixing a regression where fully-qualified canonical names like
`Std.IO.Unsafe.print_stdout` or `Lib.foo` fail with "unknown qualified name"
unless the containing module is explicitly imported.

## Bug

Reproducer: [examples/scratch.saga](../../../examples/scratch.saga) and
[examples/bugs/fully-qualified-import/src/Main.saga](../../../examples/bugs/fully-qualified-import/src/Main.saga).

```
Type error: unknown qualified name 'Std.IO.Unsafe.print_stdout'
```

Adding `import Std.IO.Unsafe` (even without `exposing`) makes the error go
away. Same shape with project modules: `Lib.foo` fails until `import Lib`
is added, even though `Lib` is in the project module map.

`Std.Int.add` works only because the prelude imports `Std.Int`.

## Root Cause

`typecheck_import` ([src/typechecker/check_module.rs:554](../../../src/typechecker/check_module.rs#L554))
bundles two distinct concerns:

1. **Loading**: parse/check the module and register its exports under
   canonical keys (`Std.IO.Unsafe.print_stdout`) in `self.env`,
   `self.constructors`, etc. via `inject_exports`.
2. **Importing into scope**: populate `scope_map` with bare/aliased forms
   so unqualified or alias-prefixed references resolve to canonical names.

`process_imports` ([src/typechecker/check_decl.rs:440](../../../src/typechecker/check_decl.rs#L440))
only walks `Decl::Import` nodes, so concern #1 only happens for explicit
imports (plus prelude transitively). Without #1, the canonical key isn't in
`self.env`, so `infer.rs::QualifiedName`
([src/typechecker/infer.rs:391](../../../src/typechecker/infer.rs#L391))
emits "unknown qualified name".

The contract implied by the resolver/codegen split is that **canonical
names should be a stable identity** — but today they only resolve if the
module was loaded for an unrelated reason.

## Fix Strategy

Treat module *loading* (concern #1) as triggerable by canonical-name
reference, separately from *importing into scope* (concern #2, which still
requires an explicit `import`).

Discovery happens before resolution, so resolve+infer see a fully-loaded
env in their normal single pass.

### Pipeline change

In `check_program_inner` ([src/typechecker/check_decl.rs:66](../../../src/typechecker/check_decl.rs#L66)):

```
process_imports                              # unchanged: explicit imports
collect_referenced_qualified_modules(...)    # NEW: small dedicated walker
for each module not yet loaded:
    if known (builtin OR in project module map):
        typecheck_import(path, alias=None, exposing=None, ...)
resolve_names                                # unchanged: runs once
register_definitions, ...                    # unchanged
```

### Why this isn't brittle

- The discovery walker only collects strings. It can't desync from real
  resolution because it doesn't make resolution decisions.
- `typecheck_import` is already idempotent: the cache check at
  [check_module.rs:590](../../../src/typechecker/check_module.rs#L590)
  short-circuits if `self.modules.exports` already has the module.
- Unknown module strings (typos, refs to non-existent modules) are skipped
  in the auto-load step and fail at resolve/infer time with the same
  existing diagnostic. No new failure modes; the user-facing error for
  truly bad names is unchanged.
- Calling `typecheck_import(path, alias=None, exposing=None, ...)` only
  registers what an explicit `import Foo.Bar` would register. Not new
  scope behavior — just doing implicitly what the user would otherwise be
  forced to write.

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
- **Better diagnostic suggesting `import X`**: doesn't fix the friction;
  canonical names should just work.

## Implementation Plan

### Phase 1: Discovery walker

Add to [src/typechecker/resolve.rs](../../../src/typechecker/resolve.rs):

```rust
pub(crate) fn referenced_qualified_modules(program: &[Decl]) -> HashSet<String>
```

Walks every `Decl` and recurses into expressions. For each
`ExprKind::QualifiedName { module, .. }`, inserts `module.clone()` into
the set.

Single-purpose walker. Mechanical match arms covering all `Decl` and
`Expr` variants. Mirrors the structure of `Resolver::resolve_decl` /
`resolve_expr` but only collects strings — it has no scope, no
`ResolutionResult`, no local-binding tracking.

Doesn't try to share code with `Resolver`. The duplication is
intentional: discovery and resolution are different jobs and giving them
the same walker would re-couple the two concerns we're separating.

### Phase 2: Auto-load step

In `check_program_inner`, after `process_imports` and before
`resolve_names`:

```rust
let referenced = referenced_qualified_modules(program);
for module_name in &referenced {
    if self.modules.exports.contains_key(module_name) {
        continue;
    }
    let path: Vec<String> = module_name.split('.').map(str::to_string).collect();
    let known = builtin_module_source(&path).is_some()
        || self.modules.map.as_ref()
            .is_some_and(|m| m.contains_key(module_name));
    if !known {
        continue;
    }
    // Use a synthetic span; errors here are reported against the module itself.
    let _ = self.typecheck_import(&path, None, None, Span::synthetic());
}
```

Failures from `typecheck_import` (e.g. parse errors in the auto-loaded
module) are surfaced as diagnostics through the normal collected-errors
path, the same way explicit-import failures are.

Span handling: pick the first `QualifiedName` reference site rather than
synthetic, so error messages from auto-loaded modules point at user code.
(Simple: change the walker to return `HashMap<String, Span>` keyed on
first occurrence.)

### Phase 3: Tests

Two integration tests:

1. **Stdlib**: `Std.IO.Unsafe.print_stdout "hello"` typechecks without an
   explicit `import Std.IO.Unsafe`. Mirrors `examples/scratch.saga`.
2. **Project module**: a two-file project where `Main` references
   `Lib.foo` without `import Lib` typechecks and runs end-to-end. Mirrors
   `examples/bugs/fully-qualified-import/`.

Plus a negative test:

3. `Bogus.Module.foo` still produces the existing "unknown qualified
   name" diagnostic (auto-load step skips it; resolve/infer fail as
   today).

### Phase 4: Verify no regressions

- `cargo test` (full suite — typechecker, codegen, integration).
- `cargo clippy`.
- Build and run the two example reproducers via
  `cargo run --bin saga -- run`.

## Out of Scope

- Changing the *importing into scope* semantics. Bare names and aliases
  still require explicit `import` decls. This plan only addresses
  fully-qualified canonical references.
- Refactoring `typecheck_import` to physically split the loading and
  scope-injection concerns into separate functions. The current shape
  works fine when called with `alias=None, exposing=None`. A larger
  split could happen later if other use cases emerge.
- LSP behavior (completion, hover, code actions). The auto-load happens
  on the same path the LSP already drives, so it should benefit
  transparently, but no LSP-specific work is planned here.

## Files Touched

- [src/typechecker/resolve.rs](../../../src/typechecker/resolve.rs) —
  add discovery walker.
- [src/typechecker/check_decl.rs](../../../src/typechecker/check_decl.rs) —
  call walker + auto-load loop in `check_program_inner`.
- New tests under `tests/` (integration).
