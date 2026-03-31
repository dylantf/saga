# Name Resolution

## Current State

Name resolution is handled by a `ScopeMap` on the `Checker` struct that maps user-visible name forms to canonical (module-qualified) names. The resolution logic lives in the standalone `resolve_import` function in `check_module.rs`.

### How it works

When `import Std.List as List exposing (map)` is processed:

1. **`resolve_import`** builds a `ScopeMap` with entries:
   - `"Std.List.map"` → `"Std.List.map"` (canonical)
   - `"List.map"` → `"Std.List.map"` (aliased)
   - `"map"` → `"Std.List.map"` (exposed)
   - Plus type and constructor entries following the same pattern

2. **`inject_exports`** merges the scope_map, then registers checker state:
   - Canonical bindings in `TypeEnv` (one entry per import)
   - Canonical constructors in `constructors` map
   - Traits, effects, handlers, type arities
   - LSP metadata (import_origins, doc_comments, constructor_def_ids)

3. **Lookups** resolve through the scope_map first:
   - `Var "map"` → scope_map resolves to `"Std.List.map"` → found in env
   - `QualifiedName "List" "map"` → constructs `"List.map"` → scope_map resolves to `"Std.List.map"` → found in env
   - Local definitions (function params, let bindings) are found directly by bare name in env, taking priority over scope_map resolution

### Key files

- `src/typechecker/mod.rs` — `ScopeMap` struct with `resolve_value`, `resolve_type`, `resolve_constructor`
- `src/typechecker/check_module.rs` — `resolve_import` (standalone resolver), `inject_exports` (checker state)
- `src/typechecker/infer.rs` — `Var`/`Constructor`/`QualifiedName` lookups use scope_map
- `src/typechecker/unify.rs` — qualified type name resolution uses `scope_map.types`
- `src/typechecker/patterns.rs` — constructor pattern resolution uses `scope_map.constructors`
- `src/typechecker/result.rs` — `CheckResult` includes scope_map for elaborator
- `src/elaborate.rs` — uses scope_map to bridge aliased names to canonical dict params
- `src/lsp/completion.rs` — scans scope_map for aliased qualified completions

### Design decisions

- **Trait methods stay bare**: Trait methods (e.g. `show`) are registered under bare names, not canonical. They work like Haskell typeclass methods — always unqualified.
- **Shadowing**: `env.get(bare).or_else(|| env.get(scope_map.resolve(bare)))`. Local definitions use bare names in env; imports use canonical names. Locals naturally shadow imports.
- **Auto-imports**: The mechanism in `infer.rs` calls `typecheck_import` → `inject_exports` which populates both env and scope_map automatically.

## Why This Works for Our Language

In some languages (Rust, Haskell), which name a reference resolves to can depend on its type — e.g. `x.foo()` in Rust dispatches based on the type of `x`, requiring type inference to complete resolution.

In our language, name visibility is purely structural — determined by module imports, `exposing` clauses, and lexical scope. `show` always resolves to `Show.show` regardless of the argument type. The question of *which implementation* runs is answered later by elaboration (dictionary passing), not by name resolution.

## Future: Full Resolve Pass

The `resolve_import` function is the seed of a standalone pre-typecheck resolver. The next step would be to move it earlier in the pipeline:

```
Parse -> Derive -> Desugar -> Resolve Names -> Typecheck -> Elaborate -> ...
```

This would involve:
1. Walking the AST to find all `import` declarations
2. Calling `resolve_import` for each to build the full scope_map
3. Rewriting name references in the AST to canonical form
4. Passing the canonicalized AST to the typechecker

The multi-module ordering already exists (`typecheck_import` processes dependencies first). The resolver would slot into this existing loop.

## Relationship to Codegen Resolve Pass

The codegen resolver (`src/codegen/resolve.rs`) is a separate concern. It runs post-elaboration and maps NodeIds to `ResolvedName` variants (`LocalFun`, `ImportedFun`, `ExternalFun`) with Erlang-specific info. It answers "what Erlang call target does this node map to?" — a codegen question, not a scoping question.
