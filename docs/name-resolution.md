# Name Resolution

## Current State

Name resolution is handled by a `ScopeMap` on the `Checker` struct that maps user-visible name forms to canonical (module-qualified) names. The resolution logic lives in two places:

- **`resolve_import`** (pure function in `check_module.rs`) — builds a `ScopeMap` from module exports and import parameters
- **`resolve_names`** (AST pass in `resolve.rs`) — rewrites constructor names and fills `canonical_module` on `QualifiedName` nodes

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

3. **`resolve_names`** rewrites the AST after all imports are processed:
   - `Constructor { name: "Just" }` → `Constructor { name: "Std.Maybe.Just" }` (unless locally defined)
   - `Pat::Constructor` — same treatment
   - `QualifiedName { module: "List", name: "map", canonical_module: None }` → fills `canonical_module: Some("Std.List")`
   - Bare `Var` nodes are NOT rewritten (see "What's not resolved yet" below)

4. **Typechecker lookups** resolve remaining names through scope_map at inference time:
   - `Var "map"` → scope_map resolves to `"Std.List.map"` → found in env
   - `QualifiedName` → uses `canonical_module` if set, falls back to scope_map
   - Local definitions (function params, let bindings) are found directly by bare name in env, taking priority

### Canonical name forms

Every imported name has a canonical form in the scope_map:

| Kind | Example | Canonical form |
|------|---------|---------------|
| Function | `map` from `Std.List` | `Std.List.map` |
| Constructor | `Just` from `Std.Maybe` | `Std.Maybe.Just` |
| Type | `Maybe` from `Std.Maybe` | `Maybe` (types use bare names internally) |
| Trait method | `show` from `Show` in `Std.Base` | `Std.Base.Show.show` |
| Effect op | `log` from `Log` in `Std.IO` | `Std.IO.Log.log` |

Trait methods and effect ops have canonical names recorded in the scope_map but are still registered under bare names in `env`. The canonical forms are available for future use when the elaborator and effect system are updated.

### Key files

- `src/typechecker/mod.rs` — `ScopeMap` struct with `resolve_value`, `resolve_type`, `resolve_constructor`, `merge`
- `src/typechecker/check_module.rs` — `resolve_import` (standalone resolver + validation), `inject_exports` (checker state)
- `src/typechecker/resolve.rs` — AST name rewriting pass (constructors, `canonical_module`)
- `src/typechecker/infer.rs` — `Var`/`Constructor`/`QualifiedName` lookups use scope_map
- `src/typechecker/unify.rs` — qualified type name resolution uses `scope_map.types`
- `src/typechecker/patterns.rs` — constructor pattern resolution uses `scope_map.constructors`
- `src/typechecker/result.rs` — `CheckResult` includes scope_map for elaborator
- `src/elaborate.rs` — uses scope_map to bridge aliased names to canonical dict params
- `src/lsp/completion.rs` — scans scope_map for aliased qualified completions

### Design decisions

- **Shadowing**: `env.get(bare).or_else(|| env.get(scope_map.resolve(bare)))`. Local definitions use bare names in env; imports use canonical names. Locals naturally shadow imports.
- **Auto-imports**: The mechanism in `infer.rs` calls `typecheck_import` → `inject_exports` which populates both env and scope_map automatically.
- **`canonical_module` on QualifiedName**: The AST node carries both the user-written `module` (for codegen) and the resolved `canonical_module` (for typechecker). This avoids breaking the codegen resolver which depends on the original alias.

## What's Not Resolved Yet

### Bare Var names

`Var { name: "map" }` is NOT rewritten to `Var { name: "Std.List.map" }` in the AST. Instead, it's resolved at lookup time via the scope_map in `infer.rs`. This is because:

1. The **codegen resolver** expects bare names in `Var` nodes and looks them up in its own `scope` map. Canonical-form Var names (containing dots) would need the codegen resolver updated to check `qualified_scope` as well.
2. **Trait methods** (`show`, `compare`, etc.) have canonical names in scope_map (`Std.Base.Show.show`) but are still registered under bare names in `env`. Rewriting the Var would point to a name that doesn't exist in env yet.

Both blockers resolve with the same work: updating the codegen resolver and the trait method / effect op registration to use canonical names.

### Trait methods and effect ops

These are registered in `env` under bare names (`"show"`, `"log"`) and dispatched through the evidence system (trait methods) or effect call syntax (effect ops). The scope_map records their canonical forms (`Std.Base.Show.show`, `Std.IO.Log.log`) but nothing uses them yet. Switching to canonical names requires updating:

- The elaborator's `trait_methods` map (keyed by bare name → needs canonical keys)
- The `resolve_trait_method` lookup in the elaborator
- The effect operation lookup in `effects.rs`
- The `seed_builtin_checker` function (copies trait methods by bare name)

## Why This Works for Our Language

In some languages (Rust, Haskell), which name a reference resolves to can depend on its type — e.g. `x.foo()` in Rust dispatches based on the type of `x`, requiring type inference to complete resolution.

In our language, name visibility is purely structural — determined by module imports, `exposing` clauses, and lexical scope. `show` always resolves to `Show.show` regardless of the argument type. The question of *which implementation* runs is answered later by elaboration (dictionary passing), not by name resolution.

## Relationship to Codegen Resolve Pass

The codegen resolver (`src/codegen/resolve.rs`) is a separate concern. It runs post-elaboration and maps NodeIds to `ResolvedName` variants (`LocalFun`, `ImportedFun`, `ExternalFun`) with Erlang-specific info. It answers "what Erlang call target does this node map to?" — a codegen question, not a scoping question.

The codegen resolver currently depends on the original user-written name forms in the AST (`module` field on QualifiedName, bare names on Var). As the pre-typecheck resolve pass rewrites more names to canonical form, the codegen resolver will need to handle canonical names too — either by checking `qualified_scope` for dot-containing Var names, or by using the `canonical_module` field on QualifiedName.
