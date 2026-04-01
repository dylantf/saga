# Name Resolution

## Current State

Name resolution is handled by a `ScopeMap` on the `Checker` struct that maps user-visible name forms to canonical (module-qualified) names. The resolution logic lives in three places:

- **`resolve_import`** (pure function in `check_module.rs`) — builds a `ScopeMap` from module exports and import parameters, validates exposing clauses
- **`resolve_names`** (AST pass in `resolve.rs`) — rewrites Var names, constructor names, and fills `canonical_module` on `QualifiedName` nodes
- **Typechecker lookups** (`infer.rs`) — resolve remaining names through scope_map at inference time (fallback for names not rewritten in the AST)

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
   - Trait method schemes under both bare and canonical names in env
   - Effects under bare + qualified names (bare for internal type checking, qualified for user access)
   - Handlers under qualified name always, bare only when exposed
   - Traits, type arities, LSP metadata

3. **`resolve_names`** rewrites the AST after all imports are processed:
   - `Var { name: "map" }` → `Var { name: "Std.List.map" }` (if not locally bound)
   - `Var { name: "show" }` → `Var { name: "Std.Base.Show.show" }` (trait methods too)
   - `Constructor { name: "Just" }` → `Constructor { name: "Std.Maybe.Just" }` (unless locally defined)
   - `Pat::Constructor` — same treatment
   - `QualifiedName { module: "List", name: "map", canonical_module: None }` → fills `canonical_module: Some("Std.List")`
   - The pass is **scope-aware**: local bindings (function params, let bindings, lambda params, case pattern bindings) shadow imports

4. **Typechecker lookups** resolve remaining names through scope_map at inference time:
   - `Var "Std.List.map"` → env.get("Std.List.map") (found directly, since resolve pass rewrote it)
   - Fallback: `env.get(name).or_else(|| env.get(scope_map.resolve(name)))` handles any names not rewritten
   - Local definitions (function params, let bindings) are found directly by bare name in env, taking priority

### Canonical name forms

Every imported name has a canonical form in the scope_map:

| Kind | Example | Canonical form |
|------|---------|---------------|
| Function | `map` from `Std.List` | `Std.List.map` |
| Constructor | `Just` from `Std.Maybe` | `Std.Maybe.Just` |
| Type | `Maybe` from `Std.Maybe` | `Maybe` (types use bare names internally) |
| Trait method | `show` from `Show` in `Std.Base` | `Std.Base.Show.show` |
| Effect | `Assert` from `Std.Test` | `Std.Test.Assert` (codegen), bare in type system |
| Effect op | `log` from `Log` in `Std.IO` | `Std.IO.Log.log` (scope_map only) |
| Handler | `exec_handler` from `Std.Test` | `Std.Test.exec_handler` |

### Import visibility rules

All imported names follow consistent rules:

| Import form | Qualified access | Bare access |
|-------------|-----------------|-------------|
| `import Logger` | `Logger.greet`, `Logger.Log`, `Logger.console_log` | none |
| `import Logger (greet, Log, console_log)` | same as above | `greet`, `Log`, `console_log` |

**Effects, handlers, functions, types, and constructors all follow the same pattern.** Nothing is implicitly exposed — `import Logger` only gives qualified access. To use bare names, list them in the exposing clause.

The parser supports qualified names in:
- `needs` clauses: `needs {Logger.Log}`
- `with` expressions: `with Logger.console_log`
- `with` inline named refs: `with { Logger.console_log, op args = body }`

**Note on effects in the type system**: The type system's `EffectRow` stores bare effect names internally. The `self.effects` map registers effects under both bare and qualified keys so internal lookups (handler arm matching, effect validation) work regardless. The bare name is an internal implementation detail — user code should use exposed or qualified names.

### Key files

- `src/typechecker/mod.rs` — `ScopeMap` struct with `resolve_value`, `resolve_type`, `resolve_constructor`, `merge`
- `src/typechecker/check_module.rs` — `resolve_import` (standalone resolver + validation), `inject_exports` (checker state), `seed_builtin_checker` (copies canonical entries)
- `src/typechecker/resolve.rs` — AST name rewriting pass (Vars, constructors, `canonical_module`), scope-aware with local binding tracking
- `src/typechecker/infer.rs` — `Var`/`Constructor`/`QualifiedName` lookups use scope_map
- `src/typechecker/unify.rs` — qualified type name resolution uses `scope_map.types`
- `src/typechecker/patterns.rs` — constructor pattern resolution uses `scope_map.constructors`
- `src/typechecker/effects.rs` — `effect_for_op` prefers bare names to match EffectRow conventions
- `src/typechecker/result.rs` — `CheckResult` includes scope_map for elaborator, canonicalizes fun_effects
- `src/elaborate.rs` — uses scope_map to bridge canonical names to trait_methods and dict params
- `src/lsp/completion.rs` — scans scope_map for aliased qualified completions
- `src/codegen/resolve.rs` — resolves canonical Var names via `qualified_scope`, CPS-expanded arity for imports
- `src/codegen/lower/init.rs` — canonical effect/handler names, `param_absorbed_effects` from type, bare→canonical resolver maps
- `src/codegen/lower/mod.rs` — `handler_canonical`/`effect_canonical` maps, `handler_param_name` sanitizes dots
- `src/parser/expr.rs` — `parse_handler_ref` supports qualified handler names in `with` expressions

### Design decisions

- **Shadowing**: `env.get(bare).or_else(|| env.get(scope_map.resolve(bare)))`. Local definitions use bare names in env; imports use canonical names. Locals naturally shadow imports.
- **Auto-imports**: The mechanism in `infer.rs` calls `typecheck_import` → `inject_exports` which populates both env and scope_map automatically.
- **`canonical_module` on QualifiedName**: The AST node carries both the user-written `module` (for codegen) and the resolved `canonical_module` (for typechecker). This avoids breaking the codegen resolver which depends on the original alias.
- **Trait methods under both names**: env has both bare (`show`) and canonical (`Std.Base.Show.show`) entries. Bare entries are needed for impl bodies; canonical entries are needed after the resolve pass rewrites Var nodes.
- **Effects under both names**: `self.effects` has both bare and qualified entries. The type system's EffectRow uses bare names, so handler arm matching needs bare-name access. User code uses qualified or exposed names.
- **Handlers respect exposing**: Unlike effects (which need bare entries for internal type checking), handlers are explicit values referenced in `with`. They follow the same exposing rules as functions.
- **CPS arity in codegen resolver**: `ImportedFun` arity includes handler params and ReturnK. Effect op counts are computed from `effect_op_counts` built from all module codegen info.
- **Canonical effect names in codegen**: `effect_defs`, `op_to_effect`, `fun_info.effects`, `handler_defs.effects` all use canonical effect names (`Std.Test.Assert`). Handler param variable names sanitize dots: `_Handle_Std_Test_Assert_assert`.
- **`param_absorbed_effects` for imports**: Computed from the type scheme so lambdas passed to HOFs get effect handler params added.

## Why This Works for Our Language

In some languages (Rust, Haskell), which name a reference resolves to can depend on its type — e.g. `x.foo()` in Rust dispatches based on the type of `x`, requiring type inference to complete resolution.

In our language, name visibility is purely structural — determined by module imports, `exposing` clauses, and lexical scope. `show` always resolves to `Show.show` regardless of the argument type. The question of *which implementation* runs is answered later by elaboration (dictionary passing), not by name resolution.

## Relationship to Codegen Resolve Pass

The codegen resolver (`src/codegen/resolve.rs`) is a separate concern. It runs post-elaboration and maps NodeIds to `ResolvedName` variants (`LocalFun`, `ImportedFun`, `ExternalFun`) with Erlang-specific info. It answers "what Erlang call target does this node map to?" — a codegen question, not a scoping question.

The codegen resolver handles canonical Var names: when a Var name contains `.` (from the pre-typecheck resolve pass), it looks up in `qualified_scope`. The `ImportedFun` arity includes CPS expansion (handler params + ReturnK).

## Remaining Work

### @external functions as values

Pre-existing bug (not from this refactor): `@external` functions used as values (not directly applied) generate `make_fun('std_io', 'println', 1)`, but the `std_io.beam` module doesn't export `println/1` because externals are forwarded to bridge modules. The `make_fun` should target the actual Erlang function, not the dylang module.
