# Name Resolution

## Overview

Every imported name is stored once under a **canonical** (module-qualified) form. A `ScopeMap` on the `Checker` struct maps all user-visible name forms to their canonical names. A pre-typecheck AST rewriting pass (`resolve_names`) canonicalizes names in the program before inference runs.

## ScopeMap

```rust
pub struct ScopeMap {
    pub values: HashMap<String, String>,       // functions, let bindings
    pub types: HashMap<String, String>,        // type names
    pub constructors: HashMap<String, String>, // data constructors
    pub effects: HashMap<String, String>,      // effect names
    pub traits: HashMap<String, String>,       // trait names
    pub origins: HashMap<String, String>,      // canonical name -> source module
}
```

Each field maps user-visible name forms to canonical names. For example, after `import Std.List as List exposing (map)`:

```
values["Std.List.map"] = "Std.List.map"   // canonical
values["List.map"]     = "Std.List.map"   // aliased
values["map"]          = "Std.List.map"   // bare (exposed)
origins["Std.List.map"] = "Std.List"      // source module
```

Methods: `resolve_value`, `resolve_type`, `resolve_constructor`, `resolve_effect`, `resolve_trait`, `origin_of`, `is_import`, `merge`.

## Canonical Name Forms

| Kind | Example | Canonical form |
|------|---------|---------------|
| Function | `map` from `Std.List` | `Std.List.map` |
| Constructor | `Just` from `Std.Maybe` | `Std.Maybe.Just` |
| Type | `Maybe` from `Std.Maybe` | `Maybe` (types use bare names internally) |
| Trait | `Show` from `Std.Base` | `Std.Base.Show` |
| Trait method | `show` from `Show` in `Std.Base` | `Std.Base.Show.show` |
| Effect | `Fail` from `Std.Fail` | `Std.Fail.Fail` |
| Handler | `exec_handler` from `Std.Test` | `Std.Test.exec_handler` |

## Pipeline

Name resolution happens in four stages during typechecking:

### 1. `resolve_import` builds the ScopeMap

`resolve_import` (`check_module.rs`) is a pure function that takes a module's exports and import parameters and produces a `ScopeMap`. It computes all user-visible-name to canonical-name mappings for the import.

For each import, it creates entries for:
- **Values**: canonical (`Std.List.map`), aliased (`List.map`), and bare when exposed (`map`)
- **Constructors**: same three forms
- **Types**: qualified to bare (`Std.Maybe.Maybe` -> `Maybe`, `Maybe.Maybe` -> `Maybe`)
- **Effects**: canonical + aliased qualified. Bare when exposed.
- **Traits**: canonical + aliased + always bare (traits are available for `impl`/`where` from any import, regardless of exposing clause)
- **Trait methods**: always bare to canonical (trait methods are always unqualified in user code)
- **Origins**: every canonical name maps to its source module

`inject_exports` merges the `ScopeMap` from `resolve_import` and registers checker state:
- Canonical bindings in `TypeEnv` (one entry per import)
- Canonical constructors in `constructors` map
- Trait methods under both bare and canonical names in env
- Traits under canonical name in `trait_state.traits`
- Effects under canonical name only in `self.effects`
- Handlers under qualified name always, bare only when exposed

### 2. `resolve_names` rewrites the AST

After all imports are processed, `resolve_names` (`resolve.rs`) rewrites the parsed AST in place, replacing user-visible names with their canonical forms:

- `Var { name: "map" }` -> `Var { name: "Std.List.map" }`
- `Constructor { name: "Just" }` -> `Constructor { name: "Std.Maybe.Just" }`
- `Pat::Constructor { name: "Just" }` -> `Pat::Constructor { name: "Std.Maybe.Just" }`
- `QualifiedName { module: "List", name: "map" }` -> fills `canonical_module: Some("Std.List")`

The pass is **scope-aware**: local bindings shadow imports. The `locals` set tracks names from:
- Function parameters and let bindings
- Lambda parameters and case pattern bindings
- Locally-defined functions, vals, and trait methods
- Record pattern fields (`User { name }` binds `name`)
- String prefix patterns (`"prefix" <> rest` binds `rest`)

Names in the locals set are NOT rewritten, preserving correct shadowing.

### 3. Typechecker lookups (fallback)

After the resolve pass, most names are already canonical. The typechecker's inference pass uses scope_map as a fallback for any names the resolve pass didn't handle:

```rust
// Var lookup: try direct first (works for locals and resolved imports), then scope_map
let env_lookup = env.get(name).or_else(|| env.get(scope_map.resolve_value(name)));
```

Local definitions (function params, let bindings) are found directly by bare name in env. Imports are found by canonical name (which the resolve pass wrote into the AST).

### 4. Specialized resolution

Some name categories have their own resolution beyond the general scope_map:

**Effects** (`resolve_effect` in `effects.rs`): Tries scope_map resolution, then local module prefix, then auto-import for fully-qualified Std names. Effect ops in qualified calls (`File.write!`) are resolved through scope_map in `lookup_effect_op`.

**Traits** (`resolve_trait_name` in `check_traits.rs`): Tries exact match in `trait_state.traits`, then scope_map, then local module prefix. Used for where clauses, impl declarations, and constraint checking. Builtin traits (Num, Eq, Semigroup) stay bare since they have no module.

## Storage: Single-Registration Principle

Each binding is stored once under its canonical name. The ScopeMap handles all user-facing name resolution.

| Category | Storage | Key form |
|----------|---------|----------|
| Values/functions | `env` (TypeEnv) | `"Std.List.map"` |
| Constructors | `constructors` | `"Std.Maybe.Just"` |
| Effects | `effects` | `"Std.Fail.Fail"` |
| Traits | `trait_state.traits` | `"Std.Base.Show"` |
| Types | `type_arity` | `"Maybe"` (bare is canonical for types) |
| Trait methods | `env` | bare (`"show"`) + canonical (`"Std.Base.Show.show"`) |
| Import origins | `scope_map.origins` | canonical -> module |

Trait methods are the exception: they need both bare (for impl bodies where the method is called by bare name) and canonical (for after the resolve pass rewrites Var nodes).

## Import Visibility

| Import form | Qualified access | Bare access |
|-------------|-----------------|-------------|
| `import Logger` | `Logger.greet`, `Logger.Log` | none (except traits and trait methods) |
| `import Logger (greet, Log)` | same as above | `greet`, `Log` |

Traits and their methods are always available from any import — you don't need to expose `Show` to write `impl Show for MyType` or use `show` in a where clause. This matches Haskell's typeclass behavior.

Effects, handlers, functions, types, and constructors require explicit exposing for bare access.

## Effect Registration

Effects use two sub-passes during declaration registration to allow forward references:

1. **Stub pass**: registers all effect names and type params with empty ops
2. **Op pass**: fills in op signatures via `convert_type_expr`

This allows effects in the same module to reference each other (e.g. `Process` referencing `Actor` in Std.Actor).

Effect ops are NOT registered in `scope_map.values` — they use `EffectCall` syntax (`op!`), not `Var` references, so they live in a separate namespace.

## Trait Canonicalization

Trait names follow the same canonical pattern as effects:

- `trait Show` defined in `Std.Base` is registered as `"Std.Base.Show"` in `trait_state.traits`
- Where clause `{a: Show}` resolves `"Show"` to `"Std.Base.Show"` through scope_map
- `impl Show for Int` resolves the trait name before looking up the trait definition
- Scheme constraints carry canonical trait names (e.g. `("Std.Base.Show", var_id, [])`)
- Evidence (`TraitEvidence.trait_name`) uses canonical names
- Builtin traits (Num, Eq, Semigroup) have no module and keep bare names

**Dict naming**: Dict constructor names use canonical trait and type names with dots mangled to underscores (e.g. `__dict_Std_Base_Show_std_int_Std_Int_Int`), built via `typechecker::make_dict_name`. Dict parameter names (for where-clause type variables) use bare trait names since they're local variables: `__dict_Show_a`, not `__dict_Std_Base_Show_a`.

**Well-known trait constants**: The elaborator defines `SHOW`, `DEBUG`, `ORD` constants for canonical names used in special-cased codegen (tuple Show inlining, Ord comparison desugaring).

## Codegen

The codegen resolver (`src/codegen/resolve.rs`) is a separate concern. It runs post-elaboration and maps NodeIds to `ResolvedName` variants (`LocalFun`, `ImportedFun`, `ExternalFun`). It handles canonical Var names by looking up in `qualified_scope` when a name contains `.`.

The lowerer uses `canonicalize_effect` to resolve user-written effect qualifiers (e.g. `"File"` from `File.write!`) to canonical form for handler param lookup.

## Key Files

- `src/typechecker/mod.rs` — `ScopeMap` struct and methods
- `src/typechecker/check_module.rs` — `resolve_import` (builds ScopeMap), `inject_exports` (registers checker state), `collect_codegen_info` (resolves trait/effect names for codegen)
- `src/typechecker/resolve.rs` — AST name rewriting pass (scope-aware, handles all pattern types)
- `src/typechecker/infer.rs` — Var/Constructor/QualifiedName lookups with scope_map fallback
- `src/typechecker/effects.rs` — `resolve_effect`, `lookup_effect_op` (resolves qualifier through scope_map)
- `src/typechecker/check_traits.rs` — `resolve_trait_name`, `register_trait_def` (canonical), `register_impl` (resolves trait name)
- `src/typechecker/check_decl.rs` — where clause processing (resolves trait names), constraint checking (resolves + bare fallback for builtin impls)
- `src/typechecker/patterns.rs` — constructor pattern resolution via scope_map
- `src/typechecker/result.rs` — `CheckResult` with scope_map, `resolve_effect` for LSP
- `src/elaborate.rs` — dict naming (canonical keys, bare param names), trait method dispatch, `SHOW`/`DEBUG`/`ORD` constants
- `src/derive.rs` — handles qualified trait names in `deriving` clauses (strips to bare)
- `src/codegen/lower/effects.rs` — `canonicalize_effect` for effect op qualifier resolution
- `src/lsp/hover/type_display.rs` — uses bare name when recursing into module ASTs for definition summaries
