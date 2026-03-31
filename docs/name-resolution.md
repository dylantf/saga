# Name Resolution Refactor

## Problem

The typechecker currently handles name resolution and scoping inline during import injection. When a module is imported, `inject_exports` and `inject_scoped_bindings` (~300 lines in `check_module.rs`) register every binding under multiple name forms:

- **Canonical**: `Std.List.map`
- **Aliased**: `List.map`
- **Bare/exposed**: `map`

Every piece of per-name metadata (type scheme, def_id, doc_comments, import_origins, etc.) must be registered under all applicable forms. This is error-prone — adding a new piece of metadata means touching every registration path. The doc_comments bug (stored by bare name only, causing collisions across modules) is a direct consequence.

## Proposed Solution

Add a **pre-typecheck name resolution pass** that runs between Desugar and Typecheck:

```
Parse -> Derive -> Desugar -> Resolve Names -> Typecheck -> Elaborate -> ...
```

The resolver would:

1. Process all `import` declarations to build a scope map:
   - `"map"` => `"Std.List.map"`
   - `"List.map"` => `"Std.List.map"`
   - `"Std.List.map"` => `"Std.List.map"`
2. Walk the AST and rewrite (or annotate) every name reference to its canonical form

After resolution, the typechecker's `TypeEnv` only needs one entry per canonical name, `imported_docs` only needs one entry, `def_ids` only needs one entry, etc.

## Why This Works for Our Language

In some languages (Rust, Haskell), which name a reference resolves to can depend on its type — e.g. `x.foo()` in Rust dispatches based on the type of `x`, requiring type inference to complete resolution. Name resolution and type inference must be interleaved.

In our language, name visibility is purely structural — determined by module imports, `exposing` clauses, and lexical scope. `show` always resolves to `Show.show` regardless of the argument type. The question of *which implementation* runs is answered later by elaboration (dictionary passing), not by name resolution. So a pre-typecheck resolve pass can do the entire job with just import structure and lexical scoping rules.

## Scope of Work

### Core work
- New resolver pass (~300-500 lines) that builds a scope map from imports and rewrites/annotates names
- Gut `inject_exports` + `inject_scoped_bindings` in `check_module.rs` (~300 lines removed/simplified)
- Light touch on `infer.rs` (`QualifiedName` handling, ~40 lines) and `unify.rs` (`convert_type_expr` type alias resolution, ~25 lines)

### Unchanged
- **`TypeEnv`** — already just `HashMap::get`, no multi-form logic
- **`check_decl.rs`** — only registers local names
- **LSP code** — consumes `import_origins`/`type_import_origins` after the fact, doesn't care who populated them
- **Codegen `resolve.rs`** — different concern (maps NodeIds to Erlang call targets post-elaboration)

### Multi-module ordering

`typecheck_import` already typechecks dependencies in order. The resolver slots into the existing loop — after a dependency is typechecked and its exports collected, the resolver rewrites the current module's names to canonical form before typechecking it:

```
for each module (in dependency order):
  1. typecheck dependency (unchanged)
  2. collect its exports (unchanged)
  3. resolve names in current module's AST (new — replaces multi-form injection)
  4. typecheck current module (simplified — canonical names only)
```

## Relationship to Existing Resolve Pass

The codegen resolver (`src/codegen/resolve.rs`) is a separate concern. It runs post-elaboration and maps NodeIds to `ResolvedName` variants (`LocalFun`, `ImportedFun`, `ExternalFun`) with Erlang-specific info (module atoms, arities, effects). It answers "what Erlang call target does this node map to?" — a codegen question, not a scoping question.

The scope management patterns in codegen resolve (scope stack, local variable tracking) are conceptually similar but the output format is lowerer-specific. The pre-typecheck resolver would use similar patterns but return typechecker-compatible name bindings.
