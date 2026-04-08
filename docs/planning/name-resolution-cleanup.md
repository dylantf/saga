# Name Resolution Cleanup

## Status

Planned

## Why

The recent handler canonicalization work is functionally correct and covered by tests, but the logic is now spread across a few places:

- `src/typechecker/resolve.rs`
- `src/typechecker/check_module.rs`
- `src/typechecker/handlers.rs`
- `tests/module_codegen_integration.rs`

This makes the rules harder to change safely, especially for:

- handler-name canonicalization
- effect qualifier canonicalization
- import visibility registration
- builtin handler detection (`ets_ref`, `beam_vec`)

## Goals

1. Keep the current behavior exactly the same.
2. Make canonicalization rules live in fewer places.
3. Reduce stringly-typed special cases where practical.
4. Make future namespace additions less copy-paste heavy.

## Non-Goals

- Changing language behavior
- Reworking the compiler pipeline
- Replacing `ScopeMap` with a new abstraction
- Refactoring unrelated `DateTime` work

## Refactor Targets

### 1. Extract resolver helpers in `resolve.rs`

The following patterns are duplicated today:

- rewrite a handler name through `scope.resolve_handler(...)`
- rewrite an effect qualifier through `scope.resolve_effect(...)`
- only rewrite when the name is not shadowed by locals

Extract small helpers such as:

```rust
fn canonicalize_handler_name_in_place(
    name: &mut String,
    scope: &ScopeMap,
    locals: &HashSet<String>,
)

fn canonicalize_effect_qualifier_in_place(
    qualifier: &mut Option<String>,
    scope: &ScopeMap,
)
```

Use them in:

- named `with` handlers
- inline named handlers
- inline handler arm qualifiers
- handler body arm qualifiers
- `EffectCall` qualifiers

### 2. Extract import-scope registration helpers in `check_module.rs`

`resolve_import(...)` currently hand-rolls similar logic for:

- effects
- handlers
- values
- constructors
- exposed bare names

Extract a helper for the common “canonical + alias-qualified + optional bare” shape.

Possible direction:

```rust
fn register_import_name(
    map: &mut HashMap<String, String>,
    canonical: String,
    alias_qualified: Option<String>,
    bare: Option<String>,
)
```

or a pair of narrower helpers:

- one for qualified forms
- one for exposed bare forms

The main goal is to make handlers/effects/values read as policy, not map mutation noise.

### 3. Centralize builtin handler recognition

The ETS/vec init flags are currently keyed off handler names.

Move that logic behind one helper instead of open-coded string checks. For example:

```rust
fn is_builtin_handler(name: &str, bare: &str) -> bool
```

or a more explicit version:

```rust
fn is_ets_ref_handler(name: &str) -> bool
fn is_beam_vec_handler(name: &str) -> bool
```

If possible, prefer canonical-aware checks over suffix matching spread across the codebase.

### 4. Reduce test harness drift

`tests/module_codegen_integration.rs` now reconstructs more of the real compiled-module pipeline so imported named handlers work during lowering.

That is good, but it can drift from production behavior.

Consider extracting a reusable helper used by both:

- the integration test harness
- the real build/test pipeline

The helper should produce `CompiledModule` entries with:

- `codegen_info`
- elaborated program
- normalized program
- resolution map

## Suggested Order

1. Extract `resolve.rs` helpers first.
2. Extract builtin-handler detection helper.
3. Extract `resolve_import(...)` registration helpers.
4. Only then consider sharing the compiled-module test helper.

This keeps the behavior-preserving changes small and reviewable.

## Acceptance Criteria

- No behavioral changes.
- `cargo test --test module_codegen_integration`
- `cargo test e2e_test_suite -- --nocapture`
- Existing handler canonicalization scenarios still pass:
  - alias-qualified named handler
  - exposed bare named handler
  - canonicalized effect qualifiers in `EffectCall`
  - `ets_ref` and `beam_vec` still trigger their required runtime init paths

## Nice-to-Have Follow-Up

After the cleanup lands, update:

- `docs/name-resolution.md`

to mention the handler namespace explicitly in the `ScopeMap` example and any new helper structure if that improves readability for future contributors.
