# Remove known_funs / known_let_bindings registries

## Background

`EffectMeta` has two fields that are no longer used for effect tracking:

- `known_funs: HashSet<String>` -- all locally defined function names
- `known_let_bindings: HashSet<String>` -- let bindings with deferred effects

These used to gate which functions had their effects committed during
inference. After the accumulator refactor, effect tracking is handled
entirely by `self.effect_row` (accumulation) and the two absorption
sites (call-site in `infer.rs`, boundary in `check_fun_clauses`).

## Current usage

Both fields are write-only from the typechecker's perspective. They're
populated during declaration checking but never read for effect decisions.

The only readers are in `result.rs`, where they're used to build
`CheckResult.fun_effects` and `CheckResult.let_effect_bindings` for
codegen. Codegen uses these to decide which functions need the CPS
transform for effect handling.

## What to do

Codegen could derive effect info directly from resolved types using
`effects_from_type()` instead of relying on a pre-built registry.
The change would be:

1. Remove `known_funs` and `known_let_bindings` from `EffectMeta`
2. Remove all the `.insert()` calls in `check_decl.rs`, `check_traits.rs`,
   `check_module.rs`, and `infer.rs`
3. In `result.rs`, instead of iterating over `known_funs` to build
   `fun_effects`, iterate over all names in the type env and check
   their resolved types with `effects_from_type()`
4. Same for `let_effect_bindings`

This is a codegen-boundary refactor, not a typechecker change. No
effect tracking behavior changes. The risk is low but it touches the
typechecker-to-codegen interface, so verify codegen integration tests
pass (`cargo test --test codegen_integration`).
