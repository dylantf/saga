# Effect Type Unification

Effects are integrated into the type system. There is no string-based side-channel.

## Type Representation

```rust
Type::Fun(Box<Type>, Box<Type>, EffectRow)  // param -> return with effects
```

Pure functions have `EffectRow::closed(vec![])`. There is no separate `Arrow` vs `EffArrow` distinction.

`Type::arrow(a, b)` is a convenience constructor for pure functions.

## Computation Types

`infer_expr` returns `(Type, EffectRow)` -- both a value type and the effects the expression performs. Effects compose through:

- **Sequencing**: block effects merge across statements
- **Branching**: if/case effects merge across branches
- **Application**: callee's effect row merges with argument effects
- **Absorption**: effects declared on a HOF parameter type are subtracted
- **Handlers**: `with` subtracts handled effects, adds handler arm effects
- **Lambdas**: body effects go on the `Fun` type's row AND propagate to the enclosing scope

## Where Effects Live on Curried Functions

Effects go on the innermost arrow (the one closest to the return type):

```
fun greet : String -> String -> Unit needs {Log}
=> Fun(String, Fun(String, Unit, {Log}), {})
```

Partial application `greet "hi"` returns `Fun(String, Unit, {Log})` -- effects preserved until saturation.

## Effect Subtyping

A function with fewer effects can be used where more effects are allowed. In row unification, when both rows are closed and one side's extras are empty, unification succeeds. A pure function can be passed where an effectful callback is expected.

## What Was Removed

The entire string-based side-channel:

- `EffectState.current: HashSet<String>` -- replaced by `EffectRow` returned from `infer_expr`
- `EffectState.fun_effects: HashMap<String, HashSet<String>>` -- replaced by `known_funs: HashSet<String>`
- `EffectState.let_bindings: HashMap<String, Vec<String>>` -- replaced by `known_let_bindings: HashSet<String>`
- `EffectState.fun_has_row_var: HashMap<String, Option<u32>>` -- deleted
- `enter_effect_scope()` / `exit_effect_scope()` -- replaced by `enter_scope()` / `exit_scope()` (saves non-effect state only)
- `EffectScope.effects` / `EffectScopeResult.effects` -- deleted
- `commit_callee_effects()` -- deleted
- `callee_effects()` -- deleted
- `check_undeclared_effects()` -- replaced by `check_effects_via_row()`
- `build_body_effect_row()` -- deleted
- `ModuleExports.fun_effects` -- replaced by `effectful_funs: HashSet<String>`
- Codegen supplement logic -- types are authoritative

## What Remains in EffectState

- `type_param_cache` -- ensures effect ops from the same effect share type vars within a scope
- `fun_type_constraints` -- concrete type args from annotations like `needs {State Int}`
- `declared_effect_rows` -- for zero-param effectful functions whose types can't carry `EffectRow`
- `known_funs` / `known_let_bindings` -- name registries for the unnecessary handler warning
- `CheckResult.fun_effects` and `let_effect_bindings` are derived from resolved types at the boundary
