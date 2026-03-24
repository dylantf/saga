# Effect Type Unification

Effects are integrated into the type system. Every function type carries an effect row.

## Type Representation

```rust
Type::Fun(Box<Type>, Box<Type>, EffectRow)  // param -> return with effects
```

Pure functions have `EffectRow::closed(vec![])`. There is no separate `Arrow` vs `EffArrow` distinction.

`Type::arrow(a, b)` is a convenience constructor for pure functions.

## Where Effects Live on Curried Functions

Effects go on the innermost arrow (the one closest to the return type):

```
fun greet : String -> String -> Unit needs {Log}
=> Fun(String, Fun(String, Unit, {Log}), {})
```

Partial application `greet "hi"` returns `Fun(String, Unit, {Log})` -- effects preserved until saturation.

## Effect Subtyping

A function with fewer effects can be used where more effects are allowed. In row unification, when both rows are closed and one side's extras are empty, unification succeeds. This means a pure function can be passed where an effectful callback is expected.

## Removed Side-Channel

The following string-based tracking was removed:

- `fun_effects: HashMap<String, HashSet<String>>` -> `known_funs: HashSet<String>` (name-only)
- `let_bindings: HashMap<String, Vec<String>>` -> `known_let_bindings: HashSet<String>` (name-only)
- `fun_has_row_var: HashMap<String, Option<u32>>` -> deleted (open rows detected via `EffectRow.tail`)
- `commit_callee_effects()` -> deleted (effects read from callee's `Fun` type)
- `callee_effects()` -> deleted
- `check_undeclared_effects()` -> replaced by `check_effects_via_row()`

## What Remains

- `current: HashSet<String>` accumulates effect names within a body scope. This is a computation-level tracker (effects are properties of computations, not values), checked against the declared `EffectRow` at function boundaries via `check_effects_via_row()`.
- `known_funs` / `known_let_bindings` gate the type-directed effect commit at call sites, preventing callback parameter effects from being committed to the enclosing function.
- `declared_effect_rows` stores the `EffectRow` from annotations for zero-param effectful functions whose types aren't arrows and thus can't carry the row.
- `CheckResult.fun_effects` and `CheckResult.let_effect_bindings` are derived from resolved types at the boundary (for codegen).
