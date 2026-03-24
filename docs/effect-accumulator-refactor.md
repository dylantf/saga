# Effect accumulator refactor

## Problem

`infer_expr` returns `(Type, EffectRow)`. Every call site must manually merge
the returned effects, and Rust happily lets you write `let (ty, _effs) = ...`
which silently drops them. We found this bug in 6 expression forms (BinOp,
UnaryMinus, Resume, Tuple, Ascription, Receive arm bodies).

The `infer_and_merge` helper prevents the pattern but doesn't fix the
underlying issue: effect accumulation is opt-in at every call site instead
of automatic.

## Proposed fix

Replace the returned `EffectRow` with an accumulator on the Checker:

```rust
struct Checker {
    // ...
    effect_row: EffectRow,  // accumulates effects for current scope
}
```

`infer_expr` goes back to returning just `Type`. Effect calls, function
applications, and other effect-producing expressions push onto
`self.effect_row` directly. This is what the old `current: HashSet<String>`
was, but using a typed `EffectRow` instead of loose strings.

### Scope isolation

Forms that need isolated effect tracking (handlers, lambdas, local fun decls)
save and restore the accumulator:

```rust
// Handler: isolate inner effects, then subtract handled ones
let saved = std::mem::replace(&mut self.effect_row, EffectRow::empty());
let ty = self.infer_expr(inner)?;
let inner_effs = std::mem::replace(&mut self.effect_row, saved);
let remaining = inner_effs.subtract(&handled_effects);
self.effect_row = self.effect_row.merge(&remaining);

// Lambda: isolate body effects, put them on the function type
let saved = std::mem::replace(&mut self.effect_row, EffectRow::empty());
let body_ty = self.infer_expr(body)?;
let body_effs = std::mem::replace(&mut self.effect_row, saved);
// body_effs go on the innermost arrow, not merged into outer scope
```

### What changes

- `infer_expr` returns `Result<Type, Diagnostic>` instead of `Result<(Type, EffectRow), Diagnostic>`
- All the manual merge points (BinOp, If, Case, Block, Tuple, etc.) disappear.
  Effects auto-accumulate.
- Handler, lambda, and local fun isolation becomes explicit save/restore.
- `check_fun_clauses` reads `self.effect_row` after body inference instead of
  receiving it as a return value.

### What stays the same

- `Type::Fun(param, ret, EffectRow)` -- types still carry effect rows.
- Row unification, effect subtyping, absorption -- all unchanged.
- `EffectMeta` (type_param_cache, known_funs, etc.) -- unchanged.

### known_funs gating

The `known_funs` / `known_let_bindings` check that prevents callback parameter
effects from being committed remains necessary with this approach. The
accumulator doesn't solve the "whose effects are these" question -- it just
makes accumulation automatic. Removing `known_funs` would require a
row-variable-per-scope approach where the scope's row variable unifies with
call site effect rows, letting the type system handle absorption. That's a
larger change.

## Scope

Mechanical refactor of inference plumbing. Type representations and all
external behavior stay identical. Estimated ~50 call sites change from
`let (ty, effs) = self.infer_expr(e)?; merged.extend(effs)` to
`let ty = self.infer_expr(e)?;` with ~5 isolation points added.
