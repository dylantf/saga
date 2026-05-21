# CPS-Chaining Composite Expressions in the Lowerer

## Status

**Phases 1 + 2 landed.** A single `lower_with_cps_slots` helper (plus the
`lower_bind_expr_with_cps` primitive it composes from) handles
CPS-chaining of effectful sub-expressions across every composite form
the lowerer assembles in tail position. Eight `_in_*_abort_correctly`
regression tests in [tests/module_codegen_integration.rs](../../tests/module_codegen_integration.rs)
cover each shape end-to-end on BEAM.

Phase 3 (structural fix via a generic sub-expression visitor) is
deferred and folds naturally into the "lowering-mode surface cleanup"
work already noted at the bottom of
[plans/effectful-call-detection-plan.md](plans/effectful-call-detection-plan.md).

## Motivation

A recurring bug class showed up in the lowerer: a composite expression
(constructor call, tuple literal, binop, record update, field access,
`if`-cond, `case`-scrutinee, …) lowered each of its sub-expressions
in **value mode** via `lower_expr_value`. For pure sub-expressions
that's fine. For an effectful sub-expression that can abort (e.g. a
call to a function performing `Fail`), value-mode lowering hands the
sub-expression an **identity continuation**. When the handler aborts,
the abort tuple (`{error, _}`) propagates synchronously back as the
sub-expression's "return value," gets bound into the composite, and
then the outer return clause wraps the whole composite — yielding e.g.
`Ok (Just (Err Boom))` instead of `Err Boom`, or a runtime crash when
the abort tuple is fed to `erlang:element/2`, `erlang:+/2`, or matched
against `true`/`false`.

The fix shape is the same at every site: when a composite has any
effectful sub-expression, lower it as a CPS chain where each effectful
sub-expression's continuation contains "build the rest of the
composite, then apply the outer K." If the handler aborts, that
continuation is discarded and the abort propagates through the call
chain to the nearest `with` boundary.

This document captures that shape as a reusable primitive so future
composite forms inherit the correct behavior by construction.

## Pre-refactor state

Before the refactor, six near-identical helpers existed:

- `lower_ctor_with_k` (ADT constructor calls — `Just (eff x)`)
- `lower_tuple_with_k` (tuple literals — `(eff x, 42)`)
- `lower_binop_with_k` (binops — `eff x + 100`)
- `lower_record_create_with_k` (record creation — `R { f: eff x }`)
- `lower_record_update_with_k` (record updates — `{ r | f: eff x }`)
- `lower_field_access_with_k` (field access — `(eff x).field`)

Each helper independently:

1. Walked its sub-expressions, classifying pure vs effectful.
2. Allocated fresh variable names per sub-expression.
3. Lowered pure sub-expressions and collected let-bindings.
4. Built the composite's "result value" CExpr from the variables —
   the only per-site difference.
5. Wrapped with `apply k_var(result)`.
6. Folded effectful sub-expressions inside-out as nested continuations.
7. Wrapped pure let-bindings outside.

Steps 1, 2, 3, 5, 6, 7 were copy-pasted. Step 4 was the actual semantic
content. The duplication made adding the next composite form a
template-instantiation exercise — and easy to forget.

Two adjacent bugs went undetected until this refactor:

- `if (eff x) then ... else ...` — the cond was lowered value-mode;
  abort crashed `case` with "no matching clause" because `{error, _}`
  isn't `true` or `false`.
- `case (eff x) { ... }` — the scrutinee was lowered value-mode; abort
  silently fell through to the wildcard arm with the abort tuple.

These were the same bug class at sites no one had thought to write a
helper for, because the per-site boilerplate raised the activation
energy for each new fix.

## Primitive: `lower_bind_expr_with_cps`

The single load-bearing operation:

```rust
fn lower_bind_expr_with_cps(
    &mut self,
    expr: &Expr,
    var_name: String,
    expected: Option<Type>,
    body: CExpr,
) -> CExpr
```

Semantics: bind `expr`'s value to `var_name` for use in `body`. If
`expr` is effectful (per `expr_is_effectful_call` or
`has_nested_effectful_expr`), CPS-chain it so an aborting handler
bypasses `body` entirely. Otherwise emit a plain `let`.

This is the *only* place in the lowerer that decides "do I let-bind
this, or do I CPS-chain it?" Everything else builds on this.

## Composer: `lower_with_cps_slots`

For composite expressions whose final form is `apply k(some_value)`:

```rust
fn lower_with_cps_slots<F>(
    &mut self,
    slots: Vec<CpsSlot<'_>>,
    k_var: &str,
    build: F,
) -> CExpr
where
    F: FnOnce(&mut Self, &[String]) -> CExpr,

enum CpsSlot<'e> {
    /// Pre-lowered value (e.g. `element(idx, rec_var)` for an
    /// untouched record-update field). Bound to a plain `let`.
    Pure(CExpr),
    /// Source expression. CPS-chained if effectful; otherwise lowered
    /// as a value with the optional expected type.
    Expr { expr: &'e Expr, expected: Option<Type> },
}
```

The helper:

1. Allocates one fresh variable per slot.
2. Runs `build` to assemble the composite using those variables.
3. Wraps the result in `apply k_var(result)`.
4. Walks slots right-to-left, wrapping the accumulated body with
   either a `let` (for `Pure` slots and non-effectful `Expr` slots) or
   a CPS chain (for effectful `Expr` slots) via
   `lower_bind_expr_with_cps`.

Evaluation order is left-to-right (slot 0 evaluates first). Effectful
and pure slots interleave naturally because the wrapping is uniform.

## Per-site usage

Every helper is now a few lines: build the slot list, hand a closure to
`lower_with_cps_slots`. Examples:

```rust
// Tuple literal: one Expr slot per element.
pub(super) fn lower_tuple_with_k(&mut self, elems: &[Expr], k_var: &str) -> CExpr {
    let slots = elems.iter()
        .map(|e| CpsSlot::Expr { expr: e, expected: None })
        .collect();
    self.lower_with_cps_slots(slots, k_var, |_, vars| {
        CExpr::Tuple(vars.iter().map(|v| CExpr::Var(v.clone())).collect())
    })
}

// Field access: one Expr slot, build a single element/2 call.
pub(super) fn lower_field_access_with_k(
    &mut self, record_expr: &Expr, field_idx: i64, k_var: &str,
) -> CExpr {
    self.lower_with_cps_slots(
        vec![CpsSlot::Expr { expr: record_expr, expected: None }],
        k_var,
        |_, vars| cerl_call("erlang", "element",
            vec![CExpr::Lit(CLit::Int(field_idx)), CExpr::Var(vars[0].clone())]),
    )
}
```

Sites that aren't `apply k(value)` (e.g. `if` and `case`, where K is
threaded into branches) call `lower_bind_expr_with_cps` directly:

```rust
ExprKind::If { cond, then_branch, else_branch, .. } => {
    let cond_var = self.fresh();
    let then_ce = self.lower_branch_with_k(then_branch, k_var);
    let else_ce = self.lower_branch_with_k(else_branch, k_var);
    let case = CExpr::Case(Box::new(CExpr::Var(cond_var.clone())), vec![/* arms */]);
    self.lower_bind_expr_with_cps(cond, cond_var, None, case)
}
```

`lower_short_circuit_with_k` (the `&&` / `||` path of binop) does the
same: build a `case` on the left, then bind the left via the primitive.

## Record update: composing primitive + composer

Record update needs both layers because the base record (CPS-chained
via the primitive) must be in scope before any field slot evaluates:

```rust
let rec_var = self.fresh();
let slots = /* [tag-via-element-1, field_0, field_1, ...] */;
let inner = self.lower_with_cps_slots(slots, k_var, |_, vars| {
    CExpr::Tuple(vars.iter().map(|v| CExpr::Var(v.clone())).collect())
});
self.lower_bind_expr_with_cps(record_expr, rec_var, None, inner)
```

Pure slots reference `rec_var` by name — it's bound by the outer wrap
when the inner CExpr is evaluated. This composition pattern is the
template for any composite that needs scoped state across slots.

## Detection: `has_nested_effectful_expr`

Detection is still per-`ExprKind`. The predicate
`has_nested_effectful_expr` answers "does this expression contain any
effectful sub-expression?" and the `lower_expr_with_k_inner` dispatcher
uses it to decide whether to take the CPS path or the value path.

When adding a new `ExprKind`, two things must be updated:

1. `has_nested_effectful_expr` — add a branch that walks the new
   ExprKind's sub-expressions, calling `branch_is_effectful` on each.
2. `lower_expr_with_k_inner` — add a match arm for the new ExprKind
   that calls `lower_with_cps_slots` or `lower_bind_expr_with_cps`.

This is **not** structural — it's audit-based. See Phase 3 below for
the structural fix.

## What's covered

Every regression test asserts both abort (`Err _`) and success
(`Ok _`) on a BEAM round-trip. Sites covered:

| Site | Helper | Regression test |
|---|---|---|
| ADT constructor arg | `lower_ctor_with_k` | `_in_ctor_arg_abort_correctly` |
| Tuple element | `lower_tuple_with_k` | `_in_tuple_elem_abort_correctly` |
| Binop operand | `lower_binop_with_k` | `_in_binop_operand_abort_correctly` |
| Record-create field | `lower_record_create_with_k` | `_in_record_field_abort_correctly` |
| Record-update field | `lower_record_update_with_k` | `_in_record_update_abort_correctly` |
| Field access | `lower_field_access_with_k` | `_in_field_access_abort_correctly` |
| `if` condition | (direct) `lower_bind_expr_with_cps` | `_in_if_cond_abort_correctly` |
| `case` scrutinee | (direct) `lower_bind_expr_with_cps` | `_in_case_scrutinee_abort_correctly` |

List literals are covered transitively — they desugar to `Cons` chains
before lowering, so the constructor helper applies recursively.

## Phase 3 (deferred): structural fix via sub-expression visitor

The remaining audit step — extending `has_nested_effectful_expr` and
`lower_expr_with_k_inner` for each new `ExprKind` — is the last manual
mirroring left. A structural fix would expose every `ExprKind`'s
sub-expressions through a uniform visitor, and have the lowerer
automatically CPS-chain effectful ones at every tail position without
per-kind arms.

This belongs with the "lowering-mode surface cleanup" already noted at
the bottom of
[plans/effectful-call-detection-plan.md](plans/effectful-call-detection-plan.md)
— consolidating the eight overlapping dispatchers (`lower_expr_value`,
`_tail`, `_with_call_return_k`, `_with_installed_return_k`,
`_terminal_effectful_*_with_return_k`, `_to_k`,
`lower_handler_owned_expr`) would touch the same code paths. Doing
both together is the natural unit of work.

Reasons to defer:

- The eight existing composite sites cover every shape that appears
  in real Saga code today. The bug class is no longer recurring at
  practical sites — both `if`/`case` (which had silently been buggy
  before this refactor) are now fixed, and the remaining gaps are
  hypothetical.
- A sub-expression visitor requires every `ExprKind` variant to
  describe its children uniformly, which is itself a refactor of the
  AST traversal layer.
- The eight composite helpers fit on one page now. Adding the next
  composite shape (e.g. bitstring segment values, if/when that gets a
  real-world repro) is a 5-line patch + test.

Track when to revive: if a new bug in this class shows up at a site
the audit missed, OR when "lowering-mode surface cleanup" kicks off.

## Acceptance

The refactor is done when:

- ✅ `lower_with_cps_slots` and `lower_bind_expr_with_cps` exist and
  are the *only* places the CPS-chaining decision lives.
- ✅ All six original composite helpers are reduced to a few lines
  each, delegating to the primitive/composer.
- ✅ `if` and `case` use `lower_bind_expr_with_cps` directly for
  cond/scrutinee.
- ✅ Eight `_in_*_abort_correctly` regression tests pass on BEAM,
  covering each shape.
- ✅ `cargo test` and `cargo clippy` clean.

For Phase 3, the design above is the spec to revisit when "lowering-
mode surface cleanup" begins. It is not a commitment to land
independently.
