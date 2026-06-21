# Repro: derived-subquery dispatch (trait dicts + nested handler + outer HOF)

Reproduces the `from_subquery` runtime crash (`prolific_authors_query`) with **no
Kraken dependency** — pure `Std.Generic` + a hand-rolled effect.

```
saga run
```

With the fix in place this prints:

```
derived subquery column: x
```

Before the fix it crashed while building the `Prepared`, with `col2_name`
hitting a `case_clause` (the subquery result was garbage).

## The trigger

The crash needs **four** things together. Earlier minimal repros had only the
first three and *passed*, which is why the bug looked fixed but Kraken still
crashed:

1. A function (`from_sub`) carrying **trait-dictionary parameters** — from the
   `BScope`/`Generic` constraints of a generic-rep transform (mirrors Kraken's
   `derived_columns` / `DerivedScope`).
2. It **runs a nested handler of the same effect** (`make () with h`) before the op.
3. It then **performs an op** (`bindd!`) whose argument captures a **closure that
   uses those dictionary params** (`fun alias -> derived_cols selection`).
4. `from_sub`'s result is bound **UNANNOTATED** (`let t = from_sub (...)`) and then
   used by a trailing op — here inside an outer `query` HOF, as real Kraken calls
   `from_subquery` inside `Query.query (fun () -> ...)`.

## Why it crashed

`from_sub`'s result type is determined only by `Generic`'s **reverse** bijection
(rep → record type). The let-generalization guard only knew *forward* fundeps, so
the unannotated `t` was generalized over its `Generic` dictionary into a
dict-lambda. That puts `from_sub` in **value position**, so it's lowered with an
**identity continuation** — `bindd!` returns its raw `Step` instead of running the
captured closure, and `t.x` is garbage.

The earlier minimal repros masked it by **annotating** the binding
(`let t : { x: Col2 Int } = ...`) or handling QB **directly** (no outer HOF), both
of which pin `t` and avoid the generalization.

## The fix

`fundep_determined_vars` (`src/typechecker/infer.rs`) now (a) treats an anonymous
record as a concrete fundep determinant, and (b) runs `Generic` in reverse — a
`Generic self rep` whose `rep` is determined pins `self`. So the unannotated `t`
stays monomorphic, `from_sub` is lowered in CPS (real continuation) position, and
`bindd!` dispatches correctly.

Regression test:
`tests/effect_property_tests.rs::unannotated_derived_subquery_result_is_not_generalized`.
