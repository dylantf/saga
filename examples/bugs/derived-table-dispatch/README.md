# Minimal self-contained repro: effect-op dispatch + trait dicts + nested handler

Reproduces the `from_subquery` runtime crash (`prolific_authors_query`) with **no
Kraken dependency** — pure `Std.Generic` + a hand-rolled effect.

```
saga run
```

```
control (no nested handler): x
Runtime error: bad argument
  lib:from_sub/6
```

## The trigger

It is **not** cross-module, and **not** the effect's shape (op count, polymorphism,
nesting, state type were all ruled out by faithful ports that pass). The crash needs
all three of these together:

1. A function (`from_sub`) carrying **trait-dictionary parameters** — here from the
   `BScope`/`Generic` constraints of a generic-rep transform (mirrors Kraken's
   `derived_columns` / `DerivedScope`). Note the arity: `lib:from_sub/6` — those are
   the dict params.
2. That function **runs a nested handler of the same effect** (`make () with h`)
   before performing the op.
3. It then **performs an effect operation** (`bindd!`) whose argument captures a
   **closure that uses those dictionary params** (`fun alias -> derived_cols selection`).

`bindd!` then fails to dispatch (in the real Kraken trace it returns its raw
`QueryStep` continuation and the `make_scope` closure never runs).

## The control (passes)

`from_sub_direct` is identical but takes the selection directly — **no nested
handler** — and works. Removing the nested handler, or the trait-dict params (a
plain `from (to selection)` with only `Generic`), both make the crash disappear.

## Ruled out (all pass as faithful ports in git history of this dir)

- Cross-module effect/handler/driver split (3-op and 11-op).
- Full 11-op `QueryBuild`-shaped effect with realistic threaded state record.
- Polymorphic ops, the two-FROM guard, alias prefixes, `DerivedTable {frag,
  make_scope}` record through the op.
- `make_scope` doing a plain Generic `from (to selection)` round-trip.

The differentiator that finally reproduced it was replacing the plain Generic
round-trip with a **trait-method** transform (`BScope`, a fundep trait over the
Generic rep), which adds the dictionary params to `from_sub`.
