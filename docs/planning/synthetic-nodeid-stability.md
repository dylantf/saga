# Synthetic `NodeId` Stability

## Summary

We have a recurring compiler problem:

- typechecking records information by AST `NodeId`
- later passes rebuild parts of the AST with fresh synthetic `NodeId`s
- lowering or other downstream passes then look up metadata for the "same"
  source expression and get nothing

This does not break every feature, because many lowering paths do not depend on
per-node type metadata. But when they do, the failures are subtle and tend to
show up far away from the original cause.

The recent handler-record bug is one instance of this broader issue, not the
final resolution of it.

## The Concrete Bug We Hit

A project like this failed during lowering:

```dy
let db = connect config
let pg = db.postgres
let tx = db.transactions
...
} with {pg, tx, console}
```

where:

- `connect` returned a record containing `Handler Postgres` and
  `Handler Transaction`
- `pg` and `tx` were local bindings extracted from record fields
- the computation was wrapped by a trailing `with {pg, tx, console}`

The panic looked like:

```text
internal lowering error: unknown handler item 'tx' (canonical: tx)
```

## Root Cause

There were actually three separate issues interacting:

1. `FieldAccess` expressions like `db.transactions` were rebuilt during
   elaboration/normalization with fresh synthetic `NodeId`s.
2. Lowering wanted to use typechecker metadata to recognize that these
   expressions had type `Handler ...`.
3. Trailing `with` lowering only pre-registered local handler bindings from the
   immediately wrapped expression, so outer handler layers in
   `with {pg, tx, console}` stopped seeing the original block-local bindings.

The first issue is the synthetic-`NodeId` problem. The third is a separate bug
in handler composition over nested `with` layers.

## What We Changed

### 1. Preserve `NodeId` for Semantics-Preserving Rebuilds

We added:

```rust
Expr::rebuild_like(expr, new_kind)
```

and used it in places where the compiler is still talking about the same source
expression but rebuilding children or attaching resolved metadata.

In this fix, that covered:

- `FieldAccess`
- `RecordUpdate`

inside:

- `elaborate.rs`
- `codegen/normalize.rs`

This lets downstream passes continue to use `type_at_node` for those
expressions.

### 2. Use Module-Specific `CheckResult` for Project `Main`

Project-mode `Main` lowering was sometimes using the aggregate top-level
`CheckResult` instead of the module-specific result. That meant even preserved
`NodeId`s could still miss the right per-node type table.

The build pipeline now prefers:

- `result.module_check_results().get(module_name)`

and only falls back to the top-level result when needed.

### 3. Pre-Register Local Handler Bindings Through Nested `with`

For:

```dy
block with {pg, tx, console}
```

surface syntax is lowered as nested handler layers. The local-binding scan must
be able to walk back through nested `With` wrappers to reach the original
`Block`, otherwise only the innermost handler sees local `let pg = ...` /
`let tx = ...`.

That bug was fixed in lowering separately from the `NodeId` work.

## What This Fix Does Not Solve

This does **not** fully solve synthetic `NodeId` drift across the compiler.

Today there are still many `Expr::synth(...)` calls in:

- `src/elaborate.rs`
- `src/codegen/normalize.rs`

Many of those are correct, because they introduce genuinely new expressions.
But some are semantics-preserving rebuilds and therefore potential future
metadata drift bugs.

So the current state is:

- this specific handler-field bug is fixed
- the compiler now has a clean mechanism (`rebuild_like`) for preserving
  identity where appropriate
- the overall synthetic-identity problem remains broader than this one fix

## Practical Rule of Thumb

When rewriting the AST after typechecking:

- use `Expr::rebuild_like(old, new_kind)` if the new node is still the same
  source expression, just with transformed children or attached metadata
- use `Expr::synth(...)` only when introducing a genuinely synthetic node that
  did not exist in source

Examples that usually want `rebuild_like`:

- attaching resolved record names
- rebuilding field access after recursively elaborating its base expression
- rebuilding record update after recursively elaborating children
- normalization that preserves the outer expression and only rewrites its
  subexpressions

Examples that usually want `synth`:

- inserted dictionary lookups
- generated wrapper lambdas
- lifted temporary expressions
- desugared helper expressions that did not exist in source

## Suggested Follow-Up

### Short Term

Audit `elaborate.rs` and `codegen/normalize.rs` for uses of `Expr::synth` that
are actually identity-preserving rewrites.

Good first targets:

- tuple rebuilds
- record creates
- handler expressions whose outer identity should remain stable
- simple expression wrappers that only recurse into children

### Medium Term

Define a compiler-wide invariant:

- after typechecking, any pass that preserves the semantic identity of a source
  expression must preserve its `NodeId`

That makes downstream metadata consumers much easier to reason about.

### Long Term

If this keeps recurring even after an audit, consider a more explicit split
between:

- source/origin identity
- synthetic node identity

For example, expressions could carry both:

- a current node id
- an optional origin/source node id

Then metadata like `type_at_node` could key off source identity while still
allowing later passes to create fresh structural nodes freely.

## Regression Targets

Any future work here should keep tests for:

- single-file handler bindings extracted from record fields
- imported-module handler bindings extracted from record fields
- trailing `with {a, b, c}` over a block with local handler bindings
- project `Main` lowering using imported handler bundles

These are the cases most likely to regress if identity preservation drifts
again.
