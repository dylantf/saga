# Nested Handler Semantics

## Summary

This proposal changes `with {...}` from a merged-handler construct into pure
syntax sugar for nested handlers.

```dy
expr with {a, b, c}
```

desugars to:

```dy
((expr with a) with b) with c
```

using lexical order.

This aligns stacked `with`s and list `with`s under one rule:

- handler order is explicit and semantically meaningful
- operations are handled by the nearest matching handler in that order
- unhandled operations propagate outward
- `return` clauses apply at each handler boundary
- inline handlers and named handlers become the same kind of ordered item

This is a semantic simplification, but likely an implementation rewrite of the
handler composition/lowering pipeline.

## Motivation

The current implementation mixes several models:

- `with {a, b, c}` mostly behaves like a merged handler set
- later handlers win for overlapping operations
- inline handlers currently have ordering restrictions
- `return` clause behavior does not fully follow the op-composition model
- lowering contains both ordinary CPS handler lowering and BEAM-native direct
  shortcuts

This leads to ambiguous behavior, especially around:

- multiple `return` clauses
- mixing named and inline handlers
- continuation ownership
- dynamic handler values
- BEAM-native effect lowering

Treating `with {...}` as sugar for nested `with`s gives the language one
coherent story instead of several partially overlapping ones.

## Proposed Semantics

### Desugaring

The primary rule:

```dy
expr with {a, b, c}
== ((expr with a) with b) with c
```

This should hold whether `a`, `b`, and `c` are:

- named handler values
- inline handlers
- conditional handler values
- handler factory results

Mixed forms are allowed, because they are just ordered handlers.

### Operation Handling

When an effect operation is performed:

1. The nearest enclosing handler gets the first chance to handle it.
2. If that handler does not define the operation, the operation propagates
   outward.
3. The first enclosing handler that defines the operation handles that
   occurrence.
4. Outer handlers do not also handle the same occurrence unless the inner
   handler explicitly re-performs or forwards it.

For overlapping handlers:

```dy
expr with {a, b, c}
```

if all three define `log`, then `a` handles `log`, not `b` or `c`.

### Propagation

If no handler in the local stack handles an operation, it continues outward to
the next enclosing `with` or to the caller's effect row.

This means nested local handlers may partially handle effects and let the rest
bubble out naturally.

### `return` Clauses

Each handler's `return` clause applies when the handled computation at that
handler boundary completes successfully.

Given:

```dy
((expr with a) with b) with c
```

the success path is:

1. `a.return`
2. `b.return`
3. `c.return`

assuming each handler completes normally and defines a `return` clause.

This means `return` clauses compose by nesting rather than by override.

### Delimitation

Each `with` is a continuation delimiter.

If `h2` handles an operation that originated inside `h1`, then `h2` resumes the
continuation delimited by the `with h2` boundary, not the entire caller
continuation.

Outer handlers may still run their own `return` clauses later when their own
wrapped expressions finish, but they are not part of the inner handler's
captured continuation.

### Inline Handlers

Inline handlers should be treated as first-class ordered handlers, not as a
special "final override block".

This means all of the following become equivalent in the sense of explicit
ordering:

```dy
expr with {a, b, c}
expr with {a, inline_h, c}
((expr with a) with inline_h) with c
```

where `inline_h` is an inline handler value or desugared inline handler block.

## Consequences

### Behavior Changes

The biggest semantic shift is that overlapping handlers no longer "merge and
last one wins". They now nest.

Old intuition:

```dy
expr with {a, b}
```

meant "one combined handler set where `b` overrides `a`".

New intuition:

```dy
expr with {a, b}
```

means "`a` is inside `b`".

This affects:

- op dispatch order
- `return` behavior
- handler reasoning in docs and examples
- any code that relied on merged override semantics

### Multiple `return` Clauses

Under this model, multiple `return` clauses are valid if they typecheck.

They do not conflict by default; they compose through nesting.

Type mismatches are still compile-time errors. For example, if an inner
`return` produces `Float` and an outer `return` expects `Int`, the composition
should fail in the typechecker.

### "Default Handlers in `main`"

A broad stack of "default" handlers remains possible, but handlers with
meaningful `return` clauses become global result transformers, not just effect
providers.

This may be a feature rather than a bug, but it is a real design consequence:

- op-only handlers compose naturally in large groups
- return-bearing handlers should be used more deliberately

## Implementation Strategy

This should be specified as one semantic change, but implemented in phases.

### Phase 1: Formalize the Semantics

Write down the language rule in user-facing docs:

- `with {a, b, c}` desugars to nested `with`
- lexical order is the handler order
- operations propagate outward until handled
- `return` clauses compose by nesting
- inline handlers participate in the same ordered model

This phase should also explicitly retire the old "merged handlers with inline
override" mental model.

### Phase 2: Desugar Early

Prefer making the nested structure explicit in the frontend rather than
re-deriving ordered semantics late in lowering.

Possible approaches:

1. Parser/AST keeps the list syntax, then an early desugaring pass rewrites it
   to nested `ExprKind::With`.
2. Lowering/typechecking keep the surface form but use a shared helper that
   treats it exactly as nested `with`.

The first option is cleaner if we want one semantic model everywhere.

### Phase 3: Typechecker Alignment

The typechecker should stop thinking of `with {...}` as "infer inner, subtract
all handled effects from a combined set".

Instead it should effectively typecheck:

```dy
((expr with a) with b) with c
```

This likely means:

- reworking `typechecker/handlers.rs`
- allowing named and inline handlers at any position
- making `return` type transformations compose in nested order
- keeping effect subtraction and propagation aligned with the nested structure

This is also where we must verify that existing row-polymorphic behavior still
works under nested subtraction/propagation.

### Phase 4: Lowering Rewrite

`codegen/lower/effects.rs` should be rewritten around explicit handler layers
instead of merged handler plans.

Likely goals:

- remove special "named vs inline merge" behavior
- lower each `with` boundary as a real layer
- make the captured continuation explicitly delimited at that layer
- apply `return` when that layer completes
- let outer layers wrap inner ones naturally

This is probably the biggest implementation step.

### Phase 5: Dynamic Handlers

Dynamic handler values should continue to work, but under the nested model they
become ordinary handler layers instead of entries in a merged dispatch table.

This includes:

- handler factory results
- conditional handler values
- imported handler values
- local `let`-bound handlers

The current tuple-of-lambdas representation may still be usable, but its use
site semantics will change from "select ops into one combined environment" to
"install a layer".

### Phase 6: BEAM-Native Effects

BEAM-native support should be re-evaluated after the layered model exists.

Current state:

- some native handlers lower through `build_beam_native_op_fun`
- some also use the stronger `direct_ops` shortcut

Nested handler semantics make `direct_ops` more suspect, because it can erase
the handler boundary that owns the continuation and `return` clause.

Proposed direction:

- preserve native-aware lowering in Rust
- prefer native-backed CPS handlers first
- disable or restrict `direct_ops` until semantics are correct
- re-introduce fast paths later only for proven-safe cases

## Refactor Scope

This is not just a bug fix. It is a semantic redesign of handler composition.

That said, it does not necessarily require rewriting the entire effect system.

Reasonable rewrite targets:

- handler composition semantics
- `with` typing
- `with` lowering
- continuation delimitation
- BEAM-native fast-path policy

Likely reusable pieces:

- effect row representation
- effect call typing
- row-polymorphic inference machinery
- dynamic handler runtime representation, if adapted carefully

## Migration / Compatibility

This proposal is a breaking semantic change for programs that relied on merged
override behavior.

Examples that may change meaning:

- `with {a, b}` where both handle the same op
- handler groups with multiple `return` clauses
- mixed named/inline blocks that assumed inline arms must be last

We should decide whether to:

1. land this as a breaking change with documentation and tests
2. stage it behind a temporary experimental flag
3. temporarily reject ambiguous cases during migration

My recommendation is to avoid a half-semantics migration. If we adopt this
model, the list form and the stacked form should mean the same thing.

## Open Questions

### Order Choice

This proposal uses lexical order:

```dy
expr with {a, b, c} == ((expr with a) with b) with c
```

We should explicitly confirm that this is the intended order before
implementation.

### Inline Syntax

If inline handlers can appear anywhere in the list, do we keep the current
single-block syntax and desugar each inline entry to a handler layer, or do we
need a slightly richer internal representation first?

### Optimization Boundaries

How much of the current fast-path lowering should be preserved during the
rewrite, versus disabled temporarily to keep semantics correct?

### Docs and Teaching

Several docs currently describe "stacking" in a way that sounds like merged
composition. These will need to be updated together so users only learn one
model.

## Suggested Execution Plan

1. Confirm lexical nested semantics as the language rule.
2. Update planning/docs with the rule and its consequences.
3. Add focused semantic tests for nested operation propagation and nested
   `return` composition.
4. Rework typechecker `with` handling to follow nested structure.
5. Rebuild lowering around explicit handler layers.
6. Temporarily simplify BEAM-native fast paths as needed.
7. Update guides/examples once implementation matches the new model.

## Non-Goal

This proposal does not attempt to redesign effect rows, effect declaration
syntax, or the runtime representation of every handler-related value. It is
about making handler composition itself principled and uniform.
