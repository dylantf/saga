# Name Resolution

## Status

This document describes the **current** resolver architecture after the
resolution refactor.

The big shift is:

- name resolution is now a real front-end phase
- the authoritative output is `ResolutionResult`, keyed by source `NodeId`
- later phases mostly consume semantic identities instead of re-resolving
  source strings

The architecture here is now the normal compiler contract, not an in-progress
experiment. Some narrow specialized lookups still exist in the typechecker and
lowerer, especially around effects and trait-related metadata, but the old
"canonicalize the AST and then guess again later" model is no longer the main
contract.

## Overview

The compiler now has two distinct resolution layers:

1. **Front-end resolution** in `src/typechecker/resolve.rs`
2. **Backend/callable resolution** in `src/codegen/resolve.rs`

They solve different problems.

### Front-end resolution

The front-end resolver runs after imports are processed and before body
inference. It records the semantic identity of source AST nodes in a
`ResolutionResult`.

This layer answers questions like:

- what value does this `Var` refer to?
- which constructor does this pattern use?
- which effect does this `EffectRef` mean?
- which handler does this `with name` reference?
- which record type does this field access/update belong to?

### Backend resolution

The backend resolver is narrower. It answers lowering-specific questions like:

- is this callable a local function or imported function?
- what BEAM module/function does it call?
- what arity/effect metadata should be used for CPS lowering?

It is no longer intended to be a second general-purpose resolver for source
syntax.

## Core Data Structures

### `ScopeMap`

`ScopeMap` still exists and is still useful, but its role is narrower than it
used to be.

It is primarily:

- an import/global scope construction artifact
- a way to map user-visible import forms to canonical names
- a helper for diagnostics, tooling, and a few remaining specialized lookups

It is **not** the main semantic lookup path for ordinary source expressions
during lowering anymore.

### `ResolutionResult`

The authoritative front-end output is `ResolutionResult` in
`src/typechecker/resolve.rs`.

It stores semantic identity per source node:

```rust
pub struct ResolutionResult {
    pub values: HashMap<NodeId, ResolvedValue>,
    pub constructors: HashMap<NodeId, String>,
    pub record_types: HashMap<NodeId, String>,
    pub types: HashMap<NodeId, String>,
    pub traits: HashMap<NodeId, String>,
    pub impl_traits: HashMap<NodeId, String>,
    pub impl_target_types: HashMap<NodeId, String>,
    pub effects: HashMap<NodeId, String>,
    pub handlers: HashMap<NodeId, ResolvedValue>,
    pub effect_call_qualifiers: HashMap<NodeId, String>,
    pub handler_arm_qualifiers: HashMap<NodeId, String>,
}
```

The exact value types vary by namespace, but the important rule is:

- **key by source identity**
- **store semantic meaning explicitly**

### `ResolvedValue`

Value-like names resolve to:

```rust
pub enum ResolvedValue {
    Local {
        binding_id: LocalBindingId,
        name: String,
    },
    Global {
        lookup_name: String,
    },
}
```

This lets later phases distinguish:

- lexical locals
- global/imported values

without re-deriving that from source spelling.

## What Resolves Early

The front-end resolver now resolves these categories before body inference:

- value references
- constructor references
- type references
- trait references
- impl trait refs
- impl target type refs
- effect refs
- handler refs
- effect-call qualifiers
- handler-arm qualifiers
- record type identity for record-driven expressions

That is the main boundary change from the old system.

## What Still Resolves Late

Some things still legitimately happen after front-end resolution:

- trait impl selection / evidence choice
- effect row solving
- some effect op lookup paths in the typechecker
- backend callable dispatch metadata

That is normal. The important distinction is:

- **names resolve early**
- **instances, rows, and lowering metadata can still be computed later**

## Lexical Scope Model

The front-end resolver no longer relies on the old "just suppress imported
rewrites with a `HashSet<String>`" model as its main abstraction.

It now uses explicit lexical scopes and stable local binding ids for values.

Conceptually:

- imported/global names come from `ScopeMap`
- lexical bindings are tracked by real scope frames
- each use site resolves to either:
  - a local binding identity
  - a global canonical lookup key

This is why the current resolver is much less fragile around shadowing.

## Canonical Names

Canonical names still matter, but mainly as **stable table keys** rather than
as the whole meaning of a source node.

Examples:

| Kind | Canonical key |
|------|---------------|
| Function | `Std.List.map` |
| Constructor | `Std.Maybe.Just` |
| Trait | `Std.Base.Show` |
| Trait method | `Std.Base.Show.show` |
| Effect | `Std.Fail.Fail` |
| Handler | `Std.Test.exec_handler` |

Types are still a special case in a few places: some type-related tables use
the existing canonical/bare conventions already present in the typechecker.

## Current Pipeline Role

The effective front-end pipeline is:

1. lex
2. parse
3. derive
4. desugar
5. process imports / build scope
6. run `resolve_names`
7. typecheck using `ResolutionResult`
8. elaborate
9. normalize
10. backend resolution + lowering

For the typechecker pipeline in more detail, see `docs/typechecking.md`.

## Typechecker Consumption

The typechecker now consumes `ResolutionResult` directly in many important
paths.

Examples:

- `ExprKind::Var` uses resolved value identity
- constructors use resolved constructor identity
- effect calls use resolved effect-call qualifiers
- trait refs and impl refs are recorded through resolved ids

There are still a few narrower specialized helpers for effects/traits, but the
ordinary expression path is now substantially more resolver-driven than before.

## Lowering Consumption

Lowering now consumes front-end resolution through narrow semantic helpers
instead of re-resolving source names directly.

Examples:

- resolved handler refs
- resolved effect-call qualifiers
- resolved handler-arm qualifiers
- resolved record type names
- resolved effect refs for module-local/imported metadata

The lowerer still has backend-specific maps, but those are now mostly about:

- callable identity
- BEAM module/function targets
- CPS arity/effect threading
- constructor atom mangling

not general-purpose source-name interpretation.

## Why This Document Still Exists

Yes, this doc is still worth keeping.

`docs/typechecking.md` explains the overall checker pipeline.
This doc explains the narrower but very important question:

- what resolution means now
- what data structures carry it
- which phase owns which kind of semantic identity

That is still useful enough to justify a separate page.

## Remaining Cleanup

The refactor is largely complete, but a few follow-up seams still exist:

- some specialized effect lookups in the typechecker
- some canonical-name normalization of already-typed effect metadata
- possible future symbol-id unification beyond canonical string keys

Those are now incremental cleanup tasks, not signs that the resolver boundary
failed.

## Key Files

- `src/typechecker/resolve.rs` — front-end source resolution
- `src/typechecker/check_module.rs` — import processing and scope construction
- `src/typechecker/check_decl.rs` — checker pipeline orchestration
- `src/typechecker/infer.rs` — main consumer of front-end resolution in inference
- `src/typechecker/result.rs` — `CheckResult` and stored `ResolutionResult`
- `src/codegen/resolve.rs` — backend/callable resolution for lowering
- `src/codegen/lower/` — consumers of semantic resolution during lowering
