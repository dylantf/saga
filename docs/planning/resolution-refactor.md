# Resolution Refactor

## Summary

The current name-resolution story is conceptually close to what we want, but the phase boundary is too soft.

Today we have:

- an import-built `ScopeMap`
- a separate `resolve_names` pass
- some AST canonicalization before inference

But we also still have:

- fallback resolution during inference
- specialized re-resolution for traits/effects/handlers
- auto-import behavior during typechecking
- lexical shadowing represented mostly by `HashSet<String>`

That combination makes name resolution advisory rather than authoritative.

This refactor aims to make resolution a real phase boundary:

- build module/global scope first
- resolve all names once
- store resolved identity in one authoritative form
- make typechecking consume resolved identities only

The resolver should be designed with eventual SCC/circular-import support in mind, but the first version should still reject cycles.

## Problem

The current implementation in `src/typechecker/resolve.rs` is doing two different jobs at once:

1. resolving imported/global names through `ScopeMap`
2. suppressing canonicalization when a local binding shadows an imported name

The shadowing side is currently managed with:

- `HashSet<String>` for locals
- special-case removal of local constructors from a cloned `ScopeMap`

This works for many cases, but it has a few structural weaknesses:

- local scope is represented by name presence, not binding identity
- different namespaces are handled differently
- not all names are canonicalized the same way
- the typechecker still re-resolves many names after the resolver supposedly ran
- some correctness depends on phase ordering plus inference-time fallback behavior

This is especially brittle around:

- imported values vs local shadowing
- constructors in patterns
- qualified names
- effect qualifiers
- trait names in where clauses / impls
- handler names

## Goals

- Make resolution a hard boundary before body typechecking
- Resolve every name-bearing use site to a stable semantic identity
- Replace string-set shadowing with real lexical scope handling
- Remove inference-time fallback resolution for ordinary names
- Keep the existing “facts flow through `Checker` / `CheckResult`” architecture
- Design the new resolver around module interfaces so circular imports are a natural later extension

## Non-Goals

- Implement circular imports in the first refactor
- Solve trait impl selection during resolution
- Solve effect instantiation during resolution
- Rewrite all downstream compiler phases at once
- Remove every canonical string representation from the compiler

## Key Principle

Names and instances are different problems.

### Resolve early

These should be fixed before inference:

- imported/top-level value identity
- constructor identity
- type name identity
- trait declaration identity
- effect declaration identity
- handler identity
- qualified module path identity

### Solve late

These can legitimately wait for or depend on unification:

- which impl satisfies a trait constraint
- which dictionary/evidence to use
- concrete effect type arguments
- effect row solving
- ambiguous field accesses
- overloaded operator constraints

Short version:

- names early
- instances late

## Proposed Phase Pipeline

The long-term pipeline should look like:

1. scan module graph
2. parse source AST
3. derive + desugar into final AST
4. collect module interfaces / headers
5. build import/global scopes from interfaces
6. resolve names
7. typecheck bodies
8. solve deferred constraints / collect evidence
9. elaborate
10. lower
11. output

For now, cycles can still be rejected after the module graph is built.

The important architectural shift is:

- resolution should consume interfaces
- typechecking should consume resolved programs

not:

- resolution should depend on fully typechecked imported bodies

## Current State

Relevant files:

- `src/typechecker/resolve.rs`
- `src/typechecker/check_module.rs`
- `src/typechecker/check_decl.rs`
- `src/typechecker/infer.rs`
- `src/typechecker/patterns.rs`
- `src/typechecker/effects.rs`
- `src/typechecker/check_traits.rs`
- `src/typechecker/mod.rs`

Current behavior includes:

- `resolve_names` rewrites many AST names to canonical strings
- `QualifiedName` keeps source spelling and stores `canonical_module`
- `infer.rs` still falls back to `scope_map.resolve_value` and `scope_map.resolve_constructor`
- `effects.rs::resolve_effect` still resolves and may auto-import
- `check_traits.rs::resolve_trait_name` still resolves traits late
- pattern matching still performs constructor fallback lookup

That means “resolved” currently means “mostly resolved.”

## Proposed Architecture

## 1. Separate Global Scope from Lexical Scope

The new resolver should have two clearly different layers:

### Global/import scope

Built from:

- current module declarations
- imported module interfaces
- builtin/prelude interfaces

It answers:

- what global names are available
- what canonical identity each global name maps to

### Lexical scope

Built during AST traversal with real scope frames.

It answers:

- whether a use site refers to a local binding
- which local binding it refers to
- whether a global/imported name is shadowed

This replaces the current “global map + `HashSet<String>` suppression” model.

## 2. Introduce Resolved Identity Types

The resolver should produce semantic identity, not just rewritten strings.

For example:

```rust
enum ResolvedName {
    LocalValue(LocalBindingId),
    TopLevelValue { module: String, name: String },
    Constructor { module: String, name: String },
    TypeName { module: String, name: String },
    Trait { module: String, name: String },
    TraitMethod { trait_module: String, trait_name: String, method: String },
    Effect { module: String, name: String },
    Handler { module: String, name: String },
}
```

This does not have to be the exact final shape, but the important idea is:

- use sites resolve to structured identities
- not just “some string after canonicalization”

## 3. Store Resolution Results Explicitly

The resolver should produce an authoritative result object.

For example:

```rust
struct ResolutionResult {
    value_uses: HashMap<NodeId, ResolvedName>,
    constructor_uses: HashMap<NodeId, ResolvedName>,
    type_refs: HashMap<Span, ResolvedName>,
    trait_refs: HashMap<Span, ResolvedName>,
    effect_refs: HashMap<Span, ResolvedName>,
    handler_refs: HashMap<Span, ResolvedName>,
}
```

The exact indexing may vary by namespace:

- `NodeId` for expressions
- `NodeId` or `Span` for patterns
- `Span` for type/effect/trait refs if there is no dedicated node id

But the main rule should be:

- resolution results are explicit and queryable
- downstream phases do not reconstruct them from strings

## 4. Keep AST Mostly Source-Shaped

The current resolver rewrites AST names in place.

That can still be useful, but it should stop being the primary contract.

Recommended direction:

- preserve source-oriented AST spelling as much as possible
- attach resolved identity in `ResolutionResult`
- let later phases read the resolution tables

This avoids awkward mixed representations like:

- `QualifiedName.module` preserving source syntax
- plus `canonical_module`
- plus inference fallback through `scope_map`

## 5. Use Real Scope Frames

Instead of carrying `HashSet<String>`, use lexical scope frames.

For example:

```rust
struct Resolver {
    globals: GlobalScope,
    value_scopes: Vec<HashMap<String, LocalBindingId>>,
    type_var_scopes: Vec<HashMap<String, TypeVarBindingId>>,
}
```

Resolution rule for `Var(name)`:

1. search lexical value scopes from innermost outward
2. if found, resolve to `LocalValue(id)`
3. otherwise consult global/import scope
4. otherwise emit unresolved-name error

This gives correct shadowing without mutating import maps or relying on name presence.

## What Should Resolve in the New Pass

The new resolver should cover:

- `ExprKind::Var`
- `ExprKind::QualifiedName`
- `ExprKind::Constructor`
- `Pat::Constructor`
- named handlers in `with`
- handler item named refs
- effect qualifiers in `EffectCall`
- type names inside `TypeExpr`
- trait names in trait defs / impl defs / where clauses
- effect names in `needs`
- impl target types
- record type names where they are semantic references

## What Should Not Resolve There

The resolver should not attempt to decide:

- which impl satisfies a trait constraint
- what concrete type fills a trait/effect parameter
- whether a field access is ambiguous
- how effect rows unify
- which evidence node elaboration will emit

Those remain typechecker/elaboration responsibilities.

## Module Interfaces

This refactor should introduce or formalize a real module interface/header representation.

For each module, the interface should include enough information to build import/global scope before body checking.

Suggested contents:

- module name
- public values/functions and signatures
- public handlers
- public types/records
- public constructors
- public traits
- public trait methods
- public effects
- type arities
- constructor ownership
- export visibility information
- source-module origin for each canonical item

This is the thing import resolution should consume.

## Global Scope Design

Instead of one `ScopeMap` full of strings, the next version should move toward a more semantic global scope.

For example:

```rust
struct GlobalScope {
    values: HashMap<String, GlobalValueId>,
    constructors: HashMap<String, ConstructorId>,
    types: HashMap<String, TypeId>,
    traits: HashMap<String, TraitId>,
    trait_methods: HashMap<String, TraitMethodId>,
    effects: HashMap<String, EffectId>,
    handlers: HashMap<String, HandlerId>,
}
```

`ScopeMap` can still exist as an intermediate compatibility layer, but it should stop carrying lexical shadowing responsibilities.

## Typechecker Contract After the Refactor

Once resolution finishes, typechecking should assume:

- global/imported names are already resolved
- local-vs-global decisions are already made
- unresolved ordinary names are resolver errors

That means removing the following patterns over time:

- `scope_map.resolve_value(...)` inside inference
- `scope_map.resolve_constructor(...)` inside inference/pattern checking
- auto-import during inference
- late trait/effect name canonicalization for ordinary declaration/use-site lookup

The typechecker should still do late work for:

- unification
- effect instantiation
- deferred trait constraints
- evidence collection

## Circular Import Compatibility

This refactor should be designed so SCC/circular import support is an easy extension later, even if we still reject cycles initially.

That means:

- import/global scope should be built from interfaces, not fully checked bodies
- the module graph should be explicit
- resolution should not rely on recursive “typecheck import now” behavior

The intended later model is:

- build module graph
- compute SCCs
- topologically order SCCs
- build interfaces for all modules in an SCC
- resolve names against those interfaces
- typecheck bodies afterward

But cycle support should not be part of the first refactor.

## Interaction with Synthetic `NodeId` Stability

This refactor is closely related to `docs/planning/synthetic-nodeid-stability.md`.

The two plans address different problems, but they meet at the same boundary:

- one pass computes semantic metadata about source nodes
- later passes rebuild AST fragments
- downstream consumers still need access to the original metadata

If the new resolver produces an authoritative `ResolutionResult` keyed by `NodeId`, then:

- typechecking can consume that result cleanly
- later phases can only keep using it if source identity is preserved across semantics-preserving rewrites

That means the resolver refactor should adopt the same rule of thumb already proposed for type metadata:

- if a later pass is still talking about the same source expression, preserve its `NodeId`
- if a later pass creates a genuinely synthetic expression, it should receive a fresh identity

In other words:

- resolution should not be re-derived from rewritten strings in later phases
- if later phases need source-resolution metadata, they must preserve the originating identity

This matters because otherwise the compiler will be tempted to reintroduce fallback resolution when a `NodeId` lookup misses, which would recreate the very “soft phase boundary” this refactor is trying to eliminate.

### Recommended Invariant

After name resolution:

- all source expression/pattern/type/effect/trait references that matter to later phases should be addressable through stable source identity
- any semantics-preserving rebuild after that point must preserve the original `NodeId` or carry an explicit origin/source id

### Long-Term Compatibility

If `NodeId` drift keeps recurring even after an audit, the resolver refactor would also fit naturally with a future split between:

- current structural node identity
- source/origin identity

That would allow:

- fresh synthetic nodes for later compiler phases
- stable lookup of resolution/type metadata by source identity

without requiring later phases to guess or reconstruct semantic identity from strings or local context.

## Migration Plan

This should be done incrementally.

## Phase 1: Introduce Resolution Data Structures

Add:

- `ResolvedName`-style enums
- `ResolutionResult`
- stable local binding ids if needed

Do this without removing the existing resolver yet.

## Phase 2: Build a New Resolver Alongside the Existing One

Implement a new resolver that:

- builds lexical scope frames
- consults imported/global scope
- records resolution results explicitly

Initially it can coexist with the current AST rewriting pass.

## Phase 3: Migrate High-Value Consumers

Start by making typechecking consume resolution results for:

- `ExprKind::Var`
- `ExprKind::Constructor`
- `Pat::Constructor`
- `QualifiedName`

These are some of the highest-regression sites today.

## Phase 4: Migrate Trait/Effect/Handler Name Resolution

Move:

- trait names in declarations and where clauses
- effect names and effect qualifiers
- handler references

to resolved identities rather than late string lookup.

Keep impl selection and effect instantiation late.

## Phase 5: Remove Inference-Time Fallback Resolution

Once the main consumers are migrated:

- strip `scope_map` fallback from inference
- strip constructor fallback from pattern binding
- isolate or remove auto-import during typechecking

At this stage unresolved-name failures should be resolver failures.

## Phase 6: Simplify or Retire AST String Rewriting

After the resolution tables are authoritative, decide whether AST rewriting is still needed.

My preference is:

- keep AST mostly source-shaped
- rely on `ResolutionResult`

But this can be deferred.

## What to Keep From the Current Design

The current implementation has a few good ideas worth preserving:

- a dedicated pre-inference resolution pass
- separate namespaces in import/global scope
- import-built visibility maps
- preserving user source spelling where useful
- flowing compiler facts forward via `CheckResult`

## What to Replace

These should be phased out:

- `HashSet<String>` as the main lexical shadowing mechanism
- cloned `ScopeMap` mutation to hide local constructor collisions
- inference-time fallback resolution
- mixed “sometimes canonicalized, sometimes not” as the main contract
- auto-import during inference

## Open Questions

### 1. Do we keep rewriting the AST?

Options:

- continue rewriting names in place but also store resolution results
- stop rewriting most names and rely on resolution maps entirely

Recommendation:

- allow both temporarily during migration
- aim for resolution maps as the authoritative source

### 2. What index should type/effect/trait refs use?

Expressions already have `NodeId`.

Type/effect/trait refs may need:

- dedicated node ids in the future
- or span-based maps for now

### 3. How much of `ScopeMap` should survive?

`ScopeMap` may still be useful for:

- import visibility construction
- IDE/tooling
- shortest-alias/origin lookups

But it should no longer be the primary runtime resolver inside type inference.

### 4. How should trait methods be represented?

Today they are a special case that exist under both bare and canonical names.

The new resolver should make this explicit rather than relying on ad hoc env insertion.

## Tests to Add

Any refactor here should preserve or expand regression coverage for:

- local variable shadows imported function
- local let shadows imported function inside nested block
- lambda parameter shadows imported function
- case pattern variable shadows imported function
- local constructor vs imported constructor with same bare name
- qualified value resolution through alias
- qualified effect call resolution through alias
- handler name shadowing
- trait name resolution in where clauses
- impl target type resolution
- imported constructor resolution in patterns
- imported constructor resolution in expressions
- no inference-time repair of unresolved names

Later, once interfaces are separated from body checking, add tests that assert:

- resolution succeeds before body typechecking
- import/global scope can be built without checking imported bodies
- cycles are still rejected cleanly but at the module-graph layer

## Suggested First Deliverable

The first meaningful milestone is not “complete resolver replacement.”

It is:

- a new explicit `ResolutionResult`
- a resolver with real lexical scopes
- inference reading that result for `Var`, `Constructor`, and `QualifiedName`

That should already remove a large amount of the current “resolve once, then silently re-resolve later” fragility.
