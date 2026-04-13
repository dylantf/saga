# Resolution Refactor Plan

## Summary

Rebuild name resolution as a first-class front-end phase and make it the only source of semantic name identity for the compiler. The end state is:

- parse + derive + desugar
- collect module interfaces
- build import/global scope
- resolve names into authoritative resolution maps
- typecheck using resolved identities only
- elaborate/lower using the same resolved identities or a thin backend-specific projection of them

This is a high-risk, whole-pipeline refactor, not a compatibility migration. We will prefer a clean end state over minimizing churn. Circular imports are not implemented in this pass, but the architecture must be interface/SCC-ready and reject cycles explicitly at the graph layer.

## Key Design Decisions

- **Authoritative output**: use **resolution maps**, not a canonicalized AST, as the long-term source of truth.
- **AST shape**: keep the source AST mostly source-shaped; remove long-term dependence on in-place canonical string rewriting.
- **Scope model**: replace `HashSet<String>` shadow suppression with real lexical scope frames plus a separate global/import scope.
- **Name vs instance split**: resolve declaration/use-site identity early; keep trait impl choice, effect instantiation, row solving, and evidence selection late.
- **Whole-pipeline cleanup**: front-end resolution replaces semantic fallback logic in typechecker, and codegen/lowering stop reconstructing origin/name identity from strings.
- **Node identity rule**: any pass that still needs resolution/type metadata after typechecking must preserve `NodeId` for semantics-preserving rebuilds or carry an explicit origin/source id.

## Implementation Changes

### 1. Foundations

Add new front-end resolution types and make them flow through `CheckResult`.

- Introduce a new resolver result type, e.g. `ResolutionResult`, containing authoritative per-use semantic identity.
- Add structured identity enums for all front-end namespaces:
  - value uses
  - constructor uses
  - type refs
  - trait refs
  - effect refs
  - handler refs
  - module-qualified refs
- Introduce stable local binding ids for lexical bindings so locals are resolved by identity, not just by spelling.
- Add `ResolutionResult` to `CheckResult` and per-module check results.
- Keep `ScopeMap` only as an import/global-scope construction/tooling helper; it is no longer the runtime semantic resolver during inference.

### 2. Module Interfaces and Scope Construction

Introduce an explicit interface/header layer before body checking.

- Add a `ModuleInterface`/header representation built from parsed+desugared declarations without checking bodies.
- Interface must include:
  - public annotated values/functions
  - public handlers
  - public types/records
  - public constructors
  - public traits and trait methods
  - public effects
  - type arities and origins
- Build the module graph up front.
- Reject cycles explicitly at the module graph stage for now.
- Build import/global scope from interfaces, not from recursively typechecked imported bodies.
- Preserve current import visibility semantics, but express them through interface-to-scope construction instead of ad hoc post hoc fallback.

### 3. New Resolver

Replace `src/typechecker/resolve.rs` with a resolver that walks the source AST using lexical frames.

- Resolver inputs:
  - module interface for current module
  - imported interfaces
  - prelude/builtin interface data
  - source/desugared AST
- Resolver algorithm:
  - maintain separate lexical scope stacks for values and type variables
  - resolve locals first, then global/import scope
  - record semantic identity in `ResolutionResult`
- Resolve all name-bearing sites needed by the front-end:
  - `ExprKind::Var`
  - `ExprKind::QualifiedName`
  - `ExprKind::Constructor`
  - `Pat::Constructor`
  - handler references
  - effect qualifiers and `needs` refs
  - type names in `TypeExpr`
  - trait names in `TraitDef`, `ImplDef`, and `where` clauses
  - impl target types
- Do **not** solve impl selection, effect row behavior, or evidence during resolution.

### 4. Typechecker Cutover

Make the typechecker consume resolved identities and remove semantic fallback resolution.

- `infer.rs`:
  - remove `scope_map.resolve_value` fallback for `Var`
  - remove constructor fallback lookup
  - remove `QualifiedName` inference-time rescue logic and auto-import behavior
  - use `ResolutionResult` for value/constructor/module-qualified identity
- `patterns.rs`:
  - resolve constructor patterns through `ResolutionResult`, not `scope_map`
- `check_traits.rs`:
  - remove late trait name resolution as a normal lookup path
  - trait declarations/where clauses/impl headers consume resolved trait refs
- `effects.rs`:
  - remove ordinary late effect name resolution and inference-time auto-import
  - effect calls/qualifiers/needs consume resolved effect refs
- `check_decl.rs` and `unify.rs`:
  - stop using `scope_map` to semantically resolve ordinary types/effects/traits during checking
  - only use canonical/import origin helpers where needed for tooling or diagnostics
- New invariant: if an ordinary semantic name is unresolved after resolution, that is a resolver failure, not something typechecking repairs.

### 5. Elaboration and Lowering Cutover

Carry the resolved identity model through the whole pipeline.

- Elaboration reads the same resolved front-end identities instead of inferring semantic meaning from raw strings where possible.
- `src/codegen/resolve.rs` is no longer the primary semantic name resolver. Replace it with one of:
  - a thin backend projection built from `ResolutionResult` + codegen metadata, or
  - a greatly reduced pass that computes only backend-specific call/arity/layout facts
- Lowering must stop guessing module/origin identity from strings when semantic identity already exists.
- Keep backend-specific tables that are genuinely lowering-specific:
  - constructor atom mangling
  - CPS-expanded arity/effect threading data
- Do not duplicate front-end lexical name resolution logic in the lowerer.

### 6. Fallback Removal Sweep

After cutover, remove semantic fallback paths rather than preserving them indefinitely.

Delete or rewrite the following classes of fallback:

- inference-time `scope_map` name rescue
- constructor fallback lookup in patterns
- trait/effect late canonicalization for ordinary declaration/use lookup
- import-on-demand during inference
- downstream origin/name reconstruction from source strings when resolution data exists

Allowed remaining fallbacks:

- parser/LSP error recovery
- diagnostics/display-only alias shortening
- temporary missing-data assertions during the refactor, but not silent semantic fallback

### 7. NodeId / Identity Rules

Align this refactor with `docs/planning/synthetic-nodeid-stability.md`.

- Resolution maps are keyed by source identity.
- Any pass after resolution/typechecking that preserves source semantic identity must preserve `NodeId`.
- Any genuinely synthetic node gets a fresh `NodeId`.
- If later phases still need source-level resolution/type metadata and `NodeId` preservation proves insufficient, introduce an explicit source/origin id rather than reintroducing fallback resolution.

## Test Plan

### Resolver and Shadowing

Add or update tests for:

- local value shadows imported value
- nested block/local function shadowing
- lambda param shadowing
- case/do/receive pattern shadowing
- handler name shadowing
- imported constructor resolution in exprs and patterns
- qualified value resolution through aliases
- qualified effect call resolution through aliases
- trait refs in `where` and `impl`
- effect refs in `needs`
- impl target type refs

### Typechecker Contract

Add tests that assert:

- no inference-time repair is needed for resolved names
- unresolved names fail in resolution, not later in inference
- imported modules do not need to be body-typechecked to build import scope
- trait/effect names are fixed before unification, while impl/evidence selection still happens after unification

### Whole Pipeline

Keep or add regression tests for:

- imported handlers with local helpers/private constructors
- record-field handler bindings through trailing `with`
- project `Main` using module-specific check results
- elaboration/normalization preserving `NodeId` where resolution/type metadata is still consumed
- lowering using resolved identity/origin rather than reconstructing it from strings

## Assumptions and Defaults

- This is a **high-risk refactor** and may temporarily break many tests; correctness and architectural cleanup are prioritized over incremental compatibility.
- End-state authority is **resolution maps**, not a canonicalized AST.
- The refactor is **whole pipeline**, not typechecker-only.
- Circular imports are **not** implemented in this pass; the new module-interface design must be compatible with later SCC support.
- Existing import visibility rules and public-API annotation rules stay the same unless a test proves they are impossible to preserve cleanly.

## Progress Checklist

### Done

- `ResolutionResult` is flowing through `CheckResult` and per-module check results.
- Stable `NodeId` usage has been pushed further through resolution, elaboration, and lowering.
- Trait refs, supertraits, trait extra type args, handler refs, and handler-arm effect qualifiers now participate in the source-keyed resolution path.
- The main typechecker/codegen pipeline now treats front-end resolution as authoritative for ordinary source `Var` and `QualifiedName` meaning.
- `codegen::emit_module(...)` has been removed so parser/desugar-only codegen is no longer a normal public path.
- `emit_module_with_context(...)` now requires a real `CheckResult`, and the lowerer now requires checked semantic data instead of carrying a fake optional mode.
- Lowering has been cut over away from several old canonicalization assumptions:
  - effect-call lowering prefers front-end effect resolution
  - handler refs prefer front-end handler resolution
  - record field/layout lookup prefers resolved record identity
  - qualified calls prefer resolved function metadata
- Most backend fallback resolution for front-resolved source nodes has been removed from `src/codegen/resolve.rs`.
- The lowerer now routes front-end resolution by semantic module more explicitly during imported handler lowering.

### In Progress

- Backend semantic consolidation:
  - imported module semantic data is still read from a few different places (`front_resolution`, `codegen_info`, elaborated module, backend resolution map)
  - the lowerer is being cleaned up to use more explicit per-module semantic access instead of ad hoc `ctx.modules` lookups
- Backend resolver shrink:
  - `src/codegen/resolve.rs` is no longer acting as the primary semantic resolver
  - it still exists as a backend-oriented projection layer and may be reducible further
- Remaining fallback audit:
  - the highest-value fallback paths are gone
  - a few lower-value compatibility patterns may still exist in rarer paths and need inspection

### Remaining

- Make imported module semantic access more explicit and uniform in codegen/lowering.
- Decide whether `src/codegen/resolve.rs` should remain as a thin backend projection pass or be folded further into lowering/init helpers.
- Audit remaining name/canonical-name lookups and classify them as:
  - legitimate table-key lookup
  - backend-only synthetic bookkeeping
  - leftover semantic fallback to remove
- Revisit the module/interface side of the plan:
  - explicit module headers/interfaces
  - graph-first import processing
  - cycle-ready SCC architecture, while still rejecting cycles for now
- Tighten docs/invariants so the new phase boundaries are written down clearly.

### Current Phase

- Phase name: **Backend Semantic Consolidation**
- Immediate goal: remove the remaining ad hoc boundaries between front-end semantic data and imported-module codegen metadata so lowering reads one clearer per-module semantic bundle instead of reconstructing it piecemeal.
