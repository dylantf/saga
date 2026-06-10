# Trait Specialization And Generic Folding

Status: **draft plan**.

This is the implementation plan for the trait-specialization optimizer track
referenced as "Stage 6 / Stage 7" in
[direct-first-optimizer-matrix.md](./direct-first-optimizer-matrix.md). It turns
statically-known trait dictionary method calls into direct calls, and folds the
`Generic`-derived representation walk into a fused encoder/decoder so hot codecs
do not allocate and re-traverse `Rep` constructor trees at runtime.

Read first:

- [trait-dict-passing.md](../trait-dict-passing.md) — how dictionaries are
  represented and passed (`DictRef`, `DictMethodAccess`, `DictConstructor`).
- [generic-deriving.md](../generic-deriving.md) — how `deriving (ToJson)` routes
  through `Generic` (the bridge + delegating impl shape this plan folds).
- [direct-first-optimizer-matrix.md](./direct-first-optimizer-matrix.md) —
  Stage 6/7 rows; the ground rules this plan inherits.
- [direct-first-effect-shape-matrix.md](./direct-first-effect-shape-matrix.md) —
  the correctness-shape boundary this plan must not cross.

## Goal And Scope

Two tracks share one substrate:

- **General trait specialization** (Stage 6): a known-dictionary method call
  becomes a direct function call instead of a tuple build plus `element/2`
  projection.
- **Generic folding** (Stage 7): a routed-derive method (`m … (to x)`) is fused
  by inlining `to` (a statically-known `Rep` constructor tree) and the
  building-block codec impls, cancelling the intermediate `Record`/`And`/
  `Labeled`/`Leaf`/`Variant`/`Adt` constructors. The result is shaped like a
  hand-written encoder.

Explicit non-goals (we are not building GHC-grade class optimization):

- No whole-program inliner/simplifier. The general rewrites in Phase 4 only fire
  where seeded by dictionary facts at recognized sites.
- No blanket monomorphization of polymorphic APIs.
- No specialization through dynamic dictionaries — dictionary passing remains the
  correctness fallback, always.

Trait-agnostic by construction: every routed derive (`ToJson`, `FromJson`,
`PostgresRow`, `CsvRow`, …) is synthesized by the same `derive_routed`
machinery, so the folding driver matches the routing *shape*, not any particular
trait. Only leaf impls differ, and those resolve as ordinary known-impl calls.

## Design Anchors

These three properties are load-bearing. Every phase must preserve them.

### 1. Optimizer fact, not correctness fact

Trait dispatch facts live in `OptimizationFacts`
([src/codegen/optimize.rs](../../src/codegen/optimize.rs)), beside
`handler_analysis` and `public_helpers`. They are **optional and fallback-safe**.
They do **not** live in `call_effects.rs`, which computes mandatory runtime call
shape. `Dynamic` is always a legal classification; a missing fact keeps today's
`element/2` dispatch.

### 2. Specialization rewrites only the callee expression

Today a trait method call lowers (conceptually) to:

```text
apply (element(i, <dict-constructor application>)) (args…, _Evidence, _ReturnK)
```

Specialization changes **only** the `element(i, <dict ctor>)` sub-expression
into a direct function reference. All user-argument, evidence, and
return-continuation threading in `lower_runtime_cps_apply` stays identical. This
is how the optimization honors "traits carry effect rows": it never alters the
effect shape. An effectful `PostgresRow` method specializes exactly like a pure
`ToJson` method — same evidence threading, cheaper callee.

### 3. Facts say *which impl*; lowering joins *what shape*

`DictDispatch` carries impl identity only. At lowering time the consumer
cross-references the existing `CallEffectInfo`
([src/codegen/call_effects.rs](../../src/codegen/call_effects.rs)) for the same
App `NodeId` to get the call shape. No effect logic is duplicated.

## The Substrate: DictDispatchMap

A new metadata pass, `src/codegen/trait_dispatch.rs`, run after backend resolve
alongside the optimizer:

```rust
pub enum DictDispatch {
    /// Runtime Var dict (where-bound param). Keep element/2 dispatch.
    Dynamic,
    /// Statically resolvable to a named dict constructor + method slot.
    KnownImpl {
        dict_constructor: String,      // e.g. __dict_ToJson_Person
        method_index: usize,
        sub_dicts: Vec<DictDispatch>,  // resolved for parameterized impls
    },
}

pub type DictDispatchMap = HashMap<NodeId, DictDispatch>; // keyed by the DictMethodAccess App node
```

This is the "function classification, but for traits" abstraction. It is a proof
input, not a second interpreter. The `DictRef`/`App`-chain peeling it needs
already exists inside `classify_dict_method_call`
([call_effects.rs:986](../../src/codegen/call_effects.rs#L986)) and will be
factored into a shared helper.

## Phased Plan

### Phase 0 — Facts shell (behavior-neutral)

- Add `src/codegen/trait_dispatch.rs` with `DictDispatch`, `DictDispatchMap`, and
  `analyze(module, program, resolution) -> DictDispatchMap` returning empty.
- Add `dict_dispatch: DictDispatchMap` to `OptimizationFacts`; populate in
  `optimize::analyze`. It rides through `CompiledModule` automatically.
- Add a `SAGA_DEBUG_TRAIT_DISPATCH` source-order trace, matching the
  `SAGA_DEBUG_EFFECT_SHAPES` convention.

Acceptance:

- No emitted-Core change.
- `cargo test` green.

### Phase 1 — Classify known dicts (local)

- Factor the `DictRef`/`App`-chain peeling out of `classify_dict_method_call`
  into a shared helper.
- Resolve each `DictMethodAccess` to a `dict_constructor` name plus recursively
  resolved `sub_dicts`. A `Var` dict resolves to `Dynamic`.
- Local impls only.

Acceptance:

- Trace shows correct `KnownImpl` on
  `examples/optimization/trait-method-specialization/02`, `03`, `04`; all other
  dict calls `Dynamic`.
- No emitted-Core change yet.

### Phase 2 — Monomorphic direct call (general trait specialization)

- Hoist each impl method out of the `DictConstructor` method tuple into a
  uniquely-named module function (`__method_{dict}_{i}`) via the existing
  `generated_helper_variants` machinery
  ([src/codegen/lower/static_helpers.rs](../../src/codegen/lower/static_helpers.rs)).
  The dict tuple references the hoisted function too, so unspecialized callers
  are unaffected.
- In the dict-method-call consumer
  ([src/codegen/lower/calls.rs](../../src/codegen/lower/calls.rs)): when
  `dict_dispatch[app.id]` is `KnownImpl` with a **nullary, local** dict
  constructor, replace the callee with a direct reference to
  `__method_{dict}_{i}`. Join with `call_effects` for threading (unchanged).
- Parameterized dicts (non-empty `sub_dicts`) are deferred to a sub-phase: the
  method captures sub-dict params, which must be threaded explicitly. Admission
  is **all-or-nothing on sub-dicts** — only specialize when *every* constructor
  sub-dict arg is itself statically known (e.g.
  `__dict_Encodable_Box(__dict_Encodable_Int)`); inline the outer method and
  continue through the inner dispatch. A single `Dynamic` sub-dict makes the whole
  call `Dynamic`. (Confirmed by selective-uniform; see Salvage below.)

Acceptance:

- `02-concrete-trait-method.saga` emits no `element/2` for the specialized call.
- The `02` effectful-method runtime test still passes (evidence still threads).
- saga_json EffectOpts benchmark neutral-or-better; no-effect JSON neutral.

### Phase 3 — Cross-module known impls

- **Extend `TraitImplDict`
  ([src/typechecker/check_module.rs:356](../../src/typechecker/check_module.rs#L356))
  with per-method info.** Port selective-uniform's `TraitImplMethodInfo` (see
  Salvage §1) — it is IR-independent and near copy-paste:
  ```rust
  pub struct TraitImplMethodInfo {
      pub name: String,
      pub source_arity: usize,
      pub trait_effects: Vec<String>,
      pub trait_open_row: bool,   // maps 1:1 onto main's open-row semantics
  }
  ```
  Take `name` / `source_arity` / `trait_effects` / `trait_open_row`. **Drop**
  selective-uniform's `runtime_shape: { Direct | Cps{adapter_arity, …} }` field —
  precomputing the ABI in the typechecker is exactly what anchor 3 avoids. We
  join `CallEffectInfo` at lowering time instead. (The producer already exists in
  main's elaboration since per-method effect rows now flow through; this is the
  export shape.) This also closes the optimizer matrix's standing "open design
  question" — per-method is the right boundary, impl-level `needs` is not.
- Export impl-method identity (hoisted `__method_{dict}_{i}` names, arities,
  capture lists) alongside `TraitImplMethodInfo`.
- Admit imported `KnownImpl`; emit a remote direct call.
- **Private-helper policy** (the matrix lists this as a hard guard;
  selective-uniform found a working policy — Salvage §2): when an imported
  method body calls a *private* (unexported) helper, **clone that helper
  caller-local** rather than emit an invalid remote call to an unexported
  function. Helper collection is a conservative dependency fixpoint; an ambiguous
  dependency graph makes the constructor ineligible (fall back to `Dynamic`).
- This is the gate that makes `SagaJson.Codec`'s building-block impls reachable
  as `KnownImpl` from user code — a prerequisite for folding.

Acceptance:

- `cross-module-dict-specialization/{02-imported-concrete-method,
  06-imported-derived-dict-chain, 07-imported-dict-private-helper,
  08-imported-derived-impl-ladder}` specialize (ported as fixtures).
- saga_json library building-block impls show as `KnownImpl` from
  `EncodeDerive`.

### Phase 4 — The two trait-neutral rewrites

- `inline_known_impl_body`: pull the method `Lambda` from
  `DictConstructor.methods[i]` and β-reduce against the call arguments.
- `case_of_known_constructor`: rewrite `case (Con …) { Con x -> e }` to
  `e[x := …]`.

Both are completely trait- and derive-agnostic.

**Ordering matters** (the key insight from selective-uniform — Salvage §3):
collapse the `Rep` constructor case-match *first*, then β-reduce the method
lambda, then re-collapse. If you inline before collapsing, the size/fuel budget
sees the unfolded `Rep` tree and rejects the fusion. The cycle is
`case_of_known_constructor → inline_known_impl_body → case_of_known_constructor`,
to a fixpoint or the fuel bound. Lift the recursion-termination guards from
selective-uniform's `lower_selective/direct.rs` and
`lower_selective/known_values.rs` — they bottom out at the same place this plan
does.

Guards:

- Depth/fuel budget.
- Bottom out at `Leaf SelfType` as an ordinary monomorphic dict call — never
  inline-recurse through self-types. This is exactly where today's "recursion is
  free" stops (see generic-deriving.md, "Why Recursion Is Free").
- No fold through recursive containers (`List` element recursion stays a normal
  dict call) until proven.
- No fold through `Multishot` resume; no CPS-callable stored in data.

Acceptance:

- `06-derived-dict-chain.saga` (the in-module, deliberately-effectful miniature)
  fuses end-to-end with its effects preserved.

### Phase 5 — Generic-routing fusion driver

- Trigger at delegating-impl bodies of shape `m … (to x)`, recognizable from
  `derive_routed` output plus `ImplDef.routed_derive_info`.
- Inline `to` (the statically-known `Rep` tree from the `Generic` impl), inline
  the codec impls, run the Phase-4 rewrites to cancel `Record`/`And`/`Labeled`/
  `Leaf`/`Variant`/`Adt`, and emit a fused caller-local function.
- Trait-agnostic: identical for `ToJson`, `FromJson`, `PostgresRow`, `CsvRow`.

Acceptance:

- `EncodeDerive`'s emitted Core matches `EncodeHand`'s shape — no `Rep`
  constructor allocation, no codec tuple walk.
- Benchmarks improve; round-trip tests pass.

### Phase 6 — From-direction

- Mirror the driver for `from`-over-`Rep` decoders (`FromJson`, `PostgresRow`
  read side), pinned by the existing from-direction fixtures (`99g`, `99i`).

### Phase 7 — Dictionary-argument pruning (later)

- After specialization erases a call site's only use of a passed dict, drop the
  now-unused dict parameter (and stop threading it). Selective-uniform carried
  this as an explicit phase; it is the "dict-only local elision" row of the
  optimizer matrix. Strictly a cleanup pass gated on proven non-use — never prune
  a dict that escapes to a helper still needing it.

## Fixtures

Existing, to drive the early phases:

- `examples/optimization/trait-method-specialization/02-concrete-trait-method.saga`
  — Phase 1/2 monomorphic effectful method.
- `.../03-generic-wrapper.saga`, `.../04-parameterized-dict.saga` — Phase 1
  classification, Phase 2 parameterized sub-phase.
- `.../06-derived-dict-chain.saga` — Phase 4 in-module fold with effects.

Headline end-to-end targets:

- `saga_json` `EncodeDerive` vs `EncodeHand` — Phase 5 fused-shape comparison.
- `99g-generic-derived-fromjson.saga`, `99i-...-custom-wrapper.saga` — Phase 6.

## Salvage From `selective-uniform`

The abandoned uniform-monadic-IR branch (`../saga-selective-uniform`) did
substantial dict-specialization work. We reuse **metadata shapes, algorithms,
admission policies, and fixtures** — never the Rust functions, which operate on
the monadic `MExpr`/`Atom` IR and would drag that IR back in. The IR is the thing
we abandoned; do not port it.

Verified against the worktree:

1. **`TraitImplMethodInfo`** (`src/typechecker/check_module.rs:393`) — IR-
   independent, lives in `ModuleCodegenInfo`. Near copy-paste for Phase 3, minus
   the `runtime_shape` field (see Phase 3). The producer
   (`check_module.rs:1908`) sources per-method `trait_effects` / `trait_open_row`
   from the trait method `effect_sig` — main already computes these, so only the
   export wiring is new.

2. **Admission policies** (the branch's `effect-optimization.md`, as-built):
   nullary-local-dict-first (Phase 2); all-or-nothing on parameterized sub-dicts
   (Phase 2 sub-phase); private-helper caller-local cloning via a conservative
   dependency fixpoint (Phase 3); dict-argument pruning (Phase 7).

3. **Generic-branch-collapse ordering** (`lower_selective/direct.rs`,
   `lower_selective/known_values.rs`): collapse known-constructor case *before*
   the inliner's size budget runs (Phase 4). Rewrite the algorithm on elaborated
   AST; the **sequencing and termination guards** are the salvage, not the code.

4. **Fixtures** (pure `.saga`, no IR coupling — port directly):
   `examples/optimization/cross-module-dict-specialization/{06-imported-derived-dict-chain,
   07-imported-dict-private-helper, 08-imported-derived-impl-ladder}` (Phase 3/5);
   `selective-uniform/{34-effectful-trait-method, 35-generic-effectful-trait-method}`
   (Phase 2 "evidence still threads" acceptance).

5. **Discipline, not code**: the runtime-shape classification vocabulary and the
   explicit ABI-assertion helpers at direct-call / CPS-call sites (the branch's
   stated #1 win: wrong ABI choices become impossible or loudly diagnosed). Port
   the assertions; they back the `SAGA_DEBUG_TRAIT_DISPATCH` trace.

Explicitly left behind: the monadic IR as lowering input; the selective/fallback
Core merge; the direct/uniform dict-adapter lattice; imported-fact reconstruction
by re-translating modules.

**On the branch's benchmark verdict:** its "specialization didn't beat main on
no-effect JSON" was the CPS-everywhere substrate tax, *not* evidence against
specialization. Discard the verdict; **keep its failure-mode checklist** as
Phase 5 acceptance gates: does the optimization reach the hot path? does it emit
worse Core? do fallback adapters reintroduce dynamic dispatch? does inlining
duplicate too much `Generic` structure?

## Global Guardrails (inherited)

- Dynamic dictionaries stay correct via the existing `element/2` path.
- Specialization never alters the call's effect shape (anchor 2).
- Missed optimization is only slower; wrong optimization is a compiler bug.
- Every phase benchmarked against no-effect JSON; a regression is narrowed or
  reverted before the next layer.
- No generated-variant emission without the stable naming/reachability story
  that `generated_helper_variants` already provides.

## Relationship To Other Docs

- Supersedes the Stage 6/7 rows of
  [direct-first-optimizer-matrix.md](./direct-first-optimizer-matrix.md) as the
  detailed plan; that matrix remains the index.
- Depends on the runtime-shape discipline frozen by
  [direct-first-effect-shape-matrix.md](./direct-first-effect-shape-matrix.md).
- Builds on [generic-deriving.md](../generic-deriving.md) (Rep shape, routing
  layer) and [trait-dict-passing.md](../trait-dict-passing.md) (dict nodes,
  per-method effects).
