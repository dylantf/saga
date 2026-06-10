# Trait Specialization And Generic Folding

Status: **Phases 0–3 implemented; Phase 4 next.**

## Implementation Status & Handoff (2026-06-10)

Phases 0–3 are done and committed (`a4fd655`, `85fa3b4`, `05ed117`, `d5a4b63`,
`b88fe38`). Phase 4 (the trait-neutral rewrites) is the next step.

| Phase | What it does | Status |
| --- | --- | --- |
| 0 Facts shell | `DictDispatchMap` in `OptimizationFacts` | done (committed) |
| 1 Classify | shape-based `KnownImpl`/`Dynamic` | done (committed) |
| 2 Local direct call | hoist local nullary methods; `FunRef` call | done (committed) |
| 3 Cross-module | export hoisted methods; remote `call` | done (committed) |
| 4a Inline parameterized | `generic_fold.rs`: inline local parameterized dict chains | done (committed) |
| 4b Case-of-ctor + Phase 5 | cancel `Rep` ctors once `to x` is inlined | **next** |

**Phase 4a** (`generic_fold.rs`, commit `dd282b9`) added an elaborated-AST pass
that inlines statically-known *parameterized* dict-method calls on **local**
impls: the conditional impl's method lambda is β-reduced (with `where`-bound dict
params substituted by the concrete sub-dicts) into nested single-arm `case`s that
bottom out at a nullary/monomorphic dict call. Runs after `normalize_effects`,
before `resolve`, so all NodeId-keyed analyses recompute over the rewritten tree;
meaning-preserving so the effect ABI is untouched (Anchor 2). In-module
parameterized fallbacks now collapse fully (06: `1→0`; 99f: `10→0`, zero
`element/2`). **Still on the dict path:** cross-module parameterized impls (the
method body isn't local — needs producer bodies; a 4a-cross-module follow-up or
Phase 5), and the `Rep` constructor allocations themselves (need
`case_of_known_constructor` + inlined `to x`, which is 4b/Phase 5). `case_of_
known_constructor` was deliberately deferred to 4b — 4a's scrutinees are
variables, so nothing exercises it until `to x` is inlined.

### Code map

- **Classification** — `src/codegen/trait_dispatch.rs`:
  `DictDispatch { Dynamic, KnownImpl { dict_constructor, method_index, sub_dicts } }`,
  `DictValue`, `analyze()`. Keyed by the **outer `App` `NodeId`** (same key as
  `call_effects`). `SAGA_DEBUG_TRAIT_DISPATCH` traces it.
- **Hoisting (producer)** — `src/codegen/lower/module.rs`:
  `plan_dict_method_hoists` (supply-driven — hoists **all** local nullary dict
  methods, exported), `method_cps_shape`; dict-constructor lowering emits
  `__saga_dictmethod_<dict>_<idx>`, exports it, and references it (`FunRef`) from
  the dict tuple. `dict_method_hoists: HashMap<(dict, idx), HoistedDictMethod {
  fn_name, user_arity, is_cps }>` lives on the `Lowerer`.
- **Specialization (consumer)** — `src/codegen/lower/calls.rs`:
  `specialized_dict_method_callee` (records stats) → `classify_dict_specialization`
  (pure decision). `CpsCallee { Value, Remote }` threads through
  `lower_runtime_cps_apply` (`.apply()` emits `Apply` or `Call`). Local →
  `FunRef`; imported → `call 'mod':'__saga_dictmethod_...'`. Saturation guard via
  `trait_method_user_arity`; producer module via `imported_dict_erlang_mod`
  (resolves the `DictRef`). The two hook sites: CPS path in
  `lower_dict_method_call`, pure path in `lower_app_expr` (guarded
  `!expr_is_effectful_call`). `collect_dict_method_call` (util.rs) now also
  returns `trait_name`.
- **Stats** — `src/codegen/lower/trait_spec_stats.rs`: `SAGA_STATS=trait-spec`;
  `FallbackReason { Imported, Parameterized, Unsaturated, AbiMismatch }`. See the
  README "Diagnostics" section.

### Invariants & findings (don't re-derive)

- Hoisted name `__saga_dictmethod_<full canonical dict name>_<idx>` is
  deterministic and globally canonical, so the consumer reconstructs it with no
  exported fact (this is why Phase 3 needed **no** `TraitImplMethodInfo`).
- Anchor 2 holds: specialization swaps only the *callee*; arg/evidence/return-K
  threading is unchanged. `cps` comes from `CallEffectInfo`.
- Only **nullary** dicts hoist (capture-free). Parameterized dicts (non-empty
  `sub_dicts`) are the Phase 4 target.
- **Eta soundness**: impl methods must carry the full parameter list — the
  typechecker rejects eta-reduced/point-free impls (`greet n = prepend n` →
  type error). So `trait_method_user_arity == impl arity == hoisted arity`, and
  the saturation guard is sound.
- **Pre-existing bug (NOT ours), track separately**: an over-applied
  function-returning dict method (`mk 10 5` where `mk : a -> (Int -> Int)`)
  `badarity`s — confirmed identical on the committed base. Specialization
  correctly falls back (`unsaturated`); it does not regress this. Root cause:
  `collect_dict_method_call` greedily collects all `App` args.

### Stats baselines (regression watch — all remaining fallbacks are `parameterized`)

- `examples/99f-generic-derived-tojson`: `32 known | 22 specialized | 10 fell
  back (10 parameterized)`.
- saga_json `EncodeDerive`: `21 | 18 | 3 parameterized`;
  `EncodeDeriveCustom`: `33 | 28 | 5 parameterized`.
- `cross-module-dict-specialization/02-imported-concrete-method`: `Lib 1/1`,
  `Main 1/1`, runtime `"15"`.

---

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

## Measuring Specialization

The direct-first analog of the abandoned branch's `--monadic-stats`. After each
module lowers, `SAGA_STATS=trait-spec` prints a one-line summary of how many
statically-known dispatch sites were specialized to direct calls vs left on the
`element/2` dict-passing path, with a reason for each fallback
([src/codegen/lower/trait_spec_stats.rs](../../src/codegen/lower/trait_spec_stats.rs)):

```text
trait-spec[EncodeDerive]: 32 known site(s) | 8 specialized | 24 fell back (14 imported, 10 parameterized)
```

It measures backend truth (what lowering actually decided), keyed by App
`NodeId` so re-visits do not double-count. The fallback reasons map onto the
phases below — `imported` → Phase 3, `parameterized` → Phase 4 — so each phase's
acceptance can be stated as "this reason's count drops" on a representative
fixture, and a regression that silently stops specializing is caught even though
behavior stays correct. Run it on any lowering command:

```bash
SAGA_STATS=trait-spec saga emit file.saga 2>&1 >/dev/null | grep trait-spec
```

`SAGA_STATS` accepts `trait-spec`/`1`/`all` (every module) or a module-name
substring filter. See the README "Diagnostics" section for usage;
`SAGA_DEBUG_TRAIT_DISPATCH` (classification trace, Phase 0/1) is the companion
upstream view.

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

**Status: done.** Built via **hoist-and-remote-call**, which diverges from the
clone-caller-local approach this section originally inherited from
selective-uniform. The divergence falls out of how Phase 2 turned out: Phase 2
hoists each nullary dict method into a top-level function (`__saga_dictmethod_
<dict>_<idx>`) and references it from the dict tuple. Phase 3 just **exports**
those functions and has importers **call them remotely**.

What was actually implemented:

- **Producer (supply-driven hoisting).** `plan_dict_method_hoists` now hoists
  *every* local nullary dict method, not only the ones with a local call site,
  and the dict-constructor lowering **exports** each hoisted function. A producer
  can't know which of its dicts an importer will specialize, and separate
  compilation means we can't add the function later — so it hoists all of them
  proactively. Empirically behavior-neutral and comparable Core size (an inline
  closure just becomes a named top-level fn).
- **Consumer (remote call).** `classify_dict_specialization` admits an imported
  `KnownImpl`: it resolves the dict's `DictRef` to the producer's Erlang module,
  reconstructs the deterministic hoisted name, and emits a direct
  `call 'mod':'__saga_dictmethod_<dict>_<idx>'(args…, _Evidence, _ReturnK)` via a
  new `CpsCallee::Remote` threaded through `lower_runtime_cps_apply`. A
  saturation guard (`trait_method_user_arity == supplied`, from the cross-module
  trait signature) keeps partial applications on the dict path.

Why this is simpler than the plan's original shape:

- **No `TraitImplMethodInfo` export needed.** The consumer *derives* everything:
  the hoisted name is deterministic from the (globally canonical) dict name + the
  method index; the Erlang module comes from resolving the `DictRef`; the arity
  is `supplied + (cps ? 2 : 0)`, where `cps` comes from `CallEffectInfo` (which
  already reflects the impl's per-method effects cross-module). So anchor 3 holds
  without a new fact.
- **No private-helper policy.** Because the body stays in its defining module and
  is called remotely (not cloned into the caller), private helpers it calls are
  always in scope. The whole private-helper-cloning problem evaporates. (Body
  *inlining* — and with it the private-helper question — only returns at
  Phase 4/5, where the Generic fold genuinely needs the body caller-local.)
- The open design question is still resolved the same way: per-method effects are
  the boundary (`cps` is per-method via `CallEffectInfo`/`method_cps_shape`), not
  impl-level `needs`.

Tradeoff vs. clone-caller-local: a remote call has marginally more overhead than
an inlined body, but it is still a *direct* call (no dict tuple build, no
`element/2`), which is Phase 3's whole point. Inlining for further speedup is the
Phase 5 fusion track.

Acceptance (met):

- `99f-generic-derived-tojson`: imported-fallback count `14 → 0` (`8 → 22`
  specialized; the remaining 10 fallbacks are all `parameterized`, Phase 4).
- `cross-module-dict-specialization/02-imported-concrete-method`: both `Lib` and
  `Main` report `1 specialized | 0 fell back`; runtime output unchanged (`"15"`).
- `cross_module_trait_dict_compiles_with_erlc` links the importer's remote call
  against the producer module — proof the call resolves to a real exported fun.
- saga_json building-block leaf impls (`ToJson Int/String/…`) now specialize
  cross-module from `EncodeDerive`; the parameterized `Record`/`And`/`Labeled`
  walk remains for Phase 4.

### Phase 4 — The two trait-neutral rewrites

**Split into 4a (done) and 4b (next).** 4a implemented `inline_known_impl_body`
for **local parameterized** dict chains in `src/codegen/generic_fold.rs` (commit
`dd282b9`). `case_of_known_constructor` and the collapse-before-inline ordering
were deferred to 4b: 4a's scrutinees are always variables (the `Rep` value
arrives via `to x`, not yet inlined), so there is no known-constructor scrutinee
to cancel until Phase 5 inlines `to`. 4b therefore lands alongside the Phase 5
`m … (to x)` trigger, which is the only thing that exercises the rewrite.

- `inline_known_impl_body` (4a, done): pull the method `Lambda` from
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
