# Evidence-Passing Calling Convention: Implementation Plan

Concrete plan for the evidence-vector calling convention refactor.
Supersedes the design sketch in
[../evidence-passing.md](../evidence-passing.md), which captures the
motivation. Read that first.

This plan also assumes the work in
[effectful-call-detection-plan.md](effectful-call-detection-plan.md)
Phase 1+2 is landed, since the canonical predicate is load-bearing for
deciding whether to thread evidence at each call site.

## Design summary

These decisions came out of a separate design session. Locked in:

1. **Evidence shape.** Tuple of per-effect entries, sorted canonically
   by effect tag. Each entry is `{EffectAtom, OpTuple}` where
   `OpTuple` is the per-op handler closures sorted alphabetically by
   op name. Always tagged for runtime lookup and debuggability.
2. **No `hevv` per entry.** Saga has no non-scoped resumes; one
   handler handles its whole continuation stack. Saved-evidence
   field omitted.
3. **No mask levels.** Innermost-wins semantics fall out of canonical
   ordering: a `with` for an effect already in scope replaces that
   effect's entry at its existing canonical position. There is no
   surface syntax for accessing shadowed outer handlers, so no need
   for mask machinery.
4. **No prompts, no yield checks.** Saga's CPS is user-level and has
   no equivalent of Koka's `is_yielding` flag. Skip.
5. **Calling convention.** Pure functions unchanged. Effectful
   functions take `(user_args..., _Evidence, _ReturnK)`. The
   "is this call effectful?" decision uses
   `expr_is_effectful_call` from the detection plan.
6. **Projection at call boundaries.** Closed-row narrowing only.
   Caller has `{Fail, IO, State}`, callee declares `{Fail}` closed →
   project. Callee declares `{..e}` open → pass full evidence.
7. **`return` clause stays separate.** `_ReturnK` is its own
   parameter alongside `_Evidence`. The return clause runs on
   successful completion at a specific handler boundary; conceptually
   distinct from op invocation.
8. **Effectful-var bindings.** `let g = factory(); g x` — `g` is a
   closure that takes evidence + return*k like any effectful function.
   Calling threads \_current* evidence at call time, not evidence at
   binding time.
9. **BEAM-native effects: zero special-case.** Today's
   `build_beam_native_op_fun` synthesizes a CPS-shaped closure
   `fun(args, K) -> let R = native_call() in K(R)` that already has
   the same shape as user-defined op closures. Under evidence
   passing, these closures sit in evidence entries identically to
   user handlers. The future fast-path optimization
   ([effects.rs:1517](../../../src/codegen/lower/effects.rs#L1517),
   currently a no-op hook) is orthogonal.

## Phases

### (DONE) Phase 0 — BEAM-execution property harness

This is the regression net the cutover in Phase 3 will lean on. It
works against the current convention so it has standalone value as a
regression test of today's behavior.

**Goal:** a CI-runnable test suite that compiles and executes
effect-heavy Saga programs on BEAM, asserting observable output.
Diffable. Catches regressions in any phase that follows.

**Coverage:**

- Basic op call (resume / abort)
- Nested `with` blocks (handler stacking)
- Partial application of effectful functions
- Cross-module effectful calls
- Multishot resumption
- BEAM-native effects (Process, Ref, Timer)
- Mixed BEAM-native and CPS handlers in the same program
- Effectful var bindings (`let g = factory(); g x`)

**Shape:** new file `tests/effect_property_tests.rs`. ~30–50 small
saga programs as inline string fixtures, each with a known stdout/
result assertion. Same `assert_erlc_compiles` + `erl -noshell` infra
as `tests/module_codegen_integration.rs`.

**Acceptance:**

- All fixtures pass on current `main`.
- Suite runs in CI.
- Failures point at lowering, not test scaffolding (clear assertion
  messages naming the fixture).

This phase is independently valuable; it can ship even if evidence
passing never lands.

### (DONE) Phase 1 — Evidence runtime primitives

**Goal:** define the evidence-vector data layout and helper functions
in isolation. No language-level emission change yet.

**New file:** `src/codegen/lower/evidence.rs`. Contents:

- `build_evidence_entry(tag: &str, op_closures: Vec<CExpr>) -> CExpr`
  — emits `{EffectAtom, OpTuple}` Core Erlang
- `insert_canonical(evidence: CExpr, new_entry: CExpr) -> CExpr` —
  emits Core Erlang that finds canonical position by tag compare,
  builds new tuple. Replaces existing entry if tag matches (innermost
  wins).
- `find_evidence(evidence: CExpr, tag: &str) -> CExpr` — emits Core
  Erlang for runtime lookup. For closed rows the caller computes the
  static index instead and emits `element/2` directly; this helper is
  for open-row paths.
- `project_evidence(evidence: CExpr, tags: &[&str]) -> CExpr` —
  builds a new tuple containing only the named tags in canonical
  order. Used for closed-row narrowing at call boundaries.
- `evidence_index_of(layout: &EvidenceLayout, tag: &str) -> usize` —
  Rust-side helper for compile-time index computation.
- `EvidenceLayout` struct — records the canonical-ordered effect tags
  for a known-shape evidence vector at a specific lowering point.

**Runtime support:** add a small Erlang module
`src/stdlib/evidence.bridge.erl` exposing `find_evidence/2`,
`insert_canonical/2`, `project_evidence/2` for the cases where
inlining the operations isn't practical. Function bodies are O(n)
linear in tuple size; n is typically ≤5.

**Acceptance:**

- Module compiles with `cargo build`.
- Unit tests in `evidence.rs` for each helper, asserting the emitted
  Core Erlang structure (no BEAM execution needed at this phase).
- `cargo clippy` clean.
- No other compiler code calls into this module yet.

### (DONE) Phase 2 — Pre-pass for per-call evidence metadata

**Goal:** populate a `NodeId → CallEffectInfo` map ahead of lowering.
The lowerer becomes a read-only consumer for "is this call effectful,
what evidence layout does it need, does it project."

This is the deferred Phase 4 from the detection plan, restored
because evidence passing genuinely needs it: the lowerer has to know
at every call site whether to project, pass through, or build empty
evidence — that's not derivable from raw syntax.

**Schema** (from
[effectful-call-detection-plan.md](effectful-call-detection-plan.md)):

```rust
pub struct CallEffectInfo {
    pub kind: CallEffectKind,
    pub user_arity: usize,
    pub needs_return_k: bool,
}

pub enum CallEffectKind {
    Pure,
    StaticOps { ops: Vec<OpKey> },
    RowForwarded { static_ops: Vec<OpKey> },
}

pub struct OpKey {
    pub effect: String,  // canonical, e.g. "Std.Fail.Fail"
    pub op: String,
}
```

**Implementation:**

- New file `src/codegen/call_effects.rs`.
- New field `call_effects: CallEffectMap` on `CompiledModule`.
- Active-module path through `emit_module_with_context`
  ([src/cli/build.rs:301](../../../src/cli/build.rs#L301)) — thread
  the map alongside `CodegenContext` rather than refactoring through
  `CompiledModule`. Less invasive.
- Pre-pass walks the elaborated program, computes for each `App`
  node:
  - Resolve callee head (Var, QualifiedName, or via effectful-var
    binder)
  - Look up callee type's effect row
  - Build `CallEffectInfo` with canonical-ordered ops
- Effectful let-bindings handled by lexical scope walk: when the let
  value is itself a `StaticOps`/`RowForwarded` call, propagate to
  binder for use at later call sites.

**Parallel-check sub-phase:**

- In `expr_is_effectful_call`, look up the map _and_ run the existing
  inline check, asserting they agree under
  `cfg(debug_assertions)`. Run full suite + Phase 0 harness. Any
  disagreement is a pre-pass bug; fix until clean.

**Acceptance:**

- Pre-pass populates the map for every `App` node in compiled and
  active modules.
- Parallel-check passes on full suite + Phase 0 harness.
- `expect()` on missing tags converts what is today a silent miscompile
  into a loud panic.
- No emission change yet — lowerer still uses old computation post-
  lookup.

### Phase 3 — The cutover

**Goal:** switch the calling convention to evidence passing across
the whole compiler in one coherent PR. Convention has to flip
atomically; cross-module calls and intra-module calls must agree.

This is the big phase. Single PR if practical, otherwise a stack of
commits in one branch that merge together.

**Sub-stages within the PR (commit-level decomposition):**

#### 3a. FunInfo and arity model

- [src/codegen/lower/init.rs](../../../src/codegen/lower/init.rs):
  `arity_and_effects_from_type` produces
  `(user_arity, has_evidence, has_return_k)` instead of per-op
  arity expansion.
- [src/codegen/lower/util.rs](../../../src/codegen/lower/util.rs):
  `param_absorbed_effects_from_type` repurposed (or deleted — its
  purpose was per-op param accounting that no longer applies).
- `FunInfo` carries an `EvidenceLayout` for closed-row callees and
  a sentinel for row-polymorphic callees.

#### 3b. Handler emission

- [src/codegen/lower/effects.rs](../../../src/codegen/lower/effects.rs)
  `lower_handler_def_to_tuple` — already produces an op tuple sorted
  by op name. Wrap with `{EffectAtom, OpTuple}` at the use site
  (the `with` boundary), not at the handler-value site, so handler-
  bound vars (`let h = handler for Foo { ... }`) keep their current
  shape internally.
- `lower_with_inherited_return_k` ([effects.rs:416](../../../src/codegen/lower/effects.rs#L416)):
  build the new entry, call `insert_canonical` on the inherited
  evidence parameter, pass extended evidence to body.
- `build_beam_native_op_fun` ([effects.rs:369](../../../src/codegen/lower/effects.rs#L369))
  unchanged — the synthesized closure body is identical.
- `current_handler_params` field deleted (its information is now in
  the evidence vector at runtime).

#### 3c. Op-call emission

- `lower_effect_call` ([effects.rs](../../../src/codegen/lower/effects.rs)):
  - Closed row: emit
    `element(OpIdx, element(2, element(EffectIdx, Evidence)))`
    using `EvidenceLayout` from `CallEffectInfo`.
  - Open row: emit `find_evidence(Evidence, EffectAtom)` then index
    by op.
- `effect_handler_ops` and `append_handler_args` deleted.

#### 3d. Call-site emission

- `lower_resolved_fun_call` and `lower_effectful_var_call`
  ([mod.rs](../../../src/codegen/lower/mod.rs)): replace per-op
  handler appending with a single evidence argument.
- For `StaticOps` callees: emit projection
  (`project_evidence(Evidence, CalleeTagList)`) when callee row is
  a strict subset of caller row; otherwise pass `Evidence` directly.
- For `RowForwarded` callees: pass `Evidence` directly.
- Append `_ReturnK` after evidence as today.

#### 3e. Partial application and eta

- Partial-app closures capture current evidence at creation time.
- Eta-expansion of effectful functions builds a closure that takes
  remaining args and forwards captured evidence + ambient
  `_ReturnK`.

#### 3f. Cross-module CPS expansion

- `init.rs` ([init.rs](../../../src/codegen/lower/init.rs)) per-
  module FunInfo registration: cross-module callees expose their
  evidence layout via `ModuleCodegenInfo`. Caller projects against
  callee's published layout.

#### 3g. Stdlib recompilation

- All stdlib `.saga` files recompile under the new convention.
- `_build/.stdlib/` cache fingerprint changes (driven by compiler
  build), so users' next `saga build` invalidates correctly without
  manual intervention.

#### 3h. Carry-over tightening from Phase 2

Items left as TODO at the close of Phase 2 that the cutover must absorb,
because they're cheap once the call sites are being touched anyway:

- **Extend the normalize NodeId stability test.** Today's
  [`normalize::tests::normalize_preserves_app_node_ids`](../../../src/codegen/normalize.rs)
  only covers a parse → normalize round-trip on a program with no effect
  calls, so it never exercises `lift_to_let`. Add a fixture that contains
  nested effect calls (`1 + ask!()`, etc.) so the lift path runs, and
  assert that every pre-normalize `App` id is still reachable post-
  normalize. The pre-pass keys on these ids; if a future normalize
  change drops or rewrites them, Phase 3's evidence threading silently
  miscompiles.
- **Make `user_arity` semantics explicit on `Pure` entries.** Phase 2's
  parallel-check enforces *agreement* between map and inline, not a
  particular value, and the two paths happen to agree only because they
  were tuned to. Phase 3 should either canonicalize `Pure.user_arity`
  to `0` everywhere (and update both producers) or add a debug assert
  in the cutover code that `user_arity` is never *read* on `Pure`
  entries — whichever fits the consumer cleaner.
- **Re-evaluate the `head_open_row` lookup table.** Phase 2 builds it
  in `populate_call_effects` by iterating the resolution map and
  consulting `check_result.env` / `ctx.modules[...].codegen_info.exports`.
  If Phase 3a moves the `is_open_row` flag onto `FunInfo` directly
  (likely, since the cutover already touches `FunInfo`), the per-call
  table becomes redundant and can be deleted. Confirm during 3a.

**Acceptance for Phase 3:**

- Phase 0 property harness passes verbatim — every fixture produces
  the same output.
- All existing `cargo test` suites pass.
- Cross-module test fixtures (especially `EffectChain.saga` and the
  bug repros) emit different Core Erlang but produce identical BEAM
  output.
- `_build/` artifacts under representative example projects rebuild
  cleanly.
- The dict-method effectful call repro
  ([examples/bugs/dict-method-effectful-call/](../../../examples/bugs/dict-method-effectful-call/))
  behavior unchanged (still panics — we'll address it in Phase 5).

### Phase 4 — Cleanup

**Goal:** delete the per-op-handler-param machinery now that nothing
uses it. Trims a substantial amount of code that has been bug surface
for as long as the lowerer has existed.

**Deletions:**

- `current_handler_params: HashMap<String, String>` field on
  `Lowerer`.
- `current_effectful_vars` mutation paths (the binder's evidence is
  now in the call-site `CallEffectInfo`).
- `effect_handler_ops`, `append_handler_args`,
  `param_absorbed_effects_from_type`.
- Everything matching `_Handle_<Effect>_<op>` in the parameter
  naming scheme.
- Per-op arity expansion in `FunInfo`.

**Simplifications:**

- `lower_resolved_fun_call` and `lower_effectful_var_call` collapse
  into a single function — the only difference today is how they
  source handler params, and that source is unified.
- The handler-binding compilation paths in
  [exprs.rs](../../../src/codegen/lower/exprs.rs) (static alias,
  conditional, dynamic) collapse since handler-bound vars are no
  longer special at the call site — the wrapping into evidence
  happens at `with`, not at let.

**Acceptance:**

- `cargo test` still green.
- Phase 0 harness still green.
- Net diff is strongly negative (deleting more than the cutover added).

### Phase 5 — Optimizations and follow-ups

Post-cutover, post-cleanup. Each is independently sized and not on
the critical path.

**Direct-native fast path.** Resurrect
`use_direct_native_fast_path` ([effects.rs:1517](../../../src/codegen/lower/effects.rs#L1517))
for BEAM-native ops in non-handler contexts. When the lowerer can
prove there's nothing meaningful between the op call and the native
invocation, fold the closure call into a direct native call. Skips
the closure allocation and the K trampoline.

**DictMethodAccess support.** The deferred bug at
[examples/bugs/dict-method-effectful-call/](../../../examples/bugs/dict-method-effectful-call/).
Under evidence passing, the predicate gap is structurally easier to
fix because the call-shape predicate is already centralized in the
Phase 2 pre-pass. Add `DictMethodAccess` to the recognized shapes and
emit evidence-threaded calls for trait method invocations.

**Closed-row specialization.** When the entire program is
closed-row (common for top-level entry points), the evidence vector
shape is statically known. Specialize op call emission to skip the
runtime tag and use direct positional indexing without the
`{Tag, OpTuple}` wrapping.

**Open-row lookup memoization.** For loops that repeatedly call the
same op under an open row, cache the resolved handler closure once
outside the loop instead of looking up on every iteration. Probably
not worth doing until a real workload shows it.

**Stdlib audit.** Some stdlib functions may have been written
defensively against per-op arity drift. Now that the convention is
uniform, those defenses can come out.

## Risks

- **Hidden assumptions about per-op handler ordering.** Today's
  ordering may not be canonical-alphabetical; some lowering paths
  might rely on declaration order. Phase 2's parallel-check catches
  most of this, but Phase 3's cutover could surface ordering bugs in
  paths that don't go through the pre-pass.
- **Cross-module ABI break.** The new convention is incompatible
  with the old. Anyone with cached `_build/` artifacts gets a
  recompile at first build. This is fine for an in-tree compiler but
  worth a release note.
- **Eta and partial application edges.** Today's eta-expansion has
  subtle special cases for effectful lambdas; the new design
  simplifies them but the simplification has to be exhaustive. The
  property harness must include partial-app coverage explicitly.
- **Multishot semantics.** Confirm that resuming K multiple times
  preserves the _captured_ evidence at each resume. Today this is
  trivially true because handler params are closure-captured.
  Verify under evidence passing that the same property holds — the
  evidence is captured in K's closure, and resuming the closure
  re-establishes the captured environment.
- **`with` block size growth.** Evidence construction at `with`
  allocates a new tuple. For deeply nested `with` blocks, this is
  more allocation than today's per-op param threading (which has no
  per-`with` allocation). The benchmark suite (Phase 0 harness with
  perf annotations) should confirm this is acceptable.

## Acceptance for the whole refactor

- Every effectful function takes `(user_args..., _Evidence, _ReturnK)`
  uniformly.
- Adding a new op to an existing effect requires no changes to
  callers or other call sites — only the effect declaration and
  handler.
- Cross-module calls don't recompute handler ordering; they project
  or forward the evidence.
- Phase 0 property harness passes with no observable behavior change
  vs. the pre-cutover baseline.
- `cargo test` green at every phase boundary.
- Net code reduction (Phase 4 deletions outweigh Phase 1+3 additions).
- The bug shapes the convention was designed to eliminate (arity
  drift, declared-but-unused effects, cross-module skew) cannot be
  expressed in the new lowerer because the inputs to those bugs
  don't exist.

## Sequencing recommendation

Strict sequencing 0 → 1 → 2 → 3 → 4 → 5. Phases 0–2 are independently
valuable and can ship as their own PRs. Phase 3 is the atomic cutover
and lands alone. Phase 4 follows immediately. Phase 5 is opportunistic.

Don't try to interleave Phase 3 with anything else. The convention
break is observable everywhere, and a half-converted lowerer would
take days to debug.
