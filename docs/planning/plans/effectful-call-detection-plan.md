# Effectful-Call Detection: Implementation Plan

Concrete plan for consolidating effectful-call detection in the lowerer.
Supersedes the analysis in
[../effectful-call-detection.md](../effectful-call-detection.md), which
describes the bug shape and motivation. Read that first for context.

This plan also sets up groundwork for the upcoming evidence-passing
calling convention ([../evidence-passing.md](../evidence-passing.md)). The
data structures introduced in Phase 4 are designed so that evidence
passing becomes a localized field-deletion rather than a call-site rewrite.

## Current state (verified, not from the older doc)

The audit-based work has already partially landed:

- `is_effectful_call_arg` exists at [src/codegen/lower/mod.rs:982](../../../src/codegen/lower/mod.rs#L982)
  and is the closest thing to a canonical predicate today.
- The two `Stmt::Let` lowering paths the older doc flagged
  ([src/codegen/lower/exprs.rs:964](../../../src/codegen/lower/exprs.rs#L964)
  and [exprs.rs:1284](../../../src/codegen/lower/exprs.rs#L1284)) already
  use it.
- One regression test, `cross_module_nested_effectful_calls_abort_correctly`,
  exists at [tests/module_codegen_integration.rs:1043](../../../tests/module_codegen_integration.rs#L1043).

What's still inconsistent:

- `is_effectful_call_name` ([mod.rs:973](../../../src/codegen/lower/mod.rs#L973))
  — Var-only, no saturation check, used in
  [effects.rs:115](../../../src/codegen/lower/effects.rs#L115).
- `has_nested_effect_call` ([util.rs:248](../../../src/codegen/lower/util.rs#L248))
  — syntactic only, misses effectful function calls. Used at
  [exprs.rs:281](../../../src/codegen/lower/exprs.rs#L281),
  [exprs.rs:997-998](../../../src/codegen/lower/exprs.rs#L997) (two
  adjacent uses inside a `Stmt` walker), and
  [exprs.rs:1289](../../../src/codegen/lower/exprs.rs#L1289).
- `lower_expr_with_call_return_k` ([exprs.rs:84](../../../src/codegen/lower/exprs.rs#L84))
  — dispatches on `collect_qualified_call` then `collect_fun_call`
  separately rather than gating on a unified predicate first.

## Phase 1 — Consolidate to one predicate

Goal: a single function answers **"is this a saturated effectful function
call?"** and every dispatcher uses it. No new behavior, only
consolidation.

Note the scope. Direct effect-op syntax (`op!`) still goes through
`collect_effect_call_expr` — that's a different question and isn't
duplicated. Detecting whether *any subexpression* nested in a branch is
effectful still goes through `has_nested_effectful_expr`, which is built
on top of the canonical predicate but answers a structural question
about composite expressions. The predicate this phase consolidates is
specifically the saturated-call shape: an `App` (or `App` chain) whose
head resolves to an effectful callable and whose user arity is met.

### Steps

1. **Rename** `is_effectful_call_arg` → `expr_is_effectful_call`
   ([mod.rs:982](../../../src/codegen/lower/mod.rs#L982)). Pure rename,
   ~6 call sites updated mechanically. The `_arg` suffix dates from the
   first use site; the predicate is general.

2. **Replace** the `collect_fun_call + is_effectful_call_name` pair in
   [effects.rs:114-117](../../../src/codegen/lower/effects.rs#L114) with
   `self.expr_is_effectful_call(expr)`. Then **delete
   `is_effectful_call_name`** ([mod.rs:973](../../../src/codegen/lower/mod.rs#L973))
   — it has no other callers and its missing saturation/qualified-call
   coverage is the bug shape we're trying to eliminate.

3. **Migrate `has_nested_effect_call` callers** to
   `has_nested_effectful_expr`:
   - [exprs.rs:281](../../../src/codegen/lower/exprs.rs#L281) in
     `lower_terminal_effectful_expr_to_k` — straight swap; the
     resolution-aware version is strictly more correct.
   - [exprs.rs:997-998](../../../src/codegen/lower/exprs.rs#L997) — two
     adjacent calls inside a `Stmt::Expr` / `Stmt::Let` walker. Both
     swap.
   - [exprs.rs:1289](../../../src/codegen/lower/exprs.rs#L1289) in
     `lower_block_with_k` — same.

   After migration, `has_nested_effect_call` and its helper
   `branch_has_effect` in `util.rs` become dead code; delete them.

4. **Reshape `lower_expr_with_call_return_k`**
   ([exprs.rs:84-124](../../../src/codegen/lower/exprs.rs#L84)).
   Keep the head-shape dispatch — it has to choose between
   `lower_qualified_call`, `lower_resolved_fun_call`, and
   `lower_effectful_var_call` based on the syntactic head — but gate the
   whole effectful path behind `expr_is_effectful_call`. The head-shape
   match decides *how* to lower; the predicate decides *whether* to lower
   as effectful. That structural separation is what the Phase 4 tagging
   work depends on.

### Acceptance for Phase 1

- All effectful-call detection routes through `expr_is_effectful_call`.
- `is_effectful_call_name`, `has_nested_effect_call`, and
  `branch_has_effect` are deleted.
- Existing test suite passes including
  `cross_module_nested_effectful_calls_abort_correctly` and the
  related `_via_let_` variant.
- `cargo clippy` clean.

This is a one-PR change. No new tests yet — that's Phase 2.

## Phase 2 — Regression tests for every call shape

Goal: every call shape that should produce a CPS call has a
BEAM-executing regression test. The `cross_module_nested_*` tests are
the template; copy their structure.

### Template

[tests/module_codegen_integration.rs:1043](../../../tests/module_codegen_integration.rs#L1043).
Each test:

1. Defines a lib module with an effectful function that aborts on a
   given input (and returns successfully otherwise).
2. Defines a main module that nests the effectful call inside another
   effectful call, plus a top-level handler that catches the abort.
3. Typechecks both, emits Core Erlang, runs `erlc`, runs `erl -noshell`.
4. Asserts the BEAM output pattern-matches `Err _`, never `Ok _` or a
   `no matching clause` crash.

### Shapes to cover

For each shape, a test that nests *that* shape as the inner argument of
an outer effectful call where the inner aborts. Status:

| Shape | Status | Test name (suggested) |
|---|---|---|
| `f x` (Var head, same module) | ✓ exists | implicit in current suite |
| `Mod.f x` (qualified head, cross-module) | ✓ exists | `cross_module_nested_effectful_calls_abort_correctly` |
| `Mod.f x` via let in block | ✓ exists | `cross_module_nested_effectful_calls_via_let_abort_correctly` |
| `let g = factory(); g x` (effectful var) | **needed** | `effectful_var_call_aborts_correctly` |
| Dict-elaborated trait method (effectful impl) | deferred — see below | — |
| Eta-reduced / first-class effectful callback | **needed if not already covered** | `eta_reduced_effectful_lambda_aborts_correctly` |
| Lambda call `(fun x -> abort_op! x) y` | deferred | — |
| Row-polymorphic forwarder calling effectful arg | deferred | — |

**Dict-elaborated trait methods: known bug, deferred.** Effectful trait
method calls do typecheck today (with impl-level `needs` clauses, e.g.
`impl Decoder for Box needs {Fail String} { ... }`), but currently
panic the lowerer at
[effects.rs:338](../../../src/codegen/lower/effects.rs#L338) with
`no handler param for op 'Std.Fail.Fail.fail', handler_params: {}`.
Root cause: trait method calls elaborate to
`ExprKind::DictMethodAccess`, a shape neither `collect_fun_call` nor
`collect_qualified_call` recognize, so the predicate misses them and
no handler param gets threaded at the dispatch site. Live repro at
[examples/bugs/dict-method-effectful-call/](../../../examples/bugs/dict-method-effectful-call/).

This is a real bug, but fixing it is **behavior expansion of the
predicate's coverage** — adding `DictMethodAccess` as a recognized
call shape — not consolidation of existing predicates. It's
out of scope for this plan and should be its own follow-up. The repro
project preserves the failure for whoever picks it up.

The two deferred shapes (lambda call, row-polymorphic forwarder) are
deferred for the same reason: the current predicate doesn't recognize
lambda heads (`(fun x -> ...) y` has neither a Var nor QualifiedName
head); making it do so is new logic, not unification of existing
logic.

`op!`-syntax effect calls (including BEAM-native effect families) don't
need a new test here — they're detected via `collect_effect_call`, not
the predicate Phase 1 consolidates. Those have separate coverage.

### Acceptance for Phase 2

- All shapes above have at least one BEAM-executing test.
- Each test asserts `Err _` on abort and `Ok _` on the success path.
- `cargo test --test module_codegen_integration` green.

Separate PR(s) from Phase 1. Easier to review when the predicate change
is already in.

## Phase 3 — Skipped (table-driven matrix later if needed)

The original plan called for a generative property test. Skipping for
now: the combinatorial space (call shape × position × outcome) is small
enough that hand-written BEAM-running regressions in Phase 2 are
cheaper and clearer than property-test infrastructure.

If the shape count grows past what's reasonable to enumerate by hand,
revisit as a small table-driven integration matrix in
`tests/module_codegen_integration.rs` rather than a generative harness.
The same `assert_erlc_compiles` + `erl -noshell` infra applies.

## Phase 4 — Tagging pre-pass (deferred)

**Status: deferred until evidence passing actually begins.**

After Phase 1 lands, the recurring bug class is structurally addressed:
one canonical predicate, audited at consolidation time. The remaining
benefit of a tagging pre-pass is mostly groundwork for evidence
passing — but that groundwork is partial. Evidence passing still has
to touch handler lowering, partial application, `FunInfo` /
`arity_and_effects_from_type`, eta expansion, cross-module CPS
expansion, and call emission. Tagging only helps the call-emission
bullet. Building the pre-pass *as part of* evidence passing — when its
exact shape is constrained by what evidence construction actually needs
— avoids designing the schema twice and paying the migration cost
twice.

The rest of this section documents the design so it's ready when
evidence passing kicks off, not as a commitment to land independently.

Goal (when revived): stop computing per-call effect metadata inline at
every dispatcher. Move the computation to a single pass that produces a
map; the lowerer becomes a read-only consumer.

### Schema

```rust
// src/codegen/call_effects.rs (new file)

/// Per-call metadata. Keyed by the NodeId of an `App` node.
pub struct CallEffectInfo {
    pub kind: CallEffectKind,
    /// Logical user-argument count (excludes handler params and return_k).
    pub user_arity: usize,
    /// Whether this call accepts a return continuation.
    pub needs_return_k: bool,
}

pub enum CallEffectKind {
    /// Pure call. No effect threading.
    Pure,
    /// Effects fully known statically at this call site.
    /// Caller threads exactly these ops, in canonical order.
    StaticOps { ops: Vec<OpKey> },
    /// Row-polymorphic call, or call inside a row-polymorphic context.
    /// `static_ops` (possibly empty) are pinned by a closed prefix; the
    /// rest is forwarded from caller's ambient evidence.
    RowForwarded { static_ops: Vec<OpKey> },
}

pub struct OpKey {
    /// Canonical effect name from `ResolutionResult.effects`,
    /// e.g. `"Std.Fail.Fail"`. Never a source-level alias.
    pub effect: String,
    /// Op name within the effect, e.g. `"fail"`.
    pub op: String,
}

pub type CallEffectMap = HashMap<NodeId, CallEffectInfo>;
```

### Ordering rule

Ops in `StaticOps.ops` and `RowForwarded.static_ops` are sorted
alphabetically by `(effect, op)`. Stable, independent of declaration
source. Whatever ordering today's `effect_handler_ops` produces, the
pre-pass forces this canonical order during the parallel-check migration
phase. Any disagreement surfaces loudly there.

### Why the two effectful variants

`StaticOps` vs. `RowForwarded` makes explicit the distinction the
lowerer encodes implicitly today via `current_effectful_vars` plus
row-resolved types. Row polymorphism is the only place where "what ops
does this call need?" can't be fully answered statically, so it's the
only place that needs its own variant. Everywhere else has been row-
resolved by the time we reach lowering.

Example: the `run` function from
[../effect-implementation.md#row-polymorphism](../../effect-implementation.md):

```dy
fun run : (f: Unit -> Unit needs {Fail, ..e}) -> Unit needs {..e}
run f = f () with { fail msg = () }
```

The call `f ()` inside `run`'s body tags as:

```rust
CallEffectInfo {
    kind: RowForwarded {
        static_ops: vec![OpKey {
            effect: "Std.Fail.Fail".into(),
            op: "fail".into(),
        }],
    },
    user_arity: 1,
    needs_return_k: true,
}
```

`Fail` is statically pinned (handled by the local `with`); `..e` is
forwarded from `run`'s caller.

### Effectful let-bindings

`let g = factory(); g x` does **not** need a separate variant. The
pre-pass walks lets in lexical order, computes the effect kind of the
let's value, propagates it to a scope-tracked entry for `g`, and when
it tags `g x` it produces a normal `StaticOps` / `RowForwarded` /
`Pure` info using the binder's stored signature. The indirection lives
in the pre-pass, not the schema. Today's `current_effectful_vars`
mutation in the lowerer goes away.

### Pipeline placement

After `src/codegen/resolve.rs` (backend resolve), before
`src/codegen/lower/`. New file `src/codegen/call_effects.rs`. The
populate pass consumes:

- `ResolutionResult` (for canonical effect names in callee types)
- `ResolutionMap` (for callable identity)
- `ModuleCodegenInfo` (for cross-module arity / FunInfo)

Output stored as a new field on `CompiledModule`:

```rust
struct CompiledModule {
    codegen_info: ModuleCodegenInfo,
    elaborated: Program,
    resolution: ResolutionMap,
    front_resolution: ResolutionResult,
    call_effects: CallEffectMap,  // new
}
```

**Active-module path.** `CompiledModule` only covers compiled/imported
modules. The active module being lowered goes through
`emit_module_with_context` ([src/cli/build.rs:301](../../../src/cli/build.rs#L301)),
which normalizes and resolves directly without producing a
`CompiledModule`. The pre-pass needs an explicit path for this case
too — either:

- run the pre-pass inside `emit_module_with_context` after backend
  resolve and before lower, threading a `&CallEffectMap` into the
  lowerer alongside the existing `CodegenContext`, or
- refactor so the active module also flows through a `CompiledModule`-
  shaped bundle, unifying the two paths.

The first is less invasive and matches where similar metadata is
threaded today. The second is cleaner long-term but is its own
refactor. Decide when Phase 4 actually starts, with current code in
hand — the right answer depends on what the build pipeline looks like
at that point.

### Lookup discipline in the lowerer

```rust
impl Lowerer {
    fn call_effects(&self, expr: &Expr) -> Option<&CallEffectInfo> {
        if !matches!(expr.kind, ExprKind::App { .. }) {
            return None;
        }
        Some(self.call_effect_map.get(&expr.id).unwrap_or_else(|| {
            panic!(
                "App node {:?} missing call effect tag — pre-pass missed a shape",
                expr.id,
            )
        }))
    }

    fn expr_is_effectful_call(&self, expr: &Expr) -> bool {
        self.call_effects(expr)
            .is_some_and(|i| !matches!(i.kind, CallEffectKind::Pure))
    }
}
```

`Option` for non-App; `expect`-style panic for App. This is the
structural guarantee — a forgotten shape crashes loudly at the first
call site that visits the node, instead of silently falling through to
value-mode and producing `Ok(error_tuple)` at runtime.

### Migration phasing

Sub-phases inside Phase 4. Each is its own PR.

#### 4a. Add the pre-pass, don't use it yet

- Add `src/codegen/call_effects.rs` with the populate pass.
- Add `call_effects: CallEffectMap` to `CompiledModule`.
- Wire population into the build pipeline.
- The lowerer ignores the new field. No behavior change.

#### 4b. Parallel-check phase

In `expr_is_effectful_call`, look up the map *and* run the old inline
check, asserting they agree:

```rust
fn expr_is_effectful_call(&self, expr: &Expr) -> bool {
    let map_says = self.call_effects(expr).is_some_and(|i| !matches!(i.kind, CallEffectKind::Pure));
    let inline_says = self.legacy_expr_is_effectful_call(expr);
    debug_assert_eq!(map_says, inline_says, "tag/inline disagreement at {:?}", expr.id);
    map_says
}
```

Run full suite plus Phase 2 regression tests plus Phase 3 property test
under `--cfg debug_assertions`. Any disagreement is a bug in the
pre-pass; fix until clean.

Same parallel check for `call_performs_effect`'s outputs (handler ops,
user arity) — assert the pre-pass's stored values match what the inline
computation would produce.

#### 4c. Cut over

After a clean parallel-check run:

- Delete the inline computations.
- Lowerer reads the map only.
- `current_effectful_vars` field deleted (its content is now in the
  pre-pass's tag for downstream calls).

#### 4d. Tighten the panic

Audit every lowering-mode dispatcher to ensure App nodes always go
through `call_effects`. Convert `expect()` from a debug aid into a
load-bearing structural assertion.

### Acceptance for Phase 4

- `expr_is_effectful_call` is a one-line map lookup.
- All per-call effect metadata (ops, arity, return_k) comes from the
  pre-pass. The lowerer computes none of it inline.
- A new call shape that the pre-pass forgets crashes the compiler
  loudly at lowering time rather than miscompiling.
- Phase 2 + Phase 3 tests still pass.

## Why this ordering

Phase 1 is the load-bearing change. It eliminates the recurring bug
class by consolidating to one predicate, deletes ~150 lines of
duplicated/strictly-weaker code, and adds no new infrastructure.

Phase 2 follows because regression coverage is leverage and the dict-
elaborated case is a real gap, not a theoretical one.

Phase 3 is skipped — the space is small enough for hand-written tests.

Phase 4 is deferred. It would be a precondition for evidence passing's
call-site work *if* evidence passing weren't going to redesign the
schema anyway. Since it is, build tagging then. Phase 1 + 2 are the
critical path; Phase 4 is groundwork that should be sequenced with the
work it supports, not ahead of it.

## Connection to evidence passing

Phase 4 is groundwork for [../evidence-passing.md](../evidence-passing.md).
After evidence passing lands, the schema collapses to:

```rust
pub struct CallEffectInfo {
    pub effectful: bool,
    pub needs_return_k: bool,
}
```

`CallEffectKind`, `OpKey`, `user_arity` all delete. Migration:

- `Pure` → `effectful: false`
- Both `StaticOps` and `RowForwarded` → `effectful: true`. Op lists are
  no longer needed at the call site because the caller hands over its
  ambient evidence (possibly extended at a local `with`).
- `user_arity` → just `args.len()` under uniform convention.

Two of the four fields disappear in one PR, and that PR doesn't have to
touch every call site — only the pre-pass and the small set of lowerer
functions that consume `kind`. That's the leverage of doing tagging
first.

`RowForwarded.static_ops` carries forward as the data evidence
construction needs at `with` sites: "what ops did this `with` block
locally pin into the evidence we're extending?" Without recording it
during tagging, evidence passing has to recompute it from types — the
same kind of duplication that motivates this whole plan.

## Deferred: lowering-mode surface cleanup

The eight lowering-mode entry points listed in the older planning doc
(`lower_expr_value`, `_tail`, `_with_call_return_k`,
`_with_installed_return_k`, `_terminal_effectful_*_with_return_k`,
`_to_k`, `lower_handler_owned_expr`) overlap heavily. After Phase 4 the
duplication of *detection* is gone; the duplication of *dispatch shape*
remains.

Worth one pass of merging the `_with_return_k` and `_to_k` variants
behind a `K` enum, but defer until Phases 1–4 land. The current
`LowerMode::Value` / `LowerMode::Tail` enum at
[mod.rs:109](../../../src/codegen/lower/mod.rs#L109) is read by only
two dispatchers; either commit (route everything through it) or delete.
Either decision is fine — but only after the predicate work is done,
otherwise the consolidation cements whatever inconsistency was present.

This phase is not on the critical path for evidence passing.

## Risks

- **NodeId stability through normalize.** The pre-pass keys on `NodeId`.
  If the normalize phase ([src/codegen/normalize.rs](../../../src/codegen/normalize.rs))
  mints fresh IDs for App nodes that started as source App nodes, the
  map breaks. The pipeline doc ([../../pipeline.md:87](../../pipeline.md))
  claims source identity is preserved through elaboration; verify the
  same holds for normalize before Phase 4a lands. If not, run the pass
  after normalize, or teach normalize to preserve App IDs.

- **Pre-pass scope tracking.** Effectful let-bindings require lexical
  scope tracking in the pre-pass, mirroring today's
  `current_effectful_vars` mutation. Bug surface if scope walks
  desync from the lowerer's. Phase 4b's parallel check catches this.

- **Performance.** Running the inline check *and* the map lookup during
  Phase 4b doubles work in debug builds. That's intentional and
  temporary. Release builds can `cfg(debug_assertions)` the
  parallel-check. Don't ship 4b to release.

- **Cross-module arity drift.** The pre-pass needs each module's
  `FunInfo` to compute `user_arity`. The build pipeline already
  assembles `CompiledModule` bundles before lower; thread them into the
  pre-pass the same way the lowerer reads them today.

## Acceptance

For the work this plan commits to landing now:

- Single predicate `expr_is_effectful_call` across the lowerer (Phase 1).
- `is_effectful_call_name`, `has_nested_effect_call`, and
  `branch_has_effect` deleted (Phase 1).
- BEAM-executing regression tests for the two needed shapes —
  effectful-var and eta-reduced effectful callback — passing (Phase 2).
- `cargo test` and `cargo clippy` clean.

For the deferred Phase 4 work, the design above is the spec to revisit
when evidence passing kicks off. It is not a commitment to land
independently.
