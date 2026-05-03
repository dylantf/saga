# Evidence-Vector Calling Convention for Effects

## Motivation

Today every effectful function takes one parameter per handler op plus a
return continuation. A function declared `needs {Fail, Log, State}` lowers
to something like:

```
fun(args..., _Handle_Fail_fail, _Handle_Log_log, _Handle_State_get,
    _Handle_State_put, _ReturnK)
```

Every call site has to compute, from the callee's resolved effect row,
which handler params to thread and in what order. This computation lives
in [src/codegen/lower/mod.rs](../../src/codegen/lower/mod.rs)
(`lower_resolved_fun_call`, `lower_effectful_var_call`,
`append_handler_args`, `effect_handler_ops`) and gets re-derived at every
boundary including cross-module calls.

The recurring bug shape this convention produces:

- **Arity drift** — caller and callee disagree on how many handler
  params the function expects. Often manifests as `no matching clause for
  the given arguments` at runtime when the callee's clause patterns don't
  match the actual arity.
- **Declared-but-unused effects** — function declares `needs {Fail}` but
  never uses a fail op. CPS expansion adds the handler param, but some
  lowering paths skip it, producing a mismatch.
- **Cross-module convention skew** — the caller derives the effect order
  from one resolution and the callee from another. Subtle ordering bugs
  follow.
- **Adding an effect op is non-local** — a new op on an existing effect
  changes the arity of every function that uses that effect, every call
  site, and every handler representation.

## Approach

Koka uses a single *evidence vector* parameter that carries handler
information for the whole effect row. See Xie & Leijen, "Generalized
Evidence Passing for Effect Handlers", 2021. Effekt does something
similar.

Under this scheme every effectful function's calling convention becomes:

```
fun(args..., _Evidence, _ReturnK)
```

`_Evidence` is a runtime structure (tuple, map, or vector) keyed by
effect/op identity. Inside the callee, an effect call `op!(args)` looks up
its handler in the evidence and invokes it.

What this buys us:

- **Uniform calling convention.** Every effectful function takes the same
  number of params modulo user args. No per-call arity computation.
- **Adding an op is local.** A new op on an existing effect just adds an
  entry to the evidence; arity is unchanged.
- **Cross-module simplicity.** Callers don't need to know the callee's
  exact ops — they hand over the current evidence and the callee indexes
  in.
- **A whole class of bugs disappears.** Specifically the arity-drift /
  ordering-skew bugs catalogued above.

What it does *not* buy:

- It does **not** fix CPS sequencing bugs (when/how to invoke the
  continuation). Those are about whether nested effectful calls
  CPS-chain or evaluate-then-wrap. See
  [effectful-call-detection.md](effectful-call-detection.md) — that
  refactor is orthogonal and should land independently.

## Design questions to settle

- **Evidence representation.** Tuple indexed by effect order? Map keyed
  by `effect.op` atoms? Tuple has zero lookup cost but requires a stable
  total order. Map is more flexible under row polymorphism but pays a
  lookup-per-op cost. Profile both on representative effect-heavy
  workloads (likely `tests/e2e/tests/effects_test.saga`).
- **Row polymorphism.** Open rows (`..e`) mean the evidence size isn't
  statically known at the partial-application boundary. Decide whether
  partial application copies the inherited evidence into the closure or
  re-resolves it at saturation.
- **Handler stacking.** Nested `with` blocks today produce nested closure
  captures. Under evidence passing, each `with` extends the evidence with
  the new layer. Confirm semantics still match the nested-handler model
  documented in [docs/effect-implementation.md](../effect-implementation.md).
- **BEAM-native effects.** Actor / Process / Ref / Timer families
  currently have custom op bodies. They still need to be reachable via
  evidence; design the evidence entry shape to accommodate both
  user-defined CPS handlers and BEAM-native dispatch.
- **Multishot.** Today multishot is "just call K twice" because K is a
  closure. Under evidence passing the same property must hold —
  evidence-bound handlers must remain plain closures, not stateful
  registrations.

## Scope

This is a substantial refactor touching:

- Handler lowering (`codegen/lower/effects.rs`,
  `lower_handler_def_to_tuple`, etc.)
- Every call site that currently appends per-op handler args
- `FunInfo` / `arity_and_effects_from_type` and the resolution map
- Partial application and eta expansion
- Cross-module CPS expansion in `init.rs`
- Test fixtures and the e2e suite (calling convention is observable in
  emitted Core Erlang)

Probably weeks, not days. Worth gating on:

1. The detection refactor in [effectful-call-detection.md](effectful-call-detection.md)
   landing first, so the lowerer's surface is smaller before we churn it.
2. A property-test harness that runs effect-heavy programs on BEAM, so
   we can prove the new convention preserves observable semantics.

## Acceptance

The refactor is done when:

- Every effectful function takes `(user_args..., _Evidence, _ReturnK)`,
  no more per-op handler params.
- Adding a new op to an existing effect requires no changes to callers
  or other call sites.
- Cross-module calls don't recompute handler ordering — they just pass
  the current evidence.
- The full test suite (including BEAM execution) passes with no
  observable behavior change relative to the per-op convention.
