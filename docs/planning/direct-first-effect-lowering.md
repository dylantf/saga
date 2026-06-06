# Direct-First Effect Lowering

Status: **phase 3 lowering-consumer migration complete**.

This document is the restart plan after the uniform monadic CPS and
selective-uniform backend experiments. The goal is not an entire backend rewrite.
The goal is to keep `main`'s working direct-first runtime model while making
runtime call shape explicit enough that future effect, callback, dictionary,
and handler cases are added in one audited place.

Working name: **direct-first effect lowering**.

Short version:

- direct by default
- CPS only where the current semantics require it
- classification is metadata, not a shadow interpreter
- lowering still owns emission
- optimization is optional, local, and measured

## Terminology

This document uses **pure** in a backend/runtime-shape sense, not as a claim
about referential transparency.

A **direct** or **externally pure** call is a call whose effects do not require a
handler above the call site. It can be emitted as an ordinary function call because
it does not need caller-provided `_Evidence` or `_ReturnK`.

That includes:

- functions whose type has an empty closed effect row;
- functions whose internal effects are fully handled below the call boundary;
- callbacks whose exposed type is effect-free even if their body uses handlers
  internally;
- future specialized calls where a known static handler makes the operation
  net-direct at the call site.

Conversely, a **CPS call** is one whose effects may bubble to the caller. It
must receive evidence and a continuation, even if the body often behaves like a
simple direct computation at runtime.

When the distinction matters, prefer **direct**, **net-direct**, or
**externally pure** over plain **pure**.

## Motivation

The current backend on `main` is simple and working. Direct or externally pure
code lowers mostly directly. Code that crosses a `with` boundary or performs an
effect that may bubble outward enters the CPS/evidence machinery. That runtime
shape is good for BEAM and should be preserved.

The weak point is maintainability. The compiler has accumulated several places
where lowering asks some version of:

- is this call direct or CPS?
- does this callable value need to be materialized as a CPS closure?
- should this effect op use evidence lookup or a direct backend path?
- does this dictionary method have a pure or effectful ABI?
- is this unknown shape unsupported or merely slow?

`src/codegen/call_effects.rs` is already a useful pre-pass for `App` nodes, but
the classification boundary is still narrower than the problem. Some decisions
are precomputed, while others remain local lowering decisions.

The next refactor should make those decisions explicit without replacing the
lowerer with a planner/optimizer/interpreter stack.

## Lessons From The Failed Branches

The uniform monadic CPS branch made every Saga callable use the same runtime
ABI:

```text
(user_args..., _Evidence, _ReturnK)
```

That solved arity-safety by construction, but it taxed all code. The optimizer
then had to rediscover direct code through dictionaries, modules, helper
functions, handlers, and generated derived code.

The selective-uniform branch tried to recover direct code with a planner,
monadic side path, fallback Core, adapters, known-dictionary facts, imported
fact reconstruction, and static handler variants. It was more structured than
the uniform rewrite, but still became a second execution model inside the
compiler.

The useful lesson is narrower:

```text
Keep main's direct-first runtime model.
Make call shape explicit.
Make wrong ABI choices impossible or loud.
Specialize only where emitted Core and benchmark data prove it helps.
```

## Non-Goals

- No whole-program monadic IR as the primary lowering input.
- No fallback Core merge.
- No broad planner that rewrites the program before lowering can begin.
- No optimizer required for baseline performance.
- No large interprocedural dictionary or Generic specialization in the first
  phase.
- No performance regression in pure or no-effect trait-heavy code as the price
  of shape discipline.

## Baseline Gates

Before changing lowering behavior, freeze a small baseline:

- `saga_json` options-as-arguments benchmark.
- `saga_json` effect-options benchmark.
- actor/native handler examples.
- ref/native handler examples.
- handler/resume/finally regression cases.
- trait/dictionary examples, especially derived and Generic-heavy code.

Early phases should be behavior-neutral. Generated Core and timings should be
close to `main`. If no-effect JSON regresses before an optimization is added,
the change should be backed out or narrowed.

## Phase 1: Name The Existing Decisions

Start by consolidating the shape decisions that already exist. Do not build a
new planner.

`src/codegen/call_effects.rs` is the seed. It already walks the elaborated
program and produces per-`App` effect metadata. The first step is to strengthen
that into an explicit ABI/classification contract.

Use [direct-first-effect-shape-matrix.md](./direct-first-effect-shape-matrix.md)
as the local checklist of case families. It adapts the useful discipline from
the selective-uniform branch's `selective-cps-value-matrix.md`, but restates the
rows in terms of `main`'s current classifier and lowerer. Do not copy the old
selective planner/fallback architecture back into this branch.

Possible shape:

```rust
pub struct RuntimeShapePlan {
    pub apps: HashMap<NodeId, AppPlan>,
    pub callable_values: HashMap<NodeId, CallableValuePlan>,
    pub effect_ops: HashMap<NodeId, EffectOpPlan>,
}

pub enum AppPlan {
    DirectCall,
    CpsCall {
        static_effects: Vec<OpKey>,
        row_forwarded: bool,
    },
    External,
    Intrinsic,
    DictMethod {
        method_shape: MethodShape,
    },
    Unsupported {
        reason: String,
    },
}

pub enum CallableValuePlan {
    DirectValue,
    NamedCpsMetadata,
    RuntimeCpsClosure,
    PureToCpsAdapterNeeded,
    Unsupported {
        reason: String,
    },
}

pub enum EffectOpPlan {
    EvidenceLookup,
    DirectNative {
        handler_canonical: String,
    },
    Unsupported {
        reason: String,
    },
}
```

These names are illustrative. The important invariant is that lowering reads a
plan instead of rediscovering ABI shape from source arity, spelling, or a local
type peek.

Acceptance:

- Done: no intended behavior change.
- Done: existing focused codegen/effect tests pass.
- Done: the current `CallEffectMap` role is clearer, not bypassed.
- Done: `CallEffectInfo` is opaque outside `call_effects.rs`; lowering consumes
  `cps_call_plan()` rather than matching classifier internals.
- Done: classified-CPS apps panic in lowering if no CPS dispatch path handles
  them.

## Phase 2: Add Audit And Assertions

Add a debug/audit mode that explains the shape decisions before emission.

Example output:

```text
App #123 Foo.bar: CpsCall static=[Std.Fail.Fail] row_forwarded=false
App #124 f: RuntimeCpsClosure row_forwarded=true
Effect #125 Std.IO.print: EvidenceLookup
Effect #126 Std.Actor.self: DirectNative handler=Std.Actor.beam_actor
```

This does not need polished UX at first. The point is to make ABI choices
visible and to make missing classifications loud.

Adapt the useful trace habit from the selective-uniform branch:

- keep a small, source-order trace at the classifier boundary;
- use shape labels like `direct`, `cps-static`, and `cps-row-forwarded`;
- allow filtering by module/target, following the old
  `SAGA_DEBUG_SELECTIVE=...` workflow;
- prefer adding one trace/assertion at an existing classification point over
  creating a separate planning interpreter.

Current hook:

```bash
SAGA_DEBUG_EFFECT_SHAPES=1 cargo run --bin saga -- build examples/scratch.saga
SAGA_DEBUG_EFFECT_SHAPES=My.Module cargo run --bin saga -- build examples/scratch.saga
SAGA_DEBUG_SELECTIVE=call-effects cargo run --bin saga -- build examples/scratch.saga
SAGA_DEBUG_SELECTIVE=effect-ops cargo run --bin saga -- build examples/scratch.saga
```

The compatibility with `SAGA_DEBUG_SELECTIVE` is intentional: this branch is
allowed to borrow the useful operator ergonomics from the previous refactor
attempt. The emitted classification still comes from `call_effects.rs`, and the
current lowerer remains the only Core Erlang emitter.

Acceptance:

- No behavior change by default.
- Done: the per-`App` classifier can emit a source-order trace before lowering.
- Done: debug output supports both `SAGA_DEBUG_EFFECT_SHAPES` and the old
  `SAGA_DEBUG_SELECTIVE` filter.
- Done: effect-op lowering emits audit rows for evidence lookup vs direct-native
  lowering, including static-index, open-row bridge, and runtime-bridge cases.
- Done: classified-CPS apps fail loudly if no lowering dispatch path handles
  them, so missing classifications do not quietly emit wrong-arity Core.
- Done: the trace is useful enough to debug why a call or op is direct, CPS, or
  evidence-routed.
- Done: single-file mode was checked with `examples/scratch.saga`; project mode
  was checked from `examples/bugs/dict-method-effectful-call`.

## Phase 3: Migrate Lowering Consumers Incrementally

Move one decision family at a time from local lowering logic into the
classification plan. Keep emission in the existing lowerer.

Suggested order:

1. Resolved function calls: direct, CPS, row-forwarded.
2. Runtime variable calls: direct closure, CPS closure.
3. Dictionary method calls: pure method, CPS method.
4. Lambda-headed calls.
5. Effect op calls: evidence lookup, direct native.
6. Handler install shape: install evidence, with room for later static direct
   plans.

Each slice should remove or shrink one local "figure out the ABI here" branch
and replace it with a plan lookup.

Progress:

- Done: qualified function calls now route through the same
  `lower_resolved_fun_call` consumer as bare resolved calls. The qualified path
  remains as a small wrapper for module-alias fallback, but no longer has its
  own copy of the direct/CPS/row-forwarded evidence and continuation branching.
- Done: runtime CPS variable calls, effectful dictionary method calls, and
  lambda-headed CPS calls now share `lower_runtime_cps_apply`, so the
  classifier-derived CPS plan is consumed once for evidence threading, row
  forwarding, return continuation binding, and nested effectful-argument
  chaining.
- Done: effect-op calls now consume an explicit local
  `EffectOpLoweringPlan` (`DirectNative` or `EvidenceLookup`) before emission.
- Done: handler installation already had an explicit `OpHandlerPlan`
  (`Inline`, `Static`, `Conditional`, `Dynamic`, `BeamNative`, `Passthrough`);
  phase 3 keeps that as the handler install shape rather than adding a second
  planner.
- Checked: current `json_bench`/`saga_json` EffectOpts benchmark on this
  branch: median encode 908 ms, decode 852 ms, roundtrip 1763 ms for 100000
  records. Reference against `saga` main for the same current branch: median
  encode 1105 ms, decode 916 ms, roundtrip 2021 ms.

Acceptance:

- Done: behavior-neutral lowering refactor; no intended Core semantics change.
- Done: current EffectOpts benchmark is within/better than the `saga` main
  compiler reference for the active saga_json branch.
- Done: if an `App` is classified as CPS, every lowering path that handles it
  consumes `CallEffectInfo::cps_call_plan()` or the shared runtime CPS apply
  helper fed by that plan.
- Done: unsupported classified-CPS app shapes fail with a lowerer diagnostic,
  not a BEAM `badarity`.
- Historical requirement: if/when the options-as-arguments benchmark branch is
  restored, run it as an additional regression gate. The current saga_json
  branch is EffectOpts-focused.

## Phase 4: Guardrails For Future Cases

Once classification is explicit, use it to reject unsupported runtime
representations early.

Important guardrails:

- CPS callable stored in arbitrary tuples/records/constructors without an
  explicit representation policy.
- Partial application of CPS functions where adapter shape is not implemented.
- Mixed direct/CPS branch results without an adapter plan.
- Effectful callbacks passed through an unknown ABI.
- Imported callable or dictionary metadata missing a runtime shape.
- Handler values whose runtime representation is not supported by the current
  lowering path.
- Trait dictionary methods must have per-method runtime shape. An impl-level
  `needs` clause cannot blindly force every method slot to CPS shape, because
  polymorphic dispatch only sees the trait method signature and pure sibling
  methods must remain direct-callable.

The desired failure mode is:

```text
compiler error or backend panic with a useful shape explanation
```

not:

```text
Core Erlang compiles, then crashes with badarity
```

Open design question: impl-level effects are convenient today, but optimization
would be simpler if effects were primarily a per-method contract. A later
language cleanup should consider making impl-level `needs` constrained sugar for
methods whose trait signatures already allow those effects, or rejecting
effectful method bodies when the trait method is externally direct.

### Guardrail Checklist

Work through this as targeted TDD. Each item should be a small executable
compiler-side test that either passes boringly or exposes a classifier/lowerer
ABI mismatch. Prefer one representative shape per row over broad enumeration.

- [x] Mixed-method trait impl: effectful method plus pure sibling method keeps
  the pure method direct-callable.
- [x] Concrete trait method dispatch where the impl-level `needs` clause is the
  only source of evidence still threads evidence correctly.
- [x] Polymorphic trait method dispatch through `where {a: Trait}` uses the
  trait method signature as the ABI contract.
- [x] Parameterized dictionary constructor with mixed method shapes preserves
  per-method direct/CPS slots after sub-dict application.
- [x] Imported mixed-method trait impl preserves method-slot shape in project
  mode.
- [x] Effectful top-level function partial application calls correctly under a
  handler.
- [x] Effectful partial application stored in a `let` binding keeps CPS shape
  when applied later.
- [x] Effectful callback passed to a higher-order function expecting
  `a -> b needs {...}` threads evidence.
- [x] Pure callback passed where CPS shape is expected gets an explicit adapter.
- [x] CPS callback passed where direct shape is expected either adapts
  explicitly or fails loudly.
- [x] List/tuple/record/constructor values containing effectful callbacks use a
  supported runtime representation.
- [x] Branches returning callable values agree on direct/CPS shape, or install
  an explicit adapter.
- [x] Intrinsic call with an effectful argument routes through intrinsic lowering
  after nested effect lowering.
- [x] Multiple intrinsic statements under one `with` boundary do not escape as
  wrong-arity Core calls.
- [x] Unsupported classified-CPS app shapes panic in lowering with the source
  node and shape label.

## Phase 5: Local Static Tail-Resume Optimization

Only after the classifier refactor is behavior-neutral, add the first effect
optimization.

Target:

```saga
value with {
  get () = resume captured
}
```

When a `perform` is statically handled by a known pure tail-resumptive arm,
lower it directly instead of doing evidence lookup plus CPS handler
application.

This should extend the effect-op plan, not introduce a global optimizer:

```rust
pub enum EffectOpPlan {
    EvidenceLookup,
    DirectNative { handler_canonical: String },
    DirectStaticTailResume { /* narrow proven facts */ },
    Unsupported { reason: String },
}
```

Initial scope should be narrow:

- inline or statically named handler only.
- handler arm is tail-resumptive.
- no multishot or non-tail `resume`.
- no dynamic handler value.
- no tricky `finally`, abort, or return-clause interaction.
- no cross-module cleverness unless existing metadata makes it direct.

If the direct plan is not proven, fall back to the current CPS/evidence path.

Acceptance:

- Missed optimization is only slower.
- Wrong optimization is not accepted.
- Effect-options JSON improves or the slice is reconsidered.
- Pure/no-effect JSON remains neutral.

## Phase 6: Trait And Dictionary Specialization

Trait specialization should be a separate track after runtime shape discipline
is in place.

First target immediate monomorphic method calls:

```text
known dict constructor
-> known method slot
-> direct method body lowering or direct method call
```

Do not start with broad Generic specialization. First prove that a small known
dictionary method rewrite improves or preserves emitted Core and benchmark
behavior.

Then expand in measured steps:

1. Local monomorphic dictionary constructors.
2. Imported public monomorphic dictionary constructors with sufficient metadata.
3. Parameterized/generic dictionary constructor chains where all sub-dicts are
   known.
4. Dict-only local elision when specialization erases the only use.
5. Known Generic/record/ADT output-shape specialization for serializers and
   decoders.

The long-term goal for `ToJson`/`Generic` is to use Generic as compile-time
structure evidence. A derived serializer should be able to emit direct code for
the final output shape instead of walking many intermediate runtime `Rep`
constructors for every value.

Acceptance:

- Dynamic dictionaries and polymorphic APIs remain correct through the normal
  dictionary-passing fallback.
- Specialization is chosen at call sites when concrete dictionary facts are
  known.
- No blanket monomorphization or generated-variant machinery before there is a
  naming/cache policy.
- Each specialization step is benchmarked against no-effect JSON.

## Hard Rules

- Keep PRs small. A large diff should be mostly tests or mechanical comments.
- Preserve `main`'s direct-first emitted shape until a specific optimization is
  intentionally added.
- Do not make optimization necessary for basic performance.
- Do not add a planner that becomes an alternate interpreter.
- Add classifier cases before lowering cases.
- Every new runtime shape gets either a regression test or an audit-trace
  fixture.
- If a refactor regresses no-effect JSON, shrink or revert it before adding
  another layer.

## Relationship To Older Planning Docs

This plan supersedes the older direction of making more code uniformly
monadic/CPS and optimizing back to direct style.

Related docs:

- `docs/planning/direct-first-effect-shape-matrix.md` - local checklist for
  call, callable-value, effect-op, handler, dictionary, and Generic shape
  families.
- `docs/planning/effectful-call-detection.md` - earlier cleanup plan for
  consolidating effectful call detection. This remains relevant as the first
  slice of the classifier work.
- `docs/planning/evidence-passing.md` - runtime evidence layout background.
- `docs/effect-implementation.md` - current effect semantics and evidence
  representation.
