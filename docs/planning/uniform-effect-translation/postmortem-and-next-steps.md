# Uniform Monadic CPS Rewrite: Postmortem And Next Steps

Status: **decision document / postmortem draft**.

This document evaluates the uniform monadic CPS rewrite as an architecture
choice, using the implementation and benchmark results from the
`uniform-effect-translation` branch. It is intentionally separate from the
implementation docs: the goal here is not to describe how the branch works, but
to decide whether it should become the compiler's default backend and what a
future effect-codegen refactor should try instead.

## Executive Summary

The uniform rewrite succeeded as a correctness experiment: it made many effect
semantics explicit, flushed out real bugs, and produced useful tests and
documentation. It did not succeed as a replacement backend for Saga on BEAM.

The core issue is the default cost model. The rewrite made every ordinary Saga
function, dictionary constructor, trait method closure, and helper use a
uniform CPS ABI:

```text
(user_args..., _Evidence, _ReturnK)
```

The optimizer then has to prove that this scaffolding can be removed. In real
Saga code, especially trait/dictionary-heavy derived code, that proof crosses
module, dictionary, method, helper, and handler-factory boundaries. The
optimizer therefore grew into a large interprocedural partial evaluator, and
the emitted BEAM code still retains significant continuation/control-tuple
overhead.

Recommendation: **do not merge the uniform monadic CPS branch as the default
backend.** Archive it as a research spike, salvage the correctness fixes and
tests, and use what it taught us to design a smaller direct-style-first
effect-codegen refactor.

## Benchmark Evidence

JSON encode/decode benchmark, 100k records unless noted:

| API shape | Median |
| --- | ---: |
| Main + Effect ops | 1058 ms |
| Main + Options arg | 924 ms |
| Main + ToJsonString fast path | 477 ms |
| Uniform + Effect ops | ~14500 ms |
| Uniform + Options arg | 1349 ms |
| Uniform + ToJsonString fast path | 745 ms |
| Elixir + Jason | 126 ms |

The important comparison is not Jason; it is Saga main vs uniform:

- options-argument code is roughly 30-50% slower under uniform lowering even
  when it has no residual algebraic effect operations;
- effect-options code goes from about 1 second to about 14.5 seconds;
- attempts to erase the residual `JsonOptions` yields by specializing through
  dictionaries were able to reduce syntactic yield counts, but at least one
  attempt generated more code and made the benchmark slower.

This means residual `Yield` count is not a sufficient performance metric.
Uniform continuation ABI overhead remains even when `Yield` is zero.

## What The Plan Promised

The original motivation was sound:

- the old selective-CPS lowerer depended on recognizing every effectful call
  shape;
- missing a shape caused runtime arity mismatches;
- each new language feature reopened the recognizer;
- a uniform translation would make the slow path correct by construction;
- optimization would be correctness-preserving and optional.

The intended division was:

1. translate uniformly into monadic IR;
2. lower all functions through explicit evidence and continuations;
3. erase monadic scaffolding where a conservative optimizer proves it safe.

## What The Implementation Actually Did

The current code follows the plan faithfully, but that is part of the problem.

### Bind Is Expensive When It Survives

In `src/codegen/lower/exprs.rs`, `lower_bind` allocates a continuation closure,
emits marked-control cases, lowers the bound expression under that
continuation, and wraps the result with abort bubbling. A surviving `Bind` is
not a cheap annotation.

Therefore a stat like:

```text
Bind 417 -> 83
```

still means 83 reachable continuation/case structures in emitted Core Erlang.

### Translation Emits Binds By Default

`src/codegen/monadic/translate/expr.rs` lowers ordinary blocks by wrapping
source lets and non-tail expression statements in `Bind`. The optimizer then
has to recover `Let` or direct style later.

This reverses the old default. Main used to keep pure calls direct and CPS only
where needed. Uniform lowering starts in CPS and asks optimization to prove its
way back to direct style.

### Ordinary Calls Keep The Uniform ABI

`src/codegen/lower/app.rs` lowers ordinary calls as:

```text
apply F(args..., _Evidence, _ReturnK)
```

This applies to pure functions, dictionary constructors, trait methods, helper
functions, and generated derived-code functions unless a later rewrite catches
the exact shape.

### The Optimizer Became A Partial Evaluator

The optimizer started with local rewrites:

- `Bind(Pure)` collapse;
- `Bind -> Let` promotion;
- static tail-resumptive direct-call;
- native direct-call.

To handle real code, it grew into:

- same-module function variants;
- cross-module function variants;
- static handler variants;
- let-bound handler factory recovery;
- imported handler factory recovery;
- dictionary constructor specialization;
- parameterized dictionary specialization;
- imported dictionary constructor specialization;
- private helper cloning;
- value-keyed variants;
- known-constructor case collapse;
- dictionary-argument pruning.

That is not just cleanup. It is interprocedural specialization across Saga's
trait/dictionary system. The complexity moved from "selective CPS call-shape
recognition" into a much larger optimizer.

## Why `saga_json` Is The Telling Case

`saga_json` is not pathological Saga code. It is exactly the kind of code Saga
is likely to encourage:

- derived trait dictionaries;
- generic representation walking;
- cross-module library calls;
- small helper functions;
- handler factories for policy/configuration;
- effectful trait methods that read ambient options.

The effect-options benchmark has a small syntactic residual yield count:

```text
whole-app entry-reachable:
  Yield 4 -> 4
  Bind 417 -> 83
  residual yields: SagaJson.JsonOptions::get_json_options=4
```

But those four yield sites sit inside generic record/field/variant encoding
paths and execute repeatedly for many records and fields. They are not cold.

The uniform optimizer tried to chase these through dictionary dispatch and
cross-module helper chains. That is exactly the hard case for this architecture:
the runtime cost is introduced uniformly, but removing it requires global
knowledge about dictionaries, handler stacks, and values.

## Root Cause

The root cause is not one missing rewrite. It is the ABI choice:

```text
uniform CPS everywhere
```

That makes correctness easier, but it taxes all code. Saga's trait/dictionary
architecture then amplifies the tax because every derived trait method and
dictionary helper also becomes CPS-shaped.

On BEAM, this is a poor default. BEAM is good at ordinary function calls,
pattern matching, recursion, and tuples. It is not free to allocate and apply
many tiny continuation closures and route success/failure through tagged
control tuples.

## What Was Still Valuable

Do not throw away the lessons. The branch contains useful work even if the
architecture is rejected.

Salvage candidates:

- value-producing resume tests and semantics;
- abort/result marker routing insight;
- finally/cleanup tests and continuation-path handling;
- dynamic handler value return-clause handling;
- `@external` higher-order callback adapters;
- effect metadata improvements such as `effect_ops`;
- anonymous-record structural metadata fixes;
- optimizer/statistics tooling;
- real-package shakedown habits;
- docs that explain evidence, handlers, and tricky resume behavior.

These should be ported selectively, not wholesale.

## Options From Here

### Option A: Keep Optimizing Uniform CPS

Pros:

- preserves the current branch's correctness model;
- avoids reintroducing selective-CPS arity bugs immediately;
- could continue improving targeted cases.

Cons:

- already large: roughly `+44k / -14k` LOC;
- still 30-50% slower on no-yield paths;
- effect-options hot path is order-of-magnitude slower;
- optimizer is now a complex partial evaluator;
- future performance work is open-ended;
- zero residual yields does not guarantee good Core Erlang.

Verdict: **not recommended** as the default compiler path.

### Option B: Redo Uniform Translation With A Direct ABI For Pure Code

Pros:

- keeps some monadic IR clarity;
- might avoid the worst tax by not CPS-lowering closed-effect functions;
- could use uniform machinery only inside effectful regions.

Cons:

- this is no longer truly "uniform CPS everywhere";
- it converges toward selective CPS;
- requires a new ABI split and interop rules;
- still must solve callbacks, partial application, dictionaries, and
  cross-module effect summaries.

Verdict: plausible, but should be framed as a hybrid/direct-first design, not
as a restart of the same uniform plan.

### Option C: Selective CPS 2.0

Keep the old backend's winning default: direct style unless the type/effect
metadata proves a call must participate in effect control.

The redesign target is not "go back to brittle shape recognition." It is:

- use typed/resolved metadata as the source of truth;
- classify call sites as direct, static-effect CPS, row-forwarding CPS, or
  native/direct;
- centralize this classification in one audited pass;
- make lowering consume classification rather than rediscovering shapes;
- add coverage for all shapes the uniform branch flushed out.

Pros:

- preserves main's proven runtime shape;
- targets the real bug class: incomplete classification;
- avoids taxing pure/dictionary-heavy code;
- aligns better with BEAM;
- lets CPS remain a local mechanism for genuinely effectful regions.

Cons:

- selective CPS remains conceptually more intricate than uniform lowering;
- needs strong invariants and diagnostics to avoid old arity bugs;
- will need careful tests for higher-order, row-polymorphic, trait-method, and
  dynamic handler shapes.

Verdict: **recommended direction**.

## Proposed Next Refactor Shape

Call it **direct-first effect lowering** or **selective CPS 2.0**.

Design principles:

1. **Direct style is the default.**
   Pure functions and closed-effect-free dictionary constructors lower to
   ordinary BEAM functions, without `_Evidence` or `_ReturnK`.

2. **CPS is selected by effect metadata, not syntactic guessing.**
   The classifier should consume resolved names, typechecked effect rows,
   trait method effect signatures, impl effect metadata, and let/lambda
   binding metadata.

3. **Effectful function values carry an explicit runtime shape.**
   Closures/callbacks should know whether they are direct or CPS-shaped.
   Native callback adapters should be generated from that shape.

4. **Dictionaries should not globally become CPS tuples.**
   A trait method should be CPS-shaped only if its method effect row requires
   CPS at the call site. Pure dictionary construction should remain direct.

5. **Evidence passing can still be uniform where CPS is active.**
   Inside an effectful region, evidence layout and handler routing can reuse
   the lessons from this branch.

6. **The compiler must fail early on unknown shapes.**
   If classification cannot decide a runtime shape for a call, emit a compiler
   diagnostic or panic in debug/compiler mode. Do not silently pick an ABI.

7. **Benchmarks are acceptance tests.**
   A new refactor is not accepted unless it is close to main on:
   - pure/direct code;
   - options-argument JSON;
   - effect-options JSON;
   - actor examples;
   - multishot/state handler examples.

## Acceptance Gates For Any Next Attempt

Before replacing main, the next backend must satisfy:

- behavioral parity with the existing test suite;
- no runtime arity mismatches in the known bug repros;
- JSON options-argument benchmark within a small margin of main;
- JSON effect-options benchmark no worse than main by more than an agreed
  small factor;
- no blanket 30% tax on closed-effect code;
- no large optimizer required for basic viability;
- emitted Core for a small pure function and a small pure trait method should
  look like ordinary direct Erlang-style code;
- emitted Core for an effectful operation should show explicit, local CPS
  routing.

Suggested red line: if the new path needs interprocedural specialization to
make a trivial pure or trait-heavy program acceptable, the architecture is
wrong.

## Immediate Next Steps

1. Freeze the uniform branch as an experiment; stop adding optimizer rewrites
   unless needed to understand the postmortem.
2. Create a salvage checklist of correctness fixes/tests worth porting.
3. Restore or branch from main as the baseline for the next attempt.
4. Write a short design for selective CPS 2.0 / direct-first effect lowering.
5. Start with one narrow classifier improvement from the old bug class, not a
   full backend rewrite.
6. Run JSON benchmarks from day one, before deleting any old path.

## Open Questions

- Can trait method calls be classified entirely from existing type/effect
  metadata, or do we need extra method-runtime-shape metadata after
  elaboration?
- Should function values carry a runtime tag for direct vs CPS shape, or can
  all call sites know the shape statically after ANF/elaboration?
- How should row-polymorphic callbacks be represented without forcing all
  callbacks into CPS?
- Which uniform-branch handler semantics tests can be ported directly to main?
- Is there a small monadic IR useful only for effectful regions, or should the
  lowerer remain direct-style with explicit CPS helpers?

