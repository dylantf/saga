# Selective-Uniform Effects

Status: **experiment charter / next-branch plan**.

This document sketches the next effect-codegen experiment after the
`uniform-effect-translation` branch. The goal is to keep the useful lessons
from the uniform monadic CPS rewrite without keeping its most expensive runtime
choice: making every Saga function use a CPS/evidence ABI.

Working name: **selective-uniform**.

## Thesis

The old selective-CPS backend failed because call-shape knowledge was
distributed and incomplete. The uniform rewrite fixed that by giving every
Saga function the same runtime shape:

```text
(user_args..., _Evidence, _ReturnK)
```

That was correct but too expensive on BEAM.

The next experiment should make the **metadata uniform**, not the **runtime ABI**.

In other words:

- every callable should have one authoritative runtime-shape classification;
- every call site should use that classification;
- pure/direct code should stay direct BEAM code;
- common statically-known tail-resumptive handlers should specialize before the
  general handler protocol is introduced;
- only effectful or effect-polymorphic boundaries should use the CPS/evidence
  convention;
- adapters should be explicit at boundaries where the shapes differ.

## Updated Diagnosis

The benchmark data does not say that every part of the uniform branch is
catastrophic.

It suggests two separate costs:

| Comparison | Result |
| --- | ---: |
| `main` options argument -> uniform options argument | roughly `1.45x` slower |
| `main` fast string path -> uniform fast string path | roughly `1.55x` slower |
| `main` effect options -> uniform effect options | roughly `13-15x` slower |
| uniform options argument -> uniform effect options | roughly `10x` slower |

So the uniform ABI creates a real baseline tax, but the branch-killing failure
is narrower: simple effect-scoped configuration reads go through the full
general handler/evidence/resume protocol.

On `main`, passing JSON encode options through an effect is only modestly
slower than passing the options as an ordinary argument. There is no optimizer
there; the old selective-CPS code is simply a much smaller CPS island.

On the uniform branch, the optimizer can reduce syntactic `Yield` counts, but
the emitted code can still retain the expensive surrounding machinery:

- CPS-shaped function and dictionary calls;
- continuation closures;
- marked value-result and abort routing tuples;
- result delimiter reconstruction;
- evidence lookup and handler tuple dispatch;
- generated variants and cloned helpers.

This means residual `Yield` count is not enough. A successful next design must
make hot simple handlers compile to simple code before Core lowering, not hope
that a large late optimizer rediscovers that fact.

## Handler Classification Before General CPS

Add a handler classification step before monadic/CPS lowering commits to the
general protocol.

Sketch:

```rust
enum HandlerArmShape {
    ReaderValue,
    TailResumptive,
    GeneralResume,
    AbortOnly,
    Finally,
    Multishot,
    DynamicUnknown,
}
```

The key hot-path case is:

```saga
get_json_options () = resume options
```

When a matching perform is statically under that handler, it should rewrite to
the captured value:

```saga
get_json_options! ()  ==>  options
```

or to the smallest equivalent direct continuation step. It should not allocate
or call the full handler/evidence/resume machinery.

This specialization is not valid for every handler. For example:

```saga
get () = fun s -> (resume s) s
```

is value-producing/state-threading resume and still needs the proper delimited
continuation semantics. Multishot, non-tail resume, `finally`, dynamic handler
values, aborting handlers, and unknown handler factories should stay on the
general path until a specific safe rewrite exists.

## Proposed Pipeline

The next backend experiment should make classification an explicit step between
resolution/elaboration and monadic lowering:

```text
Parse
→ Typecheck / Elaborate
→ Resolution + Runtime Shape Classification
→ Effect/Handler Specialization
→ Lower:
    direct path for direct code
    monadic/CPS path for general effect code
→ small cleanup optimizer
→ Core Erlang
```

The architecture to avoid is:

```text
Parse
→ Typecheck / Elaborate
→ uniform monadic CPS for everything
→ large optimizer tries to rediscover direct code
→ Core Erlang
```

The optimizer should start small. If the backend only becomes usable after a
large interprocedural partial evaluator reconstructs source-level intent, the
IR/runtime representation is doing too much damage too early.

## Reuse From The Uniform Branch

Keep or port these pieces where practical:

- `RuntimeFunctionShape` / `runtime_shape.rs`, expanded into the authoritative
  call-shape layer.
- Imported effect-op metadata (`EffectInfo::effect_ops`).
- Dynamic handler metadata for handler values and handler refs.
- `@external` wrapper/callback adapter design.
- Value-producing resume tests and semantics.
- Abort/result marker routing lessons.
- Finally/cleanup regression tests.
- Anonymous-record structural metadata fixes.
- Monadic/stat inspection tooling.
- Real-package shakedown fixtures and habits.

Do not port the full uniform ABI by default.

## Core Model

Introduce one backend-facing call-shape API, built from existing
typechecker/elaboration/resolution metadata.

Sketch:

```rust
enum RuntimeCallShape {
    Direct {
        arity: usize,
    },
    Cps {
        user_arity: usize,
        effects: Vec<String>,
        open_row: bool,
    },
    External {
        arity: usize,
        callback_adapters: Vec<CallbackShape>,
    },
    Intrinsic {
        arity: usize,
    },
}
```

This does not need to be the final spelling. The important invariant is that
lowering does not rediscover call shape ad hoc from names, arity guesses, or
one-off type lookups.

Sources of truth should include:

- `ResolvedCodegenKind::{BeamFunction, ExternalFunction, Intrinsic}`;
- `ModuleCodegenInfo::fun_effects`;
- `EffectInfo::type_at_node`;
- `EffectInfo::let_effect_bindings`;
- trait/dictionary metadata;
- handler/effect metadata for dynamic handler values;
- external function signatures for callback adapter generation.

## Lowering Strategy

Default to direct style.

- Closed empty-effect functions lower as ordinary BEAM functions of arity `N`.
- Intrinsics lower through their intrinsic path.
- Externals lower through wrappers only when needed, especially when adapting
  Saga callbacks to native Erlang callback arity.
- Effectful or open-row functions lower as CPS/evidence functions of arity
  `N + 2`.
- Handler bodies and resumptions may use monadic/CPS machinery internally, but
  that does not force every unrelated function into CPS shape.

Calls are shape-directed:

- `Direct -> Direct`: ordinary call.
- `Cps -> Cps`: pass evidence and return continuation.
- `Cps caller -> Direct callee`: ordinary call, then continue with the result.
- `Direct caller -> Cps callee`: require an enclosing handler/evidence context
  or insert an explicit adapter/thunk.
- `External` with function-typed parameters: wrap Saga callback values into
  native-arity Erlang callbacks.

Any unknown or contradictory shape should be a compiler error or backend panic
with a useful diagnostic. It should not silently guess and produce runtime
arity mismatches.

## Role Of Monadic IR

The monadic IR is still useful, but it should not necessarily be the whole
program's runtime contract.

Possible roles:

- represent effectful regions/functions;
- represent handler bodies and resumptions;
- provide a correctness-oriented slow path for functions that genuinely need
  evidence and continuation plumbing;
- give optimizers a structured place to simplify effectful code.

The experiment should explicitly test whether pure/direct functions can bypass
monadic lowering entirely or lower through a direct subset.

The next concrete spike is documented in
`docs/planning/selective-uniform-direct-shape.md`. Its main correction is
ordering: classify direct vs CPS function shape first, lower closed
non-effectful calls directly second, and only then revisit reader/config handler
specialization.

## Initial Spike Scope

This is a timeboxed experiment, not a second full rewrite.

Target duration: **1-2 focused days**.

Fixtures:

1. Pure function calls pure function.
2. Pure caller invokes an effectful function under a handler.
3. Effectful caller invokes a pure helper.
4. Higher-order callback through a stdlib/external function.
5. One trait/dictionary method call, if the first four are stable.
6. Statically-known reader/config handler:
   `get () = resume captured_value`.

Do not port the uniform optimizer for the first spike. The point is to measure
whether direct-first lowering produces reasonable baseline code before
interprocedural heroics.

Current measurement note: while this experiment is still living on the
`uniform-effect-translation` branch, the production codegen path may still run
the older `effect_opt` pass after any new selective-uniform pass. Use
`saga inspect --stage monadic-reader-stats` to measure the first reader
specializer in isolation. `--stage monadic-stats` measures the combined
pipeline and can credit existing function-variant machinery for wins that the
new spike has not earned yet.

## Success Criteria

Continue only if the spike shows clear promise:

- pure/options-argument style code is close to `main` performance;
- effect-options code is not an order of magnitude slower before optimization;
- the old arity-mismatch class is caught by call-shape assertions;
- the implementation delta stays in the low thousands of lines, not tens of
  thousands;
- fixtures and at least one real-package shakedown pass.

Stop or redesign if basic cases require:

- large interprocedural partial evaluation;
- cross-module dictionary cloning just to recover normal direct calls;
- dynamic handler specialization to make ordinary code acceptable;
- widespread name-based or arity-guessing fallbacks.

## Questions To Answer Early

1. Can direct and CPS function values coexist without making partial
   application fragile?
2. Where should shape metadata live for let-bound function values and lambdas?
3. Do trait dictionaries store direct method closures, CPS method closures, or
   shape-tagged method entries?
4. How do open effect rows appear after elaboration, and can they be made
   explicit enough for lowering?
5. What is the minimal adapter set needed for higher-order functions?
6. Can imported module metadata provide enough shape information without
   recompiling or specializing the callee module?

## Relationship To Main And Uniform Branch

`main` remains the stable working compiler.

The `uniform-effect-translation` branch is a research branch and source of
salvageable fixes/tests/docs.

The selective-uniform experiment should branch from the uniform branch if the
goal is to reuse the learned machinery quickly. If the goal is a clean final PR,
the successful pieces can later be replayed onto `main` in smaller commits.

## Non-Goals For The Spike

- Full optimizer parity with the uniform branch.
- Whole-program trait specialization.
- Dynamic handler performance work.
- Cross-module generated variants.
- Perfect Core Erlang output.
- Removing every old selective-CPS mechanism on day one.

The first question is simpler: can the backend have uniform call-shape
knowledge while preserving direct BEAM code for the common case?
