# Selective-Uniform Direct Shape Spike

This note records the next direction after the uniform-monadic performance
post-mortem. The important correction is ordering: do not specialize handlers
first. First remove unnecessary monadic/CPS shape from code that the type system
already proves is closed and non-effectful.

## Problem

The uniform branch can reduce `Yield` counts while still leaving hot paths slow.
The failed reader function-boundary prototype showed this clearly:

- the entry-reachable reader `Yield` disappeared;
- many `Bind`s became `Let`s;
- runtime still regressed when generated variants lowered pure helper calls
  through the uniform `(args..., Evidence, ReturnK)` ABI.

So `Yield 0` is not enough. The target is direct value-returning code for
closed, non-effectful calls. Effects should use CPS only where semantics require
it.

## Correct Optimization Order

1. **Classify runtime shape first.**
   - `Direct`: closed empty effect row, no open row, ordinary value-returning
     function shape.
   - `UniformCps`: effectful, open row, dynamic/unknown, or otherwise needs
     evidence and a continuation.
   - Start same-module and conservative. Unknown means `UniformCps`.

2. **Lower non-effectful calls without monadic CPS.**
   - Direct functions lower as `f(args...) -> value`.
   - Direct calls lower as ordinary value calls.
   - Direct sequencing lowers as `let`, not `Bind`.
   - No identity-continuation bridge for closed pure calls.

3. **Only then specialize simple reader handlers.**
   - Once the surrounding loop/helper path is direct-returning, replacing
     `get_config! ()` with a captured value can become as cheap as argument
     passing.
   - Before that, reader specialization can hide the `Yield` while preserving
     expensive continuation plumbing.

## Current Building Block

`src/codegen/runtime_shape.rs` already has the seed of the classifier:

- `RuntimeFunctionShape::Pure`
- `RuntimeFunctionShape::Cps`
- `RuntimeFunctionShape::Intrinsic`

It can classify from type metadata or resolution metadata. The next spike
should make this classification a first-class lowering input, not an
after-the-fact optimizer guess.

## First Implementation Slice

This should be a **new direct-first lowering path**, not private direct variants
inside the current uniform lowerer. It is acceptable, and expected, for effects
to be broken during the first slice. That is the point: prove the pure/direct
shape in isolation instead of preserving the old uniform protocol everywhere.

Keep the first slice deliberately narrow:

- same-module top-level functions only;
- closed empty effect rows only;
- no lambdas, trait dictionaries, partial application, external callbacks, or
  cross-module calls yet;
- calls or declarations that are not proven direct may panic with a clear
  "selective-uniform TODO" message in the spike path.

Expected code changes:

- add a separate spike lowerer or explicit lowering mode, for example
  `lower_selective` or `lower_direct_first`;
- build a runtime-shape map before that lowerer runs;
- emit `Direct` function bindings at arity `/N`;
- initially reject `UniformCps` function bindings instead of lowering them;
- make direct call lowering use ordinary value-returning calls;
- assert or panic when a direct function calls an unsupported CPS/dynamic shape.

Do not preserve production behavior by generating hidden direct variants beside
the current `/N+2` functions. That approach keeps the old model in charge and
makes it too easy to measure compatibility glue instead of the desired direct
backend.

## Current Spike Status

Implemented as an inspect-only path:

```text
saga inspect <file> --stage selective-core
```

The new `lower_selective` module currently:

- builds a conservative direct-function fixed point from runtime-shape metadata;
- emits only same-module, closed, non-effectful top-level functions and vals;
- emits direct `/N` Core Erlang functions with ordinary value returns;
- lowers direct sequencing as `let`;
- rejects functions that call skipped/unsupported functions, even if their type
  row is closed and empty;
- skips unsupported top-level declarations instead of trying to preserve
  production behavior.

Current proof fixture:

- `01-arg-passing.saga` emits `step/2` and `loop/3` as direct functions.
- `02-static-reader-effect.saga` and `03-handler-around-loop.saga` currently
  emit only the pure `iterations/0` val because the reader handler path is not
  reintroduced yet.

This is deliberate. The next step is not to restore all effects at once; it is
to add exactly one static-reader shape and observe the emitted Core before
expanding the subset.

## Incremental Reintroduction

After pure direct calls work:

1. Add one specific effect shape only:
   `with static_reader { get () = resume captured_value }`.
2. Lower that shape by substituting the captured value into direct code.
3. Leave all other handlers/effects unsupported in the spike path.
4. Add more effect shapes one at a time, guided by small fixtures and emitted
   Core inspection.

## Reader Fixture Acceptance

Use `examples/optimization/reader-config-effect/` as the first feedback loop.

Minimum useful progress:

- `01-arg-passing.saga`: direct pure loop remains fast;
- `03-handler-around-loop.saga`: without reader specialization, pure helper
  calls in the loop should no longer need identity continuations;
- after that, re-enable a reader-only specialization and check whether the
  effect-reader loop approaches the explicit-argument loop.

If direct-shape lowering cannot make the argument-passing path close to `main`,
stop before rebuilding more optimizer machinery.

## Non-Goals

- Reimplementing the existing `effect_opt` variant system.
- Dynamic handler specialization.
- Cross-module specialization.
- Trait/dictionary specialization.
- Handler factories.
- Perfect emitted Core Erlang in the first slice.
