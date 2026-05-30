# Native Direct-Call Specialization

## Summary

Add a conservative Stage 11 optimization for BEAM-native handlers: when a
`Yield` is lexically under a statically known `MHandler::Native` and the
native op can be represented as a plain `MExpr::ForeignCall`, rewrite the
`Yield` to that `ForeignCall`.

This is the native analogue of tail-resumptive direct-call, but it should be
implemented as a separate rewrite. The first milestone only handles simple
first-order native ops whose bootstrap closure currently does:

```text
fun(args..., _EvidenceAtPerform, K) -> apply K(erlang_or_runtime_call(args...))
```

Everything else stays on the slow evidence path.

Status: **milestone 3 implemented**. The optimizer rewrites simple first-order
native yields to `ForeignCall` for `Identity`, `NoArgs`, and `Reorder`
transforms, and now supports `PrependAtom` through an internal backend-atom IR
value. Milestone 2 also rewrites `beam_ref` `new`, `get`, and `set` to direct
process-dictionary calls. It skips `WrapThunk`, `beam_ref.modify`, `ets_ref`,
Vec, dynamic handlers, and composite handlers.

## Why This Is Separate From Static Handler Direct-Call

Tail-resumptive direct-call inlines Saga handler arms and relies on
`HandlerAnalysis::resumption`. Native handlers have no Saga arm body or
`resume`; their semantics are encoded by bootstrap metadata and bespoke Core
builders.

So the safety question is different:

- Static handler direct-call asks: "is this Saga arm tail-resumptive?"
- Native direct-call asks: "is this native op a synchronous first-order call
  whose bootstrap result is exactly the op result?"

Keep those predicates separate so later cleanup/finally/multishot work cannot
accidentally change native-call behavior.

## First Milestone Scope

Optimize only:

- `MHandler::Native { effects, handler, .. }`
- handler is lexically innermost for the yielded effect
- op is known in a shared native metadata table
- op lowering is one of:
  - `Identity`
  - `NoArgs`
  - `Reorder`
- target has a real Erlang/runtime module + function
- every inserted argument can be represented as an `Atom`

Skip:

- `WrapThunk` (`spawn`) because it needs a Core Erlang closure capturing
  evidence.
- Ref/Vec store backends because they currently require bespoke `CExpr`
  builders, not `MExpr::ForeignCall`.
- Dynamic handlers.
- Composite handlers in milestone 1. Treat them as blockers until there is a
  deliberate decomposition rule.
- Empty-module native metadata entries.
- Any op whose result needs post-processing.

## Metadata Refactor

The optimizer currently lives in `src/codegen/monadic/effect_opt/`, while
native metadata lives under `src/codegen/lower_monadic/bootstrap/`. Do not make
the optimizer import the lowerer.

The pure metadata now lives in a shared backend-neutral module:

```text
src/codegen/native_effects.rs
```

The shared module should expose read-only descriptors only:

```rust
pub struct NativeEffectSpec {
    pub tag: &'static str,
    pub ops: &'static [NativeOpSpec],
}

pub struct NativeOpSpec {
    pub name: &'static str,
    pub erl_module: &'static str,
    pub erl_func: &'static str,
    pub param_count: usize,
    pub transform: NativeArgTransform,
}

pub enum NativeArgTransform {
    Identity,
    NoArgs,
    PrependAtom(&'static str),
    Reorder(&'static [usize]),
    WrapThunk(usize),
}
```

`lower_monadic/bootstrap/native_effects.rs` re-exports the shared table for
lowerer-local names. Bootstrap-specific Core builders stay in
`lower_monadic/bootstrap.rs` and `lower_monadic/bootstrap/stores.rs`. The
optimizer consumes only the shared descriptor table.

## Optimizer Shape

The rewrite runs before existing static direct-call:

```text
optimize children
try_native_direct_call
try_static_tail_resumptive_direct_call
bind-collapse
Bind-to-Let
```

Extend the handler stack:

```rust
enum HandlerFrame {
    Static { effects, arms },
    Native { effects, handler },
    Blocking { effects },
}
```

Rules:

- `Dynamic` remains `Blocking`.
- `Composite` remains `Blocking` in milestone 1.
- `Static` keeps current behavior.
- `Native` can rewrite only if it is the innermost matching frame for
  `op.effect`.

Rewrite:

```text
Yield { op, args, source }
  under Native(handler)
  where native descriptor maps (handler, op) to module/function/arg transform
=> ForeignCall { module, func, transformed_args, source }
```

The transformed args must be built from `Atom`s:

- `Identity`: original args.
- `NoArgs`: `[]`.
- `Reorder(indices)`: reorder original args; skip if any index is out of range.

If anything does not line up, return unchanged.

## Handler Name Resolution

`MHandler::Native` carries the source handler name, e.g. `beam_actor`,
`beam_ref`, `ets_ref`, `beam_vec`.

First milestone mapping:

- `beam_actor`: may optimize first-order Actor/Timer/Process/Link/Monitor ops
  from the shared native table, except `spawn`.
- `beam_ref`: skip all Ref ops initially, because even process-dict Ref has
  bespoke behavior and callback handling for `modify`.
- `ets_ref`: skip all Ref ops initially.
- `beam_vec`: skip all Vec ops initially.

That makes the first implementation useful for common actor/timer operations
without touching the complex store backends.

## Second Milestone Scope

Milestone 2 adds process-dictionary `beam_ref` operations whose bootstrap
closures do not apply Saga callbacks:

- `new initial` becomes `erlang:make_ref()`, `erlang:put(ref, initial)`, then
  returns the generated ref.
- `get ref` becomes `erlang:get(ref)`.
- `set ref value` becomes `erlang:put(ref, value)` followed by Saga `Unit`.

Still skipped:

- `beam_ref.modify`, because it applies a Saga callback under the current
  evidence and needs callback-boundary handling.
- `ets_ref`, because `new`, `get`, and `set` need ETS-specific tuple/case
  scaffolding and are better handled as a separate backend-lowering milestone.
- `beam_vec`, for the same reason as `ets_ref`.

## Third Milestone Scope

Milestone 3 adds a backend-only `Atom::BackendAtom` for optimizer-generated
Erlang atoms. This is deliberately separate from source-level `Symbol`, which
still lowers to a binary and remains primarily a type/generic-system construct.

With that internal atom form, `PrependAtom("process")` native ops such as
`monitor` can lower to:

```text
ForeignCall(erlang:monitor, [BackendAtom(process), pid])
```

This closes the local op-shape gap. It does not optimize `monitor!` calls that
sit behind function boundaries; those still need interprocedural/native
specialization.

## Tests

Implemented optimizer unit tests:

- Native `Timer.sleep` under `beam_actor` or the relevant native timer handler
  rewrites `Yield` to `ForeignCall("timer", "sleep", [ms])`.
- Native `Actor.self`/no-args transform rewrites to a zero-arg foreign call.
- Native `Monitor.monitor` / `PrependAtom("process")` rewrites using
  `BackendAtom(process)`.
- Native `Timer.send_after` reorders args.
- `Process.spawn` does not rewrite.
- `beam_ref`, `ets_ref`, and `beam_vec` do not rewrite in milestone 1.
- `beam_ref` `new`, `get`, and `set` rewrite in milestone 2.
- `beam_ref.modify`, `ets_ref`, and `beam_vec` remain slow-path.
- Dynamic same-effect inner handler blocks native rewrite.
- Static same-effect inner handler blocks outer native rewrite.
- Composite same-effect handler blocks native rewrite in milestone 1.
- Unknown op or arg-count mismatch leaves the `Yield` unchanged.

Spot check:

- `examples/33-timer.saga --stage monadic-opt` rewrites `sleep` to
  `ForeignCall(timer:sleep, [Lit(1000)])`.

## Validation

Run:

```bash
cargo test -q -p saga --lib codegen::monadic::effect_opt
cargo test -q -p saga --lib codegen::lower_monadic
cargo test -q --test effect_property_tests
cargo test -q --test stdlib_tests stdlib_test_suite
cargo test -q --test e2e
cargo test -q -p saga --lib
cargo fmt --check
cargo clippy -q
cargo run --bin saga --quiet -- run examples/29-actors.saga
cargo run --bin saga --quiet -- run examples/32-monitor.saga
cargo run --bin saga --quiet -- run examples/33-timer.saga
```

## Non-Goals For Milestone 1

- No Ref/Vec direct native lowering.
- No `spawn` thunk specialization.
- No composite handler decomposition.
- No cleanup/finally interaction.
- No lowerer-level Core Erlang rewrite. Keep this as an MExpr optimization so
  the slow lowerer remains a shared backend target.
