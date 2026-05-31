# Uniform CPS Translation

Saga lowers algebraic effects through a uniform monadic/CPS pipeline. This is
the stable implementation note for that path; migration status and old-path
history live under `docs/planning/`.

The core invariant is simple: correctness does not depend on recognizing a
special call shape. The translator emits a uniform monadic IR, every ordinary
Saga function is callable with explicit evidence and a return continuation, and
the optimizer removes the scaffolding only when a local proof says it is safe.

## Pipeline

The relevant backend stages are:

```text
Elaborated AST
  -> ANF
  -> Monadic IR
  -> Effect optimizer
  -> Core Erlang lowering
```

Important files:

- `src/codegen/anf/` - ANF expression shape used before monadic translation.
- `src/codegen/monadic/ir.rs` - monadic IR definitions.
- `src/codegen/monadic/translate/` - AST/ANF to monadic IR.
- `src/codegen/monadic/effect_opt/` - optional optimizer.
- `src/codegen/lower/` - monadic IR to Core Erlang.
- `src/stdlib/evidence.bridge.erl` - runtime evidence helpers.

## Monadic IR

The monadic IR separates values from computations:

- `Atom` is a value-level form such as a variable, literal, tuple, constructor,
  record, lambda, dictionary reference, or qualified function reference.
- `MExpr` is a computation form such as `Pure`, `Yield`, `Bind`, `Let`, `With`,
  `Resume`, `App`, `Case`, `If`, `Ensure`, `Receive`, and `ForeignCall`.

The important control nodes are:

- `Pure(atom)` - produce a value.
- `Bind(value, var, body)` - run a computation and continue with its value.
- `Yield(op, args)` - perform an algebraic effect operation.
- `With(body, handler)` - install a handler around a computation.
- `Resume(value)` - call the resumption captured by the current handler arm.
- `Ensure(body, cleanup)` - run cleanup around handler/finally paths.

`BindMode` distinguishes ordinary sequencing from value-position binds. A
value-position bind is used when an expression needs the result of a subterm
without allowing handler control tuples to be accidentally consumed as normal
values.

## Calling Convention

Ordinary Saga functions and compiler-generated dictionary constructors lower to
uniform CPS functions:

```text
(user_args..., _Evidence, _ReturnK)
```

`_Evidence` is the runtime handler table in scope. `_ReturnK` is the
continuation used for successful completion and marked handler-control results.

There are boundary cases:

- top-level `val` declarations lower as arity-0 wrappers that build their own
  default evidence and identity return continuation;
- `@external` declarations get Saga-shaped wrappers, but saturated external
  calls with no Saga callback parameters may lower directly to the native call;
- native handler operations can be optimized to direct `ForeignCall`s, but the
  unoptimized path still uses the normal evidence/handler protocol.

When Saga functions cross a native Erlang boundary as callbacks, the wrapper
adapts a Saga CPS closure to native arity:

```erlang
fun(Arg1, ..., ArgN) ->
  apply SagaCallback(Arg1, ..., ArgN, EvidenceAtBoundary, IdentityK)
end
```

## Evidence

Evidence is a BEAM tuple of entries:

```erlang
{
  {'Effect.Atom.A', OpTupleA},
  {'Effect.Atom.B', OpTupleB}
}
```

Each entry is `{EffectAtom, OpTuple}`. The outer entries are kept in canonical
effect-atom order. Each `OpTuple` stores the operation closures for one effect
in canonical operation-name order.

Installing a handler calls `std_evidence_bridge:insert_canonical/2`. If the
effect already exists in evidence, the entry is replaced. This gives
innermost-wins shadowing without separate mask state.

Performing an operation lowers to:

1. find the effect entry in `_Evidence`;
2. select the operation closure by its canonical index;
3. apply the closure to `(op_args..., EvidenceAtPerform, K)`.

The runtime lookup remains tagged so cross-module calls and diagnostics do not
depend on a caller and callee agreeing on an untagged tuple position.

## Handlers

The IR has four handler shapes:

- `Static` - source handler arms known at the `with` site.
- `Dynamic` - a runtime handler value selected by a variable, branch, factory,
  or parameter.
- `Native` - a compiler-provided BEAM-native handler.
- `Composite` - multiple handlers installed as one surface value.

A source operation arm lowers to an op closure with shape:

```text
(op_args..., EvidenceAtPerform, K_arm)
```

`K_arm` is the captured continuation from the perform site. A resuming arm calls
it with the operation result. A non-resuming arm ignores it. Multishot arms call
it more than once.

Dynamic handler values use a self-describing runtime tuple:

```text
{__saga_handler_value, OpsByEffect, RuntimeReturn}
```

`OpsByEffect` is a canonical tuple of `{EffectAtom, OpTuple}` pairs.
`RuntimeReturn` is either `unit` or a Saga CPS function used as the handler
return clause.

## Return Clauses And Delimiters

Handler return clauses are delimited prompts. A successful result from a handled
body is routed through the nearest matching return clause, then outward through
outer return clauses.

Resumptions make this more subtle than a plain tail call. A continuation
captured inside a `with` body must re-enter the prompt stack that existed at the
perform site. The lowerer tracks this with `ResultDelimiter` in `LowerCtx` and
marks control results with the owning delimiter marker.

Two marked tuple protocols are used internally:

```text
{__saga_value_result, Marker, Value}
{__saga_handler_abort, Marker, Value}
```

The owning delimiter consumes its marker. Foreign markers are propagated. This
prevents an inner handler's abort or success result from being treated as a
plain value by an outer resuming arm, while still letting value-producing resume
patterns work.

## Resume

`resume v` lowers to an application of the current arm continuation:

```text
apply K_arm(v)
```

The value returned by that call is the resumed computation's result at the
handler boundary. This is why value-producing resume patterns such as:

```saga
get () = fun s -> (resume s) s
```

work: `resume s` produces the handled body's eventual value, which can itself
be applied or otherwise inspected by the arm body.

## Finally

Handler arms can carry cleanup through `finally` blocks. In the unoptimized
lowering, cleanup is injected into the continuation path rather than wrapped
around a `resume` call with Erlang `try/catch`. This matters because algebraic
aborts are Saga control values, not Erlang exceptions.

The optimizer has a conservative direct-call path for cleanup when every value
needed by the cleanup is available at the perform site. Other cases stay on the
slow path.

## Native And External Boundaries

BEAM-native effects are represented as native handlers installed in evidence.
The slow path still calls their operation closures through evidence. Optimizer
rewrites can replace common native operations with direct `ForeignCall`s when
the active handler stack proves the native handler is the one that will run.

`@external` functions are wrapped so Saga code can call them through the uniform
calling convention. If an external function accepts a function-typed parameter,
the wrapper adapts Saga CPS callbacks to the native callback arity with an
identity continuation.

Process spawn thunks capture the evidence at the spawn boundary. This lets a
spawned Saga callback use the handlers that were in scope where it was handed to
the native operation.

## Debugging

Useful commands:

```bash
cargo run --bin saga -- inspect file.saga --stage monadic
cargo run --bin saga -- inspect file.saga --stage monadic-opt
cargo run --bin saga -- inspect file.saga --stage monadic-stats
cargo run --bin saga -- emit file.saga
```

Read `docs/effect-optimization.md` for the rewrites that remove uniform CPS
overhead after translation.
