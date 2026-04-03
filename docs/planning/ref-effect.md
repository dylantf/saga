# Ref Effect — Mutable State via ETS

## Motivation

dylang has no mutable state by design — state is managed through recursion with
accumulator arguments. However, some patterns (counters, caches, accumulators
shared across callbacks) are painful to thread through pure CPS chains.

An earlier attempt at pure state threading through CPS lowering proved
impractical. ETS provides a clean escape hatch: the BEAM already has fast
concurrent mutable storage, and wrapping it in an effect keeps mutation explicit
and controlled.

## Design

```
pub effect Ref {
  fun new : a -> Ref a
  fun get : Ref a -> a
  fun set : Ref a -> a -> Unit
  fun modify : Ref a -> (a -> a) -> a
}
```

`Ref a` is an opaque handle. At runtime it's an ETS table key. The handler
manages table creation and cleanup.

## Usage

```
fun count_evens : List Int -> Int needs {Ref}
count_evens xs = {
  let counter = new! 0
  List.each xs (fun x ->
    if x % 2 == 0 then modify! counter (fun n -> n + 1)
    else ()
  )
  get! counter
}

main () = {
  let result = count_evens [1, 2, 3, 4, 5, 6]
  println (show result)
} with ets
```

## Properties

- **Explicit in signatures**: `needs {Ref}` — no hidden mutation. Callers know
  what they're getting into.
- **Swappable for testing**: a pure handler could back refs with a Map threaded
  through recursion. Slow, but correct for tests that want determinism.
- **Scoped by handler**: refs can't leak past the `with beam_ref` boundary.
  The handler can clean up ETS entries when the computation completes.
- **Composes with other effects**: `needs {Ref, Log, Fail}` works as expected.

## Handler

```
pub handler beam_ref for Ref {
  # Compiler builtin — ops lower to ETS calls:
  #   new    -> ets:new + ets:insert, returns key
  #   get    -> ets:lookup
  #   set    -> ets:insert
  #   modify -> ets:lookup + apply + ets:insert
}
```

The handler creates an ETS table on first `new!` and cleans it up when the
handler scope exits. Each `Ref` is a key in that table.

## Why ETS, not process dictionary or CPS state

- **Process dictionary**: mutable but untyped, no cleanup guarantees, invisible
  to the effect system. Same downsides as global mutable state.
- **CPS state threading**: attempted and abandoned. Threading state through every
  continuation in the CPS lowering added massive complexity to the compiler for
  marginal purity benefits. The state was effectively mutable anyway — just with
  extra steps.
- **ETS**: fast, concurrent, already part of the BEAM runtime. Wrapping it in an
  effect preserves the language's contract (mutation is tracked and explicit)
  without fighting the platform.

## Testing handler

A pure handler for testing, backed by an immutable Map threaded through the
handler's own recursion:

```
handler test_ref for Ref {
  # Implementation would use an internal Map, updating it on each
  # set/modify and resuming with the new state.
  # Details TBD — the important thing is the interface stays the same.
}
```

Tests swap `beam_ref` for `test_ref`, same as any other effect.
