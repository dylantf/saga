# `spawn` and effect evidence

Status: **known limitation, documented behavior**. Not yet enforced.

## Current behavior

When `spawn` starts a new process, the spawned callback runs with a **copy of
the perform-site evidence vector** — the full set of handlers in scope at the
`spawn` site (see `spawn_thunk` in `src/codegen/lower_monadic/bootstrap.rs`).
BEAM copies the closure and its captured environment into the child's separate
heap, so the child gets a *snapshot fork* of the parent's handler stack.

This is correct for **process-portable effects**:

- native BIF effects (`Actor`, `Process`, `Timer`, …) — process-agnostic calls,
- `ets_ref` — state lives in a shared ETS table.

It is **silently wrong for non-portable effects**:

- user-defined effect handlers — the handler runs in the child against the
  *copied* continuation, so `resume` returns into the child's copy of the `with`
  delimiter, never the parent's. The parent observes none of the child's
  effectful work, and there is no error.
- `beam_ref` — the process dictionary is per-process, so writes from the child
  are invisible to the parent.

## Why it has to copy something

A delimited continuation is "the rest of the computation on *this* stack." A
spawned process has a different stack and heap, and BEAM shares no memory, so a
single logical continuation cannot span parent and child. The evidence (with its
handler closures) must therefore be copied into the child if the child is to
perform any effect at all. The *only* choices are what to copy; faithfully
running the parent's handler for a child's effect would require a message-passing
proxy per `perform`, which is impractical.

## Rule of thumb (until enforced)

A `spawn` body should only use:

- native / process effects, and `ets_ref` for shared state, and
- any user effects it **handles within its own body**.

Do not rely on a parent `with` handling a user effect performed inside a spawned
body — it will silently fork instead.

## Eventual fix

Classify effects by portability and have the typechecker require a `spawn`
callback's effect row to be a subset of the portable set (plus whatever the body
handles itself). That turns today's silent fork into a compile-time error. Not
scheduled.
