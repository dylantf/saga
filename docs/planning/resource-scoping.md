# Resource Scoping via `finally` on Handler Arms

## Problem

When a handler acquires a resource (file handle, DB connection, socket) and calls
`resume`, the code after `resume` may never execute if another handler aborts the
computation. This means cleanup isn't guaranteed.

```
handler real_db for Database {
  connect url = {
    let conn = pg_connect! url
    resume conn
    pg_close conn      # SKIPPED if another handler aborts
  }
}
```

## Solution: `finally` clause on handler arms

A `finally` block on a handler arm runs after `resume` completes, regardless of
whether the computation succeeded, was aborted by another handler, or panicked.

```
handler real_db for Database {
  connect url = {
    let conn = pg_connect! url
    resume conn
  } finally {
    pg_close conn with { fail _ -> () }
  }
}
```

Code after `resume` (before `finally`) runs only on normal completion -- use it
for optional post-processing. Code in `finally` runs unconditionally -- use it
for cleanup that must happen.

### Multiple resources get reverse-order cleanup for free

Each effect operation that calls `resume` nests via CPS, so `finally` blocks
unwind in reverse acquisition order:

```
main () = {
  let db = connect! "postgres://..."
  let cache = connect_cache! "redis://..."
  do_work db cache
} with { real_db, real_cache }

# Cleanup order: cache first, then db (reverse of acquisition)
```

### Effects in `finally` must be self-contained

Effects inside a `finally` block cannot propagate out. All effects must be fully
handled within the block. This is enforced by the type system.

```
# OK: effect is handled locally
} finally {
  pg_close conn with { fail _ -> () }
}

# Type error: unhandled Fail effect escaping finally
} finally {
  pg_close! conn
}
```

This avoids the "what if the finalizer fails?" problem. The handler author decides
how to handle cleanup failures locally. The compiler enforces it.

## Guarantees

| Exit path                          | `finally` runs? |
| ---------------------------------- | ---------------- |
| Normal success                     | Yes              |
| Abort by inner handler             | Yes              |
| Abort by outer handler (past scope)| Yes              |
| Panic                              | Yes (via BEAM `try/after`) |
| Finalizer itself fails             | Self-contained; can't propagate |

## Why not `Scope` / `register_finalizer`?

Effect TS uses a separate `Scope` service with `register_finalizer` and
`acquireRelease` because it has no `finally` on handlers. With `finally`, the
handler that acquires the resource simply cleans it up directly. No extra
effect, no finalizer registry, no `scoped` wrapper.

## Compilation

Effects are lowered via straightforward CPS transformation (no exceptions or
`try/catch` on BEAM). `finally` is compiled by threading a cleanup function
alongside the continuation:

- Each `finally` block becomes a cleanup function prepended to a cleanup chain.
- On `resume`: call the continuation with the value, then run cleanup.
- On abort (handler doesn't call `resume`): run the accumulated cleanup chain,
  then return the abort value.

Nested `finally` blocks prepend to the chain, so cleanups naturally run in
reverse acquisition order. No BEAM exception machinery is involved -- it's just
an additional function parameter in the CPS output.

## Early release

Releasing a resource before scope exit is the one thing `finally` doesn't
optimize for. In practice this is rare and is a performance concern rather than
a correctness issue. If needed, an idempotent cleanup pattern could work at the
BEAM level, but this is not a priority.
