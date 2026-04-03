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
| `Process.exit` (VM termination)    | No — VM halts immediately, nothing can run |
| Finalizer itself fails             | Self-contained; can't propagate |

`panic` is dylang's own construct, compiled to a BEAM exception (`erlang:error`).
Since we control the mechanism, `try/after` reliably catches it. `Process.exit`
maps to `erlang:halt()` which terminates the VM — no cleanup is possible or
expected, same as `kill -9`.

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

## AST Representation

`finally` is part of the handler arm node, not a general-purpose block wrapper.
It only makes sense in handler context (where `resume` exists), so the AST
reflects that:

```rust
HandlerArm {
    params: Vec<Pattern>,
    body: Expr,
    finally: Option<Expr>,
}
```

This keeps `finally` out of the general expression grammar and makes it a parse
error anywhere outside a handler arm.

## Interaction with `return` Clause

When a handler has both a `return` clause and arms with `finally`, cleanup runs
**before** the `return` clause transforms the value. The `return` clause wraps
the final result of the computation; `finally` is about cleaning up resources
acquired during an individual effect operation. Sequencing:

1. Computation completes (or aborts)
2. `finally` blocks run (reverse acquisition order)
3. `return` clause transforms the success value (if computation completed)

## Multishot Continuations

If a handler calls `resume` multiple times (multishot), each `resume` is an
independent continuation call. The `finally` block runs after **each** resume
completes. This falls naturally out of CPS: the cleanup is part of the
wrapped continuation, so each invocation of that continuation includes its
own cleanup pass.

## Scope of Bindings in `finally`

Variables bound in the handler arm body (before `resume`) are visible in the
`finally` block. Implementation-wise, `finally` is a closure that captures the
arm's scope, which happens naturally since it's compiled as a lambda in the
same lexical environment.

## Compilation Details

### Cleanup Chain as CPS Argument

The cleanup chain is threaded as an additional argument through the CPS
transform. Each `finally` block prepends a zero-arity cleanup function to the
chain (a list), giving an ordered list that can be iterated on abort:

```
# Conceptual CPS output for a handler arm with finally:
fun (Args..., K, Cleanups) ->
  let Conn = pg_connect(Url) in
  let MyCleanup = fun () -> pg_close(Conn) in
  let Cleanups2 = [MyCleanup | Cleanups] in
  apply K(Conn, Cleanups2)
```

On abort (handler doesn't call `resume`), the accumulated cleanup list is
walked in order — which is reverse acquisition order, since each `finally`
prepends:

```
# Abort path:
lists:foreach(fun (F) -> apply F() end, Cleanups)
```

On normal completion, the same walk happens after the continuation returns.

### Panic Safety

Effect-level aborts (handler doesn't call `resume`) are handled purely by the
cleanup chain — no BEAM exception machinery needed for those.

However, `panic` compiles to `erlang:error`, which is a BEAM exception that
would bypass the CPS cleanup chain. Since `panic` can appear anywhere in a
continuation (it's valid in any expression position), any non-empty cleanup
chain needs protection.

**Strategy:** When the cleanup chain is non-empty, wrap the continuation call
in `try/after`:

```erlang
% No cleanup chain: no wrapping needed
apply K(Conn)

% Non-empty cleanup chain: wrap with try/after
try
  apply K(Conn, Cleanups2)
of V -> V
after
  run_cleanups(Cleanups2)
end
```

This is only emitted when the cleanup chain is non-empty, so functions without
`finally` blocks pay zero cost. `Process.exit` (`erlang:halt`) terminates the
VM immediately and bypasses `try/after` — this is expected and documented.

## Early release

Releasing a resource before scope exit is the one thing `finally` doesn't
optimize for. In practice this is rare and is a performance concern rather than
a correctness issue. If needed, an idempotent cleanup pattern could work at the
BEAM level, but this is not a priority.

## Implementation Order

1. **AST + Parser** — add `finally` to handler arm syntax
2. **Typechecker** — enforce empty effect row on `finally` blocks
3. **Lowering** — thread cleanup chain through CPS, wrap continuations
4. **Panic safety** — emit `try/after` around continuations with non-empty cleanup chains
