# Handle Bindings

Bind handlers to names for conditional selection, composition, and construction.

## Motivation

Swapping handlers is a key feature of the effect system -- different handlers
for dev vs prod, test vs real, etc. Today this requires duplicating the
computation at every branch:

```
if env == "dev" then
  run_app () with { console_log, sqlite_db, mock_http }
else
  run_app () with { sentry_log, postgres_db, real_http }
```

This scales poorly. Three handlers means two branches; five handlers with
independent choices means combinatorial duplication.

Beyond selection, there's no way to write a handler factory -- a function that
takes configuration and returns a handler -- because handlers aren't values
with types.

## The `Handler Effect` Type

Handlers have a type: `Handler Effect`. At runtime this is just a function
(the CPS handler lambda), but the type system tracks which effect it handles.

```
# Named handler declarations have type Handler Effect
handler console_log for Log { ... }       # : Handler Log
handler to_result for Fail { ... }        # : Handler Fail

# Multi-effect handlers
handler dev_env for Log, Db { ... }       # : Handler (Log, Db)

# Handlers that need effects
handler sentry_log for Log needs {Http} { ... }
```

This enables handler factory functions:

```
fun make_logger : String -> Handler Log
make_logger path = handler for Log {
  log level msg = {
    write_file! path ($"[{level}] {msg}")
    resume ()
  }
}

fun make_db : ConnectionConfig -> Handler Database
make_db config = handler for Database needs {Net} {
  query sql = {
    let conn = connect! config
    pg_execute! conn sql |> resume
  }
}
```

## The `handle` Keyword

`handle` binds a handler to a name. The right-hand side is any expression that
evaluates to a `Handler`:

```
handle logger = if dev then console_log else sentry_log
handle db = if dev then sqlite_db else postgres_db
handle http = real_http

run_app () with { logger, db, http }
```

Each handler is independently selected, then composed in a single `with` block.
No duplication of `run_app ()`.

### Keyword Family

Three related keywords, three distinct roles:

- **`handler`** -- define a handler (existing, now has type `Handler Effect`)
- **`handle`** -- bind a handler to a name
- **`with`** -- inject handlers into a computation

```
# Define (module-level, reusable)
handler console_log for Log {
  log level msg = {
    println ($"[{level}] {msg}")
    resume ()
  }
}

# Bind (local, conditional)
handle logger = if dev then console_log else sentry_log

# Bind (from factory function)
handle db = make_db production_config

# Inject
run_app () with { logger, db }
```

## Scoping

`handle` bindings are block-scoped, like `let`:

```
main () = {
  handle logger = console_log
  handle db = sqlite_db

  # logger and db are in scope for the rest of the block
  run_app () with { logger, db }
}
```

## Composition in `with` Blocks

A `with` block can mix all three kinds of items. By convention, they are
ordered: named handler references first, handle bindings second, inline arms
last:

```
run_app () with {
  real_http,                          # named handler reference
  logger,                             # handle binding
  db,                                 # handle binding
  fail reason = Err(reason),          # inline arm
}
```

### Override Semantics

When multiple items handle the same effect, the last one wins. This enables
layering -- start with a bundle, override specific operations:

```
run_app () with {
  prod_env,                           # handles Log, Db, Http
  log level msg = {                   # overrides just Log from prod_env
    println ($"[{level}] {msg}")
    resume ()
  },
}
```

---

## Implementation Notes

### Runtime Representation

`Handler Effect` has no special runtime representation. Handlers already
compile to CPS handler lambdas (`fun(Op, Args..., K) -> ...`). The type is
just the compiler tracking "this lambda is shaped like a handler for `Log`."

### Type Checking

- `handler` declarations and inline `handler` expressions produce values of
  type `Handler Effect`
- `handle` bindings infer the `Handler` type from the RHS
- Conditional expressions require both branches to produce `Handler` for the
  same effect
- `with` validates that the provided handlers cover the computation's `needs`
- Factory functions declare `Handler Effect` as their return type

### CPS Transform

Static handle bindings (`handle logger = console_log`) are pure compile-time
aliases -- zero runtime cost. The handler arms are inlined at the `with` site
exactly as if the original handler name were used.

Conditional handle bindings (`handle logger = if dev then x else y`) generate
a wrapper lambda per effect operation that dispatches via `case` at runtime:

```erlang
fun (Arg, K) ->
  case CondVar of
    'true' -> <then_handler_arm>(Arg, K)
    _ -> <else_handler_arm>(Arg, K)
  end
```

This adds one `case` per effect call -- negligible on the BEAM. The overhead
is inherent to runtime dispatch: if handler selection is a runtime decision,
there must be a runtime check. When the condition is a compile-time constant
(e.g. a `val` binding), a future inlining pass could eliminate the dead branch
entirely.

Factory functions (Phase 1b) will have similar characteristics -- one extra
indirection per op call when the handler is dynamically constructed, optimizable
away when the handler is statically known.

