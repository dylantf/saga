# Handler Bindings

Bind handlers to names for conditional selection, composition, and construction.

## Motivation

Swapping handlers is a key feature of the effect system -- different handlers
for dev vs prod, test vs real, etc. Without handler bindings, this requires
duplicating the computation at every branch:

```
if env == "dev" then
  run_app () with { console_log, sqlite_db, mock_http }
else
  run_app () with { sentry_log, postgres_db, real_http }
```

This scales poorly. Three handlers means two branches; five handlers with
independent choices means combinatorial duplication.

## The `Handler Effect` Type

Handlers have a type: `Handler Effect`. At runtime a handler binding is a
tuple of per-operation lambdas, but the type system tracks which effect it
handles.

```
# Handler declarations have type Handler Effect
handler console_log for Log { ... }       # : Handler Log
handler to_result for Fail { ... }        # : Handler Fail

# Multi-effect handlers
handler dev_env for Log, Db { ... }       # : Handler (Log, Db)

# Handlers that need effects
handler sentry_log for Log needs {Http} { ... }
```

## Terminology

Four forms of handler usage, from most static to most dynamic:

- **Handler declaration** -- `handler foo for Effect { ... }` at the top level.
  Statically known; arms are inlined at `with` sites. Zero runtime cost.

- **Handler binding** -- `let foo = console_log` or `let foo = if dev then x else y`.
  Binds an existing handler (or a conditionally-selected handler, or a factory
  result) to a local variable. Used with `with foo`.

- **Handler expression** -- `handler for Effect { ... }` as a value. Can appear
  anywhere an expression is expected: RHS of `let`, return value of a function,
  argument to a function.

- **Inline handler** -- `with { op args = body, ... }`. Arms written directly
  in a `with` block. No `Handler` value involved; arms are inlined at the site.

## Handler Bindings via `let`

Handler bindings use regular `let` syntax. The RHS is any expression that
evaluates to a `Handler`:

```
let logger = if dev then console_log else sentry_log
let db = if dev then sqlite_db else postgres_db
let http = real_http

run_app () with { logger, db, http }
```

Each handler is independently selected, then composed in a single `with` block.
No duplication of `run_app ()`. The order of items in the `with` block matters:

```dy
run_app () with { logger, db, http }
```

is sugar for:

```dy
((run_app () with logger) with db) with http
```

Handler bindings are block-scoped, like any `let`:

```
main () = {
  let logger = console_log
  let db = sqlite_db

  # logger and db are in scope for the rest of the block
  run_app () with { logger, db }
}
```

The outer `with` can also use handler bindings introduced inside the wrapped
block. This is useful for handler factory functions:

```
main () = {
  let db = connect config

  {
    run_app ()
  }
} with { db, console_log }
```

Think of the wrapped block as staying in scope for the trailing `with`. The
handler suffix does not open a fresh lexical scope; it wraps the expression you
just built.

## Handler Expressions and Factory Functions

`handler for Effect { ... }` is an expression that produces a `Handler Effect`
value. This enables handler factory functions:

```
fun make_logger : String -> Handler Log
make_logger prefix = handler for Log {
  log msg = {
    println (prefix <> ": " <> msg)
    resume ()
  }
}

main () = {
  let logger = make_logger "[app]"
  run () with logger
}
```

## Composition in `with` Blocks

A `with` block can mix handler bindings, named handler references, and inline
arms:

```
run_app () with {
  real_http,                          # handler declaration reference
  logger,                             # handler binding
  db,                                 # handler binding
  fail reason = Err(reason),          # inline arm
}
```

### Override Semantics

`with {a, b, c}` uses lexical order and nested semantics. The first item is the
nearest handler, so it gets the first chance to handle an operation. If it does
not handle that operation, it falls through to the next item, and so on.

This means:

- the first matching handler handles the operation
- unhandled operations propagate outward
- `return` clauses compose by nesting

To override part of a broader environment, put the more specific handler first:

```
run_app () with {
  log level msg = {                   # handles just Log
    println ($"[{level}] {msg}")
    resume ()
  },
  prod_env,                           # handles Log, Db, Http
}
```

Here the inline `log` arm handles `Log` first, while `Db` and `Http` still
fall through to `prod_env`.

---

## Implementation Notes

### Runtime Representation

Handler declarations (`handler foo for Log { ... }`) have no runtime
representation -- the compiler inlines their arms at `with` sites.

Handler bindings (`let foo = ...`) compile to a tuple of per-operation lambdas.
At `with foo`, the tuple is destructured to extract the handler functions.

### Compilation Paths

There are three compilation paths depending on how the handler is bound:

1. **Static alias** (`let foo = console_log`): the compiler resolves `foo` to
   the original handler declaration and inlines the arms. Zero runtime cost.

2. **Conditional** (`let foo = if dev then x else y`): each operation gets a
   wrapper lambda that dispatches via `case` at runtime. One branch per effect
   call -- negligible on the BEAM.

3. **Dynamic** (`let foo = make_logger config` or `let foo = handler for Log { ... }`):
   the handler is a tuple of lambdas. At `with` sites, the tuple is
   destructured to extract per-operation functions. One indirection per effect
   call.

The compiler chooses the path automatically based on the RHS expression form.
There is no user-facing distinction.

### Type Checking

- `handler` declarations and `handler` expressions produce values of type
  `Handler Effect`
- `let` bindings infer the `Handler` type from the RHS; when a `let` binding
  has type `Handler(...)`, the typechecker registers it for handler resolution
- Conditional expressions require both branches to produce `Handler` for the
  same effect
- `with` validates that the provided handlers cover the computation's `needs`
- Factory functions declare `Handler Effect` as their return type

---

## Future: Named Effect Instances

Not implemented. This section documents a potential future extension.

Named instances would solve the problem of multiple handlers for the same
effect type (e.g. two independent `State Int` cells):

```
# The problem: ambiguous
let counter = handler for State Int { ... }
let buffer = handler for State Int { ... }
get! ()   # which State Int?
```

Named instances would scope effect operations via dot syntax and propagate
between the signature and a new function parameter:

```
fun transfer : Int -> Unit needs {from: State Int, to: State Int}
transfer amount {from,to} = {
  let balance = from.get! ()
  from.put! (balance - amount)
  to.put! (to.get! () + amount)
}

transfer 100 with { from: checking, to: savings }
```

This was explored but deferred. For now, the recommended workaround for
multiple handlers of the same effect type is to define separate effect types
(e.g. `effect Counter`, `effect Buffer`) which works with the existing system.
