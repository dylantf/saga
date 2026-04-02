# Handle Bindings

Bind handlers to names for conditional selection and composition.

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

## The `handle` Keyword

`handle` binds a handler to a name. The right-hand side is any expression that
evaluates to a handler:

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

- **`handler`** -- define a handler (existing)
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

# Inject
run_app () with logger
```

### Inline Handler Expressions

The RHS of `handle` can also be an inline handler:

```
handle logger = handler for Log {
  log level msg = {
    println ($"[{level}] {msg}")
    resume ()
  }
}
```

This is useful when the handler is one-off and doesn't warrant a module-level
`handler` definition.

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

## Future: Named Effect Instances

A separate, larger feature that builds on handle bindings. Named instances
solve the problem of multiple handlers for the same effect type (e.g. two
independent `State Int` cells).

### The Problem

```
handle counter = handler for State Int { ... }
handle buffer = handler for State Int { ... }

get! ()   # ambiguous -- which State Int?
```

### Qualified Operations

Named instances scope effect operations via dot syntax:

```
handle counter = handler for State Int { ... }
handle buffer = handler for State Int { ... }

counter.put! 5
buffer.put! (buffer.get! () + 10)
```

### Propagation Through Functions

When a function needs multiple instances of the same effect, the names appear
in the `needs` clause and are received via `{}` in the definition:

```
# Signature: declares named effect instances
fun transfer : Int -> Unit needs {from: State Int, to: State Int}

# Definition: receives them in {}
transfer amount {from, to} = {
  let balance = from.get! ()
  from.put! (balance - amount)
  to.put! (to.get! () + amount)
}
```

At the call site, named instances are passed using `:` syntax in the `with`
block (distinct from `=` for inline arms):

```
transfer 100 with { from: checking, to: savings }
```

The three item types in a `with` block are syntactically unambiguous:

| Syntax              | Meaning                  | Example                       |
| ------------------- | ------------------------ | ----------------------------- |
| bare name           | named handler reference  | `console_log,`                |
| `name: expr`        | named instance binding   | `from: checking,`             |
| `name args = body`  | inline arm               | `log level msg = println msg` |

### Functions with Unnamed Effects

Named instances are opt-in. Functions that need only one instance of each
effect type work exactly as they do today -- no names, no `{}` block:

```
fun increment : Unit -> Unit needs {State Int}
increment () = put! (get! () + 1)
```

When calling such a function from a scope with multiple instances, the caller
disambiguates with `with`:

```
increment () with counter
```

### Design Notes

- Named instances are primarily a **local scoping mechanism**. They don't need
  to propagate through long call chains in most cases.
- If distinct effect identities need to flow through many functions, defining
  separate effect types (`effect Counter`, `effect Buffer`) is often clearer
  and works with the existing system (propagation, absorption, HOFs) with zero
  friction.
- Named instance propagation through `needs` is heavier -- intermediate
  functions must carry the names, and absorption becomes name-aware. This is
  acceptable as opt-in cost for cases that genuinely need it.
- This is **not** full "effects as values" (as in Koka's evidence passing).
  Handlers bound with `handle` cannot be stored in data structures or returned
  from functions. They are scoped bindings, not first-class values.
