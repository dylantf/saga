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

### No Changes to CPS Transform

The lowerer doesn't change. `handle` bindings are desugared before lowering --
a `handle` is just a let-binding for a handler lambda. `with` already passes
handler lambdas; it just receives them from `handle` bindings instead of only
from named `handler` declarations.

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

### Interaction with Re-entrant Effects

Re-entrant effects (see `effects-guide.md`) allow a handler to delegate to an
outer handler for the same effect. Today this works but the delegation is
implicit -- the re-performed operation routes outward through `needs` with no
syntactic indication:

```
handler double_counter for Counter needs {Counter} {
  increment () = {
    let n = increment! ()   # goes outward, but not obvious
    resume (n * 2)
  }
}
```

Named instances make delegation explicit:

```
handler double_counter for Counter needs {inner: Counter} {
  increment () {inner} = {
    let n = inner.increment! ()   # clearly delegates to inner
    resume (n * 2)
  }
}
```

This is especially valuable for middleware chains where multiple layers of the
same effect are nested. Without named instances, each layer's `increment!()`
silently routes one level out. With them, the delegation target is visible in
the code.

`handle` bindings also make middleware composition more ergonomic:

```
handle base = simple_counter
handle wrapped = double_counter   # needs Counter, satisfied by nesting

{ increment! () with wrapped } with base
```

### Name Matching and Propagation

Named effects propagate through the call stack, like unnamed effects do today.
Names are part of the effect identity -- `{from: State Int}` and
`{to: State Int}` are distinct in the effect row even though the underlying
effect type is the same.

Names must match exactly at call boundaries. When calling a function that
declares named effects, the caller must provide handlers with matching names:

```
fun transfer : Int -> Unit needs {from: State Int, to: State Int}

# Direct -- names in scope match
do_banking () {from, to} = transfer 50

# Remapping -- caller has different names
fun do_banking : Unit -> Unit needs {src: State Int, dst: State Int}
do_banking () {src, dst} = {
  transfer 50 with { from: src, to: dst }
}
```

The `with` block remaps names explicitly. This is the same `:` syntax used to
pass named instances, here serving as a rename. The type checker verifies that
`src` has type `Handler (State Int)` and that `from` is what `transfer`
expects.

### Absorption with Named Instances

Absorption (subtracting handled effects from a HOF callback's effect row)
works by matching both name and type. This is a natural extension of existing
absorption:

```
fun run_transfer : (Unit -> a needs {from: State Int, to: State Int, ..e})
                -> a needs {..e}
run_transfer f = f () with {
  from: make_state 0,
  to: make_state 100,
}
```

The parameter expects `{from: State Int, to: State Int, ..e}`. The callback
performs `{from: State Int, to: State Int}`. Absorption matches `from` to
`from` and `to` to `to` (name + type), subtracts both. Only `..e` extras
propagate.

If names don't align, the caller remaps at the call site:

```
# transfer needs {from, to} but run_stuff expects {src, dst}
run_stuff (fun () -> transfer 50 with { from: src, to: dst })
```

No name unification in the type checker -- names are concrete identifiers, not
variables. Mismatch is a type error, not something the compiler solves.

### Design Notes

- **Named instances are opt-in.** Unnamed effects work exactly as today. Most
  effects (Log, Fail, Http) will never need names. Named instances are for
  effects where identity matters (State, Ref, Channel).
- **Names propagate through `needs`.** This adds annotation cost at
  intermediate functions but makes the data flow explicit. In practice, named
  effects tend to be used 1-2 levels deep.
- **`Handler Effect` as a type** gives handlers value semantics (returnable,
  bindable, storable). This covers most practical use cases without full
  Koka-style evidence passing. The remaining gap is implicit evidence
  threading -- our system requires explicit `with` attachment, which is
  arguably more readable.

### Future Convenience

- **Effect row aliases**: A way to name a bundle of effects for reuse in
  signatures. Reduces repetition when the same set of named effects appears
  across many functions. Deferred until real code shows the need.
