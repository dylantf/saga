# dylang Effects Guide

Effects are dylang's core abstraction for anything that interacts with the
outside world - I/O, state, errors, concurrency. Instead of baking these into
the language as special constructs, they're user-defined and handler-provided.

---

## Defining an Effect

An effect declares a set of operations - what can be done, not how.

```
effect Log {
  fun log : String -> String -> Unit
}

effect Fail {
  fun fail : String -> Never
}

effect Http {
  fun get : String -> String
  fun post : String -> String -> String
}
```

An effect is like an interface: it names operations and their signatures, but
provides no implementation. The implementation comes from handlers.

---

## Performing Effects

Effect operations are called with `!` to distinguish them from pure functions:

```
fun run_server : Unit -> Unit needs {Log, Http, Fail}
run_server () = {
  log! "info" "server starting"
  let data = get! "/api/health"
  if data == "" then
    fail! "empty response"
  else
    log! "info" ("got: " <> data)
}
```

The `!` marks the exact point where control may transfer to a handler. Pure
function calls don't get it:

```
process () = {
  let x = compute_thing ()   # pure - no bang
  log! "info" (show x)       # effect - bang
  x
}
```

Only primitive effect operations (those declared in an `effect` block) get `!`.
Calling a function that _internally_ uses effects is a normal call - its
signature (`needs {Log}`) tells you it has effects, but the call site is just
`run_server ()`.

Effect calls can appear anywhere an expression is expected, not just as
standalone statements in a block. For example:

```
let x = 1 + ask! ()
let result = transform (get! "key")
if check! () then a else b
```

When multiple effect calls appear in the same expression, they are evaluated
left-to-right:

```
# ask! is called twice: first for the left operand, then for the right
let sum = ask! () + ask! ()
```

---

## Handling Effects

A handler provides implementations for effect operations. There are two forms:
**named** and **inline**.

### Named Handlers

Define a reusable handler with the `handler` keyword:

```
handler console_log for Log needs {Console} {
  log level msg = {
    print! ("[" <> level <> "] " <> msg)
    resume ()
  }
}

handler sentry_log for Log needs {Sentry} {
  log level msg = {
    sentry_send! level msg
    resume ()
  }
}
```

Attach them by name with `with`:

```
main () = {
  run_server ()
} with console_log
```

### Inline Handlers

For one-offs, define the handler inline:

```
main () = {
  run_server ()
} with {
  log level msg = {
    print! ("[" <> level <> "] " <> msg)
    resume ()
  }
}
```

Same semantics, just anonymous. Use named handlers when you'll reuse or swap
them. Use inline when it's obvious and local.

---

## resume - Continuing the Computation

`resume` is a keyword available inside any handler. It sends a value back to
the call site of the effect operation and continues the computation.

```
effect Ask {
  fun ask : String -> String
}

handler interactive for Ask needs {Console} {
  ask prompt = {
    print! prompt
    let answer = read_line! ()
    resume answer     # send `answer` back as the return value of `ask!`
  }
}

greet () = {
  let name = ask! "What's your name? "
  # after `resume`, execution continues here
  print! ("Hello, " <> name)
}
```

### What happens when a handler doesn't resume

The computation is **aborted**. The handler's return value becomes the result
of the entire `with` block:

```
handler to_result for Fail {
  fail reason = Err(reason)
  return value = Ok(value)
}

main () = {
  let result = {
    let a = safe_divide! 10 2    # succeeds, a = 5
    let b = safe_divide! a 0     # fails! handler returns Err(...)
    a + b                        # never reached
  } with to_result

  # result is Err("division by zero")
}
```

**Rules:**

- `resume` is always available in handlers
- If a handler calls `resume`, the computation continues from where the effect was performed
- If a handler doesn't call `resume`, the computation is aborted and the handler's value is the result of the `with` block
- The `resume` value must match the return type of the effect operation

### The `return` clause

A handler can include a `return` clause that intercepts the final value of a
successful computation (one that completes without triggering the effect):

```
handler to_result for Fail {
  fail reason = Err(reason)
  return value = Ok(value)
}
```

Without `return`, the value passes through unchanged. Most handlers don't need
it - `to_result` is the classic case that does, because it needs to wrap the
success case in `Ok`.

---

## Effect Namespacing

Effects act as namespaces for their operations. When there's no ambiguity, use
bare names:

```
fun process : Unit -> Unit needs {Log}
process () = {
  log! "info" "working"    # unambiguous - only Log has `log`
}
```

When multiple effects define the same operation name, qualify with the effect
name:

```
effect Database {
  fun get : String -> String
}

effect Cache {
  fun get : String -> String
}

fun fetch : String -> String needs {Database, Cache}
fetch key = {
  let cached = Cache.get! key
  let fresh = Database.get! key
  ...
}
```

Handlers mirror this:

```
} with {
  Cache.get key = {
    let result = lookup_cache! key
    resume result
  },
  Database.get key = {
    let result = query_db! key
    resume result
  },
}
```

---

## Stacking and Composing Handlers

Real programs use multiple effects. Use a `with` block to attach multiple
handlers - named references and inline arms can mix freely:

```
main () = {
  run_server ()
} with {
  console_log,
  real_db,
  real_http,
}
```

Mix named handlers with inline arms in the same block:

```
main () = {
  run_server ()
} with {
  sentry_log,
  real_db,
  get url = http_get! url |> resume,
}
```

For a single handler, skip the block:

```
run_server () with console_log
```

Or bundle multiple effects into a single named handler:

```
handler dev_env for Log, Database, Http needs {Console, Sqlite, Net} {
  log level msg = {
    print! ("[" <> level <> "] " <> msg)
    resume ()
  }
  query sql = sqlite_query! sql |> resume
  get url = http_get! url |> resume
}

handler prod_env for Log, Database, Http needs {Sentry, Postgres, Net} {
  log level msg = {
    sentry_send! level msg
    resume ()
  }
  query sql = postgres_query! sql |> resume
  get url = http_get! url |> resume
}

main () = {
  let env = get_env! "APP_ENV"
  if env == "production" then
    run_server () with prod_env
  else
    run_server () with dev_env
}
```

---

## Effect Requirements on Handlers

Handlers that use effects in their implementation declare them with `needs`,
just like functions. This makes the handler's dependencies visible:

```
handler stripe_billing for Billing needs {Log, Http} {
  charge account amount = {
    log! ("Charging ${show amount}")
    let result = http_post! "/stripe/charge" (to_json { account, amount })
    resume (parse_receipt result)
  }
}
```

If the handler is pure (no effects in its body), no `needs` clause:

```
handler mock_billing for Billing {
  charge account amount = resume (fake_receipt ())
}
```

When you attach a handler that has `needs`, those effects must also be handled
somewhere in the handler stack:

```
main () = {
  run_app ()
} with {
  stripe_billing,    # needs Log and Http
  console_log,       # handles Log (including from stripe_billing)
  real_http,         # handles Http (including from stripe_billing)
}
```

---

## Handlers Close Over Their Scope

Handlers are closures - they can reference variables from the surrounding scope:

```
main () = {
  let db_conn = connect! "postgres://localhost/mydb"
  let debug = true

  run_app ()
} with {
  query sql = {
    if debug then log! "debug" sql else ()
    pg_execute! db_conn sql |> resume
  },
}
```

Named handlers close over the scope where they're defined (typically module
scope).

---

## Effect Signatures on Functions

Functions declare which effects they require with `needs` in the type signature:

```
fun run_server : Unit -> Unit needs {Log, Http}
run_server () = {
  log! "info" "starting"
  let data = get! "/api/health"
  log! "info" "ready"
}
```

This tells callers what handlers they need to provide.

### Effect propagation

Effects propagate virally through function signatures. If a function calls
another function that needs an effect, it must either handle it (with `with`)
or declare it in its own `needs`:

```
fun get_user : Int -> User needs {Database}
get_user id = {
  query! "SELECT * FROM users WHERE id = ?"
  |> head
  |> from_row
}

# get_user_route calls get_user (needs Database)
# and calls send_response! (needs Http)
# it doesn't handle either, so both propagate
fun get_user_route : Request -> Unit needs {Database, Http}
get_user_route request = {
  request.params.id
  |> get_user_with_posts
  |> to_json
  |> send_response! 200
}
```

When a function handles an effect at the call site, that effect is peeled off
and doesn't propagate:

```
# start_app calls run_server (which needs Log, Http)
# and also uses Database directly
# it handles Log itself, so only Http and Database bubble up
fun start_app : Unit -> Unit needs {Http, Database}
start_app () = {
  init_db! ()
  run_server () with console_log   # handles Log here
}
```

The program's entry point must handle everything - nothing escapes unhandled.

### Lambdas and effects

Lambdas infer their effects automatically. If a lambda uses effects, they
become part of its type and must be accounted for by the caller:

```
# Error: foo uses Fail but has no needs declaration
foo x = fun y -> fail! "oops"

# OK: outer function declares it
fun foo : Int -> Int needs {Fail}
foo x = (fun y -> fail! "oops") x

# OK: handled at the expression level
foo x = (fun y -> fail! "oops") x with { fail msg = 0 }
```

### Effects through higher-order functions

When a function takes a callback, the type annotation on the parameter
controls which effects are allowed. There are three cases:

**No `needs` clause (pure):** The callback must be pure. This is enforced --
passing an effectful lambda is a type error:

```
fun map : (f: a -> b) -> List a -> List b

# Error: log! is not allowed in a pure callback
map (fun x -> { log! (show x); x }) xs
```

**Closed `needs` (specific effects):** The callback may use exactly the listed
effects. The HOF is expected to handle them:

```
fun try : (() -> a needs {Fail}) -> Result a String
try f = f () with {
  fail msg = Err msg
  return value = Ok value
}
```

**Open `needs` with `..e` (effect row polymorphism):** The callback may use
the listed effects plus any others. The extras propagate to the caller through
the row variable `..e`:

```
# run_logged handles Log, but forwards any other effects from the callback
fun run_logged : (f: () -> Unit needs {Log, ..e}) -> Unit needs {..e}
run_logged f = f () with { log msg = { println msg; resume () } }

# Caller uses both Log and Fail in the lambda.
# Log is handled by run_logged, Fail propagates through ..e
fun greet : Unit needs {Fail}
greet = {
  run_logged (fun () -> log! "about to greet")
  fail! "greeting failed"
}
```

The `..e` captures any additional effects from the lambda and makes them
appear in the function's own `needs` clause, so callers know they must handle
them. This is essential for HOFs that handle some effects but forward others.

---

## Testing with Effects

Effects make testing natural - swap the handler, not the code:

```
handler mock_http for Http {
  get url = resume "{\"status\": \"ok\"}"
  post url body = resume "created"
}


handler collect_logs for Log {
  log level msg = {
    # swallow logs silently
    resume ()
  }
}

test_server () = {
  run_server ()
} with {mock_http, collect_logs}
```

No mocking frameworks, no dependency injection containers. The function under
test is unchanged - only the handler differs.

---

## What Isn't an Effect: `panic` and `todo`

Not everything that interrupts execution is an effect. `panic` and `todo` are
language builtins that halt the program immediately. They exist outside the
effect system - no `!`, no handler, no `needs` propagation:

```
handler postgres_handler for Database {
  query sql = todo "connect to postgres and run query"
  execute sql = todo "connect to postgres and run execute"
}

fun impossible : Int -> String
impossible x = panic "this case should never happen"
```

Both return `Never`, so they work anywhere a value is expected. The difference
is intent:

- `panic "msg"` - logic error, unreachable code. Something is fundamentally wrong.
- `todo "msg"` - unfinished code. The type checker can treat this as a type hole,
  warn about remaining `todo`s, or reject them in release builds.

If you want recoverable errors, use the `Fail` effect instead - that's what
handlers are for.

---

## Summary

| Concept               | Syntax                                             |
| --------------------- | -------------------------------------------------- |
| Define an effect      | `effect Log { fun log : String -> Unit }`           |
| Perform an effect     | `log! "hello"`                                     |
| Named handler         | `handler h for Log { log msg = ... }`              |
| Handler with effects  | `handler h for Log needs {X} { ... }`               |
| Inline handler        | `expr with { log msg = ... }`                      |
| Attach named handler  | `expr with console_log`                            |
| Stack handlers        | `expr with { h1, h2, op args = ... }`              |
| Continue computation  | `resume value`                                     |
| Abort computation     | (just don't call `resume`)                         |
| Intercept success     | `return value = Ok(value)`                         |
| Qualify ambiguous ops | `Cache.get! key`                                   |
| Declare effects on fn | `fun f : Unit -> T needs {Log, Http}`              |
| Pure callback param   | `fun map : (f: a -> b) -> List a -> List b`        |
| Closed effect param   | `fun try : (() -> a needs {Fail}) -> Result a String` |
| Open effect row       | `fun run : (f: () -> a needs {Log, ..e}) -> a needs {..e}` |
