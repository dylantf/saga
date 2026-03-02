# dylang Effects Guide

Effects are dylang's core abstraction for anything that interacts with the
outside world - I/O, state, errors, concurrency. Instead of baking these into
the language as special constructs, they're user-defined and handler-provided.

---

## Defining an Effect

An effect declares a set of operations - what can be done, not how.

```
effect Log {
  fun log (level: String) (msg: String) -> Unit
}

effect Fail {
  fun fail (reason: String) -> Never
}

effect Http {
  fun get (url: String) -> String
  fun post (url: String) (body: String) -> String
}
```

An effect is like an interface: it names operations and their signatures, but
provides no implementation. The implementation comes from handlers.

---

## Performing Effects

Effect operations are called with `!` to distinguish them from pure functions:

```
fun run_server () -> Unit needs {Log, Http, Fail}
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

---

## Handling Effects

A handler provides implementations for effect operations. There are two forms:
**named** and **inline**.

### Named Handlers

Define a reusable handler with the `handler` keyword:

```
handler console_log for Log {
  log level msg -> {
    print! ("[" <> level <> "] " <> msg)
    resume ()
  }
}

handler sentry_log for Log {
  log level msg -> {
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
  log level msg -> {
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
  fun ask (prompt: String) -> String
}

handler interactive for Ask {
  ask prompt -> {
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
  fail reason -> Err(reason)
  return value -> Ok(value)
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
  fail reason -> Err(reason)
  return value -> Ok(value)
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
fun process () -> Unit needs {Log}
process () = {
  log! "info" "working"    # unambiguous - only Log has `log`
}
```

When multiple effects define the same operation name, qualify with the effect
name:

```
effect Database {
  fun get (key: String) -> String
}

effect Cache {
  fun get (key: String) -> String
}

fun fetch (key: String) -> String needs {Database, Cache}
fetch key = {
  let cached = Cache.get! key
  let fresh = Database.get! key
  ...
}
```

Handlers mirror this:

```
} with {
  Cache.get key -> {
    let result = lookup_cache! key
    resume result
  },
  Database.get key -> {
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
  get url -> http_get! url |> resume,
}
```

For a single handler, skip the block:

```
run_server () with console_log
```

Or bundle multiple effects into a single named handler:

```
handler dev_env for Log, Database, Http {
  log level msg -> {
    print! ("[" <> level <> "] " <> msg)
    resume ()
  }
  query sql -> sqlite_query! sql |> resume
  get url -> http_get! url |> resume
}

handler prod_env for Log, Database, Http {
  log level msg -> {
    sentry_send! level msg
    resume ()
  }
  query sql -> postgres_query! sql |> resume
  get url -> http_get! url |> resume
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

## Handlers Close Over Their Scope

Handlers are closures - they can reference variables from the surrounding scope:

```
main () = {
  let db_conn = connect! "postgres://localhost/mydb"
  let debug = true

  run_app ()
} with {
  query sql -> {
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
fun run_server () -> Unit needs {Log, Http}
run_server () = {
  log! "info" "starting"
  let data = get! "/api/health"
  log! "info" "ready"
}
```

This tells callers what handlers they need to provide. When a function calls
another effectful function, it inherits those effects (minus any it handles
itself):

```
# start_app calls run_server (which needs Log, Http)
# and also uses Database directly
# it handles Log itself, so only Http and Database bubble up
fun start_app () -> Unit needs {Http, Database}
start_app () = {
  init_db! ()
  run_server () with console_log   # handles Log here
}
```

Each `with` on a handler peels off the effects it covers. The program's entry
point must handle everything - nothing escapes unhandled.

### Effect polymorphism

Higher-order functions propagate effects from their callbacks using an effect
variable:

```
fun map (f: a -> b needs e) (xs: List a) -> List b needs e
```

If `f` is pure, `map` is pure. If `f` uses `Log`, `map` requires `Log`. The
caller always sees the full picture.

---

## Testing with Effects

Effects make testing natural - swap the handler, not the code:

```
handler mock_http for Http {
  get url -> resume "{\"status\": \"ok\"}"
  post url body -> resume "created"
}

handler collect_logs for Log {
  log level msg -> {
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

## Summary

| Concept               | Syntax                                             |
| --------------------- | -------------------------------------------------- |
| Define an effect      | `effect Log { fun log (msg: String) -> Unit }`     |
| Perform an effect     | `log! "hello"`                                     |
| Named handler         | `handler console_log for Log { log msg -> ... }`   |
| Inline handler        | `expr with { log msg -> ... }`                     |
| Attach named handler  | `expr with console_log`                            |
| Stack handlers        | `expr with { h1, h2, op args -> ... }`             |
| Continue computation  | `resume value`                                     |
| Abort computation     | (just don't call `resume`)                         |
| Intercept success     | `return value -> Ok(value)`                        |
| Qualify ambiguous ops | `Cache.get! key`                                   |
| Declare effects on fn | `fun f () -> T needs {Log, Http}`                  |
