# Messaging and Concurrency

Actor-style concurrency on the BEAM, using the effect system.

## Pid type

`Pid msg` is a built-in parameterized type. At runtime it's an Erlang pid.
The type parameter exists only at compile time, giving typed send/receive
while the BEAM mailbox stays untyped underneath.

## The Actor effect

```
effect Actor msg {
  fun spawn (f: () -> Unit) -> Pid msg
  fun self () -> Pid msg
}
```

Two effect operations. `spawn` runs a function in a new process and returns
a typed pid. `self` returns the current process's pid. Both are tied to the
current actor's message type `msg`.

`send` is a standalone builtin, not an Actor operation (see below).

## send

`send` is a standalone polymorphic builtin function, not part of Actor:

```
fun send (pid: Pid a) (msg: a) -> Unit
```

It's independent of the current actor's message type because you often need
to send to a process with a *different* message type (e.g. replying to a
caller). Making it standalone means `send caller count` works even when
`caller : Pid Int` and the current process handles `CounterMsg`.

Called without `!` since it's a regular function, not an effect operation.

## receive

`receive` is a language keyword (no `!`), like `case` but over the mailbox:

```
receive {
  Increment(n) -> counter (count + n)
  GetCount(caller) -> {
    send caller count
    counter count
  }
  Stop -> ()
  after 5000 -> print "timed out"
}
```

How it differs from `case`:

- **No scrutinee.** Pulls from the mailbox, not a provided value.
- **Selective receive.** Unmatched messages stay in the mailbox. This is why
  it can't be `case receive!() { ... }` -- that would consume the message
  before matching.
- **No exhaustiveness checking.** The mailbox is open. Unmatched messages
  stay queued.
- **Message type from effect scope.** The typechecker looks up the `Actor msg`
  effect in the current `needs` and uses `msg` as the type for the patterns.
  Arms are typechecked against a known type with full pattern checking, just
  no exhaustiveness.
- **`after N`** is a keyword clause (like `return` in handlers). Lowers to
  Erlang's `receive ... after N -> ...`.
- **Declares `needs {Actor msg}`.** A function containing `receive` must
  declare the Actor effect.

No `!` on `receive` because it's a language construct, not an effect operation
call. Same distinction as `case`, `if`, `do`.

## The handler

`beam_actor` is a compiler builtin. It looks like a normal handler from the
user's perspective (`with beam_actor`), but the compiler knows how to lower
it directly to BEAM primitives rather than going through the general handler
machinery.

```
# Usage is the same as any handler
main () = {
  let pid = spawn! (fun () -> counter 0)
  send pid (Increment 5)
} with beam_actor
```

Under the hood:
- `spawn!` lowers to `erlang:spawn/1`
- `send` lowers to `erlang:send/2`
- `self!` lowers to `erlang:self/0`
- `receive` lowers to Core Erlang's `receive ... after ... end`

## Multi-process typing

Each process has its own `Actor msg` scope with its own message type.
The `Pid msg` type bridges between them:

```
type PingMsg { Ping(Pid PongMsg) }
type PongMsg { Pong }

fun pong_server () -> Unit needs {Actor PingMsg}
pong_server () = {
  receive {
    Ping(sender) -> {
      send sender Pong
      pong_server ()
    }
  }
}

fun run () -> Unit needs {Actor PongMsg}
run () = {
  let server = spawn! (fun () -> {
    pong_server ()
  } with beam_actor)

  send server (Ping (self! ()))
  receive {
    Pong -> print "got pong"
  }
}

main () = {
  run ()
} with beam_actor
```

Two `with beam_actor` scopes, two different message types. The parent's
`Actor PongMsg` types its receive and `self!`. The child's `Actor PingMsg`
types the child's receive and `self!`. `send` works across both because
it's independently polymorphic over the pid's type parameter.

## Example: Counter

```
type CounterMsg {
  Increment(Int)
  GetCount(Pid Int)
  Stop
}

fun counter (count: Int) -> Unit needs {Actor CounterMsg}
counter count = {
  receive {
    Increment(n) -> counter (count + n)
    GetCount(caller) -> {
      send caller count
      counter count
    }
    Stop -> ()
  }
}

fun run_counter () -> Unit needs {Actor Int}
run_counter () = {
  let pid = spawn! (fun () -> counter 0)
  send pid (Increment 5)
  send pid (Increment 3)
  send pid (GetCount (self! ()))
  let result = receive { n -> n }
  print (show result)    # 8
}

main () = {
  run_counter ()
} with beam_actor
```

## Example: Worker pool

```
type Job { Run(Pid JobResult, Int) }
type JobResult { Done(Int) }

fun worker () -> Unit needs {Actor Job}
worker () = {
  receive {
    Run(caller, n) -> {
      send caller (Done (n * n))
      worker ()
    }
  }
}

fun run_pool () -> Unit needs {Actor JobResult}
run_pool () = {
  let w1 = spawn! (fun () -> worker ())
  let w2 = spawn! (fun () -> worker ())
  send w1 (Run (self! ()) 5)
  send w2 (Run (self! ()) 10)
  let a = receive { Done(n) -> n }
  let b = receive { Done(n) -> n }
  print (show (a + b))    # 125
}

main () = {
  run_pool ()
} with beam_actor
```

## Example: Timeout

```
fun wait_for_reply () -> String needs {Actor Int}
wait_for_reply () = {
  receive {
    n -> show n
    after 5000 -> "timed out"
  }
}
```

## Example: Supervision

Supervision is just a handler wrapping the Fail effect. No new concepts:

```
supervised f = {
  f () with {
    fail reason -> {
      print $"Worker crashed: {reason}, restarting..."
      supervised f
    }
  }
}

main () = {
  supervised (fun () -> {
    run_counter ()
  })
} with beam_actor
```

## Open design question: spawn return type

`spawn!` currently returns `Pid msg` where `msg` is the *current* actor's
message type. But the spawned function runs with a *different* Actor type.
The parent needs the pid typed according to the *child's* message type to
send it the right messages.

Current workaround: the spawned function handles its own `beam_actor`
internally, and `spawn!` is treated as returning a pid whose type is
inferred from usage (what you send to it).

Better solution TBD -- may require making `spawn` a standalone builtin
(like `send`) so its return type can be independently polymorphic:
```
fun spawn (f: () -> Unit) -> Pid a
```
Where `a` is inferred from the context (what messages are sent to the pid).

## What touches the compiler

1. **Token/Lexer**: `Receive` and `After` keywords
2. **AST**: new `Expr::Receive` variant with arms and optional after clause
3. **Parser**: parse `receive { arms... }` with optional `after N -> expr`
4. **Typechecker**: type arms against `msg` from `Actor msg` in scope, skip
   exhaustiveness, validate after clause
5. **Codegen**: lower to Core Erlang `receive ... after ... end`, recognize
   `beam_actor` as a builtin handler
6. **Prelude/stdlib**: `Pid` type, `Actor` effect definition, `send` builtin
