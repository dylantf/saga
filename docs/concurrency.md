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
  fun send (pid: Pid msg) (msg: msg) -> Unit
  fun self () -> Pid msg
}
```

Three standard effect operations. `spawn` takes a zero-arg function, runs it
in a new process, returns a typed pid. `send` is type-safe because the pid
carries the message type. `self` returns the current process's pid.

## receive

`receive` is a language keyword (no `!`), like `case` but over the mailbox:

```
receive {
  Increment(n) -> counter (count + n)
  GetCount(caller) -> {
    send! caller count
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

## ActorMessage trait

Message types derive `ActorMessage` to bridge the typed/untyped boundary:

```
type CounterMsg {
  Increment(Int)
  GetCount(Pid Int)
  Stop
} deriving (Show, ActorMessage)
```

`deriving (ActorMessage)` generates the code that converts raw BEAM terms
from the untyped mailbox into typed values the pattern match can work with.
Messages that don't match any constructor stay in the mailbox (selective
receive).

The derived impl also provides constructors for known system messages
(process DOWN signals, monitor notifications, etc.) so they can be handled
in the same `receive` block:

```
counter count = {
  receive {
    Increment(n) -> counter (count + n)
    Stop -> ()
    Down(pid, reason) -> log $"process {pid} died: {reason}"
    Unknown -> counter count    # discard unrecognized messages
  }
}
```

`Down`, `Monitor`, and `Unknown` are provided automatically by the
`ActorMessage` derive. `Unknown` is an opaque catchall for anything that
doesn't match the declared constructors or known system messages.

## The handler

`beam_actor` is a compiler builtin. It looks like a normal handler from the
user's perspective (`with beam_actor`), but the compiler knows how to lower
it directly to BEAM primitives rather than going through the general handler
machinery.

This sidesteps two implementation challenges:
- Polymorphic handlers (the existing machinery always binds to a concrete type)
- spawn/CPS interaction (spawned processes run on a separate stack)

It can always be generalized later once the semantics are proven out.

```
# Usage is the same as any handler
main () = {
  let pid = spawn! (fun () -> counter 0)
  send! pid (Increment 5)
} with beam_actor
```

Under the hood:
- `spawn!` lowers to `erlang:spawn/1`
- `send!` lowers to `erlang:send/2`
- `self!` lowers to `erlang:self/0`
- `receive` lowers to Core Erlang's `receive ... after ... end`

## Multi-process typing

Each process has its own `Actor msg` scope with its own message type.
The `Pid msg` type bridges between them:

```
type PingMsg { Ping(Pid PongMsg) } deriving (ActorMessage)
type PongMsg { Pong } deriving (ActorMessage)

pong_server () = {
  receive {
    Ping(sender) -> {
      send! sender Pong
      pong_server ()
    }
  }
}

main () = {
  let server = spawn! (fun () -> {
    pong_server ()
  } with beam_actor)

  send! server (Ping (self! ()))
  receive {
    Pong -> print "got pong"
  }
} with beam_actor
```

Two `with beam_actor` scopes, two different message types. The parent's
`Actor PongMsg` types its send/receive. The child's `Actor PingMsg` types
the child's. Type-safe at compile time, untyped at runtime.

## Example: Counter

```
type CounterMsg {
  Increment(Int)
  GetCount(Pid Int)
  Stop
} deriving (ActorMessage)

counter count = {
  receive {
    Increment(n) -> counter (count + n)
    GetCount(caller) -> {
      send! caller count
      counter count
    }
    Stop -> ()
  }
}

main () = {
  let pid = spawn! (fun () -> counter 0)
  send! pid (Increment 5)
  send! pid (Increment 3)
  send! pid (GetCount (self! ()))
  let result = receive { n -> n }
  print (show result)
} with beam_actor
```

## Example: Worker pool

```
type Job { Run(Pid JobResult, Int) } deriving (ActorMessage)
type JobResult { Done(Int) } deriving (ActorMessage)

worker () = {
  receive {
    Run(caller, n) -> {
      send! caller (Done (n * n))
      worker ()
    }
  }
}

main () = {
  let w1 = spawn! worker
  let w2 = spawn! worker
  send! w1 (Run (self! ()) 5)
  send! w2 (Run (self! ()) 10)
  let a = receive { Done(n) -> n }
  let b = receive { Done(n) -> n }
  print (show (a + b))
} with beam_actor
```

## Example: Timeout

```
main () = {
  let pid = spawn! (fun () -> counter 0)
  send! pid (Increment 1)
  send! pid (GetCount (self! ()))
  let result = receive {
    n -> show n
    after 5000 -> "timed out"
  }
  print result
} with beam_actor
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
    let pid = spawn! (fun () -> counter 0)
    send! pid (Increment 42)
    send! pid (GetCount (self! ()))
    let n = receive { n -> n }
    print $"count = {n}"
  })
} with beam_actor
```

## What touches the compiler

1. **Token/Lexer**: `Receive` and `After` keywords
2. **AST**: new `Expr::Receive` variant with arms and optional after clause
3. **Parser**: parse `receive { arms... }` with optional `after N -> expr`
4. **Typechecker**: type arms against `msg` from `Actor msg` in scope, skip
   exhaustiveness, validate after clause
5. **Codegen**: lower to Core Erlang `receive ... after ... end`, recognize
   `beam_actor` as a builtin handler
6. **Prelude/stdlib**: `Pid` type, `Actor` effect definition, `ActorMessage` trait
7. **Derive**: `deriving (ActorMessage)` generates mailbox-to-typed-value
   conversion, includes system message constructors and `Unknown` catchall
