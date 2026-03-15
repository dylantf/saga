# Messaging and Concurrency

Actor-style concurrency on the BEAM, using the effect system.

## Pid type

`Pid msg` is a built-in parameterized type. At runtime it's an Erlang pid.
The type parameter exists only at compile time, giving typed send/receive
while the BEAM mailbox stays untyped underneath.

## Effects

Two separate effects cover concurrency:

```
effect Process {
  fun spawn (f: () -> Unit) -> Pid msg
  fun send (pid: Pid msg) (msg: msg) -> Unit
}

effect Actor msg {
  fun self () -> Pid msg
}
```

**Process** is unparameterized. `spawn` and `send` have free type variables
(`msg`) that are inferred per call site via normal HM unification. They don't
care what the current process receives -- you can freely spawn or send to
processes of any message type.

**Actor msg** is parameterized by the current process's message type. Only
`self` and `receive` use it (scoped to this process's mailbox).

This split means a function can talk to multiple process types without
conflict:

```
fun run () -> Unit needs {Process, Actor Int}
run () = {
  let c = spawn! (fun () -> counter 0)     # c : Pid CounterMsg
  let l = spawn! (fun () -> logger ())     # l : Pid LogMsg
  send! c (Increment 5)                    # typechecks
  send! l (Log "hello")                    # typechecks
  send! c (GetCount (self! ()))            # self! : Pid Int
  let result = receive { n -> n }          # receives Int
  print (show result)
}
```

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
- **Selective receive.** Unmatched messages stay in the mailbox.
- **No exhaustiveness checking.** The mailbox is open.
- **Message type from effect scope.** The typechecker looks up `Actor msg`
  in the current `needs` and uses `msg` for the patterns.
- **`after N`** is a keyword clause (like `return` in handlers). Lowers to
  Erlang's `receive ... after N -> ...`.
- A function containing `receive` must declare `needs {Actor MsgType}`.

No `!` on `receive` because it's a language construct, not an effect
operation. Same distinction as `case`, `if`, `do`.

## The handler

`beam_runtime` handles both Process and Actor. It's a compiler builtin --
looks like a normal handler (`with beam_runtime`) but the compiler transforms
the ops to direct BEAM calls during elaboration.

```
main () = {
  run ()
} with beam_runtime
```

Under the hood:
- `spawn!` lowers to `erlang:spawn/1`
- `send!` lowers to `erlang:send/2`
- `self!` lowers to `erlang:self/0`
- `receive` lowers to Core Erlang's `receive ... after ... end`

## Example: Counter

```
type CounterMsg {
  Increment(Int)
  GetCount(Pid Int)
  Stop
}

fun counter (count: Int) -> Unit needs {Process, Actor CounterMsg}
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

fun run_counter () -> Unit needs {Process, Actor Int}
run_counter () = {
  let pid = spawn! (fun () -> counter 0)
  send! pid (Increment 5)
  send! pid (Increment 3)
  send! pid (GetCount (self! ()))
  let result = receive { n -> n }
  print (show result)    # 8
}

main () = {
  run_counter ()
} with beam_runtime
```

## Example: Multiple child types

```
type CounterMsg {
  Increment(Int)
  GetCount(Pid Int)
}

type LogMsg {
  Log(String)
  Flush
}

fun run () -> Unit needs {Process, Actor Int}
run () = {
  let c = spawn! (fun () -> counter 0)
  let l = spawn! (fun () -> logger ())

  send! c (Increment 5)
  send! c (Increment 3)
  send! l (Log "hello from logger")

  send! c (GetCount (self! ()))
  let result = receive { n -> n }
  print (show result)

  send! l Flush
}
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

## Implementation summary

### What was built

1. **Tokens/Lexer**: `Receive` and `After` keywords
2. **AST**: `Expr::Receive` with arms and optional `after` clause
3. **Parser**: `receive { arms... after N -> expr }` expression form
4. **Typechecker**:
   - `Pid` registered as built-in parameterized type
   - `Process` effect (spawn, send) with per-call-site fresh type vars
   - `Actor msg` effect (self) with shared type param for receive
   - `beam_actor` registered as builtin handler
   - `receive` typechecked against Actor's `msg` param, no exhaustiveness
   - Typed spawn: `EffArrow` carries effect type arguments, lambdas and
     function references produce EffArrow when they use effects, unification
     links spawn's return type to the spawned function's Actor type param
5. **Elaboration**: Actor/Process effect calls (`spawn!`, `send!`, `self!`)
   transformed to `ForeignCall` nodes, stripping them from CPS. The
   `with beam_actor` handler is stripped entirely.
6. **Core Erlang IR**: `CExpr::Receive` variant with arms, timeout, timeout body
7. **Codegen**: `receive` lowers directly to Core Erlang `receive ... after`
8. **Interpreter**: `receive` panics with "BEAM-only"

### Key design decisions

**Elaboration bypass**: Actor/Process operations are transformed to
`Expr::ForeignCall` during elaboration, before the lowerer sees them.
No CPS, no handler params, no continuations. Just direct BEAM calls.

**Typed spawn via EffArrow**: `Type::EffArrow` carries effect type arguments
`Vec<(String, Vec<Type>)>` not just effect names. Lambdas produce EffArrow
when they use effects, and function references with effect type constraints
are also typed as EffArrow. When spawn's EffArrow parameter unifies with
the callback's EffArrow, the Actor type args link, making the returned pid
carry the correct message type. Sending the wrong message type is a compile
error.

**Effect absorption fix**: When a HOF absorbs effects from a callback
(e.g. `try` absorbs `Fail`), only effects the callback *introduced* are
removed from the caller's effect set. Effects the caller already had are
preserved. This prevents spawn from accidentally absorbing the caller's
own Actor effect.

## Future: OTP-style effects

### Timer

```
effect Timer {
  fun sleep (ms: Int) -> Unit
  fun send_after (pid: Pid msg) (ms: Int) (msg: msg) -> TimerRef
  fun cancel_timer (ref: TimerRef) -> Unit
}
```

The `after` clause in `receive` handles the common case, but `send_after`
allows sending a message to a process on a delay independently.

### Monitor

```
effect Monitor {
  fun monitor (pid: Pid msg) -> MonitorRef
  fun demonitor (ref: MonitorRef) -> Unit
}
```

Monitoring delivers a `Down` message to the caller's mailbox when the
monitored process dies. Open question: how to handle system messages that
aren't part of the declared message type. Options: require a `Down` variant
in the message type, or make monitor delivery its own mechanism.

### Link

```
effect Link {
  fun link (pid: Pid msg) -> Unit
  fun unlink (pid: Pid msg) -> Unit
}
```

Bidirectional crash propagation. Simpler than monitors, used for
"die together" semantics.

### Supervisors

Supervisors are just effect handlers that catch failures and restart
computations. No new language support needed:

```
supervised f = {
  f () with {
    fail reason -> {
      print $"Crashed: {reason}, restarting..."
      supervised f
    }
  }
}
```

More sophisticated supervisors (restart limits, backoff, one-for-one vs
all-for-one) are library code built on top of Monitor and Link.

### Async

Higher-level wrapper around Actor for request/response patterns.
Potential API TBD.
