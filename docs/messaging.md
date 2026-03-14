# Messaging and Concurrency

Design sketch for typed-feeling concurrency on top of the BEAM's untyped mailbox.

## Core primitives

```
spawn : (() -> a) -> Pid
send  : Pid -> a -> Unit
self  : () -> Pid
```

`spawn` runs a function in a new BEAM process. `send` puts any value into a process's mailbox. Both are untyped at the boundary (the BEAM doesn't know or care about types in messages).

## receive

`receive` is a new expression form, like `case` but over the mailbox instead of a value:

```
receive {
  Ping(sender) -> send sender Pong
  Increment(n) -> loop (count + n)
  Shutdown -> ()
}
```

Messages that don't match any arm stay in the mailbox (BEAM selective receive). The expression's type is inferred from the arm bodies, which must unify.

No exhaustiveness checking on `receive` since the mailbox is open.

## Timeouts

```
receive {
  Msg(x) -> handle x
} after 5000 -> default_value
```

`after` clause runs if no matching message arrives within the timeout (milliseconds). Lowers directly to Core Erlang's `receive ... after` construct.

## Example: Counter process

```
type CounterMsg {
  Increment(Int)
  GetCount(Pid)
  Stop
}

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

main () = {
  let pid = spawn (fun () -> counter 0)
  send pid (Increment 5)
  send pid (Increment 3)
  send pid (GetCount (self ()))
  let result = receive {
    n -> n
  }
  print result  -- 8
}
```

## Example: Ping-pong

```
type PingMsg { Ping(Pid) }
type PongMsg { Pong }

pong_server () = {
  receive {
    Ping(sender) -> {
      send sender Pong
      pong_server ()
    }
  }
}

main () = {
  let server = spawn pong_server
  send server (Ping (self ()))
  receive {
    Pong -> print "got pong"
  }
}
```

## Example: Simple worker pool

```
type Job { Run(Pid, Int) }
type JobResult { Done(Int) }

worker () = {
  receive {
    Run(caller, n) -> {
      let result = n * n
      send caller (Done result)
      worker ()
    }
  }
}

main () = {
  let w1 = spawn worker
  let w2 = spawn worker
  send w1 (Run (self ()) 5)
  send w2 (Run (self ()) 10)

  -- collect both results
  let a = receive { Done(n) -> n }
  let b = receive { Done(n) -> n }
  print (a + b)  -- 125
}
```

## Design notes

- The mailbox is untyped. A `Pid` is just a `Pid`, not `Pid CounterMsg`. This matches the BEAM model and avoids the complexity of parameterized process types.
- Type safety comes from convention: define a message ADT, match on it. If someone sends the wrong type, the message sits in the mailbox unmatched (or hits a wildcard).
- `spawn`, `send`, `self` are builtins or FFI, not effects. They're direct BEAM operations with no handler semantics.
- `receive` is a new expression form that lowers to Core Erlang's `receive` primitive.
- Supervisors, monitors, links can be added later as FFI wrappers around OTP primitives.
- Typed channels / typed actors could be built as a library on top of this foundation using opaque types to restrict what can be sent to a process.
