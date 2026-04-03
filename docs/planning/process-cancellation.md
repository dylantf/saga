# Process Cancellation

## Status

Nearly complete. The receiving side is fully modeled — just missing the sending
side.

## What we have

`Std.Actor` already provides:

- **ExitReason ADT**: `Normal`, `Shutdown`, `Killed`, `Noproc`, `Error(String)`, `Other(String)`
- **SystemMsg**: `Down(Pid a, ExitReason)` and `Exit(Pid a, ExitReason)` for matching in receive blocks
- **Monitor**: `monitor`, `demonitor` — get notified when a process dies
- **Link**: `link`, `unlink` — bidirectional crash propagation
- **Timer**: `sleep`, `send_after`, `cancel_timer`

A monitored or linked process already receives `Down`/`Exit` messages with the
appropriate `ExitReason` when a process terminates.

## What's missing

One operation to explicitly kill a process from the outside. Add to the
`Process` effect:

```
pub effect Process {
  fun spawn : (f: Unit -> Unit needs {Actor msg, ..e}) -> Pid msg
  fun send : (pid: Pid msg) -> (msg: msg) -> Unit
  fun exit : (pid: Pid msg) -> ExitReason -> Unit    # new
}
```

Lowers directly to BEAM's `erlang:exit/2`.

## Usage

```
# Graceful shutdown
exit! pid Shutdown

# Forceful kill
exit! pid Killed

# Receiver (via monitor) matches as usual
receive {
  Down(dead_pid, reason) -> println $"Process died: {reason}"
}
```

## Implementation

Single addition:
1. Add `exit` to the `Process` effect in `src/stdlib/Actor.dy`
2. Lower to `erlang:exit/2` in the `beam_actor` handler
