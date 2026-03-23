# Effect Implementation Plan: CPS Transform to Core Erlang

## Core Idea

All effects are implemented via CPS (Continuation-Passing Style) transform at compile time. There is **one mechanism** for all effects — resumable, non-resumable, and multishot. No `throw`/`catch`, no process spawning for control flow.

Every effect call captures "everything after this point" as a closure (`K`) and passes it to the handler. The handler decides what to do:

- **Resume:** call `K(value)` — computation continues
- **Abort:** don't call `K` — computation is abandoned, handler's return value is the result
- **Multishot:** call `K` multiple times — each call runs an independent copy of the rest of the computation (free on BEAM since closures are immutable)

---

## CPS Transform

### Effect calls become continuation-passing

A function like:

```
fun do_work () -> Int needs {Log}
do_work () = {
  log! "starting"
  let x = 10 + 20
  log! ("result: " <> show x)
  x
}
```

Transforms to Core Erlang where each `op!` call passes a continuation:

```erlang
'do_work'/1 = fun (HandleLog) ->
  apply HandleLog('log', "starting",
    fun (_) ->
      let X = call 'erlang':'+'(10, 20) in
      apply HandleLog('log', <msg>,
        fun (_) -> X))
```

The key transform: everything after an effect call becomes the body of a `fun` that is passed as the last argument to the handler.

### Handler representation

A handler is a function that receives `(op_name, args..., K)`:

```erlang
% handler console_log for Log { log msg -> { print msg; resume () } }
'console_log'/3 = fun (_Op, Msg, K) ->
  call 'io':'format'("~s~n", [Msg]),
  apply K('unit')

% handler to_result for Fail { fail reason -> Err(reason) }
'to_result_fail'/3 = fun (_Op, Reason, _K) ->
  {'Err', Reason}       % don't call K = abort
```

### `with` attaches the handler

```
do_work () with console_log
```

Becomes:

```erlang
apply 'do_work'/1('console_log'/3)
```

The effectful function takes its handler(s) as extra parameter(s).

---

## Handler Stacking (Multiple Effects)

When a function needs multiple effects:

```
fun run () -> Unit needs {Log, Fail}
```

It takes multiple handler parameters. `with` passes them:

```
run () with { console_log, to_result }
```

Becomes:

```erlang
apply 'run'/2('console_log'/3, 'to_result_fail'/3)
```

Each effect call in the body routes to the correct handler based on which effect the operation belongs to (known at compile time from effect declarations).

---

## The `return` Clause

The `return value -> Ok(value)` clause wraps the computation's final value when it completes successfully (without the effect triggering an abort).

In CPS, this means wrapping the computation body so its final result passes through the return clause:

```
{ computation } with to_result
```

Where `to_result` has `return value -> Ok(value)`, the final value of the computation is wrapped in `Ok(...)`. If `fail!` is called, the handler returns `Err(reason)` directly without calling `K`.

Implementation: the CPS transform wraps the innermost continuation's return value through the `return` clause function.

---

## Non-Resumable Effects (Fail, Abort, etc.)

**No special mechanism needed.** A non-resumable handler simply doesn't call `K`:

```erlang
fun (_Op, Reason, _K) ->
  {'Err', Reason}
```

The continuation closure `K` is never invoked. It sits unreferenced on the heap and gets garbage collected. The handler's return value (`Err(Reason)`) becomes the result of the entire `with` expression.

There is no stack unwinding, no `throw`/`catch`, no special control flow. It's the same calling convention as resumable handlers — the only difference is one line of code (the `apply K(...)` call) being present or absent.

**Do NOT implement non-resumable effects via Erlang's throw/catch.** This creates two separate control flow mechanisms that interact poorly and prevents a unified implementation.

---

## Multishot Continuations

On BEAM, multishot is essentially free. `K` is an immutable closure on the heap. Calling it multiple times is just calling a function multiple times — no stack copying, no special machinery.

```erlang
% handler all_choices for Choose {
%   choose options -> flat_map (fun opt -> resume opt) options
%   return value -> [value]
% }
'all_choices'/3 = fun (_Op, Options, K) ->
  call 'lists':'flatmap'(fun (Opt) -> apply K(Opt) end, Options)
```

Each `apply K(Opt)` runs the entire rest of the computation independently. The type system already allows this (no linearity check on `resume`).

---

## Stack Depth Consideration

When `resume` is in tail position (the common case), BEAM's tail call optimization applies:

```erlang
% log msg -> { print msg; resume () }
fun (_Op, Msg, K) ->
  call 'io':'format'("~s~n", [Msg]),
  apply K('unit')              % tail call -- no stack growth
```

When the handler does work after resume, it's NOT in tail position:

```erlang
% invalid err -> { let (v, errs) = resume (); (v, err :: errs) }
fun (_Op, Err, K) ->
  let Result = apply K('unit') in    % not tail position
  let {V, Errs} = Result in
  {V, [Err | Errs]}
```

Stack depth is proportional to the number of effect calls in the non-tail case. On BEAM this is fine (per-process stacks grow as needed). This is the same tradeoff as any non-tail-recursive function — the user should put `resume` in tail position when possible.

---

## Implementation Order

**Start with a resumable effect (Log), not Fail.** If you start with Fail, you'll be tempted to use `throw`/`catch` because it's the obvious shortcut. If you start with Log, you're forced to build CPS properly because there's no shortcut for "print a message and continue." Once CPS works for Log, Fail falls out for free as a handler that doesn't call `K`.

Suggested order:

1. **Log effect** — simplest resumable effect, validates the CPS transform works
2. **Multiple effect calls in sequence** — validates continuation chaining
3. **Fail effect** — validates non-resumable (just don't call `K`)
4. **`return` clause** — validates success-path wrapping (`to_result`)
5. **Handler stacking** — multiple handlers on one `with` block
6. **Named handlers** — `handler foo for Eff { ... }` compiled to module-level functions
7. **Effect propagation** — effectful functions called from other effectful functions (handler parameters threaded through)
8. **Multishot** — should work automatically if the above is correct, just verify

---

## Processes Are Not the Effect Mechanism (But Handlers Can Spawn Them)

The CPS transform is the effect mechanism. Processes are never used to *implement* the handler/continuation plumbing itself. However, individual handlers are free to spawn processes in their body — this is how `Async` and `Actor` effects work. The handler receives `K` via CPS like any other handler, but internally spawns a BEAM process to do real concurrent work:

```erlang
% Async handler: spawn! creates a real process
'async_handler'/3 = fun ('spawn', Thunk, K) ->
  let Pid = call 'erlang':'spawn'(Thunk) in
  apply K(Pid);
('await', Pid, K) ->
  % selective receive
  apply K(Result)
```

The effect call/handler/continuation mechanism is always CPS. The handler's *body* may use processes when appropriate, but that's an implementation detail of specific handlers, not the effect system itself.

---

## Optimization Opportunities

- **Inlining:** When the handler is statically known (`with console_log` right there in the source), the compiler can inline the handler body directly, eliminating the closure allocation and indirect call entirely
- **Dead effect elimination:** If a handled effect is never actually called in the computation, the handler can be stripped
- **Pure functions (no `needs`):** No CPS transform at all — compiled as normal Core Erlang functions with zero overhead
- **Effect row polymorphism (`..e`):** Row variables are a type-checking concept only. They're fully resolved before codegen, so the CPS transform sees concrete effect sets. No runtime cost.
