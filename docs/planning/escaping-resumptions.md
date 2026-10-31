# Resumptions that run outside their `with`

Status: prototype on branch `escaping-resumptions` (off `scope-fixes`).
Fixes the first two "Known gaps" of "The Continuation of a `with`" in
`docs/effect-implementation.md`. No typing or syntax change.

## The invariant

In the general (non-fused) lowering, a `with` with abort reference `Ref`
lifts the frame it inherits: an operation of that frame performed inside
returns a suspension `{'$saga_meta', M}` instead of calling its handler.
The suspension travels up the native stack, through tail calls and `mbind`,
until a *binder* of `Ref` gives `M` the meta continuation `Mk`: `bind` at the
`with`'s entry, or `bind` inside `resume_into(Ref, ...)` when a handler
further out resumes the computation. `M(Mk)` then calls the handler that was
in the inherited frame.

This relies on one thing: **whatever the code of `Ref`'s extent returns
natively reaches a binder of `Ref` first.** The code of the extent is the
handled computation and `Ref`'s own arms. A `resume` directly in an arm
satisfies it: the arm runs where the operation was performed, so its native
return goes to the same binder as the handled computation.

## How the two gaps break it

**Gap 1, state passing.** `get () = fun s -> (resume s) s`; the body is
`let f = counter () with {...}; f 20 + 100`, under an outer `Stop` handler
`stop i = (resume i) * 2`.

```
with entry: bind(counter() under lifted frame, k)
  counter performs get -> arm returns the closure f   (plain value)
  bind(f, k) -> k(f) = f 20 + 100                     (bind is done)
    f 20: resume 20 -> rest of counter -> stop! 20
          -> lifted Stop returns {'$saga_meta', M}
          mbind wraps it; f returns it to k, k to the function's caller
  -> the suspension reaches the outer `with`, which has no binder for Ref.
```

Result: `{'$saga_meta', _}` (an outer handler that does not use its resume
value happened to work only because its entry was direct, not lifted).

**Gap 2, a different handler where the function is called.**

```saga
fun build : Unit -> (Int -> Int needs {Stop})
build () = (counter () with passing) with { stop i = resume i }

{ let f = build (); f 20 + 100 } with { stop _ = 7000 }
```

`f`'s type performs `Stop`, so calling it must reach the caller's handler
(7000). The continuation `f` resumes was captured with the frame of the
`with` in `build`; its `Stop` entry there is direct, so it is called in
place: 140. With `stop _ = fun _ -> 1000` in `build` instead, its abort is
thrown to a `with` that has returned: an uncaught `'$saga_abort'`.

**A third case, same cause** (found while working on this; no gap was
listed): a `resume` under a `with` inside the arm.

```saga
ask () = { let r = (resume 1) with { stop i = resume (i + 5) }; r + 10 }
```

The resumed computation's `Stop` should go to the inner handler (it is the
handler where `resume` runs); it went to the one around the outer `with`
(242 instead of 126). With an inner delimited `with` that does not handle
`Stop`, its `bind` took a suspension that belongs to the outer `with` and
gave the outer handler only part of the continuation (121 instead of 242).

## Intended semantics

A handler is deep: resuming runs the rest of the handled computation with
the handler installed again, *at the `resume`*. So:

- an operation the resumed computation performs that its own `with`
  handles goes to that `with`'s arms;
- every other operation goes to the handler for it in the context of the
  `resume` call: for a `resume` in a function, the handlers around the call
  of that function. This is what OCaml 5 does (a continuation is a stack
  segment reattached under the resumer) and what Koka's `resume` performs in
  its type: the handler context's row, at the resume site. It is also what
  Saga's types already say: `resume` is typed with the residual row of its
  `with` (`docs/planning/resume-typing.md`), and a function value's effects
  are handled where it is called;
- an abort of the resumed computation's own `with` becomes the value of
  that `resume` (the `with` is delimited there again);
- an abort of a handler around the `resume` goes to that handler's `with`.

When the `resume` is directly in an arm, the context of the `resume` is the
context of the `with` (the arm runs outside the handler it belongs to), so
nothing changes there.

## Candidates

**A. Bind in the closure, always** (the earlier experiment): treat the
`resume` inside a function as a binder whose meta continuation ends in the
function's return. Fixes gap 1, but when the function is called while the
`with`'s binder is still pending (a resuming closure stored in a list and
called in the arm), the outer handler's `resume` sees only up to the
closure's return and the `with`'s continuation is applied afterwards to
what comes back: 42 for 242. It also still calls the captured frame's
handlers (gap 2).

**B. Know at run time whether the `with`'s binder is pending**
(per-`with` bookkeeping, keyed by the existing `make_ref`): return the
suspension natively when it is, bind it in the closure otherwise. Three
problems. "Pending somewhere above" is not the right test; what matters is
whether that binder is the *first* one the native return reaches (the
`resume`-under-an-inner-`with` case has the right binder pending above and
still goes wrong). Keeping the flag right needs dynamic state (process
dictionary) set and reset around CPS calls, exceptions, multishot
resumptions and suspensions that leave and re-enter the extent; and a
spawned process has another dictionary. And it does nothing for gap 2.

**C. Redirect the captured frame through the process dictionary**: lifted
entries look up "the current frame of `Ref`" before calling a handler.
Fixes gap 2 including direct entries, but has all of B's dynamic-extent
problems, and costs a dictionary read per operation in every general
`with`.

**D. Delimit again at the `resume` (recommended).** Make every `resume`
whose frame is not the arm's own a binder of its `with` that sends
suspensions to the frame where it runs. This is exactly the deep-handler
rule above, implemented with what the lowering already has.

- *Where.* The lowerer knows the arm's frame variable and the frame at each
  `resume`. They differ when the `resume` is inside a function in the arm
  (whose frame is its caller's, passed as its evidence argument) or under a
  `with` inside the arm. There it emits
  `reroot(R, Frame, F)` instead of `mbind(R, F, Ref)`; `R` is the resumed
  computation's result (its own aborts already caught, as before), `F` the
  rest after the `resume` (for a function, ending in its continuation).
- *Binder.* `reroot` on a value applies `F`. On a suspension it is
  `bind(S, [{reroot, Frame, F}])`: the meta continuation's last element
  names the frame. A lifted operation's `M(Mk)` looks at that terminal and,
  if it is a `reroot`, takes the handler from `Frame` by tag and operation
  index instead of the captured one. The continuation it passes is the
  usual `resume_into(Ref, K, V, Mk)`, so later suspensions of the same
  resumption go to the same frame and `Ref`'s aborts are caught there.
- *Direct entries.* Such a `with` lifts every entry of its frame
  (`lift_all_evidence`), so no handler of the captured frame is ever called
  where the operation is performed. Which `with`s: those whose arms contain
  a rerouted `resume`, decided while the arms are lowered. A handler value's
  arms are lowered where the value is built; there, a rerouted `resume`
  appends the atom `reroot` to its tuple and the installing `with` chooses
  the lifting at run time (`lift_for`). The marker comes after the return
  clause, whose lookup now takes the element after the operations only when
  it is a function.
- *Why the pending case still works.* Called while the binder is pending
  (the stored closure, called in the arm), the frame at the call is the arm's
  lifted frame: the suspension is dispatched to the lifted `Stop`, which
  suspends again, and that suspension travels natively to the `with`'s
  binder as before. The outer handler gets the whole meta continuation:
  242. No run-time pending test is needed, and the in-arm case under an
  inner `with` is fixed by the same rule (the inner `with`'s frame is the
  frame at the `resume`).

Nothing new is kept at run time: the frame is passed explicitly (it is the
function's own evidence argument) and lives in the meta continuation.

## What it costs

The fused path is untouched (a fused `with` has no rerouted `resume`: an
arm with a `resume` under a function or a `with` is not tail-resumptive).
The general path gains one test per suspension (`is_function(Mk)`, else
`lists:last(Mk)`; `resume_into` already does the same scan) and one `bind`
clause. A rerouted `resume` costs what `mbind` cost. The real cost is
lifting the direct entries in the `with`s that need it: each operation of
such an entry, performed in the handled computation, now suspends (about 60
ns more here).

Median `elapsed_ms` of three runs, same machine, before / after
(`benches/evidence`, plus a scratch program for the general path: entering
a general `with` 9M times; 100M operations of a direct entry inside one
general `with`; 10M steps of a state-passing handler):

| Benchmark | Before | After |
| --- | --- | --- |
| `closed_row_hot_op` | 796 | 793 |
| `open_row_hot_op` | 1360 | 1400 |
| `deep_call_chain` | 1718 | 1719 |
| general: enter a `with` | 970 | 975 |
| general: direct op inside | 830 | 831 |
| state passing, an outer direct op per step | 344 | 974 |
| state passing, no outer op | 282 | 284 |

The `open_row_hot_op` difference is noise (its runs before the change
ranged from 1336 to 1390, and its loop has no `with`).

The last-but-one row is the price of the fix, and is paid only by a `with`
whose arms resume in a function or under a `with` and whose computation
performs operations of direct handlers further out.

## The remaining gaps

- **Operations that carry a callback, or of more than seven arguments**,
  are still performed in place with the captured frame's handler. A
  resumption rerouted to another frame therefore still sends such an
  operation to the handler it was captured under (a `scope!` with an
  effectful callback gave 141 for 1140). Unchanged otherwise.
- **`run` sites inside a rerouted resumption** (a `finally` cleanup,
  `catch_panic`, a spawned process via `run_process`, `apply_n`) bind with
  `[run]`, which dispatches to the captured frame. A cleanup or a spawned
  process that performs an outer operation reaches the handler the
  computation was captured under. Passing the frame there would need it at
  those sites; not attempted.
- **Arms of a handler value** still perform against the frame where the
  value was built. Unchanged.
- **`finally` regions resumed in another process** are still cleaned up
  only by the process that entered them. Unchanged.
- **Quadratic meta continuations.** Each non-tail `resume` that suspends
  adds a frame to `Mk`, and `pending/1`, `owns_aborts/1` and now
  `handler_for/4` scan it. A loop that performs, under an outer handler of
  the shape `{ let r = resume x; r }`, one operation per step inside a
  delimited `with` is quadratic in the number of steps. Pre-existing; the
  new scan does not change the order.
