# Koka-Faithful Foreign-Abort Routing

Goal: make `resume` stop classifying foreign aborts. A foreign abort should
always propagate. If a foreign abort should become the value of `resume`, that
means the owning delimiter must be inside the captured continuation and catch it
before it reaches the resuming arm.

## Finding (Step 2 diagnostic ran — Step 5 is insufficient as written)

The Step 2 diagnostic was run: making `lower_resume` propagate foreign aborts
makes the outer-abort case pass and the inner-abort case
(`fail_handler_inside_resume_aborts_correctly`) fail with `err:bang` instead of
`before/err:bang`. That confirms the diagnosis (the inner delimiter is not on
the resumed continuation's path).

But the fix in Steps 5–6 (reify the delimiter as the body's return-K) **cannot
work on its own**, because in this encoding **aborts short-circuit**: a
non-resuming arm returns `{__saga_handler_abort, marker, value}` *without*
applying `_K_arm`, so the tuple bubbles up the Core Erlang return-value stack
*past* every `fun(x)->…` continuation until a `case` inspects it. A reified
delimiter return-K is a `fun` that is never *applied* on the abort path, so the
short-circuiting abort bubbles straight past it to `lower_resume`'s own `case`.
Putting the delimiter "in the continuation chain" does not help when aborts
don't traverse the chain.

For the inner delimiter to catch a resumed abort, the abort must **bubble
through binds** (be inspected/composed at each bind) rather than short-circuit —
i.e. the full `Ctl = Pure v | Yield(marker, action, resumption)` model with the
composing bind law `bind(Yield m f k, g) = Yield m f (λx. bind (k x) g)`. The
delimiter-as-return-K is then a necessary piece (the prompt re-installed in the
captured continuation), but only works in combination with bind-level bubbling.
Note `lower_value_position_bind` already does a `case`-on-result; the general
`lower_bind` does not — that asymmetry is the gap.

Conclusion: this is the larger Ctl/bubbling change, not the smaller
delimiter-as-return-K change. The steps below are kept for reference but Step 5
should be folded into a `Pure | Yield` protocol with case-on-bind, not pursued
alone.

## Finding 2 (prototype attempt — the composing bind IS required)

A follow-up question was whether evidence passing lets us *drop* the composing
bind law `bind(Yield m f k, g) = Yield m f (λx. bind (k x) g)`. Argument: a
perform looks the handler up in the evidence and calls it directly, so resumes
are direct calls and never bubble — so (the reasoning went) only aborts route,
and the resumption is already the CPS `_K_arm`, complete, needing no
composition.

A prototype of that simplification (prompt reified as the body's return-K, no
composing bind) was started and traced; it does not hold. Evidence passing
removes one thing but not the other:

- **It removes "bubble to *find* the handler."** True — performs are direct
  evidence-lookup calls.
- **It does NOT remove "re-install inner delimiters in the resumption."** When
  handler H resumes, the captured continuation must re-enter the delimiters that
  lexically sit *between the perform site and H* (e.g. an inner `to_result_str`
  between `work`'s `fail!` and the outer `collect`). In the CPS encoding those
  inner prompts are `case`/wrap expressions positioned around the *original*
  body evaluation; they are not part of `_K_arm`, so a resumption does not
  re-enter them and the inner abort escapes to H's resume site.

Embedding the inner prompts *into the captured continuation* so resumptions
re-enter fresh instances is exactly what the composing bind law (or, equivalently,
the monadic `Ctl` computation that carries its prompts) provides. So the
composing bind cannot be dropped. Net: keep the full `Pure | Yield` model with
case-on-bind AND composition. The earlier "evidence passing ⇒ no composition"
simplification is retracted.

## Implemented Shape

This pass implements the needed control-result behavior in the existing
tuple/CPS encoding rather than introducing a literal `Pure | Yield` IR node:

- `lower_resume` no longer unwraps foreign aborts. Non-matching abort markers
  propagate unchanged.
- `with` bodies install a `ResultDelimiter` in `LowerCtx`. Static and dynamic
  handlers route their body return through a prompt K that catches the current
  marker and propagates foreign markers.
- `ResultDelimiter` is a stack, not a single slot. Each delimiter records the
  effects it handles, its marker, and its parent prompt. A perform-site K is
  wrapped only through the prefix needed to reach the handler selected for that
  operation.
- Ordinary binds and value-position binds now inspect abort tuples and bubble
  them to the enclosing return K instead of binding them as ordinary values.
- Handler arm bodies restore the previous delimiter stack from the `with` site
  instead of clearing it. This keeps enclosing prompts available to operations
  performed inside arm bodies.
- Performs inside handler arm bodies reify successful handler-arm results as
  target-marked value results. That lets the result escape to the handler that
  owns the operation without being mistaken for an ordinary value at an
  intervening perform site. Ordinary body performs keep the existing return
  composition path.
- There are two `__saga_value_result` tuple shapes by design:
  `{__saga_value_result, value}` is local to value-position bind, while
  `{__saga_value_result, marker, value}` is the routed form that bubbles to the
  prompt identified by `marker`.
- The e2e repro
  `"foreign abort propagates through an inner resuming arm"` is unskipped.
- The mirror arm-body repro is pinned by
  `fail_inside_nonresuming_arm_captures_outer_prompt`.
- **Markers must be globally unique, not per-function** (commit `176492a`). The
  marker atom is built once per lexical `with` site by `fresh_abort_marker`
  (`lower_monadic/mod.rs`) from a never-reset, module-qualified counter — NOT
  from the per-function `ret_k` counter (which resets at every function entry
  and made the first `with` in every function share one atom, so a callee's
  prompt caught a caller's abort). Static-per-site (vs Koka's fresh-per-
  activation) is sound here because performs dispatch to the nearest handler via
  evidence and a terminal abort bubbles to the innermost matching delimiter, so
  an abort is produced and caught by the same activation even under recursion;
  re-raises are performs, not own-marker aborts. Revisit only if first-class /
  named handlers gain continuations resumed outside their original dynamic
  extent. Guard: `effects_test.saga` "re-abort propagates across a
  function-call boundary".

This is intentionally the unoptimized form. It adds extra `case` inspection at
bind boundaries so the optimization phase has a correct control protocol to
simplify later.

## Finding 3 (the arm-body case was the symmetric gap)

The "Implemented Shape" bullet *"Handler arm bodies clear the lexical
`ResultDelimiter`"* (`arm_ctx = ctx.without_result_delimiter()...` in
`lower_with_static`) is the dual of the bug just fixed, and it is wrong for the
same reason — one level out.

**Confirmed empirically.** Take the exact oracle
(`fail_handler_inside_resume_aborts_correctly`) and move its `log!; fail!`
sequence out of `work`'s *body* and into a non-resuming handler's *arm body*:

```saga
handler fire_h for Trigger needs {Log, Fail String} {
  fire () = { log! "before"; fail! "bang"; log! "after"; "tail" }
}
result () = ((fire! () with fire_h) with to_result_str) with collect
```

This is semantically the oracle plus a transparent (non-resuming) `fire_h`
layer, so it must return `before/err:bang`. Before the fix it returned
**`err:bang`** — the `before/` was lost because the abort short-circuited *past*
`collect.log`'s `resume()` instead of returning through it. Root cause:
`collect` (outer,
resuming) captures a continuation *inside `fire_h`'s arm body*, and that arm
body's binds have no delimiter to re-install, so `fail!`'s abort to the *outer*
`to_result_str` never re-enters its prompt. A control case with **no resume**
(arm body aborts directly, no continuation captured) returns the correct
`err:boom` — confirming the gap needs a continuation captured *in the arm body*,
which is exactly when the cleared slot matters.

**Why clearing is the wrong operation.** At the `with` site, `ctx` is the *outer*
scope; this handler's delimiter is installed only on `body_ctx`. So
`ctx.result_delimiter` at that point is already the **enclosing** delimiter
(`prev`), not this handler's. `without_result_delimiter()` therefore removes the
*enclosing* delimiter from arm bodies — even though arm bodies run inside the
enclosing handler. The intended discipline is save/restore: snapshot `prev` on
`with` entry, install this handler's on the body, and **restore `prev`** (not
empty) for arm + return-clause bodies.

**The one-line "restore prev" was necessary but not sufficient.** Dropping the
`without_result_delimiter()` call (so `arm_ctx` keeps `ctx`'s `prev`) *does* fix
the routing — `before/err:bang` reappears — but it was incomplete two ways:

1. **Over-application.** The repro then returns `ok:before/err:bang`: re-installing
   the full enclosing delimiter as a `_raw` wrap unwraps the abort to a plain
   value too early, and the *real* outer delimiter reprocesses it through its
   return clause (`ok:`). The resumption needs *this* handler's delimiter for the
   duration of the resumed body, then `prev` *after* — two regimes in sequence.
   A single carried `ResultDelimiter` can't express both across (multishot)
   invocations; the captured continuation must carry the pair.
2. **Finally regressions.** It breaks `"cleanup runs on abort"` and
   `"abort still cleans up"` in `effects_test.saga` — restoring `prev` changes
   how aborts traverse the finally cleanup path, which has to be reconciled
   (see Step 9).

The implemented fix is the per-operation delimiter-prefix regime:

- keep the enclosing delimiter stack in arm bodies,
- push a new delimiter only for the handled body,
- when lowering a perform, wrap the K through the stack prefix up to the
  delimiter that handles that effect,
- for performs inside handler arm bodies, bubble successful arm results as
  target-marked value results so they escape to the owning handler delimiter
  rather than falling back into the perform site,
- preserve abort tuples through finally cleanup.

This keeps the mirror repro, the original inner-abort property, multishot
handlers, return-only handlers, and finally cleanup green together.

## Target Invariant

`lower_resume` should eventually behave like:

```text
resume_result =
  apply _K_arm(value)

case resume_result of
  {__saga_handler_abort, my_marker, v} ->
    continue_with_value(v)

  {__saga_value_result, v} ->
    continue_with_value(v)

  {__saga_handler_abort, other_marker, v} ->
    propagate unchanged

  v ->
    continue_with_value(v)
```

No depth. No foreign-marker unwrap.

## Step 1: Add/Keep Tests First

Keep both sides pinned:

- Existing passing property:
  `tests/effect_property_tests.rs::fail_handler_inside_resume_aborts_correctly`
- E2E repro:
  `tests/e2e/tests/effects_test.saga` ->
  `"foreign abort propagates through an inner resuming arm"`

Before implementation, create a temporary local version of the skipped case as a
Rust property test if easier to iterate. It should assert:

```saga
(log_then_fail () with silent_log) with to_result
```

returns:

```saga
Err "boom"
```

Keep both tests green when touching bind, resume, or handler prompt lowering.

## Step 2: Make Foreign Propagation Locally

Temporarily change `src/codegen/lower_monadic/exprs.rs::lower_resume` so foreign
abort tuples propagate unchanged:

```text
{abort, other_marker, other_value} ->
  cleanup_if_needed_then_return_tuple({abort, other_marker, other_value})
```

Expected result:

- Outer-abort repro starts passing.
- Inner-abort property fails.

That failure is the signal: the continuation passed to `resume` is missing the
inner delimiter.

Keep this as the debugging posture while fixing continuation construction.

## Step 3: Inspect Captured K Shape

Focus on these paths:

- `src/codegen/lower_monadic/effects.rs::lower_with_static`
- `src/codegen/lower_monadic/effects.rs::wrap_with_result_delimiter`
- `src/codegen/lower_monadic/effects.rs::lower_yield`
- `src/codegen/lower_monadic/exprs.rs::lower_bind`
- `src/codegen/lower_monadic/exprs.rs::lower_value_position_bind`

For the inner-abort case:

```saga
result () = (work () with to_result_str) with collect
```

the `log!` perform occurs inside the inner `to_result_str` with-body. The op
handler is `collect`, but the continuation passed to `collect.log` must
represent:

```text
rest of work after log!
then inner to_result_str delimiter
then return value to collect.resume
```

If `_K_arm` only contains "rest of work" and not the inner delimiter wrapper,
`fail!` will return a foreign abort tuple to `collect.resume`, which is the
current bug.

## Step 4: Find Where Delimiter Wrapping Is Outside the Captured K

Likely culprit shape in `lower_with_static`:

```rust
let body_ctx = ctx.with_evidence(acc_evidence_var).with_return_k(inner_k);
let body_ce = self.lower_expr(body, &body_ctx);
let wrapped_body = self.wrap_with_result_delimiter(body_ce, &abort_marker, ctx);
```

This lowers `body` under `inner_k`, then wraps the whole body afterward. But if
an operation inside `body` captures `ctx.return_k`, it may capture `inner_k`
directly, not a K that routes through `wrap_with_result_delimiter`.

That means the delimiter exists around the original body execution, but not
inside resumptions captured from inside that body.

## Step 5: Reify the With Delimiter Inside a Control-Result Protocol

Do not implement this as a return-K-only patch. Instead, first make lowered
effectful computations return an explicit control result (`Pure` / `Yield` or
Saga's equivalent abort/yield tuple discipline), and make binds inspect and
bubble that control result.

Once control results bubble through binds, reify the `with` delimiter as the
prompt that interprets those results. It can then catch its own marker and
propagate non-matching markers.

Conceptually:

```text
lower body -> Ctl

prompt(my_marker, Ctl) =
  case Ctl of
    Pure v ->
      apply inner_return_clause_or_outer(v)

    Yield/abort my_marker payload resume ->
      handle locally

    Yield/abort other_marker payload resume ->
      bubble unchanged
```

For static handlers, the rough shape becomes:

```text
let _Prompt = fun(raw_ctl) ->
  <delimiter logic over raw control result>

in
  lower body so captured continuations re-enter _Prompt
```

Important: this may require splitting `wrap_with_result_delimiter` into two
helpers:

- one that builds a delimiter continuation function from `(abort_marker, outer
  ctx)`,
- one that wraps a fully lowered expression for top-level execution if still
  needed.

The prompt form is the key part; it only works after abort/yield results are
forced to bubble through binds instead of bypassing continuations.

## Step 6: Preserve Return Clause Semantics

Return clauses complicate this. Current static flow has:

```text
body return_k = return_clause_k or raw_result_k
wrap_with_result_delimiter(body_ce, abort_marker, outer_ctx)
```

The delimiter K should preserve that behavior:

```text
_K_delim(raw) =
  case raw of
    own abort ->
      apply outer_k(v)             # or preserve marker in value-position mode

    foreign abort ->
      foreign abort tuple          # bubble

    ordinary value ->
      apply return_clause_k(v)     # if return clause exists
      or apply raw_result_k(v)
```

Be careful: if `return_clause_k` itself returns an abort tuple, the delimiter may
need to interpret that result too, depending on current semantics. Use existing
tests around aborting return clauses and nested handlers as guardrails.

A safer structure may be:

```text
body return_k = inner_success_k

inner_success_k(v) =
  apply return_clause_k(v) or raw_result_k(v)

_K_delim(raw) =
  case raw of
    abort cases...
    ordinary v -> apply inner_success_k(v)
```

Then captured resumptions include `_K_delim`.

## Step 7: Apply Same Idea to Dynamic Handlers

`lower_with_dynamic` has the same shape:

```rust
let body_ctx = ctx.with_evidence(new_ev_name).with_return_k(inner_k);
let body_ce = self.lower_expr(body, &body_ctx);
let wrapped_body = self.wrap_with_result_delimiter(body_ce, &abort_marker, ctx);
```

Once static works, apply the same control-result prompt pattern there.

## Step 8: Confirm Value-Position Bind Interaction

`lower_value_position_bind` uses `preserve_abort_marker` so abort tuples do not
become ordinary argument values. After changing delimiters into control-result
prompts, re-run tests around:

- aborting handler inside value position,
- nested handler in function argument,
- examples 54/55 multishot continuations,
- `fail_handler_inside_resume_aborts_correctly`.

Watch for double wrapping:

```text
{__saga_value_result, {__saga_handler_abort, ...}}
```

or swallowed aborts.

## Step 9: Finally Cleanup

Once both routing tests pass, revisit `finally`.

For `resume` with `finally`, cleanup should run when the resumed continuation
returns to the arm with either:

- ordinary value,
- own delimiter value,
- foreign abort that is propagating past the arm.

But cleanup must not unwrap foreign aborts. The propagated tuple should remain
intact after cleanup.

This likely means factoring the duplicate cleanup helpers in `lower_resume`
into:

```rust
sequence_finally_then(expr_to_return_or_apply)
```

## Step 10: Remove Skip and Document

Current state:

- `"foreign abort propagates through an inner resuming arm"` is unskipped.
- Foreign aborts always propagate in `lower_resume`.
- Delimiters are reified as captured return continuations.
- No depth protocol is used.
- The lowering now follows the Koka-style prompt bubbling invariant, encoded
  with abort tuples and CPS return Ks.

## Implementation Order

1. Done: change foreign abort in `lower_resume` to propagate as a diagnostic.
2. Done: confirm the outer repro passes and the inner property fails before the
   prompt/bind fix.
3. Done: define the lowered control-result protocol as the existing abort tuple
   plus return-K bubbling.
4. Done: generalize `lower_bind` so control results bubble through binds and the
   rest of the computation re-enters active prompts.
5. Done: reify static `with` delimiters as prompts over control results.
6. Done: port the same prompt protocol to dynamic handlers.
7. Done: reconcile `lower_value_position_bind`, native op boundaries, entry
   points, and finally cleanup with the unified protocol.
8. Done: run effect property tests and e2e.
9. Done: unskip the outer-abort e2e repro.
10. Remaining cleanup: reduce prompt/bind helper duplication and teach the
    optimization pass to remove redundant prompt/result cases where safe.

The big thing: do not try to make `lower_resume` smart. Make captured
continuations contain the right prompt frames, then `lower_resume` becomes dumb
and correct.
