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
- Ordinary binds and value-position binds now inspect abort tuples and bubble
  them to the enclosing return K instead of binding them as ordinary values.
- Captured bind continuations re-enter the current result delimiter before
  returning to the resuming handler, which restores the prompt frames needed for
  resumed computations.
- Handler arm bodies clear the lexical `ResultDelimiter`: they run under the
  outer evidence/return K, but they are not part of the handled body prompt.
- The e2e repro
  `"foreign abort propagates through an inner resuming arm"` is unskipped.

This is intentionally the unoptimized form. It adds extra `case` inspection at
bind boundaries so the optimization phase has a correct control protocol to
simplify later.

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
