# Sound typing of `resume`

Status: approved 2026-10-14. Branch `resume-type`. From a read-only design
study (nothing in it was built or run; line numbers are as read at
`bf0345da`). The owner asked for the sound fix, not a workaround, regardless
of which existing programs break.

## The unsoundness

`resume v` is typed as a pure function (`infer.rs`, `ExprKind::Resume`). But
resuming runs the rest of the handled computation under the same handler,
then the `return` clause, so it performs at least

    R = (inner − handled) ∪ eff(return clause) ∪ eff(arms) ∪ handler needs

(arms belong in R because later operations re-run arms inside the extent of
an earlier `resume`). This is Koka's HANDLE rule (Leijen, POPL'17 / MSR-TR
2016-29, Fig. 3): `resume` performs the handler context's row. Because Saga
types it pure, `fun s -> (resume s) s` is a pure lambda, `f 20` after the
`with` is a pure call, and an outer abort has nowhere to go.

The obvious fix (`resume` emits R) rejected good programs because of a
second, separable cause: the effect system cannot express "pure ≤ R" when R
is an open row. In `unify_effect_rows`, closed-vs-closed accepts a subset as
a recorded subsumption, but open-vs-closed and open-vs-open are equality, so
`{} ~ {..ρ}` binds `ρ := {}`. A pure arm value, a `return v = fun _ -> v`, or
a pure lambda returned at a rigid `..e` then pins R to empty.

## Unifier holes found by reading (to be confirmed by tests)

- **U1** (`unify.rs` ~409-411): open-vs-closed never looks at entries only
  the open side has, so `{Stop | e} ~ {}` succeeds with `e := {}` and Stop is
  lost. Example: `wrap : (Unit -> Int needs {..e}) -> (Unit -> Int needs
  {Stop, ..e})`, `apply_pure : (Unit -> Int) -> Int`, `bad g = apply_pure
  (wrap g)`.
- **U2** (~463-468): same single tail on both sides returns Ok even when the
  extras differ, so `{Stop | ρ} ~ {| ρ}` drops Stop. Example: `eq : a -> a ->
  a`, `bad f = (eq f (wrap f)) ()`.
- **U3**: `{..a, ..b} ~ {..b}` binds `b := {..a, ..b}` and reports an
  infinite row; common tails must cancel first.
- **H1** (`effects.rs` `check_effects_via_row` ~213-233): a declared open
  row accepts unparameterised extras: `h : (Unit -> Int needs {..e}) -> Int
  needs {..e}` with body `{ log! "x"; f () }` is accepted; a caller
  instantiating `e := {}` is typed pure and `Log` is unhandled at run time.
- **H2** (`generalize`): the answer type and R live in the resume context,
  not in `env`, so `let k = fun x -> resume x` inside an arm can be
  generalised over them.
- **H3**: `with h` where `h` is only known by its type `Handler E` never
  relates the arms' answer type to the computation's; `extract_handler_info`
  on an `if` takes the first branch.

## The design: directional row subsumption at coercion positions, a `with`-scoped R, answer slack

This is Koka's OPEN rule applied only at the existing coercion positions
(decision D2a), not at every lambda. Lambda types stay closed and exact, so
the runtime representation rule (`value_repr`, bare unless the type performs
something) does not change.

1. **`subsume_rows(actual ⊆ expected)`**, used where the coercion path is
   direct (`coercion_path_is_direct`), decided during unification rather than
   judged afterwards. Normalise both rows; unify arguments of families on
   both sides. `missing` = actual entries absent from expected, plus actual
   tails absent from expected's tails. If nothing is missing, accept without
   binding anything (`{} ⊆ {..e}`, `{Stop} ⊆ {Stop, ..e}` pass: no pinning).
   Otherwise pick an absorber: a flexible tail of expected, preferring one
   marked slack; if exactly one candidate, bind `absorber := {missing,
   ..missing tails, ..fresh}` (missing tails exclude expected's own tails, so
   no cycle). With no absorber: missing entries are an error (today's
   message); a missing flexible tail is bound to the expected row; a missing
   rigid tail is bound to `{}` as today so `check_rigid_row_vars_abstract`
   keeps its message. Equality positions (at depth, exact) are unchanged
   except U1–U3.
2. **Inline `with`.** Compute remaining as today. Check the `return` clause
   first (`T_ret`, `E_ret`). `A := open_spine(T_ret)` (or `T` without a
   return clause): each own-arrow row of the answer gets one fresh slack
   tail. `R := {remaining, E_ret, ..ρ_arm}` with `ρ_arm` slack. In each arm,
   `resume` coerces its argument as today, emits R, returns A; arm values are
   coerced to A through `subsume_rows`. After all arms, require arms' own
   effects ⊆ R (`ρ_arm` absorbs them). Then close every slack variable this
   `with` created to `{}` (an instantiation, so sound; no leaked variables; A
   is widened only by what some arm forced in). Emit remaining ∪ E_ret ∪ arm
   effects outward as today. The `with`'s type is A after closing: e.g.
   `Int -> Int needs {Stop}` for a state-passing handler over a computation
   that performs Stop; unchanged when no arm resumes under a lambda.
3. **Named handlers.** Allocate `ρ_R`, registered as rigid while arms and
   return clause are checked (display name "the handled computation's
   effects"). `R = needs ∪ ..ρ_R`. Slack on A as in 2, closed at the end of
   registration. `check_rigid_row_vars_abstract(allow_closing = false)` on
   `ρ_R`. Strip `ρ_R` from the handler's stored `needs`. Add `ρ_R` to
   `HandlerInfo.forall` and a field `resume_row`. At `with`: instantiate and
   bind `ρ_R := remaining`.
4. **Handler values whose provenance is lost** (parameter, data, `if`
   branch) must be *uniform*: no `return` clause (or identity), answer type a
   generalisable variable not constrained by the arms, `ρ_R` not in the
   answer — Koka's first-class handler type `∀ε a. (() → ⟨E|ε⟩ a) → ε a`. A
   non-uniform handler may only be named directly in `with` or aliased
   statically. (Decision; the alternative is extending `Handler E` to carry
   the answer and R, a larger language change.) Closes H3.
5. **Generalisation.** Inside an arm, the free variables of the resume
   argument type, the answer type and R are treated as environment variables
   in `generalize` / `generalize_let_binding`. Closes H2.

Soundness sketch: effects are sets; a substitution only replaces a variable
with a row containing a fresh variable or with `{}`, which preserves every
established inclusion. `subsume_rows` either finds the inclusion, binds a
flexible variable to make it hold, or fails. Closing slack is an
instantiation. R contains remaining ∪ E_ret ∪ arm effects ∪ needs by
construction, so every function whose body performs `resume` carries R on
the arrow that runs it, and every call site sees R. With U1/U2 fixed no
unification drops an entry.

Accepts/rejects compared with today: `make` becomes `Int -> Int needs
{Stop}`; passing it where a pure function is expected is rejected naming
Stop; `run_state_fail` (open `..e`, pure `fail` arm) still accepted; pure
lambdas returned at a rigid `..e` newly accepted; U1/U2/H1 programs rejected;
a resuming thunk stored in a pure field when R ≠ ∅ rejected (correctly);
non-uniform handlers passed as `Handler E` values rejected.

Errors keep the three existing `effect row mismatch` messages, plus a
provenance note when the offending row contains R ("this function resumes
the computation handled by the `with` at L:C; resuming runs the rest of that
computation, which performs {Stop} that this `with` does not handle").

Code generation: unchanged representation rule. Named-handler arm lambdas
carry `..ρ_R` and are tagged at every site (correct; per-site bare is an
optional later optimisation). Separate codegen step: a CPS closure that
resumes must pass the result of `resume`/`mbind` to its own `_ReturnK`
instead of returning a suspension.

## Steps (each mergeable and tested)

0. Tests first (ignored where needed): U1, U2, H1, H2, H3 reproductions and
   the snippet list below.
1. Unifier fixes U1–U3 (~80 lines). Measure with the function-shape matrix
   and the parameterised-effect generator how many programs change.
2. `subsume_rows` at direct coercion paths, slack-variable tracking (~200,
   minus ~100 of the old after-the-fact judging). `effect_row_rule_tests`
   unchanged; `multi_row_var_two_open_tails_in_callback_are_ambiguous` stays.
3. Resume-context variables monomorphic (H2, ~30).
4. Inline `with` per 2 (~150). Un-ignore the two typechecker tests; the guard
   `generic_state_runner_with_an_aborting_arm_is_accepted` stays green.
5. Named handlers per 3 (~120). Expect snapshot diffs for examples 54, 55.
6. Uniformity rule for `Handler E` values per 4 (~80).
7. H1 (declared open rows reject unnamed extras).
8. Codegen: resuming CPS closures return through `_ReturnK`; un-ignore the
   runtime tests. (After the abort work on `abort-exc` lands.)

Estimated 650–800 lines of non-test code, ~400 of tests.

## Snippets to add as tests

1. `make` (inline, concrete): result arrow contains Stop; `leak` (passing it
   to `apply_pure`) rejected naming Stop.
2. `run_state_fail` guard accepted; at run time under `stop _ = 1000`; the
   unannotated `rsf init f = …` infers `f : Unit -> a needs {State, Fail, ..e}`.
3. Named `passing`: `counter () with passing : Int -> Int needs {Stop}`;
   `apply_pure (counter () with passing)` rejected; `handler bad for Ask {
   ask () = apply_pure (fun x -> resume x) }` rejected at the declaration.
4. Inline counterpart: accepted when the computation performs only Ask,
   rejected when it also performs Stop.
5. Multishot: `pick_stop () with { choose () = List.flat_map (fun b ->
   resume b) [True, False]; return v = [v] }`; the lambda node's type carries
   Stop (`expr_types_tests.rs`).
6. Stored resume: a list of resumptions folded over (accepted, performs
   Stop); `Box { run: fun x -> resume x }` with a pure field rejected when
   R ∋ Stop, accepted when R = {}; a `Step` type with a pure thunk field
   rejected.
7. Generalisation: `let k = fun x -> resume x; apply_pure k` rejected when
   R ∋ Stop; a named handler using `k` at two types around a String
   computation rejected.
8. Arm and return effects in R: `get () = { log! "g"; fun s -> (resume s) s }`
   and `return v = { log! "r"; fun _ -> v }` make the state function perform
   Log; calling it outside a Log handler rejected.
9. Nested handlers of the same effect: inner state-passing arm lambda calling
   the outer `get! ()` carries {State, Stop}; returning it past the outer
   `with` into a pure context rejected.
10. Open-row trait methods: resuming over `next x` for a where-bound `x : a`
    carries `..a` (accepted under `needs {..a}`, rejected when pure); with
    `impl Src Text needs {Stop}` the concrete call carries Stop.
11. Uniformity: `use : Handler Ask -> Int needs {Stop}`, `use h = ask_stop ()
    with h` accepted; non-uniform handler values and `if c then to_result else
    to_result2` rejected.
12. Unifier holes U1, U2, H1: rejected.
13. No pinning: a pure lambda in one arm, the `return` clause, and a resuming
    lambda over a rigid `..e`, in inline and named handlers: accepted.

## Open questions from the study

- Completeness of the greedy absorber choice in `subsume_rows` (expected not
  to reject anything today's unifier accepts, not proven).
- Closing slack at the end of the `with` could reject a later equality-
  position use at a larger row (today's closed rows reject those too).
- Callbacks given to outer operations that capture `resume`: typed with R,
  evidence routing in `append_tail` not checked.
- Whether R is fully known before slack closing in every arm shape (deferred
  lambda arguments, open-row reference settlement run late).
- Whether type declarations can take row parameters (`Step e a`), which
  would give the pure-field case a non-breaking spelling.

## Outcome

Tests are in `src/typechecker/resume_typing_tests.rs` unless noted.

### Step 0: reproductions

All five holes reproduce, but U1 not as described. `thunk_pure (wrap g)`
was already rejected, for the wrong reason: `check_fun_clauses` put the row
of the function a declaration *returns* (`innermost_effect_row`) on the
function's own first arrow as well, and unified that with the declared
(empty) first arrow through `unify` (no position), where U1 dropped Stop and
closed `..e` in `wrap`'s own scheme. So `wrap` was typed `(Unit -> Int) ->
(Unit -> Int needs {Stop})`. The same placement accepted a function that
performs an effect before returning a function while its first arrow was
declared pure (`early`, unsound). U2 and U3 reproduce once U1 is fixed (U2:
`bad f = (eq f (wrap f)) ()` typed without Stop). H1, H2 and both H3
programs are accepted as described.

### Step 1: U1-U3

- `unify_effect_rows` cancels tails both rows share before comparing (U3).
  When only shared tails remain, a single shared tail takes the named
  effects that only one side has (`{Stop | r} ~ {| r}` binds `r := {Stop |
  r'}`, U2); more than one shared tail is the ambiguous-row error.
- Open-vs-closed: the open side's named effects that the closed side lacks
  (U1) go into a shared tail if there is one, else they are recorded like a
  closed-vs-closed subset with the open side larger, so the position judges
  them (a coercion accepts `{} ⊆ {Stop | e}`, rejects the reverse).
- `check_fun_clauses` checks a body against, and builds the function's own
  arrow from, the row of the arrow its arity saturates
  (`saturated_effect_row`), not the innermost one. The two "forwarded
  tail" checks (callback `..e`, open-row trait method `..a`) also accept a
  tail forwarded on the returned function's arrows.

Newly rejected (breaking-change list):

- A function that performs an effect before returning a function whose
  type names the effect only on the returned arrow (`fun early : Int -> Int
  -> Int needs {Log}`, `early x = { log! ".."; fun y -> x + y }`): calling
  `early 1` performs Log, which its first arrow does not allow. Sound.
- Function-shape matrix, 9 entries added to
  `function_shape_matrix_typecheck_rejected.txt`: `eta_op.{returned,
  returned_let, cross_module_ret}.{e1, e2, eu}`, i.e. `fun make : Unit ->
  (Int -> Int needs {Bump})`, `make () = bump!`. An effect operation
  referenced without arguments captures the handler in scope where the
  reference is written (`lower_eta_reduced_effect_op_ref`; the typechecker
  emits the effect at the reference, which is also why
  `eta_op.let_outside_handler` was already rejected). So calling `make`
  needs a Bump handler, which its pure first arrow does not provide; it was
  accepted only through the misplaced row. Writing `make () = fun x -> bump!
  x` is accepted.

Examples and stdlib: unchanged, all typecheck. `effect_property_tests` and
`core_snapshot` unchanged. Non-test `src/`: +117 / -12.

### Step 2: directional subsumption at direct coercion positions

- The position of a unification is kept on the checker while it runs
  (`RowMode`, with the coerced expression's literal structure as an owned
  `DirectShape`), and `unify_effect_rows` decides each pair of rows as it
  meets them (`unequal_rows`). The recorded `row_subsumptions` judged after
  the fact are gone; the three `effect row mismatch` messages are unchanged.
- `subsume_rows(actual ⊆ expected)` as designed, with one deviation: it is
  used only when one of the two rows has a *protected* tail, i.e. a row
  variable fixed by a declared signature (or a where-bound type's), or one
  created for `resume` (`slack_rows`, from step 4 on). Rows of inference
  variables only are still unified as equal, which is one solution of the
  inclusion and the one inference made so far. Reason: "nothing missing,
  bind nothing" for an ordinary variable leaves it unbound, so a pure
  callback passed to `List.map` would leave the call's `..e` open and give
  the enclosing unannotated function an open row (and a different calling
  convention); and binding an actual tail's missing part into the expected
  tail lets an effect the callee handles (`{Log, ..e}`) flow into its
  result row through `e`. For protected rows the absorber gets no fresh
  tail unless it is slack (whose rest is slack too and closed later).
- With no tail to absorb into, a missing *declared* tail is closed to the
  expected row's named effects (so `check_rigid_row_vars_abstract` reports
  it as before); an inference or slack tail is bound to the expected row.

Newly rejected (all sound):

- A declared row variable no longer takes on effects to make a coercion
  hold: `with_log : (Unit -> Int needs {..e}) -> (Unit -> Int needs
  {..e})`, `with_log f = fun () -> { log! ".."; f () }` was accepted (the
  caller's `..e` widened with Log); now "a function that uses {Log} is used
  where ..." is reported. Returning `fun () -> { log! ..; 1 }` at `Unit ->
  Int needs {..e}` is still rejected, now with that message instead of
  "requires that row to be exactly {Log}".
- Two independent declared row variables are no longer merged:
  `mix : (Unit -> Int needs {..a}) -> (Unit -> Int needs {..b})`, `mix f =
  f` ("declares the open effect row `..a`, but its body requires that row
  to be empty").
- U2 at a declared row variable (`fun bad : (Unit -> Int needs {..e}) ->
  Int needs {..e}`, `bad f = (eq f (wrap f)) ()`), accepted at step 1.

Newly accepted: a pure function returned or passed where a function over a
declared `..e` is expected (`fun mk : Unit -> (Unit -> Int needs {..e})`,
`mk () = fun () -> 1`), which closed `..e` and was rejected.

Core snapshot: 09-sorting and 21-do-else changed only in the numbering of
dictionary parameters (`___dict_Ord_v801` -> `v786`; fewer fresh variables
are allocated); blessed. Matrix, examples, stdlib, `effect_property_tests`:
unchanged. Non-test `src/`: +330 / -110 (`unify.rs` mostly moved code).

### Step 3: the resume context is monomorphic (H2)

`generalize` leaves out the free variables of the `resume` in scope (its
argument type and answer type; R is added at step 4), as it does those of
the environment. So `let k = fun x -> resume x` (or `let k = resume ()`) in
an arm is one function at the handled operation's types.

Newly rejected: the H2 program (a named handler using `k` at String while
the handled computation is an Int: "type mismatch: expected String, got
Int"). Sound.

Core snapshot: `Std.Test`'s `collect` handler binds `let k = resume ()`
and calls `k (...)` inside a `fun entries -> ...`. `k` was generalised, so
the call was compiled at an instantiated open row (`apply_cps` with an
empty frame); it is now at the answer type, which is pure, so the call is
a direct one (`is_function`/`apply_n`). Either path runs either closure
representation; `stdlib_tests` (the stdlib's own test suite, run by this
handler) passes. Blessed. Examples were not rechecked at this step (not
required); matrix and `effect_property_tests` unchanged. Not fixed, found
on the way: an arm may pin an operation's own type variable (`pick : List
a -> a`, `pick xs = resume 1` is accepted); that is not about
generalisation and is left for a separate fix. Non-test `src/`: +20.

### Step 4: inline `with`

As designed: the `return` clause is checked first; the answer type `A` is
the return type with one `Slack::Answer` tail per arrow of its spine
(`open_answer_spine`); `R = remaining ∪ E_ret ∪ ..ρ_arm` (`ρ_arm` is
`Slack::Arm`); in each arm `resume` coerces its argument, emits `R`
(`resume_effects`, saved and restored like `resume_type`, and in
`enter_scope`) and returns `A`; arm values are coerced to `A`. After the
arms, their effects (and `finally` blocks') are coerced into `R`, then
`close_slack` binds this `with`'s slack, and what is left of it, to `{}`.
The `with`'s type is `A`. `generalize` also leaves out the variables of
`R`. Deviations:

- `close_slack` also closes the inference variables made while the `with`
  was checked that slack was bound to (an equality position such as an
  `if` join binds a slack tail to a fresh shared one), so none stays open
  in the answer type. It does not close declared row variables: an arm's
  callback parameter has the operation's own `..r` (registered rigid), and
  closing it typed the callback as pure, which compiled its call as a pure
  call (`callbacks_across_a_delimited_with` caught this).
- The provenance note has no line and column (the checker has no source
  text): "This function resumes the computation handled by the enclosing
  `with`: resuming runs the rest of that computation, which performs {Stop}
  that the `with` does not handle." while the arm is being checked (the
  function's row still has the `with`'s slack), and "This function is the
  value of a `with` whose handler resumes inside it: calling it runs the
  rest of the handled computation, which performs {Stop} that the `with`
  does not handle." when the coerced expression is the `with` itself.
  Appended to the existing "a function that uses ..." message.

Tests: the two ignored typechecker tests in `tests.rs` are un-ignored and
pass; `generic_state_runner_with_an_aborting_arm_is_accepted` stays green.
Snippets 1, 2, 4-10 and 13 (inline forms) are in `resume_typing_tests.rs`.

Newly rejected (all sound; R ≠ ∅ in each):

- A function that resumes, or the value of such a `with`, used where a
  pure function (or one with fewer effects) is expected: `apply_pure (fun
  x -> resume x)` over a computation that also performs Stop; `apply_pure
  (counter () with {get () = fun s -> (resume s) s ...})`; `let k = fun x
  -> resume x; apply_pure k`.
- A resuming function stored in a field typed pure (`Box { run: fun x ->
  resume x }`, `More(fun () -> resume 1)` of `type Step = Done(Int) |
  More(Unit -> Step)`) when the rest of the computation performs something.
- Calling a state function outside a handler for what the arms or the
  `return` clause perform (`get () = { log! ..; fun s -> ... }` makes the
  state function perform Log).

Examples, stdlib, core snapshot, matrix and `effect_property_tests`:
unchanged (no inline handler in them resumes under a function over a
computation with effects left; `Std.Control.run_writer`'s `R` is `{}`).
Non-test `src/`: +198 / -16.

### Step 5: named handlers

As designed: `register_handler` checks the `return` clause before the arms
(its types are frozen after them), allocates `ρ_R`, registered rigid while
the arms are checked, sets `R = needs ∪ ..ρ_R` and opens the answer type's
spine with slack, closed after the arms. `ρ_R` is stripped from the stored
`needs`, added to `forall` and recorded as `HandlerInfo.resume_row`; a
`with` naming the handler binds its instance to what the computation
leaves unhandled. Deviation: instead of `check_rigid_row_vars_abstract`
(whose message names a written `..e`), the handler gets its own error when
`ρ_R` was closed or given named effects: "handler 'bad' resumes inside a
function that is used where no effects may be performed, but resuming runs
the rest of the computation the handler is installed around, which can
perform any effect the handler does not handle. Use the function where its
effects are allowed, or write the handler inline at the `with`, where that
computation is known". The note on the value of a `with` (step 4) also
covers named handlers (`apply_pure (counter () with passing)`).

Newly rejected (sound):

- A named handler whose arm puts a resuming function where its effects
  are not allowed: `handler bad for Ask { ask () = apply_pure (fun x ->
  resume x) }`.
- `Std.Stream.stream_of` (`yield v = More v (Stream (fun () -> resume
  ()))`): the `Stream` thunk is pure, but forcing it resumes whatever
  computation the handler was installed around. Edited: `stream_of` is
  removed (it was `pub`, but nothing in the repository used it outside
  `from_gen`) and `from_gen` installs the same arms inline, where the
  producer is known to perform only `Gen a`, so the thunk is pure. The
  emitted code for `Std.Stream` is identical (named handlers are compiled
  at their `with`). This removes a public name: user code that wrote
  `with stream_of` must use `Stream.from_gen`.
- The state function of a named state-passing handler now carries the
  computation's unhandled effects (`counter () with passing : Int -> Int
  needs {Stop}`), so using it as a pure function is rejected.

Core snapshot: 54 and 55 (`choose options = List.flat_map (fun x -> resume
x) options`): the callback now carries `..ρ_R` and is a tagged CPS closure
that passes `resume`'s result to its `_ReturnK` through `mbind`. Output of
`saga run` checked unchanged for 54, 55 (and 58, which uses
`Stream.from_gen`); matches the expected output in their headers. 09 and 21
changed only in dictionary-parameter numbering again. Blessed. Matrix and
`effect_property_tests` unchanged; all examples and the stdlib typecheck;
`stdlib_tests` passes. Non-test `src/` (incl. Stream.saga): +145 / -41.
