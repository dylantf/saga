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

(Filled in as steps land.)
