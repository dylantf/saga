# Sound Function Representation, Then Typed IR

Status: proposed (2026-10-12). Nothing in this document is implemented.

Revised after comparing against the earlier attempts recorded in
`docs/planning/direct-first-effect-lowering.md` on `main` and
`docs/planning/uniform-effect-translation/postmortem-and-next-steps.md` on the
`selective-uniform` branch. See [Prior attempts](#prior-attempts).

## Summary

The runtime crashes come from three gaps that no earlier attempt closed:

1. The typechecker accepts programs that no selective calling convention can
   represent.
2. A function value's representation cannot be recovered at a call site when a
   type variable or row variable hides it.
3. Codegen has types for only some expressions, so it guesses from syntax.

Stage A closes those three inside the existing backend, keeping direct style as
the default and gating every step on benchmarks. Stage B replaces positional
evidence. Stage C introduces a typed IR and Erlang source output, and is
decided after A and B using measurements.

## Why

All 1,469 tests pass today, yet every program in
[Appendix A](#appendix-a-reproductions) fails, and several involve no effects
at all. The direct-first plan listed most of these as Phase 4 guardrails
("mixed direct/CPS branch results", "CPS callable stored in arbitrary
tuples/records/constructors", "partial application of CPS functions") to be
rejected with a diagnostic. They are ordinary programs and should run.

## Prior attempts

| Attempt | Idea | Outcome |
|---------|------|---------|
| Selective CPS (original) | Recognise each effectful call shape | Missed shapes crash at runtime |
| Uniform monadic CPS | Every callable takes `(args..., Evidence, K)`; an optimizer removes it | Correct, but 30-50% slower with no effects in play and about 14x slower on effect-heavy JSON. The optimizer became an interprocedural partial evaluator. Not merged |
| Selective-uniform | Planner plus a monadic side path, fallback Core and adapters | Became a second execution model. Abandoned |
| Direct-first (current `main`) | One classifier produces metadata; the existing lowerer consumes it | Shipped. Keeps the good runtime shape, but classification is still per expression shape, so Appendix A remains |

Lessons carried into this plan, from the postmortem and the direct-first plan:

- **Direct style is the default.** Pure functions and pure dictionary methods
  compile to ordinary BEAM functions with no evidence or continuation.
- **Dictionaries must not become CPS-shaped wholesale.** Trait-heavy derived
  code amplified the uniform tax more than anything else.
- **No optimizer may be required for acceptable baseline performance.**
- **Benchmarks are acceptance gates from the first change,** not a later phase.
- **No big-bang rewrite.** Change one decision family at a time, with the old
  path working throughout.

### Where the first draft of this plan repeated them

The first draft proposed one calling convention for all closure values,
including dictionary methods, with direct dispatch restored later as an
optimisation. That is the uniform ABI again, applied to exactly the code the
postmortem identified as the amplifier. It also deferred all fast paths to a
final phase and replaced the lowerer, the IR and the emission target at once.
All three are changed below.

### What this plan adds that the earlier ones did not have

The postmortem left two questions open: whether function values need a runtime
tag for direct versus CPS shape, and how row-polymorphic callbacks can be
represented without forcing every callback into CPS. A8 answers the first:
call sites cannot always know statically, because a row variable instantiated
to the empty row inside a list leaves no place for an adapter. A6 and A7 show
the typechecker itself admitting unrepresentable programs. A2 to A4 show the
arity convention failing with no effects involved. None of the earlier
attempts changed the typechecker or the representation of closures; they all
tried to classify harder.

## Goals

- Every program in Appendix A either runs correctly or is rejected with a type
  error.
- No measurable regression against `main` on pure code, trait-heavy code, or
  the `saga_json` benchmarks, at every step.
- The representation of a function value depends on its own type and is
  checkable at runtime, so no call site depends on provenance.
- No language feature is removed, except the unsound cases of effect
  subtyping.

## Non-goals

- A uniform calling convention.
- An optimizer that is required for baseline performance.
- Replacing the lowerer as a precondition for fixing the crashes.
- Deciding whether type arguments belong in effect identity. Today's
  behaviour (`Fail String` and `Fail Int` distinct) is preserved.

## Decisions

| # | Decision | Status |
|---|----------|--------|
| D1 | Calls through a variable check the callee's arity at runtime; known calls stay direct | agreed |
| D2a | Typechecker: closed effect rows must match exactly except at coercion positions | agreed |
| D2b | Two closure representations, distinguishable at runtime: bare fun for direct, tagged for CPS | agreed |
| D3 | Emit Erlang source text instead of Core Erlang | agreed; moved to Stage C |
| D4 | Codegen gets its own complete type table; `type_at_node` stays LSP-only | agreed |
| D5 | Representation changes are whole-program behind one flag | agreed |
| D6 | Evidence keeps applied-effect identity; representation becomes a map | agreed |
| D9 | Benchmark gates are deferred for now | agreed |
| D7 | D2a lands as a warning first, then becomes an error | agreed |
| D8 | Breaking changes are acceptable; version goes to 0.5.0 when Stage A becomes the default | agreed |

### D2b: tagged CPS closures

Two earlier choices both fail:

- **Two conventions chosen statically, with adapters.** Unsound (A8).
- **One convention for every closure.** Sound, but it is the uniform tax on
  pure callbacks and on every dictionary method.

Instead, keep both representations and make them distinguishable:

| Value | Representation |
|-------|----------------|
| Closure of pure type | bare Erlang fun, arity = user arity |
| Closure of effectful or open-row type | `{cps, Fun}`, where `Fun` takes `(args..., Evidence, K)` |
| Top-level function | unchanged: `f/N` if pure, `f/(N+2)` if effectful |

A closure is created from its own type, never from the type its context
expects. Call sites:

- **Static type is pure.** After D2a, only a bare fun can arrive. If its arity
  equals the argument count, call it; this is the fast path and costs the same
  as today. Otherwise the D1 helper builds a partial application or applies in
  stages.
- **Static type is effectful or open-row.** Either representation can arrive.
  `{cps, F}` is called with evidence and continuation. A bare fun is called
  directly and its result passed to the continuation.

Consequences:

- Pure code and pure dictionary methods pay nothing.
- Open-row trait methods hold whichever representation each impl needs, so an
  impl-level `needs` does not force pure sibling methods into CPS.
- The contextual planner that tracks implementation ABI versus boundary ABI,
  and the adapters it inserts, are no longer needed for correctness.
- Pure callbacks pass to Erlang bridges unchanged.

Cost: one tuple allocation per effectful closure created, and one tag test per
call through a variable at an effectful type. Both are measured in Stage A.

**Evidence inside closures is looked up by tag.** Without adapters, the caller
of a closure does not know the positional layout its body was compiled
against. So a closure's evidence ABI is always "open, no static prefix": every
operation it performs finds its handler by tag, and a caller passes its frame
unchanged. The current representation supports this already, since every entry
is tagged and open rows use tag lookup today. Named top-level functions keep
positional indices, because their callers know the declared row. Operations
inside lambdas therefore get slower (a short linear scan instead of an indexed
load) until Stage B.

## Design

### Codegen type table (D4)

`infer_expr` is a single dispatch function. Wrap it so that every expression's
final type is written to a new table when inference of that node completes.
The table is zonked at the `to_result` boundary. The LSP does not populate it.

To verify: some nodes are inferred more than once (lambdas checked against an
expected type, deferred lambda arguments). The table must hold the type from
the attempt that was kept.

### Typechecker rule (D2a)

Today two closed rows unify whenever either is a subset of the other, at any
depth, and direction is only checked for direct function arguments. A6 lets an
unhandled effect escape the type system; A7 is the other direction.

New rule: closed rows unify only when equal. Subsumption (the actual row is a
subset of the expected row) applies at coercion positions only: direct call
arguments, annotated `let`, `if`/`case` branches, list and tuple literal
elements, record field initialisers, function return position.

With D2b, pure-to-effectful subsumption needs no adapter even at those
positions. Row-variable instantiation is unchanged and legal at any depth.

Subsumption must also become directional at every coercion position. Today
only direct call arguments are checked; an effectful function is accepted as
a pure one in an `if` branch against a declared return type (A11) and in a
record field (A12).

Existing row widening for tuple and list literals (for example
`run_pair (do_foo, do_bar)` against a shared `..e`) is a coercion-position
feature and is kept.

### Unknown calls (D1)

Call through a variable with `n` user arguments, at a pure static type:

- arity equals `n`: call directly, guarded by `is_function(F, n)`
- arity is larger: build a partial application closure
- arity is smaller: call with the arguments it takes, then apply the result to
  the rest

At an effectful static type the helper also handles `{cps, F}` at each step.
The slow paths live in one runtime module. Lambdas keep their syntactic arity;
`fun a -> fun b -> ...` and `fun a b -> ...` need not agree.

### Trait dictionaries

Method slots hold closures under D2b. A method whose trait signature is pure
is always a bare fun and is called exactly as today. Direct dispatch when the
dictionary is statically known is kept, not deferred.

### FFI

Four of the twenty bridge files (`Dict`, `Array`, `String`, `Set`) call Saga
closures. Erlang code cannot run the helper, so a function value crossing into
a bridge must be a bare fun of the declared arity. Pure closures already are.

### Evidence (Stage B)

An Erlang map keyed by effect family. Installing a handler is a map put;
performing an op is a map get. There is no positional prefix, no reframing at
call boundaries, and no adapter when rows differ, because a callee only looks
up what it needs. Distinct applications of one family are held under the
family key and selected by applied tag. The exact value shape is designed in
Stage B.

This changes the cost of every effect operation. The effect-options JSON
benchmark, which performs an op in a hot path, is the gate. If a map get loses
to today's static `element` loads there, keep a positional fast path for
closed rows and use the map only for open rows.

### Typed IR and Erlang output (Stage C)

Stage C is maintainability work. It removes the side tables and the 861
`ExprKind` match sites in codegen; it is not needed to fix Appendix A.

The IR is direct-style and typed. It is not the monadic IR of the uniform
attempt: there is no `Bind`, pure code stays pure code, and building it adds
no runtime cost.

```rust
struct Ir { ty: Type, span: Span, kind: IrKind }

enum IrKind {
    Lit(Lit),
    Local(VarId),
    Global { module: String, name: String, abi: CallableAbi },
    Con { tag: Atom, args: Vec<Ir> },
    Tuple(Vec<Ir>),
    Record { .. }, Field { .. }, Update { .. },
    Lam { params: Vec<Pat>, body: Box<Ir> },
    CallKnown { target: GlobalRef, args: Vec<Ir> },
    CallUnknown { callee: Box<Ir>, args: Vec<Ir> },
    Partial { callee: Box<Ir>, args: Vec<Ir> },
    Let { pat: Pat, value: Box<Ir>, body: Box<Ir> },
    Case { scrutinee: Box<Ir>, arms: Vec<Arm> },      // `if` folds into this
    Perform { effect: EffectId, op: usize, args: Vec<Ir> },
    Handle { body: Box<Ir>, handler: Box<Ir> },
    Handler { effect: EffectId, ops: Vec<OpArm>, ret: Option<Box<Ir>> },
    Resume(Box<Ir>),
    Foreign { module: Atom, fun: Atom, args: Vec<Ir> },
    Dict(DictRef), DictMethod { dict: Box<Ir>, index: usize },
    Receive { .. }, BitString { .. },
}
```

A checker pass verifies that every known call supplies the target's arity,
every unknown call's callee has a function type, and every `Perform` sits
under a row that includes its effect. Existing fast paths are ported as IR
passes one at a time, each with the checker run after it; none are dropped.

Erlang source emission needs unique variable names per function (an
already-bound variable in an Erlang pattern silently becomes an equality
test), named funs or lifted functions in place of `LetRec`, and no `Values`
form. `saga emit` would print Erlang and `saga emit --ir` the IR.

## Stages

Every step ends with the existing suite green.

### Benchmark gate (deferred)

Deferred by decision D9: Stage A proceeds on correctness alone. The earlier
attempts were sunk by performance found late, so this should be picked up
before A4 becomes the default. When it is, record on `main` and rerun at each
step:

- `saga_json` effect-options benchmark
- `saga_json` options-as-arguments benchmark, if that branch can be restored
- the cases under `examples/optimization`
- one actor example and one multishot or state-handler example

A step that regresses pure or trait-heavy code is backed out or narrowed.

### Stage A: sound representation, in the existing backend

**A0. Baseline.** Add a behavioural test for each program in Appendix A,
marked as expected failures.

**A1. Test generator.** Generate programs crossing the ways of producing a
function value (lambda, nested lambda, partial application, named function,
eta-reduced op, dictionary method, result of `if`/`case`/block, result of a
polymorphic call) with the places it can flow (direct argument, `let`, return
value, list element, record field, through `ident`, through an open-row
function, across a module boundary), in pure and effectful variants. Runs as
expected-failure with a recorded count.

**A2. Typechecker.** Add the codegen type table. Add D2a as a warning and
record how many warnings the stdlib, examples and sesh-importer produce.

**A3. Arity at pure types (D1).** Route calls through a variable to the
arity-checked path. No effect machinery is touched. Fixes A2 and A3.

**A4. Tagged CPS closures (D2b).** Closure creation and every call through a
variable at an effectful type change together, behind a flag. Lambdas lower
from their own type. Fixes A1, A4, A5, A7, A8, A9 and removes the contextual
adapter planner.

**A5. Switch.** Make D2a an error. A6, A11 and A12 become type errors, which
is the intended outcome. A7 also becomes a type error even though it runs correctly
after A4: allowing pure-to-effectful subsumption at depth would need variance
tracking, which this plan does not add. Fix A10. Flip the flag, bump to 0.5.0,
delete the old paths.

*Exit for Stage A:* Appendix A and the generator pass.

### Stage B: evidence as a map

Behind its own flag, with the effect-options benchmark as the gate. Removes
`runtime_shape.rs`'s reframing and most of `evidence.bridge.erl` if the gate is
met; otherwise keeps a positional fast path for closed rows.

### Stage C: typed IR and Erlang output

Decide after A and B. Proceed if the remaining shape-specific code in the
lowerer is still producing bugs or blocking work. If it goes ahead: build and
check the IR alongside the existing lowerer first, then move emission over one
construct family at a time, porting each fast path with it. Convert the
roughly 330 codegen tests that assert on Core Erlang text as the constructs
they cover move.

## Sizing

Measured on 2026-10-12 against `87e68150` using a throwaway worktree, since
removed. For calibration, the effect ABI refactor (PR #85) was 31 files,
+3248/-1521.

### What was measured

**How much code relies on the unsound row rule.** The unifier was instrumented
to log every acceptance of unequal closed rows, with its position, then run
over all 62 examples, 51 in-repo example and test projects, and copies of
`saga_json`, `saga_http`, `saga_csv`, `saga_pgo`, `saga_bcrypt` and
sesh-importer.

- 3 hits in total, all a pure function passed directly where an effectful one
  is expected. D2a keeps that legal.
- 0 hits at depth.

**What the test suite does under the stricter rule.** With unequal closed rows
rejected at depth, 1 of 1,469 tests fails:
`tuple_widens_shared_row_var_at_expected_type`, which exercises literal
widening and stays legal under the real rule. The crude experiment did not add
directional checks, so breakage from those is unmeasured.

**Whether the arity check is as local as it looks.** A spike of about 40 lines
of Rust in `lower_generic_apply` and 25 lines of Erlang, behind an environment
variable:

- fixed A2 and A4, and passed extra `compose`/`flip`/nested cases
- did not fix A3, which goes through the over-application branch of
  `lower_resolved_fun_call`
- broke nothing: the full suite gives the same result with the spike enabled

### Estimates

| Step | Scope | Size |
|------|-------|------|
| A0 baseline | 12 behavioural tests | small |
| A1 generator | new test file; roughly 8 producers x 8 positions x 2 | small to medium |
| A2 type table | wrapper on `infer_expr`, one new map through `to_result` | small |
| A2 row rule | strict unify plus a directional check at perhaps 10 to 15 of the 80 `unify` call sites | medium |
| A3 arity check | 4 to 6 call paths in `calls.rs`, one small runtime module | small |
| A4 tagged closures | see below | large |
| A5 switch | flag removal, version bump, deletions | small |

A4 in detail:

- **Creation sites to change:** the lambda arm in `exprs/dispatch.rs`; named
  functions used as values (four arms in `lower_resolved_value_ref` plus
  `lower_local_fun_ref`); partial application in `lower_resolved_fun_call` and
  `lower_generic_apply`; dictionary method slots in `module.rs`; eta-reduced
  operation references in `function_values.rs`.
- **Call sites to change:** `lower_runtime_cps_apply`, which variable calls,
  dictionary method calls and lambda-headed calls already share; field-access
  headed calls.
- **Code that goes away:** the contextual planner (about 565 lines of
  `function_values.rs`), the CPS adapters (about 400 lines), and their 45 call
  sites across 10 files.
- **Code to review, not sized:** `hof.rs`, `static_helpers.rs`, `optimize.rs`,
  `handler_analysis.rs` and `generic_fold/` total about 4,550 lines and build
  or call closures under the current shapes.
- **Tests:** about 62 of the roughly 440 textual assertions mention closures,
  `apply`, or evidence and would need updating; the rest are unaffected.

Overall, Stage A is comparable in size to PR #85, with A4 the bulk of it and
likely net-negative in lines. The largest uncertainty is how many of the fast
paths depend on the old closure shapes.

## Testing

About 330 tests across `src/codegen/tests.rs`, `tests/codegen_integration.rs`
and `tests/module_codegen_integration.rs` assert on Core Erlang text (roughly
450 assertions, counted by grepping assertion helpers). Stage A changes the
emitted shape of closures and calls through variables, so some will need
updating there; the rest are untouched until Stage C.

The behavioural oracle is the 91 tests in `tests/effect_property_tests.rs`,
the integration tests that run on the BEAM, the 24 `.saga` files under
`tests/e2e` and `tests/stdlib`, the examples, and the A1 generator.

## Rollout

- The closure representation is an ABI change. Stdlib, project and
  dependencies switch together; no mixing.
- The stdlib cache key hashes the compiler build and stdlib contents but not
  runtime flags. Each flag must be added to that key and to project manifests.
- Compiled dependencies under `deps/` are rebuilt on switch.

## Risks

- **A4 touches many paths.** Lambda lowering, partial application, function
  references, dictionary slots, the direct higher-order-function
  specialisation and static helper variants all create or call closures. It
  has not been sized in detail.
- **Existing fast paths may assume the old closure shape.** Each needs a
  generated case.
- **D2a breakage.** Unknown until the A2 warning count.
- **Tag-test cost.** Expected to be small; measured at A4.
- **Handler lowering** was surveyed from signatures and the effect doc, not
  read line by line.

## Open questions

- When to pick the benchmark gate back up.
- How applied-effect tags resolve under tag-only lookup (see A4 implementation
  notes).

## A4 implementation notes

From a read-only survey of the lowerer on 2026-10-12. Sections on fast paths,
Erlang boundaries and cross-module metadata were surveyed at one remove and not
re-verified line by line; nothing was built or run.

### Corrections to earlier sections

- **"At a pure static type only a bare fun can arrive" is false.** When the
  result type is a variable or a later arrow is effectful (`apply_gen eadd 1`),
  a tagged value reaches a call classified pure. Do not split statically: keep
  the inline `is_function(F, N)` fast path and make the `apply_n` slow path
  accept tagged values.
- **Bridges that call Saga funs** are `Dict`, `Array`, `Set`, `List`
  (`sort_with`, `sort_by`) and `Dynamic`, not `String`. All their callbacks are
  declared pure, so they are unaffected once D2a is an error.
- **Lambdas keep being flattened.** Nested lambdas and absorbed parameters stay
  merged into one fun; with the call helpers either choice is sound and this
  avoids nested tagging.

### Design answers

| Question | Answer |
|----------|--------|
| Tag format | `{'$saga_cps', F}`. A reserved atom cannot collide in well-typed code; `Dynamic`, `dbg` and `show` will see it |
| Arity mismatch at an effectful type | `apply_cps(F, Args, Ev, K)`. Exact arity: call. Too few: pass a tagged partial application to `K`. Too many: call with what it takes, continue with the rest. A bare fun gets the same treatment with its result passed to `K` |
| Named effectful function used as a value | An exported per-function wrapper that does the reframe, so the value is a constant tagged reference with no allocation per use |
| Hoisted dictionary methods | One body with a tag-only frame; direct calls pass the caller's frame unchanged |
| Frame passed to a closure | Unchanged. Treat a reframe whose target has an empty static prefix as identity |

### Unresolved: applied-effect tags under tag-only lookup

Today positional reframing and `append_tail` relabel entries by position, which
is how a handler installed generically as `Fail<$e>` reaches code that performs
`Fail<String>`. By tag alone, `find_evidence` can report an ambiguous family or
pick an outer exact match. This is the same question as the on-hold identity
decision (D6). Before the flip, add matrix cases with parameterised effects.
Interim approach: the caller relabels the callee type's named slots before
passing the frame.

### What must survive the deletion of the planner

- **Captured-evidence overlay.** A callback passed to an effect operation whose
  parameter row is `{Named.., ..r}` runs with the handler's call-time frame for
  the named effects and the perform-site frame for `..r`. This is a language
  semantic, not an ABI patch (`effects/call.rs:102-190`).
- **Native callback context.** For `spawn`, Actor operations are bound directly
  and the callback is a bare fun today.

### Sites that break and need the effectful call helper

`spawn` (`beam_interop.rs:393`), `catch_panic` (`builtins.rs:162`), and
`apply_n` / `partial` in `runtime.erl`.

### A latent bug to fix first

The lambda arm saves and restores only `current_evidence`. It leaves
`static_tail_resume_ops`, `no_resume_ops` and `direct_ops` set, so an operation
inside a lambda written under a `with` is bound statically to that handler even
if the lambda escapes. Clear all three on entry to a closure body, except for
the native callback case. Inferred from reading; not reproduced.

### Fast paths

Nothing needs disabling outright.

- **Direct higher-order-function variants** are the riskiest. The gate that
  decides a callback is direct (`hof.rs:239`) reads a planner fact. Replace it
  with "the argument's own type is closed and empty at every arrow".
- **Static helper inlining** needs its argument lowering swapped to the plain
  path.
- Tail-resume operations, handler analysis, known-impl dictionary dispatch and
  generic folding are unaffected.

### Call classification gap

`classify_app` returns pure for any head that is not a variable, qualified
name, dictionary method, lambda or field access, so `(f x) y` and `if`- or
`case`-headed calls are never effectful today. Classify every head that is not
a known function from its entry in the type table. Variable calls are
currently classified by a lexical name scope, not by type; that goes too.

### Order of work

1. **No behaviour change:** one predicate from a type to bare or tagged; the
   `apply_cps` helper and a tagged clause in `apply_n`, unused for now; the
   empty-prefix identity reframe; the handler-state fix above.
2. **Flag:** an environment variable hashed into the stdlib cache key; run the
   matrix under both settings.
3. **Flip behind the flag, all at once:** every creation site; one unknown-call
   path replacing the value arm of `lower_runtime_cps_apply` and
   `lower_generic_apply`; head classification from types; expected types
   forced off so the adapters go inert; `spawn` and `catch_panic`; the
   higher-order gate; the overlay rewrite.
4. **Burn down** the matrix and the behavioural tests under the flag, then
   update the textual assertions.
5. **A5:** delete the planner, adapters, parameter ABI metadata and the
   eta-reduced "value closure" branch.

Riskiest spots: the effect-operation callback overlay and applied-tag
relabelling; the higher-order gate disagreeing with closure creation;
dictionary slots and hoisted entry points sharing one body; variable call
classification being name-scoped.

## Appendix A: reproductions

All fail on `87e68150`. Shared declarations:

```saga
effect Skip { fun skip : Unit -> Int }

fun add : Int -> Int -> Int
add a b = a + b

fun ident : a -> a
ident x = x

fun apply_gen : (a -> b) -> a -> b
apply_gen f x = f x
```

**A1. `case` arms with different conventions.** Runtime: called with 1
argument, expects 3.

```saga
fun choose : Int -> (Unit -> Int needs {Skip})
choose n = case n {
  0 -> fun () -> 1
  _ -> fun () -> skip! ()
}

main () = {
  let f = choose 1
  dbg (f () with { skip () = resume 10 })
}
```

**A2. Function through a polymorphic function.** Runtime: called with 1
argument, expects 2.

```saga
main () = dbg ((apply_gen add 1) 2)
```

**A3. Partial application of a call result, bound with `let`.** Runtime: same
as A2. The inline form `((ident add) 3) 4` works.

```saga
main () = {
  let h = (ident add) 3
  dbg (h 4)
}
```

**A4. Effectful function through a polymorphic function.** Runtime: called
with 1 argument, expects 4.

```saga
fun eadd : Int -> Int -> Int needs {Skip}
eadd a b = a + b + skip! ()

main () = {
  let e = apply_gen eadd 1
  dbg (e 2 with { skip () = resume 100 })
}
```

**A5. Effectful lambda in a polymorphic position.** Compiler panic: no
evidence in scope for op.

```saga
main () = {
  let e = ident (fun x -> x + skip! ())
  dbg (e 5 with { skip () = resume 100 })
}
```

**A6. Effectful functions accepted as pure, in a list.** Should be a type
error. Runtime: called with 1 argument, expects 3.

```saga
fun sum_pure : List (Unit -> Int) -> Int
sum_pure fs = case fs {
  [] -> 0
  f :: rest -> f () + sum_pure rest
}

fun effs : Unit -> List (Unit -> Int needs {Skip})
effs () = [fun () -> skip! (), fun () -> 2]

main () = dbg (sum_pure (effs ()))
```

**A7. Pure functions accepted as effectful, in a list.** Runtime: called with
3 arguments, expects 1.

```saga
fun run_all : List (Unit -> Int needs {Skip}) -> Int needs {Skip}
run_all fs = case fs {
  [] -> 0
  f :: rest -> f () + run_all rest
}

fun pures : Unit -> List (Unit -> Int)
pures () = [fun () -> 1, fun () -> 2]

main () = dbg (run_all (pures ()) with { skip () = resume 100 })
```

**A8. Row variable instantiated to empty, in a list.** Runtime: same as A7.
Uses `pures` from A7.

```saga
fun run_each : List (Unit -> Int needs {..e}) -> Int needs {..e}
run_each fs = case fs {
  [] -> 0
  f :: rest -> f () + run_each rest
}

main () = dbg (run_each (pures ()))
```

**A9. Partially applied open-row trait method.** Runtime: called with 1
argument, expects 4.

```saga
trait Runner a {
  fun go : a -> Int -> Int needs {..e}
}

type Q = Q

impl Runner for Q needs {Skip} {
  go _ n = n + skip! ()
}

fun use_it : a -> Int needs {..a} where {a: Runner}
use_it x = {
  let f = go x
  f 10
}

main () = dbg (use_it Q with { skip () = resume 100 })
```

**A10. Invalid generated code.** `erlc` fails: duplicate variable `_Arg0` in
`mk/4`.

```saga
fun mk : Unit -> (Unit -> Int needs {Skip})
mk () = fun () -> skip! ()

main () = {
  let f = mk ()
  dbg (f () with { skip () = resume 1 })
}
```

**A11. Effectful function accepted as pure, in an `if` branch.** Should be a
type error. Runtime: called with 1 argument, expects 3.

```saga
fun eff : Unit -> Int needs {Skip}
eff () = skip! ()

fun get : Bool -> (Unit -> Int)
get b = if b then eff else (fun () -> 1)

main () = dbg ((get True) ())
```

**A12. Effectful function accepted as pure, in a record field.** Should be a
type error. Runtime: same as A11. Uses `eff` from A11.

```saga
record Box { run : Unit -> Int }

main () = {
  let b = Box { run: eff }
  dbg (b.run ())
}
```
