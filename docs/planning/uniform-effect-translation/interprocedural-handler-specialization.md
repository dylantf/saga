# Interprocedural Handler Specialization

Status: **milestone 1 implemented**.

The monadic optimizer can currently direct-call only when the `Yield` is
lexically inside the handled body:

```saga
get! () with h
```

It cannot optimize through a function call boundary:

```saga
fun helper () needs {E} = op! ()

helper () with h
```

That is expected. The local handler stack belongs to the optimizer walk over
one expression tree. A callee body is optimized separately, with no knowledge
that a caller will install a static handler around the call.

## Why This Is Separate From Direct-Call

Direct-call is a local rewrite:

```text
With(static handler, ... Yield(E.op, args) ...)
```

Interprocedural specialization has to expose or clone callee bodies under the
caller handler stack before the local rewrite can fire. There are two possible
families:

1. **Inlining-specialization:** inline a known callee body at a call site, then
   let existing local rewrites run.
2. **Function-variant specialization:** generate a specialized version of a
   function for a known handler/evidence context.

Milestone 1 should use inlining-specialization only. Function variants are more
powerful, but they are also an ABI/code-size feature and need their own design.

## Milestone 1: Conservative Same-Module Inlining

Implemented in `src/codegen/monadic/effect_opt/mod.rs`.

Rewrite eligible direct calls under a non-empty handler stack:

```text
App(Var(f), args)
```

to a cloned callee body with params substituted. The existing optimizer
fixpoint then sees any newly exposed `Yield`s under the current handler stack
and may apply static/native direct-call.

Eligibility:

- callee is in the same `MProgram`;
- callee has exactly one clause;
- clause has no guard;
- callee is not recursive and is not mutually recursive;
- call is saturated;
- params are only supported first-milestone patterns:
  - `Pat::Var`,
  - `Pat::Wildcard`,
  - `Pat::Lit(Unit)`;
- substitution is capture-safe using the existing substitution helpers;
- body size is under a small fixed budget;
- callee body contains exactly one `Yield`;
- callee body does not contain `With`, `LetFun`, `HandlerValue`, `Receive`, or
  lambda bodies for the first milestone;
- after substitution, the inlined body must expose a direct-call opportunity
  under the current handler stack;
- do not inline inside lambda bodies unless that lambda body itself is being
  optimized from a call-site substitution.

Skip all cross-module calls, imported functions, dictionary methods,
constructors, partial applications, multi-clause functions, recursive functions,
and unknown heads.

## Correctness Notes

- This is ordinary beta-reduction at the function boundary. It must preserve
  the same call-by-value order the ANF/monadic IR already imposed.
- Inlining exposes callee `Yield`s to the caller's handler stack. That is the
  point, but it is also the risk: only inline bodies whose control structure is
  simple enough that the local optimizer remains the only semantic rewrite.
- The single-yield gate is deliberate. A helper such as `log! (); fail! "x"`
  might expose a direct-callable `Log` operation while leaving a new residual
  `Fail` at the call site. Milestone 1 skips that partial-consumption shape.
- The slow path remains the oracle. If any eligibility check is uncertain,
  skip.
- Return clauses and evidence routing should not be reimplemented here. The
  inliner should only clone IR; existing `With`, `Yield`, direct-call, and
  lowering logic keep their current responsibilities.

## Why Not Start With Function Variants?

Function variants would avoid code duplication at individual call sites, but
they require:

- naming and emitting specialized functions;
- deciding how specialized functions interact with module exports;
- preserving stack traces and generated Core readability;
- cache invalidation across modules;
- code-size controls;
- a strategy for dynamic handler values.

That is too much for the first milestone. Local inlining gives us a smaller
proof of value and lets `monadic-stats` show whether many residual `Yield`s
come from simple helper boundaries.

## Suggested Tests

- Same-module single-clause single-yield helper:
  `helper () = op! (); helper () with h` loses the `Yield`.
- Multi-clause helper does not inline.
- Recursive helper does not inline.
- Cross-module helper does not inline.
- Handler inside callee remains semantically local.
- Inlining under a dynamic same-effect blocker does not reach an outer static
  handler.
- Multi-yield helper does not inline, even if one yield would direct-call.
- Body-size budget prevents large helper inlining.

## Open Follow-Up

If same-module inlining produces useful stats, design function-variant
specialization as a separate stage. A quick native-variant prototype showed the
main design wrinkle: redirecting a call to a specialized sibling improves that
call path, but whole-program structural stats get worse unless the original
function is proven dead or the stats report reachability-aware counts. Do not
land function variants until the design includes:

- a code-size policy;
- a reachability/export policy for keeping or dropping original functions;
- stats that can separate generated variants from source declarations, or count
  only reachable entry-point paths;
- a naming/debuggability story for generated functions.
