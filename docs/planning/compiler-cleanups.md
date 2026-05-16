# Compiler Cleanups

Four threads of accumulated complexity that, if pulled, would meaningfully
reduce the surface area of the compiler without changing semantics. None of
these are urgent — the compiler works. They're worth doing when bandwidth
allows, in roughly the order listed, because each makes the next easier.

This is a strategic sketch, not an implementation plan. Each section
describes the smell, why it costs, the rough shape of the fix, and what to
watch for.

## 1. Apply substitution at typecheck finalization

**The smell.** `type_at_node` and `type_at_span` (in
[src/typechecker/mod.rs](../../src/typechecker/mod.rs)) store raw types as
recorded during inference. Many of those types contain unresolved type
variables. Consumers — codegen, LSP, the call-effects pre-pass — have to
remember to apply `sub.apply()` before reading. Forget, and you read a
`Type::Var(_)` that carries no useful information.

**Why it costs.** This footgun has bitten at least twice in recent work:
once in `call_effects::pattern_effects` (where a pattern-bound
function-typed variable's effects came back empty because the recorded
type was still a fresh var), and once in the let-binding lambda codegen
path (same root cause, different consumer). The reason it's intermittent:
the typechecker's Constructor-pattern binding records `param_ty` _before_
unifying the scrutinee, so even consumers that diligently apply sub on
read can get the wrong thing if they read the type before unification
completes.

`CheckResult` already exposes `resolved_type_for_node` which applies sub
on read, but plenty of code reads `type_at_span` / `type_at_node`
directly. Both paths exist; the difference is "did the consumer remember
to call the resolving variant?"

**Shape of the fix.** At `CheckResult::to_result()` boundary, walk both
maps and apply the substitution once, then freeze. Make the raw fields
private to the `Checker`; expose only resolved types via `CheckResult`.
The resolving helpers become identity reads.

**Watch for.**

- LSP intentionally displays "free type variable" names (`a`, `b`, ...)
  for unresolved polymorphic types. The `prettify` pass does
  `sub.apply()` + a rename. Make sure rename still happens for display;
  finalize-time apply just changes when, not whether.
- The Constructor-pattern bind ordering is a separate bug — it records
  `param_ty` before scrutinee unification. Apply-at-finalize masks the
  symptom (by then unification is done), but it's still fragile that the
  recording happens at the wrong moment. Worth either reordering the
  bind to unify-then-bind, or documenting the dependency on finalize
  ordering explicitly.
- Cheap to do; one walk at finalize, types are small, substitutions are
  shallow after generalization.

Standalone. Low risk. Good first step because it shrinks the gotcha
surface every subsequent cleanup has to dodge.

## 2. Finish Phase 4 of effectful-call detection

**The smell.** Two parallel sources of truth for "is this var an effectful
function value": `current_effectful_vars` (mutated by the lowerer as it
walks) and the `call_effects::CallEffectMap` (populated by the pre-pass
ahead of lowering). The plan in
[plans/effectful-call-detection-plan.md](plans/effectful-call-detection-plan.md)
explicitly calls for the pre-pass to be the only writer. Phase 4 landed
the pre-pass and the parallel-check assertions, but the inline mutations
in the lowerer never got deleted.

**Why it costs.** Every bug in this area requires checking both. Did the
pre-pass tag this var? Did the lowerer's mutable state also tag it? Do
they agree? When they disagree, you can't trust either until you've
traced the divergence. The parallel-check assertions catch _some_ of
these mid-build, but only for shapes that exercise both paths in tests.

The other cost is policy drift. New call shapes get added to the
pre-pass without being added to the lowerer's inline tracking, or vice
versa. The two diverge over time even if neither is broken in isolation.

**Shape of the fix.** Audit the lowerer for every mutation of
`current_effectful_vars` (chiefly the `Stmt::Let` paths and any branch-
local tracking). Move that logic into the pre-pass scope walk. Delete the
field. The lowerer becomes a pure consumer of `call_effects`.

**Watch for.**

- Some of the inline mutations are subtle — they happen inside branch
  lowering, case arm walks, or as side effects of resolving handler
  bindings. The pre-pass already has its own scope stack but doesn't
  necessarily mirror every walk the lowerer does. Some logic may need
  to be taught to the pre-pass that the lowerer currently learns by
  accident.
- This is a precondition for the next two cleanups working cleanly.
  Helpers that want to ask "is this argument an effectful call?" should
  consult the map, not reach into lowerer mutable state. As long as the
  inline path exists, those helpers stay ambiguous.

Independent of #1, but easier after it — the pre-pass and lowerer agree
on more when types are fully resolved.

## 3. Collapse the lowering-mode surface

**The smell.** Roughly eight overlapping entry points for "lower this
expression": `lower_expr_value`, `lower_expr_tail`,
`lower_expr_with_call_return_k`, `lower_expr_with_installed_return_k`,
`lower_terminal_effectful_expr_with_return_k`, `lower_block_with_k`,
`lower_block_with_return_k`, `lower_handler_owned_expr`. They overlap
heavily in implementation and differ subtly in continuation threading.

A `LowerMode { Value, Tail(K) }` enum exists at
[mod.rs:109](../../src/codegen/lower/mod.rs#L109) but only two
dispatchers consult it; the rest encode the mode in the function name.

**Why it costs.** Adding a new call shape or continuation pattern means
deciding which of the eight to call, which feels arbitrary because the
distinctions are not orthogonal — some are about return-continuation
handling, some about whether the expression is in terminal position,
some about whether handlers are owned by the enclosing context. New
contributors learn this by reading the existing call sites and
pattern-matching, which propagates whatever inconsistency was already
there.

**Shape of the fix.** Decide which way to go on `LowerMode`. Two
reasonable choices:

- _Commit to it._ Extend the enum to cover the cases the helper names
  currently encode (`TerminalEffectful(K)`, `HandlerOwned`, etc.). Every
  current entry point becomes a thin wrapper that constructs a mode and
  calls one dispatcher. The dispatcher inspects the mode to thread the
  right continuation.
- _Delete it._ Pick a small set of named entry points that cleanly
  partition the space and consolidate the rest as call-site renames.

The point isn't which of the two — it's that the current state
(half-committed) is the worst of both. Don't pick this up until you're
ready to do one or the other.

**Watch for.**

- Some of the helpers exist because the ambient context saved across
  recursion differs (`current_evidence`, `lambda_effect_context`,
  `return_k`). The mode probably needs to encode the save/restore
  policy too, or there's a sibling enum for that. Easy to under-design
  this and end up with two enums that have to be set together.
- This is the most invasive of the four. It touches the entire
  `src/codegen/lower/` directory. Doable in pieces (migrate one helper
  at a time, preserving behavior), but worth committing to finishing.
- Once done, expect to find dead branches — the consolidation usually
  surfaces helpers that nothing calls.

Easier after #1 and #2 are done. Less context to thread, fewer parallel
state mutations to keep aligned.

## 4. Builtins through the lowerer's helpers, not raw Core Erlang

**The smell.** `lower_catch_panic`
([src/codegen/lower/builtins.rs:114](../../src/codegen/lower/builtins.rs#L114))
and friends hand-write Core Erlang for the calling convention to the
user-supplied thunk and the result tuple shape. They don't go through
the same helpers the rest of the lowerer uses for evidence threading or
constructor mangling.

**Why it costs.** Two concrete drift hazards:

- `catch_panic` applies the thunk as `apply Thunk(unit)` — pure-shape.
  Its declared type is `(f: Unit -> a needs {..e}) -> Result a String
needs {..e}`, so under any future design that compiles open-row
  callbacks in CPS shape (per `evidence-passing.md` semantics), the
  thunk arrives as `/3` and `catch_panic` calls it with `/1` →
  badarity. Today this happens to work because every thunk passed in
  practice resolves to the pure shape, but the bug is latent and
  invisible.
- The result tuple uses literal atoms `'ok'` / `'error'`. The Saga
  `Result` constructors happen to mangle to `'ok'` / `'err'` — close
  but not identical, and only because of how the mangling rule reads
  the source. If the constructor mangling logic ever changes, every
  builtin returning Result silently breaks.

The category includes anywhere a builtin manipulates a Saga value
without going through the lowerer's value-construction helpers.

**Shape of the fix.** Two extracted helpers:

- One for constructing Saga ADT values from inside a builtin. Consults
  the same constructor-mangling tables the rest of codegen uses. Used
  for the `Ok`/`Err` wrappers, `Some`/`None`, etc.
- One for invoking a user-supplied thunk with the current calling
  convention. Threads evidence and the return continuation properly,
  so when the convention shifts, builtins shift with it.

`lower_catch_panic` becomes "set up try/catch, call the thunk-invocation
helper, wrap the result with the constructor helper."

**Watch for.**

- BEAM-native effect families (Process, Actor, Ref, Timer, Monitor) hand-
  code Core Erlang on purpose because they're calling native
  operations, not Saga thunks. They should stay raw. The line is:
  _user-supplied function values invoked by the builtin_ go through the
  helper; _operations the builtin performs itself_ stay native.
- Once these helpers exist, they're attractive nuisances —
  contributors will want to use them for anything that looks similar.
  Worth being explicit in their docs about what they're for and what
  they aren't.
- `catch_panic` specifically is on the critical path for the test
  framework (`Std.Test:run_single` calls it for every test). Whatever
  change lands here gets exercised immediately by the e2e suite —
  good regression coverage built in.

Easiest of the four. Best done after #2 (so the helper can ask the
pre-pass map about callee shapes) and ideally after #3 (so the helper
uses the consolidated lowering surface), but doable independently if
that ordering doesn't fit.

## Cross-cutting note

What ties these four together: each one is a place where a fact is
_computed in one part of the compiler and read by another in a form that
might be stale_. Type substitution (#1), effectful-var tracking (#2),
continuation/mode decisions (#3), constructor mangling and calling
conventions (#4). The fix in every case is the same shape — compute
once, freeze, expose a single source of truth.

That's worth keeping in mind when adding new state to the lowerer or
typechecker. The fifth one of these is already being written; the
fastest cleanup work is preventing it before it starts.
