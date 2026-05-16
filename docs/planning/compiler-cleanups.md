# Compiler Cleanups

Five threads of accumulated complexity that, if pulled, would meaningfully
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

**The smell.** The original smell was two parallel sources of truth for
"is this var an effectful function value": lowerer-local mutable tracking
and the `call_effects::CallEffectMap` pre-pass. That has mostly been
resolved: the current lowerer no longer has a `current_effectful_vars`
field, and `call_effects.rs` owns the lexical scope walk for
effectful/open-row function values.

What remains is weaker but still worth cleaning up: the ownership is
implicit. Comments still reference the old mirror relationship, and some
shape decisions are split between the pre-pass and lowerer helpers. The
pre-pass is the single writer in practice, but the code does not make
that boundary as obvious as it should.

**Why it costs.** New call shapes are still easy to add in the wrong
place. A contributor can inspect the lowerer first, see several branches
that pattern-match on `CallEffectKind`, and assume call classification is
partly a lowering concern. That is how policy drift starts even after
the duplicate state has been deleted.

The other cost is that #5 depends on this boundary being crisp. Runtime
function shape should feed the pre-pass and lowerer from one shared
helper, but the pre-pass should remain the only phase that decides "this
specific `App` node is effectful and needs evidence."

**Shape of the fix.** Treat this as a small audit-and-contract cleanup,
not a major implementation task:

1. Search for stale references to lowerer-side effectful-var tracking
   (`current_effectful_vars`, "mirrors the lowerer", "inline check",
   etc.) and rewrite them to say `call_effects` is authoritative.
2. Add a short module-level invariant to `call_effects.rs`: every
   effectful function call through `App` must have exactly one
   `CallEffectInfo` entry before lowering; the lowerer may consume but
   not infer per-call effectfulness.
3. Keep lowerer helpers that pattern-match `CallEffectKind`, but make
   them extraction/translation helpers only. They should never inspect
   lexical scopes to decide whether a call is effectful.
4. Add a narrow debug assertion at lowerer effectful-call dispatch sites:
   when `expr_is_effectful_call(expr)` is true, lowering must find a
   corresponding effectful path (`resolved`, variable, lambda, dict
   method). Missing paths should be loud.
5. If any remaining lowerer-local classification is found during the
   audit, move it into the pre-pass before starting #5.

Current status: mostly done. The valuable output is documentation,
assertions, and deleting stale comments, plus any small drift discovered
while doing that audit.

Latest progress:

- `call_effects.rs` now documents the single-writer invariant at the
  module boundary.
- Stale lowerer-side `current_effectful_vars` comments have been removed
  from codegen.
- Lowering now debug-asserts if an `App` was classified as effectful by
  the pre-pass but no effectful dispatch path handles it.
- The `repro5` class of bug tightened the scope contract: a variable can
  have both pinned static effects and an open-row tail. The pre-pass must
  preserve both facts and classify the call as `RowForwarded { static_ops
  }`, not closed `StaticOps`.

**Watch for.**

- Do not move value-shape normalization into `call_effects`. The pre-pass
  classifies calls; the lowerer still owns emitting adapters and Core
  Erlang values.
- Pattern-bound variables, let-bound values, block-local `let fun`, and
  open-row-only callback params are the regression-sensitive scope cases.
  Keep focused tests around them.
- Intrinsics and inline vals should be classified as pure/non-call-effect
  by this pre-pass because builtin lowering intercepts them elsewhere.

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

## 5. Centralize runtime function-shape decisions

**The smell.** Several compiler phases independently answer adjacent
questions about function values:

- The typechecker says whether a function type is pure, closed-effectful,
  or open-row.
- `call_effects` classifies calls as `Pure`, `StaticOps`, or
  `RowForwarded`.
- The lowerer decides whether a function value should be emitted as a
  pure closure or CPS-shaped closure.
- Intrinsics and inline vals sit in the same resolution map as ordinary
  functions, but must be intercepted before normal call/value lowering.

These answers are closely related but were not originally represented by
one shared concept. Recent open-row callback work first added a lowerer-
local `CpsFunctionShape`, then this cleanup extracted that into
`src/codegen/runtime_shape.rs` as `CpsShape` /
`RuntimeFunctionShape`. That fixed real drift, but the larger point
remains: "runtime function shape" is now a compiler concept and should
keep becoming the source of truth where codegen crosses from types to
BEAM arities.

**Why it costs.** When the answers drift, the failure mode is usually a
runtime arity crash or evidence-layout mismatch, not a type error. The
same source type can be:

- accepted by the typechecker,
- classified one way by the pre-pass,
- emitted with a different runtime arity by `fun_info`,
- then invoked through yet another path by lowerer helpers or builtins.

The `repro3` family demonstrated both halves: open-row callback params
needed CPS calls, and values passed into those params needed CPS-shaped
normalization. `Std.Process.catch_panic` then showed a related intrinsic
edge: it has an open-row function type, but it is not an ordinary
resolved function call and must remain owned by builtin lowering.

**Shape of the fix.** Introduce a small shared representation for
runtime function shape, probably in a codegen utility module:

```rust
enum RuntimeFunctionShape {
    Pure,
    CpsClosed { static_effects: Vec<String> },
    CpsOpen { static_effects: Vec<String> },
    Intrinsic,
    InlineVal,
}
```

The exact enum may differ. A likely first version is:

```rust
struct CpsShape {
    static_effects: Vec<String>,
    is_open_row: bool,
}

enum RuntimeFunctionShape {
    Pure,
    Cps(CpsShape),
    Intrinsic,
    InlineVal,
}
```

The important part is that codegen has one helper that maps a resolved
type/symbol pair to the runtime shape.
Then:

- `fun_info` arity expansion uses it.
- `call_effects` maps it to `CallEffectKind`.
- `lower_expr_value_with_expected_type` uses it for value-boundary
  normalization.
- intrinsic/inline-val handling is explicit rather than discovered as a
  late special case.

This helper should be pure and boring: no lowering, no mutation, no Core
Erlang construction. Just "given the type and resolved symbol kind, what
runtime shape does this function value/call have?"

**Implementation plan.**

1. Done: add `src/codegen/runtime_shape.rs`.
2. Done: move the lowerer-only CPS shape into that shared module as
   `CpsShape`.
3. Done for the first useful surface: add constructors/helpers:
   - `RuntimeFunctionShape::from_type(ty, canonicalize_effect)`
   - `RuntimeFunctionShape::from_resolved_symbol(resolved, fallback_ty,
     canonicalize_effect)`
   - `expanded_arity(base_arity)` on the shape, returning
     `base_arity + 2` for CPS shapes and `base_arity` for pure/builtin
     value shapes.
4. In progress: replace the scattered `arity_and_effects_from_type` +
   `has_open_effect_row` + `expanded_arity_for_row` call sites in
   `init.rs`, block-local `let fun` lowering, and `call_effects::let_fun_sig`.
   Most type-backed paths now use `RuntimeFunctionShape::expanded_arity`;
   annotation/import fallback paths that only have an effect list still use
   the older helper.
5. Done: replace `Lowerer::cps_function_shape_from_type` with the shared
   helper. `lower_expr_value_with_expected_type` should still own
   adapter emission; it just asks the shared shape helper what runtime
   slot shape is expected.
6. Partly done: teach `call_effects` to translate `RuntimeFunctionShape` into
   `CallEffectKind` through one function:

   ```rust
   fn call_kind_from_shape(shape, ops) -> CallEffectKind
   ```

   Lambda classification, intrinsic/inline resolved heads, no-`FunSig`
   resolved heads, and local `let fun` signatures use the shared shape
   helper now. Some saturated resolved-name classification still has local
   branching around `FunSig` arity and should be collapsed carefully in a
   later pass.
7. Keep intrinsic and inline-val handling explicit in the shape enum.
   The pre-pass maps them to `Pure` call info because normal evidence
   threading does not own builtin interception.
8. After the mechanical replacement, delete `expanded_arity_for_row` if
   it becomes redundant. Leave `arity_and_effects_from_type` available
   for truly type-level queries, but remove comments that describe the
   old per-op arity convention.

**Suggested commit slices.**

1. Done: extract `CpsShape`/`RuntimeFunctionShape` and switch the lowerer
   value-boundary normalizer to use it.
2. Mostly done: switch arity expansion (`FunInfo`, imported exports,
   local `let fun`) to shape-driven expansion where full types are
   available.
3. In progress: switch `call_effects` classification to shape-driven
   translation.
4. Remaining: delete redundant helpers/comments and add focused tests if any branch
   was not already covered.

**Watch for.**

- Do not collapse call shape and value shape too aggressively. A partial
  application, a saturated call, and a function value all share the same
  underlying convention, but they need different lowering actions.
- Intrinsics are not ordinary functions even when their Saga type looks
  like one. The shape helper should make that explicit so builtin
  interception remains ahead of normal call lowering.
- This cleanup is easier after #1 because resolved types become
  reliable, and easier after #2 because the pre-pass becomes the only
  writer of call classifications. It can still be started earlier by
  extracting just the common "pure vs CPS closed vs CPS open" predicate.

Medium risk. It is mostly a refactor, but it touches the boundary where
static types become BEAM arities, so it deserves focused regression
coverage around open rows, partial application, intrinsics, and
function values stored in containers.

## Cross-cutting note

What ties these five together: each one is a place where a fact is
_computed in one part of the compiler and read by another in a form that
might be stale_. Type substitution (#1), effectful-var tracking (#2),
continuation/mode decisions (#3), constructor mangling and builtin
calling conventions (#4), runtime function shape (#5). The fix in every
case is the same shape — compute once, freeze, expose a single source of
truth.

That's worth keeping in mind when adding new state to the lowerer or
typechecker. The fifth one of these is already being written; the
fastest cleanup work is preventing it before it starts.
