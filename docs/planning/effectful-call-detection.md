# Consolidate Effectful-Call Detection in the Lowerer

## Motivation

We keep finding the same bug shape in different sites in the lowerer: a
dispatcher checks "is this an effectful call?" via one syntactic predicate,
misses a form (qualified name, eta-expanded lambda, dict-elaborated call,
effectful variable), and falls through to value-mode lowering. When that
happens, an aborting handler's `{error, _}` (or equivalent) tuple silently
leaks out as a value and gets wrapped by an outer `return` clause — producing
either a runtime crash (`no matching clause`) or a garbage `Ok(error_tuple)`.

Recent examples:

- **Same-module nested CPS** — `f (g x)` where both are effectful: the inner
  call was lowered to a `let _v = inner(args, H, identity_k)` and `_v` was
  passed positionally to `outer`. When `inner` aborted, `_v` was the error
  tuple and `outer` crashed on it. Fixed by CPS-chaining argument-position
  effectful calls in [src/codegen/lower/mod.rs](../../src/codegen/lower/mod.rs).
- **Cross-module nested CPS** — `Lib.f (Lib.g b)` defined in `Main` and run
  via a higher-order `Lib.run`: the dispatcher only checked
  `collect_fun_call` (Var-headed), not `collect_qualified_call`
  (QualifiedName-headed). The body fell through to value-mode and `_ReturnK`
  wrapped the error tuple as `Ok`. Fixed by routing both call shapes through
  one predicate.
- **Declared-but-unused effects** (separate, still open): a function
  declares `needs {Fail}` but never calls a fail op. The CPS-expanded arity
  doesn't match what the caller threads, producing a `no matching clause`
  crash at runtime.

These are not unrelated edge cases. They are the same root mistake at
different sites: the lowerer asks "is this an effectful call?" with a
hand-rolled, locally-scoped check, and the checks have drifted apart.

## The duplication

Two layers of duplication compound the problem.

**Detection predicates** scattered across the lowerer:

| Predicate | Where | What it sees |
| --- | --- | --- |
| `collect_fun_call` + `is_effectful_call_name` | `exprs.rs` (multiple sites), `mod.rs` | Var-headed effectful calls only |
| `collect_qualified_call` | `mod.rs::lower_app_expr`, util | QualifiedName-headed calls (no effectfulness check inline) |
| `current_effectful_vars.contains_key` | `exprs.rs`, `mod.rs` | In-scope effectful variables |
| `has_nested_effect_call` | `util.rs` | Static syntactic walk, no resolution |
| `has_nested_effectful_expr` | `mod.rs` | Resolution-aware walk |
| `branch_is_effectful` | `mod.rs` | Combination of the above |
| `is_effectful_call_arg` | `mod.rs` (added during recent fixes) | Var **or** QualifiedName effectful call |

`is_effectful_call_arg` is the closest to a single source of truth. It was
introduced to fix the bugs above and now backs two dispatchers, but most
other sites still use the older narrower checks.

**Lowering modes** that each need to make the CPS-or-not decision
independently:

- `lower_expr_value` / `LowerMode::Value`
- `lower_expr_tail` / `LowerMode::Tail` / `lower_expr_tail_compat`
- `lower_expr_with_call_return_k`
- `lower_expr_with_installed_return_k`
- `lower_terminal_effectful_expr_with_return_k`
- `lower_terminal_effectful_expr_to_k`
- `lower_handler_owned_expr`
- The arg lowering inside `lower_resolved_fun_call` /
  `lower_effectful_var_call` (saturated branches)

Each entry in this list contains some variation of "if the body is an
effectful call, route through the CPS path; otherwise compute as value and
wrap." The shape of "is the body an effectful call?" is the part that has
been wrong in different ways at different sites.

## Goal

One source of truth for "should this expression be lowered in CPS form?",
queried uniformly by every dispatcher. Adding a new effectful call shape
(qualified, dict-elaborated, beam-native, etc.) should require updating one
predicate, not auditing every dispatcher.

## Plan

### 1. Lock down the canonical predicate

Promote `is_effectful_call_arg` to *the* predicate. Audit every other
detection site:

- `lower_terminal_effectful_expr_with_return_k` — already migrated.
- `lower_terminal_effectful_expr_to_k` — already migrated.
- `branch_is_effectful` / `has_nested_effectful_expr` — these wrap the
  predicate over sub-expressions; rewrite in terms of
  `is_effectful_call_arg` so the syntactic shapes covered match.
- `lower_let_value` and `Stmt::Let` lowering paths in [exprs.rs](../../src/codegen/lower/exprs.rs)
  (around lines 968 and 1203 — both currently use `collect_fun_call` only).
- Any remaining `collect_fun_call` + `is_effectful_call_name` pair across
  the lowerer.

Rename to something more precise. `is_effectful_call_arg` was named for its
first use site; the predicate is general. Suggested name:
`expr_is_effectful_call`.

### 2. Cover all call shapes the predicate must recognize

Run through these forms and confirm each is handled:

- `f x y` — Var head, resolved to local fun
- `Mod.f x y` — QualifiedName head, resolved cross-module
- `effectful_var x` — `let g = ...; g x` where `g` was bound to an effectful
  result
- Dict-elaborated trait method calls — these become regular function calls
  after elaboration; confirm the resolution map flags them when the
  underlying impl is effectful
- `f` (zero-arg-ish — note saga has no zero-arg calls, but partial
  applications saturated by the CPS expansion need handling)
- Eta-reduced effectful lambdas — the lowerer has special handling
  (`lower_eta_reduced_effect_expr`); make sure the predicate sees them too
- Lambda calls: `(fun x -> ...) y` — the head isn't a name; current code
  routes through `lower_generic_apply`. Decide whether this can be
  effectful (yes, if the lambda body uses an in-scope handler param) and
  cover it.

For each shape, write a regression test along the lines of
`cross_module_nested_effectful_calls_abort_correctly` in
[tests/module_codegen_integration.rs](../../tests/module_codegen_integration.rs).
The test must actually run on BEAM — typecheck + erlc-compile is not
sufficient, the bugs only manifest at runtime.

### 3. Narrow the lowering-mode surface

Eight entry points each making the CPS-or-not decision is too many. After
step 1, look for opportunities to fold pairs together:

- `lower_terminal_effectful_expr_with_return_k` and `_to_k` differ only in
  whether the K is a `CExpr` or a variable name. They could share a body.
- `lower_expr_with_call_return_k` and `lower_expr_with_installed_return_k`
  overlap heavily; the difference is block-vs-non-block dispatch which
  could move into the caller.
- `LowerMode::Value` / `LowerMode::Tail` are vestigial — most code uses the
  explicit helpers directly. Decide whether to delete the enum or commit
  to it as the public surface.

This step is consolidation, not new behavior. It's worth doing only after
step 1 is in place; otherwise the consolidation will cement whatever
predicate inconsistency was present.

### 4. Property test

The strongest invariant the recent bugs violated: **for any expression
typed under a handler that aborts, no abort can produce an `Ok`-shaped
(or equivalently, return-clause-wrapped) value at the with-boundary.**

A small generative test would have caught both A and C. Shape:

- Generate small expressions composed of two-or-three effectful function
  calls with a known-failing inner.
- Lower, compile, run on BEAM.
- Assert the result pattern-matches as `Err _`, never `Ok _`.

This belongs as a unit-style harness in [tests/](../../tests/) rather than
the e2e suite, so failures point at lowering rather than the test runner.

### 5. (Stretch) annotate effectfulness on the AST

After elaboration but before lowering, walk the program once and tag each
call expression with whether it lowers as CPS. The lowerer reads the tag
instead of re-deciding from syntactic shape. This converts the consistency
guarantee from "every dispatcher uses the same predicate" (audit-based) to
"there is one tag, one writer" (structural).

This is the largest change in the plan and probably belongs after the
others land.

## Risks

- **Performance**: `expr_is_effectful_call` walks resolution maps. Some
  current call sites avoid it on hot paths via the cheap syntactic check.
  Profile before assuming the consolidation is free.
- **Test coverage**: the failures are runtime-only. A green `cargo test`
  doesn't prove correctness — exercise BEAM execution.
- **Eta-reduced lambdas and dict-elaborated calls** are easy to miss in the
  audit because the AST shape after elaboration differs from the source.
  Walk the post-elaboration AST, not the parser output, when validating
  step 2.

## Acceptance

The refactor is done when:

- All effectful-call detection in the lowerer routes through one predicate.
- Each call shape in step 2 has a BEAM-executing regression test.
- The property test in step 4 runs in CI and passes.
- Adding a new call shape (e.g. a future BEAM-native form) requires
  updating exactly one predicate and gets test coverage automatically via
  the property test.
