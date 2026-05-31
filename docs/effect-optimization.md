# Effect Optimization

The effect optimizer runs after monadic translation and before Core Erlang
lowering. It is intentionally optional: the unoptimized uniform CPS path is the
correctness oracle, and every rewrite must be able to skip safely.

This document describes the stable optimizer shape. Planning notes and milestone
history live under `docs/planning/uniform-effect-translation/`.

## Position In The Pipeline

```text
Monadic IR
  -> effect_opt
  -> Core Erlang lowering
```

The optimizer rewrites `MExpr` and may add generated private function bindings.
It does not change Saga source semantics, public APIs, or handler evidence
layout.

Important files:

- `src/codegen/monadic/effect_opt/mod.rs` - optimizer implementation.
- `src/codegen/monadic/effect_opt/tests.rs` - optimizer-focused unit tests.
- `src/codegen/monadic/handler_analysis.rs` - arm classification.
- `src/codegen/monadic/stats.rs` - before/after statistics.

## Local Simplification

The local simplifier runs to a fixpoint.

`Bind(Pure(a), x, body)` beta-reduces to `body[x := a]` using
capture-avoiding atom substitution.

Recursively pure bind values can be promoted:

```text
Bind(value, x, body) -> Let(value, x, body)
```

The purity predicate is deliberately conservative. Arbitrary `App` and
`ForeignCall` are not pure just because their Saga effect row is empty. The
current exception is compiler-generated dictionary constructor calls through
`Atom::DictRef`, which are pure materialization.

Dead pure lets are removed when the bound variable is unused.

## Handler Stack Model

Many rewrites depend on knowing which handler is lexically innermost for an
effect. The optimizer maintains a stack while walking an expression.

Frames are classified as:

- `Static` - source arms are available and may be inlined.
- `Native` - compiler-known BEAM-native handlers may direct-call foreign code.
- `Blocking` - dynamic or composite handlers block scanning outward for the
  effects they handle.

Lambda bodies and local function bodies reset the stack. A handler installed
outside a closure is not assumed to be active when the closure is eventually
called.

## Static Direct-Call

For a statically handled operation, a `Yield` can be replaced by the matching
handler arm body when all of these are true:

- the innermost matching handler frame is static;
- exactly one arm matches the effect and operation;
- handler analysis classifies the arm as tail-resumptive;
- the arm's parameter patterns are supported by the rewrite;
- the arm has no unsupported cleanup/finally requirement.

The rewrite substitutes operation arguments into the cloned arm body and turns
tail `resume v` into `Pure(v)`. Multishot, oneshot, value-producing resume,
dynamic handlers, composite handlers, and ambiguous arm dispatch stay on the
slow path.

Cleanup-preserving direct-call exists for conservative `finally`/`Ensure` cases
where cleanup variables are available at the perform site.

## Native Direct-Call

Native handlers model BEAM-specific effects such as actors, process operations,
timers, monitor/link operations, refs, and vec operations. The slow path calls
their op closures through evidence like any other handler.

When the handler stack proves a native handler is the innermost handler for an
operation, the optimizer can replace the `Yield` with a direct `ForeignCall` or
backend-specific IR form. This removes evidence lookup, op closure allocation,
and continuation plumbing on common BEAM-native hot paths.

Native specialization is intentionally per-operation. Native handlers with
stateful or callback-heavy behavior only get direct-call rules after the exact
boundary behavior is understood.

## Function Variants

Some yields are hidden behind helper calls. The optimizer can clone small
functions under a known handler stack and optimize the clone.

Implemented variant shapes:

- same-module helper inlining for small single-clause helpers;
- same-module native function variants;
- same-module static handler variants when specialization removes all residual
  yields from the generated body;
- caller-local cross-module variants for imported public Saga functions under
  native or fully-erasing static handler stacks.

Generated variants are private to the caller module. Cross-module variants do
not change the callee module's exports or package cache behavior. Imported
`@external` wrappers, private-helper dependencies, dynamic/composite
specialization, and ambiguous closure/local-function shapes are skipped in the
current implementation.

The optimizer can remove private source functions once entry-reachable calls are
fully covered by generated variants. Public functions are retained.

## Accepted Slow Paths

These are correct and may remain slower until measurements justify a specific
rewrite:

- dynamic handler values and conditional handler selection;
- composite handlers;
- multishot and oneshot resumptions;
- value-producing resume patterns;
- nontrivial handler parameter patterns;
- handler cleanup that cannot be moved to the perform site;
- native operations whose backend behavior needs a bespoke rule;
- cross-module effectful calls outside the current caller-local variant scope.

## Measurement

Use:

```bash
cargo run --bin saga -- inspect file.saga --stage monadic-stats
```

The report compares pre- and post-optimization monadic IR, including
entry-reachable counts, generated declaration counts, residual `Yield`s by
effect operation, and direct `ForeignCall` targets.

The standard sweep script is:

```bash
bash scripts/optimizer_sweep.sh stats
bash scripts/optimizer_sweep.sh bench 3
```

Benchmark mode is a wall-clock smoke check, not a rigorous microbenchmark. It
is mainly useful for catching large regressions and validating broad optimizer
direction on the same machine.
