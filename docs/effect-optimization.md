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
current exception is compiler-generated dictionary constructor calls through a
recognized local or imported dictionary constructor head, which are pure
materialization.

ANF scaffolding does not make a computation impure by itself: `Bind`/`Let`
expressions whose value and body are both pure are treated as pure. This matters
for derived-code paths where a pure representation conversion is emitted as a
short chain of `Bind(Pure(...))` nodes before feeding an effectful dictionary
method.

Dictionary-method helper inlining supports simple binder parameters directly.
For constructor and tuple parameters it wraps the inlined body in a one-arm
`case` around the call argument. This preserves the match while letting derived
representation dictionaries inline through shapes such as
`Rep__User -> Adt -> Variant -> Leaf`.

Dead pure lets are removed when the bound variable is unused.

Cases whose scrutinee is a closed constructor, tuple, or literal can collapse to
the first matching unguarded arm. The rewrite currently supports only simple
patterns used by optimized derived code: variables, wildcards, literals,
constructors, and tuples.

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

Let-bound handler values can be specialized before this rewrite runs. When the
optimizer sees a handler value or a small handler factory result bound to a
local and a later `with h` uses that same binding, it can replace the dynamic
handler with a static handler under the binding's lexical scope. This lets
factory patterns such as `let h = json_opts config; body with h` reuse the
ordinary static direct-call and function-variant machinery. The rewrite is
scoped and shadowing-aware; if another binding with the same name appears before
the `with`, specialization stops there.

Handler factories may include a small prefix of `let`/`bind` computations before
the returned handler value. The optimizer splices that prefix before the
handler binding, so configuration such as `let opts = f default_options` is
computed once at handler construction time instead of being duplicated inside
each optimized operation arm. Factories that do not end in a handler value stay
on the slow path.

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

Before generating a variant, the optimizer asks a conservative effect summary
whether the candidate body contains work that can be erased under the current
handler stack. This summary can look through small known same-module and
imported callees, so a wrapper whose body only calls another helper can still
get a useful generated variant. This is deliberately only a gate for existing
rewrites: it does not invent new semantics, and the optimized clone must still
fall back safely if residual yields remain.

Implemented variant shapes:

- same-module helper inlining for small single-clause helpers;
- same-module native function variants;
- same-module static handler variants when specialization removes all residual
  yields from the generated body;
- caller-local cross-module variants for imported public Saga functions under
  native or fully-erasing static handler stacks;
- let-bound handler factory specialization for small same-module factories that
  end in a `HandlerValue`, including simple configuration prefixes;
- imported public handler factory specialization for the same let-bound shape,
  including public pure values from the factory module such as default option
  records;
- conservative same-module trait method specialization for nullary dictionary
  constructors: when a generated static variant constructs a known zero-arg
  dictionary, extracts a method with `DictMethodAccess`, and applies that
  method under a known handler stack, the optimizer may inline the method lambda
  if doing so exposes an existing direct-call opportunity;
- dictionary-keyed generated variants for the same nullary dictionaries passed
  as arguments to generic functions. The generated variant substitutes the
  known dictionary tuple into its cloned body.
- conservative parameterized dictionary specialization when every constructor
  dictionary argument is already known. This lets wrappers such as
  `__dict_Encodable_Box(__dict_Encodable_Int)` inline the outer method and then
  continue through the inner method dispatch under the same handler stack.
- conservative imported dictionary constructor specialization. Imported
  constructor method bodies are available to caller-local variants when the
  constructor is structurally small and has supported lambda methods. If an
  imported method calls a small private same-module helper, that helper is
  cloned into the caller as a generated private helper instead of emitted as an
  invalid remote call to an unexported function. Helper collection is a
  conservative dependency fixpoint; ambiguous or unsupported private helper
  graphs still make the constructor ineligible.
- value-keyed generated variants for closed constructor arguments. When a call
  such as `worker (Login 5)` is optimized under a known handler stack, the
  generated variant can record the constructor value in its specialization key
  and substitute it into the cloned body. The same rewrite also looks through
  ANF-style let-bound pure constructor values, so `let x = Login 5; worker x`
  specializes like the direct call. A small case-on-known-constructor rewrite
  then collapses derived `Generic` representation branches before dictionary
  method inlining checks their size budget. This is deliberately limited to
  closed constructor-shaped values, not arbitrary literals.
- generated-variant dictionary-argument pruning. When a known dictionary
  argument becomes unused after specialization, the generated variant drops
  that parameter and the rewritten call site drops the constructor argument.

Generated variants are private to the caller module. Cross-module variants do
not change the callee module's exports or package cache behavior. Imported
`@external` wrappers, private-helper dependencies, dynamic/composite
specialization, and ambiguous closure/local-function shapes are still skipped
outside the imported dictionary-helper clone path.

Static handler stacks are keyed by the installed arm bodies, not just source arm
ids. This matters for recovered handler factories: two `with` blocks can come
from the same factory arm id while carrying different specialized handler
bodies, and they must not share a generated variant.

Trait method specialization is deliberately narrow. It handles local dictionary
constructors when their dictionary arguments are already known, which covers
concrete monomorphic impls, generic wrappers called with a concrete dictionary,
simple parameterized impls, and let-bound handler factories once they are
recovered into static handlers. It also handles the same imported public
dictionary constructors when they pass the conservative safety checks. Unknown
or dynamic dictionary values remain slow paths.

The let-bound handler factory case composes two separate rewrites: first the
handler value or small factory result is recovered as a static handler, then the
ordinary generated-variant and dictionary-method passes run under that recovered
handler stack. There is no separate trait-specific handler-factory rule. For
imported factories, the caller optimizer also merges imported handler-arm
analysis so tail-resumptive arms can participate in direct-call rewriting.

Generated variants preserve the source ABI except for known dictionary
parameters that are proven unused after specialization. Only generated variants
are rewritten this way; source functions and public APIs keep their original
shape.

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

For normal build flows, pass `--monadic-stats` to print a compact summary while
compiling:

```bash
cargo run --bin saga -- build file.saga --monadic-stats
cargo run --bin saga -- run file.saga --monadic-stats
cargo run --bin saga -- test --monadic-stats
```

Project builds also print a `whole-app entry-reachable` line rooted at
`Main.main`. Unlike per-module summaries, this follows static calls across
compiled project/library modules, so it is the preferred number when evaluating
library-heavy flows such as `Main -> Example -> SagaJson.Encode`. The graph is
still conservative: dynamic callback targets and runtime trait dispatch that
cannot be seen as a static declaration reference are not expanded.

This flag is backed by the general `CompileOptions` diagnostics struct, so it
can later grow into project-level compiler diagnostics without changing the
codegen API again.

The standard sweep script is:

```bash
bash scripts/optimizer_sweep.sh stats
bash scripts/optimizer_sweep.sh bench 3
```

Benchmark mode is a wall-clock smoke check, not a rigorous microbenchmark. It
is mainly useful for catching large regressions and validating broad optimizer
direction on the same machine.
