# Direct-First Optimizer Matrix

Status: **draft worklist**.

This is the optimization checklist for the direct-first backend. It mines the
useful case coverage from the `selective-uniform` branch without importing that
branch's planner/lowerer stack.

The companion matrix,
[direct-first-effect-shape-matrix.md](./direct-first-effect-shape-matrix.md),
answers:

```text
What runtime shape is correct?
```

This matrix answers:

```text
When may the compiler choose a faster equivalent shape?
```

## Ground Rules

- Optimizer facts are optional. Missing facts must fall back to current
  direct-first lowering.
- The first optimizer product is metadata, not a rewritten second program.
- The lowerer remains the only Core Erlang emitter.
- Every optimization has a proof predicate, a fallback, and a fixture.
- Do not add generated function variants until direct effect-op specialization
  has landed and stayed boring.
- Missed optimization is slower. Wrong optimization is a compiler bug.

## Old Branch Mining Map

| Old Source | Useful Part | Current Use | Avoid |
| --- | --- | --- | --- |
| `docs/planning/selective-cps-value-matrix.md` | Case families for CPS values, callbacks, handler values, and dictionary methods | Convert into fixture coverage and guardrail rows | Do not copy selective runtime value planning wholesale |
| `docs/effect-optimization.md` | Optimizer proof vocabulary: static handler stack, tail-resume rewrite, function variants, dictionary specialization | Use as staged checklist | Do not copy monadic IR rewrite architecture |
| `src/codegen/handler_analysis.rs` | Conservative resumption analysis | Port as optimizer fact source | Do not depend on monadic IR |
| `src/codegen/lower_selective/cps_static_yield.rs` | Narrow proof for static tail-resume op direct-call | Port next as `DirectStaticTailResume` fact/consumer | Do not pull in `DirectLowerer` state |
| `src/codegen/lower_selective/cps_with.rs` | Static handler stack guard logic and elision checks | Mine selectively after direct op fast path | Do not import broad body-specialization recursion |
| `src/codegen/lower_selective/cps_static_calls.rs` | Generated static handler variants for helper calls | Later generated-variant phase | Do not start here |
| `src/codegen/lower_selective/known_facts.rs` and `known_values.rs` | Known local values, dict aliases, pure lambdas, simple field facts | Later fact tables for dict/generic work | Do not make lowering scope tracking a second interpreter |
| `src/codegen/lower_selective/imported_facts.rs` | Conservative cross-module admission policy | Later imported dict/helper specialization | Do not clone private helpers in the first optimizer slice |

## Pipeline Target

The intended phase order is:

```text
Elaborate
  -> Normalize
  -> Backend Resolve
  -> Classification
  -> Optimization Facts
  -> Lower
  -> Emit
```

`OptimizationFacts` should start narrow:

```rust
pub struct OptimizationFacts {
    pub handler_analysis: HandlerAnalysis,
    pub effect_ops: HashMap<NodeId, EffectOpOptimization>,
}

pub enum EffectOpOptimization {
    DirectStaticTailResume { /* proven arm/value facts */ },
}
```

The exact type names can change. The important constraint is that lowering asks
for a fact at the current operation site. It should not run a separate planner
over the program body.

## Stage 0: Fact Shell

Purpose: establish the optimizer phase without changing behavior.

| Case | Proof | Consumer | Fixture | Status |
| --- | --- | --- | --- | --- |
| Handler arm resumption classification | Syntactic tail-position walk; resume inside lambdas/non-tail positions is `Multishot` | Static tail-resume proof | Unit tests in `handler_analysis` | Done |
| Optimization fact bundle | Facts computed after backend resolve | Lowerer consumes handler analysis | Compile/check only | Done |
| Imported module fact storage | `CompiledModule` carries facts beside elaborated/resolved module | None yet | Project-mode smoke checks | Done |
| Debug trace for optimizer facts | Env-filtered source-order facts | Human audit | Any optimizer fixture | Todo |

Acceptance:

- No emitted Core change.
- `cargo test -p saga codegen::handler_analysis`.
- One single-file optimization fixture still checks.
- One project-mode optimization fixture still checks.

## Stage 1: Local Static Tail-Resume Effect Ops

Purpose: make Reader/config-style effects skip evidence lookup and handler
closure application when the matching handler arm is a simple static tail
resume.

Target shape:

```saga
{
  use_config ()
} with {
  get () = resume captured_config
}
```

| Case | Proof Required | Lowering Rule | Fixture | Status |
| --- | --- | --- | --- | --- |
| Inline handler, nullary op, captured value | Innermost matching inline arm is unique, `TailResumptive`, no `finally`, params match erased runtime arity | Lower op as the resumed value, then continue with current continuation | `static-tail-resume/01-inline-reader.saga` | Done |
| Inline handler, op args bound to simple vars | Same, plus params are vars/wildcard/unit only | Bind lowered op args, lower resumed value | `inline_static_tail_resume_effect_op_binds_runtime_args` | Done |
| Named static handler in same module | Named handler resolves to static arms; same arm proof | Same as inline | `selective-uniform/19-static-handler-with-cps-island.saga` | Todo |
| Multiple arms for same op | Proof rejects ambiguity | Evidence path | New guard fixture | Todo |
| Non-tail resume | `Multishot` from handler analysis | Evidence path | `static-tail-resume/02-non-tail-guard.saga` | Done |
| Abort/one-shot arm | `OneShot`, not `TailResumptive` | Evidence path | `21-static-handler-abort-arm.saga` | Todo |
| `finally` arm | `finally_block.is_some()` | Evidence path | `finally_tail_resume_stays_on_evidence_path` | Done |
| Dynamic or conditional handler | Handler is not statically known and unique | Evidence path | Existing dynamic handler fixtures | Todo |

First implementation constraints:

- No generated helper variants.
- No cross-module specialization.
- No handler factory recovery.
- No direct rewrite through arbitrary expressions with nested effects.
- No optimization if the direct arm value itself needs the same handler stack.

Acceptance:

- Emitted Core for the first reader fixture has no evidence lookup for the
  optimized op.
- The slow path remains for each guard fixture.
- saga_json EffectOpts benchmark improves or stays neutral.
- Pure/no-effect JSON stays neutral.

## Stage 2: Static Handler Fact Scope

Purpose: make Stage 1 work across the shapes users actually write while still
only optimizing operation sites.

| Case | Proof Required | Lowering Rule | Fixture | Status |
| --- | --- | --- | --- | --- |
| Nested handlers, inner shadows outer | Static handler stack knows innermost matching effect/op | Pick inner arm only | New fixture | Todo |
| Static handler inside direct outer code | Fact scope exists only while lowering handled body | Apply Stage 1 in body | `19-static-handler-with-cps-island.saga` | Todo |
| Handler return clause present | Return clause does not affect op directness unless continuation composition is needed | Initially reject | `20-static-handler-return-clause.saga` | Todo |
| Handler body contains pure lets before op use | Fact scope survives ordinary direct lets | Apply Stage 1 at op site | New reader/config fixture | Todo |
| Static handler for multiple effects | Only optimize the proven op; other ops stay normal | Mixed path | New fixture | Todo |

This stage should still not clone functions. If an op is hidden inside a helper
call, leave it alone for now.

## Stage 3: Let-Bound Handler Values And Fact Recovery

Purpose: recover static facts for common config-handler construction patterns
without making dynamic handlers globally special.

| Case | Proof Required | Strategy | Fixture | Status |
| --- | --- | --- | --- | --- |
| `let h = handler for E { ... }; body with h` | Binding dominates `with`, no shadowing, handler value is static | Treat `with h` as static for the body | New fixture | Todo |
| Simple handler factory returning handler value | Factory is same-module, small, single result shape, no dynamic branches | Recover handler arms under factory args | `trait-method-specialization/05-let-bound-handler-factory.saga` | Later |
| Factory with pure config prefix | Prefix can be evaluated once at binding site | Bind prefix once; recovered arms reference prefix values | Routed derive options fixtures | Later |
| Conditional handler value | Branches produce common runtime handler value | Keep dynamic path | Existing dynamic handler tests | Later |
| Cross-module public factory | Imported metadata admits factory safely | Recover facts in caller | Cross-module routed fixtures | Later |

Do not start this before Stage 1 has a trace and guard fixtures.

## Stage 4: Helper/Function Variants Under Static Handlers

Purpose: optimize effectful helper calls whose only escaping effects are
handled by the active static handler facts.

| Case | Proof Required | Strategy | Fixture | Status |
| --- | --- | --- | --- | --- |
| Same-module single-clause helper | Small body, direct params, effects covered by active static handler facts | Generate private variant or inline local body | `16-cps-helper-call-island.saga` | Later |
| If/case inside helper | All branches remain covered and supported | Generate variant | `17-cps-if-island.saga`, `18-cps-case-island.saga` | Later |
| Imported public helper | Imported body and metadata admitted safely | Generate caller-local variant | Imported static handler project | Later |
| Recursive or multi-clause helper | Termination/coverage not proven | Slow path | `multi-clause-project` | Later/guard |
| Helper leaves residual uncovered effect | Effect summary says not net-direct | Slow path | New guard | Later |

Generated variants are the first point where optimizer output may add
declarations. That needs a naming/cache policy and emitted-Core tests before
implementation.

## Stage 5: Higher-Order Callback Specialization

Purpose: avoid CPS adapters when a higher-order call can stay direct or
net-direct.

| Case | Proof Required | Strategy | Fixture | Status |
| --- | --- | --- | --- | --- |
| Pure callback passed to effect-capable HOF | Callback exposed type is direct; HOF body can call it directly under known shape | Direct HOF specialization | `30-higher-order-direct-callback.saga` | Later |
| Fully handled callback | Callback effects are handled below callback boundary | Treat as externally direct | `37-handled-callback-specialization.saga` | Later |
| Effectful callback expected by HOF | Callback remains leaky | Existing CPS adapter path | `31-higher-order-effectful-callback-unsupported.saga` | Guard |
| Imported direct callback helper | Imported function metadata proves direct shape | Direct specialization | imported direct callback project | Later |
| Handler-arm HOF resume | Resume used in callback under handler arm | Preserve continuation semantics; no broad rewrite initially | Add guard before optimizing | Later |

This stage should not precede basic static op specialization.

## Stage 6: Trait And Dictionary Specialization

Purpose: specialize known dictionary method calls only when concrete dictionary
facts are visible. Dictionary passing remains the correctness fallback.

| Case | Proof Required | Strategy | Fixture | Status |
| --- | --- | --- | --- | --- |
| Local nullary dict constructor + immediate method call | Known constructor, known method index, method lambda admitted | Lower method body/call directly | `trait-method-specialization/02-concrete-trait-method.saga` | Later |
| Generic wrapper with known dict arg | Dictionary parameter is statically known at call site | Substitute known dict into generated/private variant | `03-generic-wrapper.saga` | Later |
| Parameterized dict constructor | Every constructor dict arg is known | Inline outer method, then known sub-dict calls | `04-parameterized-dict.saga` | Later |
| Let-bound handler factory plus dict method | Stage 3 recovers handler; dict facts are known | Compose handler and dict facts | `05-let-bound-handler-factory.saga` | Later |
| Imported public dict constructor | Imported method body is small and safe; private helper policy satisfied | Caller-local specialization | cross-module dict fixtures | Later |
| Effectful impl method | Per-method effect shape is known | Direct/CPS according to method slot, not impl-level blanket | `34-effectful-trait-method.saga` | Later |
| Dynamic dictionary | Concrete constructor unknown | Normal tuple/method dispatch | Existing fallback | Always |

Open design question: effects probably need to become a per-method trait
contract for this stage to stay simple. Impl-level `needs` is not enough as an
optimization boundary because pure sibling methods should remain direct.

## Stage 7: Generic/Output-Shape Specialization

Purpose: use Generic-derived structure as compile-time evidence so hot codecs
do not walk intermediate representation trees at runtime.

| Case | Proof Required | Strategy | Fixture | Status |
| --- | --- | --- | --- | --- |
| Pure derived representation chain | Known constructors/fields collapse through Generic dictionary calls | Inline and fold representation construction | `routed-derive-options` fixtures | Later |
| `ToJson` record with known fields | Record shape, field serializers, and options are known | Emit direct serializer shape | saga_json benchmark fixture | Later |
| Maybe/list fields | Element serializer facts known; container runtime helpers selected | Emit direct container calls | routed derive maybe/list fixtures | Later |
| Variant options | Tagging/options handler facts known | Emit direct variant serializer | routed derive variant fixture | Later |
| Unknown Generic dictionary | Shape not concrete | Normal Generic/dict path | Existing fallback | Always |

This is deliberately after trait specialization. `Generic` should be the source
of structure facts, not a reason to monomorphize the whole program.

## Global Guardrails

- No optimization through `Multishot`.
- No optimization through `OneShot` unless a later stage explicitly proves abort
  semantics are preserved.
- No initial direct rewrite for `finally`.
- No direct rewrite through dynamic/composite handlers.
- No storage of CPS callable values in records/tuples/constructors without an
  explicit representation policy.
- No cross-module private helper cloning before the imported helper policy is
  written down and tested.
- No generated variants without a stable naming and reachability story.
- No benchmark interpretation without an emitted-Core shape check for the case
  being measured.

## Immediate Checklist

- [x] Seed optimizer fixtures from `selective-uniform`.
- [x] Add conservative handler-arm resumption analysis.
- [x] Add an `OptimizationFacts` shell after classification.
- [ ] Add optimizer-fact debug trace.
- [x] Add first reader/config fixture for inline static tail resume.
- [x] Add emitted-Core assertion that optimized op skips evidence lookup.
- [x] Add guard fixture proving non-tail resume stays on evidence path.
- [x] Add guard fixture proving `finally` stays on evidence path.
- [x] Add project-mode smoke check for the first optimized fixture.
- [ ] Benchmark saga_json EffectOpts after Stage 1.
