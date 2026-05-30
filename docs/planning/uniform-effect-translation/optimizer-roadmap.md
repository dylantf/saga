# Optimizer Roadmap

Status: **active phase-2 scope control**.

The optimizer space is effectively infinite. This document bounds phase 2 so
the uniform effect translation can reach a useful stopping point instead of
turning into an open-ended compiler research project. Treat the slow uniform
path as the correctness oracle; every optimizer milestone must be optional and
must preserve the ability to fall back to the unoptimized path.

## Phase 2 Goal

Generate acceptable Core Erlang for the common Saga shapes while keeping the
optimizer small enough to review and maintain.

Phase 2 is not trying to optimize every possible handler shape. It should make
the new uniform path practical for normal code, document the remaining slow
paths, and leave future optimization work as explicit follow-up rather than
implicit debt.

## Current Completed Milestones

- [x] **Local simplification: bind collapse.**
  `Bind(Pure(a), x, body)` beta-reduces to `body[x := a]`.

- [x] **Local simplification: Bind to Let.**
  Recursively pure bind values lower as ordinary lets instead of CPS binds.

- [x] **Static tail-resumptive direct call.**
  Lexically handled static `Yield`s for tail-resumptive arms inline the arm
  body and rewrite tail `resume` to `Pure`.

- [x] **Cleanup-preserving static direct call.**
  The direct-call path handles conservative `finally`/`Ensure` cases where
  cleanup variables are available at the perform site.

- [x] **Native direct-call specialization.**
  Simple first-order BEAM-native actor/timer operations plus `beam_ref`
  `new`/`get`/`set` rewrite to direct `ForeignCall`s.

- [x] **Same-module helper inlining.**
  Small single-clause, single-yield helpers inline under a known handler stack
  to expose local direct-call opportunities.

- [x] **Same-module native function variants.**
  Calls under native handler stacks can redirect to generated same-module
  sibling functions optimized under that native stack.

- [x] **Measurement hook.**
  `saga inspect <file> --stage monadic-stats` reports whole-program and
  entry-reachable before/after counts, with per-op `Yield` and per-target
  `ForeignCall` breakdowns.

## Bounded Remaining Candidates

Only promote an item from this list when stats show it matters for common code
or when it removes visible compiler complexity.

- [ ] **Dead generated slow-path cleanup.**
  Remove original same-module functions when all entry-reachable calls route
  through generated variants and the original is not exported or otherwise
  referenced. This is code-size work, not required for correctness. Deferred
  until monadic IR or the optimizer has reliable export/visibility metadata:
  today `MFunBinding` visibility is recovered later by the lowerer from
  `ModuleCodegenInfo`, so deleting originals in the optimizer would be unsafe.

- [ ] **Static handler function variants for obvious cases.**
  Generate variants for same-module calls under static handlers only when the
  callee body is small, non-recursive, and all exposed operations are handled by
  single matching tail-resumptive arms. Skip dynamic/composite handlers,
  multishot/oneshot arms, return-clause ambiguity, and cleanup ambiguity.

- [x] **Native callback/thunk specialization.**
  Native ops that currently stay slow because they wrap callbacks, especially
  `spawn`, get targeted fast paths when actor-heavy stats justify it.

- [x] **Pure generated-let cleanup.**
  Remove dead let/bind temporaries introduced by direct native lowering when
  they are provably unused and side-effect-free.

- [ ] **Cross-module specialization.**
  Deferred until there is an export/cache story. Cross-module variants are a
  real compilation-model feature, not just another local rewrite.

## Known Slow Paths We Accept For Now

These should remain correct and may remain slower until a measurement sweep
proves otherwise:

- dynamic handler values and conditional handler selection;
- composite handlers;
- multishot and oneshot resumptions;
- value-producing resume patterns;
- handler arms with nontrivial parameter patterns;
- handler arms whose cleanup cannot be moved to the perform site;
- native handlers with backend-specific stateful implementations;
- cross-module effectful calls not exposed by same-module inlining/variants.

## Measurement Set

Use targeted examples instead of running the full example suite for every
optimizer change:

- `examples/25-state-effect.saga` — value-producing resume and state handler.
- `examples/29-actors.saga` — native actor handler and function variants.
- `examples/30-pingpong.saga` — actor send/receive across helper boundaries.
- `examples/32-monitor.saga` — native monitor op with backend atom argument.
- `examples/49-dynamic.saga` — dynamic handler values.
- `examples/54-choose-backtracking.saga` — multishot backtracking.
- `examples/55-nqueens-solver.saga` — larger multishot search.

For each candidate optimization, compare:

- whole-program stats, to monitor emitted code growth;
- `source decls` vs `generated decls`, to separate real source growth from
  optimizer-created variants;
- entry-reachable stats, to measure the hot path;
- residual `Yield ops`, to decide whether the next rewrite has a real target;
- new `ForeignCall` targets, to verify native direct-call movement.

Run the standard sweep with:

```bash
bash scripts/optimizer_sweep.sh stats
bash scripts/optimizer_sweep.sh bench 3
```

Benchmark mode defaults to `target/release/saga run --release`, so repeated
runs can use the script build cache and avoid recompiling each example after
the warm-up build. Set `SAGA_BIN=target/debug/saga SAGA_RUN_PROFILE=dev` for a
debug compiler smoke run. The benchmark mode is still a wall-clock smoke check
for cache lookup + BEAM startup/runtime, not a rigorous runtime microbenchmark,
but it is good enough to catch large regressions and to compare broad optimizer
direction on the same machine.

### Latest Snapshot

Last sampled after dead pure-let cleanup:

| Example | Entry-reachable result | Reading |
| --- | --- | --- |
| `25-state-effect` | `Yield 3 -> 3`; `Bind 16 -> 9` | Value-producing resume remains on the accepted slow path. |
| `29-actors` | `Yield 6 -> 0`; `ForeignCall 0 -> 6` | Native variants plus spawn thunk specialization remove all entry-reachable actor yields. |
| `30-pingpong` | `Yield 8 -> 0`; `ForeignCall 0 -> 8` | Same actor shape as `29`; all entry-reachable actor yields direct-call Erlang. |
| `32-monitor` | `Yield 4 -> 0`; `ForeignCall 0 -> 4` | Monitor/send/spawn native ops direct-call Erlang on the entry path. |
| `49-dynamic` | `Yield 0 -> 0`; `Bind 75 -> 27` | No residual monadic yield pressure; dynamic path is not the next optimization target. |
| `54-choose-backtracking` | `Yield 4 -> 4`; `Bind 35 -> 16` | Multishot/abort behavior remains intentionally slow. |
| `55-nqueens-solver` | `Yield 2 -> 2`; `Bind 48 -> 23` | Multishot/abort behavior remains intentionally slow. |

The actor-native hot path is now covered for these examples. The next optimizer
target should come from a fresh stats sweep rather than from extending function
variants by default.

The stats report now splits total declarations into `source decls` and
`generated decls`. This makes native variant growth visible as optimizer-created
code: for example, `29-actors` whole-program `decls 7 -> 9` is
`source decls 7 -> 7` plus `generated decls 0 -> 2`.

One-shot local timing smoke from `target/release/saga run --release` after
warming the per-example script cache:

| Example | Wall time |
| --- | ---: |
| `25-state-effect` | 1399ms |
| `29-actors` | 1457ms |
| `30-pingpong` | 1732ms |
| `32-monitor` | 1444ms |
| `49-dynamic` | 1461ms |
| `54-choose-backtracking` | 1401ms |
| `55-nqueens-solver` | 1531ms |

These timings are only comparable to future runs on the same machine with the
same build profile and cache state.

## Cleanup Cadence

After every two or three optimizer milestones:

- run the targeted stats set;
- run the normal behavioral tests;
- inspect `effect_opt/mod.rs` for duplicated protocol logic;
- promote obvious helper abstractions;
- update this roadmap with what is complete, deferred, or no longer worth doing.

Do not keep adding rewrites on top of unclear optimizer structure. If a new
rewrite needs more than one local helper and one local test cluster, pause for a
small design note first.

## Good Enough For Now

Phase 2 can stop when:

- all Rust, property, stdlib, e2e, and targeted example runs are green;
- common pure code loses most monadic scaffolding after optimization;
- common static tail-resumptive handlers avoid slow evidence `Yield` routing;
- common BEAM-native first-order operations direct-call Erlang/runtime targets;
- helper/function-boundary overhead is reduced for the actor and static-handler
  examples we care about;
- remaining residual yields are understood and listed as accepted slow paths or
  bounded follow-up items.

At that point, prefer old-path deletion and lowerer cleanup over speculative new
optimizer rewrites.
