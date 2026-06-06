# Selective-Uniform Postmortem

Status: archive note for the `selective-uniform` branch.

This branch was an attempt to recover the safety benefits of the failed
uniform-monadic CPS rewrite without paying the full "everything is CPS-shaped"
runtime cost. The intended design was:

```text
keep runtime metadata uniform
keep pure/direct code in direct BEAM shape
lower only effectful regions through CPS islands
use the old/raw path as a correctness fallback
specialize known dictionaries and handler shapes when proven
```

The experiment produced useful compiler knowledge, tests, and design artifacts,
but the branch should not be merged as the default backend in its current form.

## Why We Tried It

The `main` lowerer already does selective CPS by hand. Its recurring failure
mode was missing one of the places where an effectful value or call needed the
hidden evidence vector and continuation arguments. Those misses surfaced as
runtime arity errors, especially across module boundaries and trait/dictionary
calls.

The uniform-monadic rewrite fixed that class of bug by making everything
effect-shaped, but it imposed a large runtime tax and moved the hard work into a
large optimizer. The selective-uniform branch tried to keep the safety blanket
without making all pure code pay for it.

## What Worked

- The branch clarified the core invariant:
  runtime call shape must be explicit, not guessed from arity or spelling.
- The CPS value matrix is useful and should survive:
  `docs/planning/selective-cps-value-matrix.md`.
- The branch distinguished callable type shape from implementation lowering
  shape. A function can have an effect row in its type while its body is still
  directly lowerable under a particular handler/callback arrangement.
- `--selective-no-fallback` was useful as an audit mode.
- Cross-module shape metadata proved to be essential. Most bugs were imported
  function/value/dictionary bugs, not same-module bugs.
- The branch added many good repros and fixture tests for:
  CPS callable values, handler values, static handlers, actor/ref native
  handlers, imported HOFs, effectful trait methods, and known dictionary chains.
- Removing the old monadic optimizer from the execution path was the right
  move. The optimizer was not a correctness component and made the backend much
  harder to reason about.

## What Did Not Work

The final architecture had too many moving parts:

```text
ANF
-> monadic IR
-> selective planner
-> direct subset proof
-> CPS island proof
-> selective Core
-> raw fallback Core
-> merge
-> direct/uniform adapters
-> known dict facts
-> imported fact reconstruction
-> static handler variants
```

The result was better organized than the uniform rewrite, but still too large
and too easy to route through the wrong layer. The known-dict and Generic
specialization work started to recreate an optimizer/lowerer on top of an
already complex backend.

The fallback also made performance harder to reason about. A program could be
correct because fallback definitions remained available, while still being slow
because the hot path crossed an adapter, fallback dict constructor, dynamic
method tuple, or imported wrapper.

## Performance Evidence

The key comparison is the no-effect `saga_json` options-as-arguments path:

```text
main:              ~900 ms to serialize 100k records
selective-uniform: ~1442 ms to serialize 100k records
```

That case should not be paying effect CPS costs. It is the cleanest evidence
that the selective branch's direct path is still slower than `main`, even after
known-dict specialization work.

The effect-options path improved compared with the earlier uniform refactor:

```text
uniform/refactor era:       roughly 18 s
selective + optimizations:  roughly 10 s
```

But that is still unusable and still much slower than `main`'s direct/manual CPS
baseline. The improvement does not justify the amount of backend machinery.

## Known-Dict Specialization

The branch already implements the broad known-dict method specialization idea:

```text
known_dict_value_for_expr
try_lower_known_dict_immediate_method_sequence
try_lower_immediate_known_dict_method_bind
lower_known_dict_method_app
known_dict_aliases_for_params
active_known_dict_methods
```

So "add known-dict specialization" is not, by itself, an untested next step. We
tested a substantial version of it here, and the no-effect JSON benchmark was
still slower than `main`.

That suggests at least one of these is true:

- specialization is not reaching the actual hot path;
- specialization reaches the path but emits worse Core than `main`;
- cross-module fallback/adapters reintroduce dynamic dispatch;
- inlining duplicates too much Generic/helper structure;
- runtime dictionary dispatch on `main` is cheaper than the generated direct
  Core for this workload.

Any future trait/dict specialization should be measured against these exact
failure modes before growing.

## Recommendation

Do not merge this branch as the default backend.

Treat it as a research branch and quarry for ideas. The likely better path is:

```text
start from main
keep main's direct-first lowerer
port selective's shape discipline and tests
add small, measured optimizations
```

In particular, avoid porting the whole monadic IR + selective/fallback merge
architecture unless a later experiment proves that it can match `main` on the
no-effect JSON benchmark.

## Salvage List

Worth porting or preserving:

- `docs/planning/selective-cps-value-matrix.md`
- the strict audit mindset behind `--selective-no-fallback`
- runtime shape classification:
  `Pure`, `Cps`, `Intrinsic`, `InlineVal`
- explicit ABI helpers/assertions for direct calls, CPS calls, direct function
  values, and CPS function values
- imported function/value/callback/dict shape metadata
- cross-module regression fixtures
- handler/finally/abort semantic fixtures
- native actor/ref handler fixtures
- the insight that Generic-derived serializers should eventually become
  compile-time-specialized direct functions, not runtime Generic interpreters

Do not port wholesale:

- monadic IR as the primary lowering input
- selective/fallback Core merge
- direct/uniform dict adapter lattice
- imported fact reconstruction by repeatedly translating imported modules
- broad Generic inlining without first proving it improves emitted Core and
  runtime speed

## Proposed Restart From Main

If work restarts from `main`, keep the first phase deliberately small:

1. Add ABI assertion helpers around existing call emission.
2. Add or strengthen runtime-shape metadata for imported callables.
3. Add an audit/debug mode that explains direct vs CPS routing decisions.
4. Add focused tests from this branch's repros.
5. Only then add one known-dict method specialization case.
6. Measure `saga_json` no-effect ArgOpts after every optimization.

The go/no-go gate should be:

```text
selective discipline on main must not regress the no-effect JSON benchmark
before any effect-options optimization is considered.
```

If that gate fails, the optimization should be backed out immediately rather
than worked around with another layer.

## Bottom Line

The branch answered an important question:

```text
Can we get uniform-ish safety by building a monadic/selective/fallback backend
and then optimizing back toward direct code?
```

The current evidence says: not in this form.

The useful lesson is narrower and stronger:

```text
Keep main's direct-first runtime model.
Make call shape explicit.
Make wrong ABI choices impossible or loudly diagnosed.
Specialize only where the emitted Core and benchmark data prove it helps.
```
