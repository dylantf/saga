# Uniform Effect Translation Acceptance / Hardening Pass

This is the next checkpoint after phase 1 parity and the first conservative
phase 2 optimization milestone. Treat this as the handoff doc before starting
any larger new optimization.

## Current Snapshot

- The new monadic path is active.
- Phase 1 slow-path parity is complete according to the current in-repo suites.
- Stage 11 / phase 2 has shipped:
  - step 9: bind-collapse,
  - step 10: Bind-to-Let promotion,
  - step 11: conservative tail-resumptive direct-call.
- The direct-call milestone intentionally skips:
  - dynamic handlers,
  - native handlers,
  - composite handlers,
  - multishot and oneshot arms,
  - handler arms with `finally_block`,
  - multi-arm dispatch for the same op,
  - nontrivial op parameter patterns,
  - arm bodies that still contain `Yield`.
- A recent metadata fix widened `EffectInfo.effect_ops` with
  `ModuleCodegenInfo::effect_defs` from the full codegen context so imported
  effects such as `Std.Fail.Fail` have op-index metadata at translation time.

## Goal

Before adding more optimization, prove that the completed new path is a stable
baseline:

1. It remains behaviorally correct on the full repo suite and external
   shakedown projects.
2. The optimizer preserves the slow path as a correctness oracle.
3. The emitted Core shows the expected wins for simple pure and
   tail-resumptive cases.
4. Remaining runtime warnings/panics point at real unsupported surfaces, not
   stale phase wording.

## Immediate Wrap-Up

Commit the current metadata/comment cleanup once validation is green. The
important files from this detour are:

- `src/codegen/mod.rs`
- `src/codegen/monadic/translate/mod.rs`
- `src/codegen/lower_monadic/mod.rs`
- `src/codegen/lower_monadic/bootstrap.rs`
- `src/codegen/tests.rs`
- `docs/planning/uniform-effect-translation/review-notes.md`

Suggested commit message:

```text
fix: include imported effect ops in monadic metadata
```

## Repo Validation

Run these from `/home/dylan/projects/saga`:

```sh
cargo test -q -p saga --lib
cargo test -q --test codegen_integration
cargo test -q --test effect_property_tests
cargo test -q --test stdlib_tests stdlib_test_suite
cargo test -q --test e2e
cargo fmt --check
cargo clippy -q
```

Also run the example sweep and inspect any failures:

```sh
# Use the existing local example runner if available, or run the same command
# pattern the project has been using to produce output_run_examples.txt.
cargo run --bin saga --quiet -- run examples/25-state-effect.saga
cargo run --bin saga --quiet -- run examples/54-choose-backtracking.saga
cargo run --bin saga --quiet -- run examples/55-nqueens-solver.saga
```

The named examples are regression sentinels:

- `25-state-effect.saga`: value-producing resume.
- `54-choose-backtracking.saga`: multishot resume through list search.
- `55-nqueens-solver.saga`: multishot resume through recursive search.

## External Shakedown

Run the projects that have already found real boundary bugs:

```sh
cd ~/projects/saga_json
cargo run --manifest-path ~/projects/saga/Cargo.toml --bin saga -- test

cd ~/projects/saga_pgo
cargo run --manifest-path ~/projects/saga/Cargo.toml --bin saga -- test

cd ~/projects/saga_http
cargo run --manifest-path ~/projects/saga/Cargo.toml --bin saga -- test

cd ~/projects/edda
cargo run --manifest-path ~/projects/saga/Cargo.toml --bin saga -- run
```

For long-running servers such as `edda`, "compiled and started" is enough for
this acceptance pass; stop the server after confirming the compiler no longer
panics.

## Slow-Path Oracle Check

Keep `effect_opt::RunOptions { skip: true }` usable as the correctness oracle.
Before making a new optimization, compare at least one failing-looking case
with optimization skipped. If skipped behavior is wrong, the bug is in phase 1
translation/lowering. If skipped behavior is right and optimized behavior is
wrong, the bug is in Stage 11.

## Emitted-Core Spot Checks

Use `inspect` / `emit` on small programs rather than reading huge examples.

```sh
cargo run --bin saga --quiet -- inspect examples/25-state-effect.saga --stage monadic
cargo run --bin saga --quiet -- inspect examples/25-state-effect.saga --stage monadic-opt
cargo run --bin saga --quiet -- emit examples/25-state-effect.saga
```

Things to look for:

- Pure functions should not keep unnecessary bind-continuation scaffolding.
- Simple tail-resumptive static handlers should lose the relevant `Yield` in
  `monadic-opt`.
- Multishot handlers should still retain the slow path.
- Skipped direct-call cases should be obviously skipped for a conservative
  reason, not because metadata was unavailable.

## Live Warning / Panic Signals

These are still meaningful and should be investigated if they appear:

- `EffectInfo.effect_ops table is incomplete`
  - Missing effect op metadata at the emit boundary.
- `dynamic handler at with site has unknown effect tag`
  - Missing handler-effect metadata for a dynamic handler value.
- `native handler ... is not implemented in the new lowerer`
  - Native bootstrap coverage gap.
- `{not_implemented_native_op, Effect, Op}`
  - Runtime hit a deliberate native op stub.
- `Static handler ... missing arm for op_index`
  - Static handler coverage/op-index metadata mismatch.

## Next Decision After Acceptance

Pick exactly one next track after this checklist is green:

1. **Abstraction cleanup pass.** **Started.**
   Reduce duplication and name the protocol helpers before more optimization.
   Completed targets include marked-control tuple/arm helpers, callback
   boundary identity/type helpers, finally cleanup sequencing, and separating
   the static native bootstrap metadata and Ref/Vec store-specific builders
   from the bootstrap shell. Result-delimiter arm construction is also shared.
   Remaining cleanup is mostly opportunistic; new semantic work should get its
   own plan.

2. **Native direct-call specialization.**
   Optimize BEAM-native effects by bypassing evidence lookup where the handler
   is statically known native. Keep this separate from tail-resumptive static
   handler inlining.

3. **`finally_block`-preserving direct-call.**
   Extend direct-call to cleanup arms only after specifying exactly how cleanup
   composes with marked value-result and abort routing.

4. **Broader static direct-call coverage.**
   Add support for nontrivial op parameter patterns and multi-arm dispatch.
   This is less urgent than native/direct cleanup unless profiling says
   otherwise.

Recommended order: finish the started abstraction cleanup pass before adding
another semantic optimization.

## Acceptance Run: 2026-05-30

Status: **green**.

Repo validation:

- `cargo test -q -p saga --lib`
  - `1121 passed; 0 failed; 12 ignored`
- `cargo test -q --test codegen_integration`
  - `102 passed`
- `cargo test -q --test effect_property_tests`
  - `63 passed`
- `cargo test -q --test stdlib_tests stdlib_test_suite`
  - `1 passed`
- `cargo test -q --test e2e`
  - `1 passed`
- `cargo test -q -p saga --lib codegen::monadic::effect_opt`
  - `26 passed`
- `cargo fmt --check`
  - passed
- `cargo clippy -q`
  - passed

Example sweep:

- `./run_examples.sh`
  - passed with exit 0.
- Regression sentinels:
  - `25-state-effect.saga` printed `"5"` and `"hello world"`.
  - `32-monitor.saga` ran without evidence-tag errors.
  - `54-choose-backtracking.saga` printed the expected Pythagorean triples.
  - `55-nqueens-solver.saga` found 2 four-queen solutions and 92 eight-queen
    solutions.

External shakedown:

- `~/projects/saga_json`
  - `saga test`: `218 passed; 0 failed`.
- `~/projects/saga_http`
  - `saga test`: `111 passed; 0 failed`.
  - No `dynamic handler at with site has unknown effect tag` warning appeared.
- `~/projects/saga_pgo`
  - No `tests/` directory; `saga test` exits with "No tests directory found".
  - `saga build` passed.
- `~/projects/edda`
  - `saga run` compiled all modules and started the server.
  - Stopped after confirming startup; no `EffectInfo.effect_ops table is
    incomplete` panic.

IR / optimizer spot checks:

- `examples/25-state-effect.saga --stage monadic-opt` still contains `Yield`
  for the state operations. This is expected: the handler uses
  value-producing resume (`let r = resume s; r s`) and is outside the
  conservative tail-resumptive direct-call milestone.
- `examples/54-choose-backtracking.saga --stage monadic-opt` still contains
  `Yield` for `Choose/choose`. This is expected: the handler is multishot.
- `tests/e2e/tests/effects_test.saga --stage monadic-opt` shows
  `tail_resumptive_direct_call_return_clause` replacing the handled
  `get_counter!` body with `Pure(10)` under the static handler, confirming the
  positive direct-call case.

Conclusion:

- The completed phase 1 slow path and conservative Stage 11 optimizer form a
  stable baseline across repo tests, examples, and the current external
  shakedown corpus.
- Next recommended track remains the **abstraction cleanup pass** before adding
  native direct-call or `finally_block`-preserving direct-call.

## Post-Cleanup Hardening Run: 2026-05-30

Status: **green** after the abstraction cleanup batch.

- `cargo test -q -p saga --lib`
  - `1121 passed; 0 failed; 12 ignored`
- `cargo test -q --test codegen_integration`
  - `102 passed`
- `cargo test -q -p saga --lib codegen::lower_monadic`
  - `93 passed`
- `cargo test -q --test effect_property_tests`
  - `63 passed`
- `cargo test -q --test stdlib_tests stdlib_test_suite`
  - `1 passed`
- `cargo test -q --test e2e`
  - `1 passed`
- `cargo fmt --check`
  - passed
- `cargo clippy -q`
  - passed
- `./run_examples.sh`
  - passed with exit 0
