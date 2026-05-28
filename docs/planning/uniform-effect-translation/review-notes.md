# Uniform Effect Translation Review Notes

Status: **triage review started**.

This is a working review map for the large uniform-effect-translation PR. It
is intentionally not a complete audit. Use it to decide where to spend review
and refactor time before starting strategic phase 2.

## Current Diff Shape

Compared with `main`, this branch is roughly:

- ~19.4k inserted lines, mostly new compiler stages and tests.
- New stage modules:
  - `src/codegen/anf/`
  - `src/codegen/handler_analysis.rs`
  - `src/codegen/monadic/`
  - `src/codegen/lower_monadic/`
- Existing-path touch points:
  - `src/codegen/mod.rs`
  - `src/codegen/resolve.rs`
  - `src/cli/commands.rs`
  - parser unit-parameter handling
  - test harnesses and integration fixtures

The review should not try to read this as one blob. Review it by stage and
stage boundary.

## Current Test Signal

Useful default failures should stay visible until fixed.

- `tests/codegen_integration.rs`: 5 real failures.
- `tests/effect_property_tests.rs`: 4 real failures.
- `tests/module_codegen_integration.rs`: at least the two `InlineVal`
  failures are real new-path failures; many other ignored tests are stale
  old-Core-shape assertions.
- `tests/stdlib_tests.rs::stdlib_test_suite`: 12 stdlib native/bridge callback
  failures.
- `tests/e2e`: currently green, but it does not cover the full stdlib callback
  surface.

## Review Strategy

Do one stage at a time, tracing function calls from entry to output and
checking the contract from the planning/spec docs.

For each stage:

1. Identify its public entry points.
2. Verify the stage consumes only the prior stage's contract.
3. Verify it does not make decisions owned by later stages.
4. Map any failing tests to the first stage where the incorrect shape appears.
5. Fix locally, then rerun the narrowest failing tests.

## Stage Triage

### Stage 8: Backend Resolve

Contract:

- Runs after elaborate and before ANF.
- Produces immutable `ResolutionMap` keyed by source `NodeId`.
- Must not encode old selective-CPS assumptions that the new path cannot
  consume.

Review checkpoints:

- `src/codegen/resolve.rs` still imports helpers from `src/codegen/lower/`
  (`extract_external`, `arity_and_effects_from_type`, `dict_param_count`).
  Since `resolve.rs` is shared infrastructure this may be acceptable for now,
  but it is a cleanup/architecture risk: the final old-path deletion cannot
  leave `resolve.rs` depending on deleted lower modules.
- `ResolvedCodegenKind::InlineVal` is still produced and can reach
  `lower_monadic::atom`, which deliberately panics. This maps directly to:
  - `qualified_inline_val_cross_module_substitutes_rhs`
  - `qualified_inline_val_cross_module_resolves_sibling_ref_in_defining_module`

Likely action:

- Decide whether `InlineVal` should be normalized before monadic lowering or
  represented explicitly in the new path. Do not leave a panic as the contract.
- Move any shared helper logic out of old `lower/` before cleanup.

### Stage 8.5: Handler Analysis

Contract:

- Pure syntactic classification over elaborated AST handler arms.
- Used by optimization only.
- Must not affect slow-path correctness.

Review checkpoints:

- Ensure no slow-path lowering behavior depends on handler-analysis flags.
- Confirm analysis still matches the current `resume` semantics after the
  value-producing resume and abort-marker fixes.

Likely action:

- Low priority until phase 2, unless direct-call optimization begins.

### Stage 9: ANF

Contract:

- Full ANF over all expression positions.
- Does not cross lambda/branch/handler-arm boundaries.
- Preserves source `NodeId` on relocated expressions via `rebuild_like`.
- Uses fresh IDs only for synthetic wrappers and variables.

Review checkpoints:

- Field access and anonymous-record metadata failures may originate before
  lowering if ANF or type/resolution metadata splits field names incorrectly.
- Search for any `Expr::synth` use around relocated source expressions.
- Confirm handler-arm bodies, lambda bodies, receive arms, and case arms are
  ANF'd in their own contexts, not lifted outward.

Likely action:

- Use `handler_bindings_from_record_fields_compile` to trace anonymous record
  field metadata from parse/typecheck through ANF into `lower_field_access`.

### Stage 10: Monadic Translation

Contract:

- Emits `Bind` uniformly. It must not choose `Let` for pure sites.
- Does not decide "is this effectful?" except by translating explicit effects
  and using already-resolved metadata.
- Produces `MExpr` / `Atom` shapes matching `monadic-ir-spec.md`.

Review checkpoints:

- Dynamic handler values have operation arms but currently lose return-clause
  behavior. This maps to `handler_factory_let_binding_runs_return_clause`.
- Eta-reduced effect op references (`ping!` as a value) need a clear IR shape:
  either explicit eta-expanded lambda or an atom form the lowerer can adapt.
  This maps to `eta_reduced_effect_op_callback_forwarded_through_wrapper_runs`.
- Zero-arity value functions returning lambdas are represented as uniform
  `/2` functions, but some application path still emits `/0`. This maps to:
  - `pure_partial_application_compiles`
  - `over_application_of_zero_arity_compiles`

Likely action:

- Inspect translation of handler expressions and named handler references
  before changing lowering; if return clauses are absent from `MHandler` /
  handler-value IR, lowering cannot recover them cleanly.
- Trace value-function application through `MExpr::App` and `Atom::Var` for
  `increment = add 1`.

### Stage 11: Effect Optimization

Contract:

- Identity is valid during phase 1.
- No correctness bugs should depend on optimization.
- Phase 2 must not start until phase 1 parity blockers are fixed.

Review checkpoints:

- Ensure no phase 1 workaround relies on a future optimization to become
  correct.
- Keep direct-call disabled until the slow path is an oracle.

Likely action:

- Defer real review until phase 1 blockers are gone.

### Stage 12: Lower Monadic

Contract:

- Consumes monadic IR; does not rediscover effectfulness.
- `Bind` lowers via continuation threading.
- `Yield` lowers through evidence lookup.
- `With` installs evidence entries and delimits return/abort markers.
- Handler arms, dynamic handler values, and native handlers share one ABI.

Review checkpoints:

- `LowerCtx` threading is the right model, but any context field that behaves
  like ambient mutable state should be questioned.
- Dynamic handler return clauses are explicitly called out in comments as
  needing a runtime ABI slot. This is a real blocker, not polish.
- `lower_resume` / abort-marker handling is still suspect:
  - `fail_handler_inside_resume_aborts_correctly` leaks an abort marker into
    string append.
  - same-effect/dynamic-handler tests lose or misroute values.
- `effects.rs` still contains deferred panics for `finally_block` on multi-arm
  op closures and return clauses. E2E finally tests pass, but the implementation
  is not obviously complete.
- `bootstrap.rs` is large and easy to special-case incorrectly. Native handler
  tuple shapes must match normal handler tuple shapes.
- `app.rs` has the likely `/0` vs `/2` value-function bug.
- `exprs_edge.rs::lower_field_access` is the direct panic site for anonymous
  record fields with underscores.

Likely action:

- Review handler ABI as one subsystem: perform-site K, arm closure params,
  return clause K, abort marker tags, `resume`, dynamic handler values, and
  native handler tuples.
- Then review application ABI as one subsystem: top-level functions, local
  functions, vals, function references, effect-op references, partial
  application, and over-application.
- Then review edge expressions: records, field access, receive, bitstrings.

### Native / Bridge Callback Boundary

Contract:

- Saga functions are uniform CPS: `(args..., _Evidence, _ReturnK)`.
- Native Erlang callbacks expect native source arity.
- Any boundary from native/bridge code into Saga callback values must adapt.

Current failure:

- `stdlib_test_suite` fails `Dict`, `List.sort*`, and `Set.to_list` tests with
  arity mismatches such as "function called with 2 argument(s), but expects 4".

Likely action:

- Implement a general callback adapter at the external/native boundary.
- Avoid one-off stdlib rewrites unless they are temporary scaffolding.
- The adapter must be designed carefully for pure vs effectful callback types;
  do not use a throw/catch synchronous extractor for effectful callbacks unless
  the type system proves the callback is pure at that boundary.

## Open Questions

- Should dynamic handler-value tuples grow a return-clause slot, or should a
  dynamic handler value be represented as a first-class structure containing
  op tuple plus return handler?
- Should effect-op references as values be represented in monadic IR, or
  always eta-expanded during translation?
- Should `InlineVal` survive backend resolve at all in the new path?
- Which old module-codegen assertions are worth rewriting against uniform
  Core shape, and which should be deleted as old-lowerer implementation tests?
- Do finally blocks need multi-arm/return-clause support before phase 1 is
  considered complete, or are current e2e semantics enough?

## Recommended Next Review/Refactor Order

1. **Application ABI review/fix.**
   Tackle zero-arity value functions and eta-reduced effect op callbacks
   together. They both smell like "value in function position has wrong
   callable shape."

2. **Handler ABI review/fix.**
   Tackle dynamic handler return clauses, same-effect shadowing, conditional
   handler values, and abort marker crossing resume together.

3. **Native/bridge callback adapters.**
   Fix the stdlib suite's arity failures with a general boundary adapter.

4. **Record metadata.**
   Fix anonymous record field names with underscores.

5. **Cross-module `InlineVal`.**
   Remove or support stale `InlineVal` resolution in the new path.

6. **Stale tests.**
   Rewrite or delete old Core-shape assertions after the runtime/parity
   failures are fixed. Do not spend much energy here before the real bugs.

## Commands Used For This Triage

```sh
git diff --stat main...HEAD
git diff --name-status main...HEAD
rg -n "crate::codegen::lower::|normalize::|call_effects::|TODO|panic!|unimplemented|not implemented|deferred|InlineVal" \
  src/codegen/anf src/codegen/monadic src/codegen/lower_monadic src/codegen/mod.rs src/codegen/resolve.rs
```
