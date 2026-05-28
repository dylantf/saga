# Uniform Effect Translation Review Notes

Status: **triage review started**.

This is a working review map for the large uniform-effect-translation PR. It
is intentionally not a complete audit. Use it to decide where to spend review
and refactor time before starting strategic phase 2.

## Decisions Log

Intentional scope decisions made during review, so nobody re-litigates them or
mistakes them for accidental feature deletion.

- **`@inline val` optimization removed (for now).** The cross-module inline-val
  substitution was a premature compiler optimization and the only thing
  producing the two `qualified_inline_val_*` red tests (those tests asserted
  the *old-path* substitution semantics, which the uniform path deliberately
  does not implement — vals are uniformly emitted as arity-0 constants). Rather
  than build inline support into the new path to satisfy old-path-shaped tests,
  we dropped the feature:
  - parser no longer accepts the `@inline` annotation
    (`KNOWN_ANNOTATIONS` in `src/parser/decl.rs`),
  - the typechecker no longer collects or validates inline vals
    (`inline_vals` population in `check_module.rs`; `is_inlineable_expr` /
    `@inline` validation removed from `check_decl.rs`),
  - vals now fall through to the uniform arity-0 `BeamFunction` path on **both**
    old and new codegen, so no old-path code was edited,
  - the two `qualified_inline_val_*` tests were deleted; `@inline` stripped from
    `examples/42-val-inline.saga` and the fully-qualified-import bug example.

  The `inline_vals` field on `ModuleCodegenInfo` and
  `ResolvedCodegenKind::InlineVal` are now permanently empty/unreachable. They
  were left in place only because the frozen old `lower/` path still references
  them; delete both together with the old path. This resolves the Stage 8
  `InlineVal`-panic blocker and the Open Question "Should `InlineVal` survive
  backend resolve at all in the new path?" (answer: no — the feature is gone).

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

- `tests/codegen_integration.rs`: green.
- `tests/effect_property_tests.rs`: green.
- `tests/module_codegen_integration.rs`: green for active tests; remaining
  ignored tests should be reclassified individually. Many are stale
  old-Core-shape assertions, while some may still cover real cross-module
  behavior worth rewriting.
- `tests/stdlib_tests.rs::stdlib_test_suite`: green, including first-class
  references to bridge HOFs / legacy-Maybe externals.
- `tests/e2e`: green in the latest full Saga test sweep, but it does not cover
  the full stdlib callback surface.

## Review Strategy

Do one stage at a time, tracing function calls from entry to output and
checking the contract from the planning/spec docs.

For each stage:

1. Identify its public entry points.
2. Verify the stage consumes only the prior stage's contract.
3. Verify it does not make decisions owned by later stages.
4. Map any failing tests to the first stage where the incorrect shape appears.
5. Fix locally, then rerun the narrowest failing tests.

## Abstraction / Duplication Watch

This refactor is intended to simplify correctness by making evidence and
continuations uniform. That goal is undermined if the new path encodes the same
ABI rule in several handwritten places. Treat these as cleanup blockers before
phase-2 optimization, even when tests are green.

- **External-call ABI is shared.** Saturated external calls in
  `lower_monadic/app.rs` and first-class external wrappers in
  `lower_monadic/decls.rs` now both route through
  `util::lower_external_native_call`, so bridge callback adapters and
  legacy-Maybe normalization apply in both paths.
- **Handler `with` delimiter logic is duplicated.** `lower_with_static` and
  `lower_with_dynamic` both construct raw-result K, abort marker handling,
  evidence insertion, body wrapping, and outer-K forwarding. The dynamic path
  has extra handler-value extraction, but the delimiter should be one helper
  with mode-specific inputs.
- **Native handler bootstrap is becoming a second lowering language.**
  `lower_monadic/bootstrap.rs` has a useful table-driven core, but Ref/Vec and
  callback-invoking ops are growing custom Core Erlang emitters. Prefer a
  small native-op DSL/descriptor plus focused escape hatches over more
  handwritten nested `CExpr` trees.
- **Record metadata is reconstructed from runtime tags.** Anonymous-record
  field order should come from structural metadata (`RecordInfo`/type info), not
  from parsing the encoded tag string in lowering.
- **Old-path helper copies should either become shared code or disappear with
  old path deletion.** `lower_monadic/util.rs` is an acceptable temporary clone
  because the agent guide forbids imports from `lower/`, but it should not grow
  new semantics independently.
- **Shape-heavy unit tests are useful but expensive.** `lower_monadic/tests.rs`
  is large because it asserts exact Core Erlang shapes. Keep a small set of
  ABI-shape tests, but prefer runtime/e2e/property coverage for behavior so
  local refactors do not require rewriting thousands of brittle assertions.

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
- `ResolvedCodegenKind::InlineVal` — **RESOLVED, see Decisions Log.** The
  `@inline val` optimization was removed, so this kind is no longer produced and
  the `lower_monadic::atom` panic is now unreachable. The two
  `qualified_inline_val_*` tests it mapped to were deleted. The variant + the
  `inline_vals` field remain only as dead code for the frozen old path; delete
  with the old path.

Likely action:

- Move any shared helper logic out of old `lower/` before cleanup. The
  `resolve.rs` imports from `lower/` (above) are the remaining real Stage 8
  cleanup blocker.

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

Step 2 status:

- Abort markers crossing a value-producing `resume` are now unwrapped at the
  resume boundary before the arm-local continuation runs. This fixes
  `fail_handler_inside_resume_aborts_correctly`.
- `BindMode::ValuePosition` now distinguishes ANF-introduced value-position
  delimiters from source sequencing. This fixes
  `lambda_head_effectful_call_nested_in_outer_effectful_call` without changing
  ordinary source/block `Bind` continuation capture.
- `nested_same_effect_inner_shadows_outer` now asserts op dispatch shadowing
  with an identity outer return clause. Return-clause composition remains
  lexical and is covered by the e2e nested-return tests.

### Native / Bridge Callback Boundary

Contract:

- Saga functions are uniform CPS: `(args..., _Evidence, _ReturnK)`.
- Native Erlang callbacks expect native source arity.
- Any boundary from native/bridge code into Saga callback values must adapt.

Current status:

- `stdlib_test_suite` is currently green. `lower_monadic/app.rs` has callback
  adapters for known bridge functions such as Array/Dict/List/Set HOFs.
- The current implementation is table-driven but still ad hoc: callback
  argument positions/arity live in `external_callback_arg`, not in resolved
  type metadata.

Review checkpoints:

- Confirm every stdlib bridge HOF in public API either routes through Saga
  code or appears in `external_callback_arg`.
- The adapter must be designed carefully for pure vs effectful callback types;
  do not use a throw/catch synchronous extractor for effectful callbacks unless
  the type system proves the callback is pure at that boundary.
- Long-term cleanup: move callback shape out of a hardcoded module/function
  table and derive it from function types/effect metadata.

### Review Pass 3: Application / Callable ABI

Scope:

- `src/codegen/lower_monadic/app.rs`
- callable value emission in `src/codegen/lower_monadic/atom.rs`
- callable definitions/wrappers in `src/codegen/lower_monadic/decls.rs`
- app translation in `src/codegen/monadic/translate/expr.rs`
- backend resolution metadata consumed by the above

Why this is one pass:

- The same ABI question appears in several shapes: direct calls, function
  references, vals in function position, partial application, over-application,
  external calls, bridge callbacks, dict constructors, intrinsics, and
  eta-reduced effect op references. Reviewing these separately tends to create
  local fixes that disagree about arity or callable value shape.

Contract:

- Saga-defined callable values use uniform CPS shape:
  `(user/dict args..., _Evidence, _ReturnK)`.
- Top-level `val`s are arity-0 materializers, not callable values. A val whose
  materialized value is a function must be invoked in two steps:
  materialize val, then apply returned function with uniform args.
- Dict constructors are callable values even when their source arity is zero;
  they still need the uniform `_Evidence, _ReturnK` slots.
- External/runtime functions are direct Erlang calls at source/runtime arity
  when saturated. If a Saga callback crosses that boundary, wrap it in a
  native-arity adapter that supplies evidence and an identity return K.
- Partial application must eta-expand to a uniform Saga callable, never emit an
  under-applied Core Erlang `apply`.
- Eta-reduced effect ops as values should stay explicitly eta-expanded by the
  translator unless/until the IR grows a first-class effect-op-reference atom.
- Local source binders shadow imported/top-level resolution before any
  function-reference lowering happens.

Known-good signal today:

- `tests/codegen_integration.rs` is green, including partial application,
  zero-arity over-application, effectful callbacks, eta-reduced effect-op
  callbacks, external disambiguation, and import shadowing tests.
- `tests/stdlib_tests.rs` and `tests/e2e` are green, including bridge HOFs and
  actor callback cases.

Risk areas to audit anyway:

- `ResolvedCodegenKind::InlineVal` still exists as dead old-path residue after
  removing `@inline`; it should remain unreachable until old-path deletion.
- `uniform_value_arity` relies on old-path resolution conventions: effectful
  imported arities may already include `+2`, while pure arities do not. This
  is subtle and should be locked down with tests before deleting old code.
- `external_callback_arg` is a hardcoded bridge table. It is acceptable as a
  phase-1 parity bridge, but it is not the final architecture.
- Saturated external calls and first-class external references now share
  `util::lower_external_native_call`; stdlib tests cover `List.sort_by` and
  `List.nth` through first-class references.
- `external_callback_adapter` uses identity K and direct return. This is only
  correct for callbacks used synchronously by bridge/native code; async
  boundaries such as actor spawn need dedicated native-effect handling.
- Value-position `BindMode` changed effectful argument evaluation. Recheck
  nested effectful arguments plus partial application together so callable ABI
  does not accidentally reintroduce continuation capture bugs.
- Intrinsic references now use wrapper functions when source-module metadata
  is available. Missing wrappers should fail loudly, but the review should
  confirm which intrinsics are meant to be first-class.

Execution checklist:

1. Inventory all callable emitters: `lower_app`, `lower_atom` resolved refs,
   val lowering, fun/letfun lowering, dict constructor lowering, external and
   intrinsic wrappers.
2. Build a small table: source construct → `MExpr`/`Atom` shape → expected
   Core Erlang callable/value shape.
3. Trace resolution metadata for each live `ResolvedCodegenKind`, especially
   `BeamFunction`, `ExternalFunction`, and `Intrinsic`.
4. Confirm the dead `InlineVal` path is unreachable after parser removal; do
   not reintroduce support unless `@inline` returns as a deliberate feature.
5. Audit `uniform_value_arity` assumptions against imported pure/effectful
   functions and dict constructors; add/adjust focused tests if the current
   convention stays.
6. Replace or document `external_callback_arg` as the phase-1 bridge table;
   add tests for any public bridge HOF not covered by stdlib/e2e.
7. ~~Unify external wrapper lowering with saturated external-call lowering so
   callback adapters and legacy-Maybe normalization apply whether an external
   is called directly or through a first-class function reference.~~ Done via
   `util::lower_external_native_call`.
8. Re-run:
   - `cargo test -q -p saga --test codegen_integration -- --nocapture`
   - `cargo test -q -p saga --test module_codegen_integration -- --nocapture`
   - `cargo test -q -p saga --test stdlib_tests -- --nocapture`
   - `cargo run --bin saga --quiet -- test` in `tests/e2e`
   - `cargo clippy -q`

### Review Pass 4: Record Metadata / Tuple Layout

Scope:

- Anonymous record tag construction in `src/ast.rs::anon_record_tag`.
- Elaboration of field access/update record identity in `src/elaborate.rs`.
- `MExpr::FieldAccess` / `MExpr::RecordUpdate` layout payloads in
  `src/codegen/monadic/ir.rs`.
- Lowering in `src/codegen/lower_monadic/exprs_edge.rs`.
- Runtime tuple tag expectations in pattern lowering and old/new record
  construction paths.

Contract:

- Lowering must know field position from structural metadata, not by parsing a
  runtime tag string.
- Anonymous record runtime tags must be injective over field-name sets.
- Named records keep declared field order from `RecordInfo` /
  `ModuleCodegenInfo::record_fields`.
- Anonymous records use canonical sorted field order from `Type::Record`.

Findings:

- Implemented in this branch. `ast::anon_record_tag` now uses a
  length-prefixed opaque atom format, so `{a_b, c}` and `{a, b_c}` no longer
  collide at runtime.
- `ExprKind::FieldAccess` / `ExprKind::RecordUpdate` and the monadic IR now
  carry `anon_fields: Option<Vec<String>>`. Elaboration fills this from
  `Type::Record` using the canonical sorted field order.
- `lower_monadic::exprs_edge` resolves field order from structural metadata:
  anonymous records use `anon_fields`; named records use
  `ModuleCodegenInfo::record_fields`. It no longer decodes the runtime tag.
- Tests cover anonymous field access/update with underscore field names and a
  direct `anon_record_tag` collision regression.

Recommended fix:

1. Introduce an explicit record-layout payload instead of overloading
   `record_name: Option<String>`. For example:

   ```rust
   enum RecordLayout {
       Named(String),
       Anonymous(Vec<String>), // sorted canonical field order
   }
   ```

   This can live in AST first, monadic IR first, or both. The important bit is
   that `FieldAccess` and `RecordUpdate` carry `Anonymous(Vec<String>)` through
   translation so lowering never decodes a runtime tag.

2. Change anonymous runtime tag encoding to be injective. A length-prefixed or
   escaped atom format is enough, e.g. `__anon_3:a_b|1:c`; both old and new
   construction/pattern paths should use the same helper.

3. Add tests before/with the fix:
   - anonymous record access with underscore field names,
   - anonymous record update with underscore field names,
   - collision pair `{a_b, c}` vs `{a, b_c}` must not pattern-match/equal as
     the same runtime shape,
   - named-record access/update still uses declared field order across modules.

Follow-up:

- If the frozen old lowerer must remain behaviorally togglable for anonymous
  record field access/update, it would need to consume the same structural
  field-order metadata. Under the current frozen-old-path rule, only mechanical
  match updates were made there.

Decision:

- Do not patch this locally by teaching the lowerer a better string split. The
  bug is in the metadata contract and runtime tag encoding, not just the parser
  for the current tag format.

### Review Pass 5: Native Handler Bootstrap

Scope:

- `src/codegen/lower_monadic/bootstrap.rs`
- Native handler installation from `lower_monadic/effects.rs`
- Native effect declarations in `src/stdlib/Actor.saga`, `Ref.saga`,
  `Vec.saga`
- Shape tests in `src/codegen/lower_monadic/tests.rs`
- Runtime/e2e coverage in actor/ref/vector examples and tests

Contract:

- The uniform path must install runtime evidence entries for BEAM-native
  effects that the old lowerer handled by direct special cases.
- Native op closures share the same handler ABI as user handler arms:
  `fun(args..., EvidenceAtPerform, K) -> apply K(result)`.
- Callback-taking native ops must invoke Saga callbacks with uniform CPS
  arguments and the correct evidence vector.
- Explicit native handlers (`with beam_ref`, `with ets_ref`, `with beam_vec`,
  `with beam_actor`) and the entry-point initial evidence should use compatible
  op tuple shapes.

Findings:

- The file currently mixes three concerns:
  - initial evidence vector / `main/1` entry wrapper,
  - generic native-op descriptor lowering (`NativeEffect`, `NativeOp`,
    `ArgTransform`),
  - bespoke Ref/Vec storage implementations as handwritten nested `CExpr`
    trees.
- The table-driven core is good and should be kept. The bespoke Ref/Vec code is
  where complexity pools; it is not yet bad enough to block review, but it is
  the prime target for a later abstraction pass.
- Callback adaptation exists in multiple conceptual forms:
  - bridge callback adapters in `util::lower_external_native_call`,
  - `spawn_thunk` for async spawned callbacks,
  - Ref `modify` callbacks with an identity K.

  These are intentionally not all the same abstraction: `spawn` is async and
  must carry perform-site evidence into a new process; Ref `modify` is pure by
  the stdlib type (`a -> a`); bridge HOFs are synchronous native calls. Still,
  they should be documented as three callback boundary classes so future
  patches do not merge them accidentally.
- Bootstrap comments still mention “future step 8” in a few places even though
  the toggle wiring now exists. Clean this wording during the abstraction pass.
- Tests cover bootstrap shape, op tuple counts/tags, basic BIF forwarding, and
  spawn evidence threading. E2E covers actors, refs, ETS refs, and vectors.
  Remaining risk is not obvious missing behavior; it is maintainability and
  hand-written Core Erlang fragility.

Recommended cleanup later:

1. Split `bootstrap.rs` by concern, or at least group it into sections with
   smaller builders:
   - initial evidence / entry wrapper,
   - generic native effect descriptors,
   - Ref backend builders,
   - Vec backend builders.
2. Replace repeated continuation wrappers with helpers such as
   `native_closure(params, result_expr)` and `identity_k(name)`.
3. Name the callback boundary classes explicitly:
   - synchronous native bridge callback,
   - async spawn callback,
   - pure in-handler callback.
4. Keep Ref/Vec as bespoke backends unless/until more native stateful effects
   appear; a too-general DSL would be premature.

### Review Pass 6: Handler Cleanup / `finally`

Scope:

- `src/codegen/lower_monadic/effects.rs`
- `src/codegen/lower_monadic/exprs.rs::lower_resume`
- `src/codegen/lower_monadic/ctx.rs`
- `MExpr::contains_resume` / `Atom::contains_resume`
- E2E finally tests in `tests/e2e/tests/effects_test.saga`

Contract:

- A handler arm's `finally` block must run on both:
  - successful/resuming completion, after the resumed computation returns to
    the arm, and
  - non-resuming/abort completion, after the arm body has produced its abort
    result.
- Cleanup must be injected into the continuation chain. Wrapping only the
  `resume` call in Erlang `try/catch` is not sufficient under uniform CPS,
  because effect aborts are values flowing through handler continuations, not
  Erlang exceptions.
- `finally` must preserve abort markers correctly: cleanup should run, but it
  must not turn another delimiter's abort tuple into an ordinary success value.

Findings:

- Single-arm operation clauses have partial `finally` support:
  - if the arm body syntactically contains `resume`, `lower_resume` sequences
    cleanup after the delimited resume result,
  - if the arm body does not contain `resume`, `build_arm_closure_with_return_mode`
    appends cleanup after the arm body.
- Multi-arm-per-op closures still panic when any arm has `finally_block`.
  This is a real parity gap if the source language permits multiple pattern
  arms for the same operation with `finally`.
- Return-clause `finally_block` also panics as deferred. This is probably less
  urgent because return clauses having `finally` may be syntactically unusual,
  but the invariant should be enforced earlier or supported deliberately.
- Cleanup behavior depends on `contains_resume`, which descends into
  `Atom::Lambda` bodies. That is conservative for propagating `arm_k` into
  lambdas, but it can misclassify an arm that merely *returns* a lambda
  containing `resume` as a resuming arm. In that case the no-resume cleanup path
  is skipped unless the returned lambda is later invoked. This may be illegal or
  unreachable in well-typed Saga today, but the assumption should be pinned down
  with a test or with a more precise predicate.
- `lower_resume` still contains two local cleanup helper closures with nearly
  identical setup. This is an abstraction smell, not a behavior bug by itself.

Verified finding (new — confirmed live bug):

- **Foreign-abort routing through a resuming arm is only half-correct.** In
  `lower_resume`, the foreign-abort case (arm matching `{abort, other_marker,
  v}` — an abort whose marker is *not* this delimiter's) **unwraps** the abort
  and delivers `v` to this arm's continuation. That is correct only when the
  aborting handler is **inner** relative to the resuming handler (its delimiter
  is inside the resumed continuation and has already produced its result). When
  the aborting handler is **outer**, the abort must instead **propagate** past
  the inner resuming delimiter — unwrapping mis-routes it.
  - Inner-aborting case (passes today): `fail_handler_inside_resume_aborts_correctly`
    in `tests/effect_property_tests.rs` — resuming `collect` (Log) is outer,
    aborting `to_result_str` (Fail) is inner.
  - Outer-aborting case (broken): resuming `silent_log` (Log) is inner, aborting
    `to_result` (Fail) is outer. Minimal repro returns a type-confused
    `Ok (Err "boom")` instead of `Err "boom"`. Captured as a **skipped** e2e
    test, `effects_test.saga` → "foreign abort propagates through an inner
    resuming arm".
  - A blanket "always propagate" fixes the outer case but breaks the inner one
    (tried — regresses the property test). The correct fix needs **delimiter
    scope awareness**: distinguish whether `other_marker` belongs to a delimiter
    enclosing this `with` (propagate) or nested within the resumed continuation
    (deliver as value). There is no marker ordering/scope registry today, so
    this is a real design task, not a one-line change. Do not patch arm 3
    blindly.

Recommended action:

1. Add focused tests before changing behavior:
   - multi-clause op arm with `finally`,
   - return clause with `finally` if syntax/typechecker accepts it,
   - arm returning a lambda that contains `resume`, to decide whether this is
     rejected, cleaned up immediately, or cleaned up only when invoked.
2. Decide whether `contains_resume` should mean “may resume if evaluated now”
   rather than “contains resume anywhere under lambdas.” If yes, split it into
   two predicates:
   - lexical `contains_resume` for arm-K propagation,
   - immediate/body `may_resume_now` for finally scheduling.
3. Extract cleanup sequencing in `lower_resume` after semantics are pinned
   down; do not refactor it first.

## Open Questions

- Should dynamic handler-value tuples grow a return-clause slot, or should a
  dynamic handler value be represented as a first-class structure containing
  op tuple plus return handler?
- Should effect-op references as values be represented in monadic IR, or
  always eta-expanded during translation?
- ~~Should `InlineVal` survive backend resolve at all in the new path?~~
  Answered: no — `@inline` removed (see Decisions Log).
- Which old module-codegen assertions are worth rewriting against uniform
  Core shape, and which should be deleted as old-lowerer implementation tests?
- Do finally blocks need multi-arm/return-clause support before phase 1 is
  considered complete, or are current e2e semantics enough?

## Recommended Next Review/Refactor Order

1. **Application / callable ABI review.**
   Use Review Pass 3 above. This now includes native/bridge callback adapters
   because they are part of the same callable-boundary contract.

2. **Record metadata.**
   Done for the new path. Anonymous runtime tags are length-prefixed and
   lowering receives structural anonymous field order through AST/monadic IR
   metadata instead of decoding the tag string.

3. ~~**Cross-module `InlineVal`.**~~ Resolved by removing `@inline` (see
   Decisions Log).

4. **Stale tests.**
   Rewrite or delete old Core-shape assertions after the runtime/parity
   failures are fixed. Do not spend much energy here before the real bugs.

## Commands Used For This Triage

```sh
git diff --stat main...HEAD
git diff --name-status main...HEAD
rg -n "crate::codegen::lower::|normalize::|call_effects::|TODO|panic!|unimplemented|not implemented|deferred|InlineVal" \
  src/codegen/anf src/codegen/monadic src/codegen/lower_monadic src/codegen/mod.rs src/codegen/resolve.rs
```
