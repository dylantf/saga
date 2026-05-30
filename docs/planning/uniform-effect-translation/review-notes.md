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
  - `src/codegen/lower/`
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

- `tests/codegen_integration.rs`: 1 pre-existing failure
  (`tail_recursive_apply_in_tail_position`), rest green.
- `tests/effect_property_tests.rs`: green (63).
- `tests/module_codegen_integration.rs`: green (76); 0 ignored. The last
  dynamic-handler factory/record-field fixtures now assert new-path evidence
  installation instead of old-Core helper names.
- `tests/stdlib_tests.rs::stdlib_test_suite`: green, including first-class
  references to bridge HOFs and optional-return externals.
- `tests/e2e`: green in the latest full Saga sweep (370), but it does not cover
  the full stdlib callback surface.
- Lib unit tests: 1 pre-existing shape-pin failure
  (`codegen::monadic::translate::tests::alias_chase_let_h_is_static`) — leftover
  from the marked-value-result work; needs re-pinning, not a behavior bug.

### Real-world corpus: `~/projects/saga_json`

A ~3.3k-line JSON library (lib + bin demos + 218-test suite) is now a load-bearing
oracle for the new path. Run its suite with `saga test` from the project dir; run
the demos with `saga run`. It shook out the two bugs below; **218/0** after fixes.
Use it as the first place to look for real regressions.

## Resolved this pass (real bugs, with fixes)

1. **Abort-marker collision across function-call boundaries** (commit `176492a`).
   Markers were derived from the per-function `ret_k` counter, which resets at
   every function entry, so the first `with` in every function minted the same
   atom (`__saga_abort__K_ret0`). A callee's prompt then caught a *caller's*
   abort by string match and unwrapped it — a re-aborting handler (`fail e =
   fail! ...`) called through a function boundary leaked its abort as a value.
   Fix: `fresh_abort_marker` in `lower/mod.rs` mints a never-reset,
   module-qualified marker. Static-per-site (vs Koka's per-activation) is sound
   under deep-handler + evidence dispatch; see the note on `fresh_abort_marker`
   and [[koka-faithful-abort-routing]]. Guard:
   `effects_test.saga` "re-abort propagates across a function-call boundary".

2. **Qualified-alias constructors lowered as CPS calls** (commit `09f79ca`).
   `Json.InvalidShape` / `Lib.Boom` (qualified via alias) resolved only as a
   value, so codegen emitted `module:Ctor/(arity+2)` — a nonexistent function →
   runtime `undef`. Directly-imported constructors were fine. Fix: `resolve.rs`
   `QualifiedName` arm also records a constructor into `constructors[expr.id]`;
   `translate/expr.rs` emits `Atom::Ctor` so App-folding builds a tuple. Guard:
   `advanced_test.saga` "qualified constructor application" (+
   `tests/e2e/lib/QualCtorLib.saga`). Repro anchor:
   `examples/bugs/cross-mod-generic-fail`.

3. **Eta-reduced top-level function bindings emitted at LHS arity, not type
   arity** (surfaced in `saga_pgo`). `fun pg_text : String -> Value; pg_text =
   coerce_value` has LHS arity 0 but type arity 1, so the producer emitted
   `pg_text/2` while cross-module callers derive arity from the type and call
   `pg_text/3` → runtime `undef`. The old path had explicit eta-expansion at
   lowering ([`lower/mod.rs:1878-1903`](../../../src/codegen/lower/mod.rs#L1878-L1903)
   with this exact `pg_text` example in the comment); the new path was missing
   it.

   Fixed by adding eta-expansion at **elaborate** time so all downstream
   stages (resolve, ANF, translate, lower) see a normalized FunBinding with
   LHS arity matching the type. `Elaborator::new` precomputes
   `fun_declared_arities` from `result.env`'s schemes via
   `arity_and_effects_from_type`; the FunBinding arm synthesizes `___eta_N`
   `Pat::Var` params and wraps the body in curried `ExprKind::App` calls.

   Tests: `tests/e2e/tests/eta_reduction_test.saga` (12 cases — @external
   alias, 1/2/3-arg local aliases, polymorphic, HOF-passed, chained,
   in-module caller). Repro: `examples/bugs/eta-reduced-fun-binding/`.
   Verified `saga_pgo` runs end-to-end.

4. **Partial-app of a curried fn split via intermediate `let` bindings**
   (surfaced while writing eta-reduction tests; pre-existing, not eta-
   specific). `let one = three_args 1; let one_two = one 2; one_two 3`
   panicked with "function called with 3 argument(s), but expects 4".

   Two correct shapes are needed and the lowerer was honoring neither for
   opaque heads:
   - `(three_args 1) 2 3` — translator flattens nested Apps into one
     multi-arg App. Caller supplies 2 args to a 2-arg-missing lambda.
   - `((three_args 1) 2) 3` via lets — each intermediate is opaque; the
     caller can't see its arity through the resolution map.

   Fixed in two pieces:
   - `eta_expand_partial_app` keeps producing a single `missing+2`-arity
     lambda (the lambda's arity matches the remaining type's user-arg
     arity).
   - `head_atom_expected_user_args` gains a type-based fallback: for
     opaque heads, count arrows in `effect_info.type_at_node[head_id]` and
     treat under-saturated calls as a new partial-app. Each let-bound
     intermediate now eta-expands again with the correct (smaller) arity,
     producing an effective curried chain without us eagerly building one.

   Tests: `tests/e2e/tests/partial_application_test.saga` (15 cases,
   every split pattern across 2/3/4-arg curried fns + first-class use).
   Repros: `examples/bugs/partial-app-multi-step/{repro,multi-arg-suffix}.saga`.

## Phase-1 completion blockers (gate the optimization pass)

From a `panic!`/`unimplemented!`/`deferred` sweep of the new path:

- **RESOLVED — multi-arm-per-op `finally`** (was `effects.rs:956/971`). Reachable
  via inline `with` handlers (the named-handler path is blocked by the
  typechecker's duplicate-arm check, but inline handlers are not). Extracted the
  single-arm finally + abort-marker wrapping into `lower_captured_arm_body` and
  call it from both the single-arm and multi-arm paths. This also closed a latent
  gap: non-resuming multi-arm arms previously skipped abort-marker tagging, so
  they couldn't propagate aborts across nested `with` boundaries — they now match
  the single-arm aborting-arm shape. Regression: `effects_test.saga` "multi-arm-
  per-op arms each carry finally"; updated unit test
  `multi_arm_per_op_emits_single_closure_with_case`; repro
  `examples/bugs/multiarm-finally/`.
- **NOT a blocker — return-clause `finally`** (was `effects.rs:1027`). Unreachable:
  both parser paths (`decl.rs:708`, `expr.rs:708`) hardcode `finally_block: None`
  on `return` clauses, so a return clause can never carry a finally. The panic was
  replaced with a `debug_assert!` documenting the parser invariant.
- **NOT a blocker — nullary eta-reduced effect-op-as-value**
  (`translate/expr.rs::try_eta_reduced_effect_op_lambda`). Confirmed
  unreachable: the parser rejects 0-parameter effect-op declarations at parse
  time (`effect operation 'X' has no parameters; use 'fun X : Unit -> ...'`),
  and even synthetic test fixtures (`translate/tests.rs`) follow the
  convention. Non-nullary eta-refs are handled via a `(\arg0,...) -> Yield(op,
  arg0,...)` Lambda. The `param_count == 0 → return None` guard now carries a
  comment explaining the parser invariant and noting that the fallback to a
  direct `Yield` is the only safe behavior if it ever fires (a 0-param lambda
  would crash the lowerer). Verified end-to-end with a 1-arg eta-reference
  repro: `examples/bugs/nullary-eta-effect-op/unit-op.saga` (resumes twice
  through an aliased `beep!`, returns 14 = 7+7).
- **RESOLVED — cross-module effect-op panic** at `translate/mod.rs:230`.
  External project testing proved this was reachable: `effect_calls` could
  resolve `Std.Fail.Fail` while the per-module op table lacked the imported
  effect definition. `build_effect_ops_table` now merges
  `ModuleCodegenInfo::effect_defs`, and `emit_module_via_new_path` extends the
  table with the full codegen context before constructing `EffectInfo`.
- **RESOLVED — dynamic-handler return clauses end-to-end** plus two adjacent
  gaps surfaced during verification:
  1. **Parameter-passed handler values silently dropped evidence install.** A
     function parameter typed `Handler E` reached `lower_with_dynamic` with an
     empty `effects` list (the typechecker's `let_binding_handlers` only covered
     `let` bindings, not parameter NodeIds), so the `with` site bailed at the
     `effects.is_empty()` warning and `find_evidence` panicked at runtime.
     Typechecker (`check_decl.rs::check_fun_clauses`) now seeds
     `let_binding_handlers` from each `Pat::Var` parameter with `Handler E`
     type via `handler_info_from_type`; translator
     (`translate_decl::FunBinding`) reads them into `local_handler_effects` for
     the function body.
  2. **Multi-effect dynamic handlers panicked at lowering.** The runtime
     handler-value shape only carried one op tuple
     (`{__saga_handler_value, OpTuple, RuntimeReturn}`), so
     `lower_with_dynamic` had a `effects.len() != 1 → panic!("spec invariant")`
     guard. We do NOT delete language features: the shape generalized to
     `{__saga_handler_value, OpsByEffect, RuntimeReturn}` where `OpsByEffect`
     is a self-describing tuple of `{EffectAtom, OpTuple}` pairs in canonical
     alphabetical order. Both producers (`build_handler_value_tuple` in
     `atom.rs`, `lower_handler_value` in `exprs.rs`) share a new
     `build_ops_by_effect_tuple` helper. The consumer iterates the
     statically-known `effects` in the same canonical order and extracts each
     per-effect op tuple positionally — no runtime atom matching. Single-effect
     is a 1-element outer tuple, same path. See
     [`docs/effect-implementation.md`](../../effect-implementation.md) "Handler
     Bindings (Dynamic Handlers)" for the runtime shape spec.

  Regressions: `effects_test.saga` → "handler passed as function parameter" and
  "multi-effect handler value used dynamically"; updated unit test
  `with_dynamic_multi_effect_installs_evidence_per_effect` (flipped from the
  prior `should_panic` pin); repros under `examples/bugs/dynamic-handler-return/`
  cover conditional, factory, parameter-passed (single-effect), and multi-effect-
  parameter scenarios.

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
  `lower/app.rs` and first-class external wrappers in
  `lower/decls.rs` now both route through
  `util::lower_external_native_call`; callback-shaped `@external` params are
  detected with shared type helpers and adapted by the generated wrapper.
- **Handler `with` delimiter logic is duplicated.** `lower_with_static` and
  `lower_with_dynamic` both construct raw-result K, abort marker handling,
  evidence insertion, body wrapping, and outer-K forwarding. The dynamic path
  has extra handler-value extraction, but the delimiter should be one helper
  with mode-specific inputs.
- **Native handler bootstrap is becoming a second lowering language.**
  `lower/bootstrap.rs` now keeps static native effect metadata in a
  child module, but Ref/Vec and callback-invoking ops are still custom Core
  Erlang emitters. Prefer a small native-op DSL/descriptor plus focused escape
  hatches over more handwritten nested `CExpr` trees.
- **Record metadata is reconstructed from runtime tags.** Anonymous-record
  field order should come from structural metadata (`RecordInfo`/type info), not
  from parsing the encoded tag string in lowering.
- **Old-path helper copies should either become shared code or disappear with
  old path deletion.** `lower/util.rs` is an acceptable temporary clone
  because the agent guide forbids imports from `lower/`, but it should not grow
  new semantics independently.
- **Shape-heavy unit tests are useful but expensive.** `lower/tests.rs`
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
  the `lower::atom` panic is now unreachable. The two
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

### Stage 9: ANF — REVIEWED, clean

Contract:

- Full ANF over all expression positions.
- Does not cross lambda/branch/handler-arm boundaries.
- Preserves source `NodeId` on relocated expressions.
- Uses fresh IDs only for synthetic wrappers and variables.

Review outcome (this pass): **clean, no work needed.** All three load-bearing
properties hold:

- Nested contexts (handler-arm, lambda, case/receive arms, if-branches) each run
  their own `anf_expr` with a fresh bindings vec; bindings are not lifted across
  those boundaries (only `flatten_block_into` hoists, within one context).
- `NodeId` preservation: **there is no `rebuild_like` helper** (the old contract
  bullet was aspirational) — the discipline is followed by reusing the captured
  `id`/`span` on every structural rewrite; `NodeId::fresh()` appears only on
  synthetic App-spine nodes and let-binders.
- `Expr::synth` is used only for genuinely synthetic nodes (empty-block `Unit`,
  the replacement `Var` after lifting, the `finish` wrapper block), never
  wrapping a relocated source expression.

Anonymous-record field-order metadata (the earlier worry) was resolved in
Review Pass 4 (structural `anon_fields`), so the ANF path no longer risks
splitting field names.

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
- ~~`effects.rs` still contains deferred panics for `finally_block` on multi-arm
  op closures and return clauses.~~ Both resolved: multi-arm finally implemented
  via `lower_captured_arm_body`; return-clause finally shown unreachable
  (parser-enforced) and downgraded to `debug_assert!`.
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

- `stdlib_test_suite` is currently green.
- The hardcoded `external_callback_arg` table was removed. `@external`
  wrappers now derive callback adapters from function-typed source parameters,
  and saturated external calls with callback-shaped arguments route through the
  wrapper instead of the raw BIF/bridge target.

Review checkpoints:

- The adapter must be designed carefully for pure vs effectful callback types;
  only use the synchronous identity-K/direct-return adapter where the callback
  type is admitted as pure at that boundary.
- External-library shakedowns (`saga_json`, `saga_pgo`, `saga_http`) are useful
  guardrails because they exercise non-stdlib `@external` declarations.

### Review Pass 3: Application / Callable ABI

Scope:

- `src/codegen/lower/app.rs`
- callable value emission in `src/codegen/lower/atom.rs`
- callable definitions/wrappers in `src/codegen/lower/decls.rs`
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
- Saturated external calls and first-class external references now share
  `util::lower_external_native_call`; stdlib tests cover `List.sort_by` and
  `List.nth` through first-class references.
- External callback adapters use identity K and direct return. This is only
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
6. ~~Replace or document `external_callback_arg` as the phase-1 bridge table;
   add tests for any public bridge HOF not covered by stdlib/e2e.~~ Done by
   deriving callback adapters from `@external` function-typed parameters.
7. ~~Unify external wrapper lowering with saturated external-call lowering so
   callback-shaped externals route consistently whether called directly or
   through a first-class function reference.~~ Done via
   `util::lower_external_native_call` plus shared callback type helpers.
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
- Lowering in `src/codegen/lower/exprs_edge.rs`.
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
- `lower::exprs_edge` resolves field order from structural metadata:
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

- `src/codegen/lower/bootstrap.rs`
- Native handler installation from `lower/effects.rs`
- Native effect declarations in `src/stdlib/Actor.saga`, `Ref.saga`,
  `Vec.saga`
- Shape tests in `src/codegen/lower/tests.rs`
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
- Bootstrap comments that still mentioned “future step 8” were cleaned up
  after the metadata scan; the live bootstrap risk is now the explicit
  `not_implemented_native_op` stubs, not stale phase wording.
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

- `src/codegen/lower/effects.rs`
- `src/codegen/lower/exprs.rs::lower_resume`
- `src/codegen/lower/ctx.rs`
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
- ~~Multi-arm-per-op closures still panic when any arm has `finally_block`.~~
  RESOLVED. The source language *does* permit multi-arm-per-op via inline `with`
  handlers, so this was a real parity gap. Fixed by extracting the single-arm
  finally + abort-marker logic into `lower_captured_arm_body` and sharing it with
  the multi-arm path (which also gained abort-marker tagging for non-resuming
  arms — a latent gap). Verified to match single-arm behavior byte-for-byte on
  the `examples/bugs/multiarm-finally/` parity repro.
- ~~Return-clause `finally_block` also panics as deferred.~~ Confirmed
  unreachable: both parser paths hardcode `finally_block: None` on `return`
  clauses, so the invariant is enforced at parse time. Panic downgraded to a
  `debug_assert!`.
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

The slow path must be a complete oracle before the optimization pass (Stage 11)
starts. Remaining order:

1. **`finally` deferred-panics — DONE.** Multi-arm-per-op `finally` implemented
   via the shared `lower_captured_arm_body` helper; return-clause `finally` shown
   unreachable (parser hardcodes `None`) and downgraded to a `debug_assert!`. See
   "Phase-1 completion blockers" above for details.

2. **Dynamic-handler return clauses + multi-effect dynamic — DONE.**
   Verification surfaced two real bugs: parameter-passed handlers dropped
   evidence install (typechecker gap), and multi-effect dynamic handlers
   panicked at the lowerer. Both fixed; the runtime handler-value ABI was
   generalized — see "Phase-1 completion blockers" above and the ABI history
   note in [`docs/effect-implementation.md`](../../effect-implementation.md).

3. **Nullary eta-reduced-effect-op-as-value — DONE.** Confirmed unreachable
   from valid source (parser-enforced); comment tightened. See "Phase-1
   completion blockers" above.

4. **Re-pin the leftover shape tests — DONE.**
   - `alias_chase_let_h_is_static`: the assertion "let-binding emits no Bind"
     was the old path's structural invariant. The new path emits a Bind for
     the let (the HandlerValue is materialized in case it escapes as a
     runtime value) AND alias-chases correctly so the with-site is `Static`.
     Re-pinned to walk through the Bind and assert the semantic property
     (Static handler with the original arms) rather than the dead-code-
     emission detail.
   - `tail_recursive_apply_in_tail_position`: the assertion "recursive apply
     is not let-bound" pinned the old selective-CPS path's structural tail
     position. The new uniform-monadic path emits
     `let <V> = apply f(args, _Ev, _ReturnK) in case V of ...` — structurally
     non-tail, but BEAM's tail-call optimizer still handles it because the
     recursive call passes the outer `_ReturnK` directly (CPS-style tail
     call) and each case arm either tail-calls `_ReturnK` or returns the
     bound value. Re-pinned as a behavioral test: 10M iterations must
     complete without stack overflow.

5. **Keep using `~/projects/saga_json` as the shakedown corpus** after each
   change.

Done earlier: callable/ABI review (Pass 3), record metadata (Pass 4), native
bootstrap (Pass 5), finally/abort routing diagnosis + the marker and
qualified-constructor fixes, ANF review (clean). `@inline`/`InlineVal` removed.

**Phase-1 status: complete.** All blockers above resolved; full test suite
green (1094 lib + 102 codegen_integration + 373 e2e + 218 saga_json).
**Stage 11 (effect optimization) is unblocked** — the slow path is now a
complete oracle.

## Phase 2 Optimization Review

This is the starting read before implementing
[`effect-optimization-spec.md`](./effect-optimization-spec.md). The current
code in `src/codegen/monadic/effect_opt/mod.rs` has the right
`RunOptions { skip }` shape, so phase 2 can land as small optimizer increments
while preserving the slow-path oracle.

### Progress

- **Step 9 / bind-collapse — DONE.** The optimizer now runs a bottom-up
  fixpoint for `Bind(Pure(a), x, body) -> body[x := a]`. Substitution follows
  the lowerer's source-name variable identity, blocks on pattern-capture risk,
  and stays conservative around raw AST patterns whose bitstring sizes or
  nested expressions refer to the collapsed binder. Guard tests cover simple
  substitution, fixpoint chains, shadowing, and pattern-capture blocking.

- **Step 10 / Bind-to-Let promotion — DONE.** Remaining monadic binds whose
  value is recursively pure become `Let`, letting the lowerer emit direct
  value-position Core instead of threading the rest of the computation through
  a bind continuation. The purity predicate is deliberately conservative:
  structural pure forms promote; apps promote only from callee effect metadata
  or a closed-empty function type on the callee; `ForeignCall`, `With`,
  `Receive`, `Resume`, `HandlerValue`, and unknown apps stay monadic. The
  lowerer now has a `lower_pure_expr` path for the promoted pure subset; pure
  uniform-CPS calls are bridged through a local identity continuation.

- **Step 11 / tail-resumptive direct-call — DONE for the first conservative
  milestone.** `Yield` sites under an innermost static handler now inline a
  single matching `TailResumptive` arm, substitute supported op params, and
  rewrite `Resume(v)` to `Pure(v)`. The handler stack uses blocker frames for
  dynamic/native/composite handlers, resets at lambda and letfun bodies, and
  skips arms with `finally_block`, multi-arm op dispatch, nontrivial op
  patterns, `OneShot`, and `Multishot`. Native specialization is tracked
  separately and its first milestone is now complete.

- **Next checkpoint — acceptance/hardening.** Before adding another optimizer
  extension, follow
  [`acceptance-hardening.md`](./acceptance-hardening.md): repo validation,
  external shakedown, slow-path oracle checks, emitted-Core spot checks, and
  then choose one next track.

- **Native direct-call specialization — DONE for first milestone.** Details in
  [`native-direct-call-specialization.md`](./native-direct-call-specialization.md).
  Native metadata now lives in backend-neutral `codegen::native_effects`, and
  the optimizer rewrites simple first-order native yields to `ForeignCall`.
  It deliberately skips `PrependAtom` (Saga `Symbol` is not a runtime Erlang
  atom), `spawn`, Ref, Vec, dynamic, and composite handlers.

- **Abstraction cleanup — DONE for the current batch.** First low-risk
  extraction centralized the marked control-result protocol in
  `lower::util`: shared
  `ABORT_TAG` / `VALUE_RESULT_TAG`, foreign-control propagation arms, and
  "apply foreign control to K" arms; follow-up helper constructors now cover
  the common marked-control tuple/pattern shapes. Second extraction added a
  shared `identity_k` helper for synchronous Saga/native callback boundaries
  (`@external` callback adapters, `main` entry wrapper, Ref `modify`, and
  `spawn` thunk), and shared type helpers now drive `@external` callback
  detection from both the app and wrapper paths. Third extraction named the
  native op closure shell and not-implemented native-op stub constructor in
  `bootstrap.rs`; the static native effect table now lives in a child module,
  and the bespoke Ref/Vec store backends live in `bootstrap/stores.rs`.
  Fourth extraction factored finally cleanup sequencing into a shared
  `sequence_finally_then` helper, used by both `resume` cleanup and
  non-resuming arm cleanup. Fifth extraction unified the
  local-marker/foreign-control arm construction for result delimiters
  (`build_result_delimiter_k`, `wrap_with_result_delimiter_to_k`, and
  `wrap_with_result_delimiter_raw`). Sixth extraction moved native effect
  metadata to backend-neutral `codegen::native_effects` so bootstrap and the
  optimizer share one table. Behavior unchanged except for the intended native
  direct-call optimization; focused lowerer/effect/property/e2e checks stayed
  green.

### Recommended Implementation Order

1. **Build optimizer scaffolding first.**
   - Add the bottom-up/fixpoint walker and a real `skip` fast path.
   - Keep each rewrite individually togglable while developing, even if the
     public option stays one `skip` bit.
   - Add unit tests at the monadic IR level before enabling any rewrite in the
     full compiler path.

2. **Ship bind-collapse first — DONE.**
   - This is the safest rewrite: `Bind(Pure(a), x, body) -> body[x := a]`.
   - Substitute by `MVar` identity, not just source name. Pattern binders are
     still raw AST `Pat`s, so shadowing checks should be conservative where
     pattern-bound names can hide an `MVar`.
   - Treat lambda atoms carefully: construction is atomic, but substituting a
     lambda value carries free variables. The fresh-name discipline should make
     capture unlikely; the rewrite should still either enforce the invariant or
     alpha-rename on collision.

3. **Then Bind-to-Let promotion — DONE.**
   - Start conservative. Promoting too little is only slow; promoting an
     effectful expression is a miscompile.
   - `Pure`, structural record/tuple/operator forms, and apps whose callee has
     an empty effect row are the first useful targets.
   - Be careful with `ForeignCall`: the IR currently has module/function/args
     but no explicit purity flag. Unless the source annotation gives a reliable
     no-effect fact at the `source` node, default to "not pure" for the first
     pass.
   - A lambda body may yield and still be pure to *construct*; do not inspect
     through `Atom::Lambda` for construction-site purity.

4. **Leave direct-call for last — DONE for the conservative milestone.**
   - This is the only phase-2 rewrite with a real semantic footgun. It depends
     on `HandlerAnalysis::TailResumptive`, static handler resolution, innermost
     handler shadowing, and the final result-delimiter protocol.
   - The existing spec's core rule is still right for simple tail-resumptive
     arms, but it predates the phase-1 `finally` and marked-value-result
     repairs. Do **not** inline a handler arm with `finally_block` until the
     optimizer has explicit cleanup-preserving semantics. The safe first gate
     is: direct-call only when the selected arm has no `finally_block`.
   - Direct-call should skip `MHandler::Dynamic`, `MHandler::Native`, and
     `MHandler::Composite` at first. Native specialization is a separate
     optimization, not the first direct-call milestone.
   - Reset the static handler stack at lambda boundaries, as the spec says. A
     lambda can be invoked outside the lexical handler extent.

### Test Strategy

- Keep `run_with_options(..., skip: true)` as the always-correct baseline.
- For each rewrite, compare optimized vs. skipped output behavior on:
  - `tests/codegen_integration.rs`,
  - `tests/effect_property_tests.rs`,
  - `tests/e2e`,
  - stdlib tests,
  - `~/projects/saga_json`, and any external-lib shakedown corpus currently in
    use.
- Add focused IR tests for capture avoidance and handler-stack shadowing. The
  runtime suites are good at finding misroutes, but they are too coarse to pin
  optimizer invariants by themselves.

### Spec Updates Needed Before Direct-Call

- Extend `effect-optimization-spec.md` with a `finally_block` direct-call gate
  or a cleanup-preserving transformation.
- Spell out how direct-call interacts with the current marker/value-result
  delimiter protocol. The slow path now routes both abort tuples and
  `{value_result, marker, value}` tuples; optimized output must not bypass
  return clauses, cleanup, or foreign-abort propagation.
- Decide whether direct-native specialization belongs in this same pass or a
  later pass. The conservative answer is later.

## Commands Used For This Triage

```sh
git diff --stat main...HEAD
git diff --name-status main...HEAD
rg -n "crate::codegen::lower::|normalize::|call_effects::|TODO|panic!|unimplemented|not implemented|deferred|InlineVal" \
  src/codegen/anf src/codegen/monadic src/codegen/lower src/codegen/mod.rs src/codegen/resolve.rs
```
