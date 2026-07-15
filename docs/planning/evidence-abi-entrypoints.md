# Evidence ABI Entrypoint Inventory

Status: migration complete (P1-P5). This document began as the no-behavior-change
review checkpoint and is now the completed migration checklist for
[Authoritative Evidence ABI Planning](evidence-abi-planner.md). Completing this
work changed compiler ownership and fixed ABI regressions, but did not change
the public Saga API or flat runtime evidence tuple representation.

## How to Use This Inventory

The refactor must keep four concepts separate:

- **Declaration ABI**: the callable convention promised by a function's
  signature, before instantiation.
- **Instantiated target ABI**: the declaration ABI after applying the call
  site's substitutions.
- **Inferred body effects**: effects actually performed by an expression. This
  is useful for checking and optimization, but is not a callable ABI.
- **Current frame shape**: the evidence entries physically available at one
  lowering point.

Every row has one eventual owner:

- `EvidenceAbi`: normalized static slots, open-tail status, compatibility,
  installation, and slot resolution.
- `CallableAbi`: user arity plus an optional `EvidenceAbi`.
- `EvidenceFrame`: the Core variable currently carrying a particular
  `EvidenceAbi`.
- `EvidenceReframePlan`: the sole source-to-target selector mapping.
- Effect ABI planner metadata (`EffectAbiPlan` below): declaration ABIs,
  instantiated call ABIs, and contextual function-value ABIs keyed by
  `NodeId`.

Statuses are **Pending**, **Migrated**, and **Exempt**. An exempt entrypoint is
intentional and documented; it must not silently implement a parallel Saga
calling convention.

Migration phases are:

1. **P1 — frame representation**: introduce the shared ABI/frame vocabulary and
   replace ad-hoc frame state without changing emitted Core.
2. **P2 — function-value planning**: make every callable constructor consume a
   planned `CallableAbi`.
3. **P3 — reframing**: centralize selector construction in
   `EvidenceReframePlan` and remove duplicated slot arithmetic.
4. **P4 — cross-module metadata**: serialize, import, re-export, and fingerprint
   authoritative ABI metadata.
5. **P5 — compatibility removal**: delete reconstruction paths and retain only
   explicit exemptions.

## ABI Producers

| Current symbol / location | Semantic input | Current ABI responsibility | Target owner | Phase | Regression ownership | Status |
|---|---|---|---|---|---|---|
| `RuntimeFunctionShape::from_type` (`codegen/runtime_shape.rs`) | Resolved function type | Derives user arity and CPS evidence shape | `CallableAbi::from_type` | P1 | Basic same-file effectful calls; direct ABI unit tests | Migrated |
| `RuntimeFunctionShape::from_resolved_symbol` | Resolved symbol ABI plus instantiated occurrence type | Chooses the instantiated target shape over the retained declaration ABI | `EffectAbiPlan` declaration and instantiated target ABI | P4 | Qualified imported and re-exported calls | Migrated |
| `RuntimeFunctionShape::{cps_shape, expanded_arity}` | Runtime function shape | Converts semantic shape to Core arity | `CallableAbi` | P1 | Export and first-class function arity tests | Migrated |
| Former `CpsShape::for_lambda_boundary` (now `EvidenceAbi::for_lambda_boundary`) | Effect row at a lambda boundary | Normalizes static evidence slots and open-tail status | `EvidenceAbi` | P1 | `closed_lambda_in_open_hof_keeps_tail_shape_for_nested_handler_insertion` | Migrated |
| `CallEffectInfo` plus private `CallEffectKind` classification (`codegen/call_effects.rs`) | Call node, resolved target, inferred/declared type | Produces `Direct` or `Cps(CallableAbi)` and records expected callback shapes | `EffectAbiPlan` plus `CallableAbi` | P2/P4 | Applied-effect, HOF, and imported-call regressions | Migrated |
| Call-effect classification/population helpers (`populate_*`, `classify_*`) | Typed AST and resolution metadata | Populate call and function-value ABI facts keyed by `NodeId` | `EffectAbiPlan` | P2 | Planner tests for inferred/implementation/boundary separation and all call kinds | Migrated |
| `EffectAbiPlanner::plan_program` (`lower/function_values.rs`) | Declaration parameter/result types plus finalized expression types | Propagates closed versus open expected rows through calls, constructors/lists, tuples, records, branches, lets, handlers, and effect callbacks before Core emission, then the plan is frozen | `EffectAbiPlan.function_values[NodeId]` | P2 | Heterogeneous callback lists, record/ADT storage, open HOFs, applied effect callbacks | Migrated |
| Defining-module plan lookup for imported handlers/helpers | Imported body NodeId plus active semantic module | Reads callback/call facts from the producer's frozen plan without merging module maps | `EffectAbiPlan` per compiled module | P2/P4 | Imported public handler using private nested handler; nested public static helper | Migrated |
| Shape helpers (`lambda_head_shape`, `let_fun_sig`, `runtime_shape_from_*`) | Lambda/local binding context | Construct declaration and occurrence ABIs at planner producer boundaries | Shared `CallableAbi` construction | P2 | Local HOF and pattern-bound callback regressions | Migrated |
| `FunInfo` registration (`codegen/lower/mod.rs`, `lower/init.rs`) | Local/top-level declaration | Stores user arity, effects, and Core name | `CallableAbi` stored with symbol metadata | P1 | Same-file recursion and partial application | Migrated |
| `register_std_module_semantics`, `register_imported_exports`, `register_imported_module_local_funs` | `ModuleCodegenInfo` and imports | Consume authoritative exported and private-local declaration ABIs | Imported declaration `CallableAbi` | P4 | Cold dependency and qualified import tests | Migrated |
| `method_cps_shape` and dictionary method registration | Trait method scheme and impl method | Defines dictionary slot/hoist callable convention | `CallableAbi` in trait/dictionary metadata | P2/P4 | Dictionary callback and imported trait method tests | Migrated |
| `collect_codegen_info`, `ModuleCodegenInfo` (`typechecker/check_module/codegen_info.rs`) | Checked module environment and exports | Publishes declaration `CallableAbi` for local/private resolution and downstream lowering | Declaration `CallableAbi` map plus compiled-module `EffectAbiPlan` | P4 | Re-export and dependency regressions | Migrated |
| `build_imported_fun_scoped` (`codegen/resolve.rs`) | Import/re-export graph | Constructs canonical imported symbol identity retaining the origin `CallableAbi` | Symbol plus declaration `CallableAbi` | P4 | `qualified_open_row_call_prefers_canonical_fun_sig_over_local_bare_name` | Migrated |
| `hash_scheme` and interface fingerprinting (`cli/cache.rs`) | Exported schemes, constraints, and effect rows | Invalidates dependents when a public callable shape changes without redundantly hashing derived ABI metadata | Exported scheme fingerprint | P4 | Effect-row and dependent rebuild-plan tests | Migrated |

## Callable Constructors

| Current symbol / location | Semantic input | Current ABI responsibility | Target owner | Phase | Regression ownership | Status |
|---|---|---|---|---|---|---|
| Top-level function emission (`lower/module.rs`) | Declared function plus checked body | Emits user parameters and optional `_Evidence` parameter | `CallableAbi` | P1 | Same-file, exported, imported effectful functions | Migrated |
| Local `LetFun` lowering (`lower/exprs/blocks.rs`) | Planned local declaration and body | Emits local closure arity and evidence boundary | `EffectAbiPlan.declarations[NodeId]` | P1/P2/P5 | Local recursion and escaping local functions | Migrated |
| Source lambda lowering (`lower/exprs/dispatch.rs`) | Lambda node plus expected type | Chooses pure/CPS closure parameters and frame | `EffectAbiPlan[NodeId]` → `CallableAbi` | P2 | Open-row callback and stored callback regressions | Migrated |
| Dictionary slots and hoists (`lower/module.rs`, `lower/function_values.rs`) | Trait method/impl method | Builds callable dictionary values with the correct CPS arity | Dictionary `CallableAbi` | P2/P4 | Imported dictionary method shapes | Migrated |
| Partial applications (`lower/function_values.rs`) | Callee ABI and supplied arguments | Constructs residual closure and forwards evidence | Residual `CallableAbi` | P2 | `narrowed_partial_app_of_cps_function_in_widened_list`; `imported_open_partial_app_keeps_declared_static_effect_prefix` | Migrated |
| Dictionary method access | Method slot and expected function type | Turns a slot into a first-class callable value | Contextual `CallableAbi` | P2 | Dictionary access/call and stored function-value regressions | Migrated |
| Expected-boundary propagation | Expected function type | Supplies ABI context when the lambda body underdetermines its boundary | `EffectAbiPlan[NodeId]` | P2 | `open_row_callback_param_normalizes_function_value_shape` | Migrated |
| Expected types through calls, constructors, records, tuples, lists, lets, and patterns | Container/argument type | Preserves contextual function-value ABI through storage and destructuring | `EffectAbiPlan[NodeId]` | P2 | `open_row_pattern_bound_callback_forwards_static_prefix_and_tail`; escaping handler pair regression | Migrated |
| Lambda-head call lowering (`lower/calls.rs`) | Immediately invoked lambda | Plans both closure boundary and invocation | One planned `CallableAbi` | P2 | `lambda_head_open_row_call_forwards_evidence` | Migrated |
| Eta-reduced effect operations (`lower/function_values.rs`) | Effect operation used as a value | Builds CPS callable that captures/accepts the operation frame | Operation `CallableAbi` | P2 | Stored/returned effect-operation regressions | Migrated |
| Pure → CPS adapter | Source and expected callback ABIs | Adds an evidence argument without changing user arguments | Explicit adapter `CallableAbi` | P2/P3 | Closed callback passed to open HOF | Migrated |
| CPS → pure adapter | Source and expected callback ABIs | Discharges a known frame and removes evidence from the exposed value | Explicit adapter `CallableAbi` | P2/P3 | Narrowed partial application tests | Migrated |
| CPS → CPS adapter | Source and expected evidence ABIs | Reframes evidence across compatible callable boundaries, including open→open boundaries with different static prefixes | `CallableAbi` plus `EvidenceReframePlan` | P2/P3 | `closed_imported_function_in_open_hof_drops_tail_before_nested_handler`; open-prefix same/cross-module regressions | Migrated |
| Returned/stored handler factories | Result expression and captured frame | Builds first-class handler values without losing ambient evidence | Contextual `CallableAbi` and `EvidenceFrame` | P2 | Handler-factory and paired-handler regressions | Migrated |

## Frame Constructors and Mutations

| Current symbol / location | Semantic input | Current ABI responsibility | Target owner | Phase | Regression ownership | Status |
|---|---|---|---|---|---|---|
| `Lowerer.current_evidence: Option<EvidenceFrame>` initialization (`lower/mod.rs`) | Module lowering root | Represents absence/presence of an ambient frame | `Option<EvidenceFrame>` | P1 | ABI assertions at pure roots | Migrated |
| Top-level body assignment (`lower/module.rs`) | Function `EvidenceAbi` and `_Evidence` | Establishes declaration frame at function entry | `EvidenceFrame` from `CallableAbi` | P1 | Top-level applied-effect tests | Migrated |
| Local-function body assignment (`lower/exprs/blocks.rs`) | Local callable shape | Establishes local declaration frame | `EvidenceFrame` | P1 | Local HOF regressions | Migrated |
| Lambda body assignment (`lower/exprs/dispatch.rs`) | planned ABI and emitted parameter | Establishes contextual lambda frame | `EvidenceFrame` from planned lambda ABI | P1/P2 | Open-row callback regressions | Migrated |
| Eta-operation body assignment (`lower/function_values.rs`) | Planned operation ABI | Establishes frame for generated operation closure | `EvidenceFrame` | P1/P2 | Eta-operation regressions | Migrated |
| `with` body installation (`lower/effects/with.rs`) | Outer frame, handled effect, handler value | Inserts/replaces the handled slot and establishes body frame | `EvidenceAbi::plan_install` producing runtime strategy and target ABI together | P1/P3 | Applied-effect handler and nested-handler regressions | Migrated |
| Handler-arm outer-frame swap/restore (`lower/effects/with.rs`) | Captured surrounding frame | Makes the handler implementation run outside its own installed evidence | Explicit `EvidenceFrame` scope operation | P1 | Non-resuming rollback regression | Migrated |
| Effect-operation callback tails (`lower/effects/call.rs`) | Current frame and continuation | Captures the frame used when a handler resumes | `EvidenceFrame` capture metadata | P1/P2 | Callback slot-order and non-resuming regressions | Migrated |
| Direct HOF clear/restore (`lower/hof.rs`) | Runtime-native HOF callback | Prevents accidental Saga evidence capture in a direct path and asserts source user arity | Explicit exemption scope | P1/P5 | Direct-HOF ABI assertions and list/HOF regressions | Exempt |
| Imported static helper clear/restore (`lower/static_helpers.rs`) | Static helper body | Lowers helper in its defined non-ambient context and asserts the source callable ABI | Explicit exemption scope | P1/P4/P5 | Private nested helper and re-export regressions | Exempt |
| Former `lambda_effect_context` writes and reads | Expected callback/declaration/operation boundary | Previously a mutable side channel for the next generated lambda's ABI | `EffectAbiPlan[NodeId]` | P2 | All HOF and callback regressions | Migrated |

Handler installation has one essential distinction that must survive the
refactor. In an **open** frame, a unique bare/generalized family placeholder may
be specialized by an installed applied effect. In a **closed** frame, bare and
applied entries are distinct concrete runtime slots. `EvidenceAbi::install`
must encode that context; there must not be a context-free generic insertion
path. This preserves the current open-versus-closed installation fix.

## Frame Transforms and Runtime Bridges

| Current symbol / location | Semantic input | Current ABI responsibility | Target owner | Phase | Regression ownership | Status |
|---|---|---|---|---|---|---|
| `build_call_evidence_with` (`lower/calls.rs`) | Current layout and target call layout | Chooses exact reuse, family relabel, projection, tail selection, or empty frame | `EvidenceReframePlan::between` | P3 | Distinct `Fail Int`/`Fail String`, imported generic calls, open-row callbacks | Migrated |
| Adapter selector construction (`adapt_cps_function_value_to_expected_shape`) | Source and expected callback layouts | Executes the shared source-to-target selector plan | `EvidenceReframePlan::between` | P3 | CPS↔CPS adapter tests | Migrated |
| `find_evidence/2` (`evidence.bridge.erl`) | Runtime frame and tag | Dynamic open-tail lookup | Execution of an `EvidenceAbi::resolve_slot` result | P3 | `open_row_inner_handler_preserves_same_family_tail` | Migrated |
| `insert_canonical/2` | Frame and `{tag, handler}` entry | Installs/replaces canonical evidence while preserving ordering | Execution of `EvidenceAbi::plan_install` | P1/P3 | Nested applied handlers and non-resuming rollback | Migrated |
| `insert_static/3` | Frame, known static-prefix length, and handler entry | Installs into the canonical prefix without reordering an unknown tail | Execution of `EvidenceAbi::plan_install` | P1/P3 | Open handler insertion tests | Migrated |
| `select_evidence/2` | Frame and positional/tag selectors | Selects static entries and/or dynamic tags | `EvidenceReframePlan` execution | P3 | Cross-module applied effects selecting generic open slots | Migrated |
| `reframe_evidence/3` | Frame, source prefix/tail-forwarding plan, and selectors | Selects and retags entries into callee order, forwards closed-row extras that instantiate a target tail, and excludes omitted declaration slots from an already-open source | `EvidenceReframePlan` execution | P3/P5 | Same-family sibling-tail, Fail+Repo wrong-slot, and nested group/route regressions | Migrated |
| `append_tail/3` | Call frame, captured frame, and target ABI | Combines locally installed evidence with a caller tail | Target `EvidenceAbi` supplies the static labels | P1/P3 | Imported nested handler and open callback tests | Migrated |

All six bridge operations remain runtime implementation details. Lowering
must consume a typed plan and may not independently infer positions, ordering,
or relabeling from canonical strings.

## Consumers

| Current symbol / location | Semantic input | Current ABI responsibility | Target owner | Phase | Regression ownership | Status |
|---|---|---|---|---|---|---|
| `evidence_op_lookup` | Effect identity and current layout | Chooses static slot or open-tail lookup | `EvidenceAbi::resolve_slot` | P1/P3 | Same-family applied effects and ambiguity diagnostics | Migrated |
| `evidence_op_index` | Effect operation and selected handler | Chooses operation tuple index | Handler declaration metadata, not frame arithmetic | P1 | Multi-operation effect tests | Exempt |
| `lower_runtime_cps_apply` | Callable and argument list | Applies runtime CPS values with planned evidence and continuation | `CallableAbi` | P2/P3 | Stored/returned callback and handler-factory tests | Migrated |
| Resolved, qualified, local, and imported call lowering (`lower/calls.rs`) | Planned call target | Emits user args, target evidence, and continuation | Planned `CallableAbi` plus `EvidenceReframePlan` | P2/P4 | Same-file, cross-module, re-export, dependency tests | Migrated |
| Variable and field-access calls | Contextual function value | Determines whether and how evidence is passed | `EffectAbiPlan[NodeId]` | P2 | Pattern-bound and record-stored callback tests | Migrated |
| Dictionary calls | Trait/dictionary method ABI | Applies a method slot with its declared CPS convention | Dictionary `CallableAbi` | P2/P4 | Imported trait method tests | Migrated |
| Effect-operation calls (`lower/effects/call.rs`) | Applied effect identity and current frame | Resolves handler, builds continuation, forwards captured evidence | `EvidenceAbi` plus operation `CallableAbi` | P1/P2 | Applied effect, nested handler, and rollback tests | Migrated |
| Export arity (`lower/module.rs`, `lower/init.rs`) | Public declaration | Exposes expanded Core arity | Exported `CallableAbi` | P4 | `imported_effectful_function_value_uses_cps_expanded_arity` | Migrated |
| Trace labels, debug output, and internal ABI errors | Planned/current shape | Explain mismatch using the same authoritative model | `CallableAbi` / `EvidenceAbi` assertions | P1-P5 | Planner unit tests and callable/adapter assertions | Migrated |

`arity_and_effects_from_type`, `has_open_effect_row`, `effects_from_type`, and
`expanded_arity` are legitimate inputs at authoritative producer boundaries.
They count as unclassified reconstruction if lowering uses them after a
`CallableAbi` already exists. P5 should leave only authoritative producers and
unrelated typechecker uses.

## Explicit Exemptions

| Current symbol / entrypoint | Semantic input | ABI responsibility / invariant | Target owner | Phase | Regression ownership | Status |
|---|---|---|---|---|---|---|
| Handler-arm closures (`lower/effects/handlers.rs`, `lower/effects/with.rs`) | Operation arguments and resumption | Runtime protocol closures use `(operation arguments..., K)`; they are not Saga source callables and never gain `_Evidence` implicitly | Handler protocol ABI | P1 | Resuming and non-resuming handler tests | Exempt |
| Runtime handler tuples | Effect declaration and lowered arms | Store handler operation closures in declaration order; tuple layout is not callable evidence layout | Handler declaration metadata | P1 | Multi-operation and nested-handler tests | Exempt |
| Intrinsics (`lower/builtins.rs`) | Registered intrinsic call | Own an explicit native callback convention; contextual planning does not replace it with a generic declaration row | Intrinsic registry | P5 | `qualified_std_process_catch_panic_lowers_as_intrinsic`; test-build console-handler regression | Exempt |
| External functions | Foreign declaration and arguments | Preserve the foreign target ABI; any effectful Saga wrapper still receives a normal `CallableAbi` | Foreign-call metadata plus wrapper `CallableAbi` | P2 | Existing external-call tests; add effectful-wrapper assertion | Exempt |
| BEAM-native direct paths | Native effect declaration | Bypass CPS only where declared by effect metadata; surrounding Saga values still use planned ABI | Native-effect metadata | P5 | Actor/Process native-effect tests | Exempt |
| Static helper variants (`lower/static_helpers.rs`) | Imported generated helper | Use a dedicated direct ABI recorded at construction and import boundaries | Static-helper ABI record | P4 | Private nested helper and re-export tests | Exempt |
| Direct HOF variants (`lower/hof.rs`) | Runtime-native HOF and callback | Use a fixed direct callback ABI and assert that no Saga frame is silently captured | Direct-HOF ABI record | P2 | Existing list/HOF tests; add per-variant ABI assertions | Exempt |
| Pure constructors and pure adapters | Constructor fields or pure callable | Represent purity explicitly as `CallableAbi.evidence = None` rather than as missing contextual state | `CallableAbi` | P2 | Constructor storage and pure-adapter tests | Exempt |

## Direct `_Evidence` Emission Index

This is the explicit accounting for the final completeness search. Line numbers
are intentionally omitted because the migration will move them; file and
constructor ownership are stable.

| Current location | Semantic input | ABI responsibility | Target owner | Phase | Regression ownership | Status |
|---|---|---|---|---|---|---|
| `lower/module.rs` | Top-level or dictionary declaration ABI | Emit single-clause, multi-clause, eta-expanded, and dictionary method parameters/calls | `CallableAbi` / `EvidenceFrame` | P1/P2 | Export arity and dictionary tests | Migrated |
| `lower/exprs/blocks.rs` | Local declaration ABI | Emit local single-clause and multi-clause function parameters and frame variable | `CallableAbi` / `EvidenceFrame` | P1 | Local recursion/HOF tests | Migrated |
| `lower/exprs/dispatch.rs` | Planned source-lambda ABI | Emit lambda evidence parameter and establish its frame | `CallableAbi` / `EvidenceFrame` | P1/P2 | Callback/frame preservation tests | Migrated |
| `lower/calls.rs` | Residual partial-application ABI | Emit closure parameter and forwarded evidence argument | `CallableAbi` | P2 | Partial-application regressions | Migrated |
| `lower/function_values.rs` | Adapter or eta-operation ABI | Emit adapter/operation parameter, selector source, and forwarded argument | `CallableAbi` / `EvidenceReframePlan` | P2/P3 | Adapter and stored operation tests | Migrated |
| `lower/evidence.rs` tests | Synthetic test frame | Exercise bridge-expression construction without defining a production callable ABI | Six runtime bridge implementations | P3 | Bridge unit tests | Exempt |

## Regression Ownership

Existing tests attach to the matrix as follows:

- Same-file/applied effects:
  `inline_handler_specializes_open_row_parameterized_effect_slot`,
  `distinct_applied_fail_effects_coexist`, and
  `nested_handler_replaces_only_matching_applied_effect`.
- Cross-module/re-export/dependency:
  `cross_module_neweffects_have_distinct_evidence_slots`,
  `cross_module_applied_effects_select_generic_open_row_slots`,
  `imported_nested_handler_specializes_callback_effect_and_preserves_open_tail`,
  `reexported_handler_factory_can_use_private_nested_factory`, and
  `qualified_imported_static_handler_passed_as_value_runs_on_beam`.
- Handler factories and escaping values:
  `applied_effect_handler_factory_coexists_with_sibling_application`,
  `imported_handler_factory_captures_nested_open_row_callback_evidence`, and
  `effectful_handler_factory_results_escape_together_as_first_class_values`.
- Callback/frame preservation:
  `callback_layout_keeps_unused_effect_before_nonresuming_effect_slot`,
  `closed_lambda_in_open_hof_keeps_tail_shape_for_nested_handler_insertion`,
  `closed_imported_function_in_open_hof_drops_tail_before_nested_handler`,
  `nested_cross_module_open_hofs_drop_handled_static_prefix`,
  `open_cps_function_value_reframes_a_different_static_prefix`,
  `cross_module_open_cps_function_value_reframes_a_different_static_prefix`,
  `open_row_callback_param_normalizes_function_value_shape`, and
  `open_row_pattern_bound_callback_forwards_static_prefix_and_tail`.
- Partial application:
  `narrowed_partial_app_of_cps_function_in_widened_list`,
  `narrowed_cps_partial_app_passed_to_open_row_param`, and
  `imported_open_partial_app_keeps_declared_static_effect_prefix`.

The final migration added or retained coverage for:

1. scheme/interface fingerprint changes when an exported callable's effect row
   or open-tail bit changes, plus dependency fingerprint/rebuild-plan tests;
2. planner unit cases for exact reuse, relabel, unique tail lookup, ambiguous
   family lookup, and missing evidence;
3. ABI assertions for every adapter, static-helper, and direct-HOF variant; and
4. closed projections that omit the first, middle, and last static slot.

## Completeness Audit

Run these searches after every migration phase:

```sh
rg -n 'CpsShape \{|CpsShape::|RuntimeFunctionShape::' src/codegen --glob '*.rs'
rg -n 'EvidenceLayout::|EvidenceCtx \{|lambda_effect_context|current_evidence\s*=' src/codegen --glob '*.rs'
rg -n 'arity_and_effects_from_type|has_open_effect_row|expanded_arity|effects_from_type' src/codegen src/typechecker/check_module src/cli/cache.rs --glob '*.rs'
rg -n 'build_call_evidence_with|evidence_op_lookup|insert_canonical|insert_static|select_evidence|reframe_evidence|append_tail|find_evidence' src/codegen src/stdlib --glob '*.rs' --glob '*.erl'
rg -n '"_Evidence"\.to_string\(\)' src/codegen/lower --glob '*.rs'
```

Final audit (2026-07-15): `RuntimeFunctionShape`, `CpsShape`, `EvidenceLayout`,
`EvidenceCtx`, and `lambda_effect_context` have zero hits. Every remaining
`current_evidence` assignment is one of the frame scopes above. Remaining raw
type/effect extraction occurs only at ABI producer boundaries or for semantic
HOF absorption metadata; lowering consumers use `CallableAbi` and
`EffectAbiPlan`. Every runtime bridge call and direct `_Evidence` emission is
classified above. There are zero unclassified semantic entrypoints.

## Migration Order

1. Introduce `EvidenceAbi`, `CallableAbi`, and `EvidenceFrame`; migrate every
   `EvidenceCtx` assignment and direct `_Evidence` emission without changing
   Core output.
2. Populate `EffectAbiPlan` for declarations, calls, lambdas, partial
   applications, dictionary values, eta operations, and adapters.
3. Introduce `EvidenceReframePlan`; switch calls, adapters, handler insertion,
   projection, and tail forwarding to it.
4. Export, import, re-export, and fingerprint callable/evidence ABI metadata;
   exercise cold dependency builds.
5. Delete compatibility reconstruction and mutable contextual side channels,
   then rerun the completeness audit and all attached regressions.
