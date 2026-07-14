# Authoritative Evidence ABI Planning

Status: proposed. A narrow lambda-boundary fix exists, but the compiler still
reconstructs evidence shape in several places. This plan turns that invariant
into explicit shared metadata without changing Saga semantics or the runtime
evidence representation.

## Goal

Make every CPS callable have one authoritative description of its evidence
calling convention, and make both callers and callees consume that same
description.

The redesign should eliminate bugs where:

- a caller constructs `{Repo, Rollback e}` but the callback body treats slot 1
  as `Rollback e` because it does not use `Repo`;
- a generic applied effect and its concrete instantiation accidentally become
  two slots, or two distinct concrete applications collapse into one;
- a partial application, adapter, imported callback, or stored function value
  is lowered using an inferred effect set that differs from its runtime ABI;
- evidence insertion and call reframing independently calculate incompatible
  slot orderings.

The central rule is:

> The effects a body performs are not necessarily the evidence ABI of the
> callable containing that body.

For example:

```saga
fun use_callback :
  (Unit -> Result a e needs {Repo, Rollback e, ..r})
  -> Result a e
  needs {Repo, ..r}

use_callback (fun () -> rollback! "stop")
```

The lambda performs only `Rollback String`, but its callback ABI is still:

```text
static slots: [Repo, Rollback<String>]
open tail:    yes
```

`Rollback` must therefore be read from slot 2.

## Non-goals

This is not a redesign of the runtime representation.

The following remain unchanged:

- one `_Evidence` tuple followed by `_ReturnK` in the CPS function ABI;
- the flat frame shape
  `{callee static prefix..., forwarded tagged tail...}`;
- `insert_canonical`, `insert_static`, `project_evidence`,
  `select_evidence`, `reframe_evidence`, and `append_tail`;
- static `element/2` lookup for known prefix slots;
- exact-tag and unique-family lookup in an unknown open tail;
- source syntax, type inference rules, handler semantics, and module privacy;
- caller-side selection for generic parameterized effects.

This plan also does not require replacing encoded applied-effect strings with a
new structured identity. That remains a useful later cleanup, but the current
stable `AppliedEffectKey` encoding is sufficient for this refactor.

## The current ambiguity

Several compiler structures currently carry overlapping pieces of effect
shape:

```text
CheckResult resolved types
ModuleCodegenInfo function effects
FunInfo effects / is_open_row / param_types
CallEffectInfo and CpsCallPlan
RuntimeFunctionShape and CpsShape
lambda_effect_context
EvidenceCtx and EvidenceLayout
```

They answer different questions, but the distinction is implicit:

| Concept | Question answered |
| --- | --- |
| Inferred effects | Which operations does this expression/body perform? |
| Callable evidence ABI | Which positional static slots does this callable accept? |
| Current evidence frame | What static prefix and open tail are in `_Evidence` here? |
| Call reframe plan | How is the current frame transformed for this callee? |

The recent rollback regression came from using inferred effects to answer the
callable-ABI question. The caller used the expected callback type while lambda
lowering used the narrower body-inferred row.

## Required invariants

The implementation should make the following invariants explicit and
debug-assertable.

1. Every CPS callable has exactly one `CallableAbi` at the point it is lowered.
2. The callable's body indexes `_Evidence` using that ABI, never an independently
   inferred effect set.
3. A callback value uses its expected slot type as the base ABI. Inferred
   effects may fill an open tail, but cannot remove expected static slots.
4. A named generic function has a symbolic declaration ABI. Each call has an
   instantiated target ABI that is position-compatible with the declaration.
5. A partial application inherits the compiled head's residual ABI. Its
   occurrence type cannot silently change its runtime convention.
6. An adapter states both its source ABI and target ABI.
7. A reframe selector list has exactly one selector for every target static
   slot, in target order.
8. Distinct concrete applications of one family remain distinct slots.
9. A generic and concrete spelling of one compatible applied effect represent
   one slot, not two.
10. A closed evidence frame has exactly its declared static slots. An open
    frame has that static prefix followed by an unknown tagged tail.
11. Handler insertion updates the runtime frame and its compile-time ABI through
    the same operation.
12. Cross-module callers consume the exported callable ABI rather than
    reconstructing it from source names or body behavior.

## Proposed data model

### Evidence ABI

```rust
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EvidenceAbi {
    /// Canonical positional prefix used by compiled static op lookups.
    static_slots: Vec<AppliedEffectKey>,
    /// Whether additional tagged entries may follow the static prefix.
    open_tail: bool,
}
```

Initially `AppliedEffectKey` can remain a type alias or newtype around the
existing canonical string encoding.

`EvidenceAbi` owns normalization and compatibility operations:

```rust
impl EvidenceAbi {
    fn closed(slots: impl IntoIterator<Item = AppliedEffectKey>) -> Self;
    fn open(slots: impl IntoIterator<Item = AppliedEffectKey>) -> Self;

    fn for_lambda_boundary(
        expected: &EvidenceAbi,
        inferred: &EvidenceAbi,
    ) -> EvidenceAbi;

    fn with_installed(&self, effect: AppliedEffectKey) -> EvidenceAbi;
    fn slot_for(&self, effect: &AppliedEffectKey) -> SlotResolution;
}
```

Fields should become private once migration permits it. Construction should
sort and deduplicate static slots according to the canonical ABI convention;
callers should not manipulate the vectors directly.

`for_lambda_boundary` follows these rules:

- start with every expected static slot;
- retain the expected open-tail bit;
- add inferred effects admitted through the open tail;
- collapse a generic/concrete same-family pair into one compatible slot;
- preserve two distinct concrete applications of the same family;
- retain openness inferred from the value when required by its compiled shape.

### Callable ABI

```rust
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallableAbi {
    user_arity: usize,
    evidence: Option<EvidenceAbi>,
}
```

`evidence == None` means the callable uses the direct/pure ABI. A present
`EvidenceAbi`, including an empty static prefix with an open tail, means the
callable takes `_Evidence` and `_ReturnK`.

This subsumes the ABI meaning currently spread across:

- `RuntimeFunctionShape::Pure` / `Cps`;
- `CpsShape.static_effects` / `is_open_row`;
- expanded-arity calculations;
- several ad hoc `has_effects || is_open_row` checks.

Intrinsic and native functions may remain separate `RuntimeFunctionShape`
variants, but the Saga-callable branch should contain a `CallableAbi`.

### Current runtime frame

```rust
struct EvidenceFrame {
    var: String,
    abi: EvidenceAbi,
}
```

This replaces the conceptual combination of `EvidenceCtx`, `EvidenceLayout`,
and a separate `is_open` flag. It is not a runtime object: it is lowering
metadata describing the Core variable named by `var`.

The distinction matters:

- `EvidenceAbi` describes a calling convention or frame shape;
- `EvidenceFrame` says which Core variable currently contains that shape.

### Declaration ABI and instantiated target ABI

A generic function is compiled once:

```saga
fun all : Query a -> List a needs {Repo db, ..r}
```

Its body has a symbolic declaration ABI:

```text
[Repo<$db>] + open tail
```

A concrete call may have this instantiated target ABI:

```text
[Repo<UsersDb>] + open tail
```

The two ABIs have compatible slot structure but different runtime labels. The
callee still indexes positionally; the caller selects and may relabel the
concrete entry. This distinction should be represented rather than hidden by
mutating one shape in place.

### Reframe plan

```rust
struct EvidenceReframePlan {
    target: EvidenceAbi,
    selectors: Vec<EvidenceSelector>,
    forward_tail: bool,
}

enum EvidenceSelector {
    StaticSlot {
        index: usize,
        relabel_as: Option<AppliedEffectKey>,
    },
    TailTag(AppliedEffectKey),
}
```

The mapping from a source `EvidenceAbi` to a target `EvidenceAbi` should live
in one pure helper:

```rust
fn plan_reframe(
    source: &EvidenceAbi,
    target: &EvidenceAbi,
) -> Result<EvidenceReframePlan, EvidenceAbiError>;
```

Lowering translates this plan into `project_evidence`, `select_evidence`, or
`reframe_evidence`. It should not repeat exact/family/position selection logic.

The first implementation may calculate the plan during lowering because a
local `with` changes the source `EvidenceFrame`. The important boundary is that
the calculation is centralized and consumes explicit source and target ABIs.
Once frame planning is fully represented in the pre-pass, plans that are
independent of local handler installation can be precomputed.

## Planning phase

Extend the existing call-effects pre-pass rather than adding another unrelated
AST walk. Its output becomes a broader effect-ABI plan:

```rust
struct PlannedEffectAbi {
    calls: HashMap<NodeId, PlannedCall>,
    function_values: HashMap<NodeId, CallableAbi>,
}

struct PlannedCall {
    classification: CallEffectKind,
    callee_abi: CallableAbi,
}
```

The existing `CallEffectMap` remains the authoritative answer to whether a
specific `App` is direct, closed CPS, or row-forwarded. The extension makes it
also authoritative for the target ABI.

The planner determines function-value ABIs for:

- direct lambdas in call arguments;
- let-bound lambdas using their binding type;
- lambdas stored in constructors, tuples, records, lists, and anonymous
  records;
- eta-reduced effect-operation references;
- partial applications;
- branch-selected function values;
- imported and re-exported callable references;
- handler callbacks with absorbed named effects and open tails.

Expected types flow from existing metadata:

- `FunInfo.param_types` for function arguments;
- resolved let-pattern types;
- constructor argument types;
- record field types;
- tuple/list element expected types;
- effect-operation parameter types;
- contextual result types for branches.

Each expression occurrence has a unique `NodeId`, so a lambda used in two
different contexts already appears as two AST occurrences. Adapters created by
lowering state source and target ABIs explicitly rather than overwriting the
planned source ABI.

## Lowering after the redesign

Lowering should become a consumer of planned facts:

```text
typecheck + finalized substitutions
                |
                v
effect ABI planner
  - declaration/call target ABIs
  - function-value ABIs
  - direct/CPS/row-forwarded classification
                |
                v
lowering
  - emit callable using its planned ABI
  - map current EvidenceFrame to callee ABI
  - emit Core Erlang bridge calls
```

Concrete responsibilities:

- `lower_lambda` reads `function_values[lambda.id]`; it does not derive static
  slot positions from body-inferred effects.
- top-level and local functions use their declaration `CallableAbi` for both
  arity and body evidence lookup;
- partial-app lowering uses the compiled head ABI and derives a residual
  callable ABI;
- adapters receive `source_abi` and `target_abi` explicitly;
- `evidence_op_lookup` calls `current_frame.abi.slot_for(effect)`;
- `lower_with` calls `current_frame.abi.with_installed(effect)` alongside the
  runtime insertion operation;
- call lowering obtains the target ABI from `PlannedCall` and invokes the
  centralized reframe planner;
- no lowering branch sorts or deduplicates effect names independently.

## Implementation phases

### Phase 0: Characterize and pin invariants

Before structural edits:

1. Keep the non-resuming rollback regression that exposed the unused-slot bug.
2. Add focused unit tests for lambda-boundary ABI merging:
   - unused expected slot before a used effect;
   - distinct concrete applications of one family;
   - generic/concrete compatible application;
   - expected open tail absorbing an inferred effect.
3. Add debug helpers that print source and target ABI labels in failures.
4. Record the invariant in `docs/effect-implementation.md`.

The current narrow `CpsShape::for_lambda_boundary` fix is the seed for this
phase. It should move onto `EvidenceAbi`, not survive as a parallel API.

Acceptance: no behavior changes beyond the targeted regression fix.

### Phase 1: Introduce `EvidenceAbi` and `EvidenceFrame`

1. Add `EvidenceAbi` with private normalization and slot-resolution helpers.
2. Make `CpsShape` contain or alias `EvidenceAbi` temporarily.
3. Replace `EvidenceCtx { layout, is_open }` with
   `EvidenceFrame { abi }` incrementally.
4. Route handler insertion and op lookup through `EvidenceAbi` methods.
5. Preserve the existing Core output and runtime bridge calls.

Temporary compatibility constructors are acceptable, but raw vector access
should be removed by the end of the phase.

Acceptance:

- emitted Core for representative closed/open examples is structurally
  unchanged;
- all effect property tests pass;
- no direct writes to evidence slot vectors remain outside `EvidenceAbi`.

### Phase 2: Make callable-value ABI planned metadata

1. Extend the call-effects output with `function_values`.
2. Record the contextual ABI for lambdas, eta-reduced operations, and partial
   applications.
3. Replace `lambda_effect_context` with a planned ABI lookup. A narrow scoped
   override may remain only for compiler-synthesized adapters, which must state
   source and target ABIs explicitly.
4. Make `lower_lambda` require a planned ABI for every CPS lambda.
5. Move partial-application residual-shape calculation into shared ABI logic.

Acceptance:

- no source lambda chooses its slot layout from effects used by its body;
- missing CPS lambda metadata produces an internal compiler error containing
  the lambda `NodeId`, resolved type, and expected context;
- stored, returned, destructured, and cross-module callbacks pass.

### Phase 3: Centralize caller-to-callee reframing

1. Add `plan_reframe(source, target)` and typed selector values.
2. Move exact match, generic/concrete compatibility, unique-family fallback,
   and ambiguity detection into that helper.
3. Change call lowering to translate `EvidenceReframePlan` into bridge calls.
4. Delete selector construction from `build_call_evidence_with`.
5. Use the same helper for closed projection, open reframing, and CPS adapters.

Acceptance:

- one implementation owns caller/callee slot mapping;
- selector count is asserted equal to target static-slot count;
- same-family ambiguity is reported before emitting Core when statically
  knowable;
- generic and concrete cross-module calls retain positional compatibility.

### Phase 4: Make call metadata authoritative end to end

1. Replace remaining `CallEffectInfo` effect-name vectors with a target
   `CallableAbi` or `EvidenceAbi` reference.
2. Export declaration ABI through `ModuleCodegenInfo` for imported and
   re-exported functions.
3. Ensure imported occurrence types provide the instantiated target ABI while
   exported metadata provides the compiled declaration ABI.
4. Remove lowering-time reconstruction from raw function types where planned
   metadata exists.
5. Include ABI-relevant metadata in module/cache fingerprints if cached
   interfaces persist it across builds.

Acceptance:

- same-file, imported, re-exported, dependency, and cold-build paths consume
  the same ABI representation;
- changing a public callable's evidence ABI invalidates dependent artifacts;
- lowering does not infer per-call effectfulness or target slot order.

### Phase 5: Delete compatibility paths and strengthen assertions

1. Remove the transitional `CpsShape` fields or rename the final type clearly.
2. Remove `EvidenceLayout` if it has become a wrapper with no independent
   invariant.
3. Remove direct `effects_from_type`/`arity_and_effects_from_type` calls used
   solely to reconstruct runtime ABI during lowering.
4. Add debug assertions at callable emission, op lookup, handler insertion,
   and call reframing boundaries.
5. Update the compiler overview and effect implementation documentation.

Acceptance: there is one documented construction path for callable evidence
ABI and one documented mapping path between evidence frames.

## Test matrix

Every row should have at least one BEAM end-to-end test. Cross-module tests
should use a cold build where module metadata is relevant.

| Dimension | Required cases |
| --- | --- |
| Used subset | unused first slot, unused middle slot, unused final slot |
| Handler behavior | resuming, non-resuming/abort, multishot |
| Row shape | closed, open tail, empty static prefix plus open tail |
| Applied effects | plain family, generic application, concrete application |
| Same family | generic/concrete one slot, two concrete sibling slots |
| Value form | direct lambda, let-bound, returned, ADT/record/list stored |
| Callable transform | partial application, pure/CPS adapter, CPS/CPS adapter |
| Handler interaction | insertion before/after static slot, exact shadowing |
| Higher-order depth | direct HOF, nested HOF, handler factory callback |
| Modules | same file, imported, re-exported, dependency cold build |
| Nominal identity | source effect and multiple `neweffect` slots remain distinct |

Important regression families include:

- `{Repo, Rollback e}` callback performing only `Rollback e`;
- `{Fail Int, Fail String}` with either slot unused by the callback body;
- generic `Rollback e` handler delivered to a concrete `Rollback String`
  callback;
- an open callback that receives a static handler prefix and captures an
  application-owned tail;
- a partial application whose occurrence row narrows but compiled head remains
  open;
- an imported handler factory returning callbacks or handlers that retain
  their evidence ABI;
- handler insertion into an already reframed open frame.

## Diagnostics and debug tooling

Internal errors should print ABI information in positional form:

```text
evidence ABI mismatch at lambda NodeId(1234)
  inferred effects:       [Rollback<String>]
  expected callback ABI:  [Repo, Rollback<String>] + ..tail
  planned callable ABI:   [Repo, Rollback<String>] + ..tail
  current caller frame:   [Repo, Log, Rollback<String>] + ..tail
  selectors:              [1, 3]
```

Extend the existing effect-shape trace rather than adding an unrelated debug
environment variable. Useful trace events are:

- callable ABI planned;
- lambda boundary merge;
- partial-application ABI inheritance;
- source-to-target reframe plan;
- handler insertion and resulting frame ABI;
- static op lookup and selected slot.

These traces should use canonical applied-effect identities and preserve
`NodeId`/module/function context.

## Cross-module and cache considerations

Cross-module correctness is part of the design, not a final verification step.

- Exported callable metadata must include declaration ABI, including symbolic
  applied-effect arguments and the open-tail bit.
- Imported occurrence types determine the instantiated target ABI at each call.
- A re-export must preserve the original declaration ABI and source module.
- Public/private status does not change ABI identity.
- Dependency builds must not fall back to family-only or body-inferred effect
  metadata.
- If `ModuleCodegenInfo` or interface fingerprints serialize ABI-relevant
  fields, the compiler/cache fingerprint must change with this refactor.
- The Core Erlang function arity remains unchanged, so no BEAM bridge protocol
  version bump is expected unless serialized compiler metadata changes.

## Risks

### Confusing set equality with positional compatibility

Two ABIs can mention compatible effects but still disagree about slot order.
All equality and mapping APIs must state whether they compare:

- exact applied identity;
- compatible generic/concrete identity;
- static slot sequence;
- unordered row membership.

Avoid generic helpers named only `matches` or `same_effect`.

### Same-family ambiguity

Family fallback is valid only when it identifies exactly one compatible slot.
It must not collapse `Fail Int` and `Fail String`. Generic/concrete collapse
belongs in a single compatibility helper with unit tests.

### Open-tail insertion

The static prefix of an open frame may be canonicalized, but the unknown tail
must not be globally sorted. `EvidenceAbi::with_installed` describes only the
known prefix; runtime `insert_static` preserves the tagged tail.

### Planner/lowering scope disagreement

Local `with` expressions change the source evidence frame during lowering.
Do not require the initial planner to precompute mappings that depend on a
handler value not yet in scope. Centralizing `plan_reframe` is sufficient; full
precomputation is optional.

### Synthesized adapters

Compiler-generated lambdas do not necessarily have source `NodeId`s. Their
constructors must require explicit source and target ABIs so they cannot fall
back to ambient inference.

## Recommended file ownership

- `src/codegen/runtime_shape.rs`
  - `EvidenceAbi`, `CallableAbi`, ABI compatibility and residual-shape logic.
- `src/codegen/call_effects.rs`
  - per-`NodeId` call classification and function-value ABI planning.
- `src/codegen/lower/evidence.rs`
  - `EvidenceFrame`, `EvidenceReframePlan`, selector planning, Core bridge
    emission helpers.
- `src/codegen/lower/function_values.rs`
  - consume planned function-value ABIs and emit explicit adapters.
- `src/codegen/lower/calls.rs`
  - consume planned target ABIs and reframe plans.
- `src/codegen/lower/effects/with.rs`
  - update runtime frame and ABI together during handler installation.
- `src/codegen/lower/effects/ops.rs`
  - static/tail op lookup through `EvidenceAbi::slot_for`.
- `src/typechecker/check_module.rs` / module codegen metadata
  - preserve exported declaration ABI inputs across module boundaries.

Exact module placement can change during Phase 1 if `runtime_shape.rs` becomes
too broad. The ownership boundary matters more than the filename: semantic ABI
planning must stay outside Core emission.

## Completion criteria

The redesign is complete when:

1. Every emitted CPS callable obtains its slot layout from one `CallableAbi`.
2. Every call maps a current `EvidenceFrame` to the callee target ABI through
   one reframe planner.
3. Lambda body inference cannot remove expected callback slots.
4. Partial applications and adapters state their ABI transformations
   explicitly.
5. Handler insertion updates runtime evidence and compile-time ABI together.
6. Imported and re-exported callables preserve declaration/instantiation ABI
   distinction.
7. No lowering code independently sorts effect names to decide callable slot
   positions.
8. The full same-module and cross-module test matrix passes on BEAM.
9. `docs/effect-implementation.md` describes the final ownership and runtime
   invariants.

## Recommended execution order

Phases 0 and the narrow rollback fix can ship immediately. Phases 1-3 form the
valuable core cleanup and should be implemented together or in consecutive
small commits. Phase 4 should land before declaring the work complete because
cross-module metadata is where same-file-only fixes tend to diverge. Phase 5 is
the deletion pass that prevents the old reconstruction paths from returning.

The runtime vector design does not need another spike. The implementation risk
is metadata ownership, and this plan addresses it by making callable ABI and
frame mapping explicit before changing any Core Erlang representation.
