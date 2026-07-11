# Parameterized Effect Evidence

Status: implemented (Phases 0-4 and core documentation). Explicit inline
disambiguation syntax remains deferred.

## Goal

Allow distinct applications of the same effect family to coexist in one effect
row and at runtime:

```saga
fun load_both : Unit -> Result User DbError
  needs {Repo UsersDb, Repo DataDb}

fun validate : Unit -> Unit
  needs {Fail String, Fail Int}
```

The runtime identity of an effect slot becomes the fully applied effect, not
only its family name:

```text
Repo UsersDb != Repo DataDb
Fail String  != Fail Int
```

This is structural distinction. It does not replace nominal effects:

```saga
neweffect PrimaryRepo = Repo UsersDb
neweffect AuditRepo = Repo UsersDb
```

`PrimaryRepo` and `AuditRepo` remain distinct even though their source
applications are identical. Parameterized evidence alone cannot represent two
independent instances of exactly `Repo UsersDb`.

## Current state

The typechecker is already partly prepared:

- `EffectEntry` stores a canonical family name and `Vec<Type>` arguments.
- `EffectRow::merge` and substitution application can retain distinct concrete
  instantiations.
- `EffectEntry::same_instantiation` and `EffectRow::subtract_entries` already
  exist.
- `infer_with` recovers the concrete handled entry and pins an inline arm's
  operation parameters to it.

The current single-slot rule is nevertheless enforced in several places:

- effect-row joins unify entries by family;
- function-boundary checking unifies all uses of a family against one declared
  entry;
- one inline `with` layer rejects multiple instantiations of a family;
- handler metadata records handled families as `Vec<String>`;
- codegen metadata erases effect arguments.

The codegen boundary is where the information is comprehensively lost:

```text
CheckResult.fun_effects                 HashMap<String, HashSet<String>>
CheckResult.let_effect_bindings         HashMap<String, Vec<String>>
ModuleCodegenInfo.fun_effects           Vec<(String, Vec<String>)>
RuntimeFunctionShape.static_effects     Vec<String>
CallEffectInfo / CpsCallPlan            family-name-based
EvidenceLayout                          Vec<String>
```

Consequently both `Fail String` and `Fail Int` become the evidence tag
`Std.Fail.Fail`.

## Core design

### Applied effect identity

Introduce a shared semantic/codegen representation rather than encoding
applications into ad hoc strings:

```rust
struct AppliedEffect {
    family: String,
    args: Vec<Type>,
}
```

The exact ownership and serialized form can be decided during Phase 1. Required
properties:

- family names and type constructors are canonical and module-qualified;
- equality is structural after substitution;
- concrete applications have a stable cross-module runtime tag;
- applications containing type variables remain structured compiler metadata;
- diagnostics use Saga syntax (`Fail String`), not the runtime encoding.

Suggested concrete runtime tag examples:

```text
Std.Fail.Fail<Std.Base.String>
Std.Fail.Fail<Std.Base.Int>
Kraken.Query.Repo<MyApp.UsersDb>
```

The spelling is an internal ABI detail. A length-prefixed or structured Erlang
term is acceptable if string encoding becomes ambiguous.

### Caller-selected evidence

A generic function does not need a runtime type witness merely because its
effect argument is polymorphic:

```saga
fun all : Query a -> Result (List a) DbError needs {Repo db}
```

At every call, type inference has instantiated `db`. The caller selects the
matching evidence entry and passes a callee-shaped evidence value:

```text
caller has: Repo UsersDb, Repo DataDb
call all where db = UsersDb
callee receives its selected Repo UsersDb slot
```

For a closed row, `all` continues to use a static tuple index. It does not need
to know that `db` is `UsersDb` at runtime.

This selection must use the typechecker's call-site substitution. It must not
be reconstructed from source spelling in the lowerer.

### Closed-row layout

Closed rows are the simplest complete path:

1. The call classifier records the instantiated `AppliedEffect` requirements.
2. The caller maps each callee requirement to an entry in its current evidence
   layout.
3. The caller projects/reorders those entries into the callee's declared static
   layout.
4. The callee performs ordinary static `element/2` lookup.

The entry may remain tagged for diagnostics, but the callee's operation lookup
does not depend on knowing a concrete type-variable substitution.

### Open-row layout

The current rule for `RowForwarded` is to pass the ambient globally canonical
vector unchanged. That is insufficient when a generic static prefix must
select one of several applications:

```saga
fun all_open : Query a -> Result (List a) DbError
  needs {Repo db, ..r}
```

The ABI spike selected a flat evidence vector rather than separate static and
forwarded components:

```text
Evidence = {CalleeStaticSlots..., UnselectedCallerEntries...}
```

- The positional prefix contains caller-selected handlers for the callee's declared
  effect entries. Static operations use indexes.
- The remainder carries effects abstracted behind row variables. Runtime lookup in
  the tail uses concrete applied tags.
- A polymorphic caller can forward one of its own static slots to a callee by
  position; it still needs no runtime type representation.
- A concrete effect selected from the tail is found by its fully applied tag.

`std_evidence_bridge:reframe_evidence/3` builds this shape from positional or
applied-tag selectors and appends every unselected caller entry. This retained
the existing flat CPS ABI and passed the following cases:

- `{Repo db, ..r}` called with two repository applications in scope;
- a polymorphic caller forwarding `Repo db` to another polymorphic callee;
- open-row callbacks whose concrete effects are hidden behind `..r`;
- nested `with` shadowing one exact application without replacing siblings;
- multiple static applications of one family, such as
  `{Fail String, Fail Int, ..r}`;
- first-class CPS functions and partial applications;
- cross-module calls without specialization.

## Operation and handler disambiguation

### Effect operations

Qualification by family remains useful:

```saga
Fail.fail! value
```

If only one `Fail a` is compatible with the operation arguments and expected
result, inference selects it. If several applications remain compatible, the
call is ambiguous and must be ascribed or otherwise constrained.

The resolution result for an effect call must identify an `AppliedEffect`, not
only its family. For a polymorphic call this may contain type variables linked
to the enclosing function's type.

### Inline handlers

A bare inline arm can be inferred from the wrapped expression when that
expression has exactly one matching application:

```saga
read_user () with {
  fail message = recover message
}
```

If `read_user : Unit -> User needs {Fail String}`, the effect row at the
`with` site already identifies `Fail String`, even when `read_user` is defined
in another module. No body search is needed.

If the wrapped expression contains both `Fail String` and `Fail Int`, this is
ambiguous:

```saga
work () with {
  fail value = recover value
}
```

Do not select an application by speculatively typechecking the arm against each
candidate. That gives poor behavior for ignored parameters and makes handler
selection depend on distant body constraints.

Existing explicit syntax can always express the choice:

```saga
let string_fail = handler for Fail String {
  fail message = recover message
}

work () with string_fail
```

Proposed direct-inline sugar:

```saga
work () with {
  for Fail String {
    fail message = recover message
  },
  for Fail Int {
    fail code = recover_code code
  }
}
```

This groups every operation of the selected application and composes naturally
with the existing nested-handler desugaring. The syntax is a separate phase;
the evidence feature need not wait for it.

Initial inference rule:

1. Resolve an explicit effect application when provided.
2. Otherwise collect matching applications from the wrapped expression's
   inferred row.
3. Unify compatible duplicates.
4. Select exactly one candidate or report an ambiguity listing the applied
   effects and the explicit-handler workaround.

One inline layer handles one exact application. It must not subtract every
entry sharing the family name.

## Implementation phases

### Phase 0 — ABI spike and decision gate

Build focused compiler/unit prototypes for these shapes without changing the
surface type rules:

1. Closed generic `Repo db` selected from two concrete repositories.
2. Open `{Repo db, ..r}` with the unselected repository still in the tail.
3. Generic-to-generic forwarding across modules.
4. Open-row callback carrying an effect not named by the wrapper.
5. Nested replacement of `Fail String` while preserving `Fail Int`.

Compare:

- split `{StaticSlots, OpenTail}` frame;
- a flat callee-shaped vector with a statically addressed prefix and tagged
  tail.

Decision criteria:

- no runtime type witnesses;
- no function specialization requirement;
- static named effects retain constant-time lookup;
- open tails retain correct forwarding semantics;
- runtime CPS values have one documented representation;
- reasonable migration from the current evidence ABI.

Decision: use the flat callee-shaped vector. A split `{StaticSlots, OpenTail}`
frame was not needed, including for nested exact handlers and first-class
callbacks.

### Phase 1 — Preserve applied effects through metadata

Replace family-only collections with applied identities through:

- `CheckResult`;
- `ModuleCodegenInfo` and re-export/origin metadata;
- backend resolution and `FunInfo`;
- `RuntimeFunctionShape`;
- `CallEffectInfo`, `CpsCallPlan`, and `OpKey`;
- let/pattern-bound effectful callable metadata;
- handler metadata;
- evidence-layout bookkeeping.

Keep emitted Core behavior unchanged temporarily by explicitly projecting
`AppliedEffect.family` at the old boundary. Add debug assertions showing where
two applications would collapse. This separates information preservation from
the ABI cutover.

Acceptance:

- metadata tests observe both `Fail String` and `Fail Int` distinctly;
- applied identities survive imports and re-exports;
- existing programs emit equivalent Core;
- no new string parsing is introduced in lowering.

### Phase 2 — Typechecker multi-instantiation semantics

Change family-based row behavior to exact-instantiation behavior:

- row join keeps incompatible concrete applications rather than unifying them;
- compatible variables may still unify when they denote the same application;
- declared-row checking matches body entries to compatible declared entries;
- ambiguous matching reports all candidates;
- subtraction removes only the selected application;
- duplicate-handler and unnecessary-handler diagnostics render type arguments.

Retain rejection for two indistinguishable copies of the exact same applied
effect. Named instances or `neweffect` are required for that case.

Acceptance tests:

- `{Fail String, Fail Int}` typechecks;
- two operations infer their correct payload/result types;
- a missing application is reported precisely;
- ambiguous polymorphic applications fail rather than choosing by order;
- same-family applications compose through if/case/list row joins;
- all cases work across modules.

### Phase 3 — Closed-row caller selection

Implement the complete closed-row runtime path:

- emit stable concrete applied tags;
- instantiate callee requirements at each call site;
- map them to caller slots using semantic type equality/unification facts;
- project and reorder evidence into the callee layout;
- index operations positionally in the callee;
- insert/replace handlers by exact application;
- update handler values, partial applications, and dynamic CPS calls.

Acceptance tests must execute on BEAM:

- `Fail String` and `Fail Int` coexist and are handled separately;
- `Repo UsersDb` and `Repo DataDb` dispatch to different handlers;
- generic `all : ... needs {Repo db}` selects each repository from the same
  caller scope;
- nested exact-application shadowing preserves the sibling application;
- imported functions and handlers use identical tags/layouts on cold builds.

### Phase 4 — Open rows and callbacks

Cut over to the evidence-frame ABI selected in Phase 0:

- construct callee static slots from caller slots/tail;
- forward the open tail without losing unrelated applications;
- adapt open-row operation lookup;
- update evidence insertion and projection bridges;
- update runtime CPS closures, callback adapters, HOF specialization, partial
  application, and handler factories;
- publish the required shape in cross-module codegen metadata.

Acceptance matrix:

- `{Repo db, ..r}` with another `Repo` application in `..r`;
- multiple independent row tails;
- callback absorption and forwarding;
- callback stored in ADTs/records/lists where currently supported;
- direct and dynamic handlers;
- abort, resume, multishot, return, and finally;
- BEAM-native effects mixed with parameterized user effects;
- all variants across module and re-export boundaries.

### Phase 5 — Inline disambiguation syntax

Add the selected explicit syntax, formatter support, syntax reference, website
grammar, VS Code grammar, parser recovery, LSP symbols/navigation, and
diagnostics.

Until then, named/anonymous handler expressions provide the explicit form.

### Phase 6 — Documentation and cleanup

- Update `docs/effect-implementation.md` with applied identities and the final
  evidence frame.
- Update the language guide and syntax reference.
- Remove the old single-family conflict diagnostics.
- Remove temporary family-only compatibility projections and debug assertions.
- Document the boundary between applied effects, `neweffect`, and future named
  instances.

## Test matrix

At minimum, cover:

| Dimension | Cases |
| --- | --- |
| Application | concrete/concrete, concrete/generic, generic/generic |
| Row | closed, static prefix plus open tail, multiple tails |
| Handler | named static, inline, handler expression, captured dynamic |
| Control | resume, abort, multishot, return, finally |
| Value shape | direct call, partial app, function value, callback |
| Module | same file, direct import, alias, re-export, cold dependency build |
| Identity | two args of one family, exact duplicate, two `neweffect`s |
| Native mix | user effect plus Actor/Ref/Timer |

Property tests should assert observable dispatch, not only emitted text. Core
assertions should additionally verify that distinct applied entries are present
and that generic callees use positional static slots.

## Risks

### Scope

The type representation is ready enough that the feature can look smaller than
it is. Most work sits in the codegen metadata and evidence ABI, which touches
call classification, function values, handlers, and cross-module compilation.

### Type-variable identity across modules

Raw `Type::Var` IDs are compiler-local and must never enter stable runtime tags
or serialized module ABI. Cross-module metadata must express variables relative
to a function/effect scheme, or keep the structured scheme needed to instantiate
them at the caller.

### Ambiguous matching

Matching by family and taking the first compatible entry is unsound. Every
selection point needs a unique applied-effect match or a diagnostic.

### ABI transition

Changing evidence shape must invalidate stdlib and dependency artifacts. A
compiler fingerprint should already force this, but cold dependency builds are
required acceptance tests.

### Optimization assumptions

Static-handler and direct-HOF optimizations currently use family-name lists.
They must consume applied identities or conservatively fall back. Correctness
paths should land before re-enabling any optimization whose proof does not
distinguish applications.

## Quick evaluation: should we do it now?

Proceed directly if the Phase 0 spike demonstrates all of the following:

- the open-row frame works without runtime type witnesses or specialization;
- caller-to-callee slot mapping is available from existing inference metadata;
- callback/function-value representation needs adaptation, not a second CPS
  calling convention;
- applied metadata can replace `Vec<String>` incrementally;
- the closed-row phase can land with strong tests before the open-row cutover.

Pause after the spike if:

- open callbacks require pervasive runtime shape descriptors;
- call-site substitutions are no longer available by the codegen boundary and
  would require re-running inference in lowering;
- a uniform frame forces a simultaneous rewrite of every effect optimization;
- cross-module scheme instantiation cannot be represented without a broader
  interface-format change.

Current estimate: medium typechecker work, large but bounded codegen work. The
feature is architecturally aligned with evidence passing and broadly useful,
but Phase 0 is necessary before treating it as a routine extension.
