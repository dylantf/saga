# Effect-Polymorphic Traits

## Status

Planning, with one prerequisite **landed** and a spike **proven then reset**:

- ✅ **Multi-source effect rows landed.** Effect rows now support multiple row
  variables: `EffectRow { effects, tails: Vec<Type> }`, with `is_open()`, and
  `needs {..a, ..b}` parses, type-checks, and runs. Partial declaration is
  rejected — forwarding `{..a, ..b}` requires *both* tails in the signature, so
  forwarded effects can't be silently dropped. This was the foundational
  prerequisite (see "Why multi-source rows had to come first").
- ✅ **Phase A landed — sound concrete-discharge propagation (the bugfix).**
  An effectful impl's effects now reach the caller of a concrete trait-method
  dispatch. Implemented:
  - `ImplInfo.method_effects: HashMap<String, Vec<String>>` (per-method effect
    names), populated in `register_impl` from each method body's inferred
    effects. Travels cross-module via the cloned `ImplInfo` in
    `ModuleExports.trait_impls`.
  - `Checker::emit_concrete_trait_impl_effects(head)` in `infer.rs`, called at
    both saturated-call points: for constraints recorded on the call head whose
    self type resolved to a concrete `Type::Con`, it emits the selected impl's
    effects via `emit_effect`. **Per-method precision** for direct trait-method
    calls (a pure sibling of an effectful impl stays pure); union fallback for
    where-bound function calls (precise per-constraint surfacing is Phase B).
  - Tests: `concrete_trait_method_call_*`, `pure_sibling_method_*`,
    `effectful_sibling_*`, `pure_impl_emits_nothing`, `where_bound_call_*`
    (typechecker), and `cross_module_effectful_trait_call_requires_effect`
    (module integration). Full suite green, clippy clean.
  - **Known Phase-A limitation (by design):** a generic `where {a: Foo}`
    function still propagates *implicitly* — its own signature shows no effect;
    the obligation surfaces at concrete callers. Making it explicit/required is
    Phase B.

- 🔬 Session-1 spike (per-impl granularity, same-module only) proved the model,
  then was reset; Phase A is its rounded replacement.

Next: Phase B — explicit per-constraint surfacing + required declaration,
aligned with the open-row forwarding rule. Phase C — codegen E2E verification.

## Why multi-source rows had to come first

The spike's polymorphic-surfacing design originally assumed a row has exactly
**one** tail variable, so `where {a: Foo, b: Bar}` would collapse both
constraints' effects into a single `..e`. That collapse is wrong for the same
reason it's wrong for two independent callbacks:

```saga
fun do_work : (Unit -> Int needs {..a}) -> (Unit -> Int needs {..b}) -> Int
  needs {..a, ..b}
```

Sharing one row var across two independent sources forces them to unify to each
other (`expected {Foo}, got {Bar}`). Forwarding the *union* of two independent
open rows needs genuinely multiple tails — which the type representation did not
support. That gap blocked both the lambda case above and per-constraint trait
forwarding, so it was fixed first as its own change. With it in place, a
generic function over `where {a: Foo, b: Bar}` can forward `needs {..a, ..b}`
with each constraint's effects in its own row variable.

## Spike findings (reset, but proven)

A throwaway spike implemented the smallest mechanism that could prove the
propagation model. It has been reset; these findings drive the rounded bugfix.

**The mechanism that worked — concrete-discharge emission at the call site.**
At each saturated call, scan the trait constraints recorded for the call head;
for any whose self type has resolved to a concrete `Type::Con`, emit that impl's
effect row into the accumulator via the normal `emit_effect` path. Crucially,
**emit at the call site during inference, not as a post-pass** — a post-body
pass bypasses `with` subtraction and the handler-necessity check (a handled call
still warned "handler unnecessary" *and* leaked the effect). Emitting at the
call site routes through the normal accumulator, so `with` subtraction and
necessity checks just work.

**It propagates through arbitrary polymorphic chains.** Because every call chain
bottoms out at a concrete call site (entry points are concrete) and a
where-bound function re-pushes its constraint at each call, the obligation
surfaces wherever the constraint resolves concretely. Verified by the spike:

- `call_it () = foo 42` → errors requiring `Config`. (direct concrete dispatch)
- `use_it () = count_foos 42` where `count_foos : a -> Int where {a: Foo}` →
  errors requiring `Config`. (where-bound generic called at a concrete type)
- `entry () = bar 7` where `bar` calls `count_foos`, both polymorphic → still
  errors at `entry`. (transitive through two polymorphic hops)
- A **pure** impl emits nothing.

**Soundness does not require surfacing a row variable** — concrete-discharge
emission alone is sound. *But* we still want surfacing, for two reasons that
emerged in discussion:

- **Explicit effects in signatures.** The spike made `fun count_foos : a -> Int
  where {a: Foo}` propagate effects while showing none — a deviation from
  Saga's "effects are always explicit in the type" rule. The rounded bugfix
  should make the open row visible (`needs {..a}`) and *required*, leaning on
  the new multi-tail rule that every forwarded tail must be declared.
- **The optimizer/specializer.** Specializing `count_foos` at a concrete type
  needs to see, from the stored scheme, that there's an open effect row fed by
  the constraint. Concrete-discharge computes that on demand at call sites; the
  scheme itself must carry it for the specializer to read.

**Gaps the spike did NOT handle (must be fixed for the rounded bugfix):**

- **Granularity.** The spike keyed effects per-impl (per-trait granularity), so
  calling a *pure* method of an effectful impl over-emitted the whole impl's
  effects. Confirmed via probe: a pure sibling method spuriously required the
  effect. The bugfix must be **per-method**.
- **Cross-module.** The spike populated `impl_effects` only in `register_impl`
  (same module). Imported impls' effect rows must be available too, or
  cross-module effectful trait calls silently drop effects again.

## Motivation: a real soundness hole

A trait method may be effectful. Today the effect row is declared on the
**impl**, not the trait method:

```saga
trait Foo a {
  fun foo : a -> Int
}

impl Foo for Int needs {Config} {
  foo thing = if config! () == "foo" then thing + 1 else thing
}
```

This compiles and runs. The problem is what the type system does with those
impl effects: **nothing reaches the caller.** `impl_effects` is computed and
checked against the method body locally
([check_traits.rs:872-910](../../src/typechecker/check_traits.rs#L872-L910)),
then handed to codegen as metadata
([check_module.rs:1859-1889](../../src/typechecker/check_module.rs#L1859-L1889)).
It is **never consumed during expression/call-site inference** — the only
thing that feeds a caller's effect row is the trait method's *type signature*
([check_traits.rs:20-40](../../src/typechecker/check_traits.rs#L20-L40),
`trait_method_effect_sig`, which reads the row off the method's `Type::Fun`).

Consequence:

```saga
fun call_it : Unit -> Int
call_it () = foo 42        # type-checks as PURE — foo : Int -> Int
```

`call_it` type-checks with no `needs {Config}` and no handler, yet at runtime
`foo` performs `Config` and hits an unhandled effect. The handler only
"works" when one happens to be in scope; the types never require it.

The generic case makes the hole obvious and unfixable-by-accident:

```saga
fun count_foos : a -> Int where {a: Foo}
count_foos x = foo x + 2
```

`count_foos` calls `foo` on an *abstract* `a`. There is no way for it to know
which impl will be selected, so there is no way for it to declare the right
effect row. If someone adds `impl Foo for Widget needs {Log}`, then
`count_foos (someWidget)` performs `Log` that `count_foos`'s type cannot
mention.

## The invariant that forces the design

> **Adding an impl must never change the type (including the effect row) of
> existing code.**

This is non-negotiable for modularity: a library adding an impl must not be a
breaking change to downstream generic code, and must not silently make it
unsound. Given the invariant, a generic function's effect row must be fully
determined by its **trait constraints** at the point it is written — not by
the set of impls that happen to exist.

That admits exactly two sound designs:

- **A — effects fixed on the trait method.** The trait method declares its
  effect row; impls may use *up to* that row, never beyond. Generic callers
  see the fixed row. Simple and sound, but rigid: a pure-looking trait can
  have no effectful impls, and an effectful trait taxes every caller (even
  `show 42`) with the effect.
- **B — effect-polymorphic traits (this doc).** The trait method's effect row
  is a *variable* determined by the impl. Generic functions become
  effect-polymorphic over the constraint. The impl decides its effects, and
  callers are still forced to handle them.

Resolution B is what we want: it honors "a trait is an interface; the impl
decides how to satisfy it" while staying sound.

## Why generic functions must be effect-polymorphic

Under B, `count_foos`'s effect row depends on which `Foo` impl `a` resolves
to, so it cannot be a fixed closed set. Its principal type is
effect-polymorphic over the constraint — the effect analog of being generic
over `a` itself. You don't know the concrete effects, and that's fine: they
resolve per instantiation.

This is unavoidable and correct. (It is also exactly why A is the alternative:
A buys a fixed row by forbidding impl-introduced effects.)

## Surface syntax

A function generic over an effectful-impl trait carries an open effect row,
with one row variable per forwarded constraint, named after the constrained
type variable:

```saga
fun generic_foo : a -> Int needs {..a} where {a: Foo}
generic_foo thing = foo thing
```

For multiple constraints, one tail each:

```saga
fun do_two : a -> b -> Int needs {..a, ..b} where {a: Foo, b: Bar}
```

Rules:

- `..a` is the effect row contributed by the constraints on type variable `a`
  (the union of `a`'s traits' impl effects, resolved per instantiation). It
  reads as "a's effects."
- `needs {...}` lists effects the function performs *directly* (its own ops,
  calls to concrete effectful functions); `..a` forwards constraint effects.
- **No effects on value types.** `(a needs {..a})` is malformed — effects live
  on arrows (computations), never on a plain value of type `a`.
- **Forwarding must be declared.** Multi-tail rows already enforce that every
  forwarded tail appears in the signature, so a function that forwards a
  constraint's effects must spell `..a`, or it won't type-check. This keeps
  effects explicit in the signature (the property we want) for free.
- For non-`pub` functions the row can be inferred (omit `needs`); `pub`
  signatures must declare it.

No new grammar is required: `needs {..a, ..b}` and `where {a: T}` both parse
today. The only open call is whether `..a` (referencing the type variable
directly) is the spelling, versus an explicit constraint-binding form like
`where {a: Foo / e}`. Current lean: `..a`, since it needs no new binding and
maps directly onto the per-constraint row variables the representation now
supports. See "Per-constraint row variables".

## The core mechanism: constraint discharge emits effects

The load-bearing rule. Body unification is used only to make a function's
*own* signature honest; it must **not** be the channel that propagates effects
to callers, because callers (especially cross-module) type-check against the
signature alone and never see the body.

Instead, propagation is a property of **constraint resolution**. At every site
where a `Foo a` constraint is discharged during inference:

- **`a` resolved to a concrete type** → emit that impl's declared effect row
  (`TraitImplDict.impl_effects`, already computed and already exported) into
  the current effect row.
- **`a` still polymorphic** → emit the constraint's effect *variable* `ε_a`
  into the current row.

Everything falls out from this, with no caller ever reading a body:

| Site | Constraint | Emits | Result |
| --- | --- | --- | --- |
| `generic_foo 41` (a = Int) | `Foo Int` resolved | `{Config}` | caller must handle `Config` |
| inside `generic_foo` (a abstract) | `Foo a` unresolved | `ε_a` | `generic_foo : … needs {..ε_a}` |
| `bar x = generic_foo x where {b: Foo}` | `Foo b` unresolved | `ε_b` | `bar : … needs {..ε_b}` (transitive, cross-module) |

So the `..e` a user writes is the *visible residue* of unresolved
constraints, and propagation everywhere derives from the signature plus the
already-exported impl effect rows — never from body re-analysis.

### Determinism: a canonical per-constraint effect variable

For the body link to be deterministic rather than incidental, each
`where`-bound constraint mints a **canonical effect variable** at signature
elaboration: `where {a: Foo}` allocates `ε_a`, and polymorphic `Foo`-method
calls on `a` use *that* var. Then:

1. The body's `foo thing` emits `ε_a`.
2. Checking the body against the declared `{..e}` merges `e ≡ ε_a`.
3. `ε_a` is recorded in the exported scheme's constraint.

No "did unification happen to merge the right vars" — it is wired by
construction.

### Per-constraint row variables (updated: multi-tail rows now exist)

The original plan collapsed all constraint effects into a single `..e` because
rows had one tail. That is no longer the representation: rows now carry
`tails: Vec<Type>`, so each constraint can own its own row variable. With
`where {a: Foo, b: Bar}`, a forwarding function writes `needs {..a, ..b}` —
`..a` is `Foo`'s contribution for `a`, `..b` is `Bar`'s for `b`. This is both
more precise (the specializer can resolve each independently) and matches the
"a's effects" mental model directly. A single shared `..e` is no longer
required and should be avoided, since it would over-constrain (force the two
constraints' effects to unify).

## Type-level design

The machinery is almost entirely "wire existing primitives," because effect
rows are already first-class and constraints already carry rider data.

What already exists:

- **Multi-source effect rows (landed).** `EffectRow { effects, tails: Vec<Type> }`
  with `is_open()`; `needs {..a, ..b}` parses, checks, and runs; partial
  declaration is rejected. Row variables are `Type::Var(u32)` in `tails`,
  generalized into `Scheme.forall` by `collect_free_vars` and instantiated
  fresh per use; row unification handles multiple open tails (with a clear
  error on genuinely-ambiguous multi-open-tail cases).
- **Constraints carry riders.** `Scheme.constraints: Vec<(String, u32,
  Vec<Type>)>` already threads extra *type* args for multi-param traits
  (`trait Generic a r`); `TraitEvidence.trait_type_args` carries them to
  elaboration. This is the closest existing analog to attaching an effect var
  to a constraint.
- **Impl effect rows, computed and serialized cross-module** —
  `TraitImplDict.impl_effects`, and per-method `impl_method_effects_by_dict`.
- **Concrete-vs-polymorphic dispatch split already in codegen.**
  `classify_dict_method_call` unions in the impl's effects when the dict head
  is a concrete `DictRef`, and uses only the trait-method signature when the
  head is a `Var` (where-bound dispatch)
  ([call_effects.rs](../../src/codegen/call_effects.rs)).

What is new:

1. **Trait effect parameter.** At trait registration, mint a row var `ε` and
   append `..ε` to each method's stored scheme effect row. So `fun foo : a ->
   Int` is stored as `foo : a -> Int needs {<trait-declared effects>, ..ε}`.
   The method's row is now open with the trait's effect parameter as tail.
2. **Constraints carry the effect var.** Widen the constraint representation
   to record the canonical effect var id per constraint instance (e.g.
   `(String, u32, Vec<Type>, EffectVar)` where `EffectVar` is `u32` for the
   per-trait design, or a small `Vec<u32>` for per-method — see Granularity).
   Add a parallel entry to `where_bounds` / `where_bound_var_names`.
3. **Constraint-discharge emission.** At every constraint resolution site,
   emit effects per the table above (concrete impl row, or the constraint's
   effect var). The concrete row is read from `impl_effects`; the var is the
   canonical `ε_a`.
4. **Generalization.** `ε_a` generalizes into the function scheme alongside
   `a`, tied to the constraint, yielding `count_foos : a -> Int needs {..ε_a}
   where {a: Foo}`. Scheme printing surfaces it.
5. **Instantiation consistency.** Instantiation must freshen the constraint's
   self-var and its effect var **together** (same mapping), so a concrete
   resolution binds the right fresh var. `instantiate` already freshens
   constraint riders via the shared mapping
   ([unify.rs:353-379](../../src/typechecker/unify.rs#L353-L379)); extend it to
   the effect var.

## Runtime: mostly already built

The key finding from the lowerer investigation: **effect evidence is not, and
must not be, baked into the dict.** A dict (`__dict_Foo_Widget`) is a
top-level constructor that runs before any handler exists; handlers are
installed dynamically at `with` sites. Evidence flows through a normal
`_Evidence` parameter threaded *at call time* — an effectful dict method is
compiled as `fun(args…, _Evidence, _ReturnK)` and the caller hands it its own
ambient evidence ([effect-implementation.md:259-277](../effect-implementation.md),
[lower/calls.rs](../../src/codegen/lower/calls.rs) `lower_dict_method_call`).

That means B's runtime *is* the existing row-polymorphism machinery:

- A generic function over `where {a: Foo}` with `needs {..ε}` is an open-row
  function. Its dict-method calls are `CallEffectKind::RowForwarded`, which
  forwards the entire ambient evidence vector unchanged
  ([call_effects.rs](../../src/codegen/call_effects.rs)).
- At the concrete instantiation site, the resolved closed row triggers the
  existing `project_evidence` narrowing
  ([effect-implementation.md:209-219](../effect-implementation.md)).

Once the trait method's stored signature is open-row (step 1 above), the
polymorphic dict call *automatically* classifies as `RowForwarded` instead of
pure, which is exactly the codegen fix. Expect **little or no new codegen** on
the happy path — the work is verifying projection at the concrete boundary.

## Granularity decision: per-method vs per-trait

The one design choice to make deliberately.

- **Per-trait `ε` (simpler).** One effect parameter per trait; the impl's
  `needs` is its union. Maps one-to-one onto today's impl-level `needs`.
  Cost: calling a *pure* method of an effectful impl spuriously demands the
  handler — sound but imprecise. This is the imprecision the codegen already
  flags at [lower/module.rs:580-584](../../src/codegen/lower/module.rs#L580-L584).
- **Per-method `ε_m` (precise — recommended).** Each trait method gets its own
  effect parameter; the impl supplies each from its method body's *inferred*
  effects (no new impl syntax — impl methods have no signature, so it's
  inference regardless). The constraint carries a small fixed vector of row
  vars (method count is known); `foo x` merges only `ε_foo`. This matches the
  per-method effect data the typechecker already stores
  (`TraitMethodInfo.effect_sig`, `impl_method_effects_by_dict`) and keeps pure
  siblings pure.

Recommendation: **per-method.** The plumbing already exists end-to-end and it
avoids re-introducing the pure-sibling imprecision. Per-trait is the fallback
if shipping the soundness fix fast matters more than precision.

Note on the interaction with explicit syntax (if ever added): inference can
stay per-method (precise) while any *explicit* annotation names the per-trait
union, which is a sound over-approximation. So precise inference and clean
syntax do not conflict.

## Impl-level `needs`, reinterpreted

This design resolves the earlier "is impl `needs` redundant?" question. It is
neither redundant nor an unsound side-channel: under B it is **the value
supplied for the trait's effect parameter** for that impl. `impl Foo for
Widget needs {Log}` binds `ε_Widget = {Log}`; `impl Foo for Int` (no `needs`)
binds `ε_Int = {}`. The binding value is already computed and exported as
`TraitImplDict.impl_effects`.

Whether the impl must *declare* `needs` or have it inferred from the body is a
secondary choice. Inference is more ergonomic (the body already determines it);
an explicit declaration is clearer and is what exists today. Either is
compatible with this design; the body-effect check keeps the two consistent.

## Implementation plan (rounded bugfix)

The spike proved the model; this is the production version. The prerequisite
(multi-source rows) is already landed. Ordered so soundness lands first, then
explicit surfacing, then verification.

**Phase A — sound concrete-discharge propagation (the bugfix core).**

1. **Per-method impl effect rows, stored for lookup.** Record each impl
   *method's* effect row (per-method, not the per-impl union the spike used),
   keyed so a call site can find it from the resolved concrete type. Source it
   from the per-method data the typechecker already has rather than the
   impl-level `needs` clause, so a pure sibling method contributes nothing.
2. **Cross-module availability.** Ensure imported impls' per-method effect rows
   are present in the same lookup, not just impls registered in the current
   module. The impl effect rows are already exported for codegen
   (`TraitImplDict.impl_effects`); thread an equivalent per-method view into
   the typechecker so cross-module calls propagate too.
3. **Emit at the saturated call site, during inference.** At each saturated
   call, scan the constraints recorded for the call head; for any whose self
   type resolved to a concrete `Type::Con`, emit *that method's* effect row via
   `emit_effect`. (Not a post-body pass — must flow through `with` subtraction.)
4. **Tests.** Same-module concrete dispatch; where-bound generic called
   concretely; transitive polymorphic chain; cross-module; **pure sibling of an
   effectful impl stays pure** (the per-method precision check); pure impl emits
   nothing.

**Phase B — explicit surfacing via per-constraint row variables.**

This is the existing **open-row forwarding rule** applied to constraints, not a
new trait-specific rule. The rule: *you can only handle effects you can name;
an open/unknown row must be forwarded, never silently swallowed.*

- Closed-row callback (`(a -> b needs {Fail}) -> b`): `Fail` is nameable, so the
  HOF may handle it internally (and must, if its return row is pure).
- Open-row callback (`(a -> b needs {..e}) -> b`): `..e` is unknowable, so the
  HOF cannot handle it; it must forward it (`-> b needs {..e}`) or it's an error.

A trait constraint is the open-row case: inside `count_foos : a -> Int where
{a: Foo}`, the effects of `foo x` on abstract `a` depend on the impl and are
unknowable, so `count_foos` cannot handle them internally — exactly like `..e`.
Therefore:

5. **Polymorphic emission.** A trait-method call on an abstract (where-bound)
   self emits the constraint's row variable (`..a`) into the function's body
   effects — the analog of a callback's open row flowing into the body.
6. **Surface + require the row.** That `..a` must appear in the function's
   declared row, or it's an error — the same diagnostic as an unforwarded
   open-row callback ("calls X whose open effect row isn't handled; add `needs
   {..a}`"). This makes the open row visible in the signature (for humans,
   hover, and the specializer) and forbids implicit absorption, consistent with
   HOFs. The multi-tail "every forwarded tail must be declared" rule provides
   the enforcement mechanism. `ε_a` generalizes into the stored scheme.

**Phase C — verification + migration.**

7. **Codegen end-to-end.** Confirm a concrete effectful trait call threads the
   right evidence and `project_evidence` fires at the concrete boundary; the
   polymorphic dict call should classify `RowForwarded`. Likely little new
   codegen.
8. **Migration / audit.** Re-check `examples/optimization/**` and
   `examples/bugs/**effectful**` for intended behavior changes (calls that were
   silently dropping effects now correctly require handlers).

## Edge cases

- **Conditional impls** (`impl Foo for Box a where {a: Foo}`): `Box`'s effect
  parameter composes from the inner `a`'s — `ε_Box = ε_a`. The impl's
  `where {a: Foo}` already threads the inner dict; the inner `ε_a` rides along
  via the same constraint. Row-variable composition through the sub-dict is
  handled by existing unification.
- **Multi-param traits** already put extra args in the constraint; the effect
  var is one more rider on the same tuple.
- **Open-row impls** (`impl … needs {Log, ..e}`): the bound row is itself
  open; open-to-open unification already handles it.
- **Absorption / self-handling.** If a generic function handles a
  constraint's effect internally (`foo thing with { config () = … }`), the
  handled effect is subtracted from the residual via the existing `with`
  subtraction ([effect-implementation.md:83-107](../effect-implementation.md)).
  The constraint still emits the effect; handling removes it from what escapes.
- **Cross-module.** All needed data is already exported: trait method effect
  sigs (`TraitMethodInfo.effect_sig`) and impl rows
  (`TraitImplDict.impl_effects`). Callers derive obligations from the imported
  scheme + impl rows, never from bodies.

## Risks

- **Constraint-representation ripple.** Widening the constraint tuple touches
  `instantiate`, `generalize`, evidence recording, and scheme
  (de)serialization. Mechanical but broad; do it in one focused pass (step 2)
  after the spike proves the model.
- **Per-method bookkeeping.** A generic function must capture exactly the
  effect vars for the methods it actually calls. Getting the
  method→var association right is the fiddliest part.
- **Inference surprises in signatures.** Because `..e` is linked by inference,
  a confusing diagnostic is possible when a `pub` signature's declared row
  doesn't match the constraint-derived one. Invest in a good error ("this row
  must include the effects of `Foo a`; add `..e`").

## Relationship to Resolution A

A is B with the trait's effect parameter *defaulted to a fixed row*. Building
B does not preclude A-style traits: a trait that declares concrete effects on
its methods simply pins `ε` to that row, and impls are bounded by it. So the
two coexist — A for "this operation is inherently effectful for all impls," B
for "impls decide."

## See also

- [trait-dict-passing.md](../trait-dict-passing.md) — dictionary passing,
  `TraitEvidence`, `resolved_type` Some/None split.
- [effect-implementation.md](../effect-implementation.md) — effect rows, CPS
  transform, evidence vector, row forwarding, projection.
- [typechecking.md](../typechecking.md) — inference overview.
