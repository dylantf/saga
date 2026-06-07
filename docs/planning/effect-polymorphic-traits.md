# Effect-Polymorphic Traits

## Status

Planning + **Session-1 spike landed** (see "Spike results" below). The concrete
half of the soundness fix is implemented behind no flag; the polymorphic
row-variable design described in the body of this doc turned out to be
unnecessary for *soundness* (though still relevant for precise inferred types
and codegen evidence — see the spike section).

## Spike results (Session 1)

A spike implemented the smallest mechanism that could prove the propagation
model and found it covers far more than expected.

**What was built (~40 lines, no new syntax, no representation change):**

- `TraitState.impl_effects: HashMap<(canonical_trait, canonical_target), Vec<String>>`,
  populated in `register_impl` from the impl's `needs` clause
  ([check_traits.rs](../../src/typechecker/check_traits.rs)).
- `Checker::emit_concrete_trait_impl_effects(head)` in
  [infer.rs](../../src/typechecker/infer.rs), called at the two saturated-call
  points in `infer_app_chain_with_expected`. It scans the constraints recorded
  for the call head's node id; for any whose self type has resolved to a
  concrete `Type::Con`, it emits that impl's effect row into the accumulator via
  the normal `emit_effect` path.

**Key finding — emit at the call site, during inference, not as a post-pass.**
The first attempt emitted impl effects *after* body inference, in
`check_fun_clauses`. That was too late: it bypassed `with` subtraction and the
handler-necessity check, so a handled call still warned "handler unnecessary"
*and* the effect leaked to the function's row. Emitting at the saturated-call
point routes the effect through the normal accumulator, so `with` subtraction
and necessity checks just work.

**Key finding — concrete-discharge emission alone propagates through arbitrary
polymorphic chains.** Because every call chain bottoms out at a concrete call
site (entry points are concrete), and a where-bound function re-pushes its
constraint at each call, the obligation surfaces wherever the constraint
resolves concretely. Verified:

- `call_it () = foo 42` → errors requiring `Config`. (direct concrete dispatch)
- `use_it () = count_foos 42` where `count_foos : a -> Int where {a: Foo}` →
  errors requiring `Config`. (where-bound generic called at a concrete type)
- `entry () = bar 7` where `bar` calls `count_foos` and both stay polymorphic →
  still errors at `entry`. (transitive through two polymorphic hops)
- A **pure** impl emits nothing (no over-emission).

**Key finding — the `where` constraint alone carries the effect; `needs {..e}`
is not required.** `fun count_foos : a -> Int where {a: Foo}` (no `needs`)
already propagates `Config` to a concrete caller. This is the **Option-1
("implicit via constraint") semantics** emerging naturally — even though the
intended surface syntax was `needs {..e}`. The `..e` becomes optional
documentation, not a soundness requirement.

**What this changes about the plan.** The constraint-representation surgery, the
per-constraint canonical effect variable, and generalizing `ε_a` into schemes
(steps 2, 4, 5 in the implementation plan below) are **not needed for
soundness.** They remain relevant only for:

- **Precise inferred-type display** — showing `count_foos : a -> Int needs
  {..e} where {a: Foo}` rather than a bare `where {a: Foo}` whose effect
  obligation is implicit.
- **Codegen evidence threading** — confirming the runtime hands the right
  evidence to the dict method at concrete sites. (Not yet verified by the
  spike; the existing integration suite for effectful trait dispatch still
  passes, which is encouraging but not a direct test of the new propagation.)
- **The genuinely-abstract boundary** — separately-compiled generic code that
  is *never* instantiated concretely in-module. Unobservable in whole-program
  checking; revisit only if it bites.

**Validation:** full suite green with the change in place — 968 lib + 135
integration + property/codegen suites, 0 failures. Four new typechecker tests
(`concrete_trait_method_call_*`, `where_bound_call_at_concrete_type_*`) encode
the proof. `cargo clippy` clean.

**Open questions for Session 2:**

1. Codegen — does a concrete effectful trait-method call now thread `Config`
   evidence correctly end-to-end, and does the necessity/projection match the
   new typechecker view? (Spike only covered the type level.)
2. Granularity — `impl_effects` is currently per-impl (per-trait granularity).
   Move to per-method to keep pure siblings precise? (See Granularity section.)
3. Inferred-type display — do we want `needs {..e}` to show up, i.e. is the
   constraint-representation work worth it for ergonomics even though soundness
   doesn't need it?

---

The remainder of this doc is the original design (pre-spike). It is still the
reference for the polymorphic row-variable machinery, should we decide the
inferred-type/codegen reasons justify it.

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

A function generic over an effectful-impl trait carries an open effect row
whose tail is fed by the constraint:

```saga
fun generic_foo : a -> Int needs {..e} where {a: Foo}
generic_foo thing = foo thing
```

Rules:

- The `..e` is an ordinary open row variable. It names the function's
  "everything-extra" effects, which **include** whatever the `Foo` impl for
  `a` needs.
- `needs {...}` lists effects the function performs *directly* (its own ops,
  calls to concrete effectful functions). Constraint-contributed effects flow
  into the open tail.
- **No effects on value types.** `(a needs {..e})` is malformed — effects live
  on arrows (computations), never on a plain value of type `a`.
- For non-`pub` functions the row can be fully inferred (omit `needs`). For
  `pub` functions, signatures are mandatory, so you write `needs {..e}`; the
  body-effect check (below) forces you to, so it can't be accidentally
  dropped.

There is **no new grammar** — `needs {Log, ..e}` open rows and `where {a: T}`
constraints already parse
([syntax-reference.md, Effects/Traits](../../../saga-website/public/syntax-reference.md)).

### Optional explicit binding (deferred)

The link between `e` and `Foo` is established by inference, not written. If
that proves too implicit for public APIs, a future explicit form could bind
the constraint's effect row to a name:

```saga
fun generic_foo : a -> Int needs {..e} where {a: Foo / e}   # not in v1
```

This is deliberately out of scope for the first cut; inference + the
determinism guarantee below make the implicit form sound. Revisit only if
readability demands it.

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

### No ambiguity, by construction

A row has exactly one tail var, so `..e` absorbs the *union* of all
unresolved constraint effects (plus any forwarded callback rows). With
`where {a: Foo, b: Bar}`, `e = ε_a ∪ ε_b` — correct, never ambiguous. There
is never a "which constraint does `e` belong to" question.

## Type-level design

The machinery is almost entirely "wire existing primitives," because effect
rows are already first-class and constraints already carry rider data.

What already exists:

- **Row variables as `Type::Var(u32)` in `EffectRow.tail`**, generalized into
  `Scheme.forall` by `collect_free_vars` and instantiated fresh per use
  ([mod.rs:84-162](../../src/typechecker/mod.rs#L84-L162),
  [unify.rs:353-478](../../src/typechecker/unify.rs#L353-L478)).
- **Row unification / tail binding** (`{Log} ~ {..e}`, open-open shared tail)
  ([unify.rs:242-321](../../src/typechecker/unify.rs#L242-L321)).
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

## Implementation plan

Ordered to de-risk the type-level model before touching representation
surgery, and to lean on the runtime that already exists.

1. **Spike — trait effect parameter + propagation.** Add `..ε` (per-method)
   to stored trait-method scheme rows at registration. Add the
   constraint-discharge emission for the polymorphic case. Assert in a
   typechecker test that `count_foos x = foo x` over `where {a: Foo}` *infers*
   `needs {..e}` instead of pure. This proves propagation before any
   representation change.
2. **Constraint representation.** Widen the constraint tuple to carry the
   effect var(s); thread through `instantiate` / `generalize` / evidence.
3. **Concrete-dispatch emission.** At concrete constraint resolution, emit the
   impl's row (`impl_effects` / per-method). Add the test from the Motivation:
   `call_it () = foo 42` must now require `needs {Config}` (or a handler).
4. **Elaboration check.** Confirm the resolved row reaches `call_effects` so
   the polymorphic dict call classifies `RowForwarded` (should follow from the
   open-row trait signature).
5. **Codegen verification.** End-to-end: `generic_foo someWidget` requires and
   threads `Log` evidence; verify `project_evidence` fires at the concrete
   boundary. Likely no new codegen beyond verification.
6. **Migration.** Existing impls already declare `needs`; reinterpret it as the
   effect-parameter binding. Audit `examples/optimization/**` and
   `examples/bugs/**effectful**` for behavior changes (these are the existing
   effectful-trait test cases).

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
