# Effect-Polymorphic Traits

How trait methods carry effects: effect-capability is declared on the trait
method, impls are bounded by it, and generic functions forward a constraint's
effects through a per-constraint row variable.

## Current state

**Implemented:**

- **Multi-source effect rows.** `EffectRow { effects: Vec<EffectEntry>, tails:
  Vec<Type> }` ([typechecker/mod.rs](../../src/typechecker/mod.rs)), with
  `is_open()` and `tail_var_ids()`. `needs {..a, ..b}` parses, type-checks,
  unifies, and runs. A row may carry several independent open tails (the union
  of multiple open rows). Partial declaration is rejected: forwarding
  `{..a, ..b}` requires *both* tails in the signature.
- **Concrete-discharge propagation.** An effectful impl's effects reach the
  caller of a concrete trait-method dispatch.
  - `ImplInfo.method_effects: HashMap<String, Vec<String>>` — per-method effect
    names, populated in `register_impl` from each method body's inferred
    effects. Travels cross-module via the cloned `ImplInfo` in
    `ModuleExports.trait_impls`.
  - `Checker::emit_concrete_trait_impl_effects(head)`
    ([typechecker/infer.rs](../../src/typechecker/infer.rs)), called at the two
    saturated-call points in `infer_app_chain_with_expected`: for constraints
    recorded on the call head whose self type resolved to a concrete
    `Type::Con`, it emits the selected impl's effects via `emit_effect`.
    Per-method precision for direct trait-method calls (a pure sibling of an
    effectful impl stays pure); union fallback for where-bound function calls.
- **Bounding check.** `register_impl` rejects an impl whose method body uses
  effects the trait method's row does not permit (see the matrix below).

**Remaining (this doc's task):** generic functions over an *open-row* trait
method must surface and forward the constraint's effects as `..a` in their own
signature, instead of propagating implicitly. See "Work remaining".

## The problem this solves

A trait method may be effectful, but the effect lived only on the impl, and the
type system dropped it at call sites — only the trait method's declared type fed
a caller's effect row. So:

```saga
trait Foo a { fun foo : a -> Int }
impl Foo for Int needs {Config} { foo thing = if config! () == "x" then thing else thing }

fun call_it : Unit -> Int
call_it () = foo 42        # used to type-check as PURE; runtime then hits unhandled Config
```

Concrete-discharge propagation (implemented) fixes the soundness hole:
`call_it` now requires `Config`. The remaining work makes the *generic* case
explicit in signatures.

## The modularity invariant

> **Adding an impl must never change the type (including the effect row) of
> existing code.**

A generic function's effect row must be determined by its **trait constraints**
at the point it is written — never by which impls happen to exist. This is why
effect-capability must be declared on the trait, not inferred from impls: if it
were keyed on "some impl is effectful," then adding `impl Foo for Widget needs
{Log}` in another module would retroactically change an unrelated generic
function's type. (Adding an impl may legitimately affect *new* calls on that
type — those only compile once the impl exists — but never existing code.)

## The rule: effect-capability is opt-in on the trait method

Effect-capability is declared by the **trait method's effect row**, and impls
are **bounded** by it. This is the existing open-row forwarding rule (you can
only handle/forward effects the signature names or opens) applied to traits.
The row is **author-written** on the trait method — there is no auto-minting of
an effect parameter for every trait (that would force `..a` onto every generic
over `Show`/`Eq`).

| Trait method declares | An impl may use | Generic fn over `where {a: Foo}` | Analogy |
| --- | --- | --- | --- |
| `foo : a -> Int` (pure) | **nothing** — effectful impl is a compile error | nothing; no `..a` (`Show`/`Eq` stay clean) | — |
| `foo : a -> Int needs {Config}` (closed/named) | up to `{Config}` | forwards the named `{Config}` | closed-row callback |
| `foo : a -> Int needs {..e}` (open) | **any** effects (fill `..e`) | forwards `..a`; must declare it or error | open-row callback |

The open-row forwarding analogy is exact:

- Closed-row callback `(a -> b needs {Fail}) -> b`: `Fail` is nameable, so the
  HOF may handle it internally (and must, if its return row is pure).
- Open-row callback `(a -> b needs {..e}) -> b`: `..e` is unknowable, so the HOF
  cannot handle it; it must forward it (`-> b needs {..e}`) or it's an error.

Inside `count_foos : a -> Int where {a: Foo}` with `foo : a -> Int needs {..e}`,
the effects of `foo x` on abstract `a` are impl-determined and unknowable, so
`count_foos` cannot handle them — it must forward them, declaring `needs {..a}`.

## How propagation works across the three rows

- **Pure trait method:** impls are pure (bounding check), nothing propagates.
- **Closed-named trait method (`needs {Config}`):** the named effects are part
  of the trait method's *type*, so they already propagate through the normal
  `emit_saturated_call_effects` path — both at concrete calls and inside
  generics (a generic over such a trait already requires `needs {Config}`). No
  per-constraint row variable is involved. The existing `Encodable`/`Decode`
  examples are this case.
- **Open-row trait method (`needs {..e}`):** the impl's concrete effects are
  *not* in the trait method's named row.
  - At a **concrete** call, `emit_concrete_trait_impl_effects` emits the
    resolved impl's effects (implemented).
  - Inside a **generic** function (abstract self), the open tail must surface as
    the constraint's row variable `..a` and be forwarded — this is the work
    remaining.

## Surface syntax

A function generic over an open-row trait method carries an open effect row,
one row variable per forwarded constraint, named after the constrained type
variable:

```saga
fun generic_foo : a -> Int needs {..a} where {a: Foo}
generic_foo thing = foo thing

fun do_two : a -> b -> Int needs {..a, ..b} where {a: Foo, b: Bar}
```

- `..a` is the effect row contributed by the constraints on type variable `a`
  (the impl's effects filling the trait method's `..e`, resolved per
  instantiation). It reads as "a's effects."
- `needs {...}` lists effects the function performs *directly*; `..a` forwards
  constraint effects.
- Effects never go on a value type: `(a needs {..a})` is malformed — effects
  live on arrows.
- `pub` functions must declare the row; non-`pub` may infer it.

No new grammar is required: `needs {..a, ..b}` and `where {a: T}` already parse.
A `..name` row variable reuses the var id of a same-named type parameter
(`convert_type_expr`, [unify.rs](../../src/typechecker/unify.rs) ~L914), so
`needs {..a}` and `where {a: Foo}` already share the variable `a`.

## Work remaining (Phase B)

Two parts.

### 1. Fix tests broken by the bounding check (mechanical)

The bounding check correctly rejects pure-trait + effectful-impl. Tests that
encoded the old permissive behavior must move to the opt-in form (declare an
open row on the trait method). Affected typechecker tests:
`impl_uses_effect_with_correct_needs_ok`,
`concrete_trait_method_call_propagates_impl_effect`,
`concrete_trait_method_call_with_needs_ok`,
`pure_sibling_method_of_effectful_impl_stays_pure`,
`effectful_sibling_method_still_propagates`, `concrete_trait_effect_handled_by_with_is_ok`.
For each, give the effectful method an open row on the trait
(`fun foo : a -> Int needs {..e}`); the pure-sibling test keeps the pure
sibling pure. Add a test asserting pure-trait + effectful-impl is a bounding
error.

### 2. Open-row generic surfacing + required forwarding

When a trait method with an **open row** is called on an **abstract,
where-bound** type variable `a`, the constraint's effects must:

- **surface** as the row variable `..a` in the function's inferred/stored row
  (so the signature shows it, hover/specializer can read it), and
- be **required**: the function must declare `..a` (or otherwise discharge it),
  else error — mirroring the open-row callback forwarding requirement.

This is the open-row analog of `emit_concrete_trait_impl_effects`'s concrete
case. Reuse the existing forwarding-requirement machinery rather than inventing
a new rule: see `callback_row_vars` and the "calls a callback parameter whose
declared effect … is not handled" error in
[check_decl.rs](../../src/typechecker/check_decl.rs) (~L1117-L1178). The
diagnostic should read like "forwards effects from `Foo a`; add `needs {..a}`".

Implementation gotchas found during investigation:

- `emit_effects` / `emit_saturated_call_effects` propagate only **named**
  effects, not tails. That is why closed-named trait methods already propagate
  but open rows do not — the open tail is dropped. The new work must route the
  open tail into the function's row (its `tails`) and/or into the
  forwarding-requirement check.
- A `..a` tail that resolves to a concrete type (after `a = Int`) is not a valid
  effect row. At concrete sites, the real effects come from
  `emit_concrete_trait_impl_effects`; the type-resolved tail must not be emitted
  as garbage. Keep the surfaced `..a` meaningful only while `a` is abstract.
- Granularity: prefer per-method precision (a function forwards only the
  effects of the methods it actually calls). `ImplInfo.method_effects` is keyed
  per method; the per-constraint `..a` is the union of the methods the function
  calls on `a`. Per-trait union is the acceptable fallback if per-method proves
  too costly.

## Runtime

No new runtime mechanism. Effect evidence is threaded through the normal
`_Evidence` parameter at call time, never baked into a dict (a dict constructor
runs before any handler exists). A generic function over an open-row trait is an
open-row function; its dict-method calls classify as
`CallEffectKind::RowForwarded` and forward the ambient evidence unchanged; a
concrete site narrows via `project_evidence`. Expect little or no new codegen;
verify end-to-end that a concrete effectful trait call threads evidence and
runs. See [effect-implementation.md](../effect-implementation.md) and
[trait-dict-passing.md](../trait-dict-passing.md).

## Edge cases

- **Conditional impls** (`impl Foo for Box a where {a: Foo}`): `Box`'s effects
  compose from the inner `a`'s, through the threaded sub-dict and the same
  constraint; existing unification handles the row composition.
- **Multi-param traits** already carry extra type args on the constraint
  (`Scheme.constraints: Vec<(String, u32, Vec<Type>)>`); a forwarded row var is
  one more rider.
- **Self-handling.** If a generic function handles a constraint's effect with an
  internal `with`, the handled effect is subtracted by the existing `with`
  subtraction; only the residue must be forwarded.

## Risks

- **Type-var/row-var duality.** `..a` reuses the type var's id. Surfacing must
  keep the row meaning while `a` is abstract and avoid emitting a
  type-resolved tail at concrete sites.
- **Over/under-firing.** The requirement must fire only for open-row trait
  methods (not pure ones like `Show`), and only when the call's self is abstract
  (concrete is handled by concrete-discharge). Getting these conditions exact is
  the crux.
- **Diagnostic quality.** A `pub` signature missing `..a` should get a clear,
  actionable error.

## Build & test

```
cargo build --bin saga
cargo test                       # full suite (typechecker, codegen, integration, property)
cargo clippy --all-targets
cargo run --bin saga -- check <file.saga>     # quick type-check of a scratch file
```

Typechecker tests use a `check(src)` helper in
[src/typechecker/tests.rs](../../src/typechecker/tests.rs). Cross-module tests
live in [tests/module_codegen_integration.rs](../../tests/module_codegen_integration.rs).

## See also

- [trait-dict-passing.md](../trait-dict-passing.md) — dictionary passing,
  `TraitEvidence`, the `resolved_type` concrete-vs-typevar split.
- [effect-implementation.md](../effect-implementation.md) — effect rows, CPS
  transform, evidence vector, row forwarding, projection.
- [typechecking.md](../typechecking.md) — inference overview.
