# Generic Deriving

Saga supports user-extensible `deriving` clauses via a `Generic` trait that
provides a structural representation of any record or ADT. Library authors
write trait instances over a small set of building-block types; users derive
those traits on their own types without compiler changes.

```
# User code
record Person { name: String, age: Int } deriving (Generic, ToJson)

# After derive expansion (conceptual)
type Rep__Person = Rep__Person (Record (And (Labeled (Leaf String))
                                            (Labeled (Leaf Int))))

impl Generic Person (Rep__Person) {
  to p = Rep__Person (Record "Person"
                       (And (Labeled "name" (Leaf p.name))
                            (Labeled "age"  (Leaf p.age))))
  from (Rep__Person (Record _ (And (Labeled _ (Leaf n))
                                   (Labeled _ (Leaf a))))) = { name: n, age: a }
}

# Bridge: routes <Trait> Rep__Person through the inner tree
impl ToJson for Rep__Person {
  to_json (Rep__Person inner) = to_json inner
}

# Delegating: routes <Trait> Person through Generic, then the bridge
impl ToJson for Person where {Generic Person r, ToJson r} {
  to_json p = to_json (to p)
}
```

`ToJson` for `Person` resolves at the call site by composing the
library-provided `ToJson` instances for `And`/`Labeled`/`Leaf` over the
generated `Rep__Person` tree. The compiler never sees the codec.

This document covers the implementation: the building blocks, the derive
machinery in `src/derive.rs`, and the trait-system features Generic depends
on.

---

## The Building Blocks

Source: `src/stdlib/Generic.saga`

```saga
type U1                = U1
type Leaf a            = Leaf a
type Labeled a         = Labeled String a
type And l r           = And l r
type Or l r            = Or_Left l | Or_Right r
type Variant a         = Variant String a
type Record a          = Record String a
type Adt a             = Adt String a

trait Generic a r {
  fun to   : a -> r
  fun from : r -> a
}
```

These are the structural pieces every Rep is built from:

- **`U1`** — empty contribution. Used for zero-field constructors.
- **`Leaf a`** — a primitive or user-typed value. The recursion bottoms out here.
- **`Labeled a`** — a record-field name carried as a runtime string, paired
  with its inner shape. (Record-fields only — sum constructor names use
  `Variant`.)
- **`And l r`** — a product. Records and multi-field constructors fold into
  right-leaning And chains.
- **`Or l r`** — a sum. ADTs with 2+ variants fold into right-leaning Or chains.
- **`Variant a`** — a sum constructor name carried as a runtime string with
  its payload shape. Distinct from `Labeled` so library codecs can give
  different behaviour to record fields and constructor names.
- **`Record a`** — top-level framing wrapper for records: carries the runtime
  type name and the inner And/Labeled tree. Gives library code a hook for
  outer framing (e.g. JSON `{}`).
- **`Adt a`** — top-level framing wrapper for ADTs: carries the runtime type
  name and the inner Or/Variant tree. Gives library code a hook distinct
  from records.

The module is auto-imported via the prelude (`src/stdlib/prelude.saga`).
`deriving (Generic)` works without an explicit import.

`Generic` is registered in `FUNCTIONAL_TRAITS` (`src/typechecker/check_traits.rs:17`)
— see "Trait System Features Generic Depends On" below.

### Disambiguation: Labeled vs Variant, Record vs Adt

Before Phase 5, the building blocks were just
`U1 / Leaf / Labeled / And / Or`. That was enough to capture the shape of
any record or ADT but it left library authors with no way to tell:

- A record field name from a sum constructor name (both became `Labeled`).
- A record's top-level framing from an ADT's (the type name lived on the
  `Rep__T` wrapper, which the routing-layer bridge discarded).

Phase 5 split those concerns. The compiler now emits a `Record "TypeName"`
wrapper on records and an `Adt "TypeName"` wrapper on ADTs, and uses
`Variant` (not `Labeled`) for the constructor-name layer inside an ADT.
A library that wants proper JSON-shaped output writes:

```saga
impl ToJson for Record a where {a: ToJson} {
  to_json (Record _ inner) = "{" <> to_json inner <> "}"
}
impl ToJson for Variant a where {a: ToJson} {
  to_json (Variant name payload) = "{\"" <> name <> "\": " <> to_json payload <> "}"
}
impl ToJson for Adt a where {a: ToJson} {
  to_json (Adt _ inner) = to_json inner    -- passthrough
}
```

Libraries that don't care about a given hook write a passthrough — the
required impl set grew from 5 to 8, but most of the new impls are
one-liners.

---

## The Derive Pipeline

Source: `src/derive.rs`

`expand_derives` runs pre-typecheck and walks `Decl::TypeDef` and
`Decl::RecordDef`. For each `deriving (...)` list, it dispatches:

1. **Hardcoded derives** (`Show`, `Debug`, `Eq`, `Ord`, `Enum`): synthesize
   tailored impls directly. Unchanged from the original derive system.
2. **`Generic`**: synthesize a `Rep__<TypeName>` `TypeDef` and a
   `Generic <T> <Rep__T>` `ImplDef`. Two decls per derive.
3. **Anything else** (user-defined traits like `ToJson`): route through Generic
   via `derive_routed`, which synthesizes a bridge impl and a delegating impl.
   Auto-includes `Generic` if not already listed.

Synthetic decls are **spliced after their parent decl**, not appended to the
end of the program. Earlier behavior appended at end-of-program but that
broke registration order for user where-app impls referencing the derived
`Generic`. Source order is preserved for downstream passes.

### The Rep Type

Naming convention: `Rep__<TypeName>`. Leading uppercase `R` is deliberate —
names starting with `_` lex as lowercase `Ident`, which would break user
ascriptions like `(to p : Rep__Person)`.

The Rep is a **one-constructor newtype**, not a type alias:

```saga
type Rep__Person = Rep__Person (Record (And (Labeled (Leaf String))
                                            (Labeled (Leaf Int))))
```

`type` defines an ADT in Saga, so the wrapping constructor (`Rep__Person ...`)
is required. `to` boxes through it; `from` pattern-matches to unbox. The
wrapping serves two purposes:

1. Lets the impl head be `Generic Person Rep__Person` (a bare upper ident),
   sidestepping a parser limitation on parenthesized parameterized types in
   trait args (`src/parser/decl.rs:947-969`, partly fixed for where-app
   slots in commit fbdaebd).
2. Gives library-defined codecs a per-type hook (`impl <Trait> for Rep__Person`)
   even if the bridge impl currently unwraps unconditionally.

### Rep Shape

**Records**: the And-of-Labeled tree is wrapped in `Record "TypeName" (...)`.

| Field count | Inner shape (wrapped in `Record "TypeName"`) |
|-------------|-------------|
| 0           | `U1` |
| 1           | `Labeled "f" (Leaf T)` |
| 2+          | Right-leaning And of `Labeled "f" (Leaf T)` per field |

So `record Person { name: String, age: Int }` produces
`Rep__Person (Record "Person" (And (Labeled "name" (Leaf String))
                                   (Labeled "age" (Leaf Int))))`.

**ADTs**: each variant is wrapped in `Variant "VariantName" <variant_shape>`,
the variants combine in a right-leaning Or chain, and the whole Or-tree is
wrapped in `Adt "TypeName" (...)`.

| Variant arity | Variant shape |
|---------------|---------------|
| 0             | `U1` |
| 1             | `Leaf T` or `Labeled "label" (Leaf T)` if the field is labeled |
| 2+            | Right-leaning And, same as records |

| Variant count | Outer shape (wrapped in `Adt "TypeName"`) |
|---------------|-------------|
| 1             | Just the `Variant` shape (no Or) |
| 2+            | Right-leaning Or chain of `Variant` shapes |

So `type Shape = Circle Float | Triangle` produces
`Rep__Shape (Adt "Shape" (Or (Variant "Circle" (Leaf Float))
                             (Variant "Triangle" U1)))`.

**`Labeled` inside `Variant`**: a labeled constructor field like
`Circle { radius: Float }` still uses `Labeled` for the field name —
`Variant "Circle" (Labeled "radius" (Leaf Float))`. Library authors who
care can dispatch on whether the `Labeled` is inside a `Record` (record
field) or a `Variant` (labeled constructor field).

**Parameterized types**: the Rep TypeDef carries the same type parameters
as the user type. For `record Box a { value: a }`, the Rep is
`type Rep__Box a = Rep__Box (Record (Labeled (Leaf a)))` and the impl is
`impl Generic (Box a) (Rep__Box a)`.

**Recursive types**: the recursive position becomes `Leaf <SelfType>`,
not unfolded. The recursion lives in the runtime dictionary, not the Rep
type. `dict_for_type` handles the cycle because the recursive `Type::Con`
has a top-level dict reference, not an inlined expansion. See "Why Recursion
Is Free" below.

### `to` and `from` Bodies

`to` is a constructor call that builds the Rep tree from the value's
fields/variants. `from` pattern-matches the Rep tree and reconstructs the
user value.

For ADTs, `to` is a case-match on the user value with one arm per variant,
each producing the right `Or_Left`/`Or_Right` path. `from` is a case-match
on the Rep with the inverse arms.

---

## The Routing Layer

Source: `src/derive.rs` (`derive_routed`, `synth_to_direction`,
`synth_from_direction`)

When `expand_derives` encounters a derive name that isn't hardcoded or
`Generic`, it routes through `derive_routed`. Two impls are synthesized per
routed derive:

1. **Bridge** — `impl <Trait> for Rep__T`:
   - Unwraps the Rep newtype and forwards to the inner tree.
   - For to-direction: `methodname (Rep__T inner) = methodname inner`.
   - For from-direction: case-matches on the wrapper (`Result`/`Maybe`/bare)
     and wraps the inner result back into `Rep__T`.

2. **Delegating** — `impl <Trait> for T where {Generic T r, <Trait> r}`:
   - For to-direction: `methodname x = methodname (to x)`.
   - For from-direction: case-matches on the wrapper around `methodname s`,
     then threads the inner Rep through `from`.

Why two impls? The where-app `<Trait> r` validation fires at
impl-registration time and needs a concrete `<Trait> Rep__T` impl to already
exist before the routed impl for `T` registers. Without the bridge, the
chain breaks at registration.

### Direction Detection

`classify_from_return` inspects the trait's single method:
- User type in parameter list → to-direction (e.g. `to_json : a -> String`).
- User type in return position → from-direction. Three supported wrappers:
  - Bare `a` (`from_json : String -> a`)
  - `Result a _` (`from_json : String -> Result a JsonError`)
  - `Maybe a` (`from_json : String -> Maybe a`)
- Anything else → diagnostic, no synthesis.

Multi-method traits and traits where the user type appears in neither side
also emit diagnostics.

### Per-Tparam Where Bounds

For parameterized targets, the synthesizer emits per-tparam old-form bounds
alongside the where-apps:

```
impl ToJson for Maybe a where {a: ToJson, Generic (Maybe a) r, ToJson r}
```

The `a: ToJson` bound is needed so body inference can resolve `ToJson a`
constraints arising from the bridge impl. Redundant for monomorphic types,
correct for parameterized ones.

### Auto-Include Generic

If the deriving list contains a non-hardcoded trait and doesn't already
include `Generic`, `Generic` is implicitly added. Same pattern as the
existing "Ord auto-includes Eq" logic.

---

## Trait System Features Generic Depends On

Generic deriving sits on top of several trait-system features added across
Phases 1-2:

### Multi-Parameter Traits

`trait Generic a r` is a two-parameter trait. The dict-passing infrastructure
in `src/elaborate.rs` already supported this (the dict-table key is
`(trait_name, trait_type_args, target_type)`).

### Functional-Trait Coherence Rule

`src/typechecker/check_traits.rs:17` defines `FUNCTIONAL_TRAITS`, a hardcoded
set of trait names (currently `Generic` and `Std.Generic.Generic`). For
traits in this set, impl registration enforces that the first parameter
determines the rest — there can be at most one `Generic Person ?` impl.
This gives us the practical guarantee of associated types without the
type-system machinery.

### Free Type Variables in Impl Where Clauses (Phase 1c)

The new constraint form `where {TraitName arg1 arg2 ...}` allows fresh type
variables that don't appear in the impl head. Stored as
`Decl::ImplDef.where_apps: Vec<TraitApp>` alongside the existing
`where_clause: Vec<TraitBound>` for the old `a: Trait` form.

Solver behavior (`check_pending_constraints` in `check_decl.rs`):
- Constraints with all-concrete args resolve normally.
- Constraints with fresh vars look up by bound args; for `FUNCTIONAL_TRAITS`
  the coherence rule pins the fresh args uniquely.
- Per-impl substitutions inherit bindings from earlier constraints in the
  same chain. Source order; no fixed-point iteration.

### Trait Method Var Freshening (Phase 1.5)

Before Phase 1.5, a multi-param trait's non-self type params were registered
once with shared `Type::Var`s. The first impl pinned the var globally; later
impls failed. Fix: at the start of each impl's body check, instantiate fresh
type variables for the trait's non-self params. See `register_impl` in
`check_traits.rs`.

### Call-Site Coherence Fallback (Phase 2b, extended in 2d/2e)

When constraint solving at a call site sees an unresolved trait extra (e.g.
`Generic Person ?r` with `?r` unbound), it consults the impls table by
self-type-only. For `FUNCTIONAL_TRAITS` with exactly one match, the extra is
pinned to the impl's stored args.

`ImplInfo.trait_type_args` is `Vec<Type>` (widened from `Vec<String>` in
Phase 2e). Plus `target_type_param_ids: Vec<u32>` lets the fallback
substitute the impl's stored tvars with the call site's concrete args —
materializing `Rep__Box Int` from a `Box Int` call site.

This fallback is **load-bearing**, not optional. For functional traits with
concrete-headed self types, it's the resolution path. The delegating impl
body `to_json (to p)` relies on it to pin `Generic Person r → r = Rep__Person`.

### Constraint Ordering Within Batches

`check_pending_constraints` sorts each batch so concrete-self constraints
process before Var-self ones. Without this, `ToJson r` queued by the
delegating impl could error as ambiguous before the paired `Generic T r`
in the same batch had a chance to pin `r`.

---

## Why Recursion Is Free

For `type IntList = Nil | Cons Int IntList deriving (Generic)`:

```
type Rep__IntList = Rep__IntList (Or (Labeled "Nil" U1)
                                     (Labeled "Cons" (And (Leaf Int) (Leaf IntList))))
```

The recursive `IntList` position becomes `Leaf IntList`. There is no
unfolding — the inner `IntList` value remains an `IntList`, not a Rep tree.

When the runtime constructs a dict for `ToJson IntList`:
- `dict_for_type(ToJson, [], IntList)` returns `DictRef("__dict_ToJson_IntList")`
  because `IntList = Type::Con("IntList", [])` has zero args.
- The dict is a top-level closure that references its own name. BEAM handles
  self-recursive top-level functions natively.
- When the closure is called on a `Cons _ rest`, it calls `to_json` on `rest`,
  which is just another top-level call to the same dict constructor.

No memoization or cycle detection is required in `dict_for_type` because the
recursive position bottoms out at a zero-arg `Type::Con` whose dict is a
name, not an inlined expansion.

---

## Bodies and Patterns: What `derive.rs` Actually Emits

The generators in `src/derive.rs` build AST nodes directly. Helper functions:

- `build_adt_rep_inner_type` / `build_variant_shape_type` — emit the right
  TypeExpr for variants/fields.
- `build_variant_shape_expr` / `or_wrap_expr` — emit the Expr that
  constructs the Or/Variant tree at runtime (used inside the `Adt "..."`
  wrapper in `to` bodies).
- `build_variant_shape_pat` / `or_wrap_pat` — emit the Pat that
  destructures the Or/Variant tree (used inside the `Adt _` wrapper in
  `from` bodies).
- `build_ctor_application` — emit a constructor call with field arguments.
- `field_rep_type_adt` — wrap a field type as `Leaf <ty>`, or `Labeled "n"
  (Leaf <ty>)` if the field has a label.

The routed-derive helpers (`synth_to_direction`, `synth_from_direction`,
`build_from_body`) follow the same direct-AST construction pattern, with
`build_from_body` parameterized by a `wrap` callback to share logic between
bridge and delegating impls.

---

## Known Limitations and Deferred Work

### Framing (Resolved in Phase 5)

Earlier versions of this design lacked a place for library codecs to hook
outer framing. Records and ADT variants both flowed through the same
`Labeled` instance, and the bridge discarded the type name. Phase 5
addressed this by adding three new building blocks (`Variant`, `Record`,
`Adt`) and routing derive output through them — see "The Building Blocks"
above. Library authors now have:

- `Labeled` vs `Variant` to distinguish record-field names from sum
  constructor names.
- `Record` and `Adt` as per-type framing hooks at the top of the Rep tree.

`derive_routed`'s bridge is unchanged — it still unwraps `Rep__T` and
forwards — but the inner shape now starts with `Record name (...)` or
`Adt name (...)`, so the framing hook lives in the library's
building-block instances, not in per-type bridge code.

### `Show`/`Debug` Stay Hardcoded

Phase 4 (migrating `Show`/`Debug` onto Generic routing) was investigated
and deferred. Without the framing redesign, the migration would regress
output quality for every type that derives `Show`, and the "user
overridability" argument inverts (overriding via building-block impls is
*global*, not per-type, so it's worse than today's `impl Show for Person`
escape hatch). `Show`/`Debug`/`Eq`/`Ord`/`Enum` remain in the hardcoded
branches of `expand_derives`.

### Multi-Method Traits

Routed derives support single-method traits only. Multi-method traits emit
a diagnostic. Generalization is mechanical but not yet implemented.

### `TraitBound` / `TraitApp` Dual Representation

The old `a: Trait` form (`TraitBound`) and new `TraitName arg1 arg2 ...`
form (`TraitApp`) coexist as parallel AST representations. Migrating
`TraitBound` → `TraitApp` wholesale would touch elaborator, LSP, formatter,
and doc generator. Deferred as cleanup, not a blocker.

### Custom Wrapper Types for From-Direction

`derive_routed`'s from-direction support recognizes `a`, `Result a _`, and
`Maybe a` as return-type wrappers. Custom wrappers (e.g. a library's
`type MyResult a = ...`) emit a diagnostic. Could be generalized by
parameterizing the wrapper detection over constructor-name pairs, but no
real-world need has surfaced.

---

## File-by-File Pointers

- `src/stdlib/Generic.saga` — building blocks and `Generic` trait
- `src/stdlib/prelude.saga` — auto-imports `Std.Generic`
- `src/derive.rs` — `expand_derives`, `derive_record_generic`,
  `derive_adt_generic`, `derive_routed`, `synth_to_direction`,
  `synth_from_direction`, `build_from_body`, `classify_from_return`
- `src/typechecker/check_traits.rs` — `FUNCTIONAL_TRAITS`,
  `register_impl`, `is_functional_trait`
- `src/typechecker/check_decl.rs` — `check_pending_constraints` (constraint
  ordering, call-site coherence fallback)
- `src/typechecker/mod.rs` — `ImplInfo` (with `trait_type_args: Vec<Type>`
  and `target_type_param_ids: Vec<u32>`)
- `src/parser/decl.rs` — `parse_where_clause`, parenthesized type
  applications in where-app args
- `src/ast.rs` — `Decl::ImplDef.where_apps: Vec<TraitApp>`, `TraitApp`
- `docs/trait-dict-passing.md` — companion doc on how dictionaries are
  constructed and passed at runtime
- `docs/planning/user-extensible-derives.md` — the implementation history,
  decisions, and deferred work

## Example References

- `examples/99-generic-spike.saga` — original hand-written validation
  (Phase 0)
- `examples/99b-generic-derived.saga` — record + Generic, monomorphic
- `examples/99c-generic-adt.saga` — ADT + Generic
- `examples/99d-generic-parameterized.saga` — parameterized record + ADT
- `examples/99e-generic-recursive.saga` — recursive ADT
- `examples/99f-generic-derived-tojson.saga` — routed to-direction (ToJson)
- `examples/99g-generic-derived-fromjson.saga` — routed from-direction
  (FromJson), full round-trip
