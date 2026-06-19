# Generic Deriving

Saga supports user-extensible `deriving` clauses via a `Generic` trait that
provides a structural representation of any record or ADT. Library authors
write trait instances over a small set of building-block types; users derive
those traits on their own types without compiler changes.

```
# User code
record Person { name: String, age: Int } deriving (Generic, ToJson)

# After derive expansion (conceptual)
type Rep__Person = Rep__Person (Record (And (Labeled 'name (Leaf String))
                                            (Labeled 'age  (Leaf Int))))

impl Generic Person (Rep__Person) {
  to p = Rep__Person (Record "Person"
                       (And (Labeled (Leaf p.name))
                            (Labeled (Leaf p.age))))
  from (Rep__Person (Record _ (And (Labeled (Leaf n))
                                   (Labeled (Leaf a))))) = { name: n, age: a }
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
type U1                       = U1
type Leaf a                   = Leaf a
type Labeled (n : Symbol) a   = Labeled a
type And l r                  = And l r
type Or l r                   = Or_Left l | Or_Right r
type Variant (n : Symbol) a   = Variant a
type Record a                 = Record String a
type Adt a                    = Adt String a

trait Generic a r {
  fun to   : a -> r
  fun from : r -> a
}
```

These are the structural pieces every Rep is built from:

- **`U1`** — empty contribution. Used for zero-field constructors.
- **`Leaf a`** — a primitive or user-typed value. The recursion bottoms out here.
- **`Labeled (n : Symbol) a`** — a record-field name carried as a type-level
  symbol (kind `Symbol`), paired with its inner shape. Library impls
  recover the field name via `symbol_name (Proxy : Proxy n)` under a
  `where {n : KnownSymbol}` bound. (Record-fields only — sum constructor
  names use `Variant`.)
- **`And l r`** — a product. Records and multi-field constructors fold into
  right-leaning And chains.
- **`Or l r`** — a sum. ADTs with 2+ variants fold into right-leaning Or chains.
- **`Variant (n : Symbol) a`** — a sum constructor name carried as a
  type-level symbol with its payload shape. Distinct from `Labeled` so
  library codecs can give different behaviour to record fields and
  constructor names. The name lives in the type so from-direction codecs
  can compare it against an input tag and fail when they mismatch — see
  "From-direction sum-type correctness" below.
- **`Record a`** — top-level framing wrapper for records: carries the runtime
  type name and the inner And/Labeled tree. Gives library code a hook for
  outer framing (e.g. JSON `{}`).
- **`Adt a`** — top-level framing wrapper for ADTs: carries the runtime type
  name and the inner Or/Variant tree. Gives library code a hook distinct
  from records.

The module is auto-imported via the prelude (`src/stdlib/prelude.saga`).
`deriving (Generic)` works without an explicit import.

`Generic` is a functional multi-parameter trait: the user type determines its
representation type. See "Trait System Features Generic Depends On" below.

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
impl ToJson for Variant (n : Symbol) a where {n: KnownSymbol, a: ToJson} {
  to_json (Variant payload) =
    "{\"" <> symbol_name (Proxy : Proxy n) <> "\": " <> to_json payload <> "}"
}
impl ToJson for Adt a where {a: ToJson} {
  to_json (Adt _ inner) = to_json inner    -- passthrough
}
```

Libraries that don't care about a given hook write a passthrough — the
required impl set grew from 5 to 8, but most of the new impls are
one-liners.

### From-direction sum-type correctness

`Variant` and `Labeled` carry their names at the **type level** (kind
`Symbol`) rather than as value-level `String` fields. This is what makes
from-direction sum-type decoders work correctly.

Pre-symbol, the synthesized `from` for an ADT looked like

```saga
from (Rep__Role (Adt _ (Or_Left  (Variant _ _)))) = Admin
from (Rep__Role (Adt _ (Or_Right (Or_Left  (Variant _ _))))) = Editor
from (Rep__Role (Adt _ (Or_Right (Or_Right (Variant _ _))))) = Viewer
```

The variant name was wildcarded, so the library's `FromJson for Or` had
to "try left, fall back to right" by position — and the wrong branch
silently succeeded. Decoding `{"Editor": null}` into
`Role = Admin | Editor | Viewer` always returned `Admin`, regardless of
the JSON tag.

With names at the type level, the library's from-direction impl can
recover the expected name via `KnownSymbol` and reject the wrong tag:

```saga
impl FromJson for Variant (n : Symbol) a where {n: KnownSymbol, a: FromJson} {
  from_json s =
    if s == symbol_name (Proxy : Proxy n) then
      case from_json s {
        Ok x -> Ok (Variant x)
        Err e -> Err e
      }
    else
      Err "variant tag mismatch"
}
```

Now `Or`'s "try left, fall back to right" actually picks the right
variant: the wrong branch fails on the tag mismatch, the right one
succeeds. See `sum_type_fromjson_picks_correct_variant_by_tag` in
`tests/codegen_integration.rs` for the e2e test.

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
4. **Applied functional bridge derives** (`deriving (Selectable User)`):
   synthesize the named-representation bridge for a functional two-parameter
   trait whose required methods have shape `selection -> row` or
   `selection -> Wrapper row`. `Selectable` is the motivating Kraken bridge
   use case, but the compiler path is trait-name agnostic.
5. **Record synthesis** (`deriving (Trait NewName)` where `Trait` declares a
   `synthesizes` clause): *synthesize a new record type* by mapping the carrier
   record's fields through a library-defined field-map trait, plus its `Generic`,
   any attached derives, and a functional-dependency link impl. Unlike (4), the
   type argument names a type that does **not** exist yet, and the whole transform
   is library-defined — the compiler hardcodes no trait or type names. See
   [Record Synthesis](#record-synthesis).

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
| 1           | `Labeled 'f (Leaf T)` |
| 2+          | Right-leaning And of `Labeled 'f (Leaf T)` per field |

So `record Person { name: String, age: Int }` produces
`Rep__Person (Record "Person" (And (Labeled 'name (Leaf String))
                                   (Labeled 'age (Leaf Int))))`.

**ADTs**: each variant is wrapped in `Variant 'VariantName <variant_shape>`,
the variants combine in a right-leaning Or chain, and the whole Or-tree is
wrapped in `Adt "TypeName" (...)`.

| Variant arity | Variant shape |
|---------------|---------------|
| 0             | `U1` |
| 1             | `Leaf T` or `Labeled 'label (Leaf T)` if the field is labeled |
| 2+            | Right-leaning And, same as records |

| Variant count | Outer shape (wrapped in `Adt "TypeName"`) |
|---------------|-------------|
| 1             | Just the `Variant` shape (no Or) |
| 2+            | Right-leaning Or chain of `Variant` shapes |

So `type Shape = Circle Float | Triangle` produces
`Rep__Shape (Adt "Shape" (Or (Variant 'Circle (Leaf Float))
                             (Variant 'Triangle U1)))`.

**`Labeled` inside `Variant`**: a labeled constructor field like
`Circle { radius: Float }` still uses `Labeled` for the field name —
`Variant 'Circle (Labeled 'radius (Leaf Float))`. Library authors who
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

`classify_method_direction` runs **per trait method** (Phase 6 lifted the
prior single-method restriction):
- User type in parameter list only → to-direction (e.g. `to_json : a -> String`).
- User type in return position only → from-direction. The return shape is
  inspected structurally (Phase 7) — any wrapper whose `TypeDef` is in
  scope is supported, including user-defined wrappers like
  `DbResult a = DbOk a | DbErr DbError | DbNoRows`. See "Structural
  Wrapper Inspection" below.
- User type on both sides (`a -> a`) → diagnostic, no synthesis.
- User type on neither side → diagnostic, no synthesis.
- Multi-parameter methods → diagnostic, no synthesis.

If any method in the trait fails classification, the whole derive aborts
with a diagnostic naming the offending method; partial synthesis is never
emitted.

### Structural Wrapper Inspection (Phase 7)

`classify_from_return` doesn't recognize wrappers by name. Instead, it:

1. Extracts the return type's head and type args via
   `extract_head_and_args`.
2. Looks the head up in the merged imported/local decls bundle (see
   "Cross-Module Lookup" below).
3. Walks the wrapper's variants (sum) or fields (record) to find positions
   of the trait's self type variable.
4. Produces a `FromShape` enum: `Bare | Sum { variants } | Record { fields }`.
   Each variant/field carries `field_a_positions: Vec<bool>` marking
   which payload slots are direct `a` occurrences.

`build_from_body` consumes the `FromShape` and emits the appropriate
case-match. For sum wrappers, one arm per variant with positional field
binders; for record wrappers, one constructor pattern with named binders.
The `wrap` callback (bridge: `Rep__T (...)`; delegating: `from`) is
applied at every `a`-position.

`Result` and `Maybe` have no special-case — they go through the same
structural path as any user wrapper, courtesy of Phase 6.5's prelude
visibility. Dropping the special-cases was the cleaner option once
cross-module lookup landed.

**Rejected cases** (with diagnostics):
- Opaque wrapper (TypeDef not in scope): `cannot derive ... — wrapper
  type "W" is opaque (no Generic representation available)`.
- Wrapper with no `a`-position (e.g. `Hide a = Hide String`): `no
  user-type position found in wrapper "W"`.
- Nested `a` (e.g. `Wrapped a = Yep (List a) | Nope`): `user type
  appears at non-leaf position in variant "Yep"`. Recursing through
  `List`'s Generic is possible future work but introduces termination
  questions for self-referential containers.

### Cross-Module Lookup (Phase 6.5)

Routed-derive trait lookup, wrapper lookup, and building-block lookups
all consult an `ImportedDecls` bundle threaded into `expand_derives`:

```rust
pub struct ImportedDecls {
    pub traits: HashMap<String, TraitInfo>,
    pub types:  HashMap<String, WrapperTypeInfo>,
    pub records: HashMap<String, WrapperRecordInfo>,
}
```

`collect_imported_decls` walks the prelude's imports first (so `Result`,
`Maybe`, and `Std.Generic` building blocks are visible everywhere
without explicit imports), then the user program's imports. Local
`TypeDef`/`RecordDef`/`TraitDef` overlays the imported bundle.

This is what makes a multi-module workflow actually work: a library
module exporting `trait ToJson` + building-block impls, a user module
that `import ToJsonLib; record Person {...} deriving (ToJson)`. Before
Phase 6.5, the synthesizer couldn't see imported `TraitDef`s and the
derive failed silently. Now the lookup is uniform — local and imported
decls are merged before expansion.

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

### Applied Functional Bridge Derives

Applied derives are intentionally narrow. A derive like:

```saga
record User { id: Int, name: String } deriving (Generic)

record Users source {
  id: Column source 'id Int,
  name: Column source 'name String,
} deriving (Generic, Selectable User)
```

requires `Selectable` to be a functional two-parameter trait:

```saga
trait Selectable selection row | selection -> row {
  fun to_row : selection -> row
}
```

The compiler generates two impls:

```saga
impl Selectable Rep__User for Rep__Users source {
  to_row (Rep__Users inner) = Rep__User (to_row inner)
}

impl Selectable User for Users source
  where {
    Generic (Users source) selection_rep,
    Generic User row_rep,
    Selectable selection_rep row_rep,
  }
{
  to_row value = from (to_row (to value))
}
```

The compiler generates this shape for any trait that satisfies the same
contract, not just a trait literally named `Selectable`. Every non-default
method must be pure and have shape `selection -> row` or
`selection -> Wrapper row`; defaulted methods are left alone. If a trait has
multiple required methods, the derive synthesizes a bridge/delegating body for
each one.

Wrapper returns have two supported forms. Transparent unary wrappers are
rewritten through their constructor:

```saga
type Projection a = Projection a

trait Selectable selection row | selection -> row {
  fun to_projection : selection -> Projection row
}
```

For the representation bridge, the compiler rewrites through the wrapper
constructor:

```saga
impl Selectable Rep__User for Rep__Users source {
  to_projection (Rep__Users inner) =
    case to_projection inner {
      Projection row_rep -> Projection (Rep__User row_rep)
    }
}
```

The public impl similarly wraps `from row_rep` back into `Projection`.

Opaque or otherwise non-transparent unary wrappers are lifted through a
same-module `map` function. This is the Kraken shape:

```saga
opaque type Projection a = Projection (ProjectionDef a)

pub fun map : (a -> b) -> Projection a -> Projection b

trait Selectable selection row | selection -> row {
  fun to_projection : selection -> Projection row
}
```

For an imported `Db.Projection`, the bridge uses `Db.map`:

```saga
impl Selectable Rep__User for Rep__Users source {
  to_projection (Rep__Users inner) =
    Db.map Rep__User (to_projection inner)
}
```

The public impl uses the same lifting idea with `from`:

```saga
impl Selectable User for Users source {
  to_projection value =
    Db.map from (to_projection (to value))
}
```

The inner structural walk is still provided by the library's normal
`Leaf`/`Labeled`/`And`/`Record` impls. The applied derive only supplies the
named-wrapper bridge that ordinary structural routing cannot infer.

Applied bridge derives accept one named row type argument (`User` or a
parenthesized named application such as `(Box Int)`). They reject hardcoded
derives with arguments, non-functional traits, traits whose non-default methods
are not pure `selection -> row` / `selection -> Wrapper row`, wrapper returns
without an in-scope `map`, and anonymous/tuple/function/symbol row arguments.
The row type must already expose a `Generic` representation, usually via
`deriving (Generic)`.

---

## Trait System Features Generic Depends On

Generic deriving sits on top of several trait-system features added across
Phases 1-2:

### Multi-Parameter Traits

`trait Generic a r` is a two-parameter trait. The dict-passing infrastructure
in `src/elaborate.rs` already supported this (the dict-table key is
`(trait_name, trait_type_args, target_type)`).

### Functional Dependencies

`Generic` relies on the same functional-dependency rule now available to
user-written multi-parameter traits: the first parameter determines every
remaining parameter. This gives us the practical guarantee of associated types
without the type-system machinery. For example, there can be at most one
`Generic Person ?` impl, so `Generic Person r` can pin `r` to `Rep__Person`.

Historically this was hardcoded through `check_traits::FUNCTIONAL_TRAITS`;
`Generic` and `Std.Generic.Generic` still live in that legacy list because the
stdlib declaration predates the source-level `| a -> r` syntax. New traits can
declare the rule directly:

```saga
trait Selectable selection row | selection -> row {
  fun to_row : selection -> row
}
```

See
[`docs/typechecking.md`](typechecking.md#multi-parameter-traits-and-functional-dependencies)
for the general solver behavior.

### Free Type Variables in Impl Where Clauses (Phase 1c)

The new constraint form `where {TraitName arg1 arg2 ...}` allows fresh type
variables that don't appear in the impl head. Stored as
`Decl::ImplDef.where_apps: Vec<TraitApp>` alongside the existing
`where_clause: Vec<TraitBound>` for the old `a: Trait` form.

Solver behavior (`check_pending_constraints` in `check_decl.rs`):
- Constraints with all-concrete args resolve normally.
- Constraints with fresh vars look up by bound args; for functional traits,
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
self-type-only. For functional traits with exactly one match, the extra is
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

## Record Synthesis

Source: `src/derive.rs` (`derive_synthesize`, `map_field_via_trait`),
`src/parser/decl.rs` (`synthesizes` clause), `src/ast.rs` (`SynthesisSpec`).

Every other derive *relates the derive to existing types*. This one is the
exception: it **synthesizes a brand-new user-facing record type** from a per-field
transform of another record, and makes that synthetic type behave like a
hand-written one for the rest of the pipeline.

The key design constraint: **the compiler hardcodes no trait or type names.** The
entire policy — which fields map to what, which encoder to attach, which trait
links the carrier to the result — is declared *in library code*. The compiler
provides only the general mechanism. (An earlier cut hardcoded Kraken's
`Insertable`/`Col`/`Generated`/`Writable`/`InsertRow`; this replaces that.)

### The library declares the synthesis

A trait opts in with a `synthesizes via <FieldMap> deriving (...)` clause. The
motivating Kraken use case — generating a table's "insert shape" from its
column-record schema:

```saga
-- field-type map: a functional `col -> ins` relation; its impls ARE the
-- per-field rewrite table. Method-less; read syntactically at derive time.
trait InsertField col ins | col -> ins
impl InsertField a            for (Col a)        {}
impl InsertField (Writable a) for (Generated a)  {}

-- the link trait declares the synthesis
trait Insertable cols ins | cols -> ins
  synthesizes via InsertField deriving (InsertRow)
```

The carrier opts in with the familiar `deriving (Trait Arg)` surface, where the
argument **names a type that does not exist yet and is created by the derive**:

```saga
record Users { id: Generated Int, name: Col String, age: Col Int }
  deriving (Insertable UsersInsert)
```

Carrier vs. synthesized roles come from the link trait's functional dependency:
the determinant (`cols`) is the carrier, the determined parameter (`ins`) is the
synthesized type.

### What `derive_synthesize` emits

Four declarations, spliced after the carrier (in this order):

1. **The synthetic record.** Each field type is rewritten by
   `map_field_via_trait`: it finds the `via`-trait impl whose `for` pattern
   unifies with the field type and returns its substituted other argument
   (`Generated Int` matches `… for (Generated a)`, `a = Int`, output `Writable a`
   ⇒ `Writable Int`). This reuses the same `te_unify`/`te_apply` the applied
   bridge uses for scope specialization, over the impls `DeriveScope` already
   collects. Field names/order preserved; visibility inherited from the carrier.

   ```saga
   record UsersInsert { id: Writable Int, name: String, age: Int }
   ```

2. **Its `Generic`/`Rep__`** via `derive_record_generic` — the same path a
   hand-written `deriving (Generic)` takes.

3. **The attached derives** (`deriving (InsertRow)` from the clause), each routed
   onto the new record via `derive_routed`/`generate_record_derive` exactly as on
   a hand-written record. The user cannot attach `deriving (InsertRow)` to a type
   they never see, so the synthesis does it for them. Must follow the Generic
   decls (the routed bridge targets the just-emitted `Rep__`).

4. **A functional-dependency link** `impl Insertable UsersInsert for Users`. The
   determinant (`cols`) is the impl target; the determined parameter (`ins`) is
   the single extra trait argument. Method-less — it exists only so a caller typed
   `Dml.insert : Table cols -> ins -> _ where {cols: Insertable ins}` recovers the
   synthesized type from `cols` alone via the existing fundep-improvement path
   (`improve_pending_fundeps`). No improvement logic is duplicated.

### Cross-module name resolution

The `synthesizes` clause's trait names (`InsertField`, `InsertRow`) are qualified
to the link trait's defining module when collected (`qualify_synthesis_spec`), so
they resolve at any derive site: an imported module registers every public trait
under its `Module.Name` key regardless of the `exposing` list, and the carrier's
module must import the link trait's module to name the trait at all. The field-map
impls are matched by bare trait name against the impls `DeriveScope` collects
(coherence-global, brought in on import).

### Why a new `RecordDef` flows through the pipeline

`expand_derives` already splices synthetic `TypeDef`s (every `Rep__T`) into the
program, and it runs **per-module before that module is typechecked and before
its exports are computed**. So an appended `Decl::RecordDef` is registered in the
type environment, field-checked, and — when `public` — exported from
`build_module_exports` (which iterates the post-expansion program) exactly like a
hand-written record. Cross-module *use* of the synthesized type works; cross-module
*`deriving` on* it does not, because `collect_imported_decls` re-parses other
modules' source, which never contains the synthetic decl.

### Limitations

- **Non-parameterized carriers only.** A parameterized schema (e.g.
  `Users source meta` with `Column source meta name a` fields) needs scope
  specialization the syntactic field map can't express; `derive_synthesize`
  rejects it with a diagnostic rather than miscompiling.
- A field whose type matches no (or more than one) `via`-trait impl is a derive
  error, not a silent drop — which column types are insertable is library-defined.
- `synthesizes` is a contextual soft keyword (only special in a trait header), so
  a trait type parameter literally named `synthesizes` is not allowed.

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

As of Phase 6, multi-method traits are supported. Each trait method is
classified independently — one trait can mix to-direction and
from-direction methods (e.g. a unified `JsonCodec` with both `encode : a
-> String` and `decode : String -> Result a Error`). The bridge impl and
the delegating impl each carry one `ImplMethod` entry per trait method.

If any single method fails direction detection — return-shape unsupported,
self on both sides, self on neither side, or multi-parameter — the entire
derive aborts with a diagnostic naming the offending method. Partial
impls are never synthesized.

See `examples/99h-generic-derived-codec.saga` for the headline mixed
encode/decode case.

### Error Message Rewriting for Routed-Derive Constraint Failures (Phase 3c)

Constraint failures inside synthesized routed-derive impls would
otherwise surface as `no impl of ToJson for Labeled` (or `And`, etc.) —
useless to users who never wrote those types. Phase 3c added a
diagnostic-rewrite path:

- `Decl::ImplDef` carries an optional `routed_derive_info:
  Option<RoutedDeriveInfo>` field. Populated by `derive_routed` on both
  the bridge and delegating impls; `None` for everything else.
- `TraitState.routed_constraint_origins: HashMap<NodeId,
  RoutedDeriveInfo>` indexes constraints by the impl-body NodeIds that
  generated them. Populated by `register_all_impls` via a length-
  snapshot of `pending_constraints` taken around each routed impl's
  body check.
- `check_pending_constraints` uses a `rewrite_diag` closure: when a
  failing constraint's NodeId hits the table, the default `no impl of
  X for Y` (and ambiguity / function-type / record-type variants) is
  swapped for `cannot derive \`<Trait>\` for \`<Target>\`: missing
  required instance (<failed_constraint>). Make sure all field types
  implement \`<Trait>\`, or also derive \`<Trait>\` on them.`

The rewritten diagnostic is anchored at the `deriving` span carried on
`RoutedDeriveInfo`, not at the synthesized impl's location — so the
error points at user code. Hand-written impls without the marker keep
the default diagnostics.

### `TraitBound` / `TraitApp` Dual Representation

The old `a: Trait` form (`TraitBound`) and new `TraitName arg1 arg2 ...`
form (`TraitApp`) coexist as parallel AST representations. Migrating
`TraitBound` → `TraitApp` wholesale would touch elaborator, LSP, formatter,
and doc generator. Deferred as cleanup, not a blocker.

### Custom Wrapper Types for From-Direction (Resolved in Phase 7)

Earlier versions of `classify_from_return` hardcoded recognition for
`a`/`Result a _`/`Maybe a`. Phase 7 replaced this with structural
inspection: any wrapper type whose `TypeDef` is in scope can serve as a
from-direction return shape. `Result` and `Maybe` no longer need special-
case treatment — they're inspected the same way as user-defined wrappers.
See "Structural Wrapper Inspection" under "The Routing Layer" above.

The only return shapes still rejected are: opaque wrappers (no TypeDef
visible), wrappers with no `a`-position, and wrappers where `a` appears
at a non-leaf position (e.g. `Wrapped a = Yep (List a) | Nope`). The
last case could in principle be supported by recursing through `List`'s
Generic, but the implementation question of termination on self-
referential containers makes it deferred work, not blocked work.

---

## File-by-File Pointers

- `src/stdlib/Generic.saga` — building blocks and `Generic` trait
- `src/stdlib/prelude.saga` — auto-imports `Std.Generic`
- `src/derive.rs` — `expand_derives`, `derive_record_generic`,
  `derive_adt_generic`, `derive_routed`, `derive_synthesize`,
  `map_field_via_trait`, `qualify_synthesis_spec`, `classify_method_direction`,
  `synth_method_pair`, `build_from_body`, `classify_from_return`,
  `collect_imported_decls`, `collect_decls_from_imports`,
  `extract_head_and_args`
- `src/ast.rs` — `SynthesisSpec`, `TraitDef.synthesis`
- `src/parser/decl.rs` — `parse_trait_def` (the `synthesizes` soft keyword)
- `src/formatter/decl.rs` — `format_trait_def` (re-emits the `synthesizes` clause)
- `src/ast.rs` — `Decl::ImplDef.where_apps`, `Decl::ImplDef.routed_derive_info`,
  `TraitApp`, `RoutedDeriveInfo`
- `src/typechecker/check_traits.rs` — `FUNCTIONAL_TRAITS`,
  `register_trait_def`, `register_impl`, `TraitInfo.is_functional`
- `src/typechecker/check_decl.rs` — `check_pending_constraints` (constraint
  ordering, call-site coherence fallback)
- `src/typechecker/mod.rs` — `ImplInfo` (with `trait_type_args: Vec<Type>`
  and `target_type_param_ids: Vec<u32>`), `TraitState.routed_constraint_origins`
- `src/parser/decl.rs` — `parse_where_clause`, parenthesized type
  applications in where-app args
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
  (FromJson) with Result wrapper, full round-trip
- `examples/99h-generic-derived-codec.saga` — multi-method mixed-direction
  trait (`JsonCodec` with `encode` + `decode`)
- `examples/99i-generic-derived-custom-wrapper.saga` — user-defined
  three-state wrapper (`DbResult a`) threaded through structural
  from-direction synthesis (Phase 7)
