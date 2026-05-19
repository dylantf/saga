# User-Extensible Derives via Generic

## Goal

Let library authors define new derivable traits (e.g. `ToJson`, `FromJson`,
`ToPgRow`, `FromPgRow`, `ToCsv`, `FromCsv`) without modifying the compiler.
Today, every derive is hardcoded in `src/derive.rs` — adding a new one requires
a compiler change and release. With three real consumer libraries already
in flight and more coming, this doesn't scale.

The approach is the **GHC.Generics** pattern: one compiler-supported derive
(`Generic`) produces a structural "boring version" of a type plus an
isomorphism (`to`/`from`). Library authors write trait instances over a small
set of building-block types (`U1`, `Leaf`, `Labeled`, `And`, `Or`). The
compiler then synthesizes per-type instances that delegate through `Generic`
when a user writes `deriving (ToJson)`.

This is **not** a macro system. There's no AST-as-data, no staged compilation,
no hygiene story to design. It's a small, targeted set of additions to the
existing trait machinery.

## Why this works in Saga specifically

Reading [docs/trait-dict-passing.md](../trait-dict-passing.md) revealed that
most of the substrate is already in place:

- Multi-parameter traits (`trait Generic a r`) — already supported. Avoids
  needing associated types.
- Recursive dict composition (`dict_for_type`) — already builds nested dicts
  for parameterized types. This is structurally identical to what `Generic`
  needs.
- Conditional impls with `where`-clause constraints on type parameters —
  already supported (`impl Show for List a where {a: Show}`).
- NodeId-keyed evidence with substitution-aware var-name resolution — already
  supported. Handles disambiguating multiple dicts for the same trait.
- Occurrence-based dict-param disambiguation — already supported.
- Deferred trait constraint solving — already supported.

What's missing is small: overlap detection, free type vars in impl `where`
clauses, the `Generic` derive itself, and a routing layer that connects user
`deriving (X)` clauses to library-provided `Rep`-walking instances.

## What we are NOT building

To keep scope bounded, the following are explicitly out:

- **Associated types.** `trait Generic a r` with a coherence rule is good
  enough for this use case. Associated types remain a useful future feature
  but are not on the critical path.
- **Higher-kinded types.** Not needed. `Rep` is always a concrete (possibly
  parameterized) type at the use site.
- **Overlapping instances.** The "deriving X routes through Generic" path
  synthesizes a concrete per-type instance, so no overlap rules are required.
- **A general macro system.** Out of scope; revisit only if `Generic` proves
  insufficient for real use cases.
- **Type-level strings.** Field/constructor labels live as runtime values
  inside `Labeled` dictionaries. Cost is negligible; complexity savings are
  substantial.

## End-to-end picture

Given a user type:

```saga
record Person { name: String, age: Int }
  deriving (Generic, ToJson)
```

The compiler generates:

1. A `Rep` type for `Person`:
   ```saga
   type RepPerson = And (Labeled (Leaf String)) (Labeled (Leaf Int))
   ```
2. A `Generic` impl with `to`/`from`:
   ```saga
   impl Generic Person RepPerson {
     to p   = And (Labeled "name" (Leaf p.name)) (Labeled "age" (Leaf p.age))
     from (And (Labeled _ (Leaf n)) (Labeled _ (Leaf a))) = { name: n, age: a }
   }
   ```
3. A `ToJson` impl that delegates through `Generic`:
   ```saga
   impl ToJson for Person {
     to_json p = to_json (to p : RepPerson)
   }
   ```

The library `json_lib` provides:

```saga
impl ToJson for U1                                       { ... }
impl ToJson for Leaf a    where {a: ToJson}              { ... }
impl ToJson for Labeled a where {a: ToJson}              { ... }
impl ToJson for And l r   where {l: ToJson, r: ToJson}   { ... }
impl ToJson for Or l r    where {l: ToJson, r: ToJson}   { ... }
```

The existing `dict_for_type` machinery composes these recursively at the call
site, exactly the same way it composes `Show (List String)` today.

## Phases

The work splits into four phases, each independently shippable and useful on
its own. Each phase ends with a working, testable state.

---

### Phase 0: Spike — Hand-Written Validation [COMPLETE]

**Status**: Done. See `examples/99-generic-spike.saga`. Spike succeeded for
both 2-field and 3-field records; nested `And`/`Labeled`/`Leaf` dict
composition works as predicted with zero compiler changes.

**Findings to carry forward**:

- **Parser limitation in impl trait args.** `src/parser/decl.rs:947-969`
  accepts only bare `UpperIdent` or `Ident` in `impl Trait <args> for ...`,
  not parenthesized parameterized type expressions. This means Phase 2b
  cannot inline the `Rep` as `impl Generic (And (Labeled ...) ...) for Person`
  — the synthesized `Rep` must be emitted as a named `TypeDef` and referenced
  by name (`impl Generic __Rep_Person for Person`). The plan already calls
  for a named TypeDef so this is consistent, but **Phase 2b must NOT** try
  to emit inline rep types as a shortcut. Optionally, a small parser
  extension to accept full `TypeExpr` in trait args would be a nice cleanup
  but is not on the critical path.
- **`type` defines an ADT, not an alias.** The generated `Rep` is a
  one-constructor newtype wrapping the building-block tree. `to`/`from` must
  box/unbox through that wrapping constructor. The spike used
  `PersonRep (And ...)` and it worked cleanly.
- **Outer framing decision deferred.** The spike put `{` and `}` in a
  per-type `ToJson PersonRep` impl that wraps the inner comma-separated
  output from `And`/`Labeled`. In production we need to decide whether the
  library-defined `ToJson` for `Labeled`/`And` includes the outer braces, or
  whether the routing-layer-synthesized `ToJson for Person` impl provides
  them. This affects nested-record composition. **Decision to make during
  Phase 3a, before writing the first real codec library.** Recommended
  default: the building-block impls produce the outer braces (i.e. `Labeled`
  or a dedicated `record-shaped` marker carries the framing). Otherwise
  nested records produce `{"outer": "name": "Alice"}` with no inner braces.
- **No type-annotation disambiguation needed.** Solver handled three nested
  `Labeled (Leaf …)` dicts with no annotations beyond the `: PersonRep`
  ascription on the `to` result. The `current_dict_params` fallback and
  occurrence disambiguation were not exercised — evidence resolution covered
  everything.
- **Substrate risk retired.** "`dict_for_type` doesn't handle Rep shape" is
  confirmed Low → effectively zero. Remove from active risk list.

**Original goal**: Confirm `dict_for_type` actually composes the way the
dict-passing doc claims when fed `Rep`-shaped types. **Budget: 1-2 days.**

Before writing any compiler code, prototype the entire chain by hand in a
single `.saga` file:

- Hand-define `U1`, `Leaf a`, `Labeled a`, `And l r`, `Or l r` as ADTs.
- Hand-define `trait Generic a r` with `to` / `from`.
- Hand-write `impl Generic Person RepPerson` for one record type.
- Hand-write the five `ToJson` instances for the building blocks.
- Hand-write `impl ToJson for Person` that calls `to_json (to p)`.
- Compile and run. Verify the output JSON is correct.

**Success criterion**: `cargo run -- run spike.saga` prints correct JSON for a
`Person` value.

**If this fails**: the failure mode tells us what's broken in the substrate
before we've invested in any derive infrastructure. The most likely failure is
in dict composition for the nested `And`/`Labeled` shape. Fix or work around
before proceeding.

**If this succeeds**: every subsequent phase is "automate this by hand-written
code". No more substrate risk.

Deliverable: a working `spike.saga` checked in under `examples/` as a
reference for what the eventual generated code should look like.

---

### Phase 1: Trait System Tightening

**Goal**: Fix the small gaps in the trait system that the rest of the plan
depends on. **Budget: ~1 week.**

These are useful improvements regardless of whether the rest of the plan
ships.

#### 1a. Overlap detection in `register_impl` [DONE]

Pre-existing as of commit 360f287. Phase 1 added: improved diagnostic
wording, five new tests covering parameterized duplicates, derive +
hand-written conflicts, and the negative cases (different traits / different
types).

#### 1b. Coherence rule for functionally-determined trait parameters [DONE]

Implemented as a hardcoded set `FUNCTIONAL_TRAITS` in `check_traits.rs`
containing `Generic` and its canonical `Std.Generic.Generic`. Coherence and
duplicate checks now fire **before** method-body type-checking — the body
typechecker mutates the substitution map, which previously masked
duplicate/coherence errors with confusing type-mismatch diagnostics.

#### 1c. Free type variables in impl `where` clauses [DONE — commit f5ad456]

For traits where the first parameter should determine the others (notably
`Generic a r`), enforce at registration time that no two impls share the same
first parameter with different remaining parameters.

This is a per-trait flag rather than a language-wide feature. Mechanism: a
trait can opt into "first param determines the rest" via an attribute or a
hardcoded set initially. Start with hardcoded — `Generic` is the only trait
that needs this for now.

**Files**: `src/typechecker/check_traits.rs`.

**Test**: two `impl Generic Person _` with different `Rep` types → error.

#### 1c. Free type variables in impl `where` clauses

**Blocker discovered during Phase 1**: the current `where`-clause grammar is
`tvar: TraitName extras` (`src/parser/decl.rs:858`) — the leading `tvar` is a
lowercase identifier interpreted as the trait's first (self) parameter. There
is no grammar production for a bare `TraitName arg1 arg2 ...` constraint, and
the leading position cannot be a concrete type. So the natural syntax
`where {Generic Person r, ToJson r}` will not parse, and the closest
expressible form `r: Generic Person` actually means `Generic r Person` — the
opposite parameter order from what we need.

**Resolution**: introduce a new constraint form in the where clause and treat
the existing `tvar: Trait` form as sugar that desugars to it.

New form (proposed grammar):

```saga
impl ToJson for Person where {Generic Person r, ToJson r}
```

Each where-clause entry is parsed as one of:
- `tvar: Trait1 + Trait2 + ...` (existing form, unchanged).
- `TraitName arg1 arg2 ...` (new form) — a bare trait application with type
  expressions in any position, including fresh type variables.

The two forms coexist. The existing form is sugar: `a: Show + Debug`
desugars to `Show a, Debug a` (two new-form entries).

**AST**: replace (or augment) `TraitBound { type_var, traits }` with a new
`Constraint::TraitApp { trait_name, type_args: Vec<TypeExpr> }`. Old
`TraitBound` entries lower to a sequence of `TraitApp`s during parsing or
name-resolution.

**Solver semantics for fresh vars**: a type variable appearing in a where
clause but **not** in the impl's `type_params` is an implicit existential.
Process where-clause constraints in source order. For each `TraitApp`:
- If all type args are concrete (or already bound from earlier in the
  chain), look up the impl normally.
- If some args are fresh, look up the impl by the *bound* args; the
  coherence rule from 1b ensures a unique answer for `FUNCTIONAL_TRAITS`,
  which pins the fresh args. For non-functional traits where the fresh var
  can't be uniquely determined, error.

Cap iterations and bail with a clear "could not resolve constraint chain"
error if the loop doesn't converge.

**Files**: `src/parser/decl.rs`, `src/ast.rs`, `src/typechecker/check_traits.rs`,
`src/typechecker/check_decl.rs`.

**Test**: impl with fresh var in where clause that resolves cleanly → ok;
fresh var that's ambiguous → error; no fresh vars (existing behavior) →
unchanged.

**Estimated scope**: 2-3 days. This is now its own sub-phase (1c) and should
be tackled before Phase 2 starts.

**Phase 1 deliverable**: trait system catches duplicate impls (done),
enforces single-instance-per-key for marked traits (done), and permits free
vars in impl-level where clauses via the new constraint form (pending).
Existing examples and tests pass.

---

### Phase 1.5: Trait Method Var Freshening [DONE — commit 8ccff2b]

**Goal**: Fix a pre-existing bug discovered during Phase 1b. **Budget: 1
day.**

When a trait has non-self type parameters (e.g. `trait Generic a r` —
where `a` is self and `r` is extra), the trait method signatures are
registered once with a single `Type::Var` for each extra param. The first
`impl Generic RepA for Foo` unifies that shared var with `RepA`, leaving it
fixed in the global state. Any subsequent `impl Generic RepB for Bar` then
fails to unify `RepB` with the already-pinned `RepA`.

Invisible today because no production code defines multiple impls of a
multi-param trait. Phase 2 will hit this on the first compile after the
second `deriving (Generic)` — every user record/ADT generates its own
`Generic` impl with a different `Rep`.

**Fix**: at the start of each impl's body check, instantiate fresh type
variables for the trait's non-self type params and substitute them in the
method signatures used to check that impl. The existing `instantiate()`
machinery in `unify.rs` is the right hammer; the question is just where to
apply it.

**Files**: `src/typechecker/check_traits.rs` (impl body check entry),
`src/typechecker/unify.rs` (probably reuse existing `instantiate`).

**Test**: two impls of a multi-param trait with different extra-param types,
both should typecheck. Add a regression test to `tests.rs`.

This MUST land before Phase 2 starts.

---

### Phase 1 / 1.5 / 1c Outcomes (carry-forward for Phase 2)

- **Body-inference gap.** The where-clause `TraitApp` form binds fresh
  existentials at *constraint-solving* time, but those bindings don't
  propagate into expression inference inside the impl body. The practical
  effect: a delegating impl body like `to_json (to p)` needs a type
  ascription — `to_json ((to p) : __Rep_Person)` — to pin `to`'s polymorphic
  result. **Phase 2 must emit the ascription** when generating the
  delegating impl in `derive.rs`. `__Rep_Person` is known at derive-expansion
  time, so this is free.

- **AST dual representation.** `TraitBound` (old form) and `TraitApp` (new
  form) coexist as parallel parser outputs. Phase 2 will emit `TraitApp` for
  its generated delegating impls. **Decision deferred**: whether to migrate
  `TraitBound` → `TraitApp` wholesale (touches elaborator, LSP, formatter,
  doc generator) or accept permanent dual representation. Recommend
  deferring the migration past Phase 3; it's a clean-up, not a blocker.

- **New form is impl-only.** `where_apps` is currently only populated on
  `ImplDef`. Function signatures and handler bodies error if a `TraitApp` is
  used in their where clause. Phase 2/3 don't need it elsewhere; reconsider
  only if a downstream feature requires it.

- **No iteration loop in the solver.** `TraitApp` constraints are processed
  in source order with no fixed-point iteration. Each constraint may only
  depend on bindings produced by earlier constraints in the same clause.
  Phase 2's generated impls always have the shape `{Generic T r, ToJson r}`
  — strictly left-to-right resolvable — so this is fine. If a future codec
  ever needs reorderable constraints, add a worklist loop.

- **Substrate fully unblocked.** Risk table item "solver loops or
  non-deterministic ordering" is now retired. The fresh-var resolution is
  deterministic and bounded.

---

### Phase 2a / 2b Outcomes (carry-forward for Phases 2c/2d/2e and 3)

- **`Std.Generic` IS auto-imported via the prelude.** The initial
  concern was that Phase 1c tests defining `trait Generic a r` inline
  would clash with an imported `Generic`. In practice the typechecker
  treats the local trait def as a shadow (no duplicate-trait error
  raised), so the Phase 1c tests pass unchanged. `deriving (Generic)`
  works on user records with zero ceremony — no `import Std.Generic`
  needed.

- **Rep type naming is `Rep__<RecordName>`, NOT `__Rep_<RecordName>`.**
  Names starting with `_` lex as lowercase `Ident`, which would break
  user-written ascriptions like `(to p : Rep__Person)`. The leading
  uppercase `R` makes the name an `UpperIdent` (type/constructor).
  Update the Phase 3 routing layer to emit this name when generating
  delegating impls.

- **Functional-trait coherence now fires at call sites too.** Phase 1
  added coherence resolution at *impl-registration time* for the
  where-app form. Phase 2b extends it to `check_pending_constraints` in
  `check_decl.rs`: when an unresolved trait extra has the right shape
  (functional trait, concrete self, single matching impl), the extra
  is pinned to the impl's stored args. This is what makes
  `from (to value)` work without an ascription. The fallback is bounded
  (single-match only — otherwise normal "no impl" diagnostic fires)
  and contained to ~30 lines.

- **Synthesized decls are now spliced after their parent decl, not
  appended to the end of the program.** Earlier behavior appended all
  derived impls/typedefs at the end, which broke registration order
  for user-written where-app impls that referenced a derived `Generic`
  (the where-app's coherence lookup fires at registration time, so the
  derived impl must already exist). The new behavior preserves source
  ordering and is more intuitive in general — but it does change the
  decl order seen by downstream passes for *every* derive, not just
  Generic. No existing tests broke from this change.

- **Parameterized records, parameterized ADTs, and recursive types are
  all DONE in Phase 2d+2e (commits d1d7889, fbdaebd).** See the
  "Phase 2d+2e Outcomes" section below.

- **ADT Generic derive is done in Phase 2c.** Dispatched in
  `expand_derives` directly (inline `if bare == "Generic"`) rather than
  through `generate_derive`, because Generic needs to emit two decls
  (TypeDef + ImplDef) and `generate_derive` returns `Option<Decl>`.
  Mirrors the record path.

- **The `check()` test helper now surfaces derive diagnostics.**
  Previously the return value of `expand_derives` was discarded, which
  hid derive failures from test assertions. With the change, derive
  errors short-circuit the test before typechecking begins.

- **Phase 2e prerequisite.** The call-site coherence fallback added in
  2b uses `Type::Con(name, vec![])` when pinning the impl's stored
  args (`ImplInfo.trait_type_args: Vec<String>`). For parameterized
  Rep types like `Rep__Box a`, this representation is too narrow.
  Before Phase 2e lands, either widen `ImplInfo.trait_type_args` to
  carry full type info (preferred) or change the fallback to consult
  the impl's scheme directly. Pick during Phase 2e kickoff.

### Phase 3 Outcomes (shipped — carry-forward for Phase 4 and library authors)

- **Synthesizer emits TWO impls per routed derive**, not one. Required
  because the where-app `<Trait> r` validation fires at impl-registration
  time and needs a concrete `<Trait> Rep__T` impl to already exist before
  the routed impl for `T` registers. The two impls are:
  1. A **bridge** `impl <Trait> for Rep__T { method (Rep__T inner) =
     method inner }` — unconditionally unwraps the Rep newtype.
  2. A **delegating** `impl <Trait> for T where {Generic T r, <Trait> r}
     { method x = method (to x) }`.

- **Framing limitation (library-design concern, not compiler bug).** Because
  the bridge unconditionally unwraps, the library author has no hook to
  distinguish "I'm framing a record" from "I'm framing a sum variant
  payload" — both flow through the same `And`/`Labeled`/`Or` chain. The
  99f example produces unbraced JSON for this reason. **Fix is deferred
  to Phase 5+** (new top-level building block like `Record fields` or
  `Sum variants` that derives emit, giving library code a place to hook
  framing). Don't redesign the synthesizer until a real library author
  hits this and tells us what shape they actually need.

- **Single-method traits only.** Multi-method traits emit clear
  diagnostics. From-direction traits (FromJson, FromCsv, FromPgRow) are
  now supported as of Phase 3.1 — see below.

### Phase 3.1 Outcomes (shipped)

- **From-direction routing works** for traits whose method returns
  `a`, `Result a _`, or `Maybe a`. Other wrapper shapes (custom
  Result types, IO-wrapped, etc.) emit a clear diagnostic listing the
  supported forms.
- **Wrapper detection is purely AST-level** in `src/derive.rs` — no
  typechecker changes needed. The trait method's return `TypeExpr` is
  inspected directly via bare-name matching, so qualified `Result.Result`
  and bare `Result` both resolve.
- **Same two-impl bridge pattern** as to-direction (bridge for `Rep__T`
  + delegating for `T`). Body shape differs per wrapper: bare = direct
  wrap, `Result` = `Ok`/`Err` case-match, `Maybe` = `Just`/`Nothing`
  case-match. Built via a single `build_from_body` helper parameterized
  by a `wrap` callback (Rep wrap for bridge, `from` call for delegate).
- **No surprises.** Constraint resolution, body inference, dict
  composition all worked first try. The Phase 2-3 substrate fully covers
  from-direction without further trait-system work.
- **Roundtrip integration test** confirms `deriving (Generic, ToJson,
  FromJson)` on a single type produces matching serialization and
  deserialization that round-trip cleanly.

### Codec story is now complete

Library authors can ship single-method traits in either direction
(to or from) with building-block instances, and users derive them with
zero compiler involvement. The three motivating libraries (ToJson/
FromJson, ToCsv/FromCsv, ToPgRow/FromPgRow) are all now buildable as
pure library code.

---

## Phase 5: Framing Redesign

### Why

The current building-block set (`U1`, `Leaf`, `Labeled`, `And`, `Or`) leaves
library authors with no hook for distinguishing:

- A `Labeled` wrapping a record field name vs. a `Labeled` wrapping a sum
  constructor name. Both reach the same `impl ToJson for Labeled` instance.
- An `And` joining record fields vs. an `And` joining variant payload
  fields. Both reach the same `impl ToJson for And` instance.
- The top-level shape of a record (which usually wants outer framing like
  `{...}`) vs. the top-level shape of an ADT (which usually delegates to
  per-variant handling).

The bridge impl synthesized by `derive_routed` unconditionally unwraps
`Rep__T` and forwards the inner tree to the library's instances, so there
is no per-type hook either.

This bit Phase 4 (deferred): a routed `Show` cannot reproduce the hardcoded
`Person { name: "Alice", age: 30 }` framing because the type name lives at
the `Rep__T` outer layer, which the bridge discards. JSON libraries hit the
same problem: the natural output `{"name": "Alice", "age": 30}` requires
outer braces, and the library currently has nowhere to put them without
per-call-site wrapping.

We're doing the framing redesign now, before real library authors lock in
designs against the current shape and migration pain compounds.

### New Building Blocks

Three additions to `Std.Generic`:

```saga
type Variant a = Variant String a   -- sum constructor: name + payload
type Record name a = Record name a  -- top-level wrapper for records
type Adt name a = Adt name a        -- top-level wrapper for ADTs
```

(`name` is `String`; written as a separate parameter for clarity but it's
a runtime string, not a type-level value.)

### What Derives Emit

**Records** (`record Person { name: String, age: Int }`):
```
type Rep__Person = Rep__Person (Record "Person" (And (Labeled "name" (Leaf String))
                                                     (Labeled "age"  (Leaf Int))))
```

**ADTs** (`type Shape = Circle Float | Rect Float Float | Triangle`):
```
type Rep__Shape = Rep__Shape (Adt "Shape" (Or (Variant "Circle" (Leaf Float))
                                              (Or (Variant "Rect" (And (Leaf Float) (Leaf Float)))
                                                  (Variant "Triangle" U1))))
```

Notes:

- **`Labeled` is now record-fields-only.** ADT constructor names move to
  `Variant`. This removes the core ambiguity.
- **Variant payload fields with labels** (Saga allows
  `Circle { radius: Float }` style) use `Labeled` inside the variant's
  payload, e.g. `Variant "Circle" (Labeled "radius" (Leaf Float))`. Library
  authors who care about the distinction can dispatch on whether the
  Labeled is inside a `Record` or a `Variant`.
- **Single-field records** still skip `And`, producing
  `Record "Person" (Labeled "name" (Leaf String))`.
- **Zero-field records** produce `Record "Person" U1`.
- **Single-variant ADTs** still skip `Or`, producing `Adt "Wrapper" (Variant "Wrap" ...)`.
- **Recursive types** unchanged — recursive position remains `Leaf <Self>`.
- **Parameterized types** unchanged — type parameters propagate the same
  way they do today.

### Library Author Impact

The required building-block impl set grows from 5 to 8:

```saga
impl ToJson for U1
impl ToJson for Leaf a       where {a: ToJson}
impl ToJson for Labeled a    where {a: ToJson}    -- record fields
impl ToJson for Variant a    where {a: ToJson}    -- sum constructors  (NEW)
impl ToJson for And l r      where {l: ToJson, r: ToJson}
impl ToJson for Or l r       where {l: ToJson, r: ToJson}
impl ToJson for Record n a   where {a: ToJson}    -- record outer framing (NEW)
impl ToJson for Adt n a      where {a: ToJson}    -- ADT outer framing (NEW)
```

Libraries that don't care about a particular hook write a passthrough:
`impl ToJson for Adt n a where {a: ToJson} { to_json (Adt _ inner) = to_json inner }`.

A JSON library that wants proper bracing:
```saga
impl ToJson for Record n a where {a: ToJson} {
  to_json (Record _ inner) = "{" <> to_json inner <> "}"
}
impl ToJson for Variant a where {a: ToJson} {
  to_json (Variant name payload) = "{\"" <> name <> "\": " <> to_json payload <> "}"
}
```

### Compiler Impact

- `src/stdlib/Generic.saga`: add the three new types.
- `src/derive.rs`:
  - `derive_record_generic`: wrap the And-of-Labeled tree in `Record name`
    inside the `Rep__T` newtype.
  - `derive_adt_generic`: wrap the Or tree in `Adt name`; emit `Variant`
    instead of `Labeled` for the constructor-name layer.
  - Update `to` and `from` body generation to construct/destructure the
    new outer wrappers.
  - The `derive_routed` bridge impl pattern is unchanged in structure —
    still unwraps `Rep__T` and forwards. The library now sees `Record n a`
    or `Adt n a` as the immediate inner type, which is the hook it needs.
- No typechecker, elaborator, or codegen changes. Pure stdlib + derive
  work.

### Example & Test Migration

Every existing Generic-related example and test needs updating:

- `examples/99-generic-spike.saga` (Phase 0 hand-written) → update Rep
  shape and `to`/`from` to use new wrappers.
- `examples/99b-99e` (derived Generic, various shapes) → no change to user
  code; outputs may differ slightly if any printed/asserted the Rep shape.
- `examples/99f, 99g` (routed ToJson/FromJson) → the inline library code
  needs `Record`, `Variant`, `Adt` impls. User code unchanged.
- Tests asserting Rep shapes via pattern-match → update patterns.
- Round-trip tests → should pass unchanged.

### Risk

- **The 3-new-types decision is a one-way door.** Once libraries ship
  against this shape, changing it again is breaking. So get it right.
- **`Record name a` and `Adt name a` are *parameterized over the name*.**
  This is a runtime-value parameter, not a type parameter — it's a `String`
  field on the constructor. Make sure the AST representation is clean
  enough that library authors don't need to know how the name is encoded.
- **Migration churn is bounded but real.** ~6 examples + ~10-15 tests.
- **No deferral**: doing this before library authors build against the
  current shape is the point.

### Phase 5 Outcomes (to be filled in after implementation)

TBD.

---

## Phase 6: Multi-Method Routed Derives

### Why

Phase 3 shipped routed derives for **single-method traits only**. Multi-method
traits emit a clear diagnostic. The limit was a scoping decision, not a
fundamental one — both Haskell (GHC.Generics) and Rust (built-in derives)
handle multi-method derives without issue, by iterating over the trait's
methods and synthesizing one body per method.

Real-world cases where multi-method matters:

- **Pretty + compact variants**: `trait ToJson { to_json : a -> String;
  to_json_pretty : a -> String }`.
- **Bidirectional codecs in one trait**: `trait JsonCodec { encode : a ->
  String; decode : String -> Result a Error }`. Today Saga splits these
  (`ToJson` + `FromJson`); a unified trait halves the import surface.
- **Eq-style multi-method**: `==` + `/=` derive together in most languages.
- **Multiple input formats**: `trait FromConfig { from_json; from_toml;
  from_env }`.

The two-trait workaround works but is friction. Multi-method support
removes it.

### What Changes

Pure `src/derive.rs` work. No typechecker, elaborator, codegen, or stdlib
changes. The synthesizer iterates over the trait's methods instead of
stopping at one. For each method:

1. Run direction detection (`classify_from_return` plus the existing
   to-direction check). Each method is independently to- or from-direction;
   a trait can mix both (e.g. the `JsonCodec` example above).
2. Run the appropriate body builder (`build_to_body` or `build_from_body`).

Both the bridge impl and the delegating impl carry one method definition
per trait method, mirroring the trait's full signature.

Example: for `trait JsonCodec { encode : a -> String; decode : String ->
Result a Error }` and `record Person { ... } deriving (JsonCodec)`:

```saga
# Bridge
impl JsonCodec for Rep__Person {
  encode (Rep__Person inner) = encode inner
  decode s = case decode s {
    Ok inner -> Ok (Rep__Person inner)
    Err e -> Err e
  }
}

# Delegating
impl JsonCodec for Person where {Generic Person r, JsonCodec r} {
  encode p = encode (to p)
  decode s = case decode s {
    Ok rep -> Ok (from rep)
    Err e -> Err e
  }
}
```

### Constraints To Preserve

- Each method must individually pass direction detection. If any method has
  an unsupported shape (return type isn't `a`/`Result a _`/`Maybe a`, or
  user type appears on neither side, or appears on both sides), the whole
  derive errors with a clear diagnostic naming the offending method.
- The trait's method signatures are the source of truth for parameter
  names, types, and return types. The synthesizer reads them from the
  TraitDef.

### Scope of Change

- `derive_routed`: change the "single method only" early-return into an
  iteration over methods.
- `synth_to_direction` / `synth_from_direction`: probably merge into a
  single `synth_routed` that iterates and dispatches per-method, OR keep
  separate and call both in the iteration loop (preferred — less merge
  conflict surface with Phase 3.1's work).
- `build_from_body`: already parameterized by a `wrap` callback. Reuse
  as-is per method.
- Method-name and signature extraction from the TraitDef: should already
  be available — Phase 3 already reads the trait's single method; the
  generalization is "read all methods" instead of "read the first."

Estimate: half a day.

### Tests

- A two-method to-direction trait (`trait ShowBoth { show; debug }`),
  derived on a record. Both methods produce sensible output.
- A two-method bidirectional codec (`trait JsonCodec { encode; decode }`),
  derived on a record. Round-trip works.
- A two-method from-direction trait, derived on an ADT.
- A trait with a mixed method (`fun roundtrip : a -> a` — user type on
  both sides) → diagnostic, no synthesis. Confirm the diagnostic names
  the specific method.
- All existing single-method tests still pass.

### Phase 6 Outcomes (shipped)

- **Per-method classification.** `classify_method_direction` runs over
  every `TraitMethod` in the trait's AST (read from `RoutedTraitInfo` —
  the existing parser-level shape; no typechecker state needed).
  Direction detection is identical to Phase 3/3.1 but reports a
  method-specific reason on failure.
- **`a -> a` is now rejected.** Phase 3's to-direction path accepted
  methods where `self` appeared in both param and return (it fell into
  the to-direction branch). Phase 6 splits direction detection into a
  4-case match (true/false × true/false) and treats both-sides as an
  error. No existing test exercised this, so no behavioral fallout in
  the suite. Could in principle break a user trait that was abusing
  the lenience; none of the in-tree libraries do.
- **`synth_method_pair`** is the new per-method helper. It dispatches
  on `MethodDirection` and returns `(bridge_method, delegating_method)`
  for splicing into the two impls. Multi-method synthesis is just a
  `for` loop over the trait's methods.
- **Mixed-direction codec works first try.** The bridge + delegating
  pattern composes cleanly when one method goes through `to` and
  another threads back through `from`. No issues with constraint
  resolution or dict composition.
- **Diagnostic test added** verifies the multi-method derive fails
  cleanly when one method has `a -> a` shape, naming the offending
  method (`roundtrip`).
- **All Phase 3/3.1 tests pass unchanged** except for the now-obsolete
  `phase3_routed_derive_multi_method_diagnostic`, which was removed in
  favor of the Phase 6 tests.
- **Total cost:** ~200 lines net in `src/derive.rs`, no changes outside
  it. Tests added: 4. Examples added: `99h-generic-derived-codec.saga`.

What's left for real-world polish (out of scope for Phase 6):
- Constraint-failure errors in synthesized impls still mention
  `Labeled`/`And`/etc. instead of the user-facing field. Phase 3c
  carry-over.
- No attribute-based opt-in/opt-out at the trait level — every
  multi-method trait that survives classification gets routed.

---

## Phase 6.5: Cross-Module Routed Derives (PREREQUISITE for Phase 7)

### Why

Phases 3, 3.1, and 6 shipped routed derives that work, but **only when the
trait, its building-block impls, the wrapper, and the user type all live in
the same module**. Every Phase 3/3.1/6 example file (`99f`, `99g`, `99h`)
defines its codec library inline alongside the user type.

This was discovered during Phase 7 scoping: `expand_derives` runs pre-
typecheck on the current module's parsed AST. Imports aren't resolved yet,
so a user module that does:

```saga
import json_lib (ToJson)
record Person { name: String, age: Int } deriving (ToJson)
```

cannot find the `ToJson` `TraitDef` at derive-expansion time. The
synthesizer either fails or fabricates a wrong impl.

The `Generic` case appears to work cross-module only because `Std.Generic`
is auto-imported via prelude and the prelude is loaded into the parser's
view before user-module expansion. Non-prelude routed traits don't get
this treatment.

This is the blocker between "feature mechanism validated in single-file
demos" and "library authors can ship traits and users derive them across
module boundaries" — which is the actual goal stated in the plan's opening
paragraph.

### Pre-implementation scoping (mandatory)

Before any code lands:

1. **Reproduce the bug.** Write a failing test with a library module and
   a user module in separate files (or separate inline modules in one
   test source). Confirm it fails today with a specific diagnostic.
   This test is the Phase 6.5 acceptance criterion and stays as a
   regression check.
2. **Understand the prelude path.** `Std.Generic.Generic` resolves at
   derive-expansion today. Figure out how. If existing prelude-import
   machinery is generalizable, Phase 6.5 is "extend that machinery to
   user imports" (small). If the prelude path is special-cased and
   doesn't generalize, Phase 6.5 is "build pre-typecheck import
   resolution for derives" (larger).

The answer determines the implementation shape and the estimate.

### Implementation outline

Two viable approaches; pick based on the scoping outcome:

**(a) Generalize the prelude resolution path.** If imports for non-prelude
modules can be resolved into the same parsed-AST form prelude uses, just
do that resolution before `expand_derives` runs. Thread an
`&ImportedDecls` (or equivalent) into `expand_derives` and `derive_routed`.
Trait lookup, wrapper lookup, and building-block lookups all consult this
bundle.

**(b) Pre-typecheck import pass.** If the typechecker's import resolution
is too entangled with type registration to extract, build a lighter
pre-typecheck pass that produces summaries (TraitDef, TypeDef, RecordDef
shapes) without doing full type registration. `expand_derives` consumes
these summaries.

Either way, the change is:
- `expand_derives` signature grows an `&ImportedDecls` parameter (or
  whatever the resolved-imports bundle ends up being called).
- `derive_routed`'s trait lookup falls through to imported decls if not
  found locally.
- Bootstrap care: when expanding derives for the prelude itself or
  `Std.Generic`, the imported bundle is empty (or contains only what the
  prelude has already loaded — depending on staging).

### Tests

- **Cross-module routed to-direction derive**: library defines
  `trait ToJson` + building-block impls; user module imports and derives.
  Compiles and runs.
- **Cross-module routed from-direction derive**: same with `FromJson`.
- **Cross-module wrapper type**: user derives against a trait whose method
  returns a custom wrapper imported from another module. (This subsumes
  the Phase 7 case once 7 lands.)
- **Transitive import**: library A defines the trait, library B re-exports
  it, user imports from B. Verify the resolution chains through.
- **Existing single-file demos** (99 through 99h) continue working
  unchanged.

### Risks

- **Compilation-order subtlety.** If the user imports a module that hasn't
  been parsed yet, the resolved-imports bundle might be empty at expansion
  time. The compiler probably already orders module parsing such that
  imports are parsed first; verify before assuming.
- **Bootstrap loops.** `Std.Generic` defines `Generic`; if some other
  stdlib module derives `Generic`, we have a chicken-and-egg situation.
  Mitigated because the standard library compiles in a known order and
  `Generic`'s trait def is in `Std.Generic` itself.
- **Diagnostic quality on missing imports.** A user who writes
  `deriving (ToJson)` without importing `ToJson` should get a clear error
  ("trait `ToJson` not in scope; did you forget to import it?") rather
  than a synthesizer failure. Budget half a day for this.

### Estimated scope

~1-2 days if approach (a) works, ~3-5 days if approach (b) is needed.
Scoping pass determines which.

### Phase 6.5 Outcomes (to be filled in after implementation)

TBD.

---

## Phase 7: Structural From-Direction Wrappers

### Why

Phase 3.1 supports three from-direction return shapes by literal name-match:
`a`, `Result a _`, `Maybe a`. Anything else — `IO (Result a _)`,
`DbResult a` (library-defined three-state result), `Validated e a` (error-
accumulating validation), `Wrapped a = Yep (List a) | Nope` — emits a
diagnostic and refuses the derive.

The framing redesign (Phase 5) gave us a cleaner answer than the
trait-level annotation or `Unwrap` typeclass approaches considered
earlier: **the wrapper type's structural Rep is exactly the information
needed to thread `from` through it.** A library author who wants a custom
wrapper just derives `Generic` on their wrapper type, and the synthesizer
inspects its variants (or fields, for product wrappers) to find positions
of the user type `a` and apply `from` there.

This subsumes the existing `Result`/`Maybe` cases. They become specific
instances of "ADT whose Generic representation has one variant containing
`a`," not hardcoded recognized names.

### Core idea

For a from-direction trait method `fun decode : Input -> W a` where `W` is
some wrapper:

1. Look up `W`'s `TypeDef` in the program (or imported modules) at
   derive-expansion time. This is parser-level state — same access pattern
   as the existing derive code.
2. Walk `W`'s variants (or fields, for a record wrapper). Identify
   positions where the trait's `a` parameter appears.
3. Generate a case-match (for sum wrappers) or constructor pattern (for
   record wrappers) that applies the appropriate callback at each
   `a`-position and passes other positions through unchanged.

The callback is the same one Phase 3.1 already plumbs through
`build_from_body`:
- Bridge impl: wrap with `Rep__T (...)`.
- Delegating impl: apply `from`.

### Algorithm

Given trait method return type `W <type_args>` where `a` is the trait's
self type variable:

1. Resolve `W` to its `TypeDef`. If `W` is opaque (no in-tree TypeDef,
   imported abstractly, or a primitive), emit a diagnostic:
   `"cannot derive ... — wrapper type "W" is opaque (no Generic
   representation available)"`. Note: not "must derive Generic" — the
   synthesizer doesn't actually need a Generic impl to exist; it just
   needs the TypeDef to be in scope and inspectable.

2. **For sum wrappers** (`Decl::TypeDef` with variants):
   - For each variant, find `a`-positions in its fields. An `a`-position
     is a field whose type expression equals (after substitution against
     `W`'s declared type params) the trait's self variable.
   - Generate one case arm per variant. Bind each field to a fresh name.
     For `a`-position fields, apply the callback (`wrap` or `from`).
     For other fields, pass through unchanged.
   - Variants with zero `a`-positions become passthrough arms.
   - Variants with ≥1 `a`-positions get the callback applied at each
     `a`-position field.

3. **For product wrappers** (`Decl::RecordDef`):
   - Same approach but with one constructor pattern instead of multiple
     arms. Find `a`-positions in fields, apply callback there.

4. **For bare `a`** (the user type appears directly as the return type,
   not wrapped in anything):
   - Existing handling unchanged. Apply callback directly.

### Edge cases

| Case | Behavior |
|------|----------|
| Multiple variants contain `a` (`Either a a`) | Apply callback at every `a`-position in every variant. Natural extension; no special-case. |
| Single variant with multiple `a`-positions (`type Multi a = Both a a`) | Apply callback at each. Same idea. |
| `a` appears nested (`Wrapped a = Yep (List a) \| Nope`) | **Reject in v1.** Emit diagnostic: `"cannot derive ... — wrapper "Wrapped" contains the user type at a non-leaf position; only direct \`a\` positions are supported"`. Recursing through `List`'s Generic to thread `from` is a possible future extension but introduces termination questions for self-referential containers. |
| Recursive wrapper (`type Cofree a = Cofree a (Cofree a)`) | Falls under "a appears nested." Reject. |
| No `a` anywhere in the return | Phase 3.1's `classify_method_direction` already rejects this — the method isn't from-direction at all. |
| Wrapper has phantom params (`type W a b = W a` where `b` is unused) | Fine. Only `a`-positions in actual field shapes matter. |
| Wrapper type appears in trait's type args (`from : Input -> W a Int`) | Resolve `W`'s declared type params against the call-site type args. `a` is whichever position lines up with the trait's self. |
| Wrapper is a primitive (`from : Input -> Int`) | Falls under "no `a` anywhere." Rejected by classification. |
| Wrapper is itself `a` (the trait's self variable) | This is the bare case; handle as today. |
| Multi-param wrappers (`type DbResult a e = ...`) | Resolve which param position is the trait's self. Identify by name-match between the trait method's return-type arg and the trait's self variable. |

### Implementation outline

- Replace the hardcoded shape recognition in `classify_from_return`
  (`src/derive.rs`) with a structural inspection step:
  - Old: literal `Result` / `Maybe` / bare matching.
  - New: produce a `FromShape` value carrying:
    - The wrapper's `TypeDef` (or `None` for bare).
    - A list of `(variant_or_field_path, a_positions)` describing where
      to apply the callback.
- `build_from_body` already takes a `wrap` callback. Generalize it to
  consume a `FromShape` and emit the appropriate case-match or
  constructor pattern, applying the callback at each marked `a`-position.
- Diagnostics: when the wrapper is unsupported (opaque or has nested
  `a`-positions), the error message names the wrapper type and the
  specific reason. Better than today's catchall "unsupported wrapper."
- The bridge and delegating impl synthesizers (`synth_method_pair`) are
  unchanged in structure — they just pass different callbacks to the new
  body builder.

Estimated scope: ~150-250 lines of `src/derive.rs` work plus ~50 lines of
tests. No typechecker, elaborator, codegen, or stdlib changes.

### Migration / backwards compatibility

The existing `Result` / `Maybe` / bare cases must produce identical
output after the generalization. Verify via:
- All Phase 3.1 tests pass unchanged.
- Examples 99g (FromJson with Result) and 99h (JsonCodec with mixed
  direction, including Result decode) produce byte-identical output.

If `Result` and `Maybe` get `deriving (Generic)` in the stdlib (they
likely should anyway, but aren't currently part of `Std.Generic`), the
generalization can drop the bare/Result/Maybe special-case entirely and
go through the structural path for everything. **Decision deferred to
Phase 7 implementation**: cleaner to drop the special-cases or keep them
as a fast path?

### Tests

- Custom three-variant wrapper (`DbResult a = DbOk a | DbErr DbError |
  DbNoRows`) — from-direction derive works, round-trips.
- Validation-style wrapper (`Validated e a = Valid a | Invalid (List
  e)`) — from-direction derive works.
- Record wrapper (`Boxed a = { value: a, meta: String }`) — from-direction
  derive works.
- Wrapper with phantom param — works, phantom ignored.
- Multi-`a` wrapper (`Either a a`) — both arms get callback.
- Nested `a` (`Wrapped a = Yep (List a) | Nope`) — diagnostic, names the
  variant and reason.
- Opaque wrapper (e.g. an imported type without TypeDef in scope) —
  diagnostic, suggests the user export the TypeDef or use a supported
  wrapper.
- All existing Result/Maybe/bare tests pass unchanged.

### Open decisions

- **Drop hardcoded Result/Maybe special-cases?** If `Result` and `Maybe`
  derive Generic in the stdlib, yes. Cleaner. If they don't, keeping the
  special-case as a fast path is acceptable.
- **Should the diagnostic for "nested `a`" suggest a workaround?** E.g.
  "consider wrapping the inner type in `Leaf` manually." Probably not —
  users hitting this need to redesign their wrapper, not patch around it.
- **Mutual-recursion case** (`A` references `B`, `B` references `A`,
  one of them is the wrapper): can rely on the same self-reference
  handling Phase 2d uses (`Leaf` at recursive positions, runtime
  dispatch). Verify in tests.

### When to invest

Lowest-priority polish item until a real library author files an issue.
Triggers worth doing this for, in descending order:
1. Postgres library wants `DbResult a` with three variants.
2. Validation library wants error accumulation (`Validated e a`).
3. Async/effect library wants `IO (Result a _)` or similar
   effect-wrapped returns. Note: `IO` is opaque on BEAM, so this case
   would need the "nested `a`" extension. Defer further until needed.
4. Anyone files an issue saying their trait can't derive.

### Phase 7 Outcomes (to be filled in after implementation)

TBD.

- **Piece 4 (error rewriting) deferred.** Constraint failures inside
  synthesized impls still produce default-shaped errors mentioning
  `Labeled`/`And`/etc. Low-cost win whenever someone wants to do it; a
  marker on synthetic `ImplDef`s (or a NodeId side-table) is the suggested
  approach.

- **Alternative synthesizer shape on file.** A single-impl version using
  `case to x { Rep__T inner -> method inner }` works (the implementer had
  it briefly). Drops the bridge and the where-app at the cost of
  later-fired errors. ~30 line diff to switch. Don't switch unless the
  bridge approach is causing real pain.

---

### Phase 2d+2e Outcomes (carry-forward for Phase 3)

- **`ImplInfo.trait_type_args` is now `Vec<Type>`** (was `Vec<String>`).
  Plus a new `target_type_param_ids: Vec<u32>`. The call-site coherence
  fallback uses these to substitute the impl's stored type vars with
  the call site's concrete args, materializing `Rep__Box Int` from a
  `Box Int` call site.

- **The parser now accepts parenthesized type applications in
  where-app args** (commit fbdaebd). `where {Generic (Box a) r, ToJson
  r}` parses cleanly. Phase 3's routing layer can emit this form
  directly.

- **Constraint solver now sorts within each batch.** Concrete-self
  constraints process before Var-self ones in
  `check_pending_constraints`. Without this, the chained
  `Generic T r → ToJson r` resolution could error on the second
  constraint before the first had pinned `r`. Pure ordering, no
  semantic change. If Phase 3 needs more complex constraint graphs
  (unlikely for routed derives), this is the place to revisit.

- **Call-site coherence fallback is now load-bearing, not optional.**
  It's the resolution path for functional traits (Generic) when the
  self type is concrete-headed but the impl has type parameters.
  Phase 3 should treat it as a first-class resolution mechanism, not
  a recovery fallback.

- **Body-inference gap workaround**: for routed `ToJson` impls on
  parameterized types, **drop the type ascription** on `to`. The
  call-site coherence fallback pins the Generic's second arg from the
  impl's outer type param because the self-type `T a` is
  concrete-headed. Phase 3's synthesizer should emit
  `to_json m = to_json (to m)` without an ascription. If we ever need
  ascriptions referring to impl-level params, the fix is documented:
  seed `convert_user_type_expr`'s params vec with the impl's
  `(name, tvar_id)` pairs when entering an impl-method body.

- **Recursion really was free.** Removing the `type_expr_refs` bail-out
  in `derive_record_generic` and `derive_adt_generic` was the entire
  change. `dict_for_type` handles the cycle because the recursive
  position bottoms out at a zero-arg `Type::Con` whose dict is a
  top-level name reference.

- **Two viable shapes for Phase 3's synthesized delegating impl**
  (decision deferred to Phase 3 kickoff):
  - (a) **No where-app**: `impl ToJson for T { to_json m = to_json (to
    m) }`. Simplest. Relies entirely on call-site coherence fallback.
  - (b) **Explicit where-app**: `impl ToJson for T where {Generic T r,
    ToJson r} { to_json m = to_json (to m) }`. More explicit about
    the dependency on Generic; better error messages when the trait
    isn't functional. Now parseable thanks to fbdaebd.

  Recommended: (b). Cost is one extra where-app per impl; benefit is
  clearer errors when something goes wrong.

---

- **Phase 2d (recursion) is essentially free.** Feasibility spike
  confirmed (see `/tmp/recursion-spike.saga` notes): hand-written
  recursive `Generic` + delegating `ToJson` works end-to-end with zero
  compiler changes. Both suspected blockers were false alarms:
  - The call-site coherence fallback never fires for monomorphic
    recursive types — the second arg is pinned by the delegating
    impl's ascription, so coherence doesn't have to guess.
  - `dict_for_type` doesn't loop because the recursive position
    bottoms out at a zero-arg `Type::Con`, whose dict is a top-level
    name reference, not an inlined expansion. The runtime cycle
    (dict's `to_json` body calling itself on subterms) is normal
    function recursion that BEAM handles natively.

  Work is ~2-4 hours: delete the `type_expr_refs`-based bail-out in
  `derive_record_generic` and `derive_adt_generic`. The Rep-leaf
  generation already produces the right shape for recursive fields.
  **Bundle into Phase 2e** rather than running as a separate phase.

---

### Phase 2: `Generic` Derive in the Compiler

**Goal**: Implement `deriving (Generic)` end-to-end for records and ADTs.
**Budget: ~1.5 weeks.**

#### 2a. Building blocks in the prelude

Add the `Rep` building blocks and the `Generic` trait to the standard
library. These live in a new module, e.g. `Std.Generic`:

```saga
module Std.Generic

type U1 = U1
type Leaf a = Leaf a
type Labeled a = Labeled String a
type And l r = And l r
type Or l r = Or_Left l | Or_Right r

trait Generic a r {
  fun to : a -> r
  fun from : r -> a
}
```

The trait is opted into the "first param determines the rest" coherence rule
from Phase 1b.

**Files**: new `src/stdlib/Generic.saga`, registration in
`src/stdlib/prelude.saga` if auto-imported.

**Decision needed**: is `Generic` auto-imported via the prelude, or does the
user explicitly `import Std.Generic`? Recommendation: auto-import, so
`deriving (Generic)` works without ceremony. Same for the building blocks.

#### 2b. `Generic` derive for records

Extend `src/derive.rs::generate_record_derive` to handle `Generic`. For a
record:

```saga
record Person { name: String, age: Int }
```

Generate:

- A synthetic type definition: `type __Rep_Person = And (Labeled (Leaf
  String)) (Labeled (Leaf Int))`. The name is internal — users shouldn't need
  to reference it directly.
- A synthetic `impl Generic Person __Rep_Person` with `to` and `from`
  method bodies.

The `to` body builds the nested `And` tree. The `from` body pattern-matches it
and reconstructs the record.

**Key choice**: emit the `Rep` type as a synthetic `Decl::TypeDef`. This is
new territory for `derive.rs` — today it only emits `Decl::ImplDef`. The
expansion pass needs to handle multiple decl kinds per derive.

**Files**: `src/derive.rs`, AST helpers in `src/ast.rs` if needed.

**Test**: examples covering single-field, multi-field, zero-field records.
Verify `to` and `from` round-trip via a unit test.

#### 2c. `Generic` derive for ADTs

Same idea, for `Decl::TypeDef`. For:

```saga
type Shape = Circle Float | Rect Float Float | Triangle
```

Generate:

```saga
type __Rep_Shape =
  Or (Labeled (Leaf Float))
     (Or (Labeled (And (Leaf Float) (Leaf Float)))
         (Labeled U1))
```

with a `to` that nests `Or_Left`/`Or_Right` per variant, and a `from` that
pattern-matches the encoding back.

**Tricky cases to test explicitly**:
- Zero-field constructors → `U1`.
- Single-field constructors → `Leaf t` (not `And`).
- Multi-field constructors → nested `And`.
- 1 variant → just the inner type, no `Or`.
- 2 variants → one `Or`.
- 3+ variants → nested right-leaning `Or` chain.

**Files**: `src/derive.rs`.

**Test**: round-trip property for each shape, exercised via
`cargo test --test codegen_integration`.

#### 2d. Recursive types

For:

```saga
type Tree a = Leaf | Node (Tree a) a (Tree a)
```

The recursive occurrence of `Tree a` must be treated as a `Leaf (Tree a)`,
**not** unfolded into the `Rep`. Otherwise `Rep` generation loops.

Detection: when generating `Rep` for a type, any field whose type references
the type being derived (directly or through a parameterized self-reference)
becomes a `Leaf t` where `t` is the original field type. The recursion lives
inside the dictionary at runtime, not in the `Rep` type.

**Files**: `src/derive.rs` (a self-reference detector in the type-shape
analysis).

**Test**: derive `Generic` for a recursive ADT, confirm `Rep` is finite and
`to`/`from` round-trip.

#### 2e. Type parameters on the user type

For `record Box a { value: a }`, the generated `Rep` is parameterized too:
`type __Rep_Box a = Labeled (Leaf a)`. The `Generic` impl picks up a `where`
clause: `impl Generic (Box a) (__Rep_Box a)`.

**Files**: `src/derive.rs`.

**Test**: derive `Generic` for parameterized records and ADTs.

**Phase 2 deliverable**: `deriving (Generic)` works for all record and ADT
shapes including recursion and type parameters. The Phase 0 spike can be
rewritten with `deriving (Generic)` instead of hand-written impls, and
produce identical Core Erlang output.

---

### Phase 3: Routing Layer — Library-Defined Derives

**Goal**: When the user writes `deriving (ToJson)` and `Generic` is also
derived, synthesize an impl that delegates through `Generic`'s `to`. **Budget:
~1 week.**

#### 3a. Routing strategy

Convention-based, no new syntax. When `expand_derives` encounters a derive
name that isn't in the hardcoded set (`Show`/`Debug`/`Eq`/`Ord`/`Enum`/
`Generic`), it generates a delegating impl:

```saga
impl ToJson for Person {
  to_json p = to_json (to p)
}
```

Plus a where clause referencing `Generic Person __Rep_Person` and
`ToJson __Rep_Person`. The compiler validates these constraints during normal
trait-checking, which means the library must have provided `ToJson` instances
for the `Rep` building blocks. If it hasn't, the user gets a normal "no
instance for `ToJson (And ...)`" error.

**Open question**: should the routing layer require the user to explicitly
also derive `Generic`, or imply it? Recommendation: imply it. If
`deriving (ToJson)` is requested but `Generic` is not, expand the deriving
list to include `Generic` automatically. Same precedent as the existing
"Ord requires Eq" auto-inclusion in `src/derive.rs:28-36`.

**Open question**: trait method discovery. A delegating impl for `ToJson`
needs to know the method name(s) of the trait so it can generate
`to_json p = to_json (to p)`. Options:
- (a) Require the trait to have exactly one method, derive its name from the
  trait declaration. Simplest. Works for `ToJson`/`FromJson`/`ToCsv`/etc.
- (b) Support multi-method traits by generating one delegating body per
  method, mirroring whatever the building-block impls do.
  
Recommendation: ship (a) first. (b) is mechanical once (a) works.

**Files**: `src/derive.rs` (new generic routing function),
`src/typechecker/check_traits.rs` (lookup trait methods by name).

#### 3b. Direction issue: `FromX` traits

`ToJson` is easy because data flows `user_type -> Rep -> JSON`. `FromJson`
flows `JSON -> Rep -> user_type` — the delegate is
`from_json j = from <$> from_json j` (roughly). This requires the routing
layer to know which direction each method goes.

**Approach**: don't try to infer direction. Generate the body as:

```saga
from_json j = case from_json j {
  Ok rep -> Ok (from rep)
  Err e  -> Err e
}
```

— i.e. always thread the `Generic` `from` after the building-block call. The
library-defined trait methods are responsible for handling errors. For traits
where this shape doesn't fit, the user falls back to a hand-written impl.

This is the same compromise serde, aeson, and circe all make. A small
percentage of types need hand-written codecs. Accepted.

**Alternative**: let the trait declaration explicitly mark methods as
"input direction" or "output direction" via an annotation. Defer this until
we see if the simple version is insufficient.

**Files**: `src/derive.rs`.

**Test**: write a small `json_lib` library with `ToJson` and `FromJson`
traits and instances for the `Rep` building blocks. Derive both for a record,
round-trip through JSON.

#### 3c. Error messages

The big risk: when `deriving (ToJson)` fails because (a) the library isn't
imported, (b) a nested type isn't `Generic`, or (c) a field type lacks a
`ToJson` instance, the error chain runs through synthesized impls and `Rep`
machinery. Default error message will mention `Labeled` and `And` — useless
to users.

**Mitigation**: in `check_pending_constraints`, detect when a failed
constraint's NodeId traces back to a Generic-routed deriving, and rewrite the
error to point at the original `deriving (ToJson)` clause with a hint:

> No `ToJson` instance for field `tags : List Tag` in `record Foo`. Make sure
> `Tag` has `deriving (ToJson)`.

This is a quality-of-life feature, not a correctness one. Budget half a day.

**Files**: `src/typechecker/check_decl.rs` (constraint diagnostics),
`src/cli/diagnostics.rs`.

**Phase 3 deliverable**: a third-party library can ship a `ToJson`/`FromJson`
pair, users add `deriving (ToJson, FromJson)` to their types, it works
end-to-end with reasonable error messages. The same library code works for
every user type without any compiler involvement.

---

### Phase 4: Migrate Existing Derives (Optional)

**Goal**: Reimplement `Show`/`Debug`/`Eq`/`Ord` as library-defined derives on
top of `Generic`, removing the hardcoded versions from `derive.rs`. **Budget:
~3 days. Optional.**

Pros:
- Single derive mechanism, less code in `derive.rs`.
- Validates that the Generic infrastructure handles everything the hardcoded
  versions handle.
- Users can override standard library codec behavior by providing their own
  `Show` instances for the building blocks.

Cons:
- Hardcoded versions today produce slightly nicer code than the Generic-routed
  version would (e.g. inlined string concat instead of dict calls).
- Risk of regressing error messages on common derives.

Recommendation: do the migration for `Show` and `Debug` as a validation
exercise. Leave `Eq` and `Ord` hardcoded since they dispatch through BIFs and
can't route through Generic without losing the BIF optimization. `Enum` stays
hardcoded — it's nullary-only and trivial.

**Files**: `src/derive.rs`, new stdlib instances in
`src/stdlib/Generic.saga`.

**Phase 4 deliverable**: `Show` and `Debug` derives go through `Generic`,
existing tests still pass. If performance regresses materially, revert. The
infrastructure investment is the real win regardless.

---

## Risks and Mitigations

| Risk | Likelihood | Mitigation |
|------|------------|------------|
| `dict_for_type` doesn't handle `Rep` shape | Low | Phase 0 spike catches this in 1-2 days |
| Solver loops on free vars in impl where clauses | Medium | Single-pass, source-order processing; cap iterations |
| Confusing error messages on derive failures | High | Phase 3c diagnostics rewriting; budget time explicitly |
| Recursive types blow up Rep generation | Medium | Phase 2d self-reference detection; covered by test |
| Performance regression on Generic-routed derives | Medium | Phase 4 is optional; bail out if Show/Debug regress |
| Compile-time cost of Rep types proliferating | Low | Rep types are emitted once per derived type; not a hot path |

## Files Touched (Summary)

Primary:
- `src/derive.rs` — Generic derive, routing layer.
- `src/typechecker/check_traits.rs` — overlap detection, coherence rules.
- `src/typechecker/check_decl.rs` — free vars in impl where clauses,
  constraint diagnostics.
- `src/stdlib/Generic.saga` — new file: building blocks and Generic trait.

Secondary:
- `src/ast.rs` — possibly small additions for trait flags.
- `src/cli/diagnostics.rs` — error rewriting for Generic-routed failures.
- `src/stdlib/prelude.saga` — auto-import Generic if we choose that path.
- `examples/` — Phase 0 spike, Phase 3 demonstration.
- `src/typechecker/tests.rs`, `tests/codegen_integration.rs` — coverage at each phase.

## Total Estimate

| Phase | Budget | Cumulative |
|-------|--------|------------|
| 0: Spike | 1-2 days | 2 days |
| 1: Trait system tightening | 1 week | 1.5 weeks |
| 2: Generic derive | 1.5 weeks | 3 weeks |
| 3: Routing layer | 1 week | 4 weeks |
| 4: Migrate existing derives (optional) | 3 days | 4.5 weeks |

Roughly **3-5 weeks of focused work**, with a usable `deriving (Generic) +
deriving (ToJson)` story by the end of Phase 3 (~4 weeks). Phase 4 is icing.

## Decision Log

Pre-decided based on the discussion that led to this plan:

- **Multi-param `trait Generic a r`**, not associated types. Avoids a major
  type-system feature.
- **Coherence rule pinning the second parameter** in lieu of associated-type
  guarantees. ~50 lines in impl registration.
- **No overlapping instances.** Routing layer synthesizes concrete impls per
  type, so blanket-instance semantics are unnecessary.
- **Field/constructor labels as runtime values** in `Labeled`, not type-level
  strings. Negligible cost, no new type-level machinery.
- **Convention-based routing** (`deriving (X)` where `X` isn't hardcoded
  routes through Generic), not explicit `derive X via Generic` syntax. Can
  add explicit syntax later if needed.
- **Single-method traits only** for routed derives in Phase 3a.
  Multi-method support is a small addition once the base works.

Open for later decision:

- Whether `Std.Generic` is auto-imported via prelude.
- Whether `deriving (ToJson)` implies `deriving (Generic)` automatically.
- Whether to add an explicit "first param determines the rest" trait
  attribute, or hardcode the set initially.
