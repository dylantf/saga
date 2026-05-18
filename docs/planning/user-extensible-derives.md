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

### Phase 0: Spike — Hand-Written Validation

**Goal**: Confirm `dict_for_type` actually composes the way the dict-passing
doc claims when fed `Rep`-shaped types. **Budget: 1-2 days.**

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

#### 1a. Overlap detection in `register_impl`

Today, `TraitState.impls: HashMap<(trait_name, trait_type_args, target_type),
ImplInfo>` silently overwrites duplicates. Add a check at insertion time and
emit a diagnostic when two impls collide.

**Files**: `src/typechecker/check_traits.rs` (`register_impl`),
`src/typechecker/check_decl.rs` (callsite).

**Test**: add tests in `src/typechecker/tests.rs` covering:
- Two `impl Show for Int` blocks → error.
- `impl Show for List a` and `impl Show for List Int` → error (still
  overlapping, even with one being more specific — we are not implementing
  specificity rules).
- Conflicting derive + hand-written impl → error.

#### 1b. Coherence rule for functionally-determined trait parameters

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

Today, `check_pending_constraints` errors on type variables in constraints
that don't appear in the impl's `type_params`. We need to permit:

```saga
impl ToJson for Person where {Generic Person r, ToJson r}
```

where `r` is fresh and exists only in the constraint chain.

**Approach**: when constraint-solving encounters a free var in an impl's
where clause, treat it as an existential to be solved by chaining: solve the
`Generic Person r` constraint first (which pins `r` via the coherence rule
from 1b), then propagate the binding to the `ToJson r` constraint.

This is the most subtle piece in Phase 1. Risk: solver loops or
non-deterministic ordering. Mitigation: process where-clause constraints in
source order, single pass per impl.

**Files**: `src/typechecker/check_decl.rs` (`check_pending_constraints`),
`src/typechecker/check_traits.rs`.

**Test**: synthesize a hand-written impl with free vars in the where clause,
verify it typechecks and elaborates correctly.

**Phase 1 deliverable**: a trait system that catches duplicate impls, enforces
single-instance-per-key for marked traits, and permits free vars in
impl-level where clauses. All existing examples and tests still pass.

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
