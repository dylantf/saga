# Type-Level Atoms

## Goal

Add type-level atoms to Saga: interned, compile-time symbols that live at
the type level and can be reflected to a runtime string. Written
`'Foo` at use sites; participate in the type system as values of a new
kind, `Atom`.

This is a self-contained language feature. It exists independently of the
Generic deriving system, even though Generic deriving is the immediate
forcing function (see "Why" below). Once shipped, atoms become available
for other uses: nominal type tagging, capability tokens, phantom-typed
identifiers, and potentially attribute-based deriving down the road.

## Why

The user-extensible-derives feature (see
`docs/planning/user-extensible-derives.md` and
`docs/generic-deriving.md`) compiles user types into a structural
representation built from building blocks like `Variant`, `Labeled`,
`Record`, `Adt`. Today these carry constructor and field names as
**value-level strings**:

```saga
type Variant a = Variant String a
type Labeled a = Labeled String a
```

This works for the to-direction (serialization): the derive synthesizes
`Variant "Admin" U1` and a library's `ToJson for Variant` impl reads the
string out at runtime to emit `{"Admin": ...}`.

It breaks for the from-direction (deserialization) on sum types. The
synthesized `from` pattern-matches on `Or`-branch *position* with
wildcarded names:

```saga
from (Rep__Role (Adt _ (Or_Left  (Variant _ _)))) = Admin
from (Rep__Role (Adt _ (Or_Right (Or_Left  (Variant _ _))))) = Editor
from (Rep__Role (Adt _ (Or_Right (Or_Right (Variant _ _))))) = Viewer
```

The library's `FromJson for Variant` impl has no way to know the expected
name for its slot — the name is only encoded in the synthesized `from`,
downstream of the library code. Result: decoding `{"Editor": null}` into
`Role` always returns `Admin` (whichever variant `Or_Left` happens to
correspond to), regardless of the JSON tag. Silent data corruption.

This isn't an ergonomic gap; it's a correctness bug for any sum-type
from-direction derive. Lifting the names from values into types lets the
library compare expected names against runtime input and fail correctly
when they mismatch.

## What atoms are

A type-level atom literal is written `'Foo` and inhabits the new kind
`Atom`. Different atom literals are distinct types: `'Admin` ≠ `'Editor`.

A type parameter declared at kind `Atom` can be instantiated with any
atom literal. A type variable of kind `*` cannot hold an atom, and an
atom cannot appear in a `*` position — kinds don't mix.

Value-level reflection happens via a trait, dispatched through a `Proxy`
phantom type so the call site spells out which atom is being reflected:

```saga
type Proxy (n : Atom) = Proxy

trait KnownAtom (n : Atom) {
  fun atom_name : Proxy n -> String
}
```

The compiler auto-implements `KnownAtom` for every concrete atom literal
via a single universal impl backed by an intrinsic (see "Implementation"
below). At a call site:

```saga
atom_name (Proxy : Proxy 'Admin)   # => "Admin"
```

`Proxy` is a phantom — no runtime fields, exists only so its type
parameter is visible at the call site for trait dispatch. This mirrors
Haskell's `KnownSymbol`/`symbolVal` pattern.

Once atoms exist, the Generic building blocks change shape:

```saga
type Variant (n : Atom) a = Variant a    # name is now in the type
type Labeled (n : Atom) a = Labeled a
```

A library's from-direction `Variant` impl now constrains the atom and
can recover it via `KnownAtom`:

```saga
impl FromJson for Variant n a where {n : KnownAtom, a : FromJson} {
  from_json j = {
    let expected = atom_name (Proxy : Proxy n)
    ...compare expected against the JSON tag, fail if mismatch...
  }
}
```

The `Or` impl's "try left, fall back to right" then actually selects the
right variant because the wrong branch fails on the tag mismatch.

## Design decisions (pre-decided)

These are settled to keep the implementer from re-deriving them. Revisit
only if the implementation surfaces a concrete reason.

- **Kind syntax is explicit, not inferred.** Users write
  `type Variant (n : Atom) a = ...` to declare a type parameter at kind
  `Atom`. No implicit kind inference based on usage. Simpler to
  implement, easier to read, room to add inference later if needed.
- **One kind for atoms, not a full kind system.** `Atom` is added as a
  single extra kind alongside the implicit default `*`. No kind
  polymorphism, no kind variables. The minimum needed to express what
  the feature requires. `Kind` is represented as a Rust `enum` from
  day one (not a bool) so adding `Nat`, higher-kinded `* -> *`, etc.
  later is mechanical.
- **Kind annotations share syntactic shape with function labels**
  (`(name : Thing)`), disambiguated by position. Kinds appear only in
  type/trait/record/effect declaration parameter lists; trait bounds
  go in `where {...}`; function labels appear in arrow chains. Three
  uses of `:`, each locked to its clause. The alternative `::` was
  ruled out because Saga already uses `::` as the cons operator.
- **Atom literals lex as `'Foo` (apostrophe followed by an upper or
  lowercase identifier).** `'admin`, `'Admin`, `'first_name` are all
  valid atom literals; their corresponding runtime string is the
  identifier portion verbatim — no case transformation.
- **Atoms compile to BEAM atoms directly, preserving the source name
  verbatim.** `'Admin` becomes the BEAM atom `'Admin'` (quoted because
  it starts uppercase); `'admin` becomes the BEAM atom `admin`. The
  runtime representation is the same as any other BEAM atom.
- **Reflection via a `KnownAtom` trait taking `Proxy n`.** Consistent
  with how Saga already does typeclass-mediated dispatch, and the
  `Proxy` argument makes trait dispatch unambiguous at the call site
  (standard dispatch-on-argument-type, no special "look at where-clause
  bounds" rule needed). Mirrors Haskell's `KnownSymbol`/`symbolVal`
  pattern.
- **`KnownAtom` and `Proxy` live in the prelude** (alongside `Show`,
  `Eq`, etc.). Atom literals are a language-level feature; gating
  their reflection behind an import would be a weird seam.
- **The `KnownAtom` impl is provided by one universal mechanism**, not
  per-atom auto-emitted impls. Specifically: a single `impl KnownAtom n
  where {n : Atom}` backed by a compile-time intrinsic that extracts
  the atom's name at codegen. Cleaner than synthesizing N impls for N
  atom literals.

## Out of scope

- **Kind polymorphism / kind variables.** Single new kind, no
  abstraction over kinds.
- **Type-level computation on atoms** (e.g. concatenation, equality
  proofs). Not needed for the deriving use case. Atoms are opaque type
  values; the only operation is `KnownAtom` reflection.
- **Atom-tagged singleton types.** No need to materialize "the value of
  atom `'Foo` at the value level as its own type"; the `KnownAtom`
  trait gives sufficient reflection.
- **The Generic migration.** This planning doc covers atoms as a
  standalone feature. The Generic migration to use atoms is a separate
  follow-up phase (documented briefly under "Phase B" below for
  context, but implemented separately).

## Phase A: Standalone atom implementation

Self-contained. Atoms work end-to-end, with at least one small dogfooding
example unrelated to Generic deriving. Estimated scope: ~1 week.

### Lexer / parser

- Recognize `'Ident` and `'ident` at type-expression positions as atom
  literals. New token type, e.g. `Token::AtomLit(String)`.
- New `TypeExpr` variant: `TypeExpr::Atom(String, Span)`.
- Kind annotation syntax in type parameter declarations:
  `type T (n : Atom) a = ...`. Extends the existing type-parameter
  grammar to accept an optional `: Kind` annotation, where `Kind` is
  currently restricted to the bare identifier `Atom` (no other kinds
  exist in v1).
- Atom literals are NOT valid in value-expression positions. Value-level
  uses go through `KnownAtom`. Reject with a clear diagnostic if a user
  writes `'Foo` outside a type expression.

### Typechecker

- Add `Kind::Star` (the implicit default for everything today) and
  `Kind::Atom` to the typechecker. Most type machinery only deals with
  `Star`; `Atom` is a parallel track.
- During type-parameter registration (`check_traits.rs`, `check_decl.rs`),
  record the declared kind of each parameter. Parameters without an
  explicit annotation default to `Star`.
- Unification rules:
  - Two distinct atom literals do NOT unify: `'Admin` vs `'Editor` is a
    type error.
  - An atom literal unifies with a free Atom-kinded variable, binding
    the variable to that literal.
  - An atom literal does NOT unify with a `Star`-kinded variable (kind
    mismatch).
  - A `Star`-kinded type does NOT unify with an `Atom`-kinded variable.
- Kind checking when converting `TypeExpr` to `Type`: ensure atom
  literals appear only at Atom-kinded slots; ensure `Star`-kinded types
  don't appear at Atom-kinded slots.
- `convert_type_expr` (or equivalent) needs to know the expected kind
  of each position to enforce this. The expected kind comes from the
  containing type's parameter declarations.

### The `KnownAtom` trait + `Proxy` + universal impl

- Define `Proxy` and `KnownAtom` in the prelude (alongside `Show`,
  `Eq`, etc., so atom literals work without an extra import):
  ```saga
  type Proxy (n : Atom) = Proxy

  trait KnownAtom (n : Atom) {
    fun atom_name : Proxy n -> String
  }
  ```
- Provide one universal impl backed by an intrinsic. The intrinsic is a
  compiler builtin that, given a concrete atom literal at type
  resolution time, emits Core Erlang that returns the atom's name as a
  binary string.
- During trait resolution, `KnownAtom 'Foo` constraints resolve via the
  universal impl; the intrinsic is monomorphized per concrete atom at
  codegen time. The concrete atom is recovered from the `Proxy n`
  argument's inferred type at the call site.

### Codegen

- Atom literals at the type level are erased at runtime (types are
  erased generally; atoms are no different).
- The `KnownAtom` impl's body, when invoked with a concrete atom `'Foo`,
  emits Core Erlang that constructs the binary string `<<"Foo">>` (or
  whatever the stdlib `String` representation is). The codegen pass
  needs to see which concrete atom is being reflected — likely via
  evidence on the call site, similar to how trait-method dispatch
  carries type info today.

### Tests

- `'Admin` and `'Editor` are distinct types — unification fails.
- An Atom-kinded variable unifies with `'Admin` and the binding sticks
  through subsequent constraints.
- `KnownAtom 'Foo` resolves and `atom_name ()` returns `"Foo"` at
  runtime. Cover several atom names (capitalized, lowercase, with
  underscores).
- Kind-mismatch errors: passing a `Star`-kinded type to an Atom-kinded
  slot fails with a clear diagnostic. Same for the reverse.
- Atom literal in value-expression position fails with a clear
  diagnostic.
- A small example file (suggested: `examples/atoms-tagging.saga`)
  demonstrating atoms used for nominal tagging — e.g. `type Id (kind :
  Atom) = Id Int` with `type UserId = Id 'user` and `type PostId = Id
  'post`, and a function `same_kind : Id k -> Id k -> Bool` that only
  accepts IDs of the same kind. Pure-atom usage; no Generic
  involvement.

### Phase A acceptance

- The dogfooding example compiles and runs.
- All kind-related diagnostics fire correctly on misuse.
- `cargo test` clean. `cargo clippy` clean.
- No regressions in existing examples or tests.

## Phase B: Generic migration (separate work)

Once Phase A is solid, the Generic deriving system migrates to use
atoms. Brief outline only — full prompt to be written after Phase A
lands.

- Update `Std.Generic` building blocks:
  ```saga
  type Variant (n : Atom) a = Variant a
  type Labeled (n : Atom) a = Labeled a
  ```
  (Drop the value-level `String` field.)
- Update the derive synthesizer in `src/derive.rs`:
  - To-direction synthesis: emit `Variant 'Admin U1` instead of
    `Variant "Admin" U1`.
  - From-direction synthesis: the `from` pattern no longer needs to
    match the name (it's at the type level). Simpler patterns.
- Update existing Generic-aware library code, tests, examples (99b
  through 99k). Mechanical churn; ~100-200 lines across the codebase.
- Add tests demonstrating the bug repro now decodes correctly:
  `type Role = Admin | Editor | Viewer deriving (FromJson)` round-trips
  through JSON without misidentifying variants.
- Update `docs/generic-deriving.md` and the website guide to reflect
  the new building-block shapes and the `KnownAtom` reflection pattern.

Phase B estimate: ~1-2 days once Phase A is in.

## Risks

- **Kind checking is a parallel code path.** Adding kinds to the
  typechecker means every place that converts `TypeExpr` to `Type` or
  unifies types needs to be aware of kinds. Easy to miss a code path
  and produce confusing errors or accept invalid programs. Mitigation:
  comprehensive test coverage of edge cases (atom in wrong position,
  star in wrong position, kind-mismatch in nested generics).
- **Interaction with trait-method-var freshening (Phase 1.5 of the
  derives plan).** When a multi-param trait has Atom-kinded
  parameters, the per-impl var freshening needs to allocate fresh
  Atom-kinded vars, not `Star`-kinded. Worth verifying.
- **Interaction with the call-site coherence fallback (Phase 2e of the
  derives plan).** The fallback substitutes impl tvars with concrete
  args; needs to respect kinds during substitution.
- **The universal-impl-with-intrinsic approach for `KnownAtom`** has to
  thread the concrete atom through to codegen. Verify the
  evidence-passing machinery supports this — it should, since it
  already carries type-parameter values through trait dispatch.
- **LSP / hover / error messages.** All need to handle atom kinds and
  atom literals cleanly. Budget time for diagnostic polish.

## Open questions

(All previously open questions were resolved during design discussion;
see "Design decisions" above. Outcomes: BEAM atoms preserve the source
name verbatim and are quoted when BEAM requires it; `KnownAtom` and
`Proxy` live in the prelude; reflection takes `Proxy n`, not `Unit`.)

## Decision log

- **Single new kind, not full kind system.** Smallest change that
  unblocks the use case.
- **Explicit kind annotations, not inferred.** Easier to implement and
  read; revisit if ergonomics complaints surface.
- **Trait-based reflection (`KnownAtom`), not free function.**
  Consistent with existing Saga conventions.
- **Reflection method takes `Proxy n`, not `Unit`.** Makes trait
  dispatch unambiguous via the standard dispatch-on-argument-type rule.
  `Unit` would have required either a new "infer `n` from where-clause
  bounds" resolver rule or type-application syntax (which Saga lacks).
- **`KnownAtom` and `Proxy` live in the prelude.** Atom literals are
  language-level; reflection should not require an extra import.
- **BEAM atom representation: source name verbatim.** `'Admin` → BEAM
  `'Admin'`; `'admin` → BEAM `admin`. No case transformation.
- **Kind annotation syntax `(name : Kind)` shares shape with function
  labels but is unambiguous by position.** `::` was unavailable (cons).
- **One universal impl backed by an intrinsic, not per-atom synthesized
  impls.** Cleaner module structure; small intrinsic cost.
- **Atoms compile to BEAM atoms.** Free runtime story on the target
  platform.
- **Phase A is fully self-contained.** Phase B (Generic migration) is a
  separate follow-up so atoms can be validated independently before
  becoming load-bearing for derives.
