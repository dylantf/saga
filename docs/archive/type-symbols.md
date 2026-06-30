# Type-Level Symbols

## Goal

Add type-level symbols to Saga: interned, compile-time symbols that live at
the type level and can be reflected to a runtime string. Written
`'Foo` at use sites; participate in the type system as values of a new
kind, `Symbol`.

This is a self-contained language feature. It exists independently of the
Generic deriving system, even though Generic deriving is the immediate
forcing function (see "Why" below). Once shipped, symbols become available
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

## What symbols are

A type-level symbol literal is written `'Foo` and inhabits the new kind
`Symbol`. Different symbol literals are distinct types: `'Admin` ≠ `'Editor`.

A type parameter declared at kind `Symbol` can be instantiated with any
symbol literal. A type variable of kind `*` cannot hold a symbol, and a
symbol cannot appear in a `*` position — kinds don't mix.

Value-level reflection happens via a trait, dispatched through a `Proxy`
phantom type so the call site spells out which symbol is being reflected:

```saga
type Proxy (n : Symbol) = Proxy

trait KnownSymbol (n : Symbol) {
  fun symbol_name : Proxy n -> String
}
```

The compiler auto-implements `KnownSymbol` for every concrete symbol literal
via a single universal impl backed by an intrinsic (see "Implementation"
below). At a call site:

```saga
symbol_name (Proxy : Proxy 'Admin)   # => "Admin"
```

`Proxy` is a phantom — no runtime fields, exists only so its type
parameter is visible at the call site for trait dispatch. This mirrors
Haskell's `KnownSymbol`/`symbolVal` pattern.

Once symbols exist, the Generic building blocks change shape:

```saga
type Variant (n : Symbol) a = Variant a    # name is now in the type
type Labeled (n : Symbol) a = Labeled a
```

A library's from-direction `Variant` impl now constrains the symbol and
can recover it via `KnownSymbol`:

```saga
impl FromJson for Variant n a where {n : KnownSymbol, a : FromJson} {
  from_json j = {
    let expected = symbol_name (Proxy : Proxy n)
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
  `type Variant (n : Symbol) a = ...` to declare a type parameter at kind
  `Symbol`. No implicit kind inference based on usage. Simpler to
  implement, easier to read, room to add inference later if needed.
- **One kind for symbols, not a full kind system.** `Symbol` is added as a
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
- **Symbol literals lex as `'Foo` (apostrophe followed by an upper or
  lowercase identifier).** `'admin`, `'Admin`, `'first_name` are all
  valid symbol literals; their corresponding runtime string is the
  identifier portion verbatim — no case transformation.
- **Symbols would compile to BEAM atoms, preserving the source name
  verbatim.** `'Admin` would become the BEAM atom `'Admin'` (quoted because
  it starts uppercase); `'admin` would become the BEAM atom `admin`. The
  runtime representation would be the same as any other BEAM atom.

  Note (scope clarification): in Phase A and Phase B, no runtime value
  of a symbol-kinded type ever materializes — symbols live at the type
  level (kind `Symbol`, not `*`), and the only runtime artifact is the
  reflected `String` returned by `symbol_name`, which is a binary. The
  BEAM-atom correspondence above is therefore *aspirational* — it
  describes the representation we'd use if/when symbols are ever lifted
  to value-level (the out-of-scope "symbol-tagged singleton types"
  feature). For now, the only codegen path is `String`-via-reflection.
  The 1M BEAM-atom-table limit is not relevant to this feature as
  scoped, because no code path consumes from the atom table.
- **Reflection via a `KnownSymbol` trait taking `Proxy n`.** Consistent
  with how Saga already does typeclass-mediated dispatch, and the
  `Proxy` argument makes trait dispatch unambiguous at the call site
  (standard dispatch-on-argument-type, no special "look at where-clause
  bounds" rule needed). Mirrors Haskell's `KnownSymbol`/`symbolVal`
  pattern.
- **`KnownSymbol` and `Proxy` live in the prelude** (alongside `Show`,
  `Eq`, etc.). Symbol literals are a language-level feature; gating
  their reflection behind an import would be a weird seam.
- **The `KnownSymbol` impl is provided by one universal mechanism**, not
  per-symbol auto-emitted impls. Specifically: a single `impl KnownSymbol n
  where {n : Symbol}` backed by a compile-time intrinsic that extracts
  the symbol's name at codegen. Cleaner than synthesizing N impls for N
  symbol literals.

## Out of scope

- **Kind polymorphism / kind variables.** Single new kind, no
  abstraction over kinds.
- **Type-level computation on symbols** (e.g. concatenation, equality
  proofs). Not needed for the deriving use case. Symbols are opaque type
  values; the only operation is `KnownSymbol` reflection.
- **Symbol-tagged singleton types.** No need to materialize "the value of
  symbol `'Foo` at the value level as its own type"; the `KnownSymbol`
  trait gives sufficient reflection.
- **The Generic migration.** This planning doc covers symbols as a
  standalone feature. The Generic migration to use symbols is a separate
  follow-up phase (documented briefly under "Phase B" below for
  context, but implemented separately).

## Phase A: Standalone symbol implementation

Self-contained. Symbols work end-to-end, with at least one small dogfooding
example unrelated to Generic deriving. Estimated scope: ~1 week.

### Lexer / parser

- Recognize `'Ident` and `'ident` at type-expression positions as symbol
  literals. New token type, e.g. `Token::SymbolLit(String)`.
- New `TypeExpr` variant: `TypeExpr::Symbol(String, Span)`.
- Kind annotation syntax in type parameter declarations:
  `type T (n : Symbol) a = ...`. Extends the existing type-parameter
  grammar to accept an optional `: Kind` annotation, where `Kind` is
  currently restricted to the bare identifier `Symbol` (no other kinds
  exist in v1).
- Symbol literals are NOT valid in value-expression positions. Value-level
  uses go through `KnownSymbol`. Reject with a clear diagnostic if a user
  writes `'Foo` outside a type expression.

### Typechecker

- Add `Kind::Star` (the implicit default for everything today) and
  `Kind::Symbol` to the typechecker. Most type machinery only deals with
  `Star`; `Symbol` is a parallel track.
- During type-parameter registration (`check_traits.rs`, `check_decl.rs`),
  record the declared kind of each parameter. Parameters without an
  explicit annotation default to `Star`.
- Unification rules:
  - Two distinct symbol literals do NOT unify: `'Admin` vs `'Editor` is a
    type error.
  - A symbol literal unifies with a free Symbol-kinded variable, binding
    the variable to that literal.
  - A symbol literal does NOT unify with a `Star`-kinded variable (kind
    mismatch).
  - A `Star`-kinded type does NOT unify with a `Symbol`-kinded variable.
- Kind checking when converting `TypeExpr` to `Type`: ensure symbol
  literals appear only at Symbol-kinded slots; ensure `Star`-kinded types
  don't appear at Symbol-kinded slots.
- `convert_type_expr` (or equivalent) needs to know the expected kind
  of each position to enforce this. The expected kind comes from the
  containing type's parameter declarations.

### The `KnownSymbol` trait + `Proxy` + universal impl

- Define `Proxy` and `KnownSymbol` in the prelude (alongside `Show`,
  `Eq`, etc., so symbol literals work without an extra import):
  ```saga
  type Proxy (n : Symbol) = Proxy

  trait KnownSymbol (n : Symbol) {
    fun symbol_name : Proxy n -> String
  }
  ```
- Provide one universal impl backed by an intrinsic. The intrinsic is a
  compiler builtin that, given a concrete symbol literal at type
  resolution time, emits Core Erlang that returns the symbol's name as a
  binary string.
- During trait resolution, `KnownSymbol 'Foo` constraints resolve via the
  universal impl; the intrinsic is monomorphized per concrete symbol at
  codegen time. The concrete symbol is recovered from the `Proxy n`
  argument's inferred type at the call site.

### Codegen

- Symbol literals at the type level are erased at runtime (types are
  erased generally; symbols are no different).
- The `KnownSymbol` impl's body, when invoked with a concrete symbol `'Foo`,
  emits Core Erlang that constructs the binary string `<<"Foo">>` (or
  whatever the stdlib `String` representation is). The codegen pass
  needs to see which concrete symbol is being reflected — likely via
  evidence on the call site, similar to how trait-method dispatch
  carries type info today.

### Tests

- `'Admin` and `'Editor` are distinct types — unification fails.
- A Symbol-kinded variable unifies with `'Admin` and the binding sticks
  through subsequent constraints.
- `KnownSymbol 'Foo` resolves and `symbol_name ()` returns `"Foo"` at
  runtime. Cover several symbol names (capitalized, lowercase, with
  underscores).
- Kind-mismatch errors: passing a `Star`-kinded type to a Symbol-kinded
  slot fails with a clear diagnostic. Same for the reverse.
- Symbol literal in value-expression position fails with a clear
  diagnostic.
- A small example file (suggested: `examples/symbols-tagging.saga`)
  demonstrating symbols used for nominal tagging — e.g. `type Id (kind :
  Symbol) = Id Int` with `type UserId = Id 'user` and `type PostId = Id
  'post`, and a function `same_kind : Id k -> Id k -> Bool` that only
  accepts IDs of the same kind. Pure-symbol usage; no Generic
  involvement.

### Phase A acceptance

- The dogfooding example compiles and runs.
- All kind-related diagnostics fire correctly on misuse.
- `cargo test` clean. `cargo clippy` clean.
- No regressions in existing examples or tests.

## Phase B: Generic migration (separate work)

Once Phase A is solid, the Generic deriving system migrates to use
symbols. Brief outline only — full prompt to be written after Phase A
lands.

- Update `Std.Generic` building blocks:
  ```saga
  type Variant (n : Symbol) a = Variant a
  type Labeled (n : Symbol) a = Labeled a
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
  the new building-block shapes and the `KnownSymbol` reflection pattern.

Phase B estimate: ~1-2 days once Phase A is in.

## Risks

- **Kind checking is a parallel code path.** Adding kinds to the
  typechecker means every place that converts `TypeExpr` to `Type` or
  unifies types needs to be aware of kinds. Easy to miss a code path
  and produce confusing errors or accept invalid programs. Mitigation:
  comprehensive test coverage of edge cases (symbol in wrong position,
  star in wrong position, kind-mismatch in nested generics).
- **Interaction with trait-method-var freshening (Phase 1.5 of the
  derives plan).** When a multi-param trait has Symbol-kinded
  parameters, the per-impl var freshening needs to allocate fresh
  Symbol-kinded vars, not `Star`-kinded. Worth verifying.
- **Interaction with the call-site coherence fallback (Phase 2e of the
  derives plan).** The fallback substitutes impl tvars with concrete
  args; needs to respect kinds during substitution.
- **The universal-impl-with-intrinsic approach for `KnownSymbol`** has to
  thread the concrete symbol through to codegen. Verify the
  evidence-passing machinery supports this — it should, since it
  already carries type-parameter values through trait dispatch.
- **LSP / hover / error messages.** All need to handle symbol kinds and
  symbol literals cleanly. Budget time for diagnostic polish.

## Open questions

(All previously open questions were resolved during design discussion;
see "Design decisions" above. Outcomes: BEAM symbols preserve the source
name verbatim and are quoted when BEAM requires it; `KnownSymbol` and
`Proxy` live in the prelude; reflection takes `Proxy n`, not `Unit`.)

## Decision log

- **Single new kind, not full kind system.** Smallest change that
  unblocks the use case.
- **Explicit kind annotations, not inferred.** Easier to implement and
  read; revisit if ergonomics complaints surface.
- **Trait-based reflection (`KnownSymbol`), not free function.**
  Consistent with existing Saga conventions.
- **Reflection method takes `Proxy n`, not `Unit`.** Makes trait
  dispatch unambiguous via the standard dispatch-on-argument-type rule.
  `Unit` would have required either a new "infer `n` from where-clause
  bounds" resolver rule or type-application syntax (which Saga lacks).
- **`KnownSymbol` and `Proxy` live in the prelude.** Symbol literals are
  language-level; reflection should not require an extra import.
- **BEAM atom representation (aspirational): source name verbatim.** `'Admin`
  would map to BEAM `'Admin'`; `'admin` to BEAM `admin`. No case transformation.
  Not exercised by current scope; see the scope clarification above.
- **Kind annotation syntax `(name : Kind)` shares shape with function
  labels but is unambiguous by position.** `::` was unavailable (cons).
- **One universal impl backed by an intrinsic, not per-symbol synthesized
  impls.** Cleaner module structure; small intrinsic cost.
- **Symbols would compile to BEAM atoms (aspirational).** Free runtime story on the target
  platform.
- **Phase A is fully self-contained.** Phase B (Generic migration) is a
  separate follow-up so symbols can be validated independently before
  becoming load-bearing for derives.
