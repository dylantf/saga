# Exposing System & Re-exports

## Goal

Two related features, sharing one grammar:

1. **Import aliasing** (standalone): rename a name as you bring it in —
   `import M (a as b)`, mirroring the existing module alias `import M as Mod`.
2. **Re-exports**: let a module expose a name that originates in another module,
   without redefining it — `import M (pub c)`.

Both extend the import exposing list. Aliasing is useful on its own (name
collisions, local clarity) and is a prerequisite for renaming-on-re-export, so
it lands first.

## Design principle

The current export model anchors `pub` to a **definition**: you write a type
annotation (which unlocks `pub`) and the publicness lives next to the
definition. This forces every public function to carry a documented signature
and keeps the public/private decision local — no separate export list to jump
to.

Re-exports have no local definition to anchor to. The reframe that keeps the
model coherent:

> `pub` marks a **name** as part of this module's public surface — wherever the
> name originates. For a definition, the name originates at the def (and earns
> `pub` by carrying an annotation). For a re-export, the name originates at an
> import (and already carries a signature in its home module).

So re-exports don't weaken the "everything public has a documented type" rule —
the annotation just lives in the origin module. `pub` always appears next to the
name it exposes, whether that name is in a `fun` signature or an import list.

## Syntax

### Module aliasing (already exists)

```saga
import SomeModule as Mod
```

### Item aliasing (new, standalone)

```saga
import SomeModule (a as b)        # bring in `a`, locally named `b`
```

`a as b` echoes `Module as Mod` — same keyword, same shape.

### Inline re-export

`pub` before an item in the list marks it re-exported:

```saga
import SomeModule (a, b, pub c)   # use a, b; re-expose c
```

The rule is uniform: **inside an import list, `pub` before a name marks that
name as re-exported.** `pub` only ever appears inside the parens, so a module's
imports stay one statement each — no second import line for the same module, no
alignment problem.

### Whole-module re-export (facade / prelude)

```saga
import SomeModule (pub ..)        # re-export SomeModule's entire public surface
```

This is the facade pattern: a `Std` prelude that re-exports `Std.List`,
`Std.Maybe`, etc. `(pub ..)` brings every public name into scope *and* re-exports
it. (Re-export-all-without-local-import is not expressible; that's harmless —
having the names in scope costs nothing.)

### Combined

All four combine. The fully-loaded form:

```saga
import SomeModule as Mod (pub a as b)
```

means: qualified namespace `Mod`; bring in `a` from `SomeModule`; locally name it
`b`; re-export it under `b`. The `as` appears in two roles (module alias, item
alias) — accepted indirection.

### Grammar summary

```
import-decl  := 'import' module-path ('as' UpperIdent)? exposing?
exposing     := '(' ( all | item (',' item)* ) ')'
all          := 'pub'? '..'
item         := 'pub'? name ('as' name)?
name         := Ident | UpperIdent          # Upper hoists constructors as today
```

## Semantics

### Re-export at the type layer

When `Facade` does `import M (pub c)`, `Facade`'s own `ModuleExports` gains an
entry for `c` whose scheme is **M's** scheme for `c`. Importers of `Facade` see
`c` exactly as if it were defined in `M`. With renaming (`pub c as d`), the
surface name is `d` but the scheme and identity are still M's `c`.

### Codegen transparency (origin-pointing)

A re-export is transparent at the BEAM layer: it carries the **origin module**.
Calling `Facade.c` must emit `call 'm':'c'(...)`, not `call 'facade':'c'` —
`Facade` never defines `c`, so no such beam function exists. This should fall out
of the existing canonical-identity machinery (`register_module_canonical_exports`
/ `imported_names`): the re-exported name resolves to canonical identity `M.c`,
and codegen already lowers qualified calls against canonical identity. The
re-export adds a surface name pointing at an existing canonical identity; it does
**not** generate a forwarding wrapper.

### Visibility can only narrow

A re-export cannot widen visibility beyond what the origin grants, but it can
match it. Two cases to keep distinct:

- **Opaque type** — `M` exposes the type but hides its constructors. Re-exporting
  it is **allowed**: `Facade` re-exposes the opaque type and opacity propagates
  unchanged. Importers of `Facade` get the type but still cannot construct or
  pattern-match it, exactly as if they imported `M` directly. The re-export does
  not (and cannot) re-expose the hidden constructors — there is no widening.
- **Private name** — `M` does not make the name public at all. Re-exporting it is
  a **type error**: you can't expose what the origin keeps private.

In short: re-export visibility ≤ origin visibility, and opaque is a valid level to
carry forward, not an error.

### Types and constructors

There is no per-constructor granularity — the language is OCaml/F#/Rust-style:
importing a type brings *all* its constructors into scope (the existing
Upper-name-hoists-constructors behavior, [ast.rs:251](../../src/ast.rs#L251)),
not Haskell-style `MyType(A, B)` selection. Re-export follows the same all-or-
nothing rule: `import M (pub MyType)` re-exports `MyType` with every constructor
the origin exposes — or none of them, if the origin keeps the type opaque (the
narrowing rule). There is nothing finer to express.

### Conflicts

Two re-exports (or a re-export and a local def) producing the same surface name
is an error, reported at the importing module — same class as any other
duplicate-binding diagnostic. Renaming (`as`) is the escape hatch.

## AST changes

`ExposedItem` is currently `type ExposedItem = String` ([ast.rs:252](../../src/ast.rs#L252)).
Promote it to a struct:

```rust
pub struct ExposedItem {
    pub name: String,          // origin name in the imported module
    pub alias: Option<String>, // local/surface name; defaults to `name`
    pub public: bool,          // re-export flag (`pub` prefix)
    pub span: Span,
}
```

`Exposing::All` ([ast.rs:259](../../src/ast.rs#L259)) gains a `public: bool` for
`(pub ..)`:

```rust
pub enum Exposing {
    All { public: bool, span: Span },
    Items(Vec<ExposedItem>),
}
```

`Exposing::exposes` and any code matching these variants need updating — the
compiler will flag every site once the struct changes.

## Implementation steps

### 1. Parser

Extend the item loop in `parse_import_decl`
([decl.rs:1576-1601](../../src/parser/decl.rs#L1576-L1601)):

- Optional leading `pub` per item → `public`.
- Optional trailing `as <name>` → `alias`.
- For the `(..)` branch ([decl.rs:1561](../../src/parser/decl.rs#L1561)), accept
  an optional leading `pub` → `Exposing::All { public }`.

Validate: `as` target must match the kind (lower→lower, Upper→Upper); reject
`pub ..` mixed with items (the existing "`(..)` must be the entire list" check
already covers the shape).

### 2. AST + downstream match sites

Apply the struct changes above. Update `Exposing::exposes`, the LSP/resolve
sites that read exposing items, and `synthesize_all_exposed`
([check_module.rs:1335](../../src/typechecker/check_module.rs#L1335)) to produce
`ExposedItem`s carrying `public` from the `All { public }` flag.

### 3. Item aliasing in resolution

Wire `alias` through `resolve_import` / `merge_import_scope`
([check_module.rs:1034](../../src/typechecker/check_module.rs#L1034),
[check_module.rs:1369](../../src/typechecker/check_module.rs#L1369)): the
scope-map entry binds the **alias** (surface name) to the origin's canonical
identity. This is the standalone aliasing feature and can ship before any
re-export work — it touches only how an exposed name is keyed locally.

### 4. Re-export collection

`ModuleExports::collect` ([check_module.rs:48](../../src/typechecker/check_module.rs#L48))
currently gathers only `pub` *definitions* (`public_names_for_tc`). Extend it to
also walk `Decl::Import` declarations and, for every item with `public: true` (or
under `(pub ..)`), copy the corresponding entry **from the imported module's
already-resolved `ModuleExports`** into this module's exports, keyed by the
surface name (alias or origin name).

The imported module's exports are available because the importing module
typechecks after its imports (non-cyclic case). Each re-exported entry must
retain the **origin's canonical identity** so codegen points at the origin (per
"Codegen transparency"). Enforce the narrowing rule here: skip / error on
constructors the origin keeps opaque.

### 5. Codegen

Verify (likely no new code) that a re-exported name lowers to a call against its
origin canonical identity, not the re-exporting module. The risk is any path that
assumes "exported by module X ⇒ defined in module X's beam." Audit
`register_module_canonical_exports` and the qualified-call lowering for that
assumption; add a test where `Facade` re-exports `M.c` and a third module calls
`Facade.c`.

### 6. Docs generation

`saga docs` must render a re-exported name's signature by following it to the
origin module (the local file has no signature for it). Mark re-exports in
generated docs (e.g. "re-exported from `M`") so the facade's public surface is
discoverable.

## Edge cases / open decisions

- **`(pub ..)` qualified vs unqualified.** Decide whether whole-module re-export
  surfaces names unqualified (prelude-style, the useful case) or re-exports the
  qualified namespace. Recommend unqualified to match the facade goal; flag
  explicitly since `import M` with no list currently means qualified-only access.
- **Cyclic re-exports.** `A` re-exports from `B` while `B` re-exports from `A`
  is a resolution cycle. This needs the SCC machinery from
  [circular-imports.md](circular-imports.md) to resolve re-export edges within an
  SCC. Until that lands, a re-export cycle should be a clean error, not a hang.

## v1 scope vs deferred

**v1:**

- Item aliasing `a as b` (ship first, independent).
- Value + function re-export, inline `pub` and `(pub ..)`.
- Type re-export with its public constructors (whole-type granularity).
- Narrowing rule, conflict detection, docs integration.

**Deferred:**

- Re-export cycles (blocked on circular-imports SCC work).

## Interaction with circular imports

[circular-imports.md](circular-imports.md) step 1 already lists "Export/visibility
information" as part of the `ModuleHeader` that must be buildable from the AST
without inference. Re-exports make that field non-trivial: the header must be able
to name a re-exported symbol's **origin module**, and header-based scope
construction (that plan's step 4) must follow re-export edges — possibly within an
SCC. Settling this export model first means the header is designed once against
the final semantics rather than retrofitted. This is the argument for doing the
exposing revamp before circular imports.

## Relevant files

- `src/ast.rs`: `ExposedItem`, `Exposing`, `Decl::Import`
- `src/parser/decl.rs`: `parse_import_decl` (item loop, `(..)` branch)
- `src/typechecker/check_module.rs`: `ModuleExports::collect`, `resolve_import`,
  `merge_import_scope`, `register_module_canonical_exports`,
  `synthesize_all_exposed`, `inject_exports`
- `src/codegen/lower/`: qualified-call lowering against canonical identity
- `saga docs` generation: re-export signature resolution
