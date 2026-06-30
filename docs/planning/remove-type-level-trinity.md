# Removing the Type-Level Trinity (Generic deriving, fundeps, Symbol kind)

## Goal

Delete three interlocking features and revert the language to **trait dispatch +
a closed set of compiler derives**, with no type-level computation:

1. **Generic deriving** — the `Generic` representation trait and the
   routed/user-extensible derive machinery (structural rep + runtime walks),
   plus the `generic_fold` deforestation pass that exists only to make those
   walks fast.
2. **Functional dependencies** — the `trait T a b | a -> b` annotation and the
   fixpoint constraint-improvement solver that resolves determined params.
3. **Symbol kind** — type-level symbols (`'Foo`, `(n : Symbol)`), the
   `KnownSymbol` trait, and `Proxy`.

This is a **subtraction**, not a redesign. The trait system itself (dispatch,
`where` bounds, conditional impls, supertraits, dictionary passing) stays
exactly as-is. We are removing the type-level-programming layer that was bolted
on top of it.

## Why (rationale, for future readers)

- The three features are the classic "type-level programming" trinity:
  structural reflection + fundep-driven computation + type-level strings. They
  have no natural stopping point and were trending toward reimplementing GHC's
  type system — a maintenance black hole for a solo, ML/effects-focused
  language.
- Most of the machinery was built via directed prompting, not from
  first-principles understanding, so it is hard to own and extend safely.
- The cost is large and partly hidden: the Generic system needs a ~2,200-line
  fusion/deforestation pass (`codegen/generic_fold/`) purely to claw back the
  performance lost to runtime generic walks. Two complex subsystems for one
  capability.
- **The replacement has already been validated.** The Kraken querybuilder was
  rewritten with no non-`Std` derives, no fundeps, no `Generic`; the only thing
  it needed was the new **record builder** feature (`build` keyword), which is
  ~1,300 lines of pure desugaring with zero runtime machinery. So the trinity
  buys "a bit of userland niceness" that we are deliberately trading away.

See the conversation that motivated this for the longer argument; the short
version: the black hole is *type-level computation*, not traits. Rust proves
typeclasses are bounded if you keep extensibility in macros/codegen rather than
in the type system. Our equivalent of Rust's std derives already exists
(`src/derive/builtin.rs`); we are deleting our equivalent of GHC.Generics.

## What is removed vs. kept

| Area | Remove | Keep |
| --- | --- | --- |
| Derives | `deriving (Generic)`, routed/user-defined derives | `deriving (Show, Debug, Eq, Ord, Enum, Default)` (built-in, codegen) |
| Traits | fundep `\|` annotation + improvement solver | multi-param traits (e.g. `ConvertTo a b`), `where` bounds, conditional impls, supertraits, dict passing |
| Kinds | `Symbol` kind, `KnownSymbol`, `Proxy`, symbol literals `'Foo` | ordinary kinds (`*`, arrows) |
| Codegen | `codegen/generic_fold/` (fusion/deforestation) | everything else |
| Stdlib | `Std.Generic` module | `Std.Base` minus `Proxy`/`KnownSymbol` |

## Dependency graph (drives removal order)

```
Generic deriving  ──needs──>  fundeps   (Generic a r | a -> r coherence)
       │
       └────────needs──────>  Symbol    (Labeled / Variant field names, KnownSymbol)

fundeps:  only built-in functional trait is `Generic`. User fundep traits
          (Selectable, TableScope) exist ONLY in examples/bugs/ + scratch.saga.
Symbol:   independent feature; only real users are Generic + KnownSymbol/Proxy.
```

Because Generic is the top consumer and the others exist mostly to serve it,
remove **top-down**: Generic first, then fundeps, then Symbol. Each phase should
leave a compiling, passing tree.

## Removal order (phased)

### Phase 0 — Userland & fixtures first (so nothing references doomed machinery)
- Delete Generic example programs:
  - `examples/99e-generic-recursive.saga`
  - `examples/99d-generic-parameterized.saga`
  - `examples/99k-generic-derived-defaults.saga`
  - `examples/99-generic-spike.saga`
  - any other `examples/99*generic*` / `examples/scratch.saga` Generic content
- Delete fundep bug-repro fixtures:
  - `examples/bugs/parameterized_record_selectable_derive_repro.saga`
  - `examples/bugs/multi-fundeps-dict-collision.saga`
  - `examples/bugs/table-scope-arity.saga`
  - `examples/bugs/multi-fundep-disambiguation.saga`
  - `examples/scratch.saga` (Selectable) — trim or delete
- Stdlib:
  - `src/stdlib/prelude.saga:12` — remove `import Std.Generic (Generic)`
  - `src/stdlib/Base.saga:117-125` — remove `Proxy` type + `KnownSymbol` trait
  - delete `src/stdlib/Generic.saga`
  - remove `Proxy, KnownSymbol` from `prelude.saga:1` import of `Std.Base`
- Grep the Rust **test suite** for `deriving (Generic)`, `Generic`, `fundep`,
  `Symbol`, `KnownSymbol`, `Selectable`, `'Foo` and delete/trim those tests.

### Phase 1 — Generic deriving system
Remove the routed/Generic derive path; **keep** the built-in derive path.

- `src/derive/`
  - **Delete:** `generic.rs` (704), `routed.rs` (1,125), `applied.rs` (835).
    *(verify `applied.rs`: it reads the fundep carrier/synth roles —
    `derive/applied.rs:286-329` — so it is Generic/fundep-specific.)*
  - **Prune (do not delete):** `expand.rs` (1,054) — the derive-expansion
    dispatcher. Remove the routed/Generic routing; keep built-in routing.
  - **Verify & likely prune:** `scope.rs` (320, has a `fundep` field at
    `derive/scope.rs:16`), `type_expr.rs` (322), `imports.rs` (525),
    `helpers.rs` (109) — determine which are shared with built-in derives vs.
    Generic-only; prune the Generic-only parts.
  - **Keep:** `builtin.rs` (949), `mod.rs` (41, update module list).
- `src/codegen/generic_fold/` — **delete the whole directory** (2,174 LOC:
  `mod.rs`, `folder.rs`, `rewrite.rs`, `substitute.rs`, `externals.rs`) and its
  call site in `src/codegen/resolve.rs`.
- Typechecker: remove Generic-trait special cases — `is_generic_trait_name`,
  `anon_record_generic_rep` / `anon_record_from_generic_rep`, and the
  Generic branch in `improve_pending_fundeps` (`constraints.rs:20-51`,
  `175-203`). (These die naturally with Phase 2 but are listed here as Generic's.)
- Parser: keep the `deriving (...)` clause; it now only ever routes to built-in
  derives.
- Docs: delete `docs/generic-deriving.md` (911) and
  `docs/planning/user-extensible-derives.md`.

### Phase 2 — Functional dependencies
After Phase 1, the **only** built-in functional trait (`Generic`) is gone, and
no production code declares a `|` trait.

- `src/typechecker/check_decl/constraints.rs` — delete
  `improve_pending_fundeps` (~`12-209`). This is the ~200-line fixpoint solver;
  it is the bulk of the genuine solver complexity. Its only non-Generic job is
  single-step "pin determined from determinant," which has no remaining users.
- `src/typechecker/records.rs:350` — remove the `self.improve_pending_fundeps()`
  call (field-access disambiguation no longer needs it).
- `src/typechecker/check_traits.rs`
  - delete `FUNCTIONAL_TRAITS` const (`:18`) and the
    `has_builtin_functional_rule` logic (`:374-...`) and fundep construction in
    `register_trait_def` (`:378-...`).
  - delete `resolve_fundep_where_app` (`:1333`).
- `src/typechecker/check_decl/functions.rs:774,836` — remove the
  `FUNCTIONAL_TRAITS` call-site coherence rule.
- `src/typechecker/state.rs` — delete `TraitFundep` struct (`109-134`) and the
  `fundep` / `is_functional` fields on `TraitInfo` (`144-153`); delete the
  fundep-driven dict-param field comment/usage (`:208`).
- `src/elaborate/dict_resolve.rs`, `dict_params.rs` — remove fundep-driven dict
  resolution paths.
- AST/parser/formatter:
  - `src/ast.rs:1470-1487` — delete `TraitFunctionalDependency`.
  - `src/parser/decl.rs:941-956` — delete `| a b -> c` parsing.
  - `src/formatter/decl.rs:474-476` — delete fundep re-emission.
  - `src/cli/docs.rs:469-470` — delete fundep doc rendering.
- Fingerprint/LSP: `src/cli/cache.rs:290-294` and `src/lsp/analysis.rs:181-185`
  hash `info.fundep`; remove those branches.
- **Keep multi-param traits.** `ConvertTo a b` (no `|`) must still typecheck —
  confirm its resolution path doesn't secretly depend on fundep improvement
  (it shouldn't: both params are concrete at the use site). See Risks.

### Phase 3 — Symbol kind
After Phases 1-2, only `KnownSymbol`/`Proxy` (already removed in Phase 0) and the
deleted Generic rep used Symbols.

- `src/ast.rs:12-14` — delete `Kind::Symbol`; `1180-1195` — delete
  `TypeExpr::Symbol`.
- `src/parser/decl.rs:1526` — delete `(param : Symbol)` kind parsing and the
  `'Foo` symbol-literal lexing/parsing.
- `src/typechecker/unify.rs:74` (`kind_name`) and `src/typechecker/mod.rs:549`
  (`kind_of`) — remove Symbol kind arms; delete the `Type::Symbol` variant and
  all match arms (e.g. `constraints.rs:73` `Type::Symbol(_)`).
- `src/typechecker/builtins.rs:42` — delete `KNOWN_SYMBOL_TRAIT` registration.
- `src/elaborate/expr.rs` — delete `SymbolIntrinsic` handling.
- `src/codegen/resolve.rs` — delete Symbol-intrinsic lowering.
- Docs: delete `docs/planning/type-symbols.md`.

### Phase 4 — Cleanup & docs
- `docs/roadmap.md`:
  - line ~69: remove the multi-param **fundep** claim (keep multi-param traits).
  - lines ~67-68: keep `deriving` for the built-in set; note Generic/routed
    derives removed.
- Update `docs/trait-dict-passing.md` and `docs/typechecking.md` (fundep
  sections ~344-490) to drop fundep/Generic content.
- Update `AGENTS.md` "Where to start" table if it points at generic docs.
- Add a short docstring near the record-builder feature noting it is the
  HKT-free encoding of "sequence/traverse over a record," replacing the Generic
  derive for projections.
- `cargo build && cargo clippy && cargo test` clean at the end of each phase.

## What userland loses, and the replacement

| Lost capability | Replacement |
| --- | --- |
| `deriving (Generic)` + user-defined derives | Closed set of compiler derives (`src/derive/builtin.rs`); the set stays fixed — no new auto-deriving is planned. Anything beyond it is written by hand in userland libraries |
| Drizzle-style SELECT projections (Kraken) | **Record builders** (`build` keyword) — already implemented |
| Multi-param **fundep** traits (`selection -> row`) | If ever needed: **associated types** (`trait Query { type Row }`) — single-step impl lookup, no fixpoint solver, more comprehensible. Add deliberately with a concrete use case. |

## Risks & verification points

1. **`expand.rs` is shared.** It dispatches both built-in and routed derives.
   Pruning, not deleting. Verify built-in derives (`Show`/`Eq`/`Ord`/`Enum`/
   `Debug`/`Default`) still expand after the routed branch is removed.
2. **Multi-param traits without fundeps.** `ConvertTo a b`,
   `Verbose a where {a: Describe}` must still resolve. Confirm no hidden
   dependence on `improve_pending_fundeps`. Add/keep a test.
3. **`improve_pending_fundeps` call site in field access** (`records.rs:350`).
   Removing it must not regress record field-access disambiguation in normal
   (non-Generic) code. Run the records examples/tests.
4. **`Type::Symbol` / `Kind::Symbol` match arms are wide but shallow** (~46
   `Kind::Symbol`, ~69 `KnownSymbol` refs per earlier survey). Expect many small
   match-arm deletions across phases; compiler errors will guide them.
5. **Serialized type info / fingerprints.** `cli/cache.rs` and `lsp/analysis.rs`
   hash `fundep`; library `.beam` sidecars may embed it. Bump/clear the stdlib
   fingerprint and any cached `_build/` + `~/.saga/cache` after the change.
6. **Prelude breakage.** `prelude.saga` imports `Generic`; removing it must not
   break unrelated prelude consumers. Build a trivial program after Phase 0.
7. **`derive/` shared helpers.** `scope.rs`/`imports.rs`/`type_expr.rs`/
   `helpers.rs` may be partly used by built-in derives. Categorize before
   deleting; prune rather than remove if shared.

## Rough size of the removal

- Generic deriving: ~5,000 LOC in `src/derive/` (Generic-only files) +
  2,174 in `codegen/generic_fold/` + `Generic.saga` + ~900 docs.
- Fundeps: ~250-350 LOC, scattered; the meaningful chunk is the ~200-line
  `improve_pending_fundeps` fixpoint.
- Symbol kind: ~300-400 LOC, wide-but-shallow match arms.

Total: well over **8,000 lines of compiler code + ~1,800 lines of docs**
removed; replacement already in tree (record builders, ~1,300 LOC).

## Rollback

All of this is recoverable from git history and the validated Kraken
spike. Do the removal on a branch; if a load-bearing dependency surfaces
(most likely: a real multi-param-trait resolution that needed improvement, or a
built-in derive that shared Generic helpers), the smallest safe restore is the
specific helper, not the whole subsystem — prefer porting the one needed piece
into the built-in path over reviving `Generic`.

## Decided scope boundaries

- **The built-in derive set is closed.** `Show`/`Debug`/`Eq`/`Ord`/`Enum`/
  `Default` is the whole list; this removal does not add to it and no future
  auto-deriving is planned. Anything more elaborate (serialization, schema
  generation, etc.) is written by hand in a userland library, not generated by
  the compiler. This keeps the "extensibility lives in userland code, not in the
  compiler" line bright — the whole point of the removal is undermined if we
  start re-growing the derive set.
