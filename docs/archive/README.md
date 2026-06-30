# Archived design docs

These documents describe features that were **removed** from the compiler. They
are kept for historical reference only — none of this machinery exists in the
current tree, and the docs are not maintained.

- `generic-deriving.md` — the `Generic` trait, structural `Rep__T`
  representations, and routed/user-extensible derives.
- `user-extensible-derives.md` — the plan for letting userland define new
  `deriving` targets via the `Generic` representation.
- `type-symbols.md` — the type-level Symbol kind (`'Foo` literals,
  `KnownSymbol`, `Proxy`).

All three were taken out together; see
`docs/planning/remove-type-level-trinity.md` for the removal plan and rationale.
The built-in derives (`Show`, `Debug`, `Eq`, `Ord`, `Enum`, `Default`) and
multi-parameter traits were kept.
