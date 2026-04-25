# Scope Routing Refactor

## Motivation

The codebase already has a clean two-layer model for name resolution:

- **`scope_map`** — the router. Maps user-visible names (bare, aliased, canonical) to canonical names per the current module's imports.
- **Definition stores** (`self.env`, `self.effects`, `self.trait_state.traits`, `self.handlers`, etc.) — keyed by canonical name, hold the actual semantic payload for every loaded module.

For values and handlers this split is honored: bare lookups go through `scope_map.resolve_*`, and only names visible in the current import scope resolve. Unimported/unexposed names return `None` naturally, like any undefined identifier.

For **effects** and **traits** the split is bypassed. Imports unconditionally dump all effect definitions into `self.effects` and all trait method schemes into `self.env`. Bare-name lookups for effect ops and trait methods then scan those stores directly, ignoring whatever `scope_map` says. The result is that operations and methods leak into bare scope regardless of the `exposing` clause.

The concrete bug that surfaced this:

```saga
import Std.Env (system_env)   # only the handler is exposed, NOT the Env effect
import Std.IO (console, println)

main () = {
  let home = get! "HOME"       # compiles — but shouldn't, `get` belongs to Env
  ...
} with {console, system_env}
```

Renaming the `Env` effect to anything else in the stdlib keeps the program compiling, because the effect's definition is always shoved into `self.effects` on import and the bare-op scan finds `get` regardless of visibility.

## Design Principle

One sentence: **`scope_map` is the only path for bare-name resolution; definition stores are only reached via scope_map-produced canonicals.**

Nothing is "blocked" at lookup time. Names simply aren't in `scope_map` unless they should be. Lookups for names that aren't in scope return `None` just like any other unresolved name.

This matches how `register_qualified` and `scope.values` already work for ordinary value bindings. The refactor is about extending the same pattern to effect ops and trait methods — not inventing a new one.

## Intended Import Semantics

Using Elm/OCaml/Rust-style conventions (already the model for values today):

1. `import Fully.Qualified.Module`
   - Canonical access always: `Fully.Qualified.Module.foo`
   - Last-segment aliased: `Module.foo`, `Module.EffectName.some_op`
   - Bare `some_op`: **not in scope**

2. `import Fully.Qualified.Module as M`
   - Canonical access always works.
   - Aliased: `M.foo`, `M.EffectName.some_op`
   - Bare: not in scope.

3. `import Fully.Qualified.Module (EffectName)`
   - All of the above.
   - Plus bare `EffectName` and bare `EffectName.some_op` (the effect is exposed, so its ops are too).

4. `import Fully.Qualified.Module (some_op)` (exposing an op directly)
   - Design call: do we allow exposing individual ops without the effect? Probably no — ops are namespaced by their effect. Revisit during implementation.

In all cases, `Fully.Qualified.Module.EffectName.some_op` is always reachable as a canonical path if the module is loaded.

Fully qualified canonical paths always resolve because the canonical entry is in the definition store regardless of import form. That's how qualified lookups should work — through canonical name, not through scope.

## What's Wrong Today

### Effects

[check_module.rs:920-934](../../src/typechecker/check_module.rs#L920-L934) unconditionally registers every effect from an imported module into `self.effects`, independent of the `exposing` list. The `is_exposed` helper defined right above is applied to handlers but not to effects.

[effects.rs:422-442](../../src/typechecker/effects.rs#L422-L442) in `lookup_effect_op`, the bare-qualifier branch scans `self.effects` directly. No `scope_map` consultation. Whatever's in the store is reachable.

[effects.rs:198-202](../../src/typechecker/effects.rs#L198-L202) in `effect_for_op`, same pattern — scans the store.

### Trait methods

[check_module.rs:888-905](../../src/typechecker/check_module.rs#L888-L905) unconditionally inserts every trait method into `self.env` under its bare name. A comment at [check_module.rs:1113-1123](../../src/typechecker/check_module.rs#L1113-L1123) explicitly says `traits are always available for impl/where when the module is imported, regardless of exposing clause`. That's an intentional design choice for traits (typeclass ergonomics), but it's the same structural bypass as the effect bug.

Whether traits *should* follow the same gating rule as effects or keep the always-available behavior is a separate design call covered below.

## Refactor

### Scope map extensions

Add op-level visibility to `ScopeMap`:

```rust
pub struct ScopeMap {
    ...
    /// bare op name -> canonical effect names that define that op
    pub effect_ops: HashMap<String, HashSet<String>>,
    ...
}
```

A `HashSet<String>` rather than a single `String` because two effects may define an op with the same name (e.g. `get` on both `Database` and `Cache`). Ambiguity is resolved at lookup time when the set has >1 member.

Populate during:

- **Local effect registration** — when `register_effect_stub` / `register_effect_ops` fires in the current module, insert each op into `scope_map.effect_ops` under its bare name mapped to the local effect's canonical name.
- **Import with exposing** — in `resolve_import`, when an effect name appears in the `exposing` list, register each of its ops. When the effect is *not* in the exposing list, do not.
- **Import without exposing** — do not inject any ops. (Bare `EffectName.op` still works through the existing effect-name routing plus the existing `effects.get(canonical)` definition lookup.)

### Definition store changes

`self.effects` **must** stay fully populated with every imported effect's canonical entry — and not just for qualified lookups. The typechecker reads effect definition metadata by canonical name in several places that have nothing to do with the current module's `exposing` list:

- **Polymorphic effect type params** — [infer.rs:62](../../src/typechecker/infer.rs#L62), [handlers.rs:242](../../src/typechecker/handlers.rs#L242), [check_decl.rs:1787-1789](../../src/typechecker/check_decl.rs#L1787-L1789). Effects like `State s` need `info.type_params` to unify concrete type args flowing through function signatures. A transitive function signature mentioning `State Int` requires reading the effect's definition even if the importer never wrote `State` themselves.
- **Handler registration** — [check_decl.rs:1861](../../src/typechecker/check_decl.rs#L1861). `handler foo for E { ... }` walks the `for` effect names, resolves them to canonical form, and pulls `EffectDefInfo` for arm validation.
- **Codegen arity threading** — [check_module.rs:1394-1397](../../src/typechecker/check_module.rs#L1394-L1397) has an explicit comment documenting this: private effects must stay in `ModuleCodegenInfo.effect_defs` because imported call sites need the runtime op count to thread handler callbacks. The typechecker's `self.effects` is the front-end mirror of that.
- **Effect row unification** — [unify.rs:141-219](../../src/typechecker/unify.rs#L141-L219) is purely structural string matching on canonical names, so it doesn't touch `self.effects` directly. Safe on its own, but the other three sites are enough to require keeping the store populated.

So the refactor is not "drop unexposed effects from `self.effects`." It's "leave `self.effects` alone and layer a separate visibility map on top." The two concerns — definition storage vs. bare-name visibility — need to be genuinely separate.

Codegen already does this split: `lower::effect_defs` (canonical-keyed, fully populated via `ModuleCodegenInfo.effect_defs`) is the definition store, while handler-availability decisions are tracked separately through `scope_map` / resolution metadata. The typechecker should do the same thing for effect ops that codegen already does for effect defs.

For trait methods specifically at [check_module.rs:888-905](../../src/typechecker/check_module.rs#L888-L905), the bare `self.env.insert(method_name, ...)` at line 896 should go away (if the tighter rule is adopted). The resolver already records trait method uses via `ResolutionResult.values` and rewrites identifiers to canonical form — that should be enough.

### Lookup changes

`lookup_effect_op`'s bare branch becomes:

```rust
// No qualifier — consult scope_map.
let candidates = self.scope_map.effect_ops.get(op_name);
match candidates.map(|s| s.len()).unwrap_or(0) {
    0 => Err("undefined effect operation: {op_name}"),
    1 => { ... look up via the single canonical effect ... }
    _ => Err("ambiguous effect operation: {op_name}"),
}
```

No scan of `self.effects`. Ambiguity error uses the same shape as today.

`effect_for_op`'s bare branch follows the same pattern.

The qualified paths stay as they are — they already route through `scope_map.resolve_effect(qualifier) → canonical`, then `self.effects.get(canonical)`. That's the correct shape.

### Traits — design call required

Two coherent positions:

- **Traits follow effects (strict)** — methods only bare-visible when the trait is exposed or locally defined. Consistent with the effects rule. Breaks ergonomics for things like `show`, `==`, `compare` unless the prelude exposes all common traits explicitly (which it largely does already).
- **Traits stay always-available (current)** — document the divergence and move on. Typeclass method names are globally unique by convention, so ambient visibility is less dangerous.

Recommendation: go with strict first and see how bad the test fallout is. The prelude already exposes `Show`, `Eq`, `Ord` explicitly, so most user code should survive unchanged. Back off to always-available if the cost is too high.

If strict: remove the bare `self.env.insert` at [check_module.rs:891-898](../../src/typechecker/check_module.rs#L891-L898) and rely on `scope_map.values` + the resolver's rewrite pass to canonicalize `show x` at use sites.

If always-available: leave traits alone, only fix effects.

## Scope of Work

Not a fundamental architectural change. This finishes a pattern the codebase is already halfway through applying.

### Effects (~1 day)

- Add `effect_ops` to `ScopeMap` + `Default`/`merge` updates.
- Populate during local effect registration in [check_decl.rs:1633](../../src/typechecker/check_decl.rs#L1633).
- Populate during import in [check_module.rs:920](../../src/typechecker/check_module.rs#L920) and [check_module.rs:1135](../../src/typechecker/check_module.rs#L1135), gated on `exposing`.
- Rewrite bare branches of `lookup_effect_op` and `effect_for_op`.
- Fix test fallout. Likely: a handful of tests that rely on unexposed-effect bare-op resolution. Likely fix: expose the effect, or qualify the op.

### Traits (if tightening, ~1-2 days)

- Remove unconditional bare `self.env.insert` for trait methods.
- Verify resolver fully handles trait method identifiers end-to-end (it should — `ResolutionResult.values` already stores these).
- Verify impl-body method checking still works. Methods inside an `impl Show for Foo { show x = ... }` block need to be resolvable inside that scope even if `Show` isn't exposed in the module. May need a scope push specifically for impl bodies.
- Broader test fallout than effects.

### Not changing

- Typechecker pipeline ordering.
- CPS transform / handler lowering structure.
- How `with` attaches handlers.
- Qualified lookup paths.
- `self.effects` population — stays fully populated with canonical entries for every loaded module.

### What did change beyond the original plan (effects implementation)

- **`ResolutionResult` grew a richer effect-call record.** `effect_call_qualifiers: HashMap<NodeId, String>` (qualifier-only) was replaced by `effect_calls: HashMap<NodeId, ResolvedEffectOp>` storing `(effect, op)` pairs. The same change applies to `handler_arms`. This makes the resolver authoritative for effect-call identity instead of forcing inference and codegen to re-derive it.
- **Codegen's `op_to_effect` reverse map was removed.** Lowering now reads the resolver's per-NodeId answers via `current_effect_call_effect` / `handler_arm_effect_for_module`. Removing that global reverse map was the codegen mirror of the typechecker bug the refactor was originally about.
- **Codegen handler-arm matching threads a `source_module`.** `effect_for_handler_arm` and `static_arm_for_effect_op` now take an originating-module argument so imported handlers' arms resolve through the right resolution map.
- **Authoritative-resolver fallout.** A few codegen helpers used to fall back to raw-name lookups in `fun_info` when the resolver had no entry for a node. That fallback caused a silent miscompile on shadowed names (a `let foo = ...` shadowing a top-level effectful `foo` would be silently routed to the top-level fn). The fallback was dropped in `resolved_fun_info` (None arm), `resolved_effects` (None arm), and `is_effectful_call_name` (the `is_effectful(name)` raw lookup).
- **`let_effect_bindings` now stores effects at registration time.** The map used to be populated by re-querying `self.env` after typechecking, which returned stale/wrong entries when a local let-binding shadowed a top-level fun. It is now computed from each binding's actual type at the point `generalize_let_binding` fires.

### Why downstream phases are unaffected

Every downstream consumer of effect metadata reads `self.effects` (or codegen's `lower::effect_defs`) by canonical name. Those canonical names come from the resolver via `ResolutionResult`. The refactor's rule is simple:

- Resolution succeeds → canonical name flows through `ResolutionResult` → every `self.effects.get(canonical)` / `effect_defs.get(canonical)` hits. No behavior change.
- Resolution fails (bare `get!` for an unexposed effect) → the node never gets a resolved qualifier → `lookup_effect_op` returns `Err("undefined effect operation")` → typecheck error. Downstream phases don't run on a rejected program.

So polymorphic type-param reads, handler registration lookups, codegen arity threading, and cross-module effect propagation all keep working. They operate on already-resolved canonical names, not on the bare-name scope we're tightening.

## Status

Effects half is implemented and merged into `scope-routing-refactor`. Traits half is the remaining work.

## Testing Strategy

Unit tests in `src/typechecker/tests.rs`:

- `imported_handler_does_not_expose_private_effect_op_bare` — `import M (handler)` where the effect is not exposed: bare op rejected.
- `exposing_effect_exposes_its_ops_bare` — `import M (E)`: bare ops resolve.
- `imported_effect_op_remains_available_qualified_without_exposing` — `M.E.op` always works.
- `exposed_imported_effect_ops_with_same_name_are_ambiguous` — collision diagnosis.
- `only_exposed_imported_effect_op_is_bare_visible_when_names_collide` — colliding op is unambiguous when only one effect is exposed.
- `effect_ops_cannot_be_exposed_directly` — `import M (op)` is rejected at import time.

Integration test in `tests/codegen_integration.rs`:

- `local_let_shadow_of_top_level_effectful_fn_calls_local_value` — pinned the silent-miscompile bug exposed by removing codegen's raw-name fallbacks.

## Open Questions

- Should trait methods follow the same strict rule? Design call in the Traits section above.
- Does `register_qualified` need an analogous op-level helper, or is op injection handled at a different layer? Probably a dedicated helper, since op visibility is downstream of effect visibility.

## Resolved Questions

- Exposing individual ops (`import M (some_op)`) — **rejected at import time**. Ops come with their effect; this matches Elm/OCaml/Rust conventions and keeps op visibility cleanly downstream of effect visibility.
