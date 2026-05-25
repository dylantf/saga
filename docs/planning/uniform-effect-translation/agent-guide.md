# Agent Guide: Uniform Effect Translation

**Read this in full before doing any implementation work on this rewrite.**

This is the cross-cutting invariants you'll need on every step. The
detailed *what* and *why* live in the planning + spec docs; this is the
*how to not screw it up*.

---

## Load-bearing docs (read in this order)

1. [uniform-effect-translation.md](../uniform-effect-translation.md) —
   architecture, migration strategy, the stage you're working on.
2. [monadic-ir-spec.md](./monadic-ir-spec.md) — IR types.
   Skip if your step doesn't touch `MExpr`.
3. [effect-optimization-spec.md](./effect-optimization-spec.md) —
   rewrites. Skip if your step isn't in `effect_opt/`.
4. [docs/compiler-overview.md](../../compiler-overview.md) — full pipeline
   context.
5. [docs/effect-implementation.md](../../effect-implementation.md) — runtime
   evidence layout. **Unchanged by this rewrite.** Read if you're working
   on the lowerer.

---

## Cross-cutting invariants

### Strict no-imports from frozen files

The new path **must not** import from these:

- `src/codegen/normalize.rs`
- `src/codegen/call_effects.rs`
- `src/codegen/lower/` (except the explicit allowlist below)

If a helper from the old path looks useful, **copy it into the new
module**. Do not import. Coupling makes the cleanup commit harder.

**Allowlist (shared infrastructure, will outlive the old path):**

- `src/codegen/resolve.rs` — backend resolve, used by both
- `src/codegen/lower/evidence.rs` — runtime evidence layout helpers
  (`insert_canonical`, `project_evidence`, `find_evidence`)
- `src/codegen/cerl.rs` — Core Erlang IR and printer
- `src/codegen/runtime_shape.rs` — runtime layout helpers
- `src/codegen/lower/errors.rs` — diagnostics helpers (if used)
- `src/ast.rs` — shared, including `NodeId::fresh`, `Expr::synth`,
  `Expr::rebuild_like`
- `src/typechecker/` — shared (`CheckResult`, `ResolutionResult`, types,
  effect rows)

When in doubt, check the planning doc's "Strict invariant: no imports
from old files" section. If it isn't in the allowlist, don't import it.

### NodeId discipline

Three primitives, all in [src/ast.rs](../../../src/ast.rs):

- `NodeId::fresh()` ([ast.rs:212](../../../src/ast.rs#L212)) — mint a new ID.
- `Expr::synth(span, kind)` ([ast.rs:512](../../../src/ast.rs#L512)) — build a
  new expression with a fresh NodeId. Use for **genuinely new wrapper
  nodes** (a synthetic `let`, a replacement `Var` reference).
- `Expr::rebuild_like(expr, kind)` ([ast.rs:524](../../../src/ast.rs#L524)) —
  build a new expression *preserving the original NodeId*. Use when a
  source expression is just **relocated** (lifted in place by ANF, e.g.).

**Misuse silently drops nodes from `ResolutionMap` lookups in the new
lowerer.** `ResolutionMap` is keyed by source `NodeId`s; if you mint a
fresh one for a relocated source expression, the lowerer can't find its
resolution info.

Rule of thumb:
- Did this expression exist in the source? → `rebuild_like`.
- Did we invent it (wrapper, helper var, synthetic let)? → `synth`.

### Fresh-name generation

New path uses its own generator, **not** `normalize.rs`'s:

```rust
pub(crate) struct FreshNames { counter: u32 }
impl FreshNames {
    pub fn new() -> Self { Self { counter: 0 } }
    pub fn fresh(&mut self, tag: &str) -> String {
        let n = self.counter;
        self.counter += 1;
        format!("__anf_{tag}{n}")
    }
}
```

Prefix `__anf_` is intentionally distinct from old path's `__eff` so
generated names are visually distinguishable in emitted `.core` during
benchmark toggle. Lives in `anf.rs` initially; promote to a shared
location (`src/codegen/monadic/fresh.rs`) if a later step needs its own
generator.

### Effect-ness is a lookup, not a derivation

Never ask "could this be effectful?" at translation/optimization time.
Always look it up:

- Function effect row: `CheckResult.fun_effects[name]` or via
  `ResolutionMap[node_id]` → `ResolvedName.effects`.
- Expression effect row: `CheckResult.type_at_node[node_id]` — the type
  carries the effect row.

The whole point of this rewrite is to eliminate "decide per call site if
it's effectful." If you find yourself writing that logic, stop —
you're reopening the case-set-never-closes problem.

### File-size discipline

Target: any single file over **~800 LOC** must justify why it isn't
split. Split by responsibility, not by line count. The old lowerer
([lower/mod.rs](../../../src/codegen/lower/mod.rs) at ~4100 LOC) is
explicitly what we're not doing.

If your step's output file is approaching the limit, split before
finishing — easier than splitting later.

### Saga language quirks worth remembering

- **No zero-argument functions.** Every function takes at least one
  parameter. Functions with no meaningful input take `Unit`:
  `fun foo : Unit -> Int / foo () = ...`, called as `foo ()`.
  This is intentional, not a gap. Don't add zero-arity special cases.
- **Float literals in tests:** never use `3.14` (clippy warning). Use
  `std::f64::consts::PI` or simple values like `1.5`.
- **`resume` is a distinct keyword and AST node.** Not a function call.
  Pattern-match on `Expr::Resume`.

---

## Phase invariants

The architectural premise is **uniform translation, then optimization**.
Keep these straight:

- **Translator: dumb and uniform.** Emits `Bind` everywhere. Never picks
  CPS vs. non-CPS, never picks `Let` vs. `Bind`, never decides "is this
  pure?" These decisions belong to effect optimization.
- **Effect optimization: smart and safe.** Three rewrites
  (bind-collapse, Bind→Let promotion, direct-call). Identity is a valid
  implementation. Bugs here are perf regressions, never miscompiles.
- **Lowerer: consumer.** Dispatches on `MExpr` variant. `Bind` →
  continuation. `Let` → Erlang let. `Yield` → evidence lookup + apply.
  No "is this site effectful?" introspection.

If you're in the translator and find yourself looking at effect rows,
something's wrong. If you're in effect optimization and find yourself
constructing `Yield`, something's wrong.

---

## When to ask vs. proceed

**Ask the user when:**

- A decision isn't in the planning or spec docs (don't guess and ship).
- A planning-doc instruction contradicts what the codebase actually
  looks like (the doc may be stale; flag it).
- You hit an edge case the spec doesn't cover (e.g. a new AST variant
  added since the spec was written).
- You're about to take a destructive action (delete a file, push, etc.).
- You're tempted to import from a frozen file because "it's just easier."

**Proceed without asking when:**

- The decision is in the docs.
- It's a mechanical follow-on from a decision already made (e.g.
  pattern-matching the rest of an enum after handling some variants).
- The Saga test suite tells you whether you're right.

---

## Verification

Before declaring a step done:

1. `cargo build` — no errors.
2. `cargo clippy` — no warnings introduced.
3. If your step has a test target (e.g. anf.rs gets unit tests), run it.
4. If your step is plumbed into the new path's toggle: flip the toggle,
   compile a small example (`examples/hello_world.saga` or similar),
   compare output with old path. Behavior should match (perf may differ).

For the toggle (see [planning doc](../uniform-effect-translation.md),
"Migration strategy" section): two functions in
[src/codegen/mod.rs](../../../src/codegen/mod.rs) have both old and new
path blocks. Comment one out to flip.

---

## Anti-patterns

These are the failure modes most likely to bite. Avoid them.

- **"I'll just import this one helper from `normalize.rs`."** No.
  Copy it.
- **"This `let` shouldn't change the NodeId, right? `synth` is fine."**
  No. If it's a relocated source expression, `rebuild_like`. If it's a
  new wrapper, `synth`. Don't guess.
- **"The agent guide said `Bind` for effectful and `Let` for pure — I'll
  emit `Let` here in the translator since I can see this is pure."** No.
  Translator emits `Bind` uniformly. Bind→Let is an optimization-stage
  rewrite.
- **"I'll add a small visitor framework so all these passes share
  traversal."** No. Concrete struct, concrete fields, add abstraction
  only when a real second consumer appears.
- **"I'll handle a few extra cases the spec doesn't mention, just in
  case."** No. Stop and ask. Speculative cases bloat the implementation
  and may contradict the design.
- **"This file is at 1200 LOC but I'll split it later."** No. Split
  now, before the structure calcifies.
- **"Pass 3 has a flag that's `Multishot` here, but I can see it's
  actually one-shot. Let me fire the rewrite anyway."** No. False
  one-shot is a miscompile. Trust the conservative tag.

---

## Cleanup awareness

The whole new path will be deleted-and-renamed in the final cleanup
commit ([planning doc](../uniform-effect-translation.md),
"Cleanup" section). Implications:

- Don't write code that depends on the old path's existence.
- Don't write code in old-path files thinking "I'll move it later."
- Module names with `_monadic` suffix (e.g. `lower_monadic`) are
  temporary. They'll become the canonical names at cleanup.

---

## Quick reference

| Concern | Where |
|---|---|
| What stage am I on? | [planning doc](../uniform-effect-translation.md) "Pipeline stages (detailed)" |
| IR types | [monadic-ir-spec.md](./monadic-ir-spec.md) |
| Optimization rewrites | [effect-optimization-spec.md](./effect-optimization-spec.md) |
| Implementation order | [planning doc](../uniform-effect-translation.md) "Implementation phases (module-by-module)" |
| Runtime evidence layout | [docs/effect-implementation.md](../../effect-implementation.md) |
| AST shape | [src/ast.rs](../../../src/ast.rs) |
| Toggle entry points | [src/codegen/mod.rs](../../../src/codegen/mod.rs) — `compile_module_from_result`, `emit_module_with_context` |
| NodeId allocator | [src/ast.rs:208](../../../src/ast.rs#L208) |
| `Expr::synth` / `rebuild_like` | [src/ast.rs:512](../../../src/ast.rs#L512), [:524](../../../src/ast.rs#L524) |
