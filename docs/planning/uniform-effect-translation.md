# Uniform Effect Translation

Status: **phase 1 slow path complete; new path active; phase 2 effect
optimization in progress.**

## Status

Tick boxes as steps land. Each box → one focused agent session.

### Strategic phase 1 — slow uniform path correct end-to-end

- [x] **1.** `src/codegen/handler_analysis.rs` — see stage 8.5
- [x] **2.** `src/codegen/anf.rs` + `FreshNames` — see stage 9
- [x] **3.** `src/codegen/monadic/ir.rs` — see [monadic-ir-spec.md](./uniform-effect-translation/monadic-ir-spec.md)
- [x] **4.** `src/codegen/monadic/translate.rs` — see stage 10
- [x] **5.** `src/codegen/monadic/print.rs` — debug pretty-printer
- [x] **6.** `src/codegen/monadic/effect_opt/` as identity — see stage 11
- [x] **7.** `src/codegen/lower_monadic/` — see stage 12 (sub-tasks 7a–7g; see "Implementation phases")
  - [x] **7a.** Function/decl scaffolding (stubbed bodies)
  - [x] **7b.** Atom → CExpr
  - [x] **7c.** MExpr structural variants (Pure, Bind, Let, Case, If, App) + DictConstructor tuple synthesis
  - [x] **7d.** Effect machinery (Yield via evidence lookup, With site via insert_canonical)
  - [x] **7e.** Handler emission (MHandler::Static arms + return clause; MHandler::Dynamic passthrough)
  - [x] **7f.** ~~BEAM-native effect bodies~~ — **dropped.** Slow path uses uniform find_evidence; module-init bootstrap installs default native handlers (folded into 7g). Direct-native fast-path deferred to phase 2+ as an optimizer rewrite.
  - **7g.** Edge cases (split into two parts):
    - [x] **7g.A.** Expression-level edge cases: records, bitstrings, receive, dict-method-access, foreign calls, BinOp/UnaryMinus, arm guards
    - [x] **7g.B.** Patterns, decls, bootstrap: Pat::Or + surface-syntax patterns, `@external` wrappers, module-init bootstrap for BEAM-native default handlers, `public` flag resolution
- [x] **8.** Toggle wiring in `src/codegen/mod.rs` — both entry points

#### Phase 1 parity blockers

These were the correctness/parity failures that blocked the slow uniform path
from becoming the phase-2 optimization oracle. They are now resolved; keep this
list as the historical checklist for why phase 2 is unblocked. See
[`review-notes.md`](./uniform-effect-translation/review-notes.md) for the
pass-by-pass investigation notes.

- [x] **8a. Native/bridge higher-order callback adapters.**
  General `@external` wrappers now adapt function-typed parameters from
  uniform CPS shape to native Erlang callback arity. Saturated external calls
  with callback-shaped arguments route through the wrapper instead of handing a
  raw Saga closure to a BIF/bridge function.

- [x] **8b. Dynamic handler values with return clauses.**
  Runtime handler-value tuples now carry return-clause behavior, and dynamic
  handler installation handles single-effect and multi-effect values.

- [x] **8c. Eta-reduced effect operation callbacks.**
  Effect operation references used as callback values are eta-expanded into the
  expected uniform function shape during monadic translation.

- [x] **8d. Zero-arity value functions used as returned function values.**
  Nullary Saga vals/functions are materialized through the uniform
  `(Evidence, ReturnK)` path before applying any returned function value.

- [x] **8e. Anonymous record field metadata with underscores.**
  Anonymous record field order is structural metadata (`anon_fields`), not
  decoded from runtime tags; anonymous runtime tags are injective over field
  sets.

- [x] **8f. Nested/same-effect dynamic handler semantics.**
  Dynamic handler metadata, same-effect shadowing, and conditional handler
  selection have parity coverage in the effect property and e2e suites.

- [x] **8g. Abort marker crossing resume.**
  Handler result delimiters now route abort and marked value-result tuples by
  marker, re-installing the delimiter stack needed for resumed computations.

- [x] **8h. Effectful lambda-head evaluation order/value flow.**
  `BindMode::ValuePosition` distinguishes ANF-introduced value-position
  evaluation from source sequencing, preserving effectful function-position
  value flow.

- [x] **8i. Stale `InlineVal` resolution reaching the new backend.**
  `@inline val` was removed as a premature optimization. `InlineVal` metadata
  remains only as unreachable old-path residue until old-path deletion.

**Milestone:** complete. The new slow path passes the behavioral test suites
and is the oracle for strategic phase 2. Old Core-shape string assertions that
only describe the deleted selective-CPS implementation may stay ignored or be
rewritten independently.

### Strategic phase 2 — effect optimization rewrites

- [x] **9.** `effect_opt::bind_collapse` — see [effect-optimization-spec.md §1](./uniform-effect-translation/effect-optimization-spec.md)
- [x] **10.** `effect_opt::bind_to_let` — see [effect-optimization-spec.md §2](./uniform-effect-translation/effect-optimization-spec.md)
- [x] **11.** `effect_opt::direct_call` — see [effect-optimization-spec.md §3](./uniform-effect-translation/effect-optimization-spec.md)

**Milestone:** new path performance matches or exceeds old path on the
test suite; sanity invariant (zero `Yield`/`Pure`/continuation allocations
in pure-or-tail-resumptive functions) holds.

**Current hardening track:** acceptance is green and the current abstraction
cleanup batch is complete. Completed cleanup has centralized marked-control
helpers, callback boundary helpers, `finally` sequencing, result-delimiter arm
construction, and static native bootstrap metadata plus Ref/Vec store-specific
builders. Further cleanup should stay opportunistic unless it is promoted to a
separate semantic task.

**Latest semantic track:** native direct-call specialization milestone 2 is
implemented; see
[native-direct-call-specialization.md](./uniform-effect-translation/native-direct-call-specialization.md).
It rewrites simple first-order actor/timer native yields plus `beam_ref`
`new`/`get`/`set` to direct calls, and keeps callback-heavy or backend-specific
native handlers on the slow evidence path.

**Measurement hook:** `saga inspect <file> --stage monadic-stats` prints
pre/post optimizer structural counts for `Yield`, `Bind`, `Let`,
`ForeignCall`, handlers, arms, and related monadic IR nodes, plus per-op
`Yield` and per-target `ForeignCall` breakdowns. Use this before choosing the
next optimizer milestone.

**Latest optimizer milestone:** interprocedural handler specialization
milestone 1 is implemented; see
[interprocedural-handler-specialization.md](./uniform-effect-translation/interprocedural-handler-specialization.md).
It performs conservative same-module helper inlining under a known handler
stack for single-clause, single-yield helpers. Function-variant generation is
deliberately deferred.

### Cleanup (single mechanical commit)

- [ ] Delete old path; rename `lower_monadic/` → `lower/`. See
      [Cleanup](#cleanup) section for the full checklist.

## Required reading before working on this

**Agents implementing any step: start with
[agent-guide.md](./uniform-effect-translation/agent-guide.md).** It
distills cross-cutting invariants (no-imports rules, NodeId discipline,
fresh-name convention, phase invariants, anti-patterns) that bite when
forgotten.

For anyone (human or agent) implementing any stage of this rewrite:

1. **This document, top to bottom.** Architecture and migration strategy are
   load-bearing; skipping them produces wrong work.
2. [docs/compiler-overview.md](../compiler-overview.md) — the current pipeline
   end-to-end. Establishes the shape the new pipeline plugs into.
3. [docs/effect-implementation.md](../effect-implementation.md) — the runtime
   evidence layout (`{EffectAtom, OpTuple}`, canonical ordering,
   `insert_canonical` / `project_evidence` / `find_evidence`). **This is
   unchanged by the rewrite** and must be preserved exactly.
4. [src/ast.rs](../../src/ast.rs) — `Expr`, `Decl`, `Handler`, `HandlerArm`
   types. The new IR mirrors a subset of these.
5. [src/codegen/lower/evidence.rs](../../src/codegen/lower/evidence.rs) —
   shared with the new lowerer. Read to know what helpers exist.

Sibling planning docs (older, partially superseded by this one):
[evidence-passing.md](./evidence-passing.md),
[effectful-call-detection.md](./effectful-call-detection.md),
[composite-cps-chaining.md](./composite-cps-chaining.md). They cover the same
runtime evidence layout but predate the uniform-translation decision; treat
their guidance on _whether_ to CPS-transform a given site as obsolete.

---

## Motivation

Today's lowerer does **selective CPS**: it decides per call site whether the
site needs evidence + return-continuation arguments, based on a
shape-enumerating pre-pass (`CallEffectMap` in
[src/codegen/call_effects.rs](../../src/codegen/call_effects.rs)). When the
populator fails to recognize a call shape (novel higher-order pattern,
polymorphic dispatch, etc.), the lowerer emits a call without evidence/K and
we get a **runtime arity mismatch** — a miscompile discovered late and only
by hitting it.

Correctness today depends on completeness of shape recognition, and the case
set never closes. Each new language feature reopens it.

## Target

Two distinct mechanisms, applied uniformly, with optimization as a separate
correctness-safe pass:

1. **Evidence passing (always on, cheap).** Every function takes an evidence
   vector. `perform` looks up its handler by indexing the vector. `with`
   extends it. This is just a parameter — not CPS.

2. **Monadic translation (uniform, then optimized).** Every sequencing point
   becomes a monadic bind over `Pure | Yield`. effect optimization collapses
   `bind(Pure(v), k)` to `k(v)` and rewrites tail-resumptive `perform` to a
   direct call into the handler.

The slow path is correct by construction. The optimizer can only make code
faster, never wrong. New features cannot reopen correctness — they're more
code translated uniformly.

## Non-goals

- **Changing the runtime evidence layout.** The tagged tuple format
  (`{EffectAtom, OpTuple}`, canonical ordering, `insert_canonical` /
  `project_evidence` / `find_evidence`) stays as documented in
  [docs/effect-implementation.md](../effect-implementation.md).
- **Changing the surface language.** No new keywords, no new effect syntax.
- **Touching the typechecker.** Effect-row inference, absorption, and row
  polymorphism stay as-is. The new work lives between elaborate and lower.

## Cross-cutting principles

- **File size discipline.** Several existing codegen files are oversized
  ([lower/mod.rs](../../src/codegen/lower/mod.rs) at ~4100 LOC,
  [lower/exprs.rs](../../src/codegen/lower/exprs.rs) at ~2050,
  [lower/effects.rs](../../src/codegen/lower/effects.rs) at ~1950).
  The lowerer refactor is the natural opportunity to break these down. New
  modules introduced by this rewrite (monadic IR, translation, effect optimization,
  handler analysis) should be split by responsibility from the start, not
  allowed to grow into multi-thousand-line files. Rough target: any single
  file over ~800 LOC should justify why it isn't split.

## Migration strategy

**Parallel paths in the same tree, selected by comment-toggle at two entry
points.** No cargo feature, no runtime flag, no `const`. The pipeline is
invoked from exactly two functions in
[src/codegen/mod.rs](../../src/codegen/mod.rs):

- `compile_module_from_result` (used by `build_project`)
- `emit_module_with_context` (used by final emit)

Each function has both paths inline; you comment out one block to flip
between them. Both entry points need toggles.

**`compile_module_from_result`** (per-module compile, called during
`build_project` to populate `CompiledModule` for cross-module use):

```rust
let elaborated = elaborate::elaborate_module(program, mod_result, module_name);

// === OLD PATH ===
let normalized = normalize::normalize_effects(&elaborated);
let resolution = resolve::resolve_names(module_name, &normalized, ...);
let stored = normalized;

// === NEW PATH ===
// Skip normalize entirely — anf runs at emit time.
// let resolution = resolve::resolve_names(module_name, &elaborated, ...);
// let stored = elaborated;

Some(CompiledModule {
    elaborated: stored,
    resolution,
    ...
    call_effects: CallEffectMap::new(),   // unused by new path; populated by old lowerer only
})
```

**`emit_module_with_context`** (final emit):

```rust
// === OLD PATH ===
let program = normalize::normalize_effects(program);
let resolution_map = resolve::resolve_names(...);
let cmod = lower::Lowerer::new(...).lower_module(module_name, &program);

// === NEW PATH ===
// let resolution_map = resolve::resolve_names(...);                // on raw elaborated
// let effect_info = build_effect_info(check_result, ...);          // narrowed view
// let handler_info = handler_analysis::analyze(program);
// let anf = anf::normalize(program.clone());
// let monadic = monadic::translate(&anf, &resolution_map, &effect_info);
// let optimized = monadic::effect_opt::run(monadic, &handler_info, &effect_info);
// let cmod = lower_monadic::Lowerer::new(...).lower_module(module_name, &optimized);

cerl::print_module(&cmod)
```

**`CompiledModule` storage (Option A, committed):** new path stores the
**raw elaborated AST** in `CompiledModule.elaborated` (no normalize pass).
ANF + translation + optimization run fresh inside `emit_module_with_context`
per module. The lowerer only reads `codegen_info`, `resolution`, and
`front_resolution` from other modules' `CompiledModule` — never expression
bodies — so no `MProgram` needs to be cached cross-module. This keeps
`CompiledModule` shape unchanged (no new fields), at the cost of
recomputing ANF/translate/optimize on each emit. If profiling later shows
this matters, caching `MProgram` per module is a follow-up; not now.

### Why this works

- **Old path stays frozen.** We do not edit
  [normalize.rs](../../src/codegen/normalize.rs),
  [call_effects.rs](../../src/codegen/call_effects.rs), or
  [lower/](../../src/codegen/lower/). Maintenance cost on the old path is
  ~zero.
- **New code lives in parallel modules**, not edits to existing ones (see
  file layout below).
- **No type coupling.** `lower::Lowerer` and `lower_monadic::Lowerer` are
  independent types sharing no trait. Both produce `CModule`; the toggle
  decides which is instantiated. `cerl::print_module` is shared.
- **`CompiledModule` needs no new fields.** New path stores raw
  elaborated AST (skipping normalize); ANF, translation, and optimization
  run fresh inside `emit_module_with_context`. No cross-module `MProgram`
  caching needed — see "Migration strategy" entry points for details.
- **Shared infrastructure stays shared:**
  [resolve.rs](../../src/codegen/resolve.rs) (runs in both paths),
  [lower/evidence.rs](../../src/codegen/lower/evidence.rs) (runtime evidence
  layout helpers — new lowerer can call them directly).

### Strict invariant: no imports from old files into new files

The new modules (`anf.rs`, `handler_analysis.rs`, `monadic/`,
`lower_monadic/`) **must not** import from `normalize.rs`, `call_effects.rs`,
or `lower/` (except for the explicitly shared modules above:
`resolve.rs`, `lower/evidence.rs`, and obviously `cerl.rs`). The new path is
copy-and-add only.

Rationale: anything the new path inherits from old code is a coupling that
makes the eventual cleanup commit harder. If a helper from the old path is
genuinely worth reusing, copy it into the new module and let the original
die with the old path.

Explicitly allowed cross-imports (shared, will outlive the old path):

- `src/codegen/resolve.rs` — backend resolve, used by both
- `src/codegen/lower/evidence.rs` — runtime evidence layout helpers
- `src/codegen/cerl.rs` — Core Erlang IR and printer
- `src/codegen/runtime_shape.rs` — runtime layout helpers
- `src/codegen/lower/errors.rs` — diagnostics helpers (if still useful)

### Benchmark workflow

Flip the toggle, `cargo build --release`, run the same test or example
through both paths, compare emitted `.core` size, BEAM runtime, allocation
counts. The new path's "skip effect optimization" debug switch gives a third comparison
point (slow uniform vs. optimized uniform vs. old selective-CPS).

### Cleanup

Once the new path is reliable across the full test suite and benchmark wins
are confirmed, a single mechanical commit performs the migration.

**Files / directories to delete:**

- `src/codegen/normalize.rs` — partial-ANF pass; superseded by `anf.rs`.
- `src/codegen/call_effects.rs` — per-site CPS decision; no analogue in
  the new path (case set is closed by uniform translation).
- `src/codegen/lower/` — entire directory, including:
  - `lower/mod.rs` (~4100 LOC) — old lowerer
  - `lower/exprs.rs` (~2050) — old expression lowering
  - `lower/effects.rs` (~1950) — selective-CPS emission, `lower_effect_call`,
    `lower_with`, `build_op_handler_fun`, etc.
  - `lower/pats.rs`, `lower/builtins.rs`, `lower/beam_interop.rs`,
    `lower/init.rs`, `lower/util.rs` — all replaced by their equivalents
    in `lower_monadic/`.
- **Keep, move to new location:**
  - `lower/evidence.rs` — shared with new lowerer during migration; on
    cleanup, moves to `src/codegen/evidence.rs` (or stays under the renamed
    `lower/` per step below).
  - `lower/errors.rs` — diagnostics helpers; either moves alongside
    `evidence.rs` or stays under renamed `lower/`.

**Fields / methods to remove:**

- `CompiledModule::call_effects` ([src/codegen/mod.rs:27](../../src/codegen/mod.rs#L27))
  and the `set_compiled_call_effects` writeback — both belong to the old
  call-effects pre-pass.

**Entry-point edits ([src/codegen/mod.rs](../../src/codegen/mod.rs)):**

1. Delete the `// === OLD PATH ===` blocks from `compile_module_from_result`
   and `emit_module_with_context`. Uncomment the `// === NEW PATH ===`
   blocks (they become the only path).
2. Remove the `pub mod normalize;` and `pub mod call_effects;` declarations.
3. Remove `pub mod lower;` (or rename per step 4).

**Module rename:**

4. Rename `src/codegen/lower_monadic/` → `src/codegen/lower/`. Update the
   `pub mod` declaration and all `lower_monadic::` imports in the new path's
   files to `lower::`.

**Test fallout:**

5. Any tests that import from frozen paths
   (`crate::codegen::normalize`, `crate::codegen::call_effects`,
   `crate::codegen::lower::Lowerer` with old-shape arguments) — delete or
   migrate to the new lowerer.

**Sibling planning docs** ([evidence-passing.md](./evidence-passing.md),
[effectful-call-detection.md](./effectful-call-detection.md),
[composite-cps-chaining.md](./composite-cps-chaining.md)) — review and
update or delete. Their guidance on _whether_ to CPS-transform is obsolete
under uniform translation; their notes on runtime evidence layout may
still be relevant and can be folded into
[docs/effect-implementation.md](../effect-implementation.md).

One commit, mechanical. After this commit, the only remaining trace of
the old path is in git history.

## Pipeline shape (target)

```
resolve → typecheck → elaborate
  → backend resolve            (moved up — see "Backend resolve placement" below)
  → ANF / let-normalize        (new — anf.rs)
  → monadic translation        (new — AST → MExpr)
  → effect optimization        (new — bind-collapse, Bind→Let promotion, tail-resumptive direct-call)
  → lower                      (new lower_monadic/ — consumes MExpr)
  → emit Core Erlang
```

Compare to today:

```
resolve → typecheck → elaborate
  → normalize (effect-arg ANF only)
  → backend resolve + call_effects pre-pass
  → lower (selective CPS, conditional per call site)
  → emit Core Erlang
```

### Backend resolve placement

[src/codegen/resolve.rs](../../src/codegen/resolve.rs) moves from
mid-pipeline (currently after normalize, alongside `call_effects`) to
**immediately after elaborate**. With `call_effects.rs` deleted, the
artificial "backend prep" bundling has no reason to exist.

Why this works:

- **Elaborate is the last pass that changes callable identity or arity**
  (dictionary parameters added). Backend resolve must run after it; everything
  later only rewrites _sequencing_, not callables.
- **It walks ordinary source AST shape** (`resolve_program` /
  `resolve_decl` / `resolve_expr` at
  [src/codegen/resolve.rs:454](../../src/codegen/resolve.rs#L454)). Running it
  before any rewriting means it sees the cleanest representation — no
  `Pure`/`Yield`/`Bind` wrappers to peek through.
- **Its output is `NodeId`-keyed and immutable downstream.** ANF preserves
  `NodeId`s, monadic translation preserves them on the inner call/var nodes,
  effect optimization doesn't invent new callables — so the `ResolutionMap` computed once
  at the top stays valid through every later pass.
- **`ConstructorAtoms` has no IR dependency** — it's a `name → atom` table.
  Building it early is strictly fine.

This also lets the new IR passes (ANF, monadic, effect optimization) consume a complete
`ResolutionMap` as read-only input. Useful for, e.g., effect optimization's
tail-resumptive direct-call rewrite asking "is this `perform`'s handler
statically resolvable?"

Synthesized nodes introduced by effect optimization (inlined handler-clause bodies,
generated `Pure` wrappers) do **not** go through `ResolutionMap`. They're
emitted as direct `apply`s on closures the lowerer already has in hand.
`ResolutionMap` remains a source-`NodeId`-only structure.

## Current state survey (where things live today)

Per [docs/compiler-overview.md](../compiler-overview.md) and
[docs/effect-implementation.md](../effect-implementation.md):

| Concern                     | Current location                                                                                  | Disposition                                                                               |
| --------------------------- | ------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------- |
| Effect-row inference        | `src/typechecker/`                                                                                | unchanged                                                                                 |
| Evidence vector format      | runtime + `lower/evidence.rs`                                                                     | unchanged (shared with new lowerer)                                                       |
| `with` ⇒ `insert_canonical` | `lower/effects.rs::lower_with`                                                                    | helper reused via `lower/evidence.rs`; emission reimplemented in new lowerer              |
| Partial ANF (effect args)   | `src/codegen/normalize.rs` (997 LOC)                                                              | frozen; new `anf.rs` does general ANF; normalize.rs deleted at cleanup                    |
| Per-site CPS decision       | `src/codegen/call_effects.rs` (1086 LOC)                                                          | frozen; new path doesn't have an analogue; deleted at cleanup                             |
| Selective CPS emission      | `src/codegen/lower/effects.rs` (1952 LOC), `lower/mod.rs` (4111 LOC), `lower/exprs.rs` (2056 LOC) | frozen; new `lower_monadic/` is a fresh implementation; old `lower/` deleted at cleanup   |
| Handler arms / `resume`     | `lower/effects.rs::build_op_handler_fun`                                                          | reimplemented in new lowerer; new `handler_analysis.rs` adds `one_shot`/`tail_resumptive` |

## Pipeline stages (detailed)

Per-stage reference. Stages marked **unchanged** are listed for completeness
so the full pipeline is visible in one place; their detail lives in their
respective source docs.

### 1. Lex

- **What:** tokenize source into a flat token stream with spans.
- **Inputs:** `.saga` source text.
- **Outputs:** `Vec<Token>`.
- **Files:** [src/lexer.rs](../../src/lexer.rs).
- **Disposition:** unchanged.

### 2. Parse

- **What:** hand-written Pratt parser builds a nested `Expr` AST as
  `Vec<Decl>`. Every node gets a stable `NodeId` at creation.
- **Inputs:** token stream.
- **Outputs:** `Program = Vec<Decl>`.
- **Files:** [src/parser/](../../src/parser/) (`mod.rs`, `decl.rs`, `expr.rs`,
  `pat.rs`), [src/ast.rs](../../src/ast.rs).
- **Disposition:** unchanged.

### 3. Derive expansion

- **What:** synthesize trait `impl` declarations from `deriving (Show, Debug,
Eq, Ord, Enum)` clauses.
- **Inputs:** `Program`.
- **Outputs:** `Program` with synthesized `ImplDef`s appended.
- **Files:** [src/derive.rs](../../src/derive.rs).
- **Disposition:** unchanged.

### 4. Desugar

- **What:** rewrite surface sugar (pipes `|>`, composition `>>`, list literals,
  string interpolation, comprehensions, `with {a,b,c}` → nested `with`) into
  core AST forms.
- **Inputs:** `Program`.
- **Outputs:** `Program` (no sugar).
- **Files:** [src/desugar.rs](../../src/desugar.rs).
- **Disposition:** unchanged.

### 5. Name resolution

- **What:** process imports, build global scope, record `NodeId → semantic
identity` into `ResolutionResult`. AST stays source-shaped.
- **Inputs:** `Program`.
- **Outputs:** `ResolutionResult` (consumed by typecheck).
- **Files:** [src/typechecker/resolve.rs](../../src/typechecker/resolve.rs).
- **Disposition:** unchanged. See [docs/name-resolution.md](../name-resolution.md).

### 6. Typecheck

- **What:** HM-style inference returning `(Type, EffectRow)` per expression,
  with trait constraints, effect-row unification/absorption, handler effect
  subtraction, exhaustiveness checking. Effects already flow as a return
  value, not a side-channel.
- **Inputs:** `Program`, `ResolutionResult`.
- **Outputs:** `CheckResult` — types per `NodeId`, traits, effects, handlers,
  `fun_effects`, `let_effect_bindings`, per-module codegen metadata.
- **Files:** [src/typechecker/](../../src/typechecker/) (~15 files).
- **Disposition:** unchanged. The target design depends on what this phase
  already produces (resolved effect rows, per-node types).

### 7. Elaborate

- **What:** rewrite trait method calls into explicit dictionary passing:
  `ImplDef` → `DictConstructor`, trait calls →
  `DictMethodAccess`/`DictRef`, `@external` calls → `ForeignCall`,
  `where`-clause functions gain extra dictionary parameters. **Does not touch
  effects.**
- **Inputs:** `Program`, `CheckResult`.
- **Outputs:** `Program` (same AST shape, dictionary-passing made explicit).
- **Files:** [src/elaborate.rs](../../src/elaborate.rs).
- **Disposition:** unchanged. This is the last pass that changes callable
  identity / arity — everything after only rewrites sequencing. The new IR
  passes are inserted **after** this stage.

### 8. Backend resolve **(moved up)**

- **What:** build `ConstructorAtoms` (constructor → mangled Erlang atom) and
  `ResolutionMap: NodeId → ResolvedName` (callable identity, Erlang
  module/function, arity, effects).
- **Inputs:** elaborated `Program`, front-end `ResolutionResult`, module
  codegen metadata.
- **Outputs:** `ConstructorAtoms`, `ResolutionMap`.
- **Files:** [src/codegen/resolve.rs](../../src/codegen/resolve.rs).
- **Disposition:** **unchanged code, new position.** Moves from after
  normalize to immediately after elaborate. See "Backend resolve placement"
  above for rationale.
- **Invariants:**
  - Keyed only by source `NodeId`s. Synthesized nodes from later passes do
    **not** appear in the map.
  - Output is read-only / immutable for all downstream passes.

### 8.5. Handler analysis **(new)**

- **What:** classify each handler-arm body by `resume` usage so effect optimization knows
  which sites are eligible for which rewrites. Purely syntactic local walk;
  no type information needed.
- **Inputs:** elaborated `Program`.
- **Outputs:** `HandlerAnalysis` struct:

  ```rust
  pub struct HandlerAnalysis {
      pub resumption: HashMap<NodeId, ResumptionKind>,  // handler-arm classification
      pub catalog:    HashMap<NodeId, HandlerMeta>,     // arm → (effect, op, parent handler, ...)
  }

  pub enum ResumptionKind {
      TailResumptive,  // every tail position is `resume`, no other uses
                       // → eligible for direct-call rewrite
      OneShot,         // `resume` only in tail position, not in loops, not captured
                       // → eligible for bind-collapse across the resume
      Multishot,       // anything else — assume worst, full machinery
  }
  ```

- **Files:** new module — `src/codegen/handler_analysis.rs`.
- **Disposition:** **new.**
- **Why a dedicated pass (not piggybacked):**
  - **Not in typecheck.** The flags are a backend concern (optimizer
    eligibility); `CheckResult` shouldn't carry them.
  - **Not in elaborate.** Elaborate's job is trait dictionary passing. Adding
    handler analysis muddles the job description.
  - **Not lazily in effect optimization.** Lazy computation either re-walks per `Yield`
    (redundant) or builds a lazy cache (more state). A pre-pass is simpler
    and cheap — only handler-arm bodies need the inner analysis; the outer
    walk to find arms is small.
  - **Not post-monadic-translation.** `Resume` would be buried inside `Bind`
    chains; "tail position" becomes harder to define. The AST form is the
    clean shape for the syntactic rules.
- **Generality without over-engineering.** The struct has room for adjacent
  metadata (handler catalog), but we only collect fields with a named
  consumer. Do not add a visitor framework or pluggable-pass machinery.
- **Tail-position recursion shape:** recurse into `if`-branches, `case`-arms,
  let-bodies for tail-position determination; **do not** recurse into lambda
  bodies (those are inner computations, not tail positions of the outer arm).
  Same recursion shape as exhaustiveness checking.

### 9. ANF / let-normalize **(new module `anf.rs`)**

- **What:** flatten the expression tree into A-normal form so every
  continuation is syntactically the tail of a let-sequence. This is what
  makes the monadic translation mechanical (`let x = e in body` →
  `bind(e, λx. body)`, no conditional rule).
- **Inputs:** elaborated `Program`.
- **Outputs:** `Program` in A-normal form.
- **Files:** new module — `src/codegen/anf.rs`. Do **not** extend the
  existing [src/codegen/normalize.rs](../../src/codegen/normalize.rs); that
  file belongs to the old path and stays frozen until cleanup.
- **Disposition:** **new.** `normalize.rs` is partial ANF for effect-arg
  positions only; `anf.rs` does the general transform. The old normalize
  pass is not a usable starting point — different invariants, different
  output shape — so this is a fresh implementation, not a port.
- **Granularity: full ANF, atoms stay atomic.** Every non-atomic subexpression
  gets bound to a `let`. _Atomic_ expressions — variables, literals, and
  constructors whose args are all atomic — stay in place; we don't introduce
  `let x = 5 in body`. This is the conventional ANF atom/complex distinction,
  not selective-by-effect. We explicitly reject selective-by-effect ANF: it
  would require asking "could this be effectful?" at every node, which is
  exactly the case-set-never-closes question the rewrite exists to eliminate.
  The "extra let-bindings on pure code" cost is paid for here and recovered
  by effect optimization's `bind(Pure(v), k) → k(v)` collapse.
- **"Every position" means every position, not just continuation positions.**
  Function-call arguments, field-access targets, case scrutinees, if
  conditions, operator operands, non-atomic constructor args — all get lifted
  if non-atomic. Examples:

  ```
  f(g(x), h(y))               →  let a = g(x) in
                                 let b = h(y) in
                                 f(a, b)

  (compute()).field           →  let r = compute() in r.field

  case compute() of ...       →  let s = compute() in case s of ...

  if compute() then a else b  →  let c = compute() in if c then a else b

  Some(compute())             →  let r = compute() in Some(r)
  ```

- **ANF is per-computation-context. It does not cross lambda / branch / arm
  boundaries.** A lambda is _atomic at its construction site_ (it's a closure
  value), but its body is a separate computation, ANF'd recursively in its
  own context. Same for `case` arms, `if` branches, handler-arm bodies, and
  `with`-block bodies — each is its own ANF context. We never lift a complex
  expression _out_ of a lambda body into the surrounding scope; that would
  change evaluation semantics (the inner expression must run when the lambda
  is called, not when it's constructed).

  ```
  let f = fun x -> g(h(x))
  in f(compute())

  →

  let f = fun x ->                  -- lambda atomic at construction
             let r = h(x) in        -- body ANF'd in its own context
             g(r)
  in let arg = compute() in         -- outer context ANF'd separately
     f(arg)
  ```

- **`NodeId` preservation:** lifted subexpressions retain their original
  `NodeId` (use `Expr::rebuild_like` from
  [src/ast.rs:524](../../src/ast.rs#L524)); synthetic `let` binders and
  generated `Var` references get fresh IDs via `NodeId::fresh()` /
  `Expr::synth` (both at [src/ast.rs:212](../../src/ast.rs#L212),
  [src/ast.rs:512](../../src/ast.rs#L512)). The `NodeId` allocator is a
  process-wide static `AtomicU32` and is shared infrastructure — the new
  path reuses it directly without crossing the no-imports boundary.
- **Fresh-name generator:** new `FreshNames` struct local to `anf.rs`:

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

  Prefix `__anf_` is distinct from old path's `__eff` so generated names are
  visually distinguishable in emitted `.core` files during benchmark toggle.
  Promote to a shared module (e.g. `src/codegen/monadic/fresh.rs`) if effect optimization
  or `lower_monadic/` need their own fresh names.

- **`Expr::rebuild_like` vs. `Expr::synth` is load-bearing.** `ResolutionMap`
  is keyed by source `NodeId`s. ANF must use `rebuild_like` when a source
  expression is just relocated (lifted in place); use `synth` only for
  genuinely new wrapper nodes (the `let` itself, replacement `Var`
  references). Misusing `synth` on a relocated source expression silently
  drops it from `ResolutionMap` lookups in the new lowerer.

### 10. Monadic translation **(new)**

- **What:** translate the ANF'd `Program` into a monadic IR (`MExpr`) where
  every sequencing point is a `Bind`, every value-returning subterm is
  `Pure(atom)`, and every `perform` is `Yield { op, args, source }`. Uniform
  — no selective CPS decision. The translator emits `Bind` everywhere; the
  effect optimization stage rewrites pure binders to `Let`.
- **Inputs:** ANF `Program`, `ResolutionMap` (read-only).
- **Outputs:** monadic IR program (`MProgram` — selectively-parallel decl
  types; see spec doc).
- **Files:** new module tree:
  ```
  src/codegen/monadic/
  ├── ir.rs         — MExpr, Atom, MArm, MHandler, MDecl, EffectOpRef
  ├── translate.rs  — AST → MExpr translation
  ├── print.rs      — debug pretty-printer
  └── effect_opt/   — see stage 11
  ```
- **Disposition:** **new.** No analogue in the current codebase.
- **Concrete IR spec:** **see
  [monadic-ir-spec.md](./uniform-effect-translation/monadic-ir-spec.md)** for full Rust type
  definitions, the excluded-variants table, and stage entry-function
  signatures.
- **Key design decisions (resolved):**
  - **Separate IR module**, not inline `Expr` variants. Phase invariants
    enforced at the type level, not by convention.
  - **`Atom` vs. `MExpr` split** lifts the ANF invariant into the type
    system. Where AST said "any expression goes here," `MExpr` says "`Atom`
    only" at sub-positions — non-atomic in those positions is a compile
    error.
  - **Both `Bind` and `Let` are variants.** `Bind` is monadic sequencing
    (value may yield). `Let` is a pure binder (value provably never
    yields). The translator emits `Bind` uniformly; effect optimization
    promotes to `Let` where pure.
  - **`Bind` carries a `BindMode`.** Source/block sequencing uses
    `Sequence`: the bound computation's continuation is the rest of the
    program. ANF-introduced value-position temporaries use `ValuePosition`:
    the bound computation is delimited to produce a value for a surrounding
    expression before that expression runs. This preserves direct-style
    argument evaluation for value-producing `resume` while still bubbling
    abort tuples to the enclosing handler delimiter. The lowerer dispatches
    on the variant/mode — `Bind(Sequence)` → CPS-continuation threading,
    `Bind(ValuePosition)` → success-tagged local delimiter, `Let` → ordinary
    Erlang `let`.
  - **NodeIds live on `Atom` variants and on structural `MExpr` variants
    (`App`, `Case`, `If`, `With`, `FieldAccess`, etc.).** `Pure` and `Bind`
    do **not** carry their own `source: NodeId` — `Pure` wraps an atom that
    already has one; `Bind` is pure scaffolding. `Yield` keeps `source` (the
    original `EffectCall` NodeId).
  - **`MHandler` / `MHandlerArm` are parallel structs** to AST `Handler` /
    `HandlerArm` rather than generic parameterization across `ast.rs`.
  - **`MDecl::{FunBinding, Val, DictConstructor, Passthrough(ast::Decl)}`** —
    selectively-parallel: typed where bodies live, passthrough everywhere
    else.
  - **`EffectOpRef { effect, op, op_index }`** is pre-resolved at
    translation time so the lowerer doesn't need to re-look-up effect/op
    indices.
- **Scope of `MExpr`:** expression/computation bodies only. Module structure,
  decl headers, function signatures, effect declarations stay as AST.
- **Translation invariants:**
  - Translation is total: every AST node maps to exactly one rewrite rule.
    No fallback path. No conditional CPS.
  - `Atom` positions are type-checked.
  - Source `NodeId`s preserved on every leaf and structural node.

### 11. Effect optimization **(new)**

- **What:** three correctness-safe rewrites over the monadic IR, run together
  in a shared bottom-up fixpoint:
  1. **Bind-collapse**: `Bind { value: Pure(a), var: x, body: B }` → `B[x := a]`.
     Eliminates pure sequencing introduced by uniform translation.
  2. **Bind→Let promotion**: when the value's `MExpr` is recursively pure (no
     `Yield` reachable), rewrite `Bind { var, value, body }` →
     `Let { var, value, body }`. Lets the lowerer emit an ordinary Erlang
     `let` instead of CPS-continuation threading.
  3. **Direct-call** (tail-resumptive): for a `Yield` that resolves
     statically to a `TailResumptive` handler arm, inline the arm body with
     `Resume(a) → Pure(a)`. Eliminates the reified continuation at
     tail-resumptive effect call sites.
- **Inputs:** `MProgram`, `HandlerAnalysis` (from stage 8.5), `ResolutionMap`.
- **Outputs:** `MProgram` (semantically identical, lower cost).
- **Files:** new module tree:
  ```
  src/codegen/monadic/effect_opt/
  ├── mod.rs              — orchestrator (single shared fixpoint)
  ├── bind_collapse.rs
  ├── bind_to_let.rs      — purity promotion
  └── direct_call.rs      — tail-resumptive rewrite
  ```
- **Disposition:** **new.** Functionally optional — the compiler is correct
  with this pass as identity (`fn run(m, _h) -> MProgram { m }`). Required
  for shippable perf because today's baseline gives pure code zero CPS
  overhead by construction; uniform translation regresses that until
  bind-collapse + Bind→Let promotion land.
- **Concrete rewrite spec:** **see
  [effect-optimization-spec.md](./uniform-effect-translation/effect-optimization-spec.md)** for
  rewrite rules with worked examples, soundness conditions, traversal
  strategy, fixpoint argument, and handler-flag interaction.
- **Key invariants:**
  - Never produces a miscompile. A false `Multishot` verdict ⇒ just slow.
    Only a false `TailResumptive` verdict would be unsound — and
    handler-analysis is conservative.
  - Bind-collapse fires unconditionally — it's the monad left-identity law,
    independent of handler flags.
  - Direct-call fires only on `TailResumptive` arms with statically
    resolvable handlers. `OneShot` and `Multishot` arms stay slow.
  - Synthesized inlinings do not appear in `ResolutionMap`; the new lowerer
    handles them via direct `apply` on closures it already has.

### 12. Lower **(new — parallel module `lower_monadic/`)**

- **What:** translate the optimized monadic IR into Core Erlang (`CModule`).
  Handles handler emission, evidence threading at `with`, BEAM-native effect
  bodies, runtime data layout.
- **Inputs:** monadic IR program, `ResolutionMap`, `ConstructorAtoms`,
  module codegen context.
- **Outputs:** `CModule`.
- **Files:** new module — `src/codegen/lower_monadic/`. The old
  [src/codegen/lower/](../../src/codegen/lower/) stays untouched until
  cleanup. Renamed to `lower/` only in the final cleanup commit.
- **Disposition:** **new module, fresh implementation.** Not a refactor of
  the old lowerer. Old lowerer's selective-CPS branching, per-call
  conditional emission, and `CallEffectMap` consumption have no analogue
  in the new lowerer — it consumes uniform monadic IR (`Pure` → value
  emission, `Yield` → evidence lookup + apply, `Bind` → sequenced
  let-bindings).
- **Shared with old path** (allowed cross-imports):
  - [lower/evidence.rs](../../src/codegen/lower/evidence.rs) — evidence
    layout, `insert_canonical`, `project_evidence`, `find_evidence`,
    `EvidenceLayout`.
  - [cerl.rs](../../src/codegen/cerl.rs) — Core Erlang IR and printer.
  - [runtime_shape.rs](../../src/codegen/runtime_shape.rs) — runtime layout
    helpers.
- **Reimplemented fresh in new lowerer** (copy-and-adapt or rewrite):
  - Handler-arm compilation to per-op closures (today's
    `build_op_handler_fun`).
  - BEAM-native effect op bodies (Actor, Process, Timer, Ref, …).
  - `with`-site emission (extends evidence via `insert_canonical`).
  - Handler-binding dispatch (static alias / conditional / dynamic).
- **Smaller from the start.** Old `lower/mod.rs` is 4111 LOC because it
  juggles selective CPS, call-shape enumeration, and conditional emission.
  None of that is needed under uniform monadic IR. Target per-file size:
  ≤800 LOC, split by responsibility (e.g. `mod.rs`, `effects.rs`,
  `handlers.rs`, `beam_native.rs`, `exprs.rs`, `pats.rs`).

### 13. Emit Core Erlang

- **What:** pretty-print `CModule` to a `.core` file.
- **Inputs:** `CModule`.
- **Outputs:** `.core` text on disk.
- **Files:** [src/codegen/cerl.rs](../../src/codegen/cerl.rs).
- **Disposition:** unchanged.

### 14. `erlc` / `erl` (external)

- **What:** `erlc` compiles `.core` to `.beam`; `erl -noshell` executes for
  `saga run`.
- **Disposition:** unchanged (external toolchain).

## Build order

Strategic phases:

1. Build uniform translation + the slow always-yields path against the
   existing test suite. **This is the test oracle.**
2. Add effect optimization: bind-collapse first, then Bind→Let promotion,
   then tail-resumptive direct-call as separate increments.
3. Differential-test optimized output vs. slow oracle. Weight generation
   toward multishot patterns (the only place a gate error hides).
4. Run alongside the current path (comment-toggle); switch once effect
   optimization is reliable. **No big-bang.**

### Implementation phases (module-by-module)

Within strategic phase 1, the module order is:

| #   | Module                                        | Why this order                                                                                   | Rough effort |
| --- | --------------------------------------------- | ------------------------------------------------------------------------------------------------ | ------------ |
| 1   | `src/codegen/handler_analysis.rs`             | Small, no dependencies; output is needed by effect optimization later                            | ~0.5 day     |
| 2   | `src/codegen/anf.rs` + `FreshNames`           | Foundation for translation; mechanical; depends on nothing else new                              | ~1 day       |
| 3   | `src/codegen/monadic/ir.rs`                   | Type defs only; paste from [monadic-ir-spec.md](./uniform-effect-translation/monadic-ir-spec.md) | ~few hours   |
| 4   | `src/codegen/monadic/translate.rs`            | Mechanical given ANF + ir.rs                                                                     | ~2 days      |
| 5   | `src/codegen/monadic/print.rs`                | Debug pretty-printer; useful before lower_monadic so we can inspect IR                           | ~0.5 day     |
| 6   | `src/codegen/monadic/effect_opt/` as identity | Stub `fn run(m, _h) -> m`; unblocks lowerer testing                                              | ~hour        |
| 7   | `src/codegen/lower_monadic/`                  | The bulk; every MExpr variant + handler emission + BEAM-native effects                           | ~5–8 days    |
| 8   | Wire toggle in `src/codegen/mod.rs`           | Two entry points; comment-toggle pattern                                                         | ~hour        |

After step 8 and the phase-1 parity blockers above, the new path is
functional end-to-end through the slow uniform path. This is **strategic
phase 1 complete** — uniform translation correct against the test suite,
modulo perf.

Within strategic phase 2, the effect_opt fill-in order is:

| #   | Rewrite                     | Why this order                                                                                                                  |
| --- | --------------------------- | ------------------------------------------------------------------------------------------------------------------------------- |
| 9   | bind-collapse               | Most pure-code-regression wins; simplest rule; smallest code; unblocks differential testing                                     |
| 10  | Bind→Let promotion          | Recovers the remaining "pure call in effectful chain" perf gap; medium complexity                                               |
| 11  | tail-resumptive direct-call | Correctness-sensitive (gated by `TailResumptive` flag + static handler resolution); biggest perf win on hot tail-resumptive ops |

Each rewrite ships as its own increment with its own differential-test
pass. Pass 3's no-op identity is the baseline; each rewrite is a strict
improvement.

After steps 9-11, run the acceptance/hardening checklist before starting a
larger follow-up optimization. See
[acceptance-hardening.md](./uniform-effect-translation/acceptance-hardening.md).

### Realistic single-session targets

- **Front-half session:** steps 1–6 + a stubbed step 7 that handles
  literals/vars/lets/function calls only + step 8 → "hello world via new
  toggle." Sets up the scaffolding and confirms the pipeline plumbs.
- **Subsequent sessions:** flesh out step 7 by category (patterns, records,
  case/if, effects, handlers, BEAM-native effects, …). Each session
  expands the new path's test-passing surface and the toggle stays usable
  for differential comparison.
- **Phase-2 sessions:** ship the three effect_opt rewrites one at a time
  (steps 9–11), each as its own increment with differential validation.

### Expected perf valley

With uniform translation done but effect optimization incomplete, performance will
**regress** — today's compiler gives pure functions zero CPS overhead by
construction. Uniform translation makes them allocate a `Pure` and a
continuation closure per bind until effect optimization's bind-collapse rule lands. The
collapse rule needs to ship before the new path becomes the default, not
after.

### Sanity invariant

After effect optimization, a function performing no effects (or only tail-resumptive
effects) must have **zero** continuation-closure allocations and **zero**
`Yield`/`Pure` constructions in the emitted Core Erlang. Anything else there
means the optimizer didn't fire — that's the debug signal.

## Deferred follow-ups (post-phase-1)

Items that surfaced during phase 1 implementation and need addressing
but aren't blockers for phase 1 milestone completion.

### Higher-order `@external` adapter

**Status:** landed in phase 1 as blocker **8a** above. This section is kept for
design notes and soundness constraints.

**Problem:** under the new path's uniform calling convention, every
Saga function is arity+2 (`args..., _Evidence, _ReturnK`). BIFs that
expect native-arity fun callbacks (e.g. `lists:map`, `lists:filter`)
can't be handed Saga funs directly — invoking a uniform-arity fun
with native arity crashes.

**Old tactical workaround:** re-implement the ~15
higher-order stdlib functions (`List.map`, `List.filter`, `List.foldr`,
`List.flatmap`, `List.partition`, `Set.map`/`filter`/`fold`,
`Dict.map_values`/`filter_entries`/`fold_entries`,
`Array.map`/`foldl`, `List.sort_with`/`sort_by`) as pure Saga
recursion. Unblocks the test suite but doesn't generalize — any future
`@external` taking a fun arg hits the same wall.

**Strategic fix:** automatic fun-arg adaptation in `lower_external_wrapper`.
The wrapper consults source parameter types at emission time; for each
fun-typed parameter it emits an inline adapter bridging a uniform-arity Saga
function to the native-arity callback expected by the Erlang target. Saturated
external applications with callback-shaped arguments route through this wrapper
so the same adaptation applies to direct calls and first-class references.

Soundness: fun args in `(a -> b)` signatures (without effect row) are
already typechecker-enforced to be pure, so synchronous extraction is
always well-defined for the cases the typechecker admits. For
hypothetical effectful fun args the adapter would be structurally
unsound, but those aren't typeable in this position.

The new path supports higher-order `@external` calls without a stdlib-specific
callback table.

## Correctness gate

The **direct-call rewrite** (and only the direct-call rewrite) is unsound
across a genuinely multishot resumption. Bind-collapse is pure
capture-avoiding substitution — sound unconditionally as monad
left-identity. Bind→Let promotion only changes lowering shape, not
semantics — also sound unconditionally given its purity predicate.

So:

- `one_shot` / `tail_resumptive` are a **correctness gate** for direct-call,
  not a hint.
- Default to "not provably one-shot ⇒ assume multishot ⇒ keep full machinery."
- A false "one-shot" verdict is a miscompile. A false "multishot" verdict is
  just slow. Stay conservative.
- Bind-collapse and Bind→Let promotion fire unconditionally given their
  local predicates; they do not consult handler-analysis flags.

`resume` is already a distinct keyword / AST node, so the syntactic checks
are local tree walks (tail-call-detection difficulty):

- `tail_resumptive`: every tail position of the clause is a `resume`, and
  `resume` appears nowhere else in the clause.
- `one_shot`: `resume` only in tail position, not in a loop, not captured into
  a value. Otherwise multishot.

Precise interprocedural / higher-order versions of these checks are
genuinely hard but **optional** — skipping them just means some sites stay
slow.

## Reference

Primary: Xie & Leijen, _Generalized Evidence Passing for Effect Handlers_
(ICFP 2021), and the earlier _Effect Handlers, Evidently_ (ICFP 2020). Read
for operational intuition and statements of the optimization theorems
(tail-resumptive / resumed-at-most-once conditions). The logical-relation
soundness proofs can be skipped on first pass — we inherit the theorem, we
don't reproduce its proof.
