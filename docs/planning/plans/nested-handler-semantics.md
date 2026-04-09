# Nested Handler Semantics — Implementation Plan

## Context

`with {a, b, c}` currently means "one merged handler set" where later handlers override
earlier ones for overlapping operations. This creates ambiguous semantics around `return`
clauses, overlapping ops, and inline vs named handler ordering. The proposal in
`docs/planning/nested-handler-semantics.md` changes this to pure nesting:

```
expr with {a, b, c}  ==  ((expr with a) with b) with c
```

This is a semantic redesign of handler composition. It needs proper architecture: shared
helpers for any logic that appears in more than one place, no duplicated logic across
phases, no quick fixes.

---

## Phase 1: AST — Introduce `HandlerItem` enum

**Goal:** Unify the separate `named`/`arms` fields into a single ordered `items` list so
source ordering is preserved for desugaring.

### Changes to `src/ast.rs`

Add new enum:
```rust
pub enum HandlerItem {
    Named(NamedHandlerRef),
    Arm(HandlerArm),
}
```

Change `Handler::Inline`:
```rust
Inline {
    items: Vec<Annotated<HandlerItem>>,
    return_clause: Option<Box<HandlerArm>>,
    dangling_trivia: Vec<Trivia>,
}
```

This replaces the separate `named: Vec<Annotated<NamedHandlerRef>>` and
`arms: Vec<Annotated<HandlerArm>>` fields. Every downstream pattern match on
`Handler::Inline` must be updated.

### Files to update (mechanical find-and-replace of destructuring):

1. `src/parser/expr.rs` — `parse_handler_ref()`: construct with `items` instead of
   separate `named`/`arms` (no parser logic changes yet, just construction)
2. `src/desugar.rs` — `desugar_handler()`: iterate `items` instead of `arms`
3. `src/formatter/expr.rs` — `format_handler()`: iterate `items` with match on variant
4. `src/typechecker/handlers.rs` — `infer_with()` and `infer_with_inner()`:
   extract named/arms from `items` via partition/filter
5. `src/typechecker/effects.rs` — `handler_handled_effects()`
6. `src/typechecker/resolve.rs` — handler name canonicalization
7. `src/elaborate.rs` — `elaborate_handler()`/With arm in elaborate_expr
8. `src/codegen/lower/effects.rs` — `normalize_with_handler()`
9. `src/codegen/resolve.rs` — handler resolution in With expressions

### Shared helpers to add on `Handler`:

Add methods directly on `Handler` (in `src/ast.rs`) so extraction logic isn't duplicated:
```rust
impl Handler {
    /// Iterator over named handler refs in this handler.
    pub fn named_refs(&self) -> impl Iterator<Item = &Annotated<NamedHandlerRef>>
    
    /// Iterator over inline handler arms in this handler.
    pub fn arms(&self) -> impl Iterator<Item = &Annotated<HandlerArm>>
    
    /// Mutable iterator over inline handler arms.
    pub fn arms_mut(&mut self) -> impl Iterator<Item = &mut Annotated<HandlerArm>>
    
    /// All handler names (for named handlers and named refs in inline blocks).
    pub fn handler_names(&self) -> Vec<&str>
}
```

These helpers are used everywhere that currently destructures `named`/`arms` separately.
This avoids every call site re-implementing the partition logic.

### Verification
- `cargo test` — all existing tests pass
- `cargo clippy` — clean
- This is a purely mechanical refactor with zero semantic changes.

---

## Phase 2: Parser — Allow mixed handler item ordering

**Goal:** Remove the "named handler refs must come before inline handler arms" restriction.

### Changes to `src/parser/expr.rs` — `parse_handler_ref()`

Replace the two-phase loop (Phase 1: named refs only, Phase 2: inline arms only) with
a single unified loop that parses items in any order:

```
while !matches!(self.peek(), Token::RBrace | Token::Eof) {
    if matches!(self.peek(), Token::Return) {
        parse return clause (same as current)
    } else if is_named_ref_lookahead() {
        parse named ref -> push HandlerItem::Named to items
    } else {
        parse inline arm -> push HandlerItem::Arm to items
    }
    consume optional comma
}
```

The existing `is_named_ref` lookahead logic (lines 594-605) already distinguishes named
refs from inline arms correctly. The key change is: **don't break out of the loop when
switching from named to inline**. Just keep going.

Remove the error at line 682-687 entirely.

### Changes to `src/formatter/expr.rs` — `format_handler()`

Update to iterate `items` in order, formatting each `HandlerItem::Named` and
`HandlerItem::Arm` inline. The "named-only single line" optimization checks
`items.iter().all(|i| matches!(i.node, HandlerItem::Named(_)))`.

### Verification
- Parser tests: add tests for inline arms appearing before/between/after named refs
- Formatter round-trip: `format(parse(src)) == src` for mixed-order handler blocks
- `cargo test`

---

## Phase 3: Desugar — Multi-handler to nested `with`

**Goal:** Transform `with {a, b, c}` into `((expr with a) with b) with c` in the
existing desugar pass, before typechecking.

### Changes to `src/desugar.rs`

The desugar already recurses into `ExprKind::With` children (line 211-217) and
transforms sugar forms bottom-up (line 330). Add a new transformation in the
"transform current node" phase:

**Algorithm in `desugar_expr`:**

After recursing into `ExprKind::With { expr, handler }` children:

1. If handler is `Handler::Named` or `Handler::Inline` with exactly one item and no
   return clause: no transformation needed.
2. Otherwise, extract items from `Handler::Inline { items, return_clause, .. }`:
   - Build a list of individual handler layers from `items` (each becomes its own `With`)
   - If return clause exists, it becomes the outermost layer
3. Fold left: `acc = inner_expr`, then for each item in order, wrap:
   `acc = Expr::synth(span, ExprKind::With { expr: acc, handler: single_handler })`
4. Replace the original expression with the final `acc`.

**How each item becomes a handler layer:**
- `HandlerItem::Named(ref_)` -> `Handler::Named(ref_.name, ref_.span)`
- `HandlerItem::Arm(arm)` -> `Handler::Inline { items: [HandlerItem::Arm(arm)], return_clause: None, .. }`
- Return clause -> `Handler::Inline { items: [], return_clause: Some(rc), .. }`

**Return clause placement:** Always outermost, regardless of source position. This is
correct because the return clause transforms the final result of the entire handled
computation.

**Span handling:** All synthetic `With` nodes use the original `With` expression's span
so error messages point to the source location.

### Semantic change: sibling effects

Under the old merged model, an inline handler arm body could use effects handled by
sibling handlers in the same `with` block. Under nesting, the outer handler's arm body
is NOT inside the inner handler's scope.

Example that changes behavior:
```
expr with {
  console_log,
  fail msg = { log! "caught"; 0 }   # log! was handled by sibling console_log
}
```
After desugar: `(expr with console_log) with { fail msg = { log! "caught"; 0 } }`
Now `log!` in the fail arm is NOT handled by console_log — it propagates outward.

This is the intended semantic change per the design doc. Document it and update any
affected tests/examples.

### Verification
- Add desugar unit tests: verify AST structure after desugaring multi-handler `with`
- Existing codegen integration tests: some may need updating for the semantic change
- `cargo test`

---

## Phase 4: Typechecker — Simplify to single-handler `with`

**Goal:** `infer_with_inner` only needs to handle single-handler `with` nodes after
desugaring. Delete the multi-handler composition logic.

### Changes to `src/typechecker/handlers.rs`

**`infer_with` (lines 98-170):**
Simplify handler name collection. After desugar, `Handler::Inline` has at most one item.
Use the `handler_names()` helper from Phase 1.

Simplify `arm_stack_entry` building: with single handlers, at most one handler
contributes arm spans per `With` node. The LSP arm stack still works because nested
`With` nodes push/pop naturally.

**`infer_with_inner` (lines 172-608):**
The `Handler::Inline` branch (lines 321-606) currently handles:
- Multiple named refs with effect merging (329-364)
- Sequential return type chaining across named handlers (370-441)
- Return clause inference with named handler subtraction (443-467)
- Multiple inline arm inference with sibling subtraction (469-555)
- Unused handler warning across multiple handlers (563-604)

After desugar, this entire branch simplifies to three cases:

**Case A: Single `HandlerItem::Named` in items** — shouldn't occur (desugar converts
these to `Handler::Named`), but handle defensively by delegating to the Named branch.

**Case B: Single `HandlerItem::Arm` in items** — One inline handler arm:
1. Look up effect op signature for the arm's op_name
2. Bind arm params to op param types
3. Set resume_type and resume_return_type
4. Infer arm body in isolated effect scope
5. Unify arm result type with answer_ty
6. Typecheck optional finally block
7. Emit remaining effects (inner_effs minus the one handled effect)

**Case C: Return clause only** (items empty, return_clause is Some):
1. Bind return clause param to answer_ty
2. Infer return clause body
3. Return type is the body's type
4. Emit return clause body's effects

**What gets deleted:**
- The `named_handler_entries` collection loop (329-364)
- The return type chaining loop across named handlers (370-441)
- The `named_needs` accumulation and merging (422-441)
- The sibling subtraction logic (524-530)
- `expand_used_handler_families_for_warning` (only needed for multi-handler unused
  detection)

**What simplifies:**
- Unused handler warning: trivial for single handler — does the inner expr use that
  effect? One check instead of a loop.
- Effect subtraction: subtract exactly one effect family, not a merged set.

### Changes to `src/typechecker/effects.rs`

**`handler_handled_effects`:** Simplify to handle at most one item. Use `Handler::arms()`
and `Handler::named_refs()` helpers.

### Verification
- All existing typechecker tests pass (behavior preserved for single-handler cases)
- Tests for nested `with` from desugar typecheck correctly
- Tests for the sibling-effect semantic change produce expected errors
- `cargo test -p dylang typechecker`

---

## Phase 5: Lowerer — Simplify to single-handler `with`

**Goal:** `lower_with` only handles single-handler `with` nodes. Delete multi-handler
merging logic.

### Changes to `src/codegen/lower/effects.rs`

**`normalize_with_handler` (lines 687-704):**
After desugar, this returns at most:
- `(vec![one_name], vec![], None)` for Named
- `(vec![], vec![one_arm], None)` for single inline arm
- `(vec![], vec![], Some(rc))` for return clause only

No logic change needed — the function already works correctly for these cases. But
simplify it to assert the single-handler invariant.

**`lower_with` (lines 346-517):**
The current function handles multiple named refs and inline arms in a merged model.
After desugar, simplify:

1. **effect_owner map:** no longer needed (only one handler, so it owns all its ops)
2. **inline_arms_by_op merging with named handlers:** no longer needed
3. **plan_op_handler:** simplify — the plan is always either the one named handler's
   arms, the one inline arm, or passthrough. No owner lookup.
4. **The two-pass structure (register params, then build handlers)** stays — it's still
   needed for the single-handler case when the handler has multiple ops.
5. **Reachability analysis** stays — still useful for pruning unused op bindings.

**What gets deleted:**
- `effect_owner: HashMap<String, usize>` and its population
- The `inline_arms_by_op` vs named handler priority logic in `plan_op_handler`
- Multi-handler iteration in `plan_op_handler`

### Changes to `src/codegen/normalize.rs`

No changes needed — it just recurses into children and clones the handler.

### BEAM-native effects and `direct_ops`

These continue to work unchanged with single-handler `with`. A BEAM-native handler is
just a single named handler that happens to have native lowering. `direct_ops` still
applies within a single handler's scope.

### Verification
- `cargo test --test codegen_integration` — integration tests pass
- Build and run example programs that use multi-handler `with` blocks
- `cargo test -p dylang codegen`

---

## Phase 6: Tests and examples

### New tests to add

1. **Desugar tests:** Verify AST structure after multi-handler desugaring
2. **Parser tests:** Mixed-order handler items (inline before named, named after inline)
3. **Typechecker tests:**
   - Nested `with` from desugar typechecks correctly
   - Return clauses compose through nesting
   - Overlapping handlers: inner handler wins
   - Effect propagation through nested handler layers
4. **Codegen integration tests:**
   - Multi-handler `with` produces correct runtime behavior
   - Return clause composition works end-to-end
   - Overlapping handler priority is correct
5. **Formatter tests:** Round-trip mixed-order handler blocks

### Existing tests/examples to update

- Any test that relies on sibling effect handling between handlers in the same
  `with` block needs updating for the new nested semantics
- Examples in `examples/` that use multi-handler `with` — verify they still work
  or update them

### Verification
- `cargo test` — full test suite passes
- `cargo clippy` — clean
- `cargo run -- run examples/*.dy` — examples work correctly
- `cargo run -- test` — project test suite passes

---

## Phase ordering rationale

1. **AST first** (Phase 1) — mechanical refactor, zero semantic change, gets the
   foundation right
2. **Parser second** (Phase 2) — removes the restriction users hit, small isolated change
3. **Desugar third** (Phase 3) — the semantic pivot point; after this, downstream phases
   receive single-handler `with` nodes
4. **Typechecker fourth** (Phase 4) — simplify based on the desugar guarantee
5. **Lowerer fifth** (Phase 5) — simplify based on the desugar guarantee
6. **Tests last** (Phase 6) — verify everything end-to-end

Each phase keeps the codebase compiling and passing tests. Phases 4 and 5 are
independent of each other and could be done in either order.

---

## Key files

| Phase | File | What changes |
|-------|------|-------------|
| 1 | `src/ast.rs` | Add `HandlerItem`, change `Handler::Inline` |
| 1 | All consumers of `Handler::Inline` | Update destructuring |
| 2 | `src/parser/expr.rs` | Unified handler item loop |
| 2 | `src/formatter/expr.rs` | Format mixed-order items |
| 3 | `src/desugar.rs` | Multi-handler to nested `with` transform |
| 4 | `src/typechecker/handlers.rs` | Single-handler `infer_with_inner` |
| 4 | `src/typechecker/effects.rs` | Simplify `handler_handled_effects` |
| 5 | `src/codegen/lower/effects.rs` | Single-handler `lower_with` |
