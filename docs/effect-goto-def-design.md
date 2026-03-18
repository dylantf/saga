# Effect Go-to-Definition + Unused Handler Elimination

Design notes from discussion on 2026-03-17.

## Problem

When a handler defines arms for multiple ops but only some are called in the `with` body, the unused handler arm closures are still emitted in Core Erlang. Erlang warns: "a term is constructed, but never used". The `_` prefix on variable names doesn't suppress this because it's about the constructed closure value, not the variable binding.

## Proposed solution: two-hop go-to-definition

Effect calls resolve through two levels, and go-to-definition should mirror this:

1. **`a!()` -> handler arm**: jump to `a () -> resume 1` in the closest enclosing `with` handler
2. **`a () -> resume 1` -> effect op definition**: jump to `fun a () -> Int` in the `effect` declaration

This matches the mental model: the call site resolves to the handler that intercepts it, and the handler arm resolves to the effect op it implements.

## What the typechecker already knows

- `lookup_effect_op` resolves which effect + op an `op!` call refers to (level 2)
- `type_at_span` maps spans to types for LSP hover
- `register_handler` validates handler arms against effect definitions

What's missing: the typechecker doesn't currently track which specific handler arm will handle a given call (level 1), because that depends on the `with` site context.

## Implementation plan

### Phase 1: Track handler arm references during codegen

- Add `used_handler_params: HashSet<String>` to the `Lowerer`
- In `lower_effect_call`, mark the handler param key as used when accessed
- In `lower_with`, only emit let-bindings for handler arms in the used set
- This fixes the Erlang warning with minimal changes

### Phase 2: Effect call -> handler arm resolution (LSP level 1)

Store a mapping from effect call spans to handler arm spans. This could live in `CheckResult` as:

```rust
/// Maps an effect call span -> the handler arm span that handles it.
pub effect_call_targets: HashMap<Span, Span>,
```

The tricky part: this resolution currently happens in codegen (`lower_with`), not the typechecker. Options:

- **Option A**: Do a resolution pass during typechecking when processing `with` expressions. Walk the `with` body, find effect calls, match them to handler arms. Store the mapping.
- **Option B**: Have the codegen lowerer produce this mapping and feed it back to the LSP. Less clean but avoids duplicating resolution logic.

Option A is preferred since the typechecker already has all the information needed.

### Phase 3: Handler arm -> effect op definition (LSP level 2)

During `register_handler`, the typechecker already matches each arm to an effect op. Store:

```rust
/// Maps a handler arm span -> the effect op definition span it implements.
pub handler_arm_targets: HashMap<Span, Span>,
```

This is straightforward since the match is already happening.

## Edge cases

- **Nested handlers**: Inner `with` shadows outer handler arms for the same effect. The resolution must follow scoping: an `op!` call resolves to the innermost enclosing handler for that effect.
- **Inline vs named handlers**: Both need to participate in the mapping.
- **Handler stacking**: `with { console, to_result, fail reason -> ... }` merges multiple handlers. Each arm traces back to its source.

## Relation to unused handler elimination

Phases 2 and 3 naturally produce the data needed to skip emitting unused handler closures. If a handler arm span has no incoming edges from effect call spans within its `with` body, the corresponding closure doesn't need to be emitted. This unifies the LSP feature and the codegen optimization.
