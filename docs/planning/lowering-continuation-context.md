# Lowering Continuation Context

## Motivation

Recent effect/codegen bugs have clustered around the same theme:

- a nested expression is supposed to produce a value
- but lowering treats it as if it were in terminal position
- so it consumes or forwards the enclosing continuation too early
- and the surrounding `let`, argument position, or outer `with` never sees the
  value it expected

The concrete failures looked different:

- statement-level `with` swallowed following statements
- named handlers with `where` clauses elaborated into blocks that consumed the
  enclosing `_ReturnK`
- nested `with` under an outer `with { return ... }` wrapped results on the
  wrong side of the delimiter
- `with` in argument position returned the caller continuation result instead of
  the argument value

These were fixed locally, but the recurrence suggests a deeper architectural
issue in lowering.

## Diagnosis

The lowerer originally relied on ambient mutable state to describe continuation
mode:

- `current_return_k`
- `pending_callee_return_k`

Those fields implicitly encode several distinct questions:

1. Is this expression being lowered in value position or terminal position?
2. Should a direct effectful call receive an inherited `_ReturnK`?
3. Is a surrounding `with` return clause active?
4. Is the current subexpression supposed to delimit the outer continuation?

Because this mode is implicit, every lowering path has to remember when to:

- save/restore continuation state
- clear it temporarily
- re-thread it inward
- avoid applying it twice

That makes it easy for new expression forms to accidentally inherit terminal
behavior in value position.

## Current Symptom Pattern

The bad shape is usually one of these:

1. A value-producing subexpression tail-calls `_ReturnK`

```text
let x = <expr>
rest
```

but `<expr>` lowers as if it were the terminal computation of the enclosing
function/test body.

2. A nested `with` fails to delimit the outer return clause

```text
{ inner with h1 } with h2
```

and the `return` clause from `h2` is applied both inside and outside the inner
computation, or on the wrong side of an abort.

3. An argument expression consumes the caller continuation

```text
assert_eq (expr with h) expected
```

and the argument lowering jumps directly into the continuation of `assert_eq`
instead of producing the argument value first.

## Proposed Direction

Make continuation context explicit in the lowering API instead of ambient.

### Sketch

```rust
enum LowerMode {
    Value,
    Tail(CExpr),
}
```

Potentially, if needed later:

```rust
enum LowerMode {
    Value,
    Tail(CExpr),
    DirectReturn(CExpr),
}
```

Then route lowering through explicit entry points:

```rust
fn lower_expr_in(&mut self, expr: &Expr, mode: LowerMode) -> CExpr
fn lower_block_in(&mut self, stmts: &[Stmt], mode: LowerMode) -> CExpr
```

With clear semantics:

- `Value`: lower as a value-producing subexpression
- `Tail(k)`: lower as the terminal computation whose final successful value
  should flow to `k`

## How This Simplifies Things

### `let` RHS and function arguments

These always use `Value`.

That removes the need for ad hoc helper logic that temporarily clears ambient
return state when lowering subexpressions.

### Terminal block positions

These use `Tail(k)`.

The lowerer no longer has to infer terminal-vs-value position indirectly from
mutable fields.

### `with`

`with` becomes a real delimiter:

- in `Value` mode, it produces a value
- in `Tail(k)` mode, it decides how success and abort interact with `k`
- if it has a `return` clause, that clause composes explicitly with `k`

This should eliminate the current category of bugs where nested `with` uses the
outer continuation on the wrong side of the delimiter.

## Migration Plan

This should be done incrementally, not as a one-shot rewrite.

### Phase 1: Introduce explicit value/tail helpers

Add:

- `lower_expr_value(expr)`
- `lower_expr_tail(expr, k)`
- `lower_block_value(stmts)`
- `lower_block_tail(stmts, k)`

These can initially delegate to `lower_expr_in` / `lower_block_in` while the
old APIs still exist.

### Phase 2: Convert obvious value sites

Migrate these first:

- `let` RHS
- function arguments
- tuple/record fields
- operator operands
- case scrutinees

These sites should never inherit terminal continuation behavior.

### Phase 3: Convert block terminal lowering

Refactor `lower_block` around explicit tail mode instead of checking ambient
return-continuation state.

This should subsume much of:

- `lower_expr_with_k`
- `lower_block_with_k`
- special terminal-case handling for effect calls and effectful function calls

### Phase 4: Refactor `with`

Move `lower_with` to explicit mode-sensitive behavior:

- `with` in value position
- `with` in tail position
- nested `with` with outer return clause
- direct effectful inner call vs block form

This is the highest-value cleanup because most recent bugs were in this area.

### Phase 5: Remove ambient continuation state

Once the major call sites are migrated, remove or sharply reduce:

- `current_return_k`
- `pending_callee_return_k`

Ideally these disappear entirely. If anything remains, it should be a very
local implementation detail rather than the main lowering control mechanism.

Status:

- `current_return_k` has now been removed from active lowering.
- `pending_callee_return_k` has also now been removed from active lowering.
- Continuation flow is now expressed through explicit lowering helpers rather
  than ambient mutable lowering state.

## Interaction With Typechecking

This refactor should start in lowering, not in the typechecker.

The confirmed bugs so far were runtime/codegen bugs:

- programs typechecked
- effect rows were accepted
- runtime behavior was wrong because continuations were scoped incorrectly

So the primary architectural issue is in lowering.

That said, the typechecker/codegen boundary should be kept in mind:

- `FunInfo` and related effect metadata are derived from types
- if future real bugs appear around open rows or effect metadata lossiness, the
  typechecker-to-codegen interface may need to become more expressive

But that is a separate concern from the continuation-context problem described
here.

## Success Criteria

This refactor is worth doing if it makes these classes of bugs harder to write:

- nested `with` in statement position
- nested `with` under outer handlers with `return` clauses
- elaboration-introduced blocks in expression position
- `with` in argument position
- any value subexpression accidentally jumping into the enclosing `_ReturnK`

The practical goal is not just fewer bugs today, but making future effect
features less likely to require continuation-scoping patchwork.

## Handler-Specific Endgame

After the general lowering cleanup, the remaining continuation complexity is
mostly concentrated in `effects.rs`.

That remaining logic is not accidental in the same way as the earlier ambient
state usage; it represents a few real handler-specific invariants:

1. Handler return clauses are *owned by the handler*

When lowering a handler `return` clause body, inherited function/outer-handler
return behavior must be cleared. The `return` clause should describe the
handler's success mapping, not compose implicitly with an enclosing `_ReturnK`.

2. Handler arm bodies are *owned by the handler*

When lowering an op arm body, inherited return behavior must also be cleared.
The arm result becomes the handled computation's result. It should not
accidentally jump into the enclosing function's return continuation.

3. A handled direct call may still inherit an outer return continuation

For:

```text
expr with handler
```

if `expr` is a direct effectful function call and the handler has no local
`return` clause, then the outer handled return behavior may still need to flow
through to that call so abort-style handlers can skip subsequent computation
correctly.

### Recommended Next Refactor

Refactor `effects.rs` around these invariants directly, rather than around
"removing ambient state everywhere" as a goal in itself.

That likely means:

- introducing explicit helper names for "lower with no inherited return"
- introducing explicit helper names for "lower handled inner expression with
  handled return + inherited return"
- keeping any remaining ambient mechanism tightly local to handler semantics
  unless a clearer explicit representation emerges naturally

### Exit Criteria For The Handler Phase

This phase is successful if:

- handler-specific continuation behavior is concentrated in a few named helpers
- general lowering no longer depends on handler ambient state
- `effects.rs` reads like a description of handler semantics rather than a set
  of continuation-state manipulations
