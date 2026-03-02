# Implementation Notes

Notes on implementation strategy and design decisions for effects.

---

## 1. Evaluator Strategy: EvalResult Enum (Lazy CPS)

Instead of rewriting the entire evaluator into CPS, use a return enum that
only constructs continuations when an effect fires:

```rust
enum EvalResult {
    Value(Value),
    Effect {
        name: String,
        args: Vec<Value>,
        continuation: Box<dyn FnOnce(Value) -> EvalResult>,
    },
}
```

**How it works:**

- Normal code returns `EvalResult::Value(v)` - no overhead, same as today.
- When `!` is hit (e.g., `log! "hello"`), the evaluator returns
  `EvalResult::Effect { name: "log", args: ["hello"], continuation: <rest> }`.
- The continuation captures "everything left to do after this effect call"
  as a closure.
- The handler either:
  - Calls the continuation with a value (`resume`) - computation continues.
  - Returns its own value without calling it (`Fail`) - computation aborts.

**Advantages over full CPS:**

- Minimal change to existing evaluator - most `eval` cases stay the same.
- No overhead for pure code - effects only pay the continuation cost.
- Continuations are single-shot (call the `FnOnce` or don't) - Rust's
  ownership model enforces this naturally.

**Where continuations get constructed:**

Every place in the evaluator where "there's more work to do after evaluating
a subexpression" needs to handle the `Effect` case. The main sites:

- `let` bindings: `let x = <EFFECT HERE>; rest` - continuation is `rest`
  with `x` bound to the resumed value.
- Block expressions: after evaluating statement N, statements N+1..end are
  the continuation.
- Function arguments: if evaluating an argument triggers an effect,
  continuation is "finish evaluating remaining args, then call function."
- Binary operators: if left side triggers effect, continuation is "evaluate
  right side, then apply operator."

This is still nontrivial, but it's incremental - you can add effect support
to one eval case at a time and test as you go.

---

## 2. Tokenizing `!` as Part of the Identifier

`log!` is lexed as a single `EffectCall("log")` token, not as two tokens
`Ident("log")` + `Bang`.

**Rationale:**

- `!` has no other use in the language, so no ambiguity.
- The parser immediately knows this is an effect operation - no lookahead.
- `Cache.get!` parses cleanly as `Ident("Cache")` `.` `EffectCall("get")`.
- The lexer rule is simple: if an identifier is immediately followed by `!`
  (no whitespace), emit `EffectCall` instead of `Ident`.

---

## 3. Implementation Order

### Phase 1: Effects without `resume` (structured exceptions)

1. Add `EffectCall` token to lexer (identifier + `!`).
2. Add `EffectCall` AST node (name + args).
3. Parse `effect` declarations - register operation names.
4. Parse `with` handler blocks (inline) on expressions.
5. Implement handler stack in evaluator (a `Vec<Handler>`).
6. When `EffectCall` is evaluated, walk the handler stack.
7. Handler body executes, its value becomes the result of the `with` block.
8. Test with `Fail` effect and `to_result` handler.

This phase doesn't need continuations at all - effects just abort and
return a value, like `try/catch`. The `EvalResult` enum can be `Value` only,
with effects propagated via `Result<Value, EffectSignal>`.

### Phase 2: Add `resume` (continuations)

1. Change `eval` return type to `EvalResult` enum.
2. Add continuation construction at key eval sites (let, blocks, args).
3. `resume` in a handler calls the continuation with a value.
4. Test with `Log` effect (resume after logging) and `State` effect.

### Phase 3: Named handlers

1. Parse `handler name for Effect { ... }` declarations.
2. Store named handlers in the environment (they're values/closures).
3. `expr with name` looks up the handler and installs it.
4. Handler stacking: comma-separated list after `with` (`expr with h1, h2, { ... }`).

### Phase 4: Parser updates for `needs` effect annotations

1. Parse `fun f () -> T needs {Effect1, Effect2}` syntax.
2. Store effect annotations in the AST (alongside existing type annotations).
3. Ignored by evaluator (like type annotations today) - for future type checker.

---

## 4. Backend Considerations (Future)

| Backend    | Continuations               | GC             | Tail calls      | Notes                                                       |
| ---------- | --------------------------- | -------------- | --------------- | ----------------------------------------------------------- |
| BEAM       | Free (processes)            | Free           | Free            | Lowest risk. Best fit for effects. Gleam proved the path.   |
| JavaScript | Closures native             | Free           | No (trampoline) | Medium risk. Deep CPS = stack overflow without trampolines. |
| C          | fn pointers + heap closures | Must implement | No (trampoline) | Highest risk. GC is a project unto itself.                  |

Decision deferred until after effects are working in the interpreter.
The `EvalResult` enum approach is backend-agnostic - the same continuation
concept maps to closures (JS), processes (BEAM), or function pointers (C).

---

## 5. Explicitly Out of Scope

- **Multishot continuations** - calling `resume` more than once. Not needed
  for practical effects (I/O, logging, state, errors, async). Could be added
  later as opt-in if needed.
- **Effect inference** - inferring which effects a function uses. We require
  explicit annotations. Inference is a type-checker concern for later.
- **Effect tunneling** - effects silently passing through handlers. Keep it
  simple: unhandled effects are runtime errors (static errors after type checker).
