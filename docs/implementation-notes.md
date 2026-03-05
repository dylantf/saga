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
4. Handler stacking: `with` block containing mixed named refs and inline arms (`expr with { h1, h2, op args -> body }`).

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

## 5. Resume Implementation Plan (Phase 2)

Current state: abort-only effects work. `EvalSignal::Effect` propagates via
`?` and `Expr::With` catches it. No continuations, no `resume`.

### Step 1: Replace `EvalSignal` with `EvalResult` enum

Change the return type of `eval_expr` from `Result<Value, EvalSignal>` to:

```rust
type Continuation = Box<dyn FnOnce(Value) -> EvalResult>;

enum EvalResult {
    Ok(Value),
    Error(EvalError),
    Effect {
        name: String,
        qualifier: Option<String>,
        args: Vec<Value>,
        continuation: Continuation,
    },
}
```

Add a `then` helper on `EvalResult` to chain continuations:

```rust
impl EvalResult {
    fn then(self, f: impl FnOnce(Value) -> EvalResult + 'static) -> EvalResult {
        match self {
            EvalResult::Ok(v) => f(v),
            EvalResult::Error(e) => EvalResult::Error(e),
            EvalResult::Effect { name, qualifier, args, continuation } => {
                // Compose: run the original continuation, then run f on its result
                EvalResult::Effect {
                    name,
                    qualifier,
                    args,
                    continuation: Box::new(move |v| continuation(v).then(f)),
                }
            }
        }
    }
}
```

The `then` method is the key insight. When a sub-expression fires an effect,
`then` wraps the "rest of what we were doing" onto the end of the existing
continuation. This is how continuations compose without rewriting everything.

### Step 2: Update `eval_expr` cases to use `then`

Every place that evaluates a sub-expression and then does more work needs
to use `then` instead of `?`. The pattern is mechanical:

**Before (abort-only):**
```rust
Expr::BinOp { op, left, right, .. } => {
    let left_val = eval_expr(left, env)?;
    let right_val = eval_expr(right, env)?;
    eval_binop(op, left_val, right_val)
}
```

**After (with continuations):**
```rust
Expr::BinOp { op, left, right, .. } => {
    let op = op.clone();
    let right = right.clone();
    let env = env.clone();
    eval_expr(left, &env).then(move |left_val| {
        eval_expr(&right, &env).then(move |right_val| {
            eval_binop(&op, left_val, right_val)
        })
    })
}
```

Sites that need this treatment (in priority order):

1. **Block / Let bindings** - most important, this is where sequential
   effects happen. Each statement's result feeds into the next via `then`.
2. **Function application (`Expr::App`)** - eval func, then eval arg, then
   apply. Three-step chain.
3. **Binary operators** - eval left, then right, then apply op.
4. **Effect calls (`Expr::EffectCall`)** - eval args left-to-right, then
   fire the signal. The continuation starts empty (identity) and gets
   composed by the caller via `then`.
5. **If/else** - eval condition, then take a branch. Straightforward.
6. **Case** - eval scrutinee, then match and eval arm body.
7. **Record create/update** - eval each field expression.
8. **Field access** - eval the record expression, then access field.

Simple cases like `Expr::Lit`, `Expr::Var`, `Expr::Lambda`,
`Expr::Constructor` just return `EvalResult::Ok(v)` directly -- no change
needed.

### Step 3: Update `apply` to return `EvalResult`

`apply` currently returns `Result<Value, EvalSignal>`. Change to
`EvalResult`. The `EffectFn` arm becomes:

```rust
Value::EffectFn { name, qualifier, arity, mut args } => {
    args.push(arg);
    if args.len() == arity {
        EvalResult::Effect {
            name,
            qualifier,
            args,
            continuation: Box::new(EvalResult::Ok), // identity: caller composes via then
        }
    } else {
        EvalResult::Ok(Value::EffectFn { name, qualifier, arity, args })
    }
}
```

The continuation is initially just the identity function. The caller
(wherever `apply` was called from) will compose the "rest of computation"
onto it via `then`.

### Step 4: Update `Expr::With` to pass `resume` to handlers

`With` catches `EvalResult::Effect` and makes the continuation available
as `resume` in the handler's scope:

```rust
Expr::With { expr, handler, .. } => {
    let handler_val = /* resolve handler, same as before */;
    match eval_expr(expr, env) {
        EvalResult::Ok(val) => EvalResult::Ok(val),
        EvalResult::Effect { name, args, continuation, .. } => {
            // Find matching handler arm
            for arm in &handler_val.arms {
                if arm.op_name == name {
                    let handler_env = handler_val.env.extend();
                    for (param, arg) in arm.params.iter().zip(args.iter()) {
                        handler_env.set(param.clone(), arg.clone());
                    }
                    // Make the continuation available as `resume`
                    handler_env.set("resume".to_string(),
                        Value::Continuation(continuation));
                    return eval_expr(&arm.body, &handler_env);
                }
            }
            // No match, re-raise with continuation intact
            EvalResult::Effect { name, qualifier: None, args, continuation }
        }
        EvalResult::Error(e) => EvalResult::Error(e),
    }
}
```

### Step 5: Add `Value::Continuation` and implement `Expr::Resume`

Add a new Value variant to hold captured continuations:

```rust
Value::Continuation(Box<dyn FnOnce(Value) -> EvalResult>)
```

Since `FnOnce` isn't `Clone`, this needs special handling -- continuations
are single-shot by design, so we wrap in `Option` inside `Rc<RefCell<>>`
and take it on first use (second use = runtime error).

`Expr::Resume` evaluates its argument and calls the continuation:

```rust
Expr::Resume { value, .. } => {
    let val = /* eval the resume argument */;
    let cont = env.get("resume"); // get the continuation from scope
    match cont {
        Value::Continuation(k) => k(val),  // invoke it
        _ => EvalResult::Error("resume used outside handler"),
    }
}
```

### Step 6: Update `eval_program`, `eval_decl`, `main.rs`

- `eval_decl` calls `eval_expr` in let bindings and fun bodies, so it
  needs to handle `EvalResult` instead of `Result`.
- `eval_program` needs to check for unhandled effects at the top level.
- `main.rs` matches on `EvalResult` variants instead of `EvalSignal`.

### Testing plan

Test in this order:
1. All existing 119 tests still pass (abort-only effects still work).
2. `Log` effect with resume: `log msg -> { print msg; resume () }` -
   handler prints and then computation continues.
3. `State` effect: `get` resumes with current state, `put` updates state
   and resumes with unit.
4. Verify that NOT calling `resume` still aborts (Fail effect unchanged).
5. Verify single-shot: calling `resume` twice is a runtime error.

### Ownership gotcha: `FnOnce` and `Clone`

`Value` derives `Clone`, but `Box<dyn FnOnce>` isn't `Clone`. Options:
- Wrap in `Rc<RefCell<Option<...>>>` and `.take()` on use (enforces single-shot)
- Make `Value::Continuation` use `Rc<dyn Fn>` instead (allows multi-shot,
  less safe) -- probably not what we want
- Separate `Continuation` from `Value` entirely and pass through a side channel

The `Rc<RefCell<Option<>>>` approach is cleanest for single-shot semantics.

---

## 6. Built-in `panic` and `todo`

Both are language builtins that halt execution immediately. They exist
outside the effect system (no `!`, no handler, no `needs` propagation).

```rust
// In eval_expr, these are special forms:
Expr::Panic(msg) => EvalResult::Error(EvalError::Panic(msg)),
Expr::Todo(msg) => EvalResult::Error(EvalError::Todo(msg)),
```

- Return type `Never` - type checker allows them anywhere a value is expected.
- `todo` can be distinguished from `panic` for tooling: the type checker
  can warn about remaining `todo`s, list them as incomplete work, or
  reject them in release builds.
- Parser: `panic "msg"` and `todo "msg"` are keywords, not function calls.

---

## 7. Explicitly Out of Scope

- **Multishot continuations** - calling `resume` more than once. Not needed
  for practical effects (I/O, logging, state, errors, async). Could be added
  later as opt-in if needed.
- **Effect inference** - inferring which effects a function uses. We require
  explicit annotations. Inference is a type-checker concern for later.
- **Effect tunneling** - effects silently passing through handlers. Keep it
  simple: unhandled effects are runtime errors (static errors after type checker).
