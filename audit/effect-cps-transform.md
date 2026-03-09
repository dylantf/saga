# CPS Transform Audit

## Architecture: Sound but incomplete CPS

The implementation uses a **selective CPS transform**: only block-level effect calls get CPS-transformed. This is much simpler than a full-program CPS transform and works correctly for the common case where effect calls appear as block statements. The A-normalization pass handles the case where effect calls are nested in expressions (binops, function args).

## Issues Found

### 1. (DONE) Critical: Effect calls inside `if`/`case` branches don't capture outer continuation

When an abort-style effect (one where the handler doesn't call `resume`) fires inside an `if` or `case` branch, the codegen doesn't abort the outer computation. The handler returns a value that becomes the branch result, and execution continues with the next statement in the enclosing block.

Example that would behave differently in interpreter vs codegen:

```
{
  let x = if cond then fail! "oops" else 42
  x + 1      -- runs in codegen, skipped in interpreter
} with to_result
```

**Why it happens:**

In `lower_block` (exprs.rs:230-269), the first statement `let x = if ...` is not detected as an effect call by `collect_effect_call` (it checks the value, which is an `If`, not an `EffectCall`). So it takes the normal (non-effect) path: `let x = lower_expr(if_expr) in lower_block(rest)`.

Inside `lower_expr` for the `If`, each branch calls `lower_expr` on `fail! "oops"`. That gets CPS-transformed, but the continuation K for `fail!` is just an identity function (since there's nothing after it in the branch). The handler's fail arm returns `Err "oops"` without calling K. This value becomes `x`, and then `x + 1` runs.

In the interpreter, `fail!` returns `EvalResult::Effect`, which propagates through the `.then()` chain. The handler catches it without calling the continuation, so `x + 1` never executes.

A-normalization does not help here: normalize.rs:175-189 normalizes branches within their own scope. An effect call as the top-level expression of a branch stays there.

**Fix options:**

- (a) A-normalization could lift effect calls out of `if`/`case` branches into the enclosing block, but this changes semantics for conditional effects
- (b) Make `lower_expr` for `If`/`Case` aware of effect calls in branches and CPS-transform the outer continuation into each branch
- (c) Full CPS transform (heavyweight)

The most targeted fix is **(b)**: when lowering an `if`/`case` whose branches contain effect calls, and there is an outer continuation context (more statements after this expression in the block), thread the outer K through the branches.

### 2. Critical: Return clause wraps abort values for function-call inner expressions

When the inner expression of `with` is a function call (not a block), the CPS chain lives inside the called function. `current_return_k` is never consumed by `lower_block`, so `apply_return_k` at exprs.rs:465 wraps the result unconditionally, including values returned by abort-style handlers.

Example -- the `try` pattern from example 14:

```
fun try (computation: () -> a needs {Fail}) -> Result a String
try computation = computation () with {
  fail msg -> Err msg
  return value -> Ok value
}
```

Trace:

1. `lower_with` sets `current_return_k = fun (Value) -> Ok(Value)`
2. `lower_expr(computation())` emits `apply Computation(_HandleFail)` and returns
3. Inside computation, `fail! "oops"` fires. Handler returns `Err("oops")` without calling K
4. `Err("oops")` becomes the return value of `apply Computation(_HandleFail)`
5. exprs.rs:465: `apply_return_k(Err("oops"))` wraps it to `Ok(Err("oops"))`

Expected: `Err("oops")`. Got: `Ok(Err("oops"))`.

**Why this is hard:** Once the function call returns, you can't distinguish "computation completed normally" from "handler aborted." Both produce a value from `apply Computation(_HandleFail)`. The return clause should only apply to normal completions. Inside a block, this distinction is maintained naturally -- ReturnK lives inside the continuation K, so handler aborts (which don't call K) never reach it. But for function calls, the CPS chain is internal to the function, and ReturnK is external.

**Fix:** Every effectful function needs an additional `_ReturnK` parameter. At the function body's terminal, apply `_ReturnK` to the final value. The `with` site passes the return clause as `_ReturnK`. Non-`with` call sites pass identity (`fun (X) -> X`).

```erlang
% Current: do_work takes only handler params
'do_work'/1 = fun (_HandleFail) ->
  apply _HandleFail('fail', "oops", fun (X) -> X + 1)

% Fixed: do_work takes handler params + ReturnK
'do_work'/2 = fun (_HandleFail, _ReturnK) ->
  apply _HandleFail('fail', "oops",
    fun (X) ->
      let Result = call 'erlang':'+'(X, 1) in
      apply _ReturnK(Result))
```

Now:

- Abort: handler returns `Err("oops")`. K is never called. `_ReturnK` is never called. Result: `Err("oops")`. Correct.
- Success: handler calls `K(val)`. `Result = val + 1`. `_ReturnK(Result)` produces `Ok(Result)`. Correct.

At call sites:

- `computation () with { ..., return value -> Ok value }` passes `fun (V) -> Ok(V)` as ReturnK
- `computation ()` (no `with` or no return clause) passes `fun (X) -> X` as ReturnK

This increases every effectful function's arity by 1, but it's the only way to maintain the abort/success distinction across function call boundaries.

### 3. (DONE) Medium: `apply_return_k` uses `.take()` -- breaks branching

exprs.rs:204-215:

```rust
fn apply_return_k(&mut self, val: CExpr) -> CExpr {
    if let Some(k) = self.current_return_k.take() {  // <-- .take() consumes
```

Only one code path gets the return clause. Consider:

```
{
  if cond then {
    fail! "a"
    42
  } else {
    fail! "b"
    99
  }
} with { fail msg -> Err msg, return value -> Ok value }
```

The then-branch's `lower_block` terminal calls `apply_return_k`, consuming `current_return_k`. The else-branch's terminal finds `None` -- its final value 99 is not wrapped in `Ok`.

**Fix:** Clone instead of take. Have `lower_with` clear `current_return_k` after lowering the inner expression (which it already does at line 468).

### 4. Minor: `resume` hardcoded to `_K` variable name

mod.rs:765-776 always emits `apply _K(value)`. This works because handler functions always name their continuation param `_K` (exprs.rs:500). Nested handlers shadow correctly via lexical scoping. Not a bug, but using `fresh()` names would be more robust against refactoring surprises.

### 5. Latent: `EffectCall.args` field ignored in codegen

`collect_effect_call` at util.rs:109-127 only collects `App`-wrapped args, ignoring `EffectCall.args`. This is safe today because the parser always creates `EffectCall { args: vec![] }` and wraps args via `App`. But if any future pass populates `EffectCall.args` directly, this would silently drop arguments. Consider either:

- Asserting `EffectCall.args.is_empty()` in `collect_effect_call`
- Or including `EffectCall.args` in the returned args

### 6. Non-trivial patterns in CPS let-bindings

At exprs.rs:245-248, `pat_binding_var` only handles `Pat::Var`. If a user writes `let (a, b) = some_effect! ()`, the pattern is a tuple, `pat_binding_var` returns None, a fresh var is used, and the destructuring is lost. The continuation K receives the effect result but only binds it to a single variable.

## What's Correct

- **Core CPS mechanism in `lower_block`**: Correctly identifies the first effect call in a block, builds K from the remaining statements, and passes it to `lower_effect_call`. Textbook CPS.
- **A-normalization lifting**: Properly lifts nested effect calls (`1 + ask!()` becomes `let __eff0 = ask!(); 1 + __eff0`) so that `lower_block` can find them at statement level. Left-to-right evaluation order is preserved.
- **Handler reinstallation (deep handlers)**: Handler params are closed over in K since `lower_block` captures them in the continuation closure. When `resume` calls K, subsequent effect calls still reference the same handler. Correct deep handler behavior.
- **Return clause placement**: The return_k is set inside the CPS chain and consumed at terminal block positions. Handler aborts (which don't call K) naturally bypass the return clause. Matches the fix in commit 55f6753.
- **HOF effect absorption**: Threading handler params through higher-order calls works correctly.
- **Handler function construction**: Op-dispatch via case, positional arg binding, K as the last parameter.

## Detailed Trace: Why Deep Handlers Work

Consider:

```
{
  log! "a"
  log! "b"
} with console_log
```

After A-normalization, this is a block with two effect-call statements. `lower_block` processes `log! "a"` first:

- K = `fun (X) -> apply _HandleLog('log', "b", K2)` where K2 = identity
- Emits: `apply _HandleLog('log', "a", K)`

When the handler calls `resume ()`, it calls K, which then performs the second `log!`. Since `_HandleLog` is in scope as a let-binding around the whole block (from `lower_with`), it's captured by the K closure. The **same handler** handles the second call. Correct deep handler behavior.

## Recommendation

Three issues need fixing in priority order:

1. **Return clause wraps abort values (#2):** Architectural fix. Add a `_ReturnK` parameter to all effectful functions. This is the only way to maintain the abort/success distinction across function call boundaries. Without this, the `try` pattern produces wrong results.

2. **`apply_return_k` `.take()` breaks branching (#3):** Quick fix. Clone instead of take.

3. **Effect calls in `if`/`case` don't capture outer K (#1):** When lowering an `if`/`case` whose branches contain effect calls and there is an outer continuation context (more statements after this expression in the block), thread the outer K through the branches. This mirrors what the interpreter's `.then()` does automatically.
