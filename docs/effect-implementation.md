# Effect Implementation

Two layers: the **type system** tracks which effects a computation performs (compile time, zero runtime cost), and the **CPS transform** compiles effectful code to Core Erlang (runtime mechanism).

---

## Type System

### Type Representation

Every function type carries an effect row:

```rust
Type::Fun(Box<Type>, Box<Type>, EffectRow)  // param -> return with effects
```

`EffectRow` has a list of known effects and an optional row variable tail:

```rust
struct EffectRow {
    effects: Vec<(String, Vec<Type>)>,  // e.g. [("Log", []), ("State", [Int])]
    tail: Option<Box<Type>>,             // None = closed, Some(Var) = open (..e)
}
```

Pure functions have `EffectRow::empty()` (closed, no effects). `Type::arrow(a, b)` is a convenience constructor for pure function types.

### Where Effects Live on Curried Functions

Effects go on the **innermost** arrow (closest to the return type):

```
fun greet : String -> String -> Unit needs {Log}
=> Fun(String, Fun(String, Unit, {Log}), {})
```

Partial application `greet "hi"` returns `Fun(String, Unit, {Log})` -- effects are preserved until full saturation.

### Computation Types

`infer_expr` returns `(Type, EffectRow)` -- a value type and the effects the expression performs. This is the core mechanism: effects flow as return values from inference, not in a side-channel.

How effects compose at each expression form:

| Expression                   | Value type                       | Effect row                                        |
| ---------------------------- | -------------------------------- | ------------------------------------------------- |
| Literal, Var, Constructor    | the value's type                 | empty                                             |
| `log! "hello"` (effect call) | op return type                   | `{Log}`                                           |
| `f x` (application)          | return type                      | func_effs + arg_effs + callee_row (at saturation) |
| `{ a; b; c }` (block)        | type of `c`                      | merge of all statement effects                    |
| `if c then a else b`         | unified branch type              | merge of cond + both branches                     |
| `case x { ... }`             | unified arm type                 | merge of scrutinee + all arms                     |
| `fun x -> body` (lambda)     | `Fun(param, body_ty, body_effs)` | body_effs (propagates to enclosing scope)         |
| `expr with handler`          | handler result type              | inner_effs - handled + arm_effs                   |

### Effect Subtyping

A function with fewer effects can be used where more are allowed. Effect row unification is symmetric (accepting either direction of subset), but at function application sites, a directional check enforces that a callback argument's effects are a subset of the parameter's expected effects. This means:

- A pure function can be passed where an effectful callback is expected (covariant).
- An effectful function CANNOT be passed where a pure callback is expected (caught by `check_callback_effect_subtype` in `infer.rs`).

The directional check runs after unification succeeds, comparing the resolved argument type's effect row against the resolved parameter type's effect row. Open rows (with `..e` tail) are exempt since they accept extra effects by design.

### Absorption

When a HOF parameter declares effects (e.g. `f: Unit -> a needs {Fail}`), calling the HOF with an effectful lambda doesn't propagate those effects to the caller. The parameter's declared effects are **absorbed** -- subtracted from the merged effect row.

The absorption logic uses `resolve_var` (not full `apply`) on the parameter type to read only the statically declared effects, not effects captured by a row variable (`..e`). This ensures row-captured effects propagate to the caller while explicitly declared effects are absorbed.

### Row Polymorphism

Open effect rows (`..e`) allow functions to be polymorphic over effects:

```
fun run : (f: Unit -> Unit needs {Fail, ..e}) -> Unit needs {..e}
run f = f () with { fail msg = () }
```

The row variable `..e` captures any extra effects from the callback and forwards them to the caller. In unification, when one row is open and the other has extras, the tail variable binds to the extras.

### Handler Effect Subtraction

`with` blocks are desugared early into nested handlers. For example:

```dy
expr with {a, b, c}
```

becomes:

```dy
((expr with a) with b) with c
```

using lexical order.

Typechecking then happens one handler layer at a time: infer the inner
expression to get `(ty, inner_effs)`, subtract the effects handled by this
layer from `inner_effs` via `EffectRow::subtract`, then merge in any effects
performed by this layer's arm bodies that escape outward.

This has one important consequence: sibling items in a surface `with {...}`
block do not satisfy each other's arm-body effects. If an inline arm body uses
`Log`, that `Log` must be handled by an outer scope after desugaring, not by a
sibling item later in the same surface block.

### Function Body Checking

After inferring all clauses of a function body, the accumulated `EffectRow` (merged across clauses) is checked against the declared `needs` row from the annotation. This uses `check_effects_via_row`: if the declared row is open, any extras are allowed; if closed, undeclared effects are an error.

### Key Files

- `typechecker/mod.rs` -- `Type::Fun`, `EffectRow` (with `empty`, `merge`, `subtract`), `EffectMeta`, `effects_from_type`
- `typechecker/infer.rs` -- `infer_expr` returns `(Type, EffectRow)`, App absorption logic, lambda effect propagation, handler binding detection in `infer_block` (`extract_handler_info`, `handler_info_from_type`)
- `typechecker/effects.rs` -- `check_effects_via_row`, effect op lookup/instantiation
- `typechecker/handlers.rs` -- `infer_with`/`infer_with_inner`, handler subtraction
- `typechecker/check_decl.rs` -- `collect_annotations` (builds EffectRow on innermost arrow), `check_fun_clauses` (body effect check), `innermost_effect_row` helper
- `typechecker/unify.rs` -- `unify_effect_rows` (row matching, tail binding)

### EffectMeta

Metadata for effect inference (not effect tracking):

- `type_param_cache` -- ensures ops from the same effect (e.g. `get!` and `put!` from `State s`) share type vars within a scope
- `fun_type_constraints` -- concrete type args from annotations like `needs {State Int}`
- `known_funs` / `known_let_bindings` -- name registries used by codegen to derive `CheckResult.fun_effects` and `let_effect_bindings` from resolved types

### Codegen Boundary

`CheckResult.fun_effects` and `CheckResult.let_effect_bindings` are derived from resolved types at the `to_result` boundary by walking each known function/binding's type scheme and extracting effect names via `effects_from_type`. The codegen never reads effect data from the typechecker's internal state directly.

---

## CPS Transform (Codegen)

### Core Idea

All effects are implemented via CPS (Continuation-Passing Style) transform at compile time. There is **one mechanism** for all effects -- resumable, non-resumable, and multishot. No `throw`/`catch`, no process spawning for control flow.

Every effect call captures "everything after this point" as a closure (`K`) and passes it to the handler. The handler decides what to do:

- **Resume:** call `K(value)` -- computation continues
- **Abort:** don't call `K` -- computation is abandoned, handler's return value is the result
- **Multishot:** call `K` multiple times -- each call runs an independent copy of the rest of the computation (free on BEAM since closures are immutable)

### Effect Calls Become Continuation-Passing

```
fun do_work : Unit -> Int needs {Log}
do_work () = {
  log! "starting"
  let x = 10 + 20
  log! ("result: " <> show x)
  x
}
```

Transforms to Core Erlang where each `op!` call passes a continuation:

```erlang
'do_work'/1 = fun (HandleLog) ->
  apply HandleLog('log', "starting",
    fun (_) ->
      let X = call 'erlang':'+'(10, 20) in
      apply HandleLog('log', <msg>,
        fun (_) -> X))
```

### Handler Representation

Handler declarations are compiled to per-op handler functions at `with` sites. Each op gets its own function `(args..., K)`:

```erlang
% handler console_log for Log { log msg -> { print msg; resume () } }
% At the `with` site, the log arm becomes:
fun (Msg, K) ->
  call 'io':'format'("~s~n", [Msg]),
  apply K('unit')

% handler to_result for Fail { fail reason -> Err(reason) }
fun (Reason, _K) ->
  {'Err', Reason}       % don't call K = abort
```

### Handler Bindings (Dynamic Handlers)

When a handler is bound to a variable via `let` (e.g. from a conditional or factory function), it becomes a **tuple of per-op lambdas** at runtime. The tuple layout is ops sorted alphabetically by `Effect.op` key, with an optional return clause lambda as the last element.

At `with` sites, the lowerer destructures the tuple to extract per-op handler functions. Three compilation paths:

1. **Static alias** (`let foo = console_log`): resolved at compile time to the original handler declaration. Arms are inlined. Zero cost.
2. **Conditional** (`let foo = if dev then x else y`): generates wrapper lambdas that dispatch via `case` on the condition variable.
3. **Dynamic** (`let foo = make_handler()` or `let foo = handler for Log { ... }`): the handler is a tuple of lambdas, destructured at `with` sites via `erlang:element/2`.

### `with` Attaches the Handler

```
do_work () with console_log
```

Becomes:

```erlang
apply 'do_work'/1('console_log'/3)
```

The effectful function takes its handler(s) as extra parameter(s).

### Handler Stacking

Handler stacking is modeled as nested handlers, not a merged handler table.

```dy
run () with {console_log, to_result}
```

is treated like:

```dy
(run () with console_log) with to_result
```

The nearest enclosing handler gets the first chance to handle an operation. If
it does not define that operation, the operation propagates outward to the next
handler layer.

### The `return` Clause

`return value -> Ok(value)` wraps the computation's final value on success for
that handler boundary. Under nested semantics, `return` clauses compose by
nesting.

Given:

```dy
((expr with a) with b) with c
```

the success path flows through:

1. `a.return`
2. `b.return`
3. `c.return`

assuming each layer defines a `return` clause and completes normally. If an op
handler aborts instead of resuming, outer `return` clauses still run only when
their own surrounding handled expression completes.

### Lowering Structure

Continuation flow is threaded through explicit helpers:

- value-position lowering (`lower_expr_value`)
- terminal/tail lowering (`lower_expr_tail`, `lower_terminal_effectful_expr_with_return_k`)
- direct effectful callee lowering with explicit `_ReturnK`
- handler-owned expression lowering (`lower_handler_owned_expr`)

This keeps handler delimiters and nested `with` boundaries explicit in the
lowerer:

- value-position expressions produce a value for the enclosing construct
- terminal expressions route successful completion through an explicit continuation
- direct effectful callees receive `_ReturnK` explicitly
- handler-local bodies produce the handled result directly

### Non-Resumable Effects

No special mechanism needed. A non-resumable handler simply doesn't call `K`. The continuation closure sits unreferenced on the heap and gets garbage collected. Same calling convention as resumable handlers.

### Multishot Continuations

On BEAM, multishot is essentially free. `K` is an immutable closure on the heap. Calling it multiple times is just calling a function multiple times -- no stack copying, no special machinery.

### BEAM-Native Effects

Some effects (for example Actor, Process, Monitor, Link, Timer, and Ref
families) use custom BEAM-native op bodies in the lowerer, but they still flow
through handler-owned CPS lambdas. They do not bypass handler delimitation or
nested `with` semantics; the native interop happens inside the handler body.

### Key Files

- `codegen/lower/mod.rs` -- `Lowerer`, `FunInfo`, `fun_effects()`, `expanded_arity()`
- `codegen/lower/effects.rs` -- `lower_effect_call`, `lower_with`, `build_op_handler_fun`, `build_beam_native_op_fun`, `lower_handler_expr_to_tuple`, `lower_handler_def_to_tuple`, handler-owned expression lowering
- `codegen/lower/exprs.rs` -- explicit value/tail lowering helpers, `lower_handle_binding` (static alias, conditional, and dynamic handler binding detection), `is_handler_value`
- `codegen/lower/init.rs` -- populates `FunInfo` from type schemes via `arity_and_effects_from_type`
- `codegen/lower/util.rs` -- `arity_and_effects_from_type`, `param_absorbed_effects_from_type`

### Optimization Opportunities

- **Inlining:** When the handler is statically known, inline the handler body directly, eliminating closure allocation
- **Dead effect elimination:** If a handled effect is never called, strip the handler
- **Pure functions:** No CPS transform at all -- compiled as normal Core Erlang functions with zero overhead
- **Row polymorphism:** Row variables are resolved before codegen. No runtime cost.
