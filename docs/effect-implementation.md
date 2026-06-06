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

## Uniform CPS Codegen

Saga now uses a uniform monadic/CPS lowering path for algebraic effects. The
stable end-to-end implementation note is `docs/uniform-cps-translation.md`; this
section is the short version.

The backend pipeline is:

```text
Elaborated AST -> ANF -> Monadic IR -> effect optimizer -> Core Erlang
```

Ordinary Saga functions and compiler-generated dictionary constructors lower to
functions with explicit evidence and return continuation parameters:

```text
(user_args..., _Evidence, _ReturnK)
```

`_Evidence` is the current runtime handler table. `_ReturnK` is the continuation
for successful completion at the current boundary. Effects are not implemented
with Erlang exceptions or process control flow; every operation is routed through
this explicit evidence/continuation protocol.

The optimizer is optional. The unoptimized uniform CPS path is the correctness
oracle, and optimization removes scaffolding only when a conservative local proof
says it is safe. See `docs/effect-optimization.md` for the current optimizer.

### Runtime Evidence

Evidence is a BEAM tuple of tagged entries:

```erlang
{
  {'Std.Fail.Fail',   {FailHandler}},
  {'Std.IO.Stdio',    {EprintHandler, PrintHandler, ReadHandler}},
  {'Std.State.State', {GetHandler, PutHandler}}
}
```

Each entry is `{EffectAtom, OpTuple}`. Entries are stored in canonical effect
atom order. Operations inside an `OpTuple` are stored in canonical operation name
order.

Installing a handler calls `std_evidence_bridge:insert_canonical/2`. If an
entry for the same effect already exists, it is replaced, which implements
innermost-wins shadowing.

Performing an operation lowers to:

1. find the effect entry in `_Evidence`;
2. select the operation closure from the entry's `OpTuple`;
3. apply the operation closure to `(op_args..., EvidenceAtPerform, K)`.

The runtime representation stays tagged even when the compiler knows the
operation index. This keeps cross-module evidence layout uniform and makes
runtime failures self-describing.

### Handler Representation

Source handler arms lower to operation closures:

```text
(op_args..., EvidenceAtPerform, K_arm)
```

A resuming arm calls `K_arm(value)`. A non-resuming arm ignores `K_arm`.
Multishot arms call it more than once.

The handler forms in monadic IR are:

- `Static` - source arms are known at the `with` site;
- `Dynamic` - a handler value is selected at runtime;
- `Native` - compiler-provided BEAM-native handler bodies;
- `Composite` - multiple handlers installed from one surface value.

Dynamic handler values are self-describing tuples:

```text
{__saga_handler_value, OpsByEffect, RuntimeReturn}
```

`OpsByEffect` is a canonical tuple of `{EffectAtom, OpTuple}` pairs.
`RuntimeReturn` is either `unit` or a Saga CPS function used as the handler's
return clause.

### Return Clauses, Resume, And Control Markers

Handler return clauses are delimited prompts. Nested handlers compose by
nesting: the inner return clause sees the raw body result first, then the outer
return clause sees the inner handler's result.

`resume v` applies the arm continuation captured at the perform site. That
continuation must re-enter any handler delimiters that were between the perform
site and the handler arm. The lowerer tracks this with `ResultDelimiter` in
`LowerCtx` and routes marked control tuples:

```text
{__saga_value_result, Marker, Value}
{__saga_handler_abort, Marker, Value}
```

The owning delimiter consumes its marker. Foreign markers propagate outward.
This is what makes value-producing resume, nested return clauses, and aborting
handlers compose under uniform CPS.

### Finally Blocks

`finally` cleanup is part of the continuation protocol, not an Erlang
`try/catch` wrapper around `resume`. Saga aborts are handler-control values, not
Erlang exceptions, so cleanup must be injected into the same control path that
routes resumes and aborts.

The optimizer can direct-call some cleanup-preserving handler arms when all
cleanup inputs are available at the perform site. Other cases use the slow
uniform CPS path.

### Native And External Boundaries

BEAM-native effects are installed as native handlers in evidence. The slow path
still calls their operation closures through evidence. Optimizer rewrites can
replace common native operations with direct `ForeignCall`s when the active
handler stack proves the native handler is the one that will run.

`@external` declarations get Saga-shaped wrappers. If an external function takes
a function-typed parameter, the wrapper adapts the Saga CPS callback to the
native callback arity using the evidence in scope at the boundary and an identity
return continuation.

### Key Files

- `codegen/monadic/ir.rs` -- monadic IR.
- `codegen/monadic/translate/` -- translation into monadic IR.
- `codegen/monadic/effect_opt/` -- optional effect optimizer.
- `codegen/lower/ctx.rs` -- lowering context and result delimiter stack.
- `codegen/lower/effects.rs` -- `Yield`, `With`, native handlers, dynamic handler values, and resume routing.
- `codegen/lower/decls.rs` -- uniform CPS function wrappers and external wrappers.
- `codegen/lower/app.rs` -- Saga calls, partial application, and direct external call boundaries.
- `codegen/lower/util.rs` -- evidence/control tuple helpers.
- `stdlib/evidence.bridge.erl` -- runtime evidence lookup and insertion.

### Further Reading

- `docs/uniform-cps-translation.md` -- full current implementation model.
- `docs/effect-optimization.md` -- optimizer rewrites and accepted slow paths.
- `docs/planning/uniform-effect-translation.md` -- migration history and phase status.
