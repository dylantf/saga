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

Transforms to Core Erlang where the function takes an evidence vector and a return continuation. Each `op!` call indexes into the evidence to find its handler closure and passes a continuation:

```erlang
'do_work'/3 = fun (_Unit, _Evidence, _ReturnK) ->
  %% extract Log handler tuple from evidence (canonical position)
  let {_Tag, LogOps} = call 'erlang':'element'(EvIdx, _Evidence) in
  let LogOp = call 'erlang':'element'(1, LogOps) in
  apply LogOp("starting",
    fun (_) ->
      let X = call 'erlang':'+'(10, 20) in
      apply LogOp(<msg>,
        fun (_) -> apply _ReturnK(X)))
```

`_Evidence` carries every effect handler in scope; `_ReturnK` runs on successful completion at the enclosing handler boundary. Both are explicit parameters — no thread-local state, no implicit context.

### Evidence Vector Representation

The evidence vector is a BEAM tuple of per-effect entries, sorted alphabetically by canonical effect tag:

```erlang
{
  {'Std.Fail.Fail',   {FailHandler}},
  {'Std.IO.Stdio',    {EprintHandler, PrintHandler, ReadHandler}},
  {'Std.State.State', {GetHandler, PutHandler}}
}
```

Each entry is `{EffectAtom, OpTuple}`. Within an `OpTuple`, op closures are sorted alphabetically by op name. The whole structure is canonical — index of an effect in the outer tuple, and index of an op in its inner tuple, are statically determined when the row is closed.

The vector is always tagged. Closed-row op calls technically don't need the tag (the static indices suffice), but tagging keeps cross-module ABI uniform and makes runtime panics self-describing.

#### Op Call Lookup

- **Closed row (statically known indices):** `element(OpIdx, element(2, element(EffectIdx, Evidence)))`. Three constant-time element loads.
- **Open row (`..e`, callee doesn't know full row):** call out to `std_evidence_bridge:find_evidence/2` (defined in `src/stdlib/evidence.bridge.erl`), which walks the tuple by atom comparison. O(n) where n is the number of effects in scope, typically ≤5.

#### Extending Evidence at `with`

`expr with handler` extends the inherited evidence vector by inserting a new entry in canonical position:

```erlang
NewEvidence = call 'std_evidence_bridge':'insert_canonical'(
  OldEvidence,
  {'Std.Fail.Fail', {FailHandler}}),
apply Body(Args, NewEvidence, ReturnK)
```

`insert_canonical` finds the right position by tag compare, builds a new tuple, replaces an existing entry if the tag already exists (innermost-wins semantics fall out without explicit mask machinery). The inherited evidence is unchanged.

#### Projection at Call Boundaries

Effectful function calls thread evidence as a single argument followed by `_ReturnK`. When the callee declares a closed row that's a strict subset of the caller's row, the call site projects:

```erlang
NarrowedEvidence = call 'std_evidence_bridge':'project_evidence'(
  Evidence, [<<"Std.Fail.Fail">>]),
apply Callee(Args, NarrowedEvidence, ReturnK)
```

When the callee's row is open or matches the caller's exactly, evidence is forwarded unchanged. The projection cost is one tuple allocation per closed-row narrowing — comparable to today's per-op-arg appending but uniform across call shapes.

#### What Saga Doesn't Use From Koka

The convention is inspired by Koka's evidence passing (Xie & Leijen 2021), with deliberate simplifications enabled by Saga's effect semantics:

- **No `hevv` per entry.** Saga has no non-scoped resumes, so each evidence entry doesn't need to carry the saved evidence at handler installation.
- **No marker integers.** No prompt mechanism.
- **No mask levels.** Saga has no surface syntax for accessing shadowed outer handlers; innermost-wins covers all cases.
- **No yield checks.** Saga's CPS is user-level; there's no equivalent of Koka's `is_yielding` flag.
- **Projection only at closed-row narrowing**, not at every cross-row boundary. Koka projects via `@open` wrappers everywhere; Saga forwards unchanged when the callee row is open.

These reductions cut roughly half the runtime apparatus a Koka-faithful implementation would need.

### Handler Representation

Handler declarations are compiled to per-op handler functions at `with` sites and packaged as the `OpTuple` of an evidence entry. Each op closure has shape `fun(args..., K) -> ...`:

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

When a handler is bound to a variable via `let` (e.g. from a conditional or factory function), the binding holds a tuple of per-op lambdas — the same `OpTuple` shape that ends up inside an evidence entry, plus an optional return clause lambda. The wrapping into `{EffectAtom, OpTuple}` happens at the `with` site, not at the binding site.

This means handler-bound vars don't need separate compilation paths for the call site — the call site reads from evidence regardless of how the handler was obtained. The remaining distinctions are at `with` site emission:

1. **Static alias** (`let foo = console_log`): resolved at compile time to the original handler declaration; the `OpTuple` is constructed inline at `with`.
2. **Conditional** (`let foo = if dev then x else y`): the let value evaluates to an `OpTuple`; the `with` wraps it in `{EffectAtom, OpTuple}` and inserts it into evidence.
3. **Dynamic** (`let foo = make_handler()` or `let foo = handler for Log { ... }`): the let value is an `OpTuple` produced at runtime; identical `with`-site treatment to the conditional case.

### `with` Attaches the Handler

```
do_work () with console_log
```

Becomes (sketch — Core Erlang elided for clarity):

```erlang
%% Build the handler's OpTuple from console_log's arms
LogOps = {fun (Msg, K) -> ... end},
%% Insert the new entry into the inherited evidence
NewEv = call 'std_evidence_bridge':'insert_canonical'(
  Ev, {'Std.IO.Log', LogOps}),
%% Call the body with the extended evidence
apply 'do_work'/3('unit', NewEv, ReturnK)
```

The effectful function always takes `(user_args..., _Evidence, _ReturnK)`. Handler installation is a tuple insertion, not a parameter list extension.

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

When two `with` blocks handle the same effect (inner shadows outer), the canonical insertion at the inner `with` *replaces* the outer's entry at the same canonical position in the evidence vector. Innermost-wins falls out of the data structure without explicit mask handling.

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

Per-call effect metadata is computed once by a pre-pass and stored in `CallEffectMap` (keyed by AST `NodeId`). The lowerer is a read-only consumer: at every effectful call site, it reads `CallEffectInfo` from the map to determine projection, evidence layout, and op-call indices. There is no inline call-shape recognition at lowering time — adding a new call shape (e.g. `DictMethodAccess`, lambda-headed call) means teaching the populator one new branch, not auditing every dispatcher.

Continuation flow is threaded through explicit helpers:

- value-position lowering — produces a value for the enclosing construct
- terminal/tail lowering — routes successful completion through an explicit `_ReturnK`
- handler-owned expression lowering — produces the handled result directly, doesn't inherit an enclosing return continuation

This keeps handler delimiters and nested `with` boundaries explicit in the lowerer.

### Non-Resumable Effects

No special mechanism needed. A non-resumable handler simply doesn't call `K`. The continuation closure sits unreferenced on the heap and gets garbage collected. Same calling convention as resumable handlers.

### Multishot Continuations

On BEAM, multishot is essentially free. `K` is an immutable closure on the heap. Calling it multiple times is just calling a function multiple times -- no stack copying, no special machinery. The evidence vector at capture time is part of `K`'s closure environment, so each resume sees the same evidence that was in scope when the continuation was captured.

### BEAM-Native Effects

Some effects (for example Actor, Process, Monitor, Link, Timer, and Ref
families) use custom BEAM-native op bodies in the lowerer, but they still flow
through handler-owned CPS lambdas. They do not bypass handler delimitation or
nested `with` semantics; the native interop happens inside the handler body.

### Key Files

- `codegen/call_effects.rs` -- `CallEffectInfo`, `CallEffectMap`, populator. The pre-pass that determines per-call evidence shape ahead of lowering.
- `codegen/lower/evidence.rs` -- `EvidenceLayout`, `build_evidence_entry`, `insert_canonical`, `find_evidence`, `project_evidence`, `evidence_index_of`. Compile-time helpers for emitting the runtime evidence operations.
- `codegen/lower/mod.rs` -- `Lowerer`, `FunInfo`, call-site emission. Single helper for effectful calls regardless of head shape (Var, QualifiedName, DictMethodAccess, lambda).
- `codegen/lower/effects.rs` -- `lower_effect_call` (op call lookup against evidence), `lower_with` (extends evidence via `insert_canonical`), `build_op_handler_fun`, `build_beam_native_op_fun`, `lower_handler_def_to_tuple`.
- `codegen/lower/exprs.rs` -- value/tail lowering helpers, `lower_handle_binding`, `is_handler_value`.
- `codegen/lower/init.rs` -- populates `FunInfo` (with `EvidenceLayout`) from type schemes via `arity_and_effects_from_type`.
- `stdlib/evidence.bridge.erl` -- runtime helpers `find_evidence/2`, `insert_canonical/2`, `project_evidence/2` for the operations that don't inline cleanly.

### Optimization Opportunities

Already in place:

- **Pure functions:** no CPS transform at all -- compiled as normal Core Erlang functions with zero overhead. Pure-vs-effectful detection is centralized in `CallEffectInfo`.
- **Row polymorphism:** row variables are resolved before codegen. No runtime cost; rows that survive to lowering are forwarded through `_Evidence` unchanged.
- **Canonical-ordered indices:** for closed rows, op call sites emit static `element/2` loads rather than runtime atom comparisons. The runtime `find_evidence` helper is only used for open rows.
- **Innermost-wins via canonical insertion:** same-effect nesting handled by tuple replacement, not mask machinery.

Future work:

- **Direct-native fast path:** for BEAM-native ops (Process, Ref, Timer, etc.) called outside of user-defined handlers, fold the closure call into a direct native call. The `use_direct_native_fast_path` hook in `effects.rs` is currently a no-op stub.
- **Closed-row specialization:** when the entire program is closed-row (common for top-level entry points), specialize op call emission to skip the runtime tag and use direct positional indexing without the `{Tag, OpTuple}` wrapping. Speculative perf — needs benchmarking to justify.
- **Open-row lookup memoization:** for loops that repeatedly call the same op under an open row, cache the resolved handler closure once outside the loop. Probably not worth doing until a real workload shows it.
- **Handler inlining:** when the handler is statically known and small, inline the handler body at the call site, eliminating closure allocation.
- **Dead effect elimination:** if a handled effect is never called, strip the handler.
