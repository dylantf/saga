# Effect Implementation

Two layers: the **type system** tracks which effects a computation performs (compile time, zero runtime cost), and the **CPS transform** compiles effectful code to Core Erlang (runtime mechanism).

---

## Type System

### Type Representation

Every function type carries an effect row:

```rust
Type::Fun(Box<Type>, Box<Type>, EffectRow)  // param -> return with effects
```

`EffectRow` has a list of known effects and zero or more row variable tails:

```rust
struct EffectRow {
    effects: Vec<EffectEntry>,  // e.g. Log, State Int
    tails: Vec<Type>,           // [] = closed, [Var(e)] = open (..e)
}
```

Pure functions have `EffectRow::empty()` (closed, no effects).
`Type::arrow(a, b)` is a convenience constructor for pure function types.

Multiple tails are allowed: `needs {..a, ..b}` means "the union of the
independent open rows carried by `a` and `b`." Each tail binds independently
during unification. This is important for higher-order functions with multiple
effectful callbacks and for generic functions that forward multiple trait
constraints' effects.

### Where Effects Live on Curried Functions

Effects go on the **innermost** arrow (closest to the return type):

```
fun greet : String -> String -> Unit needs {Log}
=> Fun(String, Fun(String, Unit, {Log}), {})
```

Partial application `greet "hi"` returns `Fun(String, Unit, {Log})` -- effects are preserved until full saturation.

### Computation Types

`infer_expr` returns the value `Type` and emits performed effects into
`Checker.effect_row`. Callers use `save_effects` / `restore_effects` to isolate
sub-expressions and recover their accumulated `EffectRow`. This is the core
mechanism: effects are inferred while walking expressions, then checked against
the declared `needs` row at function, handler, and callback boundaries.

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

When a HOF handles a callback's declared effects internally, those effects do
not escape to its caller. The callback's effects live on its arrow and are
realized when the HOF invokes it; an enclosing `with` can discharge them before
the HOF boundary.

Call-site checking does not subtract callback effects from the HOF's declared
result row. A named result effect is unconditional, even when the supplied
callback is pure:

```saga
fun use_repo : (Unit -> a needs {Repo}) -> a needs {Repo}
```

If the result effects depend on the actual callback, that relationship must be
expressed with a shared open row:

```saga
fun run : (Unit -> a needs {..e}) -> a needs {..e}
```

This prevents a pure callback from erasing an effect the HOF performs itself.

### Row Polymorphism

Open effect rows (`..e`) allow functions to be polymorphic over effects:

```
fun run : (f: Unit -> Unit needs {Fail, ..e}) -> Unit needs {..e}
run f = f () with { fail msg = () }
```

The row variable `..e` captures any extra effects from the callback and forwards them to the caller. In unification, when one row is open and the other has extras, the tail variable binds to the extras.

Rows can forward more than one independent source:

```saga
fun both :
  (Unit -> Int needs {..a}) ->
  (Unit -> Int needs {..b}) ->
  Int needs {..a, ..b}
both fa fb = fa () + fb ()
```

Forwarding only one tail would silently drop the other callback's unknown
effects, so annotated functions must forward every open callback tail they call.

### Effect-Polymorphic Traits

Trait methods define their effect capability. Impl methods are bounded by the
trait method's row at impl registration time:

| Trait method row | Impl method may use |
| --- | --- |
| pure, e.g. `foo : a -> Int` | no effects; an effectful impl is a type error |
| closed/named, e.g. `foo : a -> Int needs {Config}` | only the named effects |
| open, e.g. `foo : a -> Int needs {..e}` | any effects, supplied by the impl |

This keeps generic callers modular: adding a new impl in another module cannot
change an existing generic function's effect row.

Concrete trait dispatch uses per-impl, per-method facts stored in
`ImplInfo.method_effects`. A call like `foo 42` emits the selected impl
method's effects into the caller, with per-method precision so a pure sibling
of an effectful method stays pure.

Generic dispatch over an open-row trait method surfaces the unknown impl
effects as the constrained type variable's row tail:

```saga
trait Foo a {
  fun foo : a -> Int needs {..e}
}

fun generic_foo : a -> Int needs {..a} where {a: Foo}
generic_foo x = foo x
```

The `..a` tail reuses the type variable id for `a`. While `a` is abstract it
means "effects supplied by the selected `Foo a` impl." After specialization at
a concrete type, the tail resolves to that type and is no longer an effect row;
concrete effects must come from concrete impl method facts instead.

Open trait rows must be forwarded even if the body wraps the call in `with`.
The generic function cannot name the open row's effects, so it cannot soundly
handle them internally.

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

After inferring all clauses of a function body, the accumulated `EffectRow`
(merged across clauses) is checked against the declared `needs` row from the
annotation. This uses `check_effects_via_row`: if the declared row is open, any
extras are allowed; if closed, undeclared effects are an error.

Function boundary checks also enforce forwarding obligations:

- callback parameters with open rows must have their row tails forwarded by the
  function's own `needs` row
- calls to open-row trait methods on abstract where-bound variables must
  forward the corresponding `..a` tail

### Key Files

- `typechecker/mod.rs` -- `Type::Fun`, `EffectRow` (with `empty`, `merge`, `subtract`), `EffectMeta`, `effects_from_type`, `ImplInfo.method_effects`
- `typechecker/infer.rs` -- `infer_expr`, App absorption logic, lambda effect propagation, concrete trait impl effect emission, open-row trait forwarding surfacing, handler binding detection in `infer_block` (`extract_handler_info`, `handler_info_from_type`)
- `typechecker/effects.rs` -- `check_effects_via_row`, effect op lookup/instantiation
- `typechecker/handlers.rs` -- `infer_with`/`infer_with_inner`, handler subtraction
- `typechecker/check_decl.rs` -- `collect_annotations` (builds EffectRow on innermost arrow), `check_fun_clauses` (body effect check and forwarding requirements), `innermost_effect_row` helper
- `typechecker/check_traits.rs` -- impl body effect checking, trait method capability bounds, per-method impl effect collection
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

The evidence vector is a BEAM tuple of per-effect entries. Effect arguments
are part of an entry's identity, so two applications of one family occupy
independent slots:

```erlang
{
  {'Std.Fail.Fail<Std.String.String>', {StringFailHandler}},
  {'Std.Fail.Fail<Std.Int.Int>',       {IntFailHandler}},
  {'Std.IO.Stdio',                     {EprintHandler, PrintHandler, ReadHandler}}
}
```

Each entry is `{EffectAtom, OpTuple}`. Within an `OpTuple`, op closures are
sorted alphabetically by op name. An initial closed-row vector is canonical.
At a call boundary it can instead be reframed into the callee's static order,
followed by the caller entries not selected for that prefix. Consequently the
meaning of the vector is:

```text
{callee-shaped positional static prefix..., tagged forwarded remainder...}
```

This flat representation was chosen over a nested `{StaticSlots, OpenTail}`
frame. It keeps the CPS function ABI unchanged while allowing a caller to
select `Repo UsersDb` for a generic `Repo db` callee and forward
`Repo DataDb` in the same vector.

The vector is always tagged. Closed-row op calls technically don't need the tag (the static indices suffice), but tagging keeps cross-module ABI uniform and makes runtime panics self-describing.

#### Op Call Lookup

- **Closed row (statically known indices):** `element(OpIdx, element(2, element(EffectIdx, Evidence)))`. Three constant-time element loads.
- **Open row (`..e`, callee doesn't know full row):** call out to `std_evidence_bridge:find_evidence/2` (defined in `src/stdlib/evidence.bridge.erl`), which walks the tuple by atom comparison. Exact applied tags win. If a handler was installed by code polymorphic in its effect argument, a unique same-family entry may satisfy the lookup; zero matches or multiple matches error. O(n) where n is the number of effects in scope, typically ≤5.

#### Extending Evidence at `with`

`expr with handler` extends the inherited evidence vector by inserting a new entry in canonical position:

```erlang
NewEvidence = call 'std_evidence_bridge':'insert_canonical'(
  OldEvidence,
  {'Std.Fail.Fail', {FailHandler}}),
apply Body(Args, NewEvidence, ReturnK)
```

`insert_canonical` finds the right position by tag compare, builds a new tuple, replaces an existing entry if the tag already exists (innermost-wins semantics fall out without explicit mask machinery). The inherited evidence is unchanged. In an open frame, `insert_static/3` instead canonicalizes only the known positional prefix and leaves the unknown tagged tail in place; globally sorting an open frame would invalidate its static indices.

#### Projection at Call Boundaries

Effectful function calls thread evidence as a single argument followed by
`_ReturnK`. Closed-row callees can still use exact-tag projection. Generic and
open-row calls use caller-side reframing:

```erlang
CallEvidence = call 'std_evidence_bridge':'reframe_evidence'(
  Evidence,
  1,
  [2]),  %% caller slot selected for the callee's first static requirement
apply Callee(Args, CallEvidence, ReturnK)
```

Selectors are either one-based positions in the caller's static prefix or
concrete applied-effect atoms found in its tagged remainder. Selected entries
are ordered as the callee expects; every unselected entry is appended as its
open tail. A generic callee therefore uses ordinary positional lookup and does
not receive a runtime type witness. Reframing costs one tuple allocation at a
cross-row call boundary.

#### What Saga Doesn't Use From Koka

The convention is inspired by Koka's evidence passing (Xie & Leijen 2021), with deliberate simplifications enabled by Saga's effect semantics:

- **No `hevv` per entry.** Saga has no non-scoped resumes, so each evidence entry doesn't need to carry the saved evidence at handler installation.
- **No marker integers.** No prompt mechanism.
- **No mask levels.** Saga has no surface syntax for accessing shadowed outer handlers; innermost-wins covers all cases.
- **No yield checks.** Saga's CPS is user-level; there's no equivalent of Koka's `is_yielding` flag.
- **Flat caller-side reframing**, rather than nested open wrappers. Koka projects via `@open` wrappers; Saga selects a positional static prefix and retains unselected entries as a tagged tail.

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

Per-call effect metadata is computed once by a pre-pass and stored in
`CallEffectMap` (keyed by AST `NodeId`). The lowerer is a read-only consumer:
at every effectful call site, it reads `CallEffectInfo` from the map to
determine projection, evidence layout, and op-call indices. There is no inline
call-shape recognition at lowering time -- adding a new call shape (e.g.
`DictMethodAccess`, lambda-headed call) means teaching the populator one new
branch, not auditing every dispatcher.

`CallEffectInfo` has three runtime shapes:

- `Pure` -- direct call; no evidence and no return continuation
- `StaticOps` -- closed-row CPS call; evidence can be projected to the static
  effect set
- `RowForwarded` -- open-row CPS call; caller evidence is reframed into the
  callee's positional static prefix plus its unselected tagged tail

`src/codegen/optimize.rs` records optional optimizer facts before lowering.
Those facts are independent metadata that the lowerer may consume for direct
fast paths. Missing facts always fall back to the classified evidence/CPS path.
Optimization facts are not a second lowered program.

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
- `codegen/handler_analysis.rs` -- conservative `resume`-position analysis for static handler optimizations.
- `codegen/optimize.rs` -- post-classifier optimizer fact collection: handler analysis, public helper facts, and HOF direct-specialization facts.
- `codegen/lower/evidence.rs` -- `EvidenceLayout`, `build_evidence_entry`, `insert_canonical`, `insert_static`, `find_evidence`, `project_evidence`, `reframe_evidence`, `evidence_index_of`. Compile-time helpers for emitting the runtime evidence operations.
- `codegen/lower/mod.rs` -- `Lowerer`, `FunInfo`, call-site emission. Single helper for effectful calls regardless of head shape (Var, QualifiedName, DictMethodAccess, lambda).
- `codegen/lower/effects.rs` -- `lower_effect_call` (op call lookup against evidence), `lower_with` (extends evidence via `insert_canonical`), `build_op_handler_fun`, `build_beam_native_op_fun`, `lower_handler_def_to_tuple`.
- `codegen/lower/hof.rs` -- generated direct HOF entries for externally-direct callbacks.
- `codegen/lower/exprs.rs` -- value/tail lowering helpers, `lower_handle_binding`, `is_handler_value`.
- `codegen/lower/init.rs` -- populates `FunInfo` (with `EvidenceLayout`) from type schemes via `arity_and_effects_from_type`.
- `stdlib/evidence.bridge.erl` -- runtime helpers `find_evidence/2`, `insert_canonical/2`, `insert_static/3`, `project_evidence/2`, and `reframe_evidence/3` for the operations that don't inline cleanly.

### Optimization Opportunities

Already in place:

- **Pure functions:** no CPS transform at all -- compiled as normal Core Erlang functions with zero overhead. Pure-vs-effectful detection is centralized in `CallEffectInfo`.
- **Row polymorphism:** no runtime type witness or specialization is needed. The caller selects the instantiated static entries and forwards the remainder through `_Evidence`.
- **Canonical-ordered indices:** for closed rows, op call sites emit static `element/2` loads rather than runtime atom comparisons. The runtime `find_evidence` helper is only used for open rows.
- **Innermost-wins via canonical insertion:** same-effect nesting handled by tuple replacement, not mask machinery.
- **Static tail-resume handler ops:** when a static handler arm is proven to
  tail-resume directly, matching op calls can lower as direct values instead of
  evidence lookup + handler closure application.
- **Static helper variants:** simple same-module/imported helpers whose
  escaping effects are covered by active static handler facts can use direct
  variants or inlining, with conservative guards for recursive, multi-clause,
  private, or residual-effect cases.
- **Direct HOF specializations:** higher-order functions can get generated
  direct entries when callback arguments are externally direct and the HOF's
  own effects are covered by callback-absorbed effects.

Future work:

- **Trait/dictionary specialization:** concrete trait dispatch can use
  per-method impl effect facts and known dictionaries to skip generic dict
  traversal. Pure trait methods are globally pure by the typechecker invariant;
  open-row concrete dispatch must use `ImplInfo.method_effects`, not a resolved
  `..a` tail.
- **Direct-native fast path:** for BEAM-native ops (Process, Ref, Timer, etc.) called outside of user-defined handlers, fold the closure call into a direct native call. The `use_direct_native_fast_path` hook in `effects.rs` is currently a no-op stub.
- **Closed-row specialization:** when the entire program is closed-row (common for top-level entry points), specialize op call emission to skip the runtime tag and use direct positional indexing without the `{Tag, OpTuple}` wrapping. Speculative perf — needs benchmarking to justify.
- **Open-row lookup memoization:** for loops that repeatedly call the same op under an open row, cache the resolved handler closure once outside the loop. Probably not worth doing until a real workload shows it.
- **Dead effect elimination:** if a handled effect is never called, strip the handler.
