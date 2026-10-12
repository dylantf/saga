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

### One Application Per Effect Family

An effect is identified by its **family** (`Fail`), whatever its type
arguments. `Fail String` and `Fail Int` are the same effect at two types, not
two effects: an operation reaches the nearest handler for its family. The type
arguments are still checked. Two instances that must coexist are declared with
`neweffect` (`neweffect UserRepo = Repo UserDb`), which mints a distinct
nominal effect with no type parameters of its own; a `neweffect` must fix
every type argument of its source.

So a row holds **at most one application of a family**. Wherever two entries
of one family would end up in the same row their arguments are unified, and a
mismatch is a type error that names both applications and suggests
`neweffect`:

| Where rows are built or combined | Code |
| --- | --- |
| a declared `needs {...}` (function, trait method, impl, handler, operation, callback type) | `push_declared_effect`: writing a family twice is an error unless the two are identical |
| effects accumulating while a body is inferred | `emit_effect` / `emit_effects` |
| two rows merged (handler `needs`, clauses of a local function) | `merge_rows` |
| branch, list-element and tuple rows joined | `join_effect_rows` |
| a body's row checked against its declared row | `check_effects_via_row` |
| any row about to be unified, and any row variable being bound | `normalize_row`, `bind_row_checked` |
| the type of a finished function | `check_type_rows` |

Binding a row variable is the subtle case. `{Fail Int, ..r}` with
`r := {Fail String}` must fail, and with `r := {Fail Int}` it collapses to one
entry. The substitution cannot see the row a variable sits in when it is
bound, so every open row records its entries against its tails
(`Substitution.row_companions`, filled by `normalize_row` and on
instantiation): "if `r` contains `Fail`, it is `Fail Int`". `bind_row_checked`
checks the bound row against those entries and passes them on to the new
tail. A variable may have several companions of one family, from different
rows (`(.. needs {Fail a, ..r}) -> .. needs {Fail b, ..r}` does not force
`a = b`; it only does once `r` is known to contain `Fail`).

These obligations live in the substitution, not in the type, so a row
variable is only generalised when its type shows them. A local binding whose
row variable has an obligation the type does not show stays monomorphic in
that variable; an unannotated top-level function in that position is an error
asking for a signature (`unexpressed_row_companion`).

### Where Effects Live on Curried Functions

Effects go on the **innermost** arrow (closest to the return type):

```
fun greet : String -> String -> Unit needs {Log}
=> Fun(String, Fun(String, Unit, {Log}), {})
```

Partial application `greet "hi"` returns `Fun(String, Unit, {Log})` -- effects are preserved until full saturation.

Lambdas and local functions follow the same rule: the row of what the body
performs goes on the arrow of the **last parameter of that lambda**
(`curried_lambda_type` in `infer.rs`).

```
fun a b -> a + b + skip! ()             => Fun(a, Fun(b, Int, {Skip}), {})
fun a -> fun b -> a + b + skip! ()      => Fun(a, Fun(b, Int, {Skip}), {})
fun a -> { skip! (); fun b -> a + b }   => Fun(a, Fun(b, Int, {}), {Skip})
```

The third one performs `Skip` when `a` is supplied, before the inner lambda
exists, so it is not an `a -> b -> Int needs {Skip}`. Rows are compared arrow
by arrow by the effect-row rule at coercion positions (see "Effect
Subtyping" below). A local
multi-clause function (`let go 0 = ..` / `let go m = ..`) gets the union of
its clauses' effects, like a top-level one.

### Computation Types

`infer_expr` returns the value `Type` and emits performed effects into
`Checker.effect_row`. The accumulator is a row: it holds one entry per effect
family (see above), and it keeps the still-open tails of the functions that
were called, so `fun () -> f ()` with `f : Unit -> a needs {..e}` has the row
`{..e}` rather than being pure. Callers use `save_effects` / `restore_effects`
to isolate sub-expressions and recover their accumulated `EffectRow`. This is the core
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

Two closed effect rows are the same type only when they are equal. The one
exception is a *coercion position*, where a value of one type is used where
another is expected: there a function with fewer effects may be used where
more are allowed.

- A pure function can be passed where an effectful callback is expected.
- An effectful function CANNOT be used where a function with fewer effects is
  expected, at any position.
- Away from a coercion position the rows must be identical in both directions:
  a `List (Unit -> Int)` is not a `List (Unit -> Int needs {Skip})`, nor the
  reverse.

Coercion positions are: a direct call argument, an annotated `let` and a type
ascription, a function or lambda body against its return type, `if` / `case`
/ `do ... else` branches and block results against the expected type, record
field initialisers and updates, handler arm and `return` clause bodies, and
the elements of tuple, list and anonymous-record literals written at one of
those positions. Only the row on the value's own arrows is coerced (compared
arrow by arrow along a curried type). A row nested in a type-constructor
argument, a function parameter type, a record field type or an effect's type
argument is "at depth" and must match exactly; there is no variance tracking.

```saga
fun run : (Unit -> Int needs {Skip}) -> Int needs {Skip}

run pure_fn              # ok: fewer effects at a call argument
take_list [pure_fn, eff] # ok: literal elements at a call argument
let fs = [pure_fn]       # List (Unit -> Int)
take_list fs             # error: rows differ inside `List`
```

Implementation (`src/typechecker/unify.rs`): `unify_effect_rows` still accepts
two closed rows when either is a subset of the other, but records every such
acceptance of unequal rows as a `RowSubsumption` with the path taken through
the types. The entry points that carry a span (`unify_at`, `unify_nested_at`,
`coerce_at`, `coerce_expected_first_at`) judge the recorded subsumptions
against their `RowPosition` and return a type error, prefixed
`effect row mismatch:`, for the first violation. Three messages exist: rows
differing at depth, an effectful function where a less effectful one is
expected at a coercion position, and rows differing directly at a position
that is not a coercion position. The spanless `unify` does not judge rows.

Open rows (with a `..e` tail) are unaffected: a row variable is instantiated
by unification at any depth.

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
handle them internally. For an effect with type parameters this is an error
rather than a redundant handler: the impl chosen by the caller could perform
that effect at another type. It is accepted only when the function's own row
names the effect next to the tail (`needs {Fail Int, ..a}`), and then a caller
whose impl performs `Fail String` is rejected at the call, where the impl's
effects and the function's row meet.

#### Open-row methods used as values

Everything above is about calls that supply every argument. An open-row
method that is only *referenced* performs nothing yet: its impl's effects
belong on the arrow of the value.

```saga
impl Foo for Text needs {Fail String} { foo _ = fail! "text" }

apply_open foo Text                  # performs {Fail String}
pick () = foo                        # pick : Unit -> (Text -> Int needs {Fail String})
Box { run: foo }                     # the field's row must allow {Fail String}
```

The impl is usually not known where the name is inferred (`foo` is
instantiated at a fresh type variable; the argument `Text` comes later), so
the reference is recorded (`open_row_refs.rs`, `TraitState.open_row_refs`)
with the row variable its arrow carries, and settled later:

- **The type becomes known** (checked after each application, before a `with`
  subtracts, and when the enclosing declaration ends): the row must contain
  the impl's effects for that method. An unconstrained row is bound to exactly
  those effects; a row that already names one of the families has its
  arguments unified (a mismatch is the family-conflict error); a closed row
  lacking one is an error at the reference that names the impl's effects.
- **The type stays a variable** (it is under a `where` bound, or the
  declaration or `let` is about to generalise it): the row becomes `..a`, the
  same form a call produces, and the forwarding rule above applies.

The same is done for a function whose own row is `..a`
(`generic_foo` above, or a `let`-bound `foo`) when it is referenced without
all its arguments: its `..a` is replaced by a row variable that is settled the
same way. A generic function may also return such a value
(`fun via : a -> (a -> Int needs {..a}) where {a: Foo}`, `via _ = foo`);
`via Text` then has the type `Text -> Int needs {Fail String}`.

Multi-parameter traits are not covered, here or at calls.

#### Effect arguments in a method's or an operation's signature

A type variable used as an effect's argument in a trait method's signature
(`fun run : a -> (Unit -> Int needs {Fail e, ..r}) -> Int needs {..r}`), or in
an effect operation's, is chosen by each caller of the method or performer of
the operation. An impl method or handler arm is checked against the signature
once, so it must work for every choice: after its body is inferred, the
variable must still be a variable, must not have been merged with another
effect-argument variable of the signature, and must not appear in an effect
the body performs outward or (for an arm) in the handler's answer type, where
it would be pinned later (`check_effect_arg_vars_abstract`,
`check_effect_arg_vars_stay_inside`). An argument left out (`needs {Fail}`)
counts the same. Variables that stand for the trait's or the effect's own
parameters are exempt: `impl Run String for T` and `handler h for Scope
String` say what they are, and callers agree by the ordinary rules.

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
layer from `inner_effs` (`EffectRow::subtract_entries`, by family), then merge
in any effects performed by this layer's arm bodies that escape outward. Open
tails of `inner_effs` stay in the result: a handler cannot discharge effects
it cannot name.

Because a handler is found by family, **every** operation of that family
performed inside the handled expression reaches it. The typechecker therefore
makes sure none can do so at a type the handler was not written for
(`resolve_handled_effect_entries`):

- If the expression's row names the family, that entry is the one handled. A
  handler declared for specific arguments (`handler h for Fail Int`, a value
  of type `Handler (Fail Int)`) must agree with it; a handler for `Fail Int`
  around a `Fail String` computation is an error, not a handler that is
  skipped. A handler value must have a known `Handler (...)` type where it is
  installed.
- An open tail that inference is still free to refine is bound to contain the
  family at the handled arguments. In an unannotated
  `h f = f () with { fail n = resume (n + 1) }`, `f` becomes
  `Unit -> a needs {Fail Int, ..}`.
- An open tail fixed by a declared signature cannot be refined: the caller
  chooses it. For an effect with type parameters the `with` is rejected unless
  the signature names the family next to that tail.

```saga
fun h : (Unit -> Int needs {..r}) -> Int needs {..r}
h f = f () with { fail n = resume (n + 1) }       # error: `..r` might contain `Fail`

fun catch_it : (Unit -> Int needs {Fail e, ..r}) -> Int needs {..r}
catch_it f = f () with { fail _ = 0 }             # ok
```

In `catch_it`, `{Fail e, ..r}` obliges every caller to keep `r` consistent
with `Fail e` (one application per family), so no other `Fail` can hide in
`r`. Effects without type parameters keep the old behaviour around a declared
tail: the handler may catch operations the tail turns out to perform, and the
signature still forwards them, which is imprecise but cannot mismatch a type.

The declared row variables are tracked in `Checker.rigid_row_vars`: the tails
written in the enclosing function's signature, in the trait method an impl
implements, and in the operation a handler arm implements.

This has one important consequence: sibling items in a surface `with {...}`
block do not satisfy each other's arm-body effects. If an inline arm body uses
`Log`, that `Log` must be handled by an outer scope after desugaring, not by a
sibling item later in the same surface block.

### Function Body Checking

After inferring all clauses of a function body, the accumulated `EffectRow`
(merged across clauses) is checked against the declared `needs` row from the
annotation. This uses `check_effects_via_row`: a family both rows name is one
application, so its arguments are unified; if the declared row is closed,
undeclared effects are an error; if it is open, extras are allowed, except
that an effect with type parameters must be named. The tail is the caller's
row and says nothing about what this body performs, so an unnamed
`Fail String` would be invisible to callers, who could then install a
`Fail Int` handler around the call.

A call emits the callee's row into the accumulator, tails included. The one
tail left out is a row variable that the callee's signature does not tie to
any argument (`fun f : Unit -> Int needs {Log, ..r}`): each call instantiates
it afresh, nothing can bind it, and emitting it would only leave an
unannotated caller with an open row of its own. A recursive call to a function
still being inferred performs that function's own row variable, which is
likewise dropped when the function's row is built.

Function boundary checks also enforce forwarding obligations:

- callback parameters with open rows must have their row tails forwarded by the
  function's own `needs` row
- calls to open-row trait methods on abstract where-bound variables must
  forward the corresponding `..a` tail

A row variable or an effect argument written in a signature is chosen by the
caller, so the body must work for every choice. After the body is inferred
(`check_rigid_row_vars_abstract`, `check_effect_arg_vars_abstract`):

- a declared row variable must not have been unified with a row naming an
  effect that has type parameters, nor closed (`h f = only_pure f` with
  `f : .. needs {..r}`); it may be widened with effects that take no type
  argument, which is how a callback is passed where more effects are allowed.
  Handler arms may close an operation callback's row variable: the callback
  finds those effects where the operation was performed.
- a declared row variable must not have been used in a row together with a
  type-parameterised effect that the signature does not name next to it
  (`catch_it (fun () -> fail! "s" + k ())` with `k : .. needs {..t}` needs
  `needs {Fail String, ..t}` on `k`'s type).
- a type variable written as an effect argument (`needs {Fail e}`) must not
  have been pinned to a type or merged with another one. An argument left out
  (`needs {Fail}`) is a hole the body fills in; it stays one unknown type,
  not generalised, until the body has been checked.

These matter because impl method bodies are checked before function bodies,
against the declared signatures.

### Key Files

- `typechecker/core.rs` -- `Type::Fun`, `EffectRow` (with `empty`, `subtract_entries`), `Substitution` (row bindings and `row_companions`)
- `typechecker/mod.rs` -- `emit_effect` / `emit_effects` (the accumulator), `EffectMeta`, `effects_from_type`, `ImplInfo.method_effects`
- `typechecker/infer.rs` -- `infer_expr`, App absorption logic, lambda effect propagation, concrete trait impl effect emission, open-row trait forwarding surfacing, handler binding detection in `infer_block` (`extract_handler_info`, `handler_info_from_type`)
- `typechecker/effects.rs` -- `check_effects_via_row`, effect op lookup/instantiation
- `typechecker/handlers.rs` -- `infer_with`/`infer_with_inner`, `resolve_handled_effect_entries` (which application a `with` handles, and the open-tail rule), handler subtraction
- `typechecker/check_decl.rs` -- `collect_annotations` (builds EffectRow on innermost arrow), `check_fun_clauses` (body effect check and forwarding requirements), `innermost_effect_row` helper
- `typechecker/check_traits.rs` -- impl body effect checking, trait method capability bounds, per-method impl effect collection
- `typechecker/unify.rs` -- `unify_effect_rows` (row matching, tail binding), `normalize_row` / `bind_row_checked` / `merge_rows` (one application per family), `check_rigid_row_vars_abstract`, `check_effect_arg_vars_abstract`
- `typechecker/effect_family_tests.rs` -- tests for the family rule and the handler/open-tail rule

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

### Authoritative Evidence ABI

The compiler keeps inferred body effects separate from the runtime convention
of a callable:

- `EvidenceAbi` describes the canonical static prefix and whether a tagged
  open tail follows it.
- `CallableAbi` describes user arity and whether the callable receives
  `_Evidence` and `_ReturnK`.
- `EvidenceFrame` identifies the Core variable currently carrying a particular
  `EvidenceAbi`.
- `EffectAbiPlan` records declaration ABIs, instantiated call ABIs, and
  contextual function-value ABIs by `NodeId`.
- `EvidenceReframePlan` is the single source-to-target slot mapping used by
  calls and CPS adapters.

A callable body indexes evidence using its `CallableAbi`, never the narrower
set of effects that happened to be performed in that body. Handler insertion
updates the runtime tuple and the compile-time `EvidenceFrame` together.
Exported `CallableAbi` metadata is preserved through imports and re-exports
and is used as declared at every occurrence.

The plan is completed in two pre-lowering stages. Call classification records
declarations, inferred callable views, and instantiated call targets. A
contextual pass then propagates the consuming declaration's expected type
through calls and containers and records each function value's implementation
ABI separately from its exposed boundary ABI. Closed callback declarations
stay closed; an open declaration such as `{Skip, ..e}` keeps its pinned static
prefix and open tail even when the stored expression has inferred a concrete
closed set such as `{Foo, Skip}`. Core lowering only reads and asserts this
completed metadata. Imported named-handler bodies are included under their
defining module's semantic context; compiler intrinsics retain their explicitly
registered native callback convention.

### Evidence Vector Representation

The evidence vector is a BEAM tuple of per-effect entries. An entry's tag is
the effect's canonical family name; type arguments are not part of it, so
`Fail String` and `Fail e` are both tagged `'Std.Fail.Fail'`. This is sound
because a row holds one application of a family (see "One Application Per
Effect Family"). A `neweffect` instance is a separate nominal effect and is
tagged with its own name:

```erlang
{
  {'Main.UserRepo', {UserLoadHandler}},   %% neweffect UserRepo = Repo UserDb
  {'Std.Fail.Fail', {FailHandler}},
  {'Std.IO.Stdio',  {EprintHandler, PrintHandler, ReadHandler}}
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
frame because it keeps the CPS function ABI unchanged.

The vector is always tagged. Closed-row op calls technically don't need the tag (the static indices suffice), but tagging keeps cross-module ABI uniform and makes runtime panics self-describing.

#### Op Call Lookup

- **Closed row (statically known indices):** `element(OpIdx, element(2, element(EffectIdx, Evidence)))`. Three constant-time element loads.
- **Open row (`..e`, callee doesn't know full row):** call out to `std_evidence_bridge:find_evidence/2` (defined in `src/stdlib/evidence.bridge.erl`), which walks the tuple by atom comparison and raises `{evidence_tag_not_found, Tag}` when no entry has that tag. O(n) where n is the number of effects in scope, typically ≤5.

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

Selectors are one-based positions in the caller's static prefix, or effect
tags (atoms) looked up in its tagged remainder. Selection never changes an
entry's tag. Selected entries are ordered as the callee expects. The reframe plan also names which unselected source
static positions instantiate the target row variable: a closed caller's extra
slots can become that tail, while an already-open caller forwards its tagged
tail without leaking handled or omitted declaration-prefix slots into it.
Closed projection uses the same selector language as open-row reframing.
When a closed CPS function value is passed through an open callback slot,
`select_evidence` uses the selector language above but drops every
unselected entry. The open tail belongs to the adapter ABI and must not enter
the closed function: its local handler insertion and positional lookups assume
a canonical closed vector.
A handler installed inside code generic in an effect argument carries the same
tag (`Abort`) as one installed by concrete code, so generic and concrete code
agree on the frame without any runtime type witness. Reframing costs one tuple
allocation at a cross-row call boundary.

A partial application's runtime evidence shape comes from its compiled head,
not solely from its instantiated result type. For example, partially applying
`route : ... needs {Skip, ..e}` produces a closure whose static prefix remains
`Skip` with an open tail, even when inference resolves `..e` to a concrete
closed set at that occurrence. Treating the closure as the canonical union of
that set would move `Skip` away from the slot used by the compiled `route`
body.

A lambda placed into a callback slot likewise uses the **expected callback
row** as its positional ABI, even when the lambda body performs only a subset
of those effects. Its inferred row contributes additional effects absorbed by
an expected open tail, but it cannot remove an unused expected slot. Otherwise
the caller and lambda can assign different meanings to the same index (for
example, a `{Repo, Rollback e}` callback that performs only `Rollback` must
still read it from slot 2).

#### Effect-Operation Callbacks With Open Tails

An effect operation may accept a callback whose row mixes handler-provided
effects with an open tail:

```saga
fun transaction :
  (Unit -> Result a e needs {Repo, Rollback e, ..r})
  -> Result a e
  needs {..r}
```

The handler invoking that callback supplies the named static frame (`Repo` and
`Rollback e`). The original perform site supplies `..r`. The callback closure
therefore retains the perform-site evidence, but does not use it directly:
`append_tail/2` keeps the handler's call-time frame and appends only captured
entries whose tags it does not already contain. This lets a transaction-scoped `Repo` shadow the outer
repository while unrelated effects in `..r` continue to the callback.
Capturing the whole perform-site frame as the callback's active frame would
incorrectly discard both nested handlers.

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

Effect ABI metadata is computed once by a pre-pass and stored in
`EffectAbiPlan` (keyed by AST `NodeId`). It contains declaration ABIs,
`CallEffectInfo` entries, and the inferred/implementation/boundary ABIs of
function values. The lowerer consumes those facts and maps its current
`EvidenceFrame` to each planned target through `EvidenceReframePlan`. There is
no inline call-shape recognition at lowering time -- adding a new call shape
(e.g. `DictMethodAccess`, lambda-headed call) means teaching the planner one
new branch, not auditing every dispatcher.

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

- `codegen/runtime_shape.rs` -- `EvidenceAbi`, `CallableAbi`, handler-installation and reframe plans, selector compatibility, and slot resolution.
- `codegen/call_effects.rs` -- `EffectAbiPlan`, `CallEffectInfo`, and the planner for declaration, call, and function-value ABIs.
- `codegen/handler_analysis.rs` -- conservative `resume`-position analysis for static handler optimizations.
- `codegen/optimize.rs` -- post-classifier optimizer fact collection: handler analysis, public helper facts, and HOF direct-specialization facts.
- `codegen/lower/evidence.rs` -- `EvidenceFrame` and thin Core emitters for the six runtime bridge operations.
- `codegen/lower/calls.rs` -- consumes planned call `CallableAbi` values and executes `EvidenceReframePlan` for every effectful head shape.
- `codegen/lower/effects/ops.rs` -- resolves static or dynamic operation slots through `EvidenceAbi`.
- `codegen/lower/effects/with.rs` -- installs handlers through `EvidenceInstallPlan` and updates the active `EvidenceFrame`.
- `codegen/lower/hof.rs` -- generated direct HOF entries for externally-direct callbacks.
- `codegen/lower/exprs.rs` -- value/tail lowering helpers, `lower_handle_binding`, `is_handler_value`.
- `codegen/lower/init.rs` -- registers local/imported `FunInfo` entries carrying `CallableAbi` plus non-ABI HOF parameter metadata.
- `stdlib/evidence.bridge.erl` -- runtime helpers `find_evidence/2`, `insert_canonical/2`, `insert_static/3`, `select_evidence/2`, `reframe_evidence/3`, and `append_tail/3` for the operations that don't inline cleanly.

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
