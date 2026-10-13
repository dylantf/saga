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
- `EffectAbiPlan` records declaration ABIs and one `CallEffectInfo` per call,
  by `NodeId`.
- `EvidenceReframePlan` is the single source-to-target slot mapping used by
  calls to named functions.

A named function's body indexes evidence using its declared `CallableAbi`,
never the narrower set of effects that happened to be performed in that body.
Handler insertion updates the runtime tuple and the compile-time
`EvidenceFrame` together. Exported `CallableAbi` metadata is preserved through
imports and re-exports and is used as declared at every occurrence.

The plan is completed by one pre-lowering pass, call classification, which
records declarations and the shape of every call. Core lowering only reads
it. Imported named-handler bodies are included under their defining module's
semantic context; compiler intrinsics retain their explicitly registered
native callback convention.

### Function Values

A function *value* is represented from its own type, never from the type its
context expects (`codegen/lower/tagged.rs`):

| Value | Representation |
|-------|----------------|
| Own type is pure | bare Erlang fun of the user arity |
| Own type is effectful or open-row | `{'$saga_cps', Fun}`, where `Fun` takes `(args..., Evidence, K)` |
| Named function, called directly | unchanged: `f/N` if pure, `f/(N+2)` if effectful |

A lambda is tagged when an arrow consumed by its own (flattened) parameters
carries effects or an open row. A named effectful function used as a value,
or partially applied, becomes a tagged closure that reframes the evidence it
is called with into the function's declared layout. A dictionary slot holds a
bare fun or a tagged one according to the method's convention.

The body of a tagged closure uses an open `EvidenceAbi` with no static prefix:
every operation finds its handler by tag, so a caller passes its own frame
unchanged and needs no knowledge of the layout the closure was compiled
against. Positional layout exists only for named functions, whose callers
know the declared row.

A call through a function value is classified from the callee's type:

- **Pure:** `apply F(Args)` when `F` visibly lowers to a fun of that arity;
  otherwise a guard `is_function(F, N)` selects the direct apply and
  `saga_runtime:apply_n/2` handles partial and over-application. A tagged
  closure can arrive here too: a value whose type has an open row is built
  tagged, and a consumer that instantiates the row to the empty row sees a
  pure function (`let run = fun g -> g ()` used as `run (fun () -> 3)`, or an
  element of a `List (a -> b needs {..e})` used at `e = {}`). At that
  instance it performs nothing of its own, so `apply_n` runs it with an empty
  evidence frame and an identity continuation. This is the mirror image of a
  bare fun arriving at an effectful site. An under-applied tagged closure
  stays a tagged partial application, and whoever saturates it supplies the
  frame. If a closure run this way did perform an effect (impossible in a
  well-typed program), the lookup fails with "effect E was performed where no
  handler for it is installed".
- **Effectful or open-row:** a `case` on the value. `{'$saga_cps', G}` with
  `is_function(G, N + 2)` is applied to the arguments, the caller's frame and
  the continuation. Anything else (a bare fun, which a pure function used at
  an effectful type remains, or an arity mismatch) goes to
  `saga_runtime:apply_cps/4`.

Erlang code does not go through these call shapes: a bridge calls its
callback as `F(A)`. The wrapper generated for an `@external` function
therefore passes every parameter declared with a pure function type through
`saga_runtime:bare_fun(F, N)`, which returns a fun of arity `N` unchanged and
wraps anything else (a tagged closure at a pure instance, or a fun of another
arity) in a fun that calls `apply_n`. Callbacks of more than four arguments
are passed through as they are.

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
A handler installed inside code generic in an effect argument carries the same
tag (`Abort`) as one installed by concrete code, so generic and concrete code
agree on the frame without any runtime type witness. Reframing costs one tuple
allocation at a cross-row call boundary.

Reframing applies only to calls whose callee is a named function. A call
through a function value passes the caller's frame unchanged, because a
closure body looks everything up by tag (see "Function Values"). A partial
application of a named effectful function is a tagged closure over the
supplied arguments; when it is finally called it reframes the frame it is
given into the head's declared layout, so partially applying
`route : ... needs {Skip, ..e}` still calls `route` with `Skip` in its
declared slot whatever the instantiation of `..e`.

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
`append_tail/3` takes the entries for the named effects from the handler's
call-time frame and every other entry from the captured frame. This lets a
transaction-scoped `Repo` shadow the outer repository while effects in `..r`
reach the handlers around the perform site, even when the handler arm itself
runs under another handler of the same effect.
Capturing the whole perform-site frame as the callback's active frame would
incorrectly discard both nested handlers. A lambda argument applies the
overlay at the top of its own body; any other callback value (a variable, a
named function) is wrapped in a tagged closure that applies it and then calls
the value.

#### What Saga Doesn't Use From Koka

The convention is inspired by Koka's evidence passing (Xie & Leijen 2021), with deliberate simplifications enabled by Saga's effect semantics:

- **No `hevv` per entry.** Saga has no non-scoped resumes, so each evidence entry doesn't need to carry the saved evidence at handler installation.
- **No marker integers.** No prompt mechanism.
- **No mask levels.** Saga has no surface syntax for accessing shadowed outer handlers; innermost-wins covers all cases.
- **No yield checks.** Saga's CPS is user-level; there's no equivalent of Koka's `is_yielding` flag. The places a result is inspected are `bind` and `mbind`, for a `with` whose arms use the value of `resume` (see "The Continuation of a `with`").
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

### The Continuation of a `with`

Everything after a `with` in the enclosing body is the continuation `k` of
the whole `with` expression: of its `return` clause applied to the handled
computation's result, and of any arm that aborts. There is one lowering, an
optimisation of it, and one exception (`finally`).

#### The lowering

`resume` must return the value of the `with`, so the handled computation
cannot simply be given `k` as its return continuation. It returns to the
`with`, and `k` is supplied afterwards, as a second, *meta* continuation:

```erlang
let LEv = call 'std_evidence_bridge':'lift_evidence'(Ev) in
let Ask = fun (_, R) ->                       %% ask () = (resume 1) + 10
            call 'std_evidence_bridge':'mbind'(apply R(1), fun (V) -> V + 10) in
let Ev1 = call 'std_evidence_bridge':'insert_canonical'(LEv, {'Ask', {Ask}}) in
call 'std_evidence_bridge':'bind'(<e lowered with Ev1 and the return clause>, K)
```

Inside a `with`, CPS code returns one of two things:

- a plain value: the value of the handled computation;
- a *suspension* `{'$saga_meta', M}`: an operation handled further out was
  performed. `M` takes the meta continuation `Mk`, "what happens once the
  handled computation has a value": the code after `resume` in the arms that
  resumed, then `k`.

```erlang
bind({'$saga_meta', M}, Mk) -> M(Mk);        %% at the `with`
bind(Value, Mk)             -> Mk(Value).

mbind({'$saga_meta', M}, F) ->               %% `let r = resume x; F(r)`
    {'$saga_meta', fun(Mk) -> M(fun(V) -> bind(F(V), Mk) end) end};
mbind(Value, F)             -> F(Value).

run({'$saga_meta', M}) -> run(M(fun(V) -> V end));   %% `bind` with the identity
run(Value)             -> Value.
```

- **Lifting.** `lift_evidence` wraps every operation of the inherited frame:
  `fun (Args, K1) -> {'$saga_meta', fun (Mk) -> Op(Args, fun (V) ->
  bind(K1(V), Mk))}`. Performed inside the `with`, an outer operation
  suspends; when the suspension reaches `bind`, the outer handler is called
  with a continuation that runs the rest of the handled computation *and
  then the meta continuation*. An outer handler that aborts skips both, and
  one that uses the value of its own `resume` gets the answer of both. Tags
  and positions are unchanged, so the lifted frame has the ABI of the
  inherited one; `lift_evidence` is the only function that looks at the
  frame's representation. A `with` in a pure host has no frame to lift.
- **Arms** are lowered against the lifted frame and never receive `k`: an arm
  that aborts returns its value, which reaches `bind`. `resume x` followed by
  the rest of the arm is `mbind(K(x), rest)`; in tail position it is `K(x)`.
  This is one case of the tail rule (`lower_tail`), reached from the `let`
  rule like any other performing expression.
- **No continuation** (the `with` is the last thing in a body that has none):
  `k` is the identity, `bind(result, fun v -> v)`, and nothing at all when no
  frame was lifted.
- **Nesting** needs nothing special. A `with` inside another lifts the
  already lifted frame; a suspension leaving the inner `bind` is a suspension
  of the outer level, returned from the inner `with` in tail position.

#### The optimisation: fusing `k` into the handled computation

When no arm looks at the value `resume` returns (arms that never resume, and
arms whose every `resume` is in tail position:
`with_handler_chains_continuation`), no frame of an arm is ever pending
between the handled computation and `bind`. Then:

1. every value that reaches `bind` does so through tail calls that end in
   the `return` clause or in an arm that aborts, so `bind(v, k) = k(v)` can
   be moved to those two places;
2. every suspension reaches `bind` unextended, so
   `bind(suspend(Op, Args, K1), k) = Op(Args, fun v -> bind(K1(v), k))`, and
   by (1) that continuation is `K1` built with a return continuation that
   already ends in `k`: the operation, not lifted.

So the handled computation gets the `return` clause lowered with `k` as its
own continuation (or `k` itself), aborting arms apply `k` to their value, and
nothing is lifted. This is ordinary CPS, and it is what such handlers have
always compiled to.

#### The exception: `finally`

Cleanup runs "after everything that follows `resume` has finished", also
when another handler aborts. In CPS an abort is a continuation nobody calls;
the only place it can be seen is the return of `apply K(x)` on the Erlang
stack (`try apply K(x) of V -> cleanup, V`). So an abort from further out has
to *return through* the `with`, where in the lowering above it returns only
to the aborting handler's own `bind`. Stopping it at the `finally` frame
makes it the value of `resume`, hence of the `with`, to which `k` would then
be applied.

A handler with a `finally` block (`with_handler_keeps_stack`) therefore
keeps the lowering it had before the meta continuation existed: nothing is
lifted and the handled computation is run on the Erlang stack. In tail
position of a body that has a continuation, that continuation is fused into
the handled computation as above; anywhere else the `with` is a value,
`run(<handled computation>)`, and the rest of the body is applied to it.
Inside it, `resume x` is `try run(K(x))` and the cleanup is `run`, so that a
suspension from an enclosing lifted frame is not mistaken for the end of the
computation.

A handler value only known at runtime (a parameter, the result of a call)
may have a `finally` arm, so its `with` is lowered the same way. Its arms are
built with `mbind` like any others.

#### Where a plain value is needed (`run`)

A suspension must reach a `bind` or an `mbind` through tail calls. Code that
is not CPS but calls code that is cannot pass one on, so it runs the result:
`bind` with the identity continuation. For what is run, a handler further
out that aborts returns there.

| Site | Why |
| --- | --- |
| the body of a pure lambda or local function inside an arm, when it resumes (`fun s -> (resume s) s`; `lower_fun_body`) | its type is pure, so its caller is an ordinary call |
| `finally`: the resumed computation, the cleanup, and the `with` itself outside tail position | above |
| `catch_panic`, and the thunk a spawned process runs | native code calling a function value |
| `saga_runtime:apply_n/2` on a tagged closure | a callback passed to an operation keeps its perform-site frame; an arm that sees its row as empty calls it as a pure function |

The lowerer itself has no such site: an expression that performs is the
value of a `let` or in tail position, and anything else is an internal error
(see "One rule for where effects go").

#### Operations that carry a callback

`lift_evidence` does not suspend an operation that is passed a tagged
closure: it is performed where it stands, inside the extent of the `with`.
Its handler's arm runs the callback and then resumes; by then an arm of the
inner `with` may have resumed across the end of the callback, so the inner
meta continuation has grown, and it would have to reach a continuation
closure built when the operation was performed, through the outer arm's
code, which was compiled without it. Only process state could carry it.
Everything the callback itself performs is lifted and bound as usual.

#### Known gaps

Each of the first three has an ignored test in
`tests/effect_property_tests.rs`.

- A `finally` handler, or a handler value only known at runtime, under an
  outer handler that aborts or uses the value of its `resume`: the abort
  value becomes the value of the `with` and the rest of the body runs
  (`non_tail_with_finally_handler_under_aborting_outer_handler`,
  `runtime_handler_value_under_aborting_outer_handler`). In tail position of
  a body with a continuation, `resume` in such a handler returns the caller's
  answer.
- `resume` in a pure function inside an arm (state passing): an outer abort
  after the first such `resume` becomes the value of that `resume`
  (`resume_under_lambda_under_aborting_outer_handler`). Fixing it needs the
  typechecker to put the residual effects of the `with` on that function.
- An operation that carries a callback, handled further out by an arm that
  aborts or uses the value of its `resume`: that arm sees the extent of the
  inner `with` (`callback_operation_aborted_by_outer_handler`). A callback
  held inside other data is not recognised, and the operation is lifted.
- An operation of more than seven arguments is not lifted either.
- The arms of a handler *value* perform outer operations against the frame
  where the value was built, not the lifted one.

#### Cost

A fused `with` costs what it did before. Otherwise, on each entry in an
effectful host: one closure per operation of the inherited frame, one tuple
per effect and one for the frame. Each operation of the inherited frame
performed inside costs a suspension tuple, two closures, a list append and
an `apply` more than the direct call, and that again for every enclosing
lifting `with` (a recursive function that enters one at each level makes
outer operations linear in the depth). Each `resume` whose value is used
costs one `mbind` call and, if the resumed computation suspends, two
closures.

A handled block with no return continuation at all (`{ g 3 + 100 } with h`
in a pure function) needs nothing special: normalization has turned its tail
into `{ let t = g 3; t + 100 }`, and the `let` rule below gives `g 3` the
rest as its continuation whether or not the block itself has one.

### Lowering Structure

Effect ABI metadata is computed once by a pre-pass and stored in
`EffectAbiPlan` (keyed by AST `NodeId`). It contains declaration ABIs and
one `CallEffectInfo` per `App` node. A call to a known function (top-level,
imported, block-local, or a dictionary method) is classified from the
callee's declared ABI; every other call is a call through a function value
and is classified from the head's entry in the type table. A head with
neither is an internal compiler error; nothing is assumed pure. For a known
callee the lowerer maps its current `EvidenceFrame` to the planned target
through `EvidenceReframePlan`; for a function value it passes the frame
unchanged.

`CallEffectInfo` has three runtime shapes:

- `Pure` -- direct call; no evidence and no return continuation
- `StaticOps` -- closed-row CPS call; evidence can be projected to the static
  effect set
- `RowForwarded` -- open-row CPS call; caller evidence is reframed into the
  callee's positional static prefix plus its unselected tagged tail. A call
  through a function value is this shape with an empty prefix

`src/codegen/optimize.rs` records optional optimizer facts before lowering.
Those facts are independent metadata that the lowerer may consume for direct
fast paths. Missing facts always fall back to the classified evidence/CPS path.
Optimization facts are not a second lowered program.

#### One rule for where effects go

All code reaches the lowerer in one shape. Before a body is lowered
(a function clause, a dictionary method, a handler arm or return clause, a
`finally` block, an inlined helper or handler arm), `lower/anf.rs` checks it
against the position rule in `codegen/effect_position.rs` and, if it fails,
normalizes it (`normalize::normalize_body`):

> Every operand is a value. An expression that computes (a call, an
> operator, a record update, a bit string, a branching form), and so every
> expression that performs an effect, is the value of a block-level
> `let`/statement (or a `do` binding), or is in tail position of a body or
> branch.

A value (`effect_position::is_value`) is a name, literal, lambda, handler
value or operation reference, a projection out of a value, or data built
only from values. The rule covers pure code too: the position of an
expression never depends on whether it performs.

"Performs" is one definition, `Lowerer::performs_effect`: a call the plan
classified CPS, an applied operation, a nullary operation (`number!`), a
`with`, a `resume`. It is composed over sub-expressions by one exhaustive
table (`effect_position::children`), which stops at bodies that run later
(lambdas, local functions, handler arms, the computation a `with` handles,
guards). Normalization lifts each operand that is not a value into a `let`,
in evaluation order, and turns `a && b` / `a || b` whose right operand is
not a value into an `if`. A guard that is a BEAM guard expression is exempt
and left as written. A violation that survives is an internal compiler
error, and so is an operand that is not a value when the lowerer evaluates
it (`Lowerer::operand`): a body that bypassed normalization fails loudly.

The lowerer then has two rules, each with one implementation:

- **Tail** (`lower_tail(expr, k)` in `lower/exprs/return_k.rs`). `k` is the
  continuation, or absent when the value is simply returned. An operation
  or an effectful call takes `k` as its own; a `with` inherits it; `if`,
  `case`, blocks, `do` and `receive` hand it to their branches; anything
  else is a value (`lower_expr`) to which `k` is applied. `lower_expr`
  sends the branching forms back to `lower_tail` with no continuation.
- **Let** (`lower_block` / `lower_statement` in `lower/exprs/blocks.rs`).
  For `let p = e; rest`, if `e` takes a continuation it is lowered in tail
  position with `fun p -> rest` as that continuation; otherwise `e` is
  evaluated and bound. This is the same whether or not the block has a
  continuation of its own. A `do` binding follows the same rule.

"Takes a continuation" (`Lowerer::takes_continuation`) is `performs_effect`
with one exception that concerns the continuation and not the position: a
`with` takes the rest of the block when its handled computation performs
and its handler does not keep the stack (a `finally` handler produces a plain
value; see "The Continuation of a `with`"). It must still be a `let`, never
an operand. A `resume` takes the rest of its arm like any call.

Normalization runs once, here. The generic fold runs before it and may copy
an argument that still contains an operation; the copy has a fresh id, and
the operation's resolution is found through the fold's record of where each
copied node came from. Handler arms and handled computations that have no
continuation are lowered with `k` absent; they are still in `let`/tail
position within their own body.

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
- `codegen/call_effects.rs` -- `EffectAbiPlan`, `CallEffectInfo`, and the classifier for declaration and call ABIs.
- `codegen/lower/tagged.rs` -- the tagged-closure representation of function values: tagging, the tag-dispatching call, named functions as values.
- `stdlib/runtime.erl` -- `saga_runtime:apply_n/2` and `apply_cps/4`, the slow path of calls through function values.
- `codegen/handler_analysis.rs` -- conservative `resume`-position analysis for static handler optimizations.
- `codegen/optimize.rs` -- post-classifier optimizer fact collection: handler analysis, public helper facts, and HOF direct-specialization facts.
- `codegen/lower/evidence.rs` -- `EvidenceFrame` and thin Core emitters for the six runtime bridge operations.
- `codegen/lower/calls.rs` -- consumes planned call `CallableAbi` values, executes `EvidenceReframePlan` for calls to known functions, and lowers calls through function values.
- `codegen/lower/effects/ops.rs` -- resolves static or dynamic operation slots through `EvidenceAbi`.
- `codegen/lower/effects/with.rs` -- installs handlers through `EvidenceInstallPlan` and updates the active `EvidenceFrame`. Lowers the continuation of a `with`.
- `codegen/lower/effects/handlers.rs` -- `with_handler_chains_continuation` (when the lowering may be fused), `with_handler_keeps_stack` (`finally`).
- `codegen/lower/hof.rs` -- generated direct HOF entries for externally-direct callbacks.
- `codegen/effect_position.rs` -- the position rule: the table of sub-expression positions, the effect predicate and the checker.
- `codegen/normalize.rs`, `codegen/lower/anf.rs` -- value-normal form, and where it is applied and asserted.
- `codegen/lower/exprs/` -- `lower_tail` (`return_k.rs`), `lower_block` (`blocks.rs`), `lower_expr` (`dispatch.rs`), `lower_handle_binding`, `is_handler_value`.
- `codegen/lower/init.rs` -- registers local/imported `FunInfo` entries carrying `CallableAbi` plus non-ABI HOF parameter metadata.
- `stdlib/evidence.bridge.erl` -- runtime helpers `find_evidence/2`, `insert_canonical/2`, `insert_static/3`, `select_evidence/2`, `reframe_evidence/3`, and `append_tail/3` for the operations that don't inline cleanly. `lift_evidence/1`, `bind/2`, `mbind/2` and `run/1` for the continuation of a `with`.

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
