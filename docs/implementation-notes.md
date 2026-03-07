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

## 7. `needs` Effect Set Tracking (Implemented)

The type checker tracks which effects each function body uses and checks
them against the declared `needs` clause.

**What's tracked:**

- **Direct effect calls**: `fail! "oops"` adds `Fail` to the current
  function's effect set.
- **Named function calls**: if `bar` has `needs {Fail}` and you call `bar x`,
  `Fail` propagates to your function's effect set.
- **`with` subtraction**: `expr with handler` removes the handler's effects
  from the inner expression's set before merging back.
- **Lambda propagation**: effects inside a lambda body propagate up to the
  enclosing function boundary, same as any other expression. Lambdas are
  transparent to the effect system -- they have no independent `needs`
  declaration. See below for how HOFs absorb effects from lambdas.
- **HOF effect absorption**: when a function takes a callback parameter
  annotated with `needs`, passing an effectful lambda to that parameter
  subtracts those effects from the caller's set (see `Type::EffArrow` below).
- **Function boundary check**: after inferring a function body, if it uses
  effects not in the declared `needs`, the checker reports an error. If there's
  no `needs` declaration at all, any effect usage is an error.

**Lambda propagation in detail:**

Lambdas (`fun x -> body`) do not isolate effects. Any effect call in the
body propagates out to the enclosing named function, which must either handle
it with `with` or declare it in its own `needs`.

```
# Error: foo uses Fail but has no needs declaration
foo x = fun y -> fail! "oops"

# OK: the enclosing function declares needs {Fail}
fun foo (x: Int) -> Int needs {Fail}
foo x = (fun y -> fail! "oops") x

# OK: lambda is inside a with that handles the effect
foo x = (fun y -> fail! "oops") x with { fail msg -> 0 }
```

This design keeps lambdas annotation-free (no `fun x -> expr needs {Eff}`
syntax). Effects belong to named function boundaries, which are the only
places that can carry a `needs` clause.

**HOF effect absorption (`Type::EffArrow`):**

When a function takes a callback whose type annotation includes `needs`, the
type checker stores that information in an `EffArrow` type node and uses it to
subtract those effects from the caller's propagating set at the call site.

```
# `try` declares that its callback absorbs Fail
fun try (computation: () -> a needs {Fail}) -> Result a String
try computation = computation () with {
  fail msg -> Err msg
  return value -> Ok value
}

# Caller: lambda uses Fail, but try absorbs it -- no needs required on main
main () = {
  let result = try (fun () -> fail! "something went wrong")
  ...
}
```

Mechanically: when inferring `try (fun () -> ...)`, the checker:
1. Infers the lambda body, adding `Fail` to `current_effects`
2. Resolves `try`'s parameter type to `EffArrow(Unit, a, [Fail])`
3. Subtracts `[Fail]` from `current_effects`

The result: `Fail` never reaches `main`'s boundary. If `main` had no
`needs {Fail}`, no error is reported -- because `try` absorbed it.

**Implementation: `Type::EffArrow`:**

The internal `Type` enum has two arrow variants:

- `Type::Arrow(param, ret)` -- pure arrow, no effect annotation
- `Type::EffArrow(param, ret, Vec<String>)` -- arrow with absorbed effects

`EffArrow` is produced only by `convert_type_expr` when a `TypeExpr::Arrow`
has a non-empty `needs` list (from a parsed annotation like
`computation: () -> a needs {Fail}`). All other arrow constructions (lambda
types, constructor types, trait method types) produce plain `Arrow`.

Unification treats `Arrow` and `EffArrow` identically -- effect sets are not
unified, only the type arguments. This keeps HM inference sound: a plain
lambda `fun () -> ...` unifies cleanly with an `EffArrow` parameter.

**Known remaining limitation -- `needs` on local function parameters:**

If a named function takes an effectful callback but doesn't annotate `needs`
on the parameter type, the checker can't see those effects:

```
# f's effects are invisible -- checker sees f () as a pure call
fun run (f: () -> Int) -> Int
run f = f ()
```

Callers passing an effectful lambda to `run` will have their effects
propagate up through `run` and out to the top -- which may or may not be
what they want. The fix is always to annotate the parameter with `needs`:

```
fun run (f: () -> Int needs {Fail}) -> Int
```

Full effect row polymorphism (effect variables like `needs e`) would allow
HOFs to be transparent without manual annotation, but that requires row
unification and is deferred to a later phase.

---

## 8. Type System Roadmap

### Phase 1: Traits and Impls (Implemented)

Trait definitions, impl blocks, and constraint solving are working in the type
checker. Runtime dispatch uses mangled environment keys in the interpreter.

**What's implemented:**

- **Trait registry**: stores trait name, type parameter, supertraits, method
  signatures. Methods added to env as polymorphic schemes with trait constraints.
- **Impl checking**: verifies correct methods (no missing, no extra), type-checks
  each body against the trait's expected signature with type param substituted.
- **Constraint solving**: deferred via `pending_constraints`. When a trait method
  is referenced (e.g. `describe x`), a constraint is pushed. After all types
  settle, constraints are checked against the impl registry. Unresolved type
  vars are checked against where clause bounds.
- **Where clauses**: extracted from `FunAnnotation`, mapped to type var IDs.
  Annotated functions require explicit where clauses; unannotated functions get
  automatic constraint inference. Constraints propagate to callers via scheme
  instantiation.
- **Runtime dispatch (interpreter)**: `TraitDef` registers methods as
  `Value::TraitMethod` dispatchers. `ImplDef` stores closures under mangled
  keys (`__impl_Trait_Type_method`). On application, the dispatcher looks up
  the right impl based on the argument's runtime type.
- **Dictionary passing (codegen)**: for a future compiled backend, trait methods
  would dispatch via dictionaries (records of functions) passed as implicit
  arguments. This is the standard Haskell/GHC approach and maps cleanly to
  BEAM (dictionaries are just Erlang tuples/maps).

- **Supertrait enforcement**: `check_supertrait_impls()` runs after all impls
  are registered (order-independent). Verifies that for every `impl Trait for X`,
  all supertraits of `Trait` also have impls for `X`.

- **Unified type representation**: primitive types (Int, Float, String, Bool,
  Unit) are no longer separate `Type` enum variants. All types are `Type::Con`,
  e.g. `Type::Con("Int", [])`. Convenience helpers: `Type::int()`, etc.
  Simplifies trait constraint checking (single `Con` match arm instead of
  separate primitive and user-defined arms).

- **Built-in Show trait**: registered in `register_builtins` with impls for
  Int, Float, String, Bool, Unit. `show` and `print` now require `Show a`
  constraint. Custom types need `impl Show for T` to be printable. Show
  constraints propagate through inference like user-defined traits.

- **Built-in trait constraints on operators**: `Num` (arithmetic: +, -, *, /,
  %, unary -), `Eq` (==, !=), `Ord` (<, >, <=, >=) are registered as built-in
  traits with impls for Int, Float, String (Eq/Ord only), Bool (Eq only).
  BinOp inference pushes constraints to `pending_constraints`.

- **Conditional impls**: `ImplInfo` carries `param_constraints: Vec<(String, usize)>`
  mapping trait names to type parameter indices. `check_pending_constraints`
  loops until stable, since resolving e.g. `Show for List Int` pushes `Show for
  Int`. Works for built-in types (Show for List/Maybe/Result, Show/Eq for Tuple)
  and user-defined impls (`impl Show for Box a where {a: Show}`).

- **Tuples**: `Type::Con("Tuple", vec![...])` with any arity. No predefined
  Tuple2/Tuple3 types. Trait constraints on Tuple propagate to all elements.
  Tuple patterns work in let, case, and function args.

**Done:**

- **`needs` on handler bodies**: handler arms have their effects tracked and
  checked against the declared `needs` clause, same as function bodies. Pure
  handlers omit `needs`; impure handlers must declare all used effects.

**Still needed:**

- **`todo` and `panic` builtins**: not yet implemented. See section 6 for
  design. Keywords, no `!`, return type `Never`. `todo` is a type hole
  (typechecker accepts anywhere a value is expected). `panic` is an
  immediate halt for logic errors.

- **`needs` on impl blocks**: not parsed yet. Different impls of the same trait
  may use different effects (e.g. a pure `Store` impl vs one using `Http`).
  `needs` should go on `ImplDef`, mirroring handlers.

- **Effect row polymorphism**: HOFs that are transparent to their callback's
  effects (like `map`, `filter`) require effect variables (`needs e`) to be
  fully tracked. The current `EffArrow` approach handles the absorbing-HOF
  pattern (`try`, `run_with_state`) but not the transparent-HOF pattern.
  Full row polymorphism is a larger change and is deferred.

**Core traits for the stdlib (future):**

```
trait Semigroup a { concat : a -> a -> a }
trait Monoid a    where {a: Semigroup} { empty : a }
```

### Phase 2: Higher-Kinded Types (Kinds)

Add kind inference so trait type parameters can be type constructors
(`* -> *`), not just concrete types (`*`). This enables `Functor`,
`Applicative`, and friends.

**What's needed:**

- **Kind representation**: `Kind::Star`, `Kind::Arrow(Kind, Kind)`. Most
  types are `*`. `Maybe` is `* -> *`. `Result` is `* -> * -> *`.
- **Kind inference**: mostly mechanical. If the checker sees `f a` in a type
  position, it infers `f : * -> *` and `a : *`. Uses unification at the kind
  level (same algorithm as type unification, just simpler).
- **Kind checking**: reject nonsense like `Int Int` (applying a `*` to a `*`).
- **Update trait definitions**: trait type parameters carry a kind. `trait
  Functor f` means `f : * -> *`.

**Key traits this enables (library code, not compiler):**

```
trait Functor f {
    map : (a -> b) -> f a -> f b
}

trait Applicative f where {f: Functor} {
    pure : a -> f a
    apply : f (a -> b) -> f a -> f b
}
```

`Monad` can also be defined as a trait but is less necessary since algebraic
effects cover most of its use cases (IO, error handling, state, async).
Applicative is the more important one -- it enables patterns like parallel
validation / error accumulation that effects don't naturally express.

**Important**: traits (Phase 1) should not hardcode the assumption that type
parameters are kind `*`. Keep them as type variables and the kind system
will constrain them in Phase 2.

### Phase 3: Exhaustiveness Checking

Verify that pattern matches cover all cases. Not strictly required for the
backend but important for real-world use. Can be implemented independently
of the other phases.

---

## 9. BEAM Backend

Replace the tree-walking interpreter (`eval.rs`) with a codegen pass that
emits Core Erlang (`.core` files). The Erlang compiler handles optimization
and BEAM bytecode generation from there.

**Pipeline:**

```
source -> lexer -> parser -> typechecker -> codegen -> .core files
           |___________________________________________|
                          all Rust
```

Types are erased at the Core Erlang boundary. The BEAM runtime is untyped,
same as Gleam's approach. All type checking happens in Rust.

**What BEAM gives us for free:**

- Garbage collection (per-process, no stop-the-world)
- Lightweight processes and preemptive scheduling
- Tail call optimization
- Pattern matching compilation
- Hot code reloading
- Distribution / clustering
- The entire OTP library ecosystem

**Codegen approach:**

Emit Core Erlang as text (string templates). Walk the AST, emit corresponding
Core Erlang constructs. Can optionally add a structured IR (Rust enums
representing Core Erlang nodes) between AST and text if direct emission
gets messy.

Core Erlang is a stable, well-documented format. Gleam's Rust compiler
(targeting Core Erlang) is the closest reference implementation.

**Key translation concerns:**

- **Closures**: Core Erlang has `fun` -- direct mapping.
- **ADTs**: tagged tuples, e.g. `Just(5)` becomes `{'Just', 5}`.
- **Pattern matching**: Core Erlang `case` expressions.
- **Currying**: emit nested `fun`s or use Erlang's `fun F/N` with partial
  application wrappers.
- **Effects/handlers**: map to processes, message passing, or CPS depending
  on the approach. Processes are the most natural fit on BEAM.
- **Trait dictionaries**: passed as extra arguments (tuples/maps of functions).
- **Tail calls**: free on BEAM, no special handling needed.

**Build tooling:**

Need to decide whether to lean on rebar3/mix for project management and
dependencies, or build custom tooling. Can use Hex (Erlang package registry)
for interop with existing BEAM packages.

### FFI

Foreign function interface for calling Erlang/OTP libraries. Minimal syntax
for declaring external functions with type signatures:

```
effect FileSystem {
    read_file(path: String) -> String
}

foreign erlang "file" "read_file" as read_file in FileSystem
```

FFI functions slot into the effect system -- the user maps foreign functions
to effect operations. This means:

- FFI calls are tracked by the type checker like any other effect.
- Handlers can swap FFI-backed effects for pure implementations in tests.
- Pure FFI (math, string ops) needs no effect annotation.

Type safety at the FFI boundary is trust-based: the programmer declares the
type, the checker believes it. Same approach as Gleam.

### JavaScript Backend (Future)

Second codegen backend emitting JS instead of Core Erlang. Enables fullstack
development: BEAM server + JS client, shared types, compiler-inferred RPC
boundaries (functions with server-side `needs` automatically become HTTP
calls from the client).

Not planned until the BEAM backend is solid. The AST, type checker, and
trait system are fully shared -- only the codegen pass differs.

---

## 10. String Interpolation

Syntax: `$"hello {expr}, you are {age}!"` -- the `$` prefix opts the string
in to interpolation. Plain `"..."` strings are unchanged.

**Escaping:**

- `\{` produces a literal `{` (consistent with `\n`, `\t`, `\"`)
- `}` never needs escaping -- it is only special inside holes
- No `{{`/`}}` doubling syntax (C# style was rejected for inconsistency)

**Holes:**

- `{expr}` where `expr` is a full expression at the lowest precedence level
- Pipe works inside holes: `$"count: {xs |> length}"`
- Any `Show` instance is accepted; the typechecker enforces this naturally

**Implementation -- parse-time desugaring:**

No new AST node. `Token::InterpolatedString(Vec<InterpPart>)` carries
pre-tokenized hole expressions from the lexer. The parser desugars inline:

```
$"hello {name}, age {age}!"
  →  "hello " <> show(name) <> ", age " <> show(age) <> "!"
```

Each hole becomes `App(Var("show"), hole_expr)`. Literal segments become
`Lit::String`. The whole thing folds left with `BinOp::Concat`. Empty
literal parts are dropped.

The typechecker and evaluator see ordinary `BinOp::Concat` and `App` nodes --
no special casing required.

**Lexer sub-tokenization:**

When `read_interp_string` encounters `{`, it collects raw chars until the
matching `}` (tracking brace depth for nested braces), then creates a fresh
`Lexer` on that source to tokenize the hole expression. The resulting
`Vec<Spanned>` is stored as `InterpPart::Hole`. The parser re-uses
`Parser::new(hole_tokens).parse_expr(0)` to parse each hole.

**String prefix system (planned):**

The `$` prefix establishes a general string prefix system:

| Syntax         | Meaning                          | Status   |
| -------------- | -------------------------------- | -------- |
| `"..."`        | Plain string, backslash escapes  | Done     |
| `$"..."`       | Interpolated string              | Done     |
| `r"..."`       | Raw string, no escape processing | Planned  |
| `"""..."""`    | Multiline plain string           | Planned  |
| `$"""..."""`   | Multiline interpolated string    | Planned  |

`r"..."` and `$"..."` are mutually exclusive (raw strings disable `\{`,
which is needed for escaping in interpolated strings).

---

## 11. Trait Dispatch and `set_root`

**Problem:**

`impl Show for T` wasn't being picked up at runtime for the builtin `show`
function. The root cause: `TraitMethod` values capture their lookup env at
registration time, but impl closures are registered in a different env frame.

`show` is registered in `base_env` (in `register_builtins`). User code runs
in `main_env = base_env.extend()`. `impl Show for User` stores the closure
in `main_env`. When `show alice` dispatches, it calls `base_env.get(key)`,
which walks up toward the root -- but `main_env` is a child of `base_env`,
not an ancestor. The lookup fails.

The same bug affects cross-module trait impls: a trait defined in module A
(TraitMethod captures module_A_env) and implemented in module B (impl stored
in module_B_env) would fail because the two envs are siblings, neither can
see the other.

**Fix: `Env::set_root`**

`ImplDef` evaluation now calls `env.set_root(key, closure)` instead of
`env.set(key, closure)`. `set_root` walks up the parent chain and stores
the binding in the outermost (root) frame.

This works because:
1. All impls land in root -- globally visible regardless of registration site
2. `TraitMethod.env.get(key)` walks up to root and finds them
3. The invariant matches the language semantics: impls are globally scoped,
   there is no such thing as a local `impl` block

**`show` specifically:**

`show` was changed from `Value::BuiltIn("show")` (which called
`format!("{}", arg)` directly) to `Value::TraitMethod { trait_name: "Show" }`.
This makes it go through the same dispatch path as user-defined trait methods.
A fallback to `format!("{}", arg)` remains in the dispatch code for primitive
types and types without an explicit `impl Show`.

**Open question:**

`set_root` is a blunt instrument -- any `ImplDef` mutates the root frame
regardless of where it is evaluated. The cleaner fix would be to pass the
current env to `apply` so trait dispatch always uses the most-derived env
at the call site (Option A), or to use a separate `ImplRegistry` shared
struct instead of the env chain (Option B). Both require threading a new
parameter through `apply` and `eval_expr`. Deferred.

---

## 12. Qualified Record Creation

Record types have no runtime constructor value (unlike ADT constructors).
`Animal { name: "Rex" }` is parsed as `Expr::RecordCreate { name: "Animal" }`
directly in the parser -- there is no `Animal` binding in the env to look up.

This means `import Animals as A` followed by `A.Animal { ... }` would not
work -- the `A.Animal` part would parse as a `QualifiedName`, and the `{`
would be parsed as a block, not a record literal.

**Fix:**

In `parse_postfix`, after assembling `QualifiedName { module, name }`, if
`name` starts with an uppercase letter and the next token is `{`, parse a
record create immediately:

```
A.Animal { name: "Rex" } → RecordCreate { name: "Animal", fields: [...] }
```

The unqualified type name (`"Animal"`) is stored in the `RecordCreate` node,
consistent with how qualified ADT constructors work:
`A.Circle(5)` resolves to `Value::Constructor { name: "Circle", ... }`.

This means two modules both exporting a record named `Animal` would produce
values with the same type name -- impl dispatch would be ambiguous. Full
namespacing (storing `"Animals.Animal"` in `Value::Record`) would fix this
but requires also qualifying `ImplDef` target types at registration time and
is deferred.

---

## 13. `do...else` Blocks

Sequential pattern-binding with unified bail handling. Each binding either
extracts a value (on match) or short-circuits the whole block (on mismatch).
The else block handles all possible short-circuit values.

### Syntax

```
do {
  Pattern1 <- expr1
  Pattern2 <- expr2
  PatternN <- exprN
} else {
  BailPat1 -> result1
  BailPat2 -> result2
}
```

- Every line in the `do` block is a binding: `Pattern <- expr`.
- The last binding's extracted value is the return value of the whole block
  on the success path.
- The `else` block is a set of pattern arms covering all possible bail values.
- A variable pattern (`x <- expr`) always matches and never bails -- useful
  as the last line when you need to transform before returning.

### Semantics

Each `Pattern <- expr` is evaluated in order:

1. Evaluate `expr` to get a value `v`.
2. Attempt to match `v` against `Pattern`.
3. If match succeeds: bind the pattern variables, continue to next line.
4. If match fails: short-circuit -- evaluate the else block with `v` as the
   bail value. The matching else arm fires, and its result is the result of
   the entire `do...else` expression.

The else arms collectively cover the *union of all bail values* from all
bindings. Since each binding contributes different constructors to the bail
pool, the else block is a multi-source pattern match.

### Type Checking

**The bail pool:**

For each binding `Pattern <- expr`:
- Infer `expr` to get type `T` (e.g. `Result User e`)
- Determine which constructors are consumed by `Pattern` (e.g. `Ok`)
- The remaining constructors of `T` are added to the bail pool with their
  payload types (e.g. `Err(e)` added as a bail entry)

The bail pool is a list of `(constructor_name, payload_types, source_type)`
entries accumulated across all bindings.

**Checking else arms:**

Each else arm `P -> body` is checked as follows:

1. Bind pattern variables as fresh unification variables.
2. Infer the arm body -- unification constrains those variables.
3. Apply substitution: pattern variables now have (possibly solved) types.
4. Find the bail pool entry whose constructor and payload types match the
   resolved pattern.
5. Verify the arm body type unifies with the block's overall return type.

Step 3→4 is "deferred bail matching": inference runs first, then the resolved
types are matched against the bail pool. This means annotations are not
required in the common case -- the body provides enough information:

```
Err(a) -> a <> " failed"   -- infers a: String, matches Err(String) bail
Err(a) -> a + 1            -- infers a: Int, matches Err(Int) bail
```

If the body doesn't constrain the variable (e.g. `Err(a) -> "fallback"`),
the arm is treated as a wildcard covering all `Err(...)` entries.

**Constructor unification:**

Duplicate bail entries are unified before exhaustiveness checking:
- Same constructor + same payload type from multiple bindings → single entry,
  covered by one arm.
- Same constructor + different payload types → separate entries requiring
  separate arms (or a wildcard payload `Err(_)`).

**Exhaustiveness:**

After checking all else arms, every bail pool entry must be covered by at
least one arm. Uncovered entries are a type error listing the missing
constructors. A wildcard arm `_ -> ...` covers everything.

**Return type:**

The overall return type of the `do...else` expression is the unified type of:
- The last binding's extracted value (success path)
- All else arm bodies (bail paths)

These must unify, or it is a type error.

**No union types required:**

The bail pool and multi-source exhaustiveness checking are a special typing
rule scoped to the else block. No `Union(Vec<Type>)` variant is added to the
`Type` enum. Union types as a general language feature remain out of scope.

### Evaluator

The `do...else` block is implemented as a first-class AST node rather than
desugaring to nested `case` expressions. Desugaring would require duplicating
the else arms at each binding site, which is ugly and loses the unified
exhaustiveness context needed for good error messages.

Evaluation loop:

```rust
Expr::Do { bindings, else_arms } => {
    for (pattern, expr) in bindings {
        let val = eval_expr(expr, env)?;
        match try_match_pattern(&pattern, &val, env) {
            Some(bindings) => {
                for (name, v) in bindings { env.set(name, v); }
                // last binding: fall through, val is the result
            }
            None => {
                // bail: find matching else arm
                for arm in else_arms {
                    if let Some(b) = try_match_pattern(&arm.pattern, &val, env) {
                        for (name, v) in b { env.set(name, v); }
                        return eval_expr(&arm.body, env);
                    }
                }
                // no else arm matched -- runtime error (type checker prevents this)
                return EvalResult::Error("non-exhaustive do...else");
            }
        }
    }
    // all bindings succeeded: last extracted value is already in env
    // (the last pattern's variables are bound; the "result" is the last val)
}
```

Note: the last binding's extracted value is the success return. If the last
pattern is `Ok(x)`, then `x` is the return value. The evaluator needs to
track the last bound value specifically, or require the last pattern to bind
a single variable.

### New token: `<-`

The `<-` token does not currently exist in the lexer. It must be added:
- Lexer: emit `Token::LeftArrow` when `<` is followed immediately by `-`.
  Be careful not to conflict with `<=` (less-than-or-equal): `<-` consumes
  both characters, `<=` consumes both characters, `<` alone consumes one.
- Parser: `<-` is only valid inside a `do` block. It is not a general
  operator.

### Examples

**Homogeneous Result chain:**

```
do {
  Ok(user)  <- get_user id
  Ok(order) <- get_order user
  Ok(result) <- process order
} else {
  Err(e) -> Err(e)   -- covers all three Err bails (unified, same type)
}
```

**Mixed types:**

```
do {
  True      <- bool_fn ()
  Some(str) <- maybe_fn True
  Ok(result) <- result_fn str
} else {
  False    -> Err("it was false")
  None     -> Err("it was none")
  Err(str) -> Err(str)
}
```

**Variable binding as final line (transformation):**

```
do {
  Ok(user)  <- get_user id
  Ok(order) <- get_order user
  summary   <- format_summary user order   -- always matches, no bail
} else {
  Err(e) -> Err(e)
}
-- returns: summary (a String or whatever format_summary returns)
```

**Shadowing across bindings (works via overwrite):**

```
do {
  Ok(value) <- step1 ()
  Ok(value) <- step2 value   -- shadows previous value, refers to step1's result
  Ok(value) <- step3 value   -- shadows again, refers to step2's result
  value
} else {
  Err(e) -> default
}
```

### Implementation Order

1. Add `Token::LeftArrow` to lexer.
2. Add `Expr::Do { bindings: Vec<(Pat, Expr)>, else_arms: Vec<MatchArm> }` to AST.
3. Parser: parse `do { Pat <- expr ... } else { arms }`.
4. Evaluator: implement the evaluation loop above.
5. Type checker: bail pool collection, deferred bail matching, exhaustiveness.

The evaluator (step 4) can be implemented and tested before the type checker
(step 5) -- run examples to verify correct short-circuit behavior, then add
type safety.

---

## 14. Explicitly Out of Scope

- **Multishot continuations** - calling `resume` more than once. Not needed
  for practical effects (I/O, logging, state, errors, async). Could be added
  later as opt-in if needed.
- **Effect inference** - inferring which effects a function uses. We require
  explicit annotations. Inference is a type-checker concern for later.
- **Effect tunneling** - effects silently passing through handlers. Keep it
  simple: unhandled effects are runtime errors (static errors after type checker).
