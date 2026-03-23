### Core Foundation: Algorithm W with Extensions

The base is recognizably Algorithm W - you have the classic pieces:

- Type variables (Var(u32)) unified via a substitution map
- Instantiation creates fresh vars for each forall in a scheme
- Generalization at let-bindings collects free vars not in the environment
- Unification walks type structure, binding vars along the way

So the HM skeleton is solid. The interesting story is where you deviate.

### Extensions Beyond Standard HM

#### 1. Hybrid Effect System (side-channel + row polymorphism)

Effects are tracked through two cooperating mechanisms:

**String-based tracking** (`EffectState.current: HashSet<String>`) accumulates effect names during inference and checks them against `needs` declarations. This handles the common case: a function calls `log!`, the Log effect goes into `current`, and at the end of the function body it's checked against the declared `needs {Log}`.

**Row-polymorphic effect types** (`EffectRow` on `EffArrow`) handle higher-order functions where effects must flow through callbacks. The `..e` syntax creates an open effect row that captures unknown effects and propagates them via unification:

```
fun run_logged : (f: () -> Unit needs {Log, ..e}) -> Unit needs {..e}
```

Row variables are `Type::Var` values stored in `EffectRow.tail`, so they participate in standard substitution, renaming, and generalization. Row unification matches effects by name, unifies type args pairwise, then binds leftover effects to row variables. A separate `row_map` on `Substitution` stores row variable bindings (mapping var ID to `EffectRow`).

**Enforcement rules for annotated arrow types:**

- No `needs` clause in an annotation = pure (closed empty `EffectRow`). Passing an effectful lambda is a type error.
- `needs {Assert}` = closed row. Only these effects allowed.
- `needs {Assert, ..e}` = open row. Assert plus whatever else, forwarded via `e`.
- Bare `Arrow` (no annotation, inference-generated) = effect-agnostic, unifies with anything. This is used internally by the App inference code.

**Known gap:** The string-based tracking and type-level row variables don't fully communicate. When effects flow through a row variable (e.g., `..e` binds to `{Log}`), `EffectState.current` doesn't see `Log` as one of the callee's effects. This causes false positives in the handler-unnecessary check (mitigated by suppressing the check for functions with `fun_has_row_var`). Long-term these two systems should converge.

#### 2. Effect Type Param Caching

The `type_param_cache` in `EffectState` ensures `State s` uses the same `s` for both `get!` and `put!` within a function. Instantiated type params are cached per-effect and reused, and these vars are excluded from generalization.

This works but is somewhat fragile - it's a global-ish side channel that relies on scope discipline. A more formal approach would be something like Koka's scoped effect variables, but what you have is pragmatic and correct for the common cases. Potential issue: if row variables bind to additional instances of the same effect (e.g., two different `State` instantiations), the cache could get confused.

#### 3. Deferred Constraint Solving (not OutsideIn)

Standard HM doesn't have trait constraints. GHC's approach (OutsideIn) interleaves constraint generation with solving, using a sophisticated solver with given/wanted distinction.

You've gone simpler: constraints accumulate as `pending_constraints` during inference, then get checked in a single pass at the end (`check_pending_constraints`). At that point, type variables should be resolved to concrete types, and you look up impls.

This is totally reasonable for the complexity level you're at. The tradeoff is:

- You can't do constraint-driven inference (where knowing `x : Show` helps resolve an ambiguous type)
- You can't backtrack if a constraint fails
- But you avoid the complexity of a full constraint solver, and for a language where most types are inferred from usage, this is fine

Note: row variables are solved eagerly during unification, not deferred. If row constraints ever need to influence type inference (e.g., "this function's return type depends on which effects the callback uses"), the deferred approach would need revisiting.

#### 4. Where-Clause Bounds

Your `where_bounds` map (`var_id -> HashSet<trait_names>`) is a lighter-weight version of what Haskell/Rust do. When a polymorphic function has `where {a: Show}`, constraints on that var are satisfied by the bound rather than needing a concrete impl. This feeds into elaboration for dictionary passing.

#### 5. Multi-Pass Declaration Checking

The 8-pass approach in `check_decl.rs` (types -> imports -> externals -> annotations -> pre-bind -> impls -> bodies -> constraints) is more passes than most implementations, but it cleanly handles forward references and mutual recursion. Each pass has a clear responsibility.

### Things Done Well

- **Error recovery:** The `Type::Error` that unifies with everything means one type error doesn't cascade into dozens of follow-on errors. This is important for IDE/LSP use.
- **Never type:** Having a proper bottom type for `panic`/`exit` that unifies with anything is correct and avoids the need for special-casing in branch unification.
- **Scope isolation for effects:** The `enter_effect_scope`/`exit_effect_scope` pattern prevents effects from leaking between branches or into outer contexts incorrectly. Handler arms get their own scope but inherit the type param cache from the inner expression, which is exactly right.
- **Exhaustiveness checking:** Using Maranget's usefulness algorithm is the gold standard here (same as Rust, OCaml, etc.).
- **Row polymorphism as a layer:** Effect row polymorphism was added as an orthogonal extension to unification (separate `row_map`, `EffectRow` struct, `unify_effect_rows` method) rather than rewriting the core. Row variables reuse the existing type variable machinery (`Type::Var`) for substitution, renaming, and generalization.

### Potential Concerns

- **Two-tier effect tracking:** The string-based `EffectState.current` and the type-level `EffectRow` with row variables are parallel systems that don't fully communicate. The handler-unnecessary check, unused-effects warning, and `check_undeclared_effects` all operate on strings and can't see effects that flow through row variables. This is mitigated but not fully resolved.
- **Arrow/EffArrow semantic distinction:** `Arrow` (inference-generated, effect-agnostic) vs `EffArrow` (annotation-generated, enforced) is a meaningful distinction that's easy to confuse. The rule is: user-written annotations always produce `EffArrow` (even without `needs`, via `convert_type_expr`), while the App inference code produces `Arrow`. Mixing them up would silently weaken enforcement.
- **No incremental constraint solving:** Right now this is fine, but if you ever want things like "the type of this expression depends on which traits are in scope" or Rust-style `impl Trait` return types, you'd need to move toward incremental solving.
- **Substitution without union-find:** You do recursive follow-through in `apply()`, which is O(path length) per application. For the program sizes you're targeting this is fine, but union-find with path compression is the standard optimization if it ever becomes a bottleneck.

### Overall Assessment

This is a well-structured, pragmatic HM implementation. You're following the core algorithm faithfully (instantiate, unify, generalize) and your extensions (effects, traits, handlers) are added as orthogonal layers rather than deeply entangled with the core. The deferred constraint approach is the right call for a language at this stage.

The effect system is now a hybrid: string-based tracking for the common case (declaring and checking `needs` on named functions) and row-polymorphic types for the higher-order case (forwarding unknown effects through callbacks). The main architectural debt is the gap between these two layers, which manifests as edge cases in handler validation and unused-effect warnings. Converging them (making the string-based tracking aware of row variable bindings, or replacing it with type-directed tracking) would be the natural next step if these edge cases become painful.
