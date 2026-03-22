### Core Foundation: Algorithm W with Extensions

The base is recognizably Algorithm W - you have the classic pieces:

- Type variables (Var(u32)) unified via a substitution map
- Instantiation creates fresh vars for each forall in a scheme
- Generalization at let-bindings collects free vars not in the environment
- Unification walks type structure, binding vars along the way

So the HM skeleton is solid. The interesting story is where you deviate.

### Extensions Beyond Standard HM

#### 1. Effects as a Side-Channel (not in the types)

This is probably the biggest architectural decision. In languages like Koka or Eff, effects are part of the type (row-typed effect rows). You've taken a different approach: effects are tracked as sets on the side (current: HashSet<String> in EffectState), accumulated during inference, and checked separately.

Pros: simpler unification, avoids row polymorphism machinery.
Cons: effects don't participate in type-directed inference. You can't, for example, infer which handler to use based on return type + effect context the way a row-typed system can.

The EffArrow type is a pragmatic bridge - it annotates arrows with effect info for HOF parameters (like spawn! needing to know the callback uses {Actor M}), but it's not a general effect-in-type mechanism.

#### 2. Effect Type Param Caching

The type_param_cache in EffectState is a clever solution to a real problem: ensuring State s uses the same s for both get! and put! within a function. You cache the instantiated type params per-effect and reuse them, and you exclude these vars from generalization.

This works but is somewhat fragile - it's a global-ish side channel that relies on scope discipline. A more formal approach would be something like Koka's scoped effect variables, but what you have is pragmatic and correct for the common cases.

#### 3. Deferred Constraint Solving (not OutsideIn)

Standard HM doesn't have trait constraints. GHC's approach (OutsideIn) interleaves constraint generation with solving, using a sophisticated solver with given/wanted distinction.

You've gone simpler: constraints accumulate as pending_constraints during inference, then get checked in a single pass at the end (check_pending_constraints). At that point, type variables should be resolved to concrete types, and you look up impls.

This is totally reasonable for the complexity level you're at. The tradeoff is:

You can't do constraint-driven inference (where knowing x : Show helps resolve an ambiguous type)
You can't backtrack if a constraint fails
But you avoid the complexity of a full constraint solver, and for a language where most types are inferred from usage, this is fine 4. Where-Clause Bounds
Your where_bounds map (var_id -> HashSet<trait_names>) is a lighter-weight version of what Haskell/Rust do. When a polymorphic function has where {a: Show}, constraints on that var are satisfied by the bound rather than needing a concrete impl. This feeds into elaboration for dictionary passing.

#### 5. Multi-Pass Declaration Checking

The 8-pass approach in check_decl.rs (types -> imports -> externals -> annotations -> pre-bind -> impls -> bodies -> constraints) is more passes than most implementations, but it cleanly handles forward references and mutual recursion. Each pass has a clear responsibility.

### Things Done Well

- Error recovery: The Type::Error that unifies with everything means one type error doesn't cascade into dozens of follow-on errors. This is important for IDE/LSP use.
- Never type: Having a proper bottom type for panic/exit that unifies with anything is correct and avoids the need for special-casing in branch unification.
- Scope isolation for effects: The enter_effect_scope/exit_effect_scope pattern prevents effects from leaking between branches or into outer contexts incorrectly. Handler arms get their own scope but inherit the type param cache from the inner expression, which is exactly right.
- Exhaustiveness checking: Using Maranget's usefulness algorithm is the gold standard here (same as Rust, OCaml, etc.).

### Potential Concerns

- Arrow/EffArrow unification asymmetry: Allowing Arrow to unify with EffArrow (and vice versa) adds complexity to unification. The special-casing for parameter effect absorption in infer.rs (preventing spawn! from absorbing caller effects) is correct but ad-hoc. If you add more effect-polymorphic combinators, this may need to become more systematic.
- No incremental constraint solving: Right now this is fine, but if you ever want things like "the type of this expression depends on which traits are in scope" or Rust-style impl Trait return types, you'd need to move toward incremental solving.
- Substitution without union-find: You do recursive follow-through in apply(), which is O(path length) per application. For the program sizes you're targeting this is fine, but union-find with path compression is the standard optimization if it ever becomes a bottleneck.

### Overall Assessment

This is a well-structured, pragmatic HM implementation. You're following the core algorithm faithfully (instantiate, unify, generalize) and your extensions (effects, traits, handlers) are added as orthogonal layers rather than deeply entangled with the core. The deferred constraint approach is the right call for a language at this stage - you can always move toward something more sophisticated (like OutsideIn) later if the need arises.

The biggest architectural question long-term is whether effects-as-side-channel will be sufficient or whether you'll eventually want effects in the type structure (row polymorphism). That would be a significant rearchitecture but would unlock things like effect polymorphism and handler inference.
