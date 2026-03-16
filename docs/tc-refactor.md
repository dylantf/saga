# Typechecker Refactor Plan

## Goal

Make the typechecker's output explicit so downstream consumers (elaborator, lowerer, LSP) depend on a clean result struct instead of reaching into Checker internals. This unblocks LSP Phase 2 (hover on locals, per-expression types) without requiring an algorithmic rewrite.

## Current state

The Checker is simultaneously the inference engine, definition registry, output carrier, and LSP data source. Every downstream consumer reaches into it:

- `main.rs` reads `checker.modules.codegen_info`, `checker.modules.programs`, `checker.evidence`
- `elaborate.rs` reads `checker.modules.codegen_info`, `checker.evidence`, `checker.env`
- LSP reads `checker.env`, `checker.modules.map`, `checker.modules.programs`
- Lowerer reads `checker.modules.codegen_info` (via main.rs)

The pipeline is: lex -> parse -> typecheck -> elaborate -> lower -> emit. The boundaries between typecheck and elaborate are blurry because the elaborator reads directly from the Checker.

## Why not a separate resolution pass?

Resolution and type checking are interleaved by necessity:

- Trait impl selection depends on inferred types
- Effect op disambiguation depends on effect type params
- Field access resolution depends on type narrowing (`field_candidates`)
- Constructor patterns need type context for cross-module overlap

The first 2-3 passes of `check_program` (register types, imports, constructors) could theoretically be a separate resolution pass, but they're already sequential within `check_program` and the payoff of extracting them is small.

## Plan: extract CheckResult

### Step 1: Define CheckResult

```rust
pub struct CheckResult {
    /// Per-span type information for LSP hover, go-to-def, etc.
    pub types: HashMap<Span, Type>,
    /// Trait evidence for elaboration (dictionary passing)
    pub evidence: Vec<TraitEvidence>,
    /// Errors and warnings
    pub errors: Vec<TypeError>,
    pub warnings: Vec<TypeWarning>,
    /// Module system output (codegen info, parsed programs, module map)
    pub modules: ModuleContext,
    /// Effect requirements per function (for lowerer CPS transform)
    pub fun_effects: HashMap<String, HashSet<String>>,
    /// Type environment (function/constructor types, for LSP completion + elaboration)
    pub env: TypeEnv,
    /// Constructor schemes (for elaboration)
    pub constructors: HashMap<String, Scheme>,
    /// Record definitions (for elaboration)
    pub records: HashMap<String, Vec<(String, Type)>>,
    /// Effect definitions (for lowerer)
    pub effects: HashMap<String, EffectDefInfo>,
    /// Handler definitions (for lowerer)
    pub handlers: HashMap<String, HandlerInfo>,
    /// ADT variant info (for exhaustiveness, used by elaboration)
    pub adt_variants: HashMap<String, Vec<(String, usize)>>,
    /// Trait impl registry
    pub trait_impls: HashMap<(String, String), ImplInfo>,
}
```

Initially this is just moving fields out of Checker. Over time, the Checker-internal fields (sub, next_var, pending_constraints, resume_type, current_effects, etc.) stay private, and CheckResult is the public API.

### Step 2: Record types during inference (LSP Phase 2 prerequisite)

Add `types: HashMap<Span, Type>` to Checker. Record types at:

- **Variable binding sites:** `bind_pattern` records each bound variable's span + type
- **Variable usage sites:** `Expr::Var` resolution records the usage span + instantiated type
- **Let bindings:** record the binding pattern's span + inferred type
- **Function parameters:** record each param's span + type
- **Expression hover targets:** selectively record spans for function calls, field access, constructors

Granularity matters. Don't record every subexpression (noisy, slow). Focus on things a human would hover over:
- Named things (variables, parameters, functions)
- Application results (what does `foo bar` return?)
- Field access results (what type is `user.name`?)

The types should be resolved through the substitution before storing (apply `sub` so you get `Int`, not `?42`). This means recording happens either at the end of inference or lazily on lookup.

**Decision: eager vs lazy resolution.** Eager (apply sub when recording) is simpler but means you need to re-record after unification refines a type. Lazy (store raw type, apply sub on lookup) is more correct but requires keeping the substitution around. Lazy is probably better since the sub is already on Checker and CheckResult can hold a reference or clone.

### Step 3: Make check_program return CheckResult

Change the signature:

```rust
// Before
pub fn check_program(&mut self, program: &[Decl]) -> Result<(), Vec<TypeError>>

// After
pub fn check_program(&mut self, program: &[Decl]) -> CheckResult
```

Errors become part of the result instead of early returns (we already do multi-error collection in many places). The Checker is still mutated during checking (it needs to accumulate state across declarations), but the result is extracted at the end.

### Step 4: Update consumers

**Elaborator:** takes `&CheckResult` instead of `&Checker`. Reads evidence, env, constructors, records, effects, codegen_info.

**main.rs:** reads `CheckResult.modules.codegen_info`, `CheckResult.modules.programs`, passes evidence to elaborator.

**LSP hover:** looks up `span` in `CheckResult.types` instead of scanning `env`.

**LSP completion:** reads `CheckResult.env` for available names + types.

**LSP diagnostics:** reads `CheckResult.errors` and `CheckResult.warnings`.

### Step 5 (optional): Separate Definitions from Checker

Once CheckResult exists, the definition fields (constructors, records, effects, handlers, traits, trait_impls, adt_variants) could move into a `Definitions` struct that's shared between Checker (for inference) and CheckResult (for consumers). This is optional polish, not a prerequisite for the LSP work.

## Migration strategy

Don't do this all at once. The steps are designed to be incremental:

1. Add `types: HashMap<Span, Type>` to Checker, start recording in `bind_pattern` and `Expr::Var`. This alone unblocks LSP hover on locals.
2. Define `CheckResult`, have `check_program` build and return one. Initially just moves fields; downstream code updates mechanically.
3. Update elaborator to take `&CheckResult`.
4. Update main.rs and LSP.
5. Clean up: make Checker fields private, remove pub from internal state.

Each step compiles and passes tests independently.

## What stays on Checker (internal inference state)

These fields are only needed during inference and don't escape:

- `next_var`, `sub` (unification machinery)
- `pending_constraints` (trait constraint queue)
- `resume_type` (handler arm context)
- `current_effects`, `effect_type_param_cache` (per-body effect tracking)
- `field_candidates` (ambiguous field access narrowing)
- `where_bounds`, `where_bound_var_names` (constraint solving)
- `collected_errors` (multi-error accumulation during blocks)
- `fun_effect_type_constraints` (annotation-provided effect type args)
