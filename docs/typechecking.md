# Typechecking

## Overview

The typechecker lives in `src/typechecker/` and is driven by `Checker::check_program` in `src/typechecker/check_decl.rs`.

At a high level, typechecking is:

1. A small number of ordered **module-level passes**
2. One large **body-checking / inference pass**
3. A few **final validation and warning passes**

For a single module, it is reasonable to describe the pipeline as:

- **7-8 core semantic passes**
- **Around 12-15 stages total** if you count sub-passes, validation sweeps, and warning cleanup

That distinction matters because most of the checker is not implemented as many whole-AST passes. Instead, a lot of the detailed work happens during one recursive expression-inference walk.

## Entry Points

- `src/typechecker/check_decl.rs`
  - `check_program`
  - `check_program_inner`
- `src/typechecker/infer.rs`
  - `infer_expr`
- `src/typechecker/check_module.rs`
  - `typecheck_import`

`check_program` is the public entry point. `check_program_inner` runs the main typechecking pipeline. `typecheck_import` recursively typechecks imported modules using the same machinery.

## Pass Summary

### 0. Local Type Name Seeding

Before the named passes begin, `check_program_inner` does a quick scan of the module and inserts local type and record names into `scope_map.types`.

Purpose:

- Let local types resolve during later declaration registration
- Ensure local types shadow imported ones

This is best thought of as a setup pre-pass rather than a full semantic pass.

### 1. Definition Registration

Implemented by `register_definitions` in `src/typechecker/check_decl.rs`.

This is the first major pass and it has two sub-passes.

### 1a. Register types, records, effect stubs, and traits

This sub-pass registers:

- ADT type definitions
- Record definitions
- Effect names and effect type parameters, but not operation signatures yet
- Trait definitions and trait methods

Purpose:

- Populate the constructor environment
- Populate record metadata
- Populate trait metadata and trait method schemes
- Make effect names available before their operations are processed

### 1b. Fill in effect operation signatures

After all effect names are known, the checker goes back over effect declarations and registers each operation signature.

Purpose:

- Allow forward references between effects in the same module
- Finish effect metadata now that all effect names exist

### 2. Import Processing

Implemented by `process_imports` in `src/typechecker/check_decl.rs`, which calls `typecheck_import` in `src/typechecker/check_module.rs`.

This pass:

- Resolves each import
- Loads, parses, derives, desugars, and typechecks imported modules on demand
- Caches module exports and codegen metadata
- Merges imported names into the current checker state

Important detail:

- Imported modules recursively run the same typechecking pipeline
- A cached prelude snapshot is reused so imports do not repeatedly rebuild the prelude

### 3. Name Resolution

After imports are processed and definitions are registered, the checker runs the standalone resolve pass:

- `src/typechecker/resolve.rs`
  - `resolve_names`

This rewrites the AST in place to canonicalize imported names using the accumulated `ScopeMap`.

Purpose:

- Rewrite imported values, constructors, traits, and effect qualifiers to canonical names
- Preserve shadowing by leaving local bindings alone

This is a real pass, but it is narrow in scope: it prepares the AST for inference rather than performing type inference itself.

See `docs/name-resolution.md` for the full design.

### 4. External Function Registration

Implemented by `register_externals` in `src/typechecker/check_decl.rs`.

This pass registers `@external` function signatures in the environment so they are available to later checking, including impl method bodies.

It:

- Converts user-written type annotations into internal `Type`
- Rejects illegal `needs` clauses on externals
- Attaches `where` constraints to the resulting schemes

### 5. Function Annotation Collection

Implemented by `collect_annotations` in `src/typechecker/check_decl.rs`.

This pass walks `FunSignature` declarations and converts them into internal type schemes.

It collects:

- Function type annotations
- Declared effect rows from `needs`
- Open effect row variables like `..e`
- `where`-clause trait constraints

It also seeds the function environment with annotated schemes before function bodies are checked.

Purpose:

- Let annotations guide inference
- Preserve declared effect information on function arrows
- Record explicit trait constraints before body checking starts

### 6. Function Pre-Binding

Implemented by `pre_bind_functions` in `src/typechecker/check_decl.rs`.

This pass assigns each function name a fresh placeholder type and inserts it into the environment if needed.

Purpose:

- Support recursion and mutual recursion
- Ensure function names are available while their bodies are being checked

Annotated functions still get a fresh placeholder in `fun_vars`, but their declared schemes are already in the environment from the annotation pass.

### 7. Impl Registration and Impl Body Checking

Implemented by `register_all_impls` in `src/typechecker/check_decl.rs`, with most trait logic in `src/typechecker/check_traits.rs`.

This pass:

- Registers trait impls
- Checks impl headers for validity
- Verifies required methods exist
- Rejects duplicate or extra methods
- Typechecks each impl method body against the corresponding trait method signature
- Checks impl `needs` clauses against effects used in method bodies

Although it is called a registration pass, it is already doing real body checking for impl methods.

### 8. Main Declaration / Body Pass

This is the largest pass in the pipeline. It is the main loop inside `check_program_inner`.

It:

- Walks all declarations in source order
- Groups consecutive `FunBinding`s with the same name into a single function
- Sends function groups to `check_fun_clauses`
- Sends non-function declarations to `check_decl`

This is where most user code is actually inferred and checked.

## Function Body Checking

The core routine for top-level functions is `check_fun_clauses` in `src/typechecker/check_decl.rs`.

For each function, it roughly does the following:

1. Determine arity and create fresh parameter/result types
2. If there is an annotation, unify the fresh types with it up front
3. Register `where` bounds for the function's type variables
4. Enter an isolated inference scope for effects and ambiguity tracking
5. Check each clause:
   - bind clause patterns
   - check the guard
   - infer the body
   - unify clause result with the function result type
6. Merge and normalize the effects used by all clauses
7. Run multi-clause exhaustiveness and redundancy checking when needed
8. Compare inferred effects against the declared `needs` row
9. Detect ambiguous field access that remained unresolved
10. Build the final function type
11. Generalize it into a scheme
12. Partition trait constraints into scheme constraints vs deferred concrete constraints

This is the heart of top-level function checking.

## Expression Inference Is Mostly One Recursive Pass

Expression checking is centered on `infer_expr` in `src/typechecker/infer.rs`.

This is not a sequence of many whole-program passes. It is one recursive walk over each expression tree, with local checks interleaved.

`infer_expr` handles:

- literals, variables, constructors
- applications
- operators
- `if`
- blocks
- lambdas
- `case`
- records
- effect calls
- `with`
- `resume`
- tuples
- qualified names
- `do`
- `receive`
- ascriptions
- inline handler expressions
- bitstrings

During this recursive walk, the checker also accumulates:

- type equalities for unification
- trait constraints
- effect usage
- LSP/reference metadata

## Local Analyses Triggered During Inference

Several important analyses happen during expression inference or body checking, but they are not separate compiler-wide passes.

### Pattern binding

Implemented in `src/typechecker/patterns.rs` by `bind_pattern`.

Used for:

- function parameters
- `let`
- `case` arms
- `do` bindings
- handler arms

### Exhaustiveness and redundancy

Implemented mainly in:

- `src/typechecker/patterns.rs`
  - `check_exhaustiveness`
  - `check_do_exhaustiveness`
- `check_fun_clauses` in `src/typechecker/check_decl.rs`

Used for:

- `case`
- `do ... else`
- multi-clause function definitions

These checks use Maranget-style usefulness/exhaustiveness logic, but they run at the point where the relevant expression or function is being checked.

### Effect checking

Implemented across:

- `src/typechecker/infer.rs`
- `src/typechecker/effects.rs`
- `src/typechecker/handlers.rs`

Key behavior:

- effect calls emit effect entries into the current effect accumulator
- applications perform callback-effect absorption logic
- lambdas isolate body effects, then attach them to the resulting function type
- `with` subtracts handled effects and re-emits escaping ones
- function and handler bodies are checked against declared `needs` rows using `check_effects_via_row`

### Handler checking

Implemented in:

- `src/typechecker/handlers.rs`
- `register_handler` in `src/typechecker/check_decl.rs`

This includes:

- checking handler arms against effect operation signatures
- checking handler return clauses
- checking handler `needs`
- computing which effects are handled and which still escape
- inferring the resulting `Handler` type

### Trait constraint collection

Trait constraints are generated throughout inference, especially for:

- operators like `+`, `==`, `<`, `<>`
- trait method calls
- where-bounded polymorphic values
- handler where constraints

Many of these constraints are pushed into `trait_state.pending_constraints` during inference and solved later.

### 9. Post-Body Validation Inside `check_program_inner`

After the main declaration/body pass, `check_program_inner` runs several validation steps.

### `main` effect validation

Checks that `main` does not declare or infer unhandled effects.

### `main` trait validation

Checks that `main` does not have unresolved trait constraints, since there is no caller to supply dictionaries.

### Annotation-without-body validation

Checks for function annotations that do not have a matching body, except for allowed bodyless cases such as certain builtins/externals.

### Deferred trait constraint solving

Implemented by `check_pending_constraints` in `src/typechecker/check_decl.rs`.

This is the final semantic validation pass for deferred trait requirements.

It:

- resolves type variables through the final substitution
- consults `where` bounds
- checks impl availability for concrete types
- may trigger more constraints through conditional impls
- records trait evidence used later by elaboration

This pass loops until no pending constraints remain.

### 10. Warning and Cleanup Passes

After `check_program_inner` returns, `check_program` runs three cleanup passes:

### Unused function check

Implemented by `check_unused_functions` in `src/typechecker/mod.rs`.

Warns about private top-level functions that are never referenced.

### Unused variable check

Implemented by `check_unused_variables` in `src/typechecker/mod.rs`.

Warns about local bindings that are never referenced.

### Warning zonking

Implemented by `zonk_warnings` in `src/typechecker/mod.rs`.

This applies the final substitution to deferred warning data and emits only warnings that are still valid after inference has settled.

Examples:

- discarded non-`Unit` values
- unused variables
- unused functions
- declared-but-unused effects

## Counting Passes

If you want one simple number, the cleanest approximation is:

- **7-8 core passes per module** before cleanup
- **12-15 stages total** if you count:
  - the definition sub-passes
  - the resolve pass
  - final `main` validations
  - deferred trait solving
  - warning cleanup passes

The most important nuance is this:

- The checker is **not** implemented as 12-15 independent whole-program traversals
- It is better described as a handful of setup/validation passes wrapped around **one large recursive inference pass**

## File Guide

- `src/typechecker/check_decl.rs`
  - top-level pipeline
  - function checking
  - annotation collection
  - impl registration
  - deferred trait solving
- `src/typechecker/infer.rs`
  - expression inference
  - application logic
  - block checking
- `src/typechecker/patterns.rs`
  - pattern binding
  - exhaustiveness and redundancy
- `src/typechecker/handlers.rs`
  - `with` checking
  - handler effect subtraction
- `src/typechecker/effects.rs`
  - effect lookup
  - effect row checking
- `src/typechecker/check_traits.rs`
  - trait registration
  - impl checking helpers
- `src/typechecker/check_module.rs`
  - import typechecking
  - module export injection
- `src/typechecker/mod.rs`
  - checker state
  - warning cleanup

## Short Version

Per module, the typechecker does a handful of setup passes, one big declaration/body inference pass, one deferred trait-solving pass, and a few warning sweeps. Most of the real work happens inside `check_fun_clauses` and `infer_expr`, with exhaustiveness, effects, handlers, and pattern checks firing as local analyses during that inference walk rather than as separate whole-program passes.
