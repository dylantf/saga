# Bidirectional Typechecking

## Summary

We have now fixed several inference bugs by pushing expected types into lambda
checking in narrow, targeted ways:

- lambda arguments in ordinary call position
- first-argument lambdas constrained by later arguments in the same application
- eta-reduced partial applications constrained by annotated function results

These fixes were worth doing, but they all point at the same deeper issue:

- the current typechecker is mostly inference-first
- many expressions are inferred bottom-up before surrounding expected types are
  available
- later unification often comes too late to help field access, tuple patterns,
  or effectful callback typing inside lambda bodies

At this point we should plan for a proper bidirectional split between:

- inferring an expression's type when no useful expected type is available
- checking an expression against an expected type when the context already
  knows what shape it must have

This document maps out that migration.

## Why We Keep Hitting This

### Current Shape

Today the core expression path is roughly:

1. infer the callee
2. infer the argument
3. unify argument type with parameter type

That works fine for simple expressions, but it is fundamentally late for
expressions whose internals need context to typecheck well.

The main examples are:

- lambdas
- tuple-pattern lambda params
- field access through ambiguous record shapes
- eta-reduced higher-order definitions
- effectful callback parameters

### Recent Symptoms

We have already seen all of these:

- `push_values rows (fun (sesh_id, wd) -> ...)`
- `List.filter_map (fun pair -> case pair { ... }) rows`
- `wind_rows = List.filter_map (fun pair -> ...)` with an annotation
- effectful callback wrappers and eta-reduced operation refs

The common pattern is always the same:

- some later context knows the callback shape
- the lambda body is checked before that context is applied
- field/pattern/effect inference inside the lambda becomes too weak or
  ambiguous

The recent narrow fixes reduced the surface area, but they did not change the
underlying model.

## What "Bidirectional" Means Here

We do **not** need a completely different type system.

We do need an explicit split between two operations:

- `infer_expr(expr) -> Type`
- `check_expr(expr, expected_ty) -> Type`

The important rule is:

- if context already knows the expected type, prefer checking
- only infer when there is no meaningful expected type to use

For Saga, the most valuable expressions to support in `check_expr` are:

- lambda expressions
- case expressions where the result type is known
- record literals where the target record type is known
- partial applications / application spines where later arguments or result
  types constrain earlier lambdas

This should remain an HM-style checker with effect rows and traits. The change
is architectural, not a redesign of the language.

## Proposed Migration

### Phase 1: Formalize the API Boundary

Add and standardize a `check_expr_against` path in the typechecker.

Target interface:

```rust
infer_expr(&Expr) -> Result<Type, Diagnostic>
check_expr_against(&Expr, &Type) -> Result<Type, Diagnostic>
```

Rules:

- `infer_expr` remains the default entry point
- `check_expr_against` is used only where the caller already has a meaningful
  expected type
- `check_expr_against` may call `infer_expr` as a fallback for expression forms
  that do not benefit from contextual typing

This is the key refactor boundary. Once it exists cleanly, the rest of the
migration becomes incremental instead of ad hoc.

### Phase 2: Move Lambda Logic Into Checking

Lambdas should become the primary bidirectional expression.

`check_expr_against(lambda, expected_fun_ty)` should:

- decompose the expected function type across lambda params
- bind lambda params directly from those expected parameter types
- infer/check the body against the expected return type where useful
- preserve current effect behavior
  - body effects remain on the outermost arrow
  - callback effect-subtyping still applies at call sites
  - call-site effect absorption still works

`infer_expr(lambda)` should remain available, but only as the fallback path when
no expected function type exists.

This phase should absorb the targeted lambda hacks currently living in
application inference.

### Phase 3: Replace Ad Hoc Application-Specific Special Cases

Once `check_expr_against` exists, `App` should stop manually accumulating
lambda-specific heuristics.

Instead:

- infer the application spine
- whenever an argument position has a usable expected parameter type, call
  `check_expr_against(arg, expected_param_ty)`
- when an enclosing expected result type is available, thread that through the
  application spine in a uniform way

This keeps application inference generic and moves expression-specific logic
back into checking where it belongs.

The current application-spine work is a good stepping stone, but it should
eventually become an ordinary consumer of `check_expr_against`, not a second
typechecking framework.

### Phase 4: Expand Contextual Checking to Other Expression Forms

After lambdas are stable, expand `check_expr_against` only where it clearly
improves correctness or diagnostics.

Good next candidates:

- record creation against a known record type
- tuple expressions against a known tuple type
- case expressions against a known result type
- partial application results constrained by annotations

This phase should be incremental. We do not need to convert every expression
form immediately.

### Phase 5: Simplify Deferred/Ambiguity Machinery

After more expressions are checked contextually, revisit logic that currently
exists mainly because types arrive too late.

Likely cleanup targets:

- field ambiguity tracking
- ad hoc lambda deferral in application inference
- some fallback unification/error-reporting paths

The goal is not to remove ambiguity tracking entirely, but to make it the true
fallback for genuinely ambiguous programs instead of a frequent artifact of
late context propagation.

## Concrete Design Constraints

### Keep the Current Type System

Do not combine this project with:

- a new effect system
- trait-system redesign
- polymorphism changes
- AST redesign

This should be a checker architecture refactor, not a language change.

### Preserve Existing Semantics

The migration must preserve:

- callback effect-subtyping behavior
- call-site callback effect absorption
- boundary-half callback absorption in function checking
- current annotation semantics
- existing row-variable propagation rules

If any of those change, they should be planned separately.

### Prefer One Checking API Over Many Local Hacks

Avoid continuing the current pattern of adding narrow helper paths for:

- lambda in arg position
- lambda in first arg position
- annotated eta-reduced HOFs
- etc.

Once `check_expr_against` exists, new fixes should be expressed through it
instead of adding more expression-specific escape hatches.

## Suggested Implementation Shape

### New Entry Points

Add these checker helpers:

- `check_expr_against`
- `check_lambda_against`
- optional small helper for "decompose expected function type"

Keep:

- `infer_expr`
- `infer_lambda`

But treat `infer_lambda` as the fallback path, not the preferred one.

### Call Sites To Migrate First

Use `check_expr_against` first in:

- application argument checking
- annotated function body checking
- any existing place where we already manually bind params from an expected type

This lets us delete the new ad hoc logic incrementally rather than all at
once.

### Diagnostics

Bidirectional checking should improve diagnostics naturally:

- fewer fake ambiguities from unconstrained lambda params
- fewer misleading "not a function" errors when the real issue is argument type
- more precise field/pattern errors once expected types are available earlier

We should preserve the recent application-mismatch improvement:

- when the callee is known to be a function, prefer "expected X, got Y"
  over "`T` is not a function"

## Test Strategy

### Must Keep Passing

The following categories should remain covered:

- lambda argument constrained by earlier non-lambda args
- lambda argument constrained by later args in the same application
- eta-reduced HOF bindings constrained by annotations
- imported/project-mode versions of the same shapes
- effectful callback wrappers
- eta-reduced effect operation callbacks
- named-binder cases that already worked
- non-lambda ambiguous-field cases that should still require annotations

### New Regression Targets

When the full bidirectional work begins, add targeted tests for:

- case result checking against annotations
- record literals checked against known record types
- nested lambdas with partially known expected types
- open effect-row callbacks checked bidirectionally
- partial application under annotated let bindings

## Risks

### Hidden Semantic Drift

If `check_expr_against` starts eagerly unifying too much, it may:

- over-constrain polymorphic code
- change row-variable behavior
- interfere with trait constraint collection

So the migration should be staged, with tests after each moved expression form.

### Duplicate Logic During Transition

For a while we will have both:

- legacy inference-first paths
- new contextual checking paths

That is acceptable temporarily, but only if there is a clear plan to collapse
them back into one model. Otherwise we will just trade one set of special cases
for another.

## Recommendation

The next real compiler cleanup in this area should be:

1. introduce `check_expr_against`
2. migrate lambdas onto it
3. make application inference call it instead of carrying more lambda-specific
   logic
4. then expand carefully to other expression forms

That is the smallest path that gives us a proper bidirectional foundation
without requiring a full checker rewrite in one step.
