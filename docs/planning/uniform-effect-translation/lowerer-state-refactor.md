# Lowerer state refactor

**Status:** planning. Triggered by the arm-K bug in Example 11 and the
broader recognition that `lower_monadic/`'s ambient-state model is the
wrong shape for a lowerer consuming uniform monadic IR.

## Background

`lower_monadic/` consumes a uniform monadic IR where every sequencing
point is `Bind` and every yielding effect is `Yield`. The MExpr → CExpr
translation algorithm itself is **correct**: `lower_bind` does textbook
monadic-CPS reification (lower body first, build K-fun around it, lower
value under rebound K). `lower_app`/`lower_pure`/`lower_case`/`lower_if`
all thread the ambient K correctly.

The problem is **how the ambient K and related continuation state is
stored**: seven mutable fields on `Lowerer`, save/restore via
`std::mem::replace` at every lambda/letfun boundary. This collapses
distinct continuations into one slot and creates an open bug class.

### Example 11 (Result/Try, abort semantics) symptom

A handler arm that aborts via `fail x = Err x` was resuming the perform
site with `Err x` instead of escaping to the with-site. The arm body
lowered under `current_return_k = arm_K`, so `Pure(Err x)` applied the
arm K (continue at perform site) instead of the with-site K (escape).

Root cause: `current_return_k` carries two distinct meanings inside a
handler arm and the field can only hold one:
- **Pure target** (with-site K — abort/escape)
- **Resume target** (arm's perform-site K — continue)

The old lowerer kept these in two distinct fields
(`current_handler_k` vs `current_handler_inherited_k`). The new lowerer
has `current_arm_k: Option<String>` but the arm-construction code
*also* swaps `current_return_k` to the arm K, which is wrong.

## Scope

This refactor touches `src/codegen/lower_monadic/` only. ANF, monadic
IR, translation, handler-analysis, effect-opt stub, and toggle wiring
are out of scope — they are not the source of the issue.

Existing test coverage in `lower_monadic/tests.rs` (3,317 LOC) stays
green throughout. The refactor is mechanical and behavior-preserving
*except* for the arm-K fix in step 3, which is the one new line of
business logic.

## Target architecture

### `LowerCtx` value, threaded by argument

```rust
// src/codegen/lower_monadic/ctx.rs
#[derive(Clone)]
pub(super) struct LowerCtx {
    /// What `Pure(v)` applies — the "tail" target of the current
    /// computation. Defaults to `_ReturnK` at function entry. Rebound
    /// to a fresh `_K{n}` by `Bind`. **Never overwritten inside a
    /// handler arm body** — Pure in an arm body escapes to the
    /// with-site K, not the perform-site.
    pub return_k: String,

    /// In-scope evidence vector variable. Defaults to `_Evidence` at
    /// function entry. Rebound to `_Ev{n}` inside a `With` body.
    pub evidence: String,

    /// `Some(perform_site_k)` while lowering a handler arm body.
    /// `None` outside an arm. `Resume(v)` applies this K when set;
    /// when `None`, `Resume` is a translation error (typechecker
    /// already forbids `resume` outside arm bodies).
    pub arm_k: Option<String>,
}

impl LowerCtx {
    pub fn fresh() -> Self {
        Self {
            return_k: exprs::RETURN_K_VAR.into(),
            evidence: exprs::EVIDENCE_VAR.into(),
            arm_k: None,
        }
    }

    pub fn with_return_k(&self, k: String) -> Self {
        Self { return_k: k, ..self.clone() }
    }

    pub fn with_evidence(&self, e: String) -> Self {
        Self { evidence: e, ..self.clone() }
    }

    pub fn with_arm_k(&self, k: String) -> Self {
        Self { arm_k: Some(k), ..self.clone() }
    }
}
```

Cloning three short strings per bind/with/arm derivation is fine — the
arena allocation is dwarfed by the CExpr nodes being built.

### `Lowerer` keeps only cross-cutting state

After the refactor:

```rust
pub struct Lowerer<'ctx> {
    // unchanged — module-level read-only inputs
    resolution: &'ctx ResolutionMap,
    ctors: &'ctx ConstructorAtoms,
    module_ctx: &'ctx CodegenContext,
    handler_info: &'ctx HandlerAnalysis,
    effect_info: &'ctx EffectInfo<'ctx>,

    // unchanged — module-level mutable state
    pub(super) record_fields: HashMap<String, Vec<String>>,
    pub(super) emit_bootstrap: bool,
    pub(super) current_erlang_module: String,
    pub(super) handler_names: HashSet<String>,

    // kept — counters are genuinely cross-cutting, reset per function entry
    k_counter: u32,
    ev_counter: u32,
    arm_k_counter: u32,
    ret_k_counter: u32,
    helper_counter: u32,
}
```

Removed: `current_return_k`, `current_evidence`, `current_arm_k`,
`with_return_k`, `reset_k_state`.

Counters stay on `Lowerer` because they need monotonic uniqueness
across the whole function body, not per-derivation. They reset at
function entry (a single helper).

### Signature change

```rust
// Before:
fn lower_expr(&mut self, expr: &MExpr) -> CExpr

// After:
fn lower_expr(&mut self, expr: &MExpr, ctx: &LowerCtx) -> CExpr
```

Every `lower_*` helper that today reads `self.current_return_k` /
`self.current_evidence` / `self.current_arm_k` takes `&LowerCtx`.

## Refactor steps

### Step 1: introduce `LowerCtx`, thread through the public API

**Files touched:** `mod.rs`, `ctx.rs` (new), `decls.rs`, `exprs.rs`,
`effects.rs`, `exprs_edge.rs`, `pats.rs`.

**Changes:**
1. Create `ctx.rs` with `LowerCtx` as defined above.
2. Remove `current_return_k`, `current_evidence`, `current_arm_k` from
   `Lowerer`. Remove `with_return_k`, `reset_k_state`.
3. Add `ctx: &LowerCtx` parameter to every `lower_*` method on
   `Lowerer` that today reads any of the three ambient fields.
4. At entry points where a fresh context is needed (decl bodies,
   lambda bodies, letfun bodies), construct `LowerCtx::fresh()` and
   reset counters via a new `reset_counters` helper.

**Mechanical translation:**
- `self.current_return_k` → `ctx.return_k`
- `self.current_evidence` → `ctx.evidence`
- `self.current_arm_k` → `ctx.arm_k`
- `self.with_return_k(k, |this| this.lower_expr(value))` →
  `self.lower_expr(value, &ctx.with_return_k(k))`
- The two 14-line `mem::replace` blocks in `lower_lambda_atom` and
  `lower_let_fun` collapse to:
  ```rust
  let prev_counters = self.snapshot_counters();
  self.reset_counters();
  let body_ce = self.lower_expr(body, &LowerCtx::fresh());
  self.restore_counters(prev_counters);
  ```
  (counter save/restore stays — they're per-function-body monotonic).

**Verification:**
- `cargo build` green.
- `cargo test -p saga lower_monadic` green (existing 3,317 LOC of
  tests must pass unchanged — this step is purely structural).
- E2E test suite still failing at exactly the same set of cases as
  before this step (no behavior change).

### Step 2: fix the arm-K bug

**Files touched:** `effects.rs` (handler arm construction).

**Change:** arm-body lowering derives `ctx.with_arm_k(perform_k)`,
**not** `ctx.with_return_k(perform_k)`. The with-site K stays in
`ctx.return_k` so `Pure(v)` in an arm tail escapes to it
(abort semantics). `Resume(v)` reads `ctx.arm_k` and applies the
perform-site K (continue semantics).

This is the one new line of business logic in the refactor. Without
step 1 it was impossible to express; with step 1 it is one substitution.

`lower_resume` simplifies — `ctx.arm_k` is now guaranteed `Some` inside
arm bodies, so the fallback to `return_k` becomes a hard error:

```rust
fn lower_resume(&mut self, value: &Atom, ctx: &LowerCtx) -> CExpr {
    let v = self.lower_atom(value, ctx);
    let k = ctx.arm_k.as_ref().expect(
        "Resume outside handler arm body — typechecker should have rejected this"
    );
    CExpr::Apply(Box::new(CExpr::Var(k.clone())), vec![v])
}
```

**Verification:**
- `cargo build` + clippy green.
- Example 11 (`safe_str ""` with `to_result`) now produces `Err _`
  at the with-site rather than continuing through `safe_str`'s caller.
- No regressions in passing examples — the change only affects sites
  where `Pure` is reached inside an arm body, which previously
  miscompiled.

### Step 3: split `exprs.rs`

**Files touched:** `exprs.rs` (split), new `case.rs`, new `atom.rs`,
new `app.rs` (optional).

**Change:** `exprs.rs` is currently 1043 LOC. The contents factor
cleanly:

| New file | Contents | LOC est. |
|---|---|---|
| `exprs.rs` | `lower_expr` dispatcher, `lower_pure`, `lower_bind`, `lower_let`, `lower_resume`, `lower_lambda_atom`, `lower_let_fun` | ~350 |
| `case.rs` | `lower_case`, `lower_case_chain`, `lower_if`, `lower_arm`, `lower_guard`, `guard_safe`, `case_clause_error`, `bind_catchall_pattern` | ~280 |
| `atom.rs` | `lower_atom`, `lower_var_atom`, `lower_ctor_atom`, `lower_anon_record_atom`, `lower_record_atom`, `lower_dict_ref_atom`, `lower_qualified_ref_atom`, `lower_resolved_value_ref`, `uniform_value_arity`, `fun_value_of` | ~350 |
| `app.rs` | `lower_app`, `head_atom_expected_user_args`, `eta_expand_partial_app`, `lower_panic_or_todo` | ~150 |

Each file is well under 800 LOC. Splitting is mechanical — no logic
changes, just `mod` declarations and re-exports.

**Verification:**
- `cargo build` + clippy green.
- All tests still green.
- File-size invariant restored.

### Step 4 (optional, only if step 1–3 surface them): audit
        `effects.rs` and `decls.rs` for the same ambient-state pattern

`effects.rs` (591 LOC) and `decls.rs` (605 LOC) are within the
file-size target but may have their own duplicate `mem::replace`
clusters now that the pattern is recognized. If so, the same
`LowerCtx`-by-value substitution applies.

Defer the audit until after step 3 lands — premature scope expansion
is what caused the original drift. Run the e2e suite first; let real
failures drive any further refactoring.

## Out of scope

- Removing or renaming the `_monadic` suffix (deferred to cleanup
  commit per the main planning doc).
- Renaming `CodegenContext` to `ModuleCodegenContext` (deferred — the
  type-note comment in `Lowerer` can stay).
- Test reorganization. The 3,317 LOC of `lower_monadic/tests.rs` is
  big but it is the safety net for this refactor. Reorganizing it
  belongs in a separate pass after the e2e suite is green.
- Any optimization-stage work. Phase 2 (effect_opt rewrites) does not
  start until phase 1 ships.

## Post-refactor: resume e2e bug-hunt

After steps 1–3, return to the e2e failure list. Expected outcomes:

- Example 11 passes (step 2 fix).
- The class of "Pure-in-arm-conflated-with-Resume" failures is closed
  by construction.
- Remaining failures are individual bugs to triage, not architectural
  issues.

If a new failure surfaces and the fix wants ambient state again,
**stop and consult** — that is the signal that another distinction
needs to be added to `LowerCtx`, not that the field model was right
all along.

## Anti-goals

- **Don't rewrite the lowerer from scratch.** The MExpr → CExpr
  algorithm is correct. Only the state-holding shape is wrong.
- **Don't add a visitor framework.** Concrete `lower_*` methods with
  `&LowerCtx` are the right abstraction; a trait-based visitor adds
  indirection without payoff.
- **Don't change file-split boundaries beyond step 3.** The split
  proposed is the natural one; resist the urge to factor finer.
- **Don't promote counters into `LowerCtx`.** They are
  per-function-body monotonic, not per-derivation; moving them into
  the ctx would break stable Bind-K naming across tests.

## Time estimate

| Step | Effort |
|---|---|
| 1. Introduce `LowerCtx`, thread through API | 0.5 day (mechanical, ~30 call sites) |
| 2. Fix arm-K bug | 30 minutes |
| 3. Split `exprs.rs` | 1 hour |
| 4. Audit follow-up | 0.5 day if needed |

Plus 1–2 days resuming e2e bug-hunt on the refactored lowerer.
Total: ~3–4 days to phase 1 milestone (full e2e green under new path).
