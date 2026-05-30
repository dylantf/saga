# Plan: Infer effects for local (non-`pub`) functions

Status: **scoping** (not yet implemented). Owner: Dylan.

## ⚠️ Read this first (post-compaction context)

If you are picking this up fresh: **read the full language guide before touching
anything** — `/Users/dylan/projects/saga-website/public/llms-full.txt` (~5.8k
lines, the concatenated user guide + worked examples). You need the real
semantics of effects, `needs`, handlers (`with`), `resume`, `pub`, and the
local-vs-top-level function distinction, or you will make wrong assumptions
about effect propagation. Do not work from memory of a summary.

Repo: `/Users/dylan/projects/saga` (this compiler). Language is HM + traits
(dictionary passing) + algebraic effects with effect-row inference, compiling to
Core Erlang / BEAM.

## The feature

Today: a function that performs an effect handled _higher up the call chain_
(the `with` is in a caller) must carry a `needs {E}` annotation, **even if it is
a local, non-`pub` function**. See the gate below.

Goal: **drop the `needs` requirement for local (non-`pub`) functions.** Their
effect row is inferred (it already is — see findings), so a single-file program
can be written with zero type/effect annotations. `pub` functions still require
a full signature (that is the only place `pub` attaches, and it is the module
contract boundary — keep it).

Why (the real reason, not just demos): a function's type in Saga _is_
`(Type, EffectRow)`. For locals we already infer the `Type` half; mandating the
`EffectRow` half is inconsistent — we infer half a type and require the other
half. Making the rule "locals fully inferred (type AND effects); `pub` fully
annotated" is more consistent and more teachable.

Cost: loss of _local_ effect visibility (can't see "this helper logs/fails/hits
DB" from its signature). Mitigation: **LSP inlay hints** showing the inferred
effect row on local functions — recovers visibility in-editor with no source
tax. Pair the relaxation with the hint. (LSP already exists; see roadmap.)

## Findings so far (verified empirically on `target/debug/saga`)

- The gate is `TypeChecker::check_effects_via_row` at
  `src/typechecker/effects.rs:151`. For an unannotated function it is called
  with an **empty closed declared row**, so every inferred body effect is
  "undeclared" → error `"<fn> uses effects {E} but has no 'needs' declaration"`
  (effects.rs:191-198). Same message duplicated for trait-impl methods
  (`check_traits.rs:894`) and the main fun-decl path (`check_decl.rs:2601`).
- The inferred effect row already EXISTS on the function type:
  `check_decl.rs:1370-1378` sets an unannotated function's `effect_row` to its
  inferred body effects (`all_body_effs`).
- **CRITICAL UNRESOLVED RISK — verify before/while implementing:** in the
  empirical test, when a local fn used `Log` (handled at `main`), `main` ALSO
  warned _"expression does not use effects {Log}; handler is unnecessary"_. That
  means the local fn's effect **did not propagate to its caller**. If we simply
  delete the gate and propagation genuinely doesn't happen, we get something
  _worse than today_: local performs effect → nothing carries it up → `main`
  doesn't require a handler → compiles → **effect call hits no handler at
  runtime → crash.** The gate may currently be standing in _for_ propagation,
  not supplementing it. So the change is NOT "delete the check"; it is "delete
  the check AND ensure the inferred row propagates up the call chain so callers
  / `main` still correctly demand a handler."

## Scoping checklist (the compiler walk)

1. Trace how a CALLER consumes a callee's effect row during inference
   (`src/typechecker/infer.rs` application logic; `param_absorbed_effects`;
   `check_decl.rs:1200` "unhandled" path; how `with` subtracts effects).
   Determine: is an unannotated fn's scheme effect row read by callers, or
   zeroed? (The warning says zeroed — confirm and find where.)
2. Find every call site of `check_effects_via_row` and classify which are the
   "no needs declaration" (unannotated) path vs the "not declared in needs
   clause" (partial annotation — KEEP) path.
3. Decide the relaxation condition: skip the gate only when the decl is
   non-`pub` AND has no annotation. Annotated functions (partial `needs`) keep
   the existing "not declared in needs clause" error. `pub` keeps requiring full
   signature.
4. Mutual recursion: confirm inferred effect rows on mutually-recursive locals
   converge without the annotation breaking the fixpoint cycle.
5. Decisive experiment: disable the unannotated-path branch, rebuild, run
   `/tmp/.../e1.saga` (local fn + Log handled at main) and a two-hop case.
   PASS = main correctly sees `{Log}`, handler is used (no "unnecessary"
   warning), program runs, AND removing the handler correctly errors at main.
   FAIL = effect vanishes / unhandled effect reaches runtime.

## Verdict on size: QUICK CHANGE (prototype proven end-to-end)

Core compiler change = **one condition**. At `check_decl.rs:1295-1305`, gate the
`check_effects_via_row(...)?` call on `annotation.is_some()` so unannotated
functions skip the declared-vs-body check and let their inferred row commit:

```rust
if annotation.is_some() {
    self.check_effects_via_row(&all_body_effs, &declared_row,
        &format!("function '{}'", name), err_span)?;
}
```

(This edit is currently LIVE in the working tree as the prototype.)

### Why it's safe (all verified empirically on debug build)
- Propagation already works with NO annotated/unannotated distinction:
  `infer.rs::emit_saturated_call_effects` reads the effect row off any
  `Type::Fun(_, _, row)`. The inferred row was always computed
  (`check_decl.rs:1370-1378`); the ONLY bug was the gate's `?` returning early
  before the type committed to env (lines 1394/1435), so callers saw the
  pre-bound *pure* placeholder. Removing the early error fixes that — the row
  commits and propagates for free.
- Entry-point safety net HOLDS: unhandled effect propagated through two
  unannotated locals → correct error at `main` ("`main` cannot use `needs` ...
  no caller to provide handlers for {Log}"). No runtime hole.
- Annotated contracts fully preserved: annotated fn with partial `needs` still
  errors ("not declared in its 'needs' clause"); annotated pure fn whose body
  uses an effect still errors ("has no 'needs' declaration"). Relaxation fires
  ONLY when there is no annotation (⟺ private, since `pub` requires one).

### Verified working
handled-at-main; two-hop; inner `let`-bound fn; mutual recursion; full
end-to-end run (printed "Hello, world!").

### Policy (clean rule)
Relax ONLY unannotated function bindings. Keep strict: `pub` (needs annotation
anyway), annotated private fns (contract), trait-impl methods
(`check_traits.rs:894` — trait is the contract), named handlers
(`check_decl.rs:2601` — declared/exportable). Rule: "declared/named/exported
things state their effects; anonymous/local bindings infer them."

### Work to land it (the actual feature size — ~half a day)
1. Keep the one-line gate (done in prototype).
2. Rewrite 5 typechecker unit tests that assert the OLD error (all have passing
   annotated siblings — invert to assert success + inferred effect):
   `effect_call_without_needs_is_error`,
   `effect_propagates_through_function_call`,
   `handler_arm_body_unhandled_effect_propagates`,
   `lambda_effects_propagate_to_enclosing_function`,
   `with_subtracts_only_handled_effect`.
3. Run the FULL suite (`cargo test`) — e2e/.saga programs already carry
   annotations so relaxing a requirement is backward-compatible; expect only the
   5 above. Confirm.
4. **MULTI-MODULE EDGE (Dylan's raise) — CONFIRMED SAFE empirically.** Test
   lives in `examples/module-test/` (`lib/EffLib.saga` = module A: private
   unannotated effectful helpers `log_access`/`record_visit` + `pub visit`
   wrapper + `pub accessor` HO value; `lib/Main.saga` = module B importing and
   handling). Run with `saga run` from that dir (NOT `saga run <file>` — single-
   file is script mode, no user imports). Results:
   - POSITIVE: runs end-to-end, prints `accessed profile:alice / bob / carol`.
     Inferred {Audit} from private helpers propagates through the `pub` boundary;
     B handles it. Higher-order value (`accessor () |> apply`) also carries the
     effect across and is handled.
   - NEGATIVE (a) CONFIRMED: dropping `needs {Audit}` from `pub visit` makes
     EffLib fail to compile ("function 'visit' uses effects {Audit} but has no
     'needs' declaration"). Effect cannot cross a module boundary undeclared.
   - STILL TODO (b): `saga build --lib` type-info SIDECAR — confirm a
     precompiled library serializes the wrapper's effect row so a downstream
     project (not same-build) enforces it. In-project multi-module path is
     proven; the precompiled-lib path is a separate serialization path.
   - PRE-EXISTING WRINKLE (not from this change; accessor is annotated): the HO
     `accessor : Unit -> (String -> Unit needs {Audit})` emits a spurious
     "declares needs {Audit} but never uses it" warning — the unused-effects
     heuristic mis-attributes the inner (returned) arrow's row to the outer fn.
     Runs correctly; warning only. File separately if it bothers you.
5. Guide updates: the "needs clause" / "Performing effects" sections
   (llms-full.txt ~1666-1700) and "Visibility" (~2957) currently imply `needs`
   is required for effect-carrying fns and only show PURE inferred privates.
   Add: private functions infer effects too.
6. Roadmap note under Type Checker (HM).

### Follow-up (separate, optional)
LSP inlay hints showing inferred effect row on local fns — recovers local effect
visibility lost by dropping the annotation. Pairs with this; not a blocker.

## PR target
Land on `main` (typechecker is untouched by the uniform-effect refactor, so no
dependency on that branch). The prototype edit is in the working tree on the
`uniform-effect-translation` branch and is uncommitted — carry it to `main`.
