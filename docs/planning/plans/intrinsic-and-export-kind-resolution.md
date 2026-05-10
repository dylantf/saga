# Resolved Symbol Carries Codegen Kind (Intrinsic / Inline / BEAM Function / External)

Plan for a follow-up refactor that pushes "what kind of thing this name is at
the BEAM layer" into the resolver's output, so the lowerer stops dispatching
on raw source spellings.

## Status

Not started. Captures the **Medium #2** finding from the system review of the
auto-load PR ([auto-load-qualified-modules.md](auto-load-qualified-modules.md)),
plus the design suggestion from that review.

## Motivation

After the auto-load fix landed, the lowerer still has two places where
codegen identity is decided by _string match on source spelling_, not by
resolved canonical identity:

### Site 1: `@builtin` intrinsic dispatch

[`try_lower_builtin_intrinsic`](../../../src/codegen/lower/builtins.rs) is
consulted from both the bare-call path
([lower/mod.rs:2492](../../../src/codegen/lower/mod.rs#L2492)) and the
qualified-call path ([lower/mod.rs:2463](../../../src/codegen/lower/mod.rs#L2463))
_before_ the resolver's `ResolutionMap` is consulted. It matches names like:

```rust
"print_stdout" | "Std.IO.Unsafe.print_stdout" => lower_builtin_print(args, false, false),
"print_stderr" | "Std.IO.Unsafe.print_stderr" => lower_builtin_print(args, true, false),
"dbg" | "Std.IO.dbg"                          => lower_builtin_dbg(args),
```

**The hijack risk**: a user-defined `fun print_stdout : String -> Unit` in
their own module would be intercepted by intrinsic lowering before the
resolver's identity (`MyModule.print_stdout` ≠ `Std.IO.Unsafe.print_stdout`)
gets a chance to disambiguate. Today this is latent — no stdlib name shadows
a builtin — but it's a correctness footgun waiting on a user-introduced
collision.

### Site 2: `@inline val` lookup

[`lower_var`](../../../src/codegen/lower/mod.rs#L745) and the qualified-
value-ref path ([lower/mod.rs:2882](../../../src/codegen/lower/mod.rs#L2882))
both consult `self.inline_vals` keyed by string. The current PR put the
_storage_ on a sound footing (cross-module RHSs lower under the defining
module's context, with topological dep-resolution and cycle detection),
but the _dispatch_ is still: "did the lowerer see this string in
`inline_vals`?" rather than "did the resolver tell us this is an inline
val?"

This means the `LocalFun + arity==0 + inline_vals[canonical].is_some()`
check at [lower/mod.rs:2742](../../../src/codegen/lower/mod.rs#L2742) and
[3069](../../../src/codegen/lower/mod.rs#L3069) is doing identity
discrimination after the fact, which a richer `ResolvedName` would have
encoded directly.

### The shared root cause

Three layers each hold a partial view of "what is this name":

| Layer              | Knows                                                 |
| ------------------ | ----------------------------------------------------- |
| Front-end resolver | "this qualified name canonicalizes to `Lib.foo`"      |
| Backend resolver   | "this is local / imported / external (callable)"      |
| Lowerer            | "is this string a builtin?" / "is it in inline_vals?" |

The lowerer has to rediscover special-case identity that earlier passes
already had enough information to record. The fix is to make
**resolution decide what symbol this is; lowering only executes the
symbol's codegen behavior**.

## Investigation Summary (already done)

Findings from the auto-load PR review:

- The string-based intrinsic dispatch was identified at
  [lower/mod.rs:2463](../../../src/codegen/lower/mod.rs#L2463) (qualified
  path) and [2492](../../../src/codegen/lower/mod.rs#L2492) (bare path).
  Both call into `try_lower_builtin_intrinsic`, the single source of truth
  for intrinsic _behavior_, but driven by spelling.
- `inline_vals` keying was confirmed to be canonical after the cross-
  module fix ([lower/mod.rs:1461-1505](../../../src/codegen/lower/mod.rs#L1461))
  — but the lookup sites still discriminate "is this name an inline val?"
  by table membership rather than by resolved kind.
- The current `ResolvedName` enum
  ([codegen/resolve.rs:163](../../../src/codegen/resolve.rs#L163)) only
  distinguishes `LocalFun` vs `ImportedFun`. Both carry callable metadata
  (arity, effects); neither carries "intrinsic" or "inline-val" identity.
- `ModuleCodegenInfo` ([typechecker/check_module.rs](../../../src/typechecker/check_module.rs))
  has `exports: Vec<(String, Scheme)>`, `external_funs`, and (after the
  current PR) `inline_vals: Vec<(String, Expr)>`. It does **not** mark
  `@builtin` exports as such — the lowerer infers it by string match.

## Proposed Design

### 1. Codegen-kind enum at the metadata layer

Add to `typechecker::check_module`:

```rust
pub enum ExportCodegenKind {
    BeamFunction {
        erlang_mod: String,
        erlang_name: String,
        arity: usize,
        effects: Vec<String>,
    },
    External {
        erlang_mod: String,
        erlang_name: String,
        arity: usize,
    },
    Intrinsic {
        intrinsic: IntrinsicId,
        arity: usize,
    },
    InlineVal {
        canonical_name: String,
    },
}

pub struct CodegenExport {
    pub source_name: String,
    pub canonical_name: String,
    pub kind: ExportCodegenKind,
    pub scheme: Scheme,
}
```

`ModuleCodegenInfo.exports` becomes `Vec<CodegenExport>` (the existing
`(String, Scheme)` shape collapses into the per-kind `kind` plus
`scheme`). `external_funs` and `inline_vals` go away — they're now just
two of the kinds.

Layering note: `ModuleCodegenInfo` is produced by the typechecker, so it
should not own lowered `codegen::cerl::CExpr` values. Inline-val metadata
can record that an export is inline and what its canonical identity is; the
lowered inline-expression cache should remain codegen-owned (for example on
`CompiledModule` or inside `Lowerer`) and should be produced under the
defining module's semantic context.

```rust
pub enum IntrinsicId {
    PrintStdout,
    PrintStderr,
    Dbg,
    CatchPanic,
    // Other future inline-only ops.
}
```

### 2. Backend resolver produces a richer symbol

In `codegen::resolve`:

```rust
pub enum ResolvedCodegenKind {
    BeamFunction { erlang_mod, erlang_name, arity, effects },
    External    { erlang_mod, erlang_name, arity },
    Intrinsic   { intrinsic: IntrinsicId, arity },
    InlineVal   { canonical_name: String },
}

pub struct ResolvedSymbol {
    pub canonical_name: String,
    pub source_module: Option<String>,
    pub kind: ResolvedCodegenKind,
}
```

`ResolutionMap` becomes `HashMap<NodeId, ResolvedSymbol>`. The
`LocalFun`/`ImportedFun` distinction folds into the kind (via
`source_module`). Producing the kind is direct: `register_canonical_qualified_scope`
and `register_import_aliases` already iterate `codegen_info`; with
`CodegenExport.kind` available, they read it through.

### 3. Lowerer becomes a pure consumer

```rust
match resolved.kind {
    ResolvedCodegenKind::Intrinsic { intrinsic, .. } =>
        self.lower_intrinsic(intrinsic, &args),
    ResolvedCodegenKind::InlineVal { value } =>
        value.clone(),
    ResolvedCodegenKind::BeamFunction { erlang_mod, erlang_name, arity, .. } =>
        self.emit_call(erlang_mod, erlang_name, arity, args),
    ResolvedCodegenKind::External { erlang_mod, erlang_name, arity } =>
        self.emit_call(erlang_mod, erlang_name, arity, args),
}
```

Both `try_lower_builtin_intrinsic(name: &str, ...)` and the
`inline_vals.get(&qualified)` checks go away. The bare-name and qualified-
name dispatch paths converge on the same switch.

`lower_intrinsic(IntrinsicId, &[Expr])` is the new internal entry point.
Its body is the existing `try_lower_builtin_intrinsic` body, just keyed
on the enum instead of a string.

The current state has two overlapping mechanisms tracking the same
information (intrinsic-ness, inline-val-ness): one in the lowerer, one
implicit in the codegen-info tables. Each new "kind of decl that doesn't
compile to a normal BEAM function" would add another such mechanism.
The proposed shape collapses both to a single fact recorded once
(at codegen-info collection) and consumed at the use site without
re-derivation.

## Migration Path

The work splits cleanly into two phases. **Phase 1 alone closes the
Medium #2 hijack risk** — that's the user-visible win. Phase 2 is
structural cleanup that pays off the next time someone adds a "decl
that doesn't compile to a normal BEAM function."

The phases are independent: Phase 1 can land and ship without Phase 2
ever being scheduled. The raw-spelling dispatch must not remain as an
unconditional fallback after Phase 1: falling back to
`try_lower_builtin_intrinsic("print_stdout", ...)` is exactly the user-defined
shadowing bug. If a migration fallback is temporarily useful, guard it by
resolved canonical identity so it only fires for known stdlib intrinsic
canonical names.

### Phase 1 — Builtin disambiguation MVP (~2 hours)

Scope: `@builtin` only. No `ResolvedName` rename, no `@inline val`
restructuring, no shape change to `ModuleCodegenInfo.exports`. Adds a
parallel intrinsic map and consults it before the existing dispatch.

1. **Define `IntrinsicId`** as a flat enum. Four variants today
   (`PrintStdout`, `PrintStderr`, `Dbg`, `CatchPanic`). Place it in a shared module
   (e.g. `src/intrinsics.rs`) so the typechecker can reference it
   without depending on codegen. Add `intrinsic_id_for_name(&str) ->
   Option<IntrinsicId>` and `lower_intrinsic(IntrinsicId, args)` to
   `codegen::lower::builtins`. Body of `lower_intrinsic` is the existing
   `try_lower_builtin_intrinsic` body, keyed on the enum. Include
   `Std.Process.catch_panic`; it is also `@builtin` and currently has its
   own spelling-based lowering path.

2. **Classify `@builtin` in `collect_codegen_info`**. Add
   `pub builtins: Vec<(String, IntrinsicId)>` to `ModuleCodegenInfo`.
   Populate by inspecting the `@builtin` annotation on
   `Decl::FunSignature`; map the source name to `IntrinsicId` via
   `intrinsic_id_for_name`.

3. **Build a `NodeId → IntrinsicId` parallel map**, NOT a richer
   `ResolvedName`. In `codegen::resolve::resolve_names`, after the
   existing scope construction, walk every `ExprKind::Var` /
   `ExprKind::QualifiedName` node whose canonical name appears in any
   loaded module's `codegen_info.builtins`. Emit
   `HashMap<NodeId, IntrinsicId>` alongside `ResolutionMap`.

4. **Update use-site dispatch**. At the qualified-call and bare-call
   sites in `lower/mod.rs` (lines 2463 and 2492), consult the parallel
   map *first*. If hit, dispatch to `lower_intrinsic(id, args)`.
   Otherwise continue through normal resolved-call lowering. Do not fall
   through to raw-spelling intrinsic matching unless it is guarded by
   resolved canonical identity.

After step 4, the user-visible Medium #2 hijack risk is closed:
a user-defined `fun print_stdout` resolves to `MyMod.print_stdout`,
which has no entry in any module's `builtins` table, so the parallel
map has no entry for that NodeId, and normal call lowering routes to the
user's function correctly.

**Tests for Phase 1** (must add):

1. **Shadowed-builtin disambiguation (bare)**: user module defines
   `fun print_stdout : String -> Unit`, calls it bare. Codegen routes
   to the user's function, not `io:format`.
2. **Shadowed-builtin disambiguation (qualified)**: same fun called
   as `MyMod.print_stdout`. Routes to user's fun.
3. **Stdlib qualified intrinsic still works**: `Std.IO.Unsafe.print_stdout`
   still inlines as `io:format` (regression for the auto-load fix).
4. **Aliased identity equivalence**: `import Std.IO.Unsafe as U;
   U.print_stdout "x"` lowers identically to the canonical form.
5. **Shadowed `catch_panic` disambiguation**: a user-defined
   `catch_panic` routes to the user's function; `Std.Process.catch_panic`
   still lowers through the intrinsic recovery boundary.

### Phase 2 — Structural cleanup (separate session, ~1–2 days)

Scope: collapse the parallel mechanisms into a unified
`ResolvedSymbol`. No new user-visible behavior — pure refactor.

5. **Same migration for `@inline val`**. The `inline_vals` table on
   `Lowerer` becomes a write-only cache of "values seen so far by
   canonical name during lowering"; the *decision* "is this an inline
   val?" comes from the resolver, not the table. Delete the
   `arity == 0 && inline_vals.get(&canonical_name)` discriminators at
   the `LocalFun` ref sites in `lower/mod.rs:2742` and `:3069`.

6. **Collapse `external_funs` into the kind enum**. `@external`
   exports get an `ExportCodegenKind::External` entry. The lowerer's
   existing external-fun dispatch becomes a kind match.

7. **Rename `ResolvedName` → `ResolvedSymbol`** with the unified
   shape from the Proposed Design section. Last step deliberately:
   `ResolutionMap` is consumed throughout the lowerer (`emit_call`,
   `lower_qualified_call`, `lower_resolved_fun_call`, value-ref paths,
   trait-dispatch sites), so the rename ripples broadly. Doing it
   earlier means every intermediate commit has both names floating
   around.

8. **Delete the vestigial string-match fallback**. After step 7, the
   parallel `NodeId → IntrinsicId` map from Phase 1 step 3 collapses
   into `ResolvedCodegenKind::Intrinsic`. The
   `try_lower_builtin_intrinsic` string match in `builtins.rs` can be
   removed; `lower_intrinsic` is called directly from the kind match.

Risk notes for Phase 2:

- Trait method dispatch (`DictMethodAccess`), dict constructors, and
  effect-call lowering all flow through similar machinery. The agent
  doing this work should expect to discover invariants the plan
  didn't anticipate and budget time for surfacing edge cases via the
  test suite.
- `ResolvedSymbol` has a real overlap with the front-end
  `ResolutionResult::values` (`ResolvedValue::Global { lookup_name }`).
  See Open Questions — the answer affects how aggressively to
  consolidate.

## Out of Scope

- Changing the `@builtin` / `@inline val` user-facing semantics.
- Source-language additions (e.g. user-defined intrinsics).
- LSP/tooling changes — `ResolvedSymbol`'s richer shape may help
  hover/go-to-def, but that's incidental, not a goal of this work.

## Open Questions

- Does `ResolvedSymbol` subsume the front-end `ResolutionResult`'s
  `ResolvedValue::Global { lookup_name }`, or should those remain
  distinct (front-end resolves _what value_, backend resolves _how to
  emit_)? Today they're separate; the answer affects how aggressively to
  consolidate.
- `IntrinsicId` placement: does it belong in `codegen::lower` (where the
  behavior lives) or in a shared `crate::intrinsics` module (so the
  typechecker can refer to it without depending on codegen)? Probably
  the latter to keep codegen as a downstream consumer.

## Files Touched (anticipated)

- [src/typechecker/check_module.rs](../../../src/typechecker/check_module.rs)
  — `ModuleCodegenInfo` shape; `collect_codegen_info` classifies kinds.
- [src/codegen/resolve.rs](../../../src/codegen/resolve.rs) —
  `ResolvedName` → `ResolvedSymbol`; `register_canonical_qualified_scope`
  and `register_import_aliases` propagate kind.
- [src/codegen/lower/mod.rs](../../../src/codegen/lower/mod.rs) — use-
  site dispatch becomes a `match resolved.kind`. Delete
  `inline_vals.get` discriminators at value-ref sites.
- [src/codegen/lower/builtins.rs](../../../src/codegen/lower/builtins.rs)
  — `try_lower_builtin_intrinsic(&str, ...)` replaced by
  `lower_intrinsic(IntrinsicId, ...)`.
- New: `src/intrinsics.rs` (or similar) hosting `IntrinsicId` if shared
  between typechecker and codegen.
