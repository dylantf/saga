# Value Bindings & Visibility

Status: **design notes — agreed direction, not scheduled. Defer until after
the [uniform-effect-translation](./uniform-effect-translation.md) cleanup
commit. See "Why not now" below.**

## TL;DR — decisions

- **Eliminate the `val` keyword.** A top-level zero-parameter binding
  `foo = e` becomes the value-binding form — exactly what `val foo = e` is
  today. It is a *value*, not a function.
- **Zero-arg *functions* stay banned.** `foo () = e` remains the only
  "runs per call / deferred / effectful" form. This change adds zero-*param
  value bindings*; it does **not** add callable zero-arg functions. This
  distinction is load-bearing — see Rationale.
- **`@inline` becomes an attribute** on a value binding (`@inline foo = e`),
  replacing `@inline`-on-`val`.
- **Value bindings must be pure.** An effectful RHS is a compile error that
  directs the user to `foo () = ...`. (Same rule `val` enforces today, moved
  to the new syntax — and it doubles as the teaching moment the keyword used
  to provide.)
- **Visibility stays local-pub.** `pub` keeps living on the signature. A
  public value is `pub foo : Int` + `foo = e`, identical mechanism to a
  function. We are **not** switching to a module-header `exposing (...)` list.
- **Add `pub import Mod (name)` for re-exports** — Rust's `pub use`
  analogue — replacing today's wrapper-function-with-duplicated-signature
  workaround.

## Open questions

- **Internal visibility tier?** A `pub(internal)`-style tier (project-visible
  but not externally public) is only needed for *true facade encapsulation*:
  internal modules whose functions are reachable **only** through a
  re-exporting facade. If facades merely curate names that are already `pub`,
  `pub import` alone suffices and we skip the tier. Decide based on whether we
  want real encapsulation behind facades. This is orthogonal to the `val`
  work and to the local-pub-vs-`exposing` choice.
- **Future `const`.** A compile-time-*required* inlined constant, distinct
  from the runtime `/0` value binding. The only real delta from
  `@inline foo = e` is *guaranteed* vs *best-effort* inlining: a real `const`
  requires a compile-time-evaluable RHS and forbids emitting a `/0` fallback.
  Punted — `@inline` covers the need until perf demands the guarantee.

## Rationale

### Why the keyword existed at all

Saga uses Haskell-style binding syntax (`foo = e`, signature on a separate
`pub foo : T` line). Haskell's `foo = e` is unambiguous between "a constant"
and "a nullary computation" **only because Haskell is lazy and pure**:

- Pure ⇒ the *number* of evaluations is unobservable (referential
  transparency).
- Lazy ⇒ the *timing* of evaluation is unobservable (thunk, forced on demand,
  memoized as a CAF).

Saga is **strict and effectful**, so both properties are gone: *when* a
binding runs and *how many times* its effects fire are both observable.
A strict+effectful language therefore **must** distinguish "compute once as a
value" from "compute each call" — it cannot collapse them the way Haskell
does. ML (`let x = e` vs `let f () = e`) splits them by the presence of
parameters. Saga split them with `val foo = e` (value) vs `foo () = e`
(function), and banned the ambiguous middle case (zero-arg functions).

### Why eliminating `val` is safe

A zero-param **value binding** is not a function, so it never has the
call-site ambiguity that got zero-arg *functions* banned: you reference `foo`
as a value, you never "call" it. (A callable nullary function would be invoked
by writing bare `foo`, indistinguishable from a value reference — *that's* why
the function form needs `()`.) So `foo = e` as a value form does not reopen
the thing we closed; `foo () = e` stays as the deferred/effectful form.

`val` is also observationally just a pure constant (see next section), so bare
`foo = e` meaning "foo is that value" is honest to any ML/Haskell reader. The
keyword's only remaining job — letting a constant be `pub` — disappears under
local-pub, where `pub foo : T` + `foo = e` works exactly like a function.

### BEAM grounding: constants are zero-arity functions

Erlang has no top-level value bindings. Module constants are zero-arity
functions: `pi` is `math:pi/0`, called as `math:pi()`. Today's `val` already
lowers to a `/0` function (see [atom.rs:414](../../src/codegen/lower/atom.rs#L414),
regression test [tests.rs:1402](../../src/codegen/tests.rs#L1402)) and is
recomputed on each reference — `math:pi()` does the same. Erlang doesn't
memoize module constants either, so Saga's recompute-on-use is the *native*
model, not a quirk. This is also **why `val` requires a pure RHS**:
recomputation is only observationally a constant when it's pure.

The two BEAM mechanisms map onto the two knobs:

- zero-arity function (`math:pi/0`) ↔ plain value binding `foo = e` → `foo/0`.
- macro (`-define(PI, ...)` → `?PI`) ↔ `@inline`. Unlike an Erlang macro
  (shareable only via `.hrl` includes), an `@inline` value binding can be both
  inlined *and* exported with a real signature — strictly better.

### Visibility: why local-pub, not `exposing`

There are two independent "force a signature" rules: **public ⇒ annotated**
(mechanized today by `pub`-living-on-the-signature) and **effectful ⇒
annotated** (a standalone check, regardless of visibility). The point of
requiring annotations on public functions is to keep inference *module-local*:
cross-module typechecking only ever consumes *written* signatures, never
inferred ones, so a body change can't silently mutate the public API. **Any
design must preserve: everything visible outside its module has a written
type.**

`exposing (...)` (Elm-style) was considered. It puts the API in one readable
place and dissolves the `val`/`pub` entanglement, but it adds a sync point,
trades the structural "can't be public without a sig" guarantee for a check,
and needs a careful answer for `exposing (..)`. Local-pub was preferred:
it colocates visibility + type + docs and makes the invalid state
unrepresentable. The multi-clause objection (Elixir repeats `def`/`defp` per
clause) does **not** apply — `pub` sits on the single signature line, clauses
stay bare:

```
pub fun safe_div : Int -> Int -> Float
safe_div x 0 = fail! "div by 0"
safe_div x y  = x / y
```

Re-exports — the one real gap in local-pub — are handled by `pub import`
(Rust `pub use`) rather than by adopting `exposing`. The annotation check
rides on it for free: a re-exported name crossed a module boundary, so it is
already annotated.

## Why not now

This is a **surface-language change**, which the in-flight
[uniform-effect-translation](./uniform-effect-translation.md) PR explicitly
lists as a non-goal ("Changing the surface language. No new keywords"). More
importantly, **it would not relieve the friction that prompted it.** The
zero-arity special-casing biting that PR is in *codegen*, not *syntax*:

- **Blocker 8d** (zero-arity value functions as returned function values,
  `apply 'increment'/0()` vs uniform `increment/2`) is a calling-convention
  fix. Renaming `val foo` → `foo` changes nothing — bare `foo = e` still
  lowers to `/0`.
- **Blocker 8i** (stale `InlineVal` cross-module resolution) persists because
  `@inline` survives the elimination; the inline-value cross-module behavior
  still needs to be correct.

So: **fixing zero-arity value lowering is required now** (8d/8i, can't ship
without it); **eliminating the `val` keyword is a separable surface change to
defer.** Deferring is strictly cheaper — after the cleanup commit there is one
lowerer (`lower/`), not two, so the migration touches lowering once instead of
fighting old/new parity while also churning syntax.

## Migration sketch (when we do it)

Needs a real scoping pass before execution; this is the rough surface area.

- **Lexer/parser:** remove the `val` keyword/token; accept a top-level
  zero-param binding `foo = e` as a value binding. Confirm `@inline` parses as
  an attribute on it.
- **AST:** fold `Decl::Val` (and `MDecl::Val` in the monadic IR) into the
  ordinary binding/decl representation, or a dedicated value-binding node.
- **Typechecker:** register zero-param bindings as values; move the
  pure-RHS check here, with the "use `foo () = ...` for effects" diagnostic.
- **Codegen:** value binding → `/0` (unchanged lowering); carry over the
  `@inline` substitution path (the `InlineVal` resolution concept survives,
  just no longer keyed off the keyword).
- **`pub import`:** new re-export form + the "re-exported name must be
  annotated somewhere" check.
- **Stdlib + examples:** mechanical sweep — `val X = …` → `X = …`,
  `@inline val X = …` → `@inline X = …`.
- **Docs:** syntax reference, `llms-full.txt`, and **CLAUDE.md** — its
  "no zero-argument functions" note must be reworded to "no zero-arg
  *functions*; zero-param *value bindings* are written `foo = e`," and its
  link to the nonexistent `docs/const-bindings.md` is already stale.
