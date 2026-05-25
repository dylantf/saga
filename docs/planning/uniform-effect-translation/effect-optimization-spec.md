# Effect Optimization Specification

Companion to [uniform-effect-translation.md](../uniform-effect-translation.md)
and [monadic-ir-spec.md](./monadic-ir-spec.md). Concrete rewrite
specifications for the effect optimization stage (stage 11).

Status: **draft / design**. Subject to revision during implementation.

## Required context

Read these first:

1. [uniform-effect-translation.md](../uniform-effect-translation.md) —
   architecture. Especially the "Correctness gate" section.
2. [monadic-ir-spec.md](./monadic-ir-spec.md) — the IR these rewrites
   operate on.
3. [docs/effect-implementation.md](../../effect-implementation.md) — what the
   slow path compiles `Yield` and `Resume` into. Direct-call's job is to
   avoid that machinery when safe.

---

## Notation

Throughout this doc:

- `body[x := a]` means "substitute every free occurrence of `x` in `body`
  with `a`." Standard PL/lambda-calculus capture-avoiding substitution.
- Worked examples use pseudo-IR notation matching the `MExpr` variants from
  the IR spec.
- "Pure" without qualification means *recursively pure* — the MExpr
  contains no reachable `Yield`.

---

## Three rewrites

The stage runs three correctness-safe rewrites in a shared bottom-up
fixpoint:

1. **Bind-collapse** — eliminate `Bind(Pure(a), x, body)` by substitution
2. **Bind→Let promotion** — pure binders become Erlang lets
3. **Direct-call** — tail-resumptive `Yield` becomes inlined arm body

Order in the fixpoint loop: try direct-call, then Bind→Let, then
bind-collapse, bottom-up at each node. Loop until no rewrite fires.

---

## 1. Bind-collapse

### Rule

```
Bind { value: Pure(a), var: x, body: B }   ⟶   B[x := a]
```

where `a : Atom` (by IR construction).

### Substitution shape

Substitution is `subst(B, x, a) -> MExpr`, recursing structurally and
replacing free `Atom::Var { name: x, .. }` with `a` everywhere `Atom`
appears (`App.head`, `App.args`, `Case.scrutinee`, `If.cond`, `Yield.args`,
`Resume.value`, `Pure`, nested `Ctor.args`, …).

Because `a` is an `Atom` and every variable use-site lives inside an
`Atom`, substitution is shape-preserving — no `MExpr` node ever changes
type.

### Capture-avoidance

Three cases:

1. **`a` is a non-Lambda atom (Var, Lit, atomic Ctor/Tuple/Record).** No
   bound variables of its own; no capture possible.

2. **`a` is `Atom::Lambda { params, body }`.** Carries free variables from
   the enclosing scope. The pipeline maintains Barendregt-fresh `MVar`s; if
   we cannot guarantee uniqueness, alpha-rename `body` binders that collide
   with `a`'s free vars before substituting.

3. **Shadowing of `x` inside `B`.** Any binder in `B` that re-binds `x`
   (`Let { var: x, … }`, `Lambda { params containing x, … }`,
   `Bind { var: x, … }`, case-arm patterns binding `x`) stops substitution
   in that subtree.

### Termination

Each firing strictly decreases the count of `Bind` nodes whose `value` is
`Pure(_)`. Substitution cannot create new `Pure`/`Bind` nodes — only
replaces `Atom` leaves with `Atom` leaves. Therefore fixpoint terminates
in ≤ N steps where N is the initial count of such binds.

### Traversal

Bottom-up, single pass with outer loop until no rule fires. After firing,
no need to re-scan all of `B` — substitution into an already-normalized `B`
cannot expose new `Bind(Pure(_), …)` opportunities not already collapsed
by the bottom-up pass.

### Worked examples

**A — pure chain collapses fully:**
```
Bind { value: Pure(Lit 1), var: x,
  body: Bind { value: Pure(Var x), var: y,
    body: Pure(Var y) } }

⟶  Bind { value: Pure(Lit 1), var: y, body: Pure(Var y) }
⟶  Pure(Lit 1)
```

**B — pure ANF threading evaporates:**
```
Bind { value: Pure(Ctor "Some" [Var n]), var: r,
  body: App { head: Var f, args: [Var r] } }

⟶  App { head: Var f, args: [Ctor "Some" [Var n]] }
```

**C — effectful bind is left alone:**
```
Bind { value: Yield { op = get, args = [] }, var: s,
  body: App { head: Var print, args: [Var s] } }
```
No firing. `value` is `Yield`, not `Pure`.

### Soundness

Monad left-identity `bind(η a, k) ≡ k a`. **Sound unconditionally** —
independent of handler-analysis flags, independent of multishot
considerations. The rewrite is pure capture-avoiding substitution; it
does not reify continuations, does not interact with `resume`, and is
unaffected by how many times any surrounding continuation might be
called. The only multishot-sensitive rewrite in this stage is direct-call
(§3); bind-collapse and Bind→Let promotion (§2) fire unconditionally
given their own local predicates.

---

## 2. Bind→Let promotion

### Rule

```
Bind { var, value, body }   ⟶   Let { var, value, body }
```

iff `value` is **recursively pure** — i.e. `Yield` is not reachable from
`value`.

### Purity predicate

`pure(m: &MExpr) -> bool`:

| Variant | Pure? |
|---|---|
| `Pure(_)` | yes (atom is pure by IR construction; lambdas are pure to construct even if their bodies yield — closures are values, calling them is what may yield) |
| `Let { value, body, .. }` | `pure(value) && pure(body)` |
| `Case { arms, .. }` | every arm body pure, every guard pure |
| `If { then_branch, else_branch, .. }` | both branches pure |
| `App { head, .. }` | callee's effect row is `{}` (look up via `ResolutionMap` + typechecker effects) |
| `FieldAccess { .. }`, `RecordUpdate { .. }`, `DictMethodAccess { .. }`, `BinOp { .. }`, `UnaryMinus { .. }`, `BitString { .. }` | yes (no side effects in IR semantics) |
| `ForeignCall { .. }` | yes if marked pure in the FFI signature, else no (conservative default: no) |
| `Yield { .. }` | **no** |
| `Bind { .. }` | **no** (it's still effectful even if its value happens to be pure — the rewrite is the very thing that would change that) |
| `With { .. }` | yes if `body` is pure under the new handler's evidence; equivalently, yes if the handler discharges the only effects in `body`. Conservative: no, unless body is statically pure. |
| `Resume { .. }` | no (semantically yields control to the captured continuation) |
| `Receive { .. }` | no (mailbox interaction) |
| `Lambda { .. }` body | does **not** affect purity at the use site — constructing a closure is pure |

### Where the effect-row info comes from

`App { head, .. }`: the callee's effect row is known. Cases:
- `head` is `Atom::Var(x)` and `x` is a local function definition — look up
  `fun_effects` for that definition.
- `head` is `Atom::QualifiedRef { module, name }` — look up
  `ResolutionMap[source_node_id]` to find the callee, then its
  `fun_effects`.
- `head` is `Atom::Lambda { … }` — the lambda's body's effect row is
  known from the typechecker at the lambda's NodeId.
- `head` is `Atom::DictRef`, `Atom::Symbol`, or otherwise dynamic — be
  conservative and treat as effectful.

### Termination

Each firing strictly decreases the count of `Bind` nodes with pure
`value`. Bounded.

### Soundness

A `Bind` whose `value` provably never yields is semantically equivalent to
a `Let`. The monadic sequencing carries no effect to discharge. The lowerer
emits an Erlang `let` instead of CPS-continuation threading; observable
behavior is unchanged.

### Worked example

```
fun do_thing () = {
  let x = perform get
  let y = pure_helper x      -- pure_helper has effect row {}
  perform put y
}
```

After translation:
```
Bind { value: Yield { op = get, .. }, var: x,
  body: Bind { value: App { head: pure_helper, args: [Var x] }, var: y,
    body: Yield { op = put, args = [Var y] } } }
```

After bind→let promotion (middle binder's value is pure):
```
Bind { value: Yield { op = get, .. }, var: x,
  body: Let { value: App { head: pure_helper, args: [Var x] }, var: y,
    body: Yield { op = put, args = [Var y] } } }
```

The outer and inner `Yield`s are unchanged. The middle binder becomes a
plain Erlang `let` at lower time. `op → pure → op` chains compose correctly.

---

## 3. Direct-call (tail-resumptive)

### What "resolves statically" means

A `Yield { op, args, source }` resolves statically to a handler arm iff:

- The innermost enclosing `With { handler, body, … }` (along the lexical
  path to this `Yield`) servicing `op`'s effect has `handler` as
  `MHandler::Static { arms, … }` — **not** `MHandler::Dynamic`.
- The matching arm in that `Static` handler is a literal `MHandlerArm`
  for `op`.

Concretely: effect optimization carries `handler_stack: Vec<&MHandler>`
while walking. On entering `With { handler, body, … }`, push; on leaving,
pop. **Reset on entering `Lambda` body** (a lambda may be invoked outside
the current handler scope) — save and restore the stack.

When a `Yield { op, … }` is encountered, scan the stack from top to find
the matching effect. If found and the matched entry is
`MHandler::Static`, the resolution is static. If the matched entry is
`MHandler::Dynamic`, **skip** — `Yield` survives unchanged, falls
through to the lowerer's standard evidence-lookup path. (A dynamic
handler for the effect shadows any outer static handler for the same
effect — innermost-wins, per the runtime evidence layout.)

### Rule

For matching arm `MHandlerArm { params: [p1, …, pn], body: A, id: arm_id }`
tagged `ResumptionKind::TailResumptive` in
`HandlerAnalysis.resumption[arm_id]`:

```
Bind { value: Yield { op, args: [v1, …, vn], .. }, var: y, body: K }
⟶
Bind { value: inline(A, [p1 := v1, …, pn := vn], Resume → Pure), var: y, body: K }
```

where `inline` performs:
1. Parameter substitution: `A[p1 := v1, …, pn := vn]`.
2. Resume rewrite: every `Resume { value: a, .. }` in the resulting body
   becomes `Pure(a)`.

After the rewrite, run bind-collapse — the freshly produced `Pure(a)` is
exactly what bind-collapse eats.

If the `Yield` was not inside a `Bind` (tail position of an `MExpr`), the
rewrite is the same: substitute params, rewrite `Resume(a) → Pure(a)`,
replace the `Yield` with the rewritten arm body.

### How we know `Resume(v)` is in tail position

We don't recompute — `HandlerAnalysis` (stage 8.5) already classified the
arm as `TailResumptive`, which *means* "every tail position is `Resume`
and `Resume` appears nowhere else." Pass 3 trusts the tag and applies the
substitution `Resume(a) → Pure(a)` unconditionally over the arm body.

### Worked example

Handler:
```
handle State {
  get () -> resume state              -- TailResumptive
  put s' -> resume () with state := s' -- (not TailResumptive — set aside)
}
```

Inside the `with`-body:
```
Bind { value: Yield { op = get, args = [] }, var: s,
  body: App { head: print, args: [Var s] } }
```

Apply rewrite: substitute params (none), rewrite `Resume(Var state) → Pure(Var state)`:

```
Bind { value: Pure(Var state), var: s,
  body: App { head: print, args: [Var s] } }
```

Then bind-collapse:

```
App { head: print, args: [Var state] }
```

Zero `Yield`, zero `Bind`, zero continuation closure. Matches the sanity
invariant in the planning doc.

### Inlined arm body may contain `Bind`/`Yield`

Carries through verbatim. Those inner `Yield`s have their own handler stack
— resolved against the *same* lexical context the original `Yield` lived
in (since the inlining happens at that site). If they point at a different
handler frame, they're resolved against *that* frame's static
resolvability. Each inlining decision is local.

Inlining cannot accidentally hoist a `Yield` out from under its handler —
the inlined body sits in the same lexical position as the original
`Yield`.

### Soundness conditions

- Arm tagged `TailResumptive`. **Never fire on `OneShot` or `Multishot`.**
  This is the multishot-sensitive rewrite (the one the planning doc's
  "correctness gate" section scopes to).
- Handler resolved as `MHandler::Static`. On `MHandler::Dynamic`, skip
  — `Yield` stays; the lowerer emits the slow evidence-lookup-plus-apply
  path.
- No intervening `MHandler::Dynamic` for the same effect between the
  `Yield` and the resolved static arm. (Handler-stack walk picks the
  innermost matching entry; if a `Dynamic` shadows the `Static`, give up.)
- Capture-avoidance during parameter and resume substitution.

### Conservativeness rule

`HandlerAnalysis` errs toward `Multishot` whenever uncertain. Direct-call
inherits this — we trust the tag, never widen eligibility. False
`Multishot` is fine (slow). False `TailResumptive` would be a miscompile.

---

## Ordering / fixpoint

Single shared bottom-up fixpoint:

```
loop {
    let mut changed = false;
    walk MProgram bottom-up:
        at each node, try direct-call;
        at each node, try Bind→Let promotion;
        at each node, try bind-collapse;
        if any fired, set changed = true.
    if !changed { break }
}
```

Rationale:

- **direct-call → bind-collapse** is productive: direct-call produces
  `Pure(a)` in tail position of the inlined arm body; the enclosing `Bind`
  matches bind-collapse and eliminates the binder.
- **bind-collapse → Bind→Let** can also be productive (collapsing reveals
  a pure expression underneath that was previously gated by a bound name).
- **Bind→Let → direct-call** doesn't compose (Let doesn't host Yield) —
  no productive sequence there.

Termination: each firing strictly decreases either `Bind` count
(bind-collapse, Bind→Let), `Bind`-with-`Pure`-value count (bind-collapse
alone), or `Yield` count at statically-resolvable `TailResumptive` sites
(direct-call). No rule resurrects another's targets indefinitely. Cap
iterations at `O(size(MProgram))` as a paranoid invariant.

---

## Handler-flag interaction

| `ResumptionKind` | bind-collapse | Bind→Let | direct-call |
|---|---|---|---|
| `TailResumptive` | always | always | **enabled** |
| `OneShot` | always | always | **disabled** (future work: separate "inline-with-explicit-continuation" rewrite) |
| `Multishot` | always | always | **disabled** |

- bind-collapse and Bind→Let are independent of handler flags. They're
  monad laws / purity rewrites.
- Direct-call is gated solely by `TailResumptive` + static resolvability.
- No fallback that fires on `OneShot` or `Multishot`.

---

## No-op identity

The trivial implementation is correct:

```rust
pub fn run(m: MProgram, _h: &HandlerAnalysis, _e: &EffectInfo) -> MProgram {
    m
}
```

This is sound because:
- Uniform monadic translation produces a fully correct, fully-yielding
  program. Every `perform` becomes `Yield`; evidence threaded by the
  lowerer; handlers invoked via the evidence vector.
- The lowerer consumes any well-formed `MExpr`. It handles
  `Bind { value: Pure(a), … }` by emitting a let-binding to `a`
  (equivalent but with a wasted closure cycle), and `Yield` via uniform
  evidence lookup.

Consequences:
- Program is in the "expected perf valley" — pure ANF code pays an
  allocation per bind and a closure per continuation.
- This is the **test oracle** for differential testing — optimized output
  must produce identical observable behavior to the no-op-pass output.

Recommended scaffolding: ship `run` with a `skip: bool` (or env-toggle)
that short-circuits to identity. The rest of the pass is feature-gated
behind it during early development.

**Incremental order:** bind-collapse + Bind→Let first (recovers most of the
pure-code regression); direct-call later as a strict improvement.
