# Row widening for list literals

## Problem

When a list literal is unified against a parameter of type `List (T needs {..e})`,
elements with different effect rows fail to unify. The list type variable gets
pinned to the row of the first/some element and subsequent elements with
disjoint effects are rejected.

This breaks a natural and useful pattern: a heterogeneous list of effectful
callbacks where each callback declares only the effects it actually uses.

## Minimal repro

```saga
effect Foo { fun foo : Unit -> Unit }
effect Bar { fun bar : Unit -> Unit }

fun do_foo : Unit -> Unit needs {Foo}
do_foo () = foo! ()

fun do_bar : Unit -> Unit needs {Bar}
do_bar () = bar! ()

fun pure_thing : Unit -> Unit
pure_thing () = ()

fun take_callbacks : List (Unit -> Unit needs {..e}) -> Unit needs {..e}
take_callbacks fs () = case fs {
  [] -> ()
  f :: _ -> f ()
}

main () = {
  take_callbacks [pure_thing, do_foo, do_bar] () with {
    foo () = resume (),
    bar () = resume (),
  }
}
```

Expected: compiles. Each element's row fits under the row variable `..e`, so
the type checker should solve `..e` to the union of all element rows.

Actual: type mismatch. Saga pins `..e` to the row of the first element it
sees and then rejects elements whose row isn't a subset of that.

## Where this hurts in practice

This came up immediately while building [Edda](../../../edda), the prototype
web framework. Routes have heterogeneous effects: a public route is pure, an
authed route `needs {Auth}`, a route using ambient context `needs {ReqCtx}`,
etc. The framework's central dispatch combinator is:

```saga
pub fun choose : List (Request -> Response needs {Skip, ..e})
              -> Request -> Response needs {..e}
choose routes req = case routes {
  [] -> not_found
  r :: rest -> r req with { skip () = choose rest req }
}
```

And user code is:

```saga
choose [
  route GET "/"        home,        # needs {Skip}
  route GET "/whoami"  whoami,      # needs {Skip, ReqCtx}
  route GET "/account" account,     # needs {Skip, Auth}
]
```

Today this is a type error. The workaround is to annotate every route with
the union of all effects the app uses (`needs {Skip, ReqCtx, Auth}`), even
pure ones. That:

- forces routes to over-declare effects they don't perform,
- triggers the "declares X but never uses it" warning on every pure handler,
- couples every route to the union of the whole app's effects.

## Proposed fix

When unifying a list literal `[e1, e2, ...]` against an expected type
`List (T needs {..e})`, solve `..e` by taking the **union** of the rows
present in `e1, e2, ...` (rather than picking one element's row and
requiring the others to match).

Concretely, for the list element row positions:

- Each `ei` contributes its concrete effect row.
- The solver picks `..e = union(rows(e1, ..., en))`.
- Each `ei` then unifies against the unified row by row subsumption — the
  upper-bound reading of `needs` at the unification site.

This is a targeted change: it only fires when the expected element type is
row-polymorphic. Single-function calls already work and shouldn't be
affected. Concrete-row positions (e.g. `List (Unit -> Unit needs {Foo})`
with no row variable) should continue to require exact match.

## What this does _not_ change

- The "declares X but never uses it" warning at function _definition_ sites
  stays correct. We're widening at _use_ sites, not silently allowing lies
  in declarations.
- Calling a function whose row claims more than the caller provides is still
  an error. `f : T needs {Auth}` called from a context without Auth is
  rejected as it should be.
- The semantics of `needs` as documentation/audit doesn't change. Each
  function's signature still describes exactly what it does.

## Other contexts where the same fix would help

Anywhere multi-element unification happens against a row-polymorphic
position:

- Tuples of effectful functions: `(f, g)` where `f` and `g` have different
  rows
- Records with multiple effectful function fields
- Multi-arm `case` branches all returning effectful function values

These are less common than list literals in practice, but the same
join-on-unification logic would handle them.

## Test matrix

The full matrix is small. With the fix:

| Input                                         | Today         | After fix |
| --------------------------------------------- | ------------- | --------- |
| `take_callbacks [pure_thing]`                 | ✅            | ✅        |
| `take_callbacks [do_foo]`                     | ✅            | ✅        |
| `take_callbacks [do_foo, do_bar]`             | ❌ type error | ✅        |
| `take_callbacks [pure_thing, do_foo]`         | ❌ type error | ✅        |
| `take_callbacks [pure_thing, do_foo, do_bar]` | ❌ type error | ✅        |

Plus regression coverage:

- Concrete-row position (`List (Unit -> Unit needs {Foo})`): still rejects
  callbacks with extra effects.
- Function with row claiming effects unavailable at the call site: still
  rejects.

## Implications for Edda

With the fix, Edda's `choose` works as designed and we can drop the
"declare the union of effects on every route" workaround. Pure routes stay
pure in their signatures; effectful ones declare only what they use.
Capability-based routing then lives where the design intends — at the
route level, not the sub-app level.

Sub-apps remain a useful organizing pattern for _architectural_ reasons
(grouping by domain, scoping handlers, isolating test mocks), but no
longer for _workaround_ reasons.
