# Derived-table runtime crash — effect-op dispatch bug (compiler)

`prolific_authors_query` (and any `from_subquery` use) crashes at runtime when its
`Prepared` is built:

```
Runtime error: no matching clause for the given arguments
  kraken_db:field_auto/2
  kraken_db:field_projection/2
  ...Selectable Leaf/Labeled/Record...
  kraken_db:project/4
  kraken_db_query:query/4        # Core.select on the outer selection
```

## Verdict: compiler bug (effect-operation dispatch), not Kraken logic

The Kraken logic is correct; `bind_derived!` simply fails to dispatch to its
handler clause in one specific situation.

### Smoking gun

Tracing the real `from_subquery` (dumping raw terms via an FFI `io:format`):

- `bind_derived! (...)` evaluates to a raw `{kraken_db_query_QueryStep, ...}`
  (the handler clause's *return value*), **not** the resumed scope.
- The `make_scope` closure (→ `derived_columns`) is **never called**.

So `t` becomes the `QueryStep` continuation tuple; the outer `select! ({ x: t.x })`
then projects `t.x` (garbage) and `field_auto`'s `let Col info = column` finds no
matching clause. The handler clause body is never entered — the operation is being
compiled as a plain value-returning call instead of an effect performance.

### Ruled out (all confirmed by running)

- **`derived_columns` / Generic `from` / `build_scope`** are correct. Called
  directly they produce a well-formed `{'__anon_x', {kraken_db_Col, {...}}}`.
- **Not** `selection_items` / `select_frag`: replacing the rendered frag with a
  dummy still crashes.
- **Not** the col source: a direct `Db.col` in the subquery crashes the same way
  as `p.id` / `p.title`.
- **`bind_derived!` works inline.** Performed directly in the `query` closure (no
  `from_subquery` wrapper, no nested handler), it dispatches correctly and renders
  `SELECT t0.x AS x FROM (SELECT 1) AS t0`.
- Hand-written custom-effect replicas of the full structure (nested same-effect
  handler → capture selection → polymorphic op carrying a dict-capturing closure →
  trailing op) all work. So the trigger is specific to the real `collect_query`
  setup, not the shape alone.

### Trigger (confirmed, self-contained)

Reduced to a no-Kraken repro: `dev/repro/xmod_repro` (`saga run`). The crash needs
**all three** together:

1. A function carrying **trait-dictionary parameters** (Kraken: `from_subquery`'s
   `DerivedScope`/`Generic` constraints, via `derived_columns`).
2. That function **runs a nested handler of the same effect** before the op.
3. It then **performs an effect operation whose argument captures a closure that
   uses those dictionary params** (Kraken: `make_scope: fun alias -> derived_columns
   selection alias`).

Removing any one fixes it: a control with **no nested handler** passes; a
`make_scope` using a plain `from (to selection)` (only `Generic`, no fundep trait
dict) passes. Ruled out as *not* the cause (faithful ports all pass): cross-module
boundary, op count, polymorphic ops, the full 11-op `QueryBuild` shape with a
realistic threaded state record, the two-FROM guard, alias prefixes, and the
`DerivedTable` record passed through the op.

Symptom: the operation fails to dispatch — it returns its raw handler-clause
continuation value (`QueryStep`) and the captured closure never runs.

## Reproduce

Point the binary at this query (e.g. temporarily set `project.toml` `[bin]
main` to a `Repro.saga`, or add it to `Read`/`Main`):

```saga
fun probe_query : Unit -> Query.Prepared { x: Int }
probe_query () = Query.query (fun () -> {
  let t = Query.from_subquery (fun () -> {
    let p = from! posts
    select! ({ x: (Db.col "id" "s0" : Db.Col Int) })
  })
  select! ({ x: t.x })
})
```

`(probe_query ()).sql` crashes with the trace above (no DB needed — it dies while
building the `Prepared`).
