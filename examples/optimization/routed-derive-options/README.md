# Routed derive options optimizer fixtures

These examples model the `saga_json` customization path: a derived Generic
dictionary routes through one or more trait dictionaries, while leaf encoders
read an ambient options effect.

The goal is not to benchmark wall-clock time. Run with `--monadic-stats` and
watch whether entry-reachable `Options::get_options` yields disappear.

## Levels

| File | Shape |
| --- | --- |
| `01-routed-derive-options.saga` | Same-module derived ADT encoder. |
| `02-cross-module-routed-derive/` | Cross-module derived ADT encoder. |
| `03-split-trait-record.saga` | Same-module record encoder routed through split traits. |
| `04-cross-module-split-trait/` | Cross-module record encoder routed through split traits. |
| `05-cross-module-handler-factory/` | Cross-module split traits plus a let-bound handler factory. |
| `06-cross-module-maybe-field/` | Handler factory plus a nested `Maybe` field. |
| `07-cross-module-list-field/` | Handler factory plus a list field encoded through `Std.List.map`. |
| `08-cross-module-variant-options/` | Cross-module generic variant impl reads options. |
| `09-cross-module-inner-handler-adt/` | Cross-module `as_tagged`-style inner handler around derived ADT encoding. |

## Current Reference Stats

Recorded after value-keyed generated variants learned to specialize closed ADT
constructor arguments. Level 09 mirrors the `saga_json` `as_tagged` shape: the
selected constructor path no longer materializes the full generic ADT
dictionary before encoding.

| Level | Whole-app entry-reachable stats |
| --- | --- |
| `05-cross-module-handler-factory` | `Yield 2 -> 0`, `Bind 32 -> 2`, `decls 10 -> 2` |
| `06-cross-module-maybe-field` | `Yield 2 -> 0`, `Bind 35 -> 2`, `decls 11 -> 2` |
| `07-cross-module-list-field` | `Yield 3 -> 0`, `Bind 31 -> 5`, `decls 10 -> 2` |
| `08-cross-module-variant-options` | `Yield 2 -> 0`, `Bind 35 -> 3`, `decls 11 -> 3` |
| `09-cross-module-inner-handler-adt` | `Yield 3 -> 0`, `Bind 49 -> 3`, `decls 13 -> 3` |

## Level 09 Resolution

This was not a missing imported-dictionary lookup. The optimizer could already
resolve imported dict constructors through direct `DictRef`, qualified, and
lowered `Var` heads. The residual `get_options` yields came from the derived ADT
dictionary shape: selected `Heartbeat`/`Login` calls built a full generic
`Event` dictionary, including latent method closures for the unused
`Click Int Int` branch.

The fix is value-keyed generated variants for closed constructor arguments,
plus a small case-on-known-constructor collapse. `override_options Heartbeat`
and `override_options (Login 5)` now get separate caller-local variants, so the
derived representation branch is known before the oversized dictionary method
inline budget check. The ordinary dictionary-method and direct-call rewrites
then erase the option reads.

Run project fixtures from their directory:

```bash
cargo run --bin saga --quiet -- run --monadic-stats
```
