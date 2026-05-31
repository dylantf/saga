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

## Current Reference Stats

Recorded after imported dictionary constructors learned to admit immediate
lambda applications while still rejecting escaping lambda arguments.

| Level | Whole-app entry-reachable stats |
| --- | --- |
| `05-cross-module-handler-factory` | `Yield 2 -> 0`, `Bind 32 -> 2`, `decls 10 -> 2` |
| `06-cross-module-maybe-field` | `Yield 2 -> 0`, `Bind 35 -> 2`, `decls 11 -> 2` |
| `07-cross-module-list-field` | `Yield 3 -> 0`, `Bind 31 -> 5`, `decls 10 -> 2` |

Run project fixtures from their directory:

```bash
cargo run --bin saga --quiet -- run --monadic-stats
```
