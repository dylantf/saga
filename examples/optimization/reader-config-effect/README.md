# Reader Config Effect Optimization

Small fixtures for the selective-uniform static reader-handler spike.

- `01-arg-passing.saga` passes a config value explicitly through a hot loop.
- `02-static-reader-effect.saga` reads the same config through a static
  `get_config () = resume 7` handler.
- `03-handler-around-loop.saga` installs the handler around the loop while a
  helper performs the read; this is the next function-boundary target for the
  selective-uniform spike.
- `04-timing.saga` runs the arg-passing and effect-reader loops in one process
  and prints rough elapsed milliseconds.

The first spike intentionally keeps the handler local to `step` in the effect
version. That makes the perform lexically visible under the handler and tests
only the reader rewrite. Use `monadic-reader-stats` to measure this pass in
isolation; `monadic-stats` measures the production optimizer path. The reader
spike is deliberately not wired into normal `saga run` yet.

Optimizing the more realistic shape:

```saga
{ loop ... } with config_7
```

requires function-boundary specialization and is a later milestone for the new
selective-uniform path. The existing effect optimizer can already generate a
hot-path variant for this fixture, so the two stats stages intentionally answer
different questions. The reader-only function-boundary prototype can remove the
entry-reachable yield, but it is not accepted for production because its
generated variants are slower than the existing optimizer on `04-timing.saga`.

Useful checks:

```sh
cargo run --bin saga --quiet -- inspect examples/optimization/reader-config-effect/02-static-reader-effect.saga --stage monadic-stats
cargo run --bin saga --quiet -- inspect examples/optimization/reader-config-effect/02-static-reader-effect.saga --stage monadic-reader-stats
cargo run --bin saga --quiet -- inspect examples/optimization/reader-config-effect/03-handler-around-loop.saga --stage monadic-stats
cargo run --bin saga --quiet -- inspect examples/optimization/reader-config-effect/03-handler-around-loop.saga --stage monadic-reader-stats
cargo run --bin saga --quiet -- inspect examples/optimization/reader-config-effect/04-timing.saga --stage monadic-stats
cargo run --bin saga --quiet -- inspect examples/optimization/reader-config-effect/04-timing.saga --stage monadic-reader-stats
cargo run --bin saga --quiet -- run examples/optimization/reader-config-effect/01-arg-passing.saga
cargo run --bin saga --quiet -- run examples/optimization/reader-config-effect/02-static-reader-effect.saga
cargo run --bin saga --quiet -- run examples/optimization/reader-config-effect/03-handler-around-loop.saga
cargo run --bin saga --quiet -- run examples/optimization/reader-config-effect/04-timing.saga
```
