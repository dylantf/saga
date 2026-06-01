# Reader Config Effect Optimization

Small fixtures for the selective-uniform static reader-handler spike.

- `01-arg-passing.saga` passes a config value explicitly through a hot loop.
- `02-static-reader-effect.saga` reads the same config through a static
  `get_config () = resume 7` handler.
- `03-handler-around-loop.saga` installs the handler around the loop while a
  helper performs the read; this is the next function-boundary target.
- `04-timing.saga` runs the arg-passing and effect-reader loops in one process
  and prints rough elapsed milliseconds.

The first spike intentionally keeps the handler local to `step` in the effect
version. That makes the perform lexically visible under the handler and tests
only the reader rewrite. Optimizing the more realistic shape:

```saga
{ loop ... } with config_7
```

requires function-boundary specialization and is a later milestone.

Useful checks:

```sh
cargo run --bin saga --quiet -- inspect examples/optimization/reader-config-effect/02-static-reader-effect.saga --stage monadic-stats
cargo run --bin saga --quiet -- inspect examples/optimization/reader-config-effect/03-handler-around-loop.saga --stage monadic-stats
cargo run --bin saga --quiet -- inspect examples/optimization/reader-config-effect/04-timing.saga --stage monadic-stats
cargo run --bin saga --quiet -- run examples/optimization/reader-config-effect/01-arg-passing.saga
cargo run --bin saga --quiet -- run examples/optimization/reader-config-effect/02-static-reader-effect.saga
cargo run --bin saga --quiet -- run examples/optimization/reader-config-effect/03-handler-around-loop.saga
cargo run --bin saga --quiet -- run examples/optimization/reader-config-effect/04-timing.saga
```
