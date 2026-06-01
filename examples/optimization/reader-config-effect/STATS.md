# Reader Config Effect Stats Journal

This journal tracks the selective-uniform reader specialization spike. Commands
are run from the Saga repo root.

## Milestone 1: Lexical Static Reader Handler

Fixture: `02-static-reader-effect.saga`

```sh
cargo run --bin saga --quiet -- inspect examples/optimization/reader-config-effect/02-static-reader-effect.saga --stage monadic-stats
```

Entry-reachable result after the initial reader pass:

| Metric | Before | After | Delta |
| --- | ---: | ---: | ---: |
| Yield | 1 | 0 | -1 |
| Config::get_config | 1 | 0 | -1 |
| Bind | 11 | 1 | -10 |
| With | 1 | 0 | -1 |
| Resume | 1 | 0 | -1 |

Notes:

- The reader pass rewrites the lexical `Yield` to the resumed value.
- The existing optimizer removes the now-dead `with`.
- Both `01-arg-passing.saga` and `02-static-reader-effect.saga` print
  `"15000850000"`.

## Milestone 2: Handler Around Loop

Fixture: `03-handler-around-loop.saga`

This is the realistic shape: the handler encloses the loop call, while the
effect read is inside `step`. It is expected to require function-boundary
specialization.

```sh
cargo run --bin saga --quiet -- inspect examples/optimization/reader-config-effect/03-handler-around-loop.saga --stage monadic-stats
```

Whole-program result after milestone 1:

| Metric | Before | After | Delta |
| --- | ---: | ---: | ---: |
| Yield | 1 | 1 | 0 |
| Config::get_config | 1 | 1 | 0 |
| Bind | 11 | 3 | -8 |
| With | 1 | 1 | 0 |
| generated decls | 0 | 1 | +1 |

Entry-reachable result after milestone 1:

| Metric | Before | After | Delta |
| --- | ---: | ---: | ---: |
| Yield | 1 | 0 | -1 |
| Config::get_config | 1 | 0 | -1 |
| Bind | 11 | 2 | -9 |
| With | 1 | 1 | 0 |
| generated decls | 0 | 1 | +1 |

Notes:

- The source `step` function still contains the reader yield, so whole-program
  stats keep one residual yield.
- The existing function-variant optimizer generates an entry-reachable variant
  under the static handler. The new reader pass erases the yield in that
  generated hot path.
- `03-handler-around-loop.saga` prints `"15000850000"`.

## Milestone 2 Timing Harness

Fixture: `04-timing.saga`

```sh
cargo run --bin saga --quiet -- inspect examples/optimization/reader-config-effect/04-timing.saga --stage monadic-stats
cargo run --bin saga --quiet -- run examples/optimization/reader-config-effect/04-timing.saga
```

Entry-reachable stats after milestone 1:

| Metric | Before | After | Delta |
| --- | ---: | ---: | ---: |
| Yield | 1 | 0 | -1 |
| Config::get_config | 1 | 0 | -1 |
| Bind | 68 | 21 | -47 |
| With | 2 | 2 | 0 |
| generated decls | 0 | 2 | +2 |

Timing sample with `iterations = 5000000`:

| Run | Arg ms | Effect ms |
| --- | ---: | ---: |
| 1 | 40 | 7 |
| 2 | 44 | 6 |

Notes:

- This is not a full benchmark harness, just a quick signal.
- The effect version specializes the config read to the literal `7` in the hot
  generated path, while the explicit argument version still threads `cfg`
  through the loop and step calls.
