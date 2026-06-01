# Reader Config Effect Stats Journal

This journal tracks the selective-uniform reader specialization spike. Commands
are run from the Saga repo root.

## Milestone 1: Lexical Static Reader Handler

Fixture: `02-static-reader-effect.saga`

```sh
cargo run --bin saga --quiet -- inspect examples/optimization/reader-config-effect/02-static-reader-effect.saga --stage monadic-stats
cargo run --bin saga --quiet -- inspect examples/optimization/reader-config-effect/02-static-reader-effect.saga --stage monadic-reader-stats
```

Reader-only result after the initial reader pass:

| Metric | Before | After | Delta |
| --- | ---: | ---: | ---: |
| Yield | 1 | 0 | -1 |
| Config::get_config | 1 | 0 | -1 |
| Bind | 11 | 1 | -10 |
| Let | 0 | 10 | +10 |
| With | 1 | 1 | 0 |
| Resume | 1 | 1 | 0 |

Notes:

- The reader pass rewrites the lexical `Yield` to the resumed value.
- Reader-only stats now include the narrow `Bind -> Let` promotion for
  non-yielding values. The older general optimizer can still remove more
  scaffolding after the yield is gone.
- Both `01-arg-passing.saga` and `02-static-reader-effect.saga` print
  `"15000850000"`.

## Milestone 2: Handler Around Loop

Fixture: `03-handler-around-loop.saga`

This is the realistic shape: the handler encloses the loop call, while the
effect read is inside `step`. It is expected to require function-boundary
specialization.

```sh
cargo run --bin saga --quiet -- inspect examples/optimization/reader-config-effect/03-handler-around-loop.saga --stage monadic-stats
cargo run --bin saga --quiet -- inspect examples/optimization/reader-config-effect/03-handler-around-loop.saga --stage monadic-reader-stats
```

Reader-only result after the bind-cleanup and function-boundary prototype:

| Metric | Before | After | Delta |
| --- | ---: | ---: | ---: |
| Yield | 1 | 1 | 0 |
| Config::get_config | 1 | 1 | 0 |
| Bind | 11 | 5 | -6 |
| Let | 0 | 12 | +12 |
| With | 1 | 1 | 0 |
| generated decls | 0 | 2 | +2 |

Reader-only entry-reachable result after the bind-cleanup and
function-boundary prototype:

| Metric | Before | After | Delta |
| --- | ---: | ---: | ---: |
| Yield | 1 | 0 | -1 |
| Config::get_config | 1 | 0 | -1 |
| Bind | 11 | 3 | -8 |
| Let | 0 | 8 | +8 |
| With | 1 | 1 | 0 |
| generated decls | 0 | 2 | +2 |

Notes:

- The reader-only pass can promote the closed, non-yielding sequencing to
  `Let`.
- The function-boundary prototype can generate entry-reachable reader variants
  for `loop` and `step`, removing the hot-path yield in this fixture.
- This prototype is not wired into normal `saga run`; it was slower than the
  existing optimizer on `04-timing.saga`, because its generated variants still
  lower pure calls through the uniform CPS ABI.
- The full `monadic-stats` pipeline currently reports an entry-reachable
  `Yield 1 -> 0` here, but that comes from the existing static
  function-variant/direct-call optimizer generating a hot-path variant under
  the handler.
- `03-handler-around-loop.saga` prints `"15000850000"`.

## Milestone 2 Timing Harness

Fixture: `04-timing.saga`

```sh
cargo run --bin saga --quiet -- inspect examples/optimization/reader-config-effect/04-timing.saga --stage monadic-stats
cargo run --bin saga --quiet -- inspect examples/optimization/reader-config-effect/04-timing.saga --stage monadic-reader-stats
cargo run --bin saga --quiet -- run examples/optimization/reader-config-effect/04-timing.saga
```

Reader-only entry-reachable stats after the bind-cleanup and
function-boundary prototype:

| Metric | Before | After | Delta |
| --- | ---: | ---: | ---: |
| Yield | 1 | 0 | -1 |
| Config::get_config | 1 | 0 | -1 |
| Bind | 68 | 17 | -51 |
| Let | 0 | 51 | +51 |
| With | 2 | 2 | 0 |
| generated decls | 0 | 2 | +2 |

Full-pipeline entry-reachable stats after milestone 1:

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
- The reader-only function-boundary prototype now crosses `loop` / `step` and
  removes the entry-reachable config read.
- Normal `saga run` currently uses the full production optimizer instead of
  this prototype. A temporary wiring test made the effect loop regress to about
  1.8s, while production remains around 6ms on this machine.
- The full pipeline specializes the config read to the literal `7` in the hot
  generated path through the existing function-variant optimizer, while the
  explicit argument version still threads `cfg` through the loop and step
  calls.
