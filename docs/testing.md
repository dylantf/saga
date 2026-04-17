# Testing Framework

Spec for saga's built-in testing support.

---

## Overview

Tests are ordinary saga modules discovered from the project's `tests/` directory. Each test
module exports a `tests` function that uses the `Std.Test.Testing` effect to register test
groups and test bodies. `saga test` collects all selected test modules, generates a synthetic
entry module, compiles everything through the normal project pipeline, and runs the suite in a
single BEAM VM.

Assertions use `Std.Test.Test`. The runner handles `Test` per test body, so failures are
fail-fast within a single test but do not stop the rest of the suite.

---

## File layout and discovery

Tests live in a `tests/` directory at the project root by default:

```
my_project/
  project.toml
  Main.saga
  Math.saga
  User.saga
  tests/
    math_test.saga
    user_test.saga
```

The directory is configurable via `project.toml`:

```toml
[project]
name = "my_project"
tests_dir = "src/tests"    # default: "tests"
```

`saga test` discovers all `.saga` files under the configured test directory. Selected test
files must declare a module and export `pub fun tests : Unit -> Unit needs {Testing}`.

Test files are regular modules. They import the code under test and only see `pub` items.

---

## Authoring

Tests are defined with ordinary functions from `Std.Test`; there is no parser special-case or
desugaring.

```saga
module MathTest

import Math
import Std.Test (Testing, describe, test, skip, assert_eq)

pub fun tests : Unit -> Unit needs {Testing}
tests () = {
  describe "addition" (fun () -> {
    test "positive numbers" (fun () -> {
      assert_eq (Math.add 2 3) 5
    })
  })

  skip "division by zero" (fun () -> {
    assert_eq (Math.div 10 0) 0
  })
}
```

`describe` groups tests for reporting. `test`, `skip`, and `only` register individual test
cases. Shared helper functions, types, handlers, and pure declarations live above `tests` like
any other module code.

Top-level `test` / `describe` declarations are not supported; everything is registered from the
exported `tests` function.

---

## Effects

`Std.Test` exposes two public effects:

```saga
pub effect Test {
  fun assert : (ok: Bool) -> (msg: String) -> Unit
}

pub effect Testing {
  fun register_test : (name: String) -> (mode: TestMode) -> (body: Unit -> Unit needs {Test}) -> Unit
  fun enter_group : (name: String) -> Unit
  fun leave_group : Unit -> Unit
}
```

`Test` is the primitive assertion effect. Assertion helpers are ordinary functions that call
`assert!` and therefore use `needs {Test}`.

Users can define custom assertion helpers the same way:

```saga
import Std.Test (Test)

pub fun assert_even : Int -> Unit needs {Test}
assert_even n =
  assert! (n % 2 == 0) $"Expected an even number, got {show n}"
```

`Testing` is used by `test`, `describe`, `skip`, and `only` during suite collection. Test
modules usually only mention it in the type of their exported `tests` function.

---

## Runner behavior

### Command

```
saga test
saga test math
```

The filter matches selected test files by path / file name, then generates an entry module that
imports only those test modules.

### Execution model

`saga test` performs three phases:

1. Discover test modules and generate a synthetic `Main` module that calls `Std.Test.run_modules`
2. Compile the project and selected test modules together through the standard build pipeline
3. Collect all tests, apply global `only` normalization, then execute tests in module order

### Failure and panic handling

- The first failed assertion aborts that individual test.
- A panic inside a test body is reported as a failed test, not a VM crash.
- Other tests and modules continue running after a failure.

### `only`

`only` is global across the selected suite. If any `only` exists anywhere, every non-`only`
test in every selected module is reported as skipped.

### Output

The runner prints:

- live per-test results
- a per-module summary after each module
- one overall summary at the end

The process exits with code `1` if any test failed, otherwise `0`.
