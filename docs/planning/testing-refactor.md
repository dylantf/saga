# Testing Refactor

## Problem

The current test runner is a single large effect (`TestRunner`) that deeply
exercises the CPS/continuation machinery. This causes two issues:

1. **Brittleness**: the runner itself is sensitive to bugs in deeply nested
   continuation passing, making it hard to tell whether a failure is in the
   test code or the test framework.

2. **Performance**: each test file compiles to a temporary `_test` module,
   boots a fresh BEAM VM, runs, and shuts down. N test files means N VM
   boots, N `erlc` invocations, and no combined summary across files.

3. **Coupling**: the compiler synthesizes a `main` function with
   `run_collected`, restructures the module to separate test declarations
   from other code, and wraps everything in effect handlers. This desugaring
   is complex and fragile.

The goal is to decouple the test runner from the compiler, simplify the
effect usage to only where it earns its keep, and run all tests in a single
BEAM process.

---

## Design

### Test files export a `tests` function

Each test file declares a module and exports `pub fun tests`. The function
takes Unit, returns Unit, and needs the `Register` effect. `val` bindings
can't hold effectful values, so it must be a function.

```
# tests/math_test.saga
module MathTest

import Math (add, div)
import Std.Test (Register, describe, test, skip, assert_eq)

pub fun tests : Unit -> Unit needs {Register}
tests () = {
  describe "addition" (fun () -> {
    test "positive numbers" (fun () -> {
      assert_eq (add 2 3) 5
    })
  })

  skip "by zero" (fun () -> {
    assert_eq (div 10 0) 0
  })
}
```

Helper functions, types, and mock handlers live above `tests` as normal
module declarations.

### No desugaring

There is no desugaring. Test files are normal saga modules. The parser does
not need a test mode. `test`, `describe`, `skip`, and `only` are ordinary
functions that take a string and a lambda.

### Two-pass execution per module

The test harness runs each module's tests in two passes.

**Pass 1: Registration.** The harness calls the `Tests` thunk with a
`Register` handler. Each `test`/`describe`/`skip`/`only` call performs a
`Register` effect. The handler captures the name, mode, and body thunk via
the continuation:

```
effect Register {
  fun register_test : String -> TestMode -> (Unit -> Unit needs {Test}) -> Unit
  fun enter_group : String -> Unit
  fun leave_group : Unit -> Unit
}
```

The handler uses `resume` to continue executing the rest of the thunk,
then conses the current entry onto the result:

```
handler collect for Register {
  register_test name mode body = {
    let rest = resume ()
    Cons(TestEntry { name, mode, body }, rest)
  }
  enter_group name = {
    let children = resume ()
    [Group(name, children)]
  }
  leave_group () = []
}
```

After pass 1 completes, the harness has a `List TestEntry` (a flat or
tree structure of all tests in the module).

**Pass 2: Execution.** A pure recursive function walks the collected entries.
For each test, it calls the body thunk with a `Test` handler scoped to that
single test:

```
fun run_entry : TestEntry -> TestResult needs {Console}
run_entry entry = case entry.mode {
  SkipMode -> {
    print_skip! entry.name
    TestResult { name: entry.name, status: Skipped }
  }
  _ -> {
    let outcome = {
      entry.body ()
      Ok(())
    } with {
      assert ok msg =
        if ok then resume ()
        else Err(msg)
    }
    let status = case outcome {
      Ok(()) -> Passed
      Err(msg) -> Failed(msg)
    }
    print_result! entry.name status
    TestResult { name: entry.name, status }
  }
}
```

Results print live as each test completes. The recursive walk accumulates
pass/fail/skip counts through its arguments.

`only` support: after pass 1, the harness checks if any entry has `OnlyMode`.
If so, it filters the list before pass 2. This is a simple list operation,
no second registration pass needed.

### Test harness (orchestrator)

Effectful functions can't cross the FFI boundary (CPS handler params can't
be provided from Erlang), so dynamic dispatch via a bridge is not possible.
Instead, the compiler generates a static entry module that imports all test
modules by name.

`Std.Test` provides `run_modules : List (String, Unit -> Unit needs {Register}) -> Unit`
which handles registration, execution, and summary printing.

The generated entry module looks like:

```
import Std.Test (run_modules)
import MathTest
import UserTest

main () = run_modules [
  ("MathTest", MathTest.tests),
  ("UserTest", UserTest.tests),
]
```

Generated as source text, parsed and compiled through the normal pipeline.

### Compilation flow

Test files must be compiled as project modules (not scripts). Scripts don't
handle module-scoped trait resolution or record pattern guards correctly.

The build uses the existing `build_project` pipeline with two extensions:

1. The test directory is scanned and its modules are added to the checker's
   module map (using `scan_source_dir` which doesn't skip `tests/` subdirs)
2. A generated entry module is fed as the "main" program

The typechecker crawls from the entry module's imports, pulling in each
test module on demand, same as it does for regular project modules.

```
build_project_ext("test", &[tests_dir], Some(("_test_entry.saga", &entry_source)))
```

One VM boot. One combined summary.

---

## What changes

### Removed

- `run_collected` and the two-pass `collect_handler`/`exec_handler` in
  `Std.Test`
- Synthesized `main` function generation in `build.rs`
- Module restructuring (partitioning test exprs from other decls)
- The `TestRunner` effect
- Per-file VM boot/shutdown cycle
- The `_test` module name reuse
- `test_mode` flag in the parser
- Lambda wrapping desugaring in `desugar.rs`
- `test`/`describe`/`skip`/`only` keyword recognition in the parser
  (`parse_test_expr` and related code)
- `TopExpr` declaration variant and its handling in `build.rs`

Test files become normal saga modules with no special compiler support.
The compiler's only responsibility is compiling them and passing the
module list to the harness.

### Kept

- `Test` effect for assertions (scoped to individual test bodies)
- Assertion helpers (`assert_eq!`, `assert_true!`, etc.)

`test`, `describe`, `skip`, and `only` continue to exist but only as
ordinary functions in `Std.Test`. The compiler has no knowledge of them.

### New

- `Register` effect for test registration (shallow, always resumes)
- `TestEntry`, `TestResult`, `TestMode` types
- `collect` handler builds flat entry list via continuation unwinding
- `run_modules` entry point in `Std.Test`
- Generated static entry module (no FFI bridge)
- `build_project_ext` to include test dirs and custom main
- `scan_source_dir` (like `scan_project_modules` but doesn't skip `tests/`)
- Each test file compiles as a named project module

---

## Discovered constraints

- `val` bindings must be pure. Test thunks must use `pub fun tests`, not
  `pub val tests = Tests(...)`.
- Effects can't cross the FFI boundary. No bridge module for dynamic dispatch.
- The callback-absorption pass produces a false warning on `describe` ("declares
  needs {Register} but never uses it") because the body parameter also needs
  Register. This is a warning only, doesn't affect runtime.
- `lower/mod.rs` ets/vec init only checks for `main`. Needs to also check
  `tests` (or whichever function is the entry point for the module).

## Future

- **Parallel execution**: spawn an actor per module, collect results via messages
- **`@test` annotation**: when annotations are available at runtime, drop the
  `pub fun tests` convention in favor of annotated functions
- **Watch mode**: recompile changed files, re-run affected test modules
