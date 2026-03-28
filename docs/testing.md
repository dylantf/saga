# Testing Framework

Spec for dylang's built-in testing support.

---

## Overview

Tests are written in separate `*_test.dy` files that import the modules they test. They only
have access to `pub` items from those modules. Assertions use the effect system: a single
`Test` effect with an `assert` operation, handled by the test runner. This means the runner
controls behavior (fail-fast vs collect-all) without any changes to test code.

---

## File layout and discovery

Tests live in a `tests/` directory at the project root (next to `project.toml`) by default:

```
my_project/
  project.toml
  Main.dy
  Math.dy
  User.dy
  tests/
    math_test.dy
    user_test.dy
```

The test directory is configurable via `project.toml`:

```toml
[project]
name = "my_project"
tests_dir = "src/tests"    # default: "tests"
```

This lets projects that keep source under `src/` colocate their tests:

```
my_project/
  project.toml
  src/
    Main.dy
    Math.dy
    tests/
      math_test.dy
```

`dylang test` discovers all `*.dy` files under the configured test directory. No
registration needed.

### Visibility

Test files are regular modules. They import the code under test with `import` and only see
`pub` items. This is intentional: tests verify the public contract.

---

## Syntax

Two new declaration forms: `test` and `describe`.

### test

```
test "name" {
  body
}
```

A `test` declaration defines a single test case. The body is a block expression. The `Test`
effect is implicitly available (the runner provides the handler). Tests can also use any
other effects as long as they attach handlers via `with` inside the test body.

### describe

```
describe "group name" {
  test "case 1" { ... }
  test "case 2" { ... }

  describe "subgroup" {
    test "case 3" { ... }
  }
}
```

`describe` groups tests for organization and reporting. It can contain `test` blocks, other
`describe` blocks, and `let` bindings (for shared setup). Nesting is unlimited.

`let` bindings inside a `describe` are visible to all tests and nested `describe`s in that
scope. They are re-evaluated for each test (no shared mutable state between tests):

```
describe "Math" {
  let x = 42

  test "addition" {
    assert_eq! (x + 1) 43
  }

  test "subtraction" {
    assert_eq! (x - 1) 41
  }
}
```

### Top-level tests

`test` can appear at the top level of a test file without a surrounding `describe`:

```
# tests/math_test.dy
import Math

test "add works" {
  assert_eq! (Math.add 2 3) 5
}

describe "division" {
  test "basic" {
    assert_eq! (Math.div 10 2) 5
  }
}
```

---

## The Test effect

Defined in a new stdlib module `Std.Test`:

```
module Std.Test

pub effect Test {
  fun assert (ok: Bool) (msg: String) -> Unit
}
```

This is the only primitive. All assertion helpers are plain functions that call `assert!`:

```
pub fun assert_eq (a: x) (b: x) -> Unit needs {Test} where {x: Show + Eq}
assert_eq a b =
  assert! (a == b) ($"Expected {show b}, got {show a}")

pub fun assert_neq (a: x) (b: x) -> Unit needs {Test} where {x: Show + Eq}
assert_neq a b =
  assert! (a != b) ($"Expected {show a} to not equal {show b}")

pub fun assert_true (cond: Bool) -> Unit needs {Test}
assert_true cond = assert! cond "Expected True, got False"

pub fun assert_false (cond: Bool) -> Unit needs {Test}
assert_false cond = assert! (not cond) "Expected False, got True"

pub fun assert_gt (a: x) (b: x) -> Unit needs {Test} where {x: Show + Ord}
assert_gt a b =
  assert! (a > b) ($"Expected {show a} to be greater than {show b}")

pub fun assert_gte (a: x) (b: x) -> Unit needs {Test} where {x: Show + Ord}
assert_gte a b =
  assert! (a >= b) ($"Expected {show a} to be greater than or equal to {show b}")

pub fun assert_lt (a: x) (b: x) -> Unit needs {Test} where {x: Show + Ord}
assert_lt a b =
  assert! (a < b) ($"Expected {show a} to be less than {show b}")

pub fun assert_lte (a: x) (b: x) -> Unit needs {Test} where {x: Show + Ord}
assert_lte a b =
  assert! (a <= b) ($"Expected {show a} to be less than or equal to {show b}")

pub fun assert_some (m: Maybe a) -> Unit needs {Test} where {a: Show}
assert_some m = case m {
  Some(_) -> assert! True ""
  None -> assert! False "Expected Some(_), got None"
}

pub fun assert_none (m: Maybe a) -> Unit needs {Test} where {a: Show}
assert_none m = case m {
  Some(x) -> assert! False ($"Expected None, got Some({show x})")
  None -> assert! True ""
}

pub fun assert_ok (r: Result a b) -> Unit needs {Test} where {a: Show, b: Show}
assert_ok r = case r {
  Ok(_) -> assert! True ""
  Err(e) -> assert! False ($"Expected Ok(_), got Err({show e})")
}

pub fun assert_err (r: Result a b) -> Unit needs {Test} where {a: Show, b: Show}
assert_err r = case r {
  Ok(x) -> assert! False ($"Expected Err(_), got Ok({show x})")
  Err(_) -> assert! True ""
}
```

Users can define their own assertion helpers the same way. No special syntax needed, just
call `assert!` with a bool and a message.

---

## Test runner

### Command

```
dylang test              # run all tests in tests/
dylang test math         # filter: only tests whose path or describe/test name contains "math"
```

### Execution model

For each test file:

1. Compile the file and its imports
2. Walk the `describe`/`test` tree
3. For each `test`, evaluate its body with the `Test` handler attached
4. Collect results (pass/fail + failure message)
5. Print results, then print summary

Each test runs independently. A failure in one test does not prevent other tests from
running.

### Handler strategy

The runner wraps each test body with a handler for `Test`. The default handler is
**fail-fast within a test** (the first failed assertion stops that test), but
**continues across tests** (other tests still run).

Conceptually:

```
handler test_runner for Test {
  assert ok msg =
    if ok then resume ()
    else msg   # abort this test, return the failure message
}
```

The test runner calls each test body, catches the abort, and records the result.

### Output format

```
math_test
  ✓ add works
  division
    ✓ basic
    ✗ handles zero (Expected 0, got panic)

user_test
  User
    validation
      ✓ rejects empty name
      ✓ accepts valid user
    age
      ✗ must be positive (Expected 5 to be greater than 0)

Tests: 4 passed, 2 failed, 6 total
```

The describe/test hierarchy maps directly to indented output. Passing tests get a check
mark, failing tests get an X followed by the failure message.

### Exit code

`dylang test` exits with code 0 if all tests pass, 1 if any test fails. This makes it
usable in CI pipelines.

---

## Testing with effects

The effect system makes test isolation natural. Functions that use effects are testable
by providing mock handlers:

```
# src
pub effect Database {
  fun query : (sql: String) -> List String
}

pub fun get_users : Unit -> List String needs {Database}
get_users () = query! "SELECT name FROM users"

# tests
import App (get_users)

describe "get_users" {
  test "returns query results" {
    let result = {
      get_users ()
    } with {
      query sql -> resume ["alice", "bob"]
    }
    assert_eq! result ["alice", "bob"]
  }
}
```

No mocking libraries, no dependency injection. The test just provides a different handler.

---

## AST representation

Two new `Decl` variants:

```rust
Decl::Test {
    name: String,      // "add works"
    body: Box<Expr>,   // the block expression
    span: Span,
}

Decl::Describe {
    name: String,          // "division"
    entries: Vec<Decl>,    // Test, Describe, or Let declarations
    span: Span,
}
```

`test` and `describe` are only legal inside test files (files under `tests/`). Encountering
them in non-test files is a compile error.

---

## Parser changes

Two new keywords: `test` and `describe`.

`test` parses as: `test` STRING_LITERAL BLOCK

`describe` parses as: `describe` STRING_LITERAL `{` (decl)\* `}`

Inside a `describe` block, the parser accepts `test`, `describe`, and `let` declarations.
No function definitions, type definitions, imports, etc. Imports go at the top of the file
as usual.

---

## Type checking

- `test` bodies are checked as expressions of type `Unit` with `Test` in the effect context
  (the runner provides the handler, so `Test` is always available).
- `describe` blocks recurse into their entries.
- `let` bindings inside `describe` are added to the environment for nested entries.
- No type signatures on tests. The name is a string, the body is `Unit`.

---

## Implementation order

1. **Keywords and parsing** - Add `test` and `describe` tokens, parse the new declaration
   forms, add AST variants.
2. **Std.Test module** - Define the `Test` effect and assertion helpers in
   `src/stdlib/Test.dy`.
3. **Type checking** - Handle `Decl::Test` and `Decl::Describe` in the type checker.
   Inject `Test` into the effect context for test bodies.
4. **Backend lowering** - Lower test declarations to BEAM functions. Each test becomes a
   zero-arg function. Describe groups become a data structure the runner can walk.
5. **Test runner** - Add `dylang test` subcommand. Discover test files, compile them,
   invoke the generated test functions, collect results, print the report.
6. **Filter flag** - Support `dylang test <pattern>` to filter by name.
