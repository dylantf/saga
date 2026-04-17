# saga - Language Design

---

## 1. Basics

Annotations are optional for private functions -- the type checker infers everything. They are required to export a function from a module (`pub` without an annotation is an error) and serve as documentation for anyone reading the code.

```
# Comments with hash

#@ Doc comments with hash-at
#@ They attach to the next definition

# Function definitions - three levels:

# Public, annotated (required for public API)
pub fun add : Int -> Int -> Int
add x y = x + y

# With optional parameter labels (documentation only)
pub fun add : (a: Int) -> (b: Int) -> Int
add x y = x + y

# Private, annotated (optional, for documentation)
fun double : Int -> Int
double x = x * 2

# Private, inferred (no annotation at all)
triple x = x * 3

# Zero-arg functions take Unit

main () = {
  let x = add 3 4
  let y = double x
  print y
}

# Pipe operator

main () = {
  5
  |> add 3
  |> show
  |> print
}

# Lambdas
pub fun apply : (a -> b) -> a -> b
apply f x = f x

# Currying / partial application
add_five = add 5

main () = {
  apply (fun x -> x + 1) 5 |> print
}
```

---

## 2. ADTs and Pattern Matching

```
type Maybe a
  = Maybe(a)
  | Nothing

type Result a e
  = Ok(a)
  | Err(e)

type List a
  = Cons(a, List a)
  | Nil

# Exhaustive pattern matching
pub fun unwrap : Option a -> a -> a
unwrap opt default = case opt {
  Just x -> x
  Nothing -> default
}

# Nested patterns
type Expr
  = Lit(Int)
  | Add(Expr, Expr)
  | Mul(Expr, Expr)

pub fun eval : Expr -> Int
eval expr = case expr {
  Lit(n) -> n
  Add(a, b) -> eval a + eval b
  Mul(a, b) -> eval a * eval b
}

# Guards use `when` in both case arms and function definitions
# Any pure function (no effects) can be used in guards
pub fun clamp : Int -> Int
clamp n = case n {
  n when n < 0 -> 0
  n when n > 100 -> 100
  n -> n
}

# Arbitrary pure functions in guards
is_valid s = String.length s > 0 && String.length s < 100

pub fun describe : String -> String
describe s = case s {
  s when is_valid s -> "valid: " <> s
  _ -> "invalid"
}

# Guards on function definitions use `when`
pub fun abs : Int -> Int
abs n when n < 0 = -n
abs n = n
```

Opaque types are also possible. The type is exposed to other modules, but the constructors are hidden. This allows pattern matching on the type, but not construction outside of the module it is defined in.

```
module A
opaque type Foo = Bar | Baz

module B
# This is ok
case foo {
  Bar -> "bar"
  Baz -> "baz
}

# Type error
let foo = Bar

```

---

## 3. Records

```
# Records are their own thing, defined with `record`
record User {
  name : String,
  age : Int,
  email : String,
}

# Constructor uses the record name
let u = User { name: "Dylan", age: 30, email: "d@d.com" }

# Dot access
pub fun greet : User -> String
greet user = "Hello, " <> user.name

# Record update syntax
pub fun birthday : User -> User
birthday user = { user | age: user.age + 1 }

# ADTs can reference records as variants
record Success {
  status : Int,
  body : String,
}

record ApiError {
  code : Int,
  message : String,
}

type ApiResponse
  = Success
  | ApiError

# Pattern matching on record variants
pub fun describe : ApiResponse -> String
describe resp = case resp {
  Success { status, body } -> "OK " <> show status
  ApiError { code, message } -> "Error " <> show code <> ": " <> message
}

# Field aliasing in patterns
describe resp = case resp {
  Success { status: s, body: b } -> "OK " <> show s
  ApiError { code: c } -> "Error " <> show c
}

# Record matches are always partial - unmentioned fields are ignored
# No special syntax needed, just match what you care about
header_only resp = case resp {
  Success { status } -> status
  ApiError {} -> 0
}

# Exhaustiveness is at the variant level, not field level
# This warns - missing ApiError case:
#   case resp { Success { status } -> status }
# This is fine - matches all variants:
#   case resp { Success { status } -> status, _ -> 0 }

# `_` for positional ADT discards
fun has_value : Option a -> Bool
has_value opt = case opt {
  Just _ -> True
  None -> False
}

# ADTs can still have simple positional variants
type Maybe a
  = Just(a)
  | None

# Rule: ADT variants are either bare names (possibly records)
# or carry positional data with parens. Never inline field definitions.
```

---

## 4. Effects - The Core Idea

See `docs/effects-guide.md` for the full deep-dive with rationale and examples.

```
# Effects are declared like traits/interfaces
effect Console {
  fun print : String -> Unit
  fun read_line : Unit -> String
}

effect FileSystem {
  fun read_file : String -> String
  fun write_file : String -> String -> Unit
}

effect Fail {
  fun fail : String -> a
}

# Functions declare which effects they use
pub fun greet : String -> String needs {Console}
greet name = {
  print! ("Hello, " <> name)
  "greeted"
}

# Effect operations use ! to mark the perform site
# Pure function calls don't get it
pub fun process_file : String -> Unit needs {Console, FileSystem, Fail}
process_file path = {
  let contents = read_file! path
  if contents == "" then
    fail! "empty file"
  else
    print! contents
}
```

---

## 5. Effect Handlers

```
# Handlers provide implementations for effects.
# Two forms: named (reusable) and inline (one-off).

# Named handler - defined once, used by name
# Handlers declare `needs` when they use other effects
handler std_io for Console needs {Stdout, Stdin} {
  print msg -> {
    stdout_print! msg
    resume ()
  }
  read_line () -> read_stdin! () |> resume
}

# Pure handler - no `needs` clause
handler mock_console for Console {
  print msg -> resume ()       # swallow output
  read_line () -> resume "mock input"
}

# Inline handler - anonymous, defined at the use site
main () = {
  process_file! "data.txt"
} with {
  print msg -> {
    stdout_print! msg
    resume ()
  },
  read_line () -> read_stdin! () |> resume,
  read_file path -> os_read_file! path |> resume,
  write_file path data -> {
    os_write_file! path data
    resume ()
  },
  fail reason -> Err(reason),   # no resume - aborts the computation
}

# Attach a named handler

main () = {
  greet "Dylan"
} with std_io

# For testing - swap the handler, not the code
test () = {
  let result = greet "Dylan" with mock_console
  assert (result == "greeted")
}

# Stack handlers - named refs and inline arms mix in a block
main () = {
  run_server ()
} with {
  std_io,
  real_db,
  fail reason -> {
    print! ("Error: " <> reason)
    exit! 1
  },
}
```

---

## 6. Effect Handlers - Advanced (Continuations)

```
# `resume` is a keyword available in any handler
# It sends a value back to the point where the effect was performed
# Think of it like async/await - but for everything

effect Ask {
  fun ask : String -> String
}

# A handler that intercepts and continues
handler interactive for Ask needs {Console} {
  ask prompt -> {
    print! prompt
    let answer = read_line! ()
    resume answer     # send answer back as return value of ask!
  }
}

# A handler that doesn't resume - computation is aborted
handler to_result for Fail {
  fail reason -> Err(reason)
  return value -> Ok(value)
}

# Retry logic - resume on success, give up on second failure
handler with_retry for Http needs {Net, Timer, Fail} {
  get url -> {
    case http_get! url {
      Ok(body) -> resume body
      Err(_) -> {
        sleep! 1000
        case http_get! url {
          Ok(body) -> resume body
          Err(e) -> fail! ("gave up: " <> e)
        }
      }
    }
  }
}

# Rules:
# - `resume` is always available in handlers
# - If a handler calls `resume`, computation continues
# - If a handler doesn't call `resume`, computation is aborted
# - `return value -> ...` intercepts the final value on success
```

---

## 7. Error Handling via Effects

```
# No exceptions, no special syntax - errors are just effects

fun safe_divide : Int -> Int -> Int needs {Fail}
safe_divide x y =
  if y == 0 then fail! "division by zero"
  else x / y

main () = {
  let result = {
    let a = safe_divide 10 2
    let b = safe_divide a 0    # fails -handler returns Err(...)
    a + b                      # never reached
  } with to_result

  case result {
    Ok(n) -> print! (show n)
    Err(e) -> print! ("Error: " <> e)
  }
}
```

---

```
# Explicit module naming - file path doesn't matter
# File: foo/bar/some_module.saga

module Foo.Bar.SomeModule

# pub fun = public, fun = private annotation, bare = private inferred
pub fun abs : Int -> Int
abs n when n < 0 = -n
abs n = n

pub fun max : Int -> Int -> Int
max a b = if a > b then a else b

# Private - not visible outside module
helper x = x + 1

# Importing
import Math
import Math (abs, max)
import Math as M


main () = {
  M.abs (-5) |> print
}
```

---

## 10. Traits

```
# Traits are for type-driven dispatch - the implementation is
# determined by the type, not the call site.
# Effects are for context-driven dispatch - the caller provides
# the implementation via handlers.

trait Show a {
  fun show : a -> String
}

trait Eq a {
  fun eq : a -> a -> Bool
}

# Trait inheritance - Ord requires Eq
trait Ord a where {a: Eq} {
  fun compare : a -> a -> Ordering
}

# Implementing for a type
impl Show for User {
  show user = user.name <> " (age " <> show user.age <> ")"
}

impl Eq for User {
  eq a b = a.id == b.id
}

# --- Trait bounds on functions ---

# Single bound
pub fun to_string : a -> String where {a: Show}
to_string x = show x

# Multiple bounds on one type variable - use `+`
pub fun print_if_equal : a -> a -> Unit needs {Console} where {a: Show + Eq}
print_if_equal x y =
  if eq x y then print! (show x)
  else print! "not equal"

# Bounds on multiple type variables
pub fun convert : a -> b -> String where {a: Show, b: Show + Eq}
convert x y = show x <> " -> " <> show y

# `needs` and `where` are independent - effects and traits together
# `needs` comes first (what the function does), `where` second (what the types must support)
pub fun print_all : List a -> Unit needs {Console} where {a: Show}
print_all items = case items {
  Cons(x, rest) -> {
    print! (show x)
    print_all rest
  }
  Nil -> ()
}

# --- Why `where` and not `needs`? ---
# `needs` = runtime context: "this function needs these effects to be handled"
# `where` = compile-time constraint: "these types must support these operations"
# They answer different questions and appear at different phases,
# so they get different syntax.

# Rule of thumb:
# - "How do I convert X to a string?" -> trait (Show), determined by type
# - "Where do I send this log message?" -> effect (Log), determined by caller
```

---

## 11. Putting It All Together - A Realistic Program

```
module UserService

import Http
import Json
import Db

record User {
  id : Int,
  name : String,
  email : String,
}

type ApiError
  = NotFound(String)
  | Unauthorized
  | ServerError(String)

effect Log {
  fun log : String -> Unit
}

pub fun fetch_user : Int -> User needs {Http, Fail, Log}
fetch_user id = {
  log! ("Fetching user " <> show id)
  let response = get! ("/api/users/" <> show id)
  case parse_json response {
    Ok(user) -> user
    Err(e) -> fail! ("Parse error: " <> e)
  }
}

pub fun save_user : User -> Unit needs {Db, Fail, Log}
save_user user = {
  log! ("Saving user " <> user.name)
  db_execute! "INSERT INTO users VALUES (?, ?, ?)"
    [user.id, user.name, user.email]
}

# A handler that logs to stderr with timestamps
handler timed_log for Log needs {Clock, Stderr} {
  log msg -> {
    let time = now! ()
    stderr_print! ("[" <> format_time time <> "] " <> msg)
    resume ()
  }
}

# Pure handler - just swallows logs (for testing)
handler collect_logs for Log {
  log msg -> resume ()
}


main () = {
  let user = fetch_user 42
  let updated = { user | name: "New Name" }
  save_user updated
  print! ("Done: " <> updated.name)
} with {timed_log, real_http, real_db, to_result}
```

---

## 12. Concurrency & Actors

Concurrency follows the actor model, but falls out of the effect system
rather than being a separate language primitive. Actors are just an effect:

```
effect Actor {
  fun spawn : (() -> Unit needs e) -> Pid
  fun send : Pid -> Msg -> Unit
  fun receive : Unit -> Msg
}
```

Each actor is isolated - no shared memory, only immutable messages passed
between them. This means no data races by construction.

`receive` suspends the actor by storing its continuation; the runtime resumes
it when a message arrives. A simple example:

```
worker () = {
  let msg = receive! ()
  case msg {
    Shutdown -> ()
    Work(data) -> {
      process data
      worker ()
    }
  }
}

main () = {
  let pid = spawn! worker
  send! pid (Work "hello")
  send! pid Shutdown
} with real_actor_runtime
```

**Supervision** is just a handler that catches failures and re-invokes the
computation. No special syntax - it's library code:

```
supervise f =
  f () with {
    fail reason -> {
      log! ("Crashed: " <> reason)
      supervise f   # restart from scratch
    }
  }

main () = {
  supervise (fun () -> {
    let data = Http.get! "/api/data"
    process data
  })
} with {real_http, timed_log}
```

This could implement the "let it crash" philosophy expressed as an effect handler. A more
sophisticated supervisor could track restart counts, apply backoff, or give
up after N failures - all in userspace, no language support needed.

---

## 13. Testing

Tests use the effect system, but test authoring is entirely library-level.
`Std.Test` defines `Test` (for assertions inside an individual test body) and
`Testing` (for registering tests and groups during collection). The `test`,
`describe`, `skip`, and `only` helpers are ordinary functions, not language
primitives.

```
module MathTest

import Std.Test (Testing, describe, test, skip, assert_eq)
import MathLib (add, double)

pub fun tests : Unit -> Unit needs {Testing}
tests () = {
  describe "MathLib" (fun () -> {
    describe "add" (fun () -> {
      test "adds positive numbers" (fun () -> {
        assert_eq (add 2 3) 5
      })

      test "adds negative numbers" (fun () -> {
        assert_eq (add (-1) (-2)) (-3)
      })
    })

    describe "double" (fun () -> {
      test "doubles a number" (fun () -> {
        assert_eq (double 5) 10
      })
    })
  })

  skip "not implemented yet" (fun () -> {
    assert_eq 1 2
  })
}
```

Test files live in a `tests/` directory (configurable via `project.toml`).
Running `saga test` discovers test modules, generates a synthetic entry module,
builds the suite through the normal project pipeline, and runs everything in a
single BEAM VM.

Under the hood:

- `test` / `skip` / `only` perform `Testing` to capture names, modes, and
  thunks
- `describe` performs `enter_group!` / `leave_group!` to preserve structure
- `run_modules` collects all selected modules first, applies global `only`,
  then executes tests one by one
- each test body runs with a `Test` handler attached, so the first failed
  assertion aborts that test only
- panics are caught per test via `catch_panic`, so one crashing test does not
  take down the suite

The exit code behavior means `saga test` works directly in CI pipelines.

---

## 14. Val Bindings

Module-level named values. Not functions -- `val` is for data, `fun` is for
functions. Compiles to a zero-arity BEAM function under the hood, called
automatically at every use site.

```
# Simple constants
val pi = 3.14159
val app_name = "my-app"
val max_retries = 5

# Public (no type signature required -- the value is self-documenting)
pub val version = "1.0.0"

# Any pure expression is valid
val origins = ["localhost", "example.com"]
val config = Config { port: 8080, debug: False }
val codes = Dict.from_list [(404, "Not Found"), (500, "Server Error")]

# @inline annotation: compiler substitutes the literal at use sites
# instead of emitting a function call. RHS must be a compile-time value.
@inline
val pi = 3.141592653589793
```

**Rules:**

- RHS must be pure (no effects). If the expression performs effects, it's an error.
- Inferred type must not be a function (`a -> b`). Use `fun` for functions.
- Can reference other vals and call pure functions.
- `pub val` is exported without a type signature.
- `@inline` restricts the RHS to compile-time literals (scalars, lists, tuples).
  The value is substituted at each use site within the module; a zero-arity
  function is still emitted for cross-module consumers.

**Why not zero-argument functions?** There are no zero-argument functions in the
language -- every function takes at least one parameter. `val` fills the gap for
named constants and precomputed data without introducing zero-arity functions
into the type system. See `docs/val-bindings.md` for the full design rationale.

---

## 15. Settled Decisions & Notes

1. **Effect polymorphism** - higher-order functions explicitly propagate
   effects from callbacks using an effect variable `e`:

   ```
   pub fun map : (a -> b needs e) -> List a -> List b needs e
   ```

   If `f` is pure, `e` is empty and `map` is pure.
   If `f` has effects, `map` has those same effects.
   The caller always sees the full picture.

2. **Effect subtyping** - yes. A function with fewer effects can be used
   where more effects are allowed. `{Console}` is accepted where
   `{Console, FileSystem}` is expected. A function that does less
   is always safe where _more_ is permitted.

3. **Do-notation / block syntax** - not needed. Effectful code is just
   normal code in blocks. The `Fail` effect + `to_result` handler covers
   error chaining. For FFI boundaries returning `Result`, use `and_then`.

4. **Async** - yes, it's just another effect. Lives in the prelude
   alongside Result, Option, print, etc.

   ```
   effect Async {
     fun spawn : (() -> a needs e) -> Future a
     fun await : Future a -> a
   }
   ```

5. **No mutability** - no `let mut`, no `State` effect. State is
   managed through recursion with accumulator arguments, the standard
   ML/functional approach. Handlers don't need mutable state either -
   they define behavior for each effect operation independently.
   If a handler needs to "accumulate" something, that's a sign the
   accumulation belongs in the calling code via recursion, not in the
   handler.

6. **Effect call syntax** - effect operations use `!` at the call site:
   `log! "hello"`, `fail! "oops"`, `get! key`. This marks the exact
   point where control may transfer to a handler. Pure function calls
   don't get `!`. Only primitive effect operations (declared in an
   `effect` block) use it -calling a function that internally uses
   effects is a normal call.

7. **Effect annotation syntax** - functions declare effects with `needs`
   after the return type: `fun f : Unit -> T needs {Log, Http}`. Handlers use
   `for`: `handler foo for Log { ... }`. This aligns with `impl Show for User`.
   `with` is reserved exclusively for handler attachment (`expr with handler`).
   Handlers that use effects in their body also declare `needs`:
   `handler foo for Log needs {Console} { ... }`. Pure handlers omit it.

8. **String interpolation** - `$"..."` prefix opts a string in to interpolation. Holes are `{expr}`.

   ```
   greet name = print $"Hello, {name}!"
   debug x y = print $"x = {show x}, y = {show y}"
   ```

9. **Lambdas** - use `fun`, no trailing lambda syntax.
   Pipes with `fun` read cleanly enough.

   ```
   items |> List.map (fun x -> x * 2)
   ```

10. **Backward pipes** - `<|` for lowering precedence, avoids parens.

```
# These are equivalent:
print (show (add 1 2))
print <| show <| add 1 2
```

11. **Effect propagation** - effects propagate virally through function
    signatures. If `fn3` needs `{Log}` and `fn2` calls `fn3` without
    handling it, `fn2` must also declare `needs {Log}`. This continues
    up the call chain until a handler is attached via `with`. This is
    intentional: every function signature tells you exactly what effects
    it requires. The handler can be attached at any level - the direct
    caller, or further up.

12. **`panic`, `todo`, and process control** - `panic "msg"` and `todo ()`
    are language builtins, not effects. They crash the program by default --
    no handler, no propagation, no `!`. They return `-> a` (a free type
    variable), which unifies with any expected type, so they work in any
    position. `panic` is for unreachable code / logic errors. `todo`
    is for unfinished code.

    Unhandled panics print to stderr and exit with code 1. Panics can be
    caught at recovery boundaries with `catch_panic` (see item 13).

    For explicit exit codes, `Std.Process` provides `exit : Int -> a`
    (immediate halt) and `shutdown : Int -> a` (graceful VM shutdown).

    ```
    import Std.Process

    Process.exit 0        # success
    Process.exit 1        # failure
    panic "unreachable"   # prints "panic: unreachable" to stderr, exits 1
    todo ()               # prints "todo: not implemented" to stderr, exits 1
    ```

13. **Panic recovery** - `catch_panic` is an opt-in recovery boundary, similar
    to Rust's `std::panic::catch_unwind`. It runs a function and returns
    `Ok(value)` if it completes normally, or `Err(message)` if it panicked.

    ```
    import Std.Process (catch_panic)

    # Basic recovery
    case catch_panic (fun () -> might_blow_up ()) {
      Ok(result) -> use_result result
      Err(msg) -> log! $"recovered from panic: {msg}"
    }
    ```

    `catch_panic` is not for error handling -- use the `Fail` effect for
    recoverable errors. It exists for two cases: protecting a boundary
    (server loop, request handler) from crashing the whole process, and
    testing that code panics when it should.

    Effects work inside the thunk. Handler parameters from the surrounding
    scope are captured by the lambda, so effectful code runs normally:

    ```
    fun safe_process : Request -> Response needs {Log, Database}
    safe_process req = {
      case catch_panic (fun () -> handle_request req) {
        Ok(resp) -> resp
        Err(msg) -> {
          log! $"request panicked: {msg}"
          error_response 500
        }
      }
    }
    ```

    The return value is `Result a String` -- you get the panic message as a
    string, nothing more. You can't match on structured error types or build
    control flow around panic messages. For structured errors, use `Fail`.

    ```
    # In tests
    import Std.Test (assert_panics)

    test "head of empty list panics" {
      assert_panics (fun () -> List.head [])
    }
    ```

14. **Negative literals as arguments** - require parentheses, same as Elm/Haskell.
    `-` is always binary minus in application position; wrap negatives in parens.

```
f (-5)    # fine
f -5      # parse error: binary minus with missing right operand
-x        # fine: unary negation in expression position
```

15. **Libraries return `Result`, applications use `Fail`** - fallible operations
    in libraries (stdlib and third-party) should return `Result`, not impose the
    `Fail` effect on callers. Effects propagate virally through `needs` clauses,
    so a library that uses `Fail QueryError` (or any specific Fail instance)
    forces every transitive caller to declare the same `needs` or attach a
    handler. Different applications have different error policies — fail-fast
    in dev, retry in prod, structured errors over HTTP. Libraries don't know
    their caller's policy and shouldn't pre-commit to one.

    `Result` is the neutral primitive; `Fail` is application-level sugar built
    on top of it. Going from `Result` to `Fail` is a one-line wrapper; going
    the other way requires `to_result` and an extra layer of indirection. The
    `Result`-returning library preserves both options without losing
    information.

    ```
    # Library: returns Result
    pub fun execute : String -> List Value -> Result (Returned Dynamic) QueryError
      needs {Postgres}

    # Application: lifts to Fail when convenient
    fun execute_or_fail : String -> List Value -> Returned Dynamic
      needs {Postgres, Fail QueryError}
    execute_or_fail sql params = case execute sql params {
      Ok(r) -> r
      Err(e) -> fail! e
    }
    ```

    Inside a library, `Fail` is fine as an internal implementation detail
    handled before the function returns. The rule is about public signatures,
    not internal mechanics.
