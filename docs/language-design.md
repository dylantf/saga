# dylang — Language Design Exploration

These are fake programs to explore how the syntax and features fit together.
Nothing here is implemented — it's all vibes and iteration.

---

## 1. Basics (what already works, more or less)

```
# Comments with hash

#@ Doc comments with hash-at
#@ They attach to the next definition

# Function definitions — three levels:

# Public, annotated (required for public API)
pub fun add (a: Int) (b: Int) -> Int
add x y = x + y

# Private, annotated (optional, for documentation)
fun double (x: Int) -> Int
double x = x * 2

# Private, inferred (no annotation at all)
triple x = x * 3

# Zero-arg functions take Unit
pub fun main () -> Unit
main () = {
  let x = add 3 4
  let y = double x
  print y
}

# Pipe operator
pub fun main () -> Unit
main () = {
  5
  |> add 3
  |> show
  |> print
}

# Lambdas
pub fun apply (f: a -> b) (x: a) -> b
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
type Option a {
  Some(a)
  None
}

type Result a e {
  Ok(a)
  Err(e)
}

type List a {
  Cons(a, List a)
  Nil
}

# Exhaustive pattern matching
pub fun unwrap (opt: Option a) (default: a) -> a
unwrap opt default = case opt {
  Some(x) -> x
  None -> default
}

# Nested patterns
type Expr {
  Lit(Int)
  Add(Expr, Expr)
  Mul(Expr, Expr)
}

pub fun eval (expr: Expr) -> Int
eval expr = case expr {
  Lit(n) -> n
  Add(a, b) -> eval a + eval b
  Mul(a, b) -> eval a * eval b
}

# Guards in patterns — yes, with `if`
# Any pure function (no effects) can be used in guards
pub fun clamp (n: Int) -> Int
clamp n = case n {
  n if n < 0   -> 0
  n if n > 100 -> 100
  n            -> n
}

# Arbitrary pure functions in guards
is_valid s = String.length s > 0 && String.length s < 100

pub fun describe (s: String) -> String
describe s = case s {
  s if is_valid s  -> "valid: " <> s
  _               -> "invalid"
}

# Guards on function definitions too
pub fun abs (n: Int) -> Int
abs n if n < 0 = -n
abs n          = n
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
pub fun greet (user: User) -> String
greet user = "Hello, " <> user.name

# Record update syntax
pub fun birthday (user: User) -> User
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

type ApiResponse {
  Success
  ApiError
}

# Pattern matching on record variants
pub fun describe (resp: ApiResponse) -> String
describe resp = case resp {
  Success { status, body } -> "OK " <> show status
  ApiError { code, message } -> "Error " <> show code <> ": " <> message
}

# Field aliasing in patterns
describe resp = case resp {
  Success { status: s, body: b } -> "OK " <> show s
  ApiError { code: c }           -> "Error " <> show c
}

# Record matches are always partial — unmentioned fields are ignored
# No special syntax needed, just match what you care about
header_only resp = case resp {
  Success { status } -> status
  ApiError {}        -> 0
}

# Exhaustiveness is at the variant level, not field level
# This warns — missing ApiError case:
#   case resp { Success { status } -> status }
# This is fine — matches all variants:
#   case resp { Success { status } -> status, _ -> 0 }

# `_` for positional ADT discards
fun has_value (opt: Option a) -> Bool
has_value opt = case opt {
  Some(_) -> True
  None    -> False
}

# ADTs can still have simple positional variants
type Option a {
  Some(a)
  None
}

# Rule: ADT variants are either bare names (possibly records)
# or carry positional data with parens. Never inline field definitions.
```

---

## 4. Effects — The Core Idea

```
# Effects are declared like traits/interfaces
effect Console {
  fun print (msg: String) -> Unit
  fun read_line () -> String
}

effect FileSystem {
  fun read_file (path: String) -> String
  fun write_file (path: String) (data: String) -> Unit
}

effect Fail {
  fun fail (reason: String) -> Never
}

# Functions declare which effects they use
pub fun greet (name: String) -> String with {Console}
greet name = {
  print ("Hello, " <> name)
  "greeted"
}

# Effects compose naturally
pub fun process_file (path: String) -> Unit with {Console, FileSystem, Fail}
process_file path = {
  let contents = read_file path
  if contents == "" then
    fail "empty file"
  else
    print contents
}
```

---

## 5. Effect Handlers

```
# Handlers provide implementations for effects
# They look like case expressions (intentionally)

main () = {
  process_file "data.txt"
} with {
  # Console handler
  print msg   -> stdout_print msg
  read_line () -> stdout_read_line ()

  # FileSystem handler
  read_file path        -> os_read_file path
  write_file path data  -> os_write_file path data

  # Fail handler
  fail reason -> {
    print ("Error: " <> reason)
    exit 1
  }
}

# QUESTION: should handlers be named/reusable?

handler std_io : Console {
  print msg   -> stdout_print msg
  read_line () -> stdout_read_line ()
}

handler mock_console : Console {
  print msg   -> ()   # swallow output
  read_line () -> "mock input"
}

# Then you use them by name
pub fun main () -> Unit
main () = {
  greet "Dylan"
} with std_io

# For testing
test () = {
  let result = greet "Dylan" with mock_console
  assert (result == "greeted")
}
```

---

## 6. Effect Handlers — Advanced (Continuations)

```
# `resume` is a keyword available in any handler
# It sends a value back to the point where the effect was performed
# Think of it like async/await — but for everything

effect Ask {
  fun ask (question: String) -> String
}

# A handler that intercepts questions and returns placeholders
handler collect_questions : Ask {
  ask question -> {
    log question
    resume "placeholder"
  }
}

# A handler that doesn't resume — computation stops
# (like a catch block that doesn't rethrow)
handler to_result : Fail {
  fail reason -> Err(reason)
}

# Retry logic — resume on success, fail on second attempt
effect Http {
  fun get (url: String) -> String
}

handler with_retry : Http {
  get url -> {
    case http_get url {
      Ok(body) -> resume body
      Err(_)   -> {
        sleep 1000
        case http_get url {
          Ok(body) -> resume body
          Err(e)   -> fail ("gave up: " <> e)
        }
      }
    }
  }
}

# Rules:
# - `resume` is always available in handlers, like `return`
# - If a handler calls `resume`, computation continues
# - If a handler doesn't call `resume`, computation is aborted
# - No need to explicitly bind the continuation
```

---

## 7. Error Handling via Effects

```
# No exceptions, no special syntax — errors are just effects

effect Fail {
  fun fail (reason: String) -> Never
}

# The classic Result pattern falls out of handlers
# `return` handles the case where no effect was triggered
handler to_result : Fail {
  fail reason -> Err(reason)
  return value -> Ok(value)
}

fun safe_divide (x: Int) (y: Int) -> Int with {Fail}
safe_divide x y =
  if y == 0 then fail "division by zero"
  else x / y

main () = {
  let result = safe_divide 10 0 with to_result
  case result {
    Ok(n)  -> print (show n)
    Err(e) -> print ("Error: " <> e)
  }
}

# `return` in a handler intercepts the final value of the computation
# Without it, the value passes through unchanged
# Most handlers don't need it — to_result is the classic case that does
```

---

## 8. With Expressions (Result Chaining)

```
# `with` is sugar for chaining Result-returning functions
# Short-circuits on the first Err, like Elixir's `with`

# Pure effect-based code doesn't need this — fail handles it.
# But at the boundary with Result-returning code (libraries, FFI),
# it's really nice.

pub fun load_user_profile (id: Int) -> Result UserProfile String
load_user_profile id = with {
  user <- fetch_user id,
  profile <- fetch_profile user,
  settings <- load_settings profile.id,
} then {
  Ok { user, profile, settings }
} else {
  Err(reason) -> Err("Failed: " <> reason)
}

# It's just an expression — use it in let bindings
main () = {
  let result = with {
    x <- parse_int input,
    y <- parse_int other_input,
  } then {
    Ok (x + y)
  } else {
    Err(e) -> Err(e)
  }

  case result {
    Ok(n)  -> print (show n)
    Err(e) -> print e
  }
}

# Works in pipes too
with {
  x <- parse_int input,
  y <- parse_int other_input,
} then {
  Ok (x + y)
} else {
  Err(e) -> Err(e)
}
|> handle_result

# Each `<-` unwraps an Ok and binds the value
# If any step returns Err, jumps straight to `else`
# `then` is the happy path, `else` handles the error
```

---

```
# Explicit module naming — file path doesn't matter
# File: foo/bar/some_module.dy

module Foo.Bar.SomeModule

# pub fun = public, fun = private annotation, bare = private inferred
pub fun abs (n: Int) -> Int
abs n if n < 0 = -n
abs n          = n

pub fun max (a: Int) (b: Int) -> Int
max a b = if a > b then a else b

# Private — not visible outside module
helper x = x + 1

# Importing
import Math
import Math exposing { abs, max }
import Math as M

pub fun main () -> Unit
main () = {
  M.abs (-5) |> print
}
```

---

## 10. Traits

```
# Traits are for type-driven dispatch — the implementation is
# determined by the type, not the call site.
# Effects are for context-driven dispatch — the caller provides
# the implementation via handlers.

trait Show a {
  fun show (x: a) -> String
}

trait Eq a {
  fun eq (x: a) (y: a) -> Bool
}

trait Ord a where Eq a {
  fun compare (x: a) (y: a) -> Ordering
}

# Implementing for a type
impl Show for User {
  show user = user.name <> " (age " <> show user.age <> ")"
}

# Used as constraints with `where`
pub fun print_all (items: List a) -> Unit with {Console} where Show a
print_all items = case items {
  Cons(x, rest) -> {
    print (show x)
    print_all rest
  }
  Nil -> ()
}

# Rule of thumb:
# - "How do I convert X to a string?" -> trait (Show), determined by type
# - "Where do I send this log message?" -> effect (Log), determined by caller
```

---

## 11. Putting It All Together — A Realistic Program

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

type ApiError {
  NotFound(String)
  Unauthorized
  ServerError(String)
}

effect Log {
  fun log (msg: String) -> Unit
}

pub fun fetch_user (id: Int) -> User with {Http, Fail, Log}
fetch_user id = {
  log ("Fetching user " <> show id)
  let response = get ("/api/users/" <> show id)
  case parse_json response {
    Ok(user) -> user
    Err(e)   -> fail ("Parse error: " <> e)
  }
}

pub fun save_user (user: User) -> Unit with {Db, Fail, Log}
save_user user = {
  log ("Saving user " <> user.name)
  db_execute "INSERT INTO users VALUES (?, ?, ?)"
    [user.id, user.name, user.email]
}

# A handler that logs to stderr with timestamps
handler timed_log : Log {
  log msg -> {
    let time = now ()
    stderr_print ("[" <> format_time time <> "] " <> msg)
  }
}

# A handler that collects logs into a list (for testing)
handler collect_logs : Log {
  log msg -> {
    append_to_state msg
    resume ()
  }
}

pub fun main () -> Unit
main () = {
  let user = fetch_user 42
  let updated = { user | name: "New Name" }
  save_user updated
  print ("Done: " <> updated.name)
} with {
  timed_log,
  real_http,
  real_db,
  to_result
}
```

---

## 12. Settled Decisions & Notes

1. **Effect polymorphism** — higher-order functions explicitly propagate
   effects from callbacks using an effect variable `e`:

   ```
   pub fun map (f: a -> b with e) (xs: List a) -> List b with e
   ```

   If `f` is pure, `e` is empty and `map` is pure.
   If `f` has effects, `map` has those same effects.
   The caller always sees the full picture.

2. **Effect subtyping** — yes. A function with fewer effects can be used
   where more effects are allowed. `{Console}` is accepted where
   `{Console, FileSystem}` is expected. A function that does _less_
   is always safe where _more_ is permitted.

3. **Do-notation / block syntax** — not needed. Effectful code is just
   normal code in blocks. For Result chaining at effect boundaries,
   `with` expressions handle it (see section 8).

4. **Async** — yes, it's just another effect. Lives in the prelude
   alongside Result, Option, print, etc.

   ```
   effect Async {
     fun spawn (f: () -> a with e) -> Future a
     fun await (future: Future a) -> a
   }
   ```

5. **Mutability** — yes, local mutable state is an effect.

   ```
   effect State s {
     fun get () -> s
     fun put (value: s) -> Unit
   }

   fun counter () -> Int with {State Int}
   counter () = {
     let n = get ()
     put (n + 1)
     n
   }
   ```

6. **String interpolation** — `${expr}` inside double-quoted strings.

   ```
   greet name = print "Hello, ${name}!"
   debug x y = print "x = ${show x}, y = ${show y}"
   ```

7. **Lambdas** — use `fun`, no trailing lambda syntax.
   Pipes with `fun` read cleanly enough.

   ```
   items |> List.map (fun x -> x * 2)
   ```

8. **Backward pipes** — `<|` for lowering precedence, avoids parens.
   ```
   # These are equivalent:
   print (show (add 1 2))
   print <| show <| add 1 2
   ```
