# dylang Syntax Cheatsheet

Quick reference for all language syntax. See `language-design.md` for rationale and `effects-guide.md` for effects deep-dive.

---

## Comments

```
# Line comment
#@ Doc comment (attaches to next definition)
```

---

## Bindings & Functions

```
# Let binding
let x = 42
let name = "Dylan"

# Function - annotated (required for pub)
pub fun add : Int -> Int -> Int
add a b = a + b

# With optional parameter labels (documentation only)
pub fun add : (a: Int) -> (b: Int) -> Int
add a b = a + b

# Function - private annotated (optional)
fun double : Int -> Int
double x = x * 2

# Function - unannotated (fully inferred)
triple x = x * 3

# Zero-arg function
pub fun main : Unit -> Unit
main () = print "hello"

# Lambda
fun x -> x + 1

# Currying / partial application
add_five = add 5
```

---

## Operators & Syntax

```
# Arithmetic: + - * / % (% is Int-only)
# Integer division truncates: 7 / 2 = 3
# Comparison: == != < > <= >=
# Logic: && ||
# String concat: <>
# Pipe: |>
# Backward-pipe: <| (desugars to opposite of pipe)
# Compose: >>  (f >> g = fun x -> g (f x))
# Backward-compose: <<  (f << g = fun x -> f (g x))
# Cons: ::

5 |> add 3 |> show |> print

"hello" <> " " <> "world"

1 :: 2 :: 3 :: []

# Composition: point-free version of piping
let process = parse >> validate >> save
result |> process
```

---

## Blocks & Sequencing

```
main () = {
  let x = add 3 4
  let y = double x
  print (show y)
}

# Last expression is the block's value
compute x = {
  let a = x * 2
  let b = a + 1
  b         # returned
}
```

---

## Conditionals

```
abs n = if n < 0 then -n else n
```

---

## ADTs

```
type Shape
  = Circle(Float)
  | Rect(Float, Float)
  | Point

# With type parameter
type Maybe a
  = Just(a)
  | Nothing

# Single line
type Color = Red | Green | Blue

# Opaque types (opaque keyword implies `pub`)
opaque type Foo = Bar | Baz
```

---

## Records

```
# Comma-separated fields (trailing comma optional)
record User {
  name : String,
  age  : Int,
}

# Polymorphic records
record Box a {
  value : a,
}

# Create
let u = User { name: "Dylan", age: 30 }
let b = Box { value: 42 }        # Box Int

# Field access
u.name
b.value                           # 42

# Update
{ u | age: u.age + 1 }
{ b | value: "hello" }           # Box String
```

---

## Tuples

```
let pair = (1, "hello")
let triple = (1, 2, 3)

# Type annotation
fun swap : (a, b) -> (b, a)
swap (x, y) = (y, x)
```

---

## Pattern Matching

```
# Case expression
case shape {
  Circle(r) -> r * r * 3.14
  Rect(w, h) -> w * h
  Point -> 0.0
}

# Guards (| in both case arms and function definitions)
case n {
  n | n < 0 -> 0
  n | n > 100 -> 100
  n -> n
}

# Guard on function definition
abs n | n < 0 = -n
abs n = n

# Wildcard
case opt {
  Just(x) -> x
  _ -> 0
}

# List patterns
case xs {
  [] -> "empty"
  [x] -> "one"
  [x, y] -> "two"
  h :: t -> "many"
}

# Tuple patterns
case pair {
  (x, y) -> x + y
}

# Record patterns
case user {
  User { name, age } -> name
  User { name: n } -> n   # field alias
}

# String patterns
case msg {
  "hello" -> "exact match"
  "[ERROR]: " <> detail -> detail   # prefix split
  _ -> "unknown"                    # required (strings are infinite)
}
```

---

## Let Destructuring

```
let (x, y) = compute_pair ()
let Point { x, y } = get_point ()
let h :: t = some_list
```

---

## List Comprehensions

```
# Haskell-style: [expr | qualifiers]
[x * 2 | x <- xs]                    # map
[x | x <- xs, x > 0]                 # filter
[x + y | x <- xs, y <- ys]           # nested generators (cartesian product)
[x * 2 | x <- xs, x > 3]             # guard + transform
[y | x <- xs, let y = x + 1, y > 3]  # let binding in comprehension
```

Desugars in the parser to `flat_map`, `if/else`, and `let` -- no special runtime support.

---

## String Interpolation

```
$"Hello, {name}!"
$"Result: {show (x + y)}"
$"Pipe works: {xs |> length}"

# Escape literal brace
$"Show \{ literal brace"
```

---

## Multiline Strings

```
# Triple-quoted strings allow literal newlines
let sql = """
    SELECT *
    FROM users
    WHERE age > 30
    """
# Result: "SELECT *\nFROM users\nWHERE age > 30"
# Indentation is stripped based on the column of the closing """

# Escape sequences work the same as regular strings
let msg = """
    hello\tworld
    """

# Multiline interpolated strings
let report = $"""
    Name: {user.name}
    Age:  {user.age}
    """
```

---

## Raw Strings

```
# @ prefix disables escape processing
@"hello\nworld"       # literal backslash-n, not a newline

# Raw multiline strings
@"""
    no \n escapes here either
    backslashes are \ literal
    """
```

---

## Effects

```
# Declare an effect
effect Log {
  fun log : String -> Unit
}

effect Fail {
  fun fail : String -> Never
}

# Zero-arg op called with ()
effect State {
  fun get : Unit -> Int
  fun put : Int -> Unit
}

# Use effects -- ! marks the call site
fun process : String -> Unit needs {Log, Fail}
process path = {
  log! ("processing " <> path)
  if path == "" then fail! "empty path"
  else log! "done"
}

# Qualified when ambiguous
Cache.get! key
Database.get! key
```

---

## Handlers

```
# Named handler
handler console for Log {
  log msg = {
    print msg
    resume ()
  }
}

# Handler that uses other effects
handler timed_log for Log needs {Clock} {
  log msg = {
    let t = now! ()
    print ($"{t}: {msg}")
    resume ()
  }
}

# Aborting handler (no resume)
handler to_result for Fail {
  fail reason = Err(reason)
  return value = Ok(value)   # intercept success
}

# Inline handler
result = compute () with {
  log msg = { print msg; resume () },
  fail reason = Err(reason),
}

# Named handler attachment
result = compute () with console

# Handler stacking (named + inline mixed)
main () = {
  run ()
} with {
  console,
  to_result,
  fail reason = { print reason; resume () },
}
```

---

## Traits

```
# Define a trait
trait Show a {
  fun show : a -> String
}

# Trait with supertraits
trait Ord a where {a: Eq} {
  fun compare : a -> a -> Ordering
}

# Implement a trait
impl Show for User {
  show u = u.name <> " (age " <> show u.age <> ")"
}

# Conditional impl
impl Show for List a where {a: Show} {
  show xs = "[" <> join ", " (map show xs) <> "]"
}

# Trait bounds on functions
fun to_string : a -> String where {a: Show}
to_string x = show x

# Multiple bounds: +
fun print_if_equal : a -> a -> Unit needs {Log} where {a: Show + Eq}
print_if_equal x y =
  if x == y then log! (show x)
  else log! "not equal"

# Bounds on multiple type vars
fun convert : a -> b where {a: Show, b: Read}
convert x = read (show x)

# needs comes before where
pub fun run : List a -> Unit needs {Log} where {a: Show}
run items = case items {
  [] -> ()
  h :: t -> { log! (show h); run t }
}
```

---

## Modules

```
# Declare (top of file)
module Math
module Data.Collections

# Import
import Math
import Math as M
import Math (abs, max)
import Math as M (abs, max)

# Qualified access
M.abs (-5)

# Visibility
pub fun exported : Unit -> Int   # visible to importers
fun private : Unit -> Int        # module-internal only
pub type Shape = ...
pub record User { ... }
pub handler console for Log { ... }
```

---

## do...else (Sequential Pattern Binding)

```
# Each line: Pat <- expr. If the pattern matches, bind vars and continue.
# If it doesn't match, evaluate the corresponding else arm.
# The last line (no <-) is the success return expression.

do {
  Ok(user)  <- get_user id
  Ok(order) <- get_order user
  Ok(order)                    # success return; type: Result Order E
} else {
  Err(e) -> Err(e)             # bail return; must unify with success type
}

# Mixed bail types (each binding can fail differently):
do {
  True      <- bool_fn ()
  Some(str) <- maybe_fn True
  Ok(n)     <- result_fn str
  Ok(n)
} else {
  False    -> Err("false")
  None     -> Err("none")
  Err(msg) -> Err(msg)
}

# Success expression can be any value -- not required to be Ok/Err:
do {
  Ok(x) <- step1 ()
  Ok(y) <- step2 x
  x + y                        # success return type: Int
} else {
  Err(_) -> 0                  # else must also return Int
}
```

---

## Dictionaries

```
# Built-in Dict k v type. Keys require Eq. All operations are immutable.

# Empty dict
let d = Dict.new ()

# Create from list of tuples
let ages = Dict.from_list [("alice", 30), ("bob", 25)]

# Lookup (returns Maybe v)
Dict.get "alice" ages        # Some(30)
Dict.get "unknown" ages      # None

# Insert / update
let ages2 = Dict.put "charlie" 35 ages

# Remove
let ages3 = Dict.remove "bob" ages

# Membership
Dict.member "alice" ages     # True

# Size
Dict.size ages               # 2

# Keys and values (as Lists)
Dict.keys ages               # ["alice", "bob"]
Dict.values ages             # [30, 25]

# Round-trip through list of tuples
Dict.to_list ages            # [("alice", 30), ("bob", 25)]

# Pipe-friendly
Dict.new ()
  |> Dict.put "x" 1
  |> Dict.put "y" 2
```

---

## Testing

```
import Std.Test (describe, test, skip, assert_eq, assert_neq)

# describe/test/skip are sugar: the block becomes a lambda argument
# test "name" { body }  ->  test "name" (fun () -> { body })
# describe "name" { body }  ->  describe "name" (fun () -> { body })

describe "Math" {
  test "addition" {
    assert_eq (1 + 2) 3
  }

  test "subtraction" {
    assert_eq (5 - 3) 2
  }

  skip "not ready yet" {
    assert_eq 1 2
  }
}

# Run with: dylang test
# Exit code 1 on any failure (CI-friendly)
```

---

## Process Control

```
import Std.Process

# Immediate termination with exit code
Process.exit 0
Process.exit 1

# Graceful VM shutdown (flushes IO, runs shutdown hooks)
Process.shutdown 0

# panic / todo print to stderr and exit 1
panic "something went wrong"    # prints "panic: something went wrong" to stderr
todo "implement this"           # prints "todo: implement this" to stderr

# All three return Never -- usable in any expression position
```

---

## Builtins

```
# Built-in traits: Show, Eq, Ord, Num
# Built-in types: Int, Float, String, Bool, Unit, Never, Dict k v
# Literals: 42, 3.14, "hello", True, False, ()
# Unit value: ()

# IO
print "hello"               # stdout
print_error "oops"           # stderr
```

---

## Type Annotations

```
# Annotations use `:` followed by an arrow chain
fun add : Int -> Int -> Int

# Labels are optional (purely documentation)
fun add : (a: Int) -> (b: Int) -> Int

# With needs on a parameter type (HOF effect absorption)
fun try : (() -> a needs {Fail}) -> Result a String

# Unit param
fun main : Unit -> Unit

# Needs and where together
fun f : a -> b needs {Log} where {a: Show}

# Arrow type parameter
fun apply : (a -> b) -> a -> b

# Mix labeled and unlabeled freely
fun foldl : (f: b -> a -> b) -> b -> List a -> b
```
