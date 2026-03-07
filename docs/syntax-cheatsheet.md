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
pub fun add (a: Int) (b: Int) -> Int
add a b = a + b

# Function - private annotated (optional)
fun double (x: Int) -> Int
double x = x * 2

# Function - unannotated (fully inferred)
triple x = x * 3

# Zero-arg function
pub fun main () -> Unit
main () = print "hello"

# Lambda
fun x -> x + 1

# Currying / partial application
add_five = add 5
```

---

## Operators & Syntax

```
# Arithmetic: + - * / %
# Comparison: == != < > <= >=
# Logic: && ||
# String concat: <>
# Pipe: |>
# Backward-pipe: <| (desugars to opposite of pipe)
# Cons: ::

5 |> add 3 |> show |> print

"hello" <> " " <> "world"

1 :: 2 :: 3 :: []
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
type Shape {
  Circle(Float)
  Rect(Float, Float)
  Point
}

# With type parameter
type Maybe a {
  Just(a)
  Nothing
}

# Pipe separator (optional, newlines also work)
type Color { Red | Green | Blue }
```

---

## Records

```
record User {
  name : String,
  age  : Int,
}

# Create
let u = User { name: "Dylan", age: 30 }

# Field access
u.name

# Update
{ u | age: u.age + 1 }
```

---

## Tuples

```
let pair = (1, "hello")
let triple = (1, 2, 3)

# Type annotation
fun swap (p: (a, b)) -> (b, a)
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

# Guards
case n {
  n if n < 0 -> 0
  n if n > 100 -> 100
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
```

---

## Let Destructuring

```
let (x, y) = compute_pair ()
let Point { x, y } = get_point ()
let h :: t = some_list
```

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

## Effects

```
# Declare an effect
effect Log {
  fun log (msg: String) -> Unit
}

effect Fail {
  fun fail (reason: String) -> Never
}

# Zero-arg op called with ()
effect State {
  fun get () -> Int
  fun put (n: Int) -> Unit
}

# Use effects -- ! marks the call site
fun process (path: String) -> Unit needs {Log, Fail}
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
  log msg -> {
    print msg
    resume ()
  }
}

# Handler that uses other effects
handler timed_log for Log needs {Clock} {
  log msg -> {
    let t = now! ()
    print ($"{t}: {msg}")
    resume ()
  }
}

# Aborting handler (no resume)
handler to_result for Fail {
  fail reason -> Err(reason)
  return value -> Ok(value)   # intercept success
}

# Inline handler
result = compute () with {
  log msg -> { print msg; resume () },
  fail reason -> Err(reason),
}

# Named handler attachment
result = compute () with console

# Handler stacking (named + inline mixed)
main () = {
  run ()
} with {
  console,
  to_result,
  fail reason -> { print reason; resume () },
}
```

---

## Traits

```
# Define a trait
trait Show a {
  fun show (x: a) -> String
}

# Trait with supertraits
trait Ord a where {a: Eq} {
  fun compare (x: a) (y: a) -> Ordering
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
fun to_string (x: a) -> String where {a: Show}
to_string x = show x

# Multiple bounds: +
fun print_if_equal (x: a) (y: a) -> Unit needs {Log} where {a: Show + Eq}
print_if_equal x y =
  if x == y then log! (show x)
  else log! "not equal"

# Bounds on multiple type vars
fun convert (x: a) -> b where {a: Show, b: Read}
convert x = read (show x)

# needs comes before where
pub fun run (items: List a) -> Unit needs {Log} where {a: Show}
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
pub fun exported () -> Int   # visible to importers
fun private () -> Int        # module-internal only
pub type Shape { ... }
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

## Builtins

```
# Halt immediately, type Never (works anywhere)
panic "unreachable"
todo "implement this"

# Built-in traits: Show, Eq, Ord, Num
# Built-in types: Int, Float, String, Bool, Unit, Never
# Literals: 42, 3.14, "hello", True, False, ()
# Unit value: ()
```

---

## Type Annotations

```
# Basic
(x: Int)
(xs: List Int)
(f: a -> b)

# With needs on a parameter type (HOF effect absorption)
(computation: () -> a needs {Fail})

# Unit param
fun main () -> Unit

# Needs and where together
fun f (x: a) -> b needs {Log} where {a: Show}

# Arrow type
fun apply (f: a -> b) (x: a) -> b
```
