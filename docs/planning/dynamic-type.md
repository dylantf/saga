# Dynamic Type — Safe BEAM Interop

## Problem

Data from outside the type system arrives as untyped Erlang terms: FFI calls,
ETS lookups, messages from non-dylang processes, database drivers, decoded
binary protocols. Without a safe bridge, you either trust the data blindly or
can't interop with the Erlang ecosystem.

## Design

`Dynamic` is an opaque type wrapping a raw Erlang term. Pure decoder functions
attempt to extract typed values, returning `Result`:

```
opaque type Dynamic = Dynamic

pub type DecodeError =
  | TypeMismatch(expected: String, got: String)
  | MissingField(name: String)
  | IndexOutOfBounds(index: Int)

fun as_int : Dynamic -> Result Int DecodeError
fun as_float : Dynamic -> Result Float DecodeError
fun as_string : Dynamic -> Result String DecodeError
fun as_bool : Dynamic -> Result Bool DecodeError
fun as_list : Dynamic -> Result (List Dynamic) DecodeError

fun field : String -> Dynamic -> Result Dynamic DecodeError
fun index : Int -> Dynamic -> Result Dynamic DecodeError

fun from_erlang : a -> Dynamic    # wrap any BEAM term
```

## Why pure, not an effect

Decoding is a type check on a value — it either matches or it doesn't. The
interesting error handling (fail fast vs collect all) already lives in the
`Validate` effect (see `examples/20-validation-applicative.dy`). Layering a
`Decode` effect on top would be redundant.

The two layers compose cleanly:

- **Dynamic**: "is this BEAM term an Int?" → `Result`
- **Validate**: "is this Int above 18?" → error accumulation via effect

## Usage

### Basic decoding

```
fun parse_user : Dynamic -> Result User DecodeError
parse_user d = do {
  Ok(name) <- field "name" d |> Result.and_then as_string
  Ok(age)  <- field "age" d |> Result.and_then as_int
  Ok(User { name, age })
} else {
  Err(e) -> Err(e)
}
```

### With validation (error collecting)

```
fun parse_and_validate : Dynamic -> Validation (List String) ValidUser
  needs {Validate}
parse_and_validate d = {
  let name = field "name" d |> Result.and_then as_string |> unwrap_or ""
  let age = field "age" d |> Result.and_then as_int |> unwrap_or 0
  require_non_empty "name" name
  require_min_age 18 age
  ValidUser { name, age }
}

main () = {
  let raw = from_erlang some_erlang_term
  let result = parse_and_validate raw with collecting
  println (debug result)
}
```

### Erlang FFI

```
# Calling an Erlang function that returns a dynamic term
let raw = from_erlang (erlang_lib_call ())

case as_int raw {
  Ok(n) -> process n
  Err(TypeMismatch(expected, got)) ->
    fail! $"expected {expected}, got {got}"
}
```

## Use cases

- **Erlang/Elixir library interop**: return values from FFI calls
- **ETS**: untyped term storage
- **Process messages from non-dylang processes**: unknown message shapes
- **Database drivers**: rows as Erlang tuples/lists
- **JSON/msgpack/ETF**: after initial parse, walk the resulting BEAM terms

## Implementation

Decoders are thin wrappers around BEAM runtime type checks:

- `as_int` → `is_integer/1` guard + cast
- `as_string` → `is_binary/1` guard + cast
- `as_list` → `is_list/1` guard + cast
- `field` → map/proplist lookup
- `from_erlang` → identity (just wraps the term in the opaque type)

Straightforward FFI, no special compiler support needed.
