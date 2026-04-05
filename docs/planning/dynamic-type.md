# Dynamic Type — Safe BEAM Interop

## Problem

Data from outside the type system arrives as untyped Erlang terms: FFI calls,
ETS lookups, messages from non-dylang processes, database drivers, decoded
binary protocols. Without a safe bridge, you either trust the data blindly or
can't interop with the Erlang ecosystem.

## Audience

`Std.Dynamic` is an escape hatch for **library authors** wrapping Erlang
packages, not something application developers should reach for. The expected
layering:

```
Erlang lib (pgo, jason, etc.)
  ↓ @external returning Dynamic
Std.Dynamic (decoders)
  ↓ library author writes typed wrapper
Typed wrapper library (e.g. a Postgres or JSON lib)
  ↓ app developer uses this
Application code
```

Application developers should never see `Dynamic`. If they do, the library
wrapper is incomplete.

## Design

### Dynamic type

`Dynamic` is an opaque type wrapping a raw Erlang term:

```
opaque type Dynamic = Dynamic
```

FFI functions can return `Dynamic` directly — since `@external` trusts the type
signature, no bridge file is needed:

```
@external("erlang", "pgo", "query")
fun raw_query : String -> List Dynamic -> Dynamic
```

### Decoder type

`Decoder a` is an opaque type wrapping a function from `Dynamic` to
`(a, List DecodeError)`. It always produces a value (possibly a placeholder)
plus any errors, so that multiple decoders can run independently and accumulate
all errors rather than stopping at the first failure.

```
opaque type Decoder a = Decoder(Dynamic -> (a, List DecodeError))

pub type DecodeError =
  | DecodeError(expected: String, found: String, path: List String)
```

You build decoders by composing smaller ones, then call `run` to execute:

```
pub fun run : Dynamic -> Decoder a -> Result a (List DecodeError)
```

### Primitive decoders

```
pub fun int : Decoder Int
pub fun float : Decoder Float
pub fun string : Decoder String
pub fun bool : Decoder Bool
pub fun dynamic : Decoder Dynamic     # always succeeds, returns the value as-is
```

### Structural decoders

```
# Decode a field from a map/dict, then continue building a larger decoder
pub fun field : String -> Decoder a -> (a -> Decoder b) -> Decoder b

# Positional access into tuples or lists (0-indexed)
pub fun element : Int -> Decoder a -> (a -> Decoder b) -> Decoder b

# Decode a list where every element matches a decoder
pub fun list : Decoder a -> Decoder (List a)

# Decode a Maybe — handles nil/undefined/none as Nothing
pub fun optional : Decoder a -> Decoder (Maybe a)
```

### Building record decoders

`field` and `element` are continuation-passing: they decode one piece, then
thread the result into a function that returns the next decoder. The final
step calls `success` to wrap the finished value:

```
fun user_decoder : Decoder User
user_decoder = {
  field "name" string (fun name ->
  field "age" int (fun age ->
  success (User { name, age })))
}

# Run it
let result = run raw_data user_decoder
# result : Result User (List DecodeError)
```

If "name" is missing and "age" is the wrong type, you get both errors back —
every field runs regardless of earlier failures.

For positional data (database rows as tuples):

```
fun row_decoder : Decoder User
row_decoder = {
  element 0 string (fun name ->
  element 1 int (fun age ->
  success (User { name, age })))
}
```

### Additional combinators

```
# Finish a decoder with a value
pub fun success : a -> Decoder a

# A decoder that always fails
pub fun failure : a -> String -> Decoder a

# Transform a decoded value
pub fun map : Decoder a -> (a -> b) -> Decoder b

# Try multiple decoders, use the first that succeeds
pub fun one_of : Decoder a -> List (Decoder a) -> Decoder a

# Decode then decide what to decode next (for tagged unions, enums, etc.)
pub fun then : Decoder a -> (a -> Decoder b) -> Decoder b

# Nested path access: field within field within field
pub fun at : List String -> Decoder a -> Decoder a

# Wrap any value as Dynamic
pub fun from_erlang : a -> Dynamic

# Classify a Dynamic value (returns "Int", "String", "List", etc.)
pub fun classify : Dynamic -> String
```

### Tagged unions / enum decoding

`then` enables decoding tagged unions by first extracting a tag, then choosing
the appropriate decoder:

```
fun shape_decoder : Decoder Shape
shape_decoder =
  then (at ["type"] string) (fun tag ->
    case tag {
      "circle" ->
        field "radius" float (fun r ->
        success (Circle r))
      "rect" ->
        field "width" float (fun w ->
        field "height" float (fun h ->
        success (Rect w h)))
      _ -> failure Point "Shape"
    })
```

## Why pure, not an effect

Decoding is a type check on a value — it either matches or it doesn't. Error
accumulation is built into the `Decoder` type itself (every decoder runs and
collects errors). The `Validate` effect can layer on top for domain validation
("is this Int above 18?") but isn't needed for structural decoding.

The two layers compose cleanly:

- **Decoder**: "is this BEAM term an Int?" → accumulated structural errors
- **Validate**: "is this Int above 18?" → domain validation via effect

## Usage

### Wrapping an Erlang library

A library author wrapping pgo would use Dynamic/Decoder internally and expose
a typed API. The application developer never sees Dynamic:

```
# Inside the Postgres wrapper library (internal module)

@external("erlang", "pgo", "query")
fun raw_query : String -> List Dynamic -> Dynamic

# Library author defines a decoder
fun user_row : Decoder User
user_row = {
  element 0 string (fun name ->
  element 1 int (fun age ->
  success (User { name, age })))
}

# Exposed public API — typed, no Dynamic visible
pub fun get_user : Int -> Result User DbError needs {Database}
get_user id = {
  let result = raw_query "SELECT name, age FROM users WHERE id = $1" [from_erlang id]
  run result user_row |> Result.map_error to_db_error
}
```

## Use cases

- **Erlang/Elixir library interop**: return values from FFI calls
- **ETS**: untyped term storage
- **Process messages from non-dylang processes**: unknown message shapes
- **Database drivers**: rows as Erlang tuples/lists
- **JSON/msgpack/ETF**: after initial parse, walk the resulting BEAM terms

## Implementation

The Erlang FFI is minimal — a single bridge file with ~10 functions:

- `classify` → `is_integer/1`, `is_binary/1`, etc. guards → type name string
- `decode_int` → `is_integer/1` guard, return `{ok, V}` or `{error, 0}`
- `decode_float` → `is_float/1` guard, return `{ok, V}` or `{error, 0.0}`
- `decode_string` → `is_binary/1` guard, return `{ok, V}` or `{error, <<>>}`
- `decode_bool` → handled in pure dylang (compare against `true`/`false` atoms)
- `index` → handles maps (`maps:get`), tuples (`element/2`), lists (head matches for first N elements). 0-indexed in dylang, converted to 1-indexed for Erlang. Returns `{ok, {some, V}}`, `{ok, none}`, or `{error, Kind}`.
- `decode_list` → `is_list/1` guard, iterates calling the inner decoder on each element
- `decode_dict` → `is_map/1` guard
- `is_null` → checks `nil`, `null`, `undefined`
- `identity` → wraps any term (used by `from_erlang` and constructors like `Dynamic.int`)

Everything else — `field`, `element`, `success`, `map`, `one_of`, `then`,
`optional`, `at`, `run` — is pure dylang composing these primitives.

No special compiler support needed.
