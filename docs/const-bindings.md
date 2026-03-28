# Const Bindings

## Summary

Add `const` declarations for named, compile-time constant values at the module level.

## Motivation

Currently, defining a simple named constant requires a `Unit ->` function:

```
fun pi : Unit -> Float
pi () = 3.14159

fun max_retries : Unit -> Int
max_retries () = 5
```

This is ceremonial — `pi` isn't a computation, it's a value. AI agents and new users frequently try to write zero-argument functions, which don't exist in the language. `const` provides the right tool for this.

### Why not parameterless functions?

A parameterless function in a strict language is just a value — but on BEAM, there's no "evaluate once at module load" mechanism. A zero-arity function would either:
- Re-evaluate its body on every reference (pointless for constants, confusing for effectful expressions)
- Require a caching mechanism (ETS, persistent_term, process dictionary) with initialization ordering concerns

### Why not top-level `let`?

- Can't be `pub` — public declarations require type signatures for documentation, and `let` bindings don't have them
- Computed `let` expressions would need module-load evaluation, which BEAM doesn't support natively
- Allowing lambdas in top-level `let` would create a second syntax for defining functions

### Why `const`?

- Type is self-evident from the literal — no signature needed
- `pub const` reads naturally and doesn't violate the "public things have signatures" rule, since the value *is* the documentation
- Compiles away entirely via inlining — no runtime cost, no BEAM impedance mismatch
- Small implementation surface

## Design

### Syntax

```
# Private const
const pi = 3.14159
const max_retries = 5
const app_name = "dylang"

# Public const
pub const default_port = 8080
pub const version = "0.1.0"
```

### Allowed expressions

Const values must be compile-time evaluable:

- Literal values: `Int`, `Float`, `String`, `Bool`
- Tuples/lists of const values: `const origins = ["localhost", "example.com"]`
- References to other consts: `const tau = 6.28318` (not `2.0 * pi` unless we add const folding)
- Record literals with const fields (if useful): `const default_config = { port: 8080, debug: False }`

Explicitly **not** allowed:
- Function calls (no `const x = List.map f xs`)
- Lambdas (use `fun` for functions)
- Effect operations
- References to functions

This can be relaxed later (const folding for arithmetic, string concatenation) but starting restrictive is safer.

### Type inference

The type is inferred from the literal. No annotation syntax — if the value needs a type signature, it should be a function.

### Compilation

Constants are inlined at every use site during lowering. No Core Erlang function is emitted for a `const`. The constant simply disappears from the output, replaced by its literal value everywhere it's referenced.

### Module exports

`pub const` values are visible to importing modules. Since they're inlined at compile time, the importing module gets a copy of the literal — no runtime dependency on the defining module.

### Interaction with existing features

- `const` is **not** a function and cannot be called with arguments
- `const` cannot appear inside function bodies (use `let` for local bindings)
- Pattern matching: const names cannot be used as patterns (they're not constructors)

## Implementation

### Parser

- New `Decl::Const` AST variant: `{ name, value: Expr, public: bool }`
- Parse `[pub] const <name> = <expr>` at the declaration level
- `const` becomes a reserved keyword

### Typechecker

- Infer the type of the expression
- Verify the expression is const-evaluable (literal check, reject function calls/effects/lambdas)
- Register the const in the type environment so other declarations can reference its type

### Codegen

- During lowering, replace every reference to a const name with its literal value
- Emit nothing for the const declaration itself

### Estimated scope

Small. A new AST variant, a validation pass in the typechecker, and a substitution step in lowering. No changes to the Core Erlang emitter, effect system, or trait system.

## Future extensions

- **Const folding**: Allow arithmetic and string operations on const values (`const tau = 2.0 * pi`)
- **Const in patterns**: Use const names in match arms as literal patterns
- **Const generic parameters**: Type-level constants (far future, if ever)
