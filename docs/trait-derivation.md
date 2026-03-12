# Trait Derivation Implementation Guide

## Syntax

```
type Color { Red | Green | Blue } deriving {Show, Eq}

type Maybe a { Some(a) | None } deriving {Show}
```

`deriving {Trait1, Trait2}` appears after the closing `}` of a type definition.

## Existing infrastructure

### What the typechecker already tracks

- `checker.adt_variants: HashMap<String, Vec<(String, usize)>>` -- type name to list of (constructor_name, arity) pairs. Gives us the structure of every ADT.
- `checker.constructors: HashMap<String, Scheme>` -- constructor name to full type scheme. From this we can extract the field types for each constructor arg.
- The elaboration pass (`elaborate.rs`) already receives the full `Checker` and generates Show method bodies for built-in types in `builtin_show_methods`.

### What the elaboration pass already does

`builtin_show_methods` has hardcoded cases for Bool, Maybe, Result, List, etc. that generate case expressions matching each constructor. For example, the Maybe case generates:

```
fun x -> case x {
  None -> "None"
  Some(v) -> "Some(" <> show v <> ")"
}
```

This is exactly the pattern we need to generalize.

## Implementation steps

### 1. Parser (small, ~20-30 lines)

Add `deriving: Vec<String>` field to the `TypeDef` AST node in `ast.rs`.

In the parser (`parser/decl.rs`), after parsing the closing `}` of a type definition, check for the `deriving` keyword. If present, parse `{ Trait1, Trait2 }` as a comma-separated list of trait names.

### 2. Typechecker (small)

Register the derived trait impls. For `deriving {Show}`, this is equivalent to the user writing:

```
impl Show for Color { ... }
```

The typechecker needs to:
- Register the impl in `trait_impls` (so constraint checking works)
- For parameterized types like `Maybe a`, automatically add where clauses: `impl Show for Maybe a where {a: Show}`

### 3. Elaboration -- Show derivation (medium, ~50-80 new lines, ~200 deleted)

Replace the hardcoded arms in `builtin_show_methods` with a generic function:

```rust
fn derive_show_methods(&self, type_name: &str, checker: &Checker) -> Option<Vec<Expr>> {
    let variants = checker.adt_variants.get(type_name)?;
    let s = Span { start: 0, end: 0 };

    let arms: Vec<CaseArm> = variants.iter().map(|(ctor_name, arity)| {
        if *arity == 0 {
            // Zero-arg: CtorName -> "CtorName"
            CaseArm {
                pattern: Pat::Constructor { name: ctor_name, args: vec![], .. },
                body: Expr::Lit { value: Lit::String(ctor_name.clone()), .. },
                ..
            }
        } else {
            // N-arg: CtorName(a0, a1) -> "CtorName(" <> show a0 <> ", " <> show a1 <> ")"
            let arg_pats = (0..*arity).map(|i| var_pat(format!("__v{i}"))).collect();
            let body = build_show_concat(ctor_name, arity);  // string concat chain
            CaseArm {
                pattern: Pat::Constructor { name: ctor_name, args: arg_pats, .. },
                body,
                ..
            }
        }
    }).collect();

    // Wrap in: fun x -> case x { ...arms }
    Some(vec![lambda("x", Expr::Case { scrutinee: var("x"), arms })])
}
```

For the `show` calls on constructor fields, we need to dispatch through the right dict. For concrete field types (e.g. `Circle(Float)`) we use the known dict. For type-parameter fields (e.g. `Some(a)`) we use the dict param passed to the dict constructor.

### 4. Elaboration -- Eq derivation (possibly unnecessary)

Eq currently uses BEAM's `=:=` BIF, which already does structural comparison on tagged tuples. So `Red == Red` already works at the BEAM level. The question is whether the typechecker allows it. Currently Eq is a built-in trait with impls for `Int`, `Float`, `String`, `Bool`.

Two options:
- Register derived Eq impls in the typechecker so `Color == Color` passes constraint checking, but don't generate any dict methods (BEAM handles it)
- Or generate structural equality methods if we ever move Eq to dictionary dispatch

The first option is minimal: just register the impl, no codegen needed.

## What gets deleted

Once derivation works, the following hardcoded cases in `builtin_show_methods` can be removed:
- `"Bool"` (2 zero-arg constructors)
- `"Maybe"` (None + Some(a))
- `"Result"` (Ok(a) + Err(e))
- `"List"` (Nil + Cons, though list has special `[a, b, c]` formatting)

Primitives (`Int`, `Float`, `String`, `Unit`) stay hardcoded since they use foreign calls, not case expressions.

`"List"` might stay hardcoded too, since its Show formats as `[1, 2, 3]` rather than `Cons(1, Cons(2, Nil))`.

## Net change estimate

- ~20-30 lines: parser
- ~10 lines: typechecker impl registration
- ~50-80 lines: generic derivation in elaboration
- ~-200 lines: deleted hardcoded Show arms for Bool, Maybe, Result
- Net: roughly break-even on line count, but much more extensible

## Open questions

- Should `List` keep its special `[a, b, c]` Show formatting, or should derived Show use `Cons(1, Cons(2, Nil))`? Probably keep the special case.
- Should `Tuple` be derivable? It's already handled inline. Probably leave as-is.
- For `deriving {Eq}` on parameterized types, do we need `where {a: Eq}` constraints, or does BEAM structural equality just work? (It just works, but the typechecker needs to know.)
