# Significant-whitespace syntax examples

These are runnable conversions of ten files from `examples/`. They illustrate
Saga's indentation-based expression and declaration blocks while retaining
braces for structural syntax.

Converted examples:

| Existing example | Layout conversion | Main syntax exercised |
| --- | --- | --- |
| [`04-fizzbuzz.saga`](../../examples/04-fizzbuzz.saga) | [`04-fizzbuzz.saga`](./04-fizzbuzz.saga) | Multiline `if` and sequencing |
| [`08-bst.saga`](../../examples/08-bst.saga) | [`08-bst.saga`](./08-bst.saga) | Nested `case` and `if` |
| [`10-log-effect.saga`](../../examples/10-log-effect.saga) | [`10-log-effect.saga`](./10-log-effect.saga) | Effectful handler-arm body |
| [`14-fail-to-result.saga`](../../examples/14-fail-to-result.saga) | [`14-fail-to-result.saga`](./14-fail-to-result.saga) | Inline handler, nested lambdas, pipelines |
| [`16-traits.saga`](../../examples/16-traits.saga) | [`16-traits.saga`](./16-traits.saga) | Retained structural braces and postfix `with` |
| [`21-do-else.saga`](../../examples/21-do-else.saga) | [`21-do-else.saga`](./21-do-else.saga) | `do...else` and `case` |
| [`42-dijkstra.saga`](../../examples/42-dijkstra.saga) | [`42-dijkstra.saga`](./42-dijkstra.saga) | Deeply nested control flow and handler use |
| [`48-bitstring.saga`](../../examples/48-bitstring.saga) | [`48-bitstring.saga`](./48-bitstring.saga) | Multiline case arms and delimiter-heavy patterns |
| [`54-choose-backtracking.saga`](../../examples/54-choose-backtracking.saga) | [`54-choose-backtracking.saga`](./54-choose-backtracking.saga) | Whole-body postfix handler |
| [`58-streams.saga`](../../examples/58-streams.saga) | [`58-streams.saga`](./58-streams.saga) | Pipeline continuation layout |

## Layout rules

- A newline and increased indentation after `=`, `->`, `then`, `else`, `do`,
  or inline `with` opens an expression block.
- An `effect`, `handler`, `trait`, or `impl` header opens an indented member
  list. These declarations no longer use braces.
- Logical lines at the same indentation are sequential expressions. The last
  expression is the block's value.
- `case subject of` is followed by an indented list of arms. The `of` keyword
  explicitly introduces the arm list; no `:` marker is used.
- A multiline case arm is indented beneath its `->`.
- `do` and `else` each introduce an indented block.
- A line-leading `|>` aligns with the expression it continues. At that same
  layout indentation it suppresses the virtual separator that would otherwise
  begin a new sequential expression.
- A postfix named-handler clause that handles an entire function body is
  aligned with the function definition's head:

  ```saga
  computation x =
    first_step x
    second_step ()
  with handler_name
  ```

  The aligned `with` applies to the completed function body.
- Blank lines and comments do not affect layout.

## Braces deliberately retained

- Record declarations, construction, update, and patterns
- Effect rows such as `needs {Fail}`
- Trait constraints such as `where {a: Show}`
- String interpolation

Declaration members now use the same layout principle as expression blocks;
braces are reserved for structural values, rows, and constraints.
