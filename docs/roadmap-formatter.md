# Formatter Roadmap

Tracks formatting rules that need proper group/break behavior. Most braced-body constructs (case, block, handler, effect, trait, impl, record def) already work since they always break to multi-line. This list covers constructs that need "try one line, break if too wide" logic.

## Line-break rules

- [ ] **Fun bindings** — `name params = body` should break after `=` and indent body when too long
- [ ] **Fun signatures** — `fun name : A -> B -> C needs {E}` break on arrows or after `:`
- [ ] **`with` expressions** — break handler side first (into braced block), then expression side
- [ ] **Application** — `func arg1 arg2 arg3` break arguments when too long
- [ ] **Binary operators** — `a + b * c + d` break before operator when too long
- [ ] **Record create/update** — `Name { field: val, field: val }` break to multi-line fields
- [ ] **Lists** — `[a, b, c, d]` break to multi-line elements
- [ ] **Tuples** — `(a, b, c)` break to multi-line elements
- [ ] **Lambda** — `fun x y -> body` break before body
- [ ] **Import exposing** — `import Foo (a, b, c, d, e)` break the exposed list
- [ ] **Type expressions** — `Map String (List (Option Int))` break complex nested types

## Normalization

- [ ] **Blank lines** — collapse multiple consecutive blank lines to one
- [ ] **Trailing whitespace** — already handled by the Doc pretty-printer
- [ ] **EOF newline** — already handled

## Infrastructure

- [x] Wadler-Lindig Doc algebra with Nest/Group
- [x] Token-level trivia attachment
- [x] Trailing trivia splitting (blank line = paragraph break)
- [x] Source-preserving numeric literals
- [x] `--debug` flag for AST dump
- [x] `--width` flag / `project.toml [formatter]` config
- [ ] Idempotency test (format twice, output matches)
- [ ] Formatter test suite on stdlib files
- [ ] Round-trip test: format then parse, AST matches
