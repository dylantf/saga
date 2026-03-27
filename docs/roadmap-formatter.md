# Formatter Roadmap

Tracks formatting rules that need proper group/break behavior. Most braced-body constructs (case, block, handler, effect, trait, impl, record def) already work since they always break to multi-line. This list covers constructs that need "try one line, break if too wide" logic.

## Line-break rules

- [x] **Fun bindings** — break after `=` and indent body; block-like bodies (`{`, `case`, `do`, `receive`, inline `with`) stay on `=` line
- [x] **Fun signatures** — break `needs`/`where` clauses first (from end), then arrows
- [x] **`with` expressions** — inline handler `{` stays on line; named handler breaks before `with`
- [x] **Application** — apps never break across lines (newlines terminate application parsing); trailing lambda args with block bodies stay compact
- [x] **Binary operators** — flatten same-operator chains, break before operator
- [x] **Record create/update** — `{ }` with comma-separated fields; trailing comma in broken mode via `IfBreak`
- [x] **Lists** — `[ ]` comma-separated, same break pattern as records
- [x] **Tuples** — `( )` comma-separated, same break pattern
- [x] **Lambda** — `fun params ->` break before body, like `=` in bindings
- [x] **Import exposing** — `(item1, item2, ...)` breaks the exposed list
- [x] **Type expressions** — can't break across lines (same constraint as application); types stay on one line

## Normalization

- [x] **Import sorting** — `Std.*` first (sorted), then everything else (sorted)
- [x] **Blank lines** — collapse multiple consecutive blank lines to one
- [x] **Trailing whitespace** — handled by Doc pretty-printer
- [x] **EOF newline** — handled

## Infrastructure

- [x] Wadler-Lindig Doc algebra with Nest/Group/IfBreak
- [x] Token-level trivia attachment
- [x] Trailing trivia splitting (blank line = paragraph break)
- [x] Source-preserving numeric literals (`Lit::Int(String, i64)`, `Lit::Float(String, f64)`)
- [x] `--debug` flag for AST dump
- [x] `--width` flag / `project.toml [formatter]` config
- [x] Idempotency test (format twice, output matches)
- [x] Formatter test suite (58 tests)
- [x] Round-trip test on examples + stdlib: format, re-parse, normalized AST matches
- [x] Idempotency + re-format checks on all .dy files
