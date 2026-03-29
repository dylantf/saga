# High Priority - Very Common Operations

## List (biggest gaps)

- [x] sort / sort_by - Can't sort anything right now. Critical for any real program.
- [x] find - Find first element matching a predicate. Extremely common.
- [x] is_empty - Simple but used constantly.
- [x] last - Get last element.
- [x] nth / at - Access by index.
- [x] contains - Check if element is in list (needs Eq).
- [x] sum / product - Numeric aggregation (needs Num).
- [x] minimum / maximum - Needs Ord.
- [x] unzip - Inverse of zip.
- [x] partition - Split by predicate into two lists.
- [x] unique - Remove duplicates (needs Eq).
- [x] enumerate - Pair elements with their indices.
- [x] concat - Flatten a List (List a) (you have flatten but it's List String -> String).
- [x] zip_with - Zip with a combining function.
- [x] intersperse - Insert separator between elements.

## String

- [ ] replace / replace_all - You have this in Regex but not as plain string operations. Very common need.
- [ ] is_empty
- [ ] join - Join a List String with a separator. Your current List.join returns List String which looks like it intersperses, and List.flatten concatenates strings — but String.join ", " ["a", "b", "c"] producing "a, b, c" is the standard expected API.
- [ ] char_at - Get character at index.

## Maybe

- [ ] is_just / is_nothing - Boolean checks.
- [ ] unwrap - Crash on Nothing (for when you know it's Just). Complements unwrap_or.
- [ ] or_else - Try a fallback Maybe.
- [ ] to_result - Convert Maybe a to Result a e given an error.

## Result

- [ ] is_ok / is_err - Boolean checks.
- [ ] or_else - Try alternative on Err.
- [ ] to_maybe - Drop the error info.
- [ ] flatten - Result (Result a e) e -> Result a e.

## Dict

- [x] map - Transform values.
- [x] filter - Filter entries.
- [x] fold - Fold over entries.
- [x] merge - Combine two dicts.
- [x] is_empty
- [x] update - Update value at key with a function.

# Medium Priority - Missing Modules

## Set

This is a fundamental data structure missing entirely. Erlang has sets and gb_sets you could FFI into. Basic operations:

- [ ] new
- [ ] from_list
- [ ] to_list
- [ ] insert
- [ ] remove
- [ ] member
- [ ] size
- [ ] union
- [ ] intersection
- [ ] difference
- [ ] is_subset
- [ ] is_empty
- [ ] map
- [ ] filter
- [ ] fold

## Char

Character-level operations. Even if strings are UTF-8 binaries on BEAM, having

- [ ] is_alpha
- [ ] is_digit
- [ ] is_upper
- [ ] is_lower
- [ ] to_upper
- [ ] to_lower
- [ ] to_int
- [ ] from_int

## Bitwise

Bit operations on Int:
Erlang has band, bor, bxor, bnot, bsl, bsr.

- [ ] and
- [ ] or
- [ ] xor
- [ ] not
- [ ] shift_left
- [ ] shift_right

# Lower Priority - Nice to Have

- [ ] List.scan - Like fold but returns all intermediate accumulators
- [ ] List.group_by - Group elements by key function (returns Dict k (List a))
- [ ] List.chunks - Split into chunks of size n
- [ ] List.window - Sliding window
- [ ] Float.is_nan / is_infinite
- [ ] Int.to_string / Float.to_string as public (currently private, covered by show)
- [ ] String.to_int / to_float as aliases for Int.parse / Float.parse
