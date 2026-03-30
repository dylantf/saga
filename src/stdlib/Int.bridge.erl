-module(std_int_bridge).
-export([parse/1, shift_left/2, shift_right/2]).

parse(S) ->
    case string:to_integer(S) of
        {N, <<>>} -> {just, N};
        {N, []} -> {just, N};
        _ -> {nothing}
    end.

shift_left(Bits, N) ->
    N bsl Bits.

shift_right(Bits, N) ->
    N bsr Bits.
