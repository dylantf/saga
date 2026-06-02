-module(std_int_bridge).
-export([parse/1, shift_left/2, shift_right/2, to_hex/1, parse_hex/1]).

parse(S) ->
    case string:to_integer(S) of
        {N, <<>>} -> {std_maybe_Just, N};
        {N, []} -> {std_maybe_Just, N};
        _ -> {std_maybe_Nothing}
    end.

shift_left(Bits, N) ->
    N bsl Bits.

shift_right(Bits, N) ->
    N bsr Bits.

to_hex(N) when N < 0 ->
    <<"-", (string:lowercase(integer_to_binary(-N, 16)))/binary>>;
to_hex(N) ->
    string:lowercase(integer_to_binary(N, 16)).

parse_hex(<<"-", Rest/binary>>) ->
    case parse_hex(Rest) of
        {std_maybe_Just, N} -> {std_maybe_Just, -N};
        Nothing -> Nothing
    end;
parse_hex(S) when is_binary(S), byte_size(S) > 0 ->
    try {std_maybe_Just, binary_to_integer(S, 16)}
    catch _:_ -> {std_maybe_Nothing}
    end;
parse_hex(_) -> {std_maybe_Nothing}.
