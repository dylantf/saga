-module(std_int_bridge).
-export([parse/1]).

parse(S) ->
    case string:to_integer(S) of
        {N, []} -> N;
        _ -> undefined
    end.
