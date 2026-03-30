-module(std_float_bridge).
-export([parse/1, to_string/1]).

parse(S) ->
    case string:to_float(S) of
        {F, []} -> F;
        _ -> undefined
    end.

to_string(X) ->
    float_to_binary(X, [short]).
