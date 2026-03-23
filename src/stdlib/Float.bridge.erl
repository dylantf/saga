-module(std_float_bridge).
-export([parse/1]).

parse(S) ->
    case string:to_float(S) of
        {F, []} -> F;
        _ -> undefined
    end.
