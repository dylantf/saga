-module(std_dict_bridge).
-export([new/0, get/2]).

new() ->
    #{}.

get(Key, Dict) ->
    case maps:find(Key, Dict) of
        {ok, V} -> V;
        error -> undefined
    end.
