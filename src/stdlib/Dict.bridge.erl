-module(std_dict_bridge).
-export([new/0, get/2, map_values/2, filter_entries/2, fold_entries/3, update/3]).

new() ->
    #{}.

get(Key, Dict) ->
    case maps:find(Key, Dict) of
        {ok, V} -> V;
        error -> undefined
    end.

map_values(Fun, Dict) ->
    maps:map(fun(_K, V) -> Fun(V) end, Dict).

filter_entries(Fun, Dict) ->
    maps:filter(fun(K, V) -> Fun(K, V) end, Dict).

fold_entries(Fun, Init, Dict) ->
    maps:fold(fun(K, V, Acc) -> Fun(Acc, K, V) end, Init, Dict).

update(Key, Fun, Dict) ->
    case maps:find(Key, Dict) of
        {ok, V} -> maps:put(Key, Fun(V), Dict);
        error -> Dict
    end.
