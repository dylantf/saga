-module(std_array_bridge).
-export([new/0, get/2, map/2, foldl/3]).

new() ->
    array:new().

get(Index, Arr) ->
    case Index >= 0 andalso Index < array:size(Arr) of
        true -> {just, array:get(Index, Arr)};
        false -> {nothing}
    end.

map(Fun, Arr) ->
    array:map(fun(_I, V) -> Fun(V) end, Arr).

foldl(Fun, Acc, Arr) ->
    array:foldl(fun(_I, V, A) -> Fun(A, V) end, Acc, Arr).
