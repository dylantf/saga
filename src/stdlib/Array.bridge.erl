-module(std_array_bridge).
-export([new/0, get/2, map/2, foldl/3]).

new() ->
    array:new().

get(Index, Arr) ->
    case Index >= 0 andalso Index < array:size(Arr) of
        true -> {std_maybe_Just, array:get(Index, Arr)};
        false -> {std_maybe_Nothing}
    end.

map(Fun, Arr) ->
    array:map(fun(_I, V) -> Fun(V) end, Arr).

foldl(Fun, Acc, Arr) ->
    array:foldl(fun(_I, V, A) -> Fun(A, V) end, Acc, Arr).
