-module(std_list_bridge).
-export([sort_with/2, sort_by/2, nth/2, enumerate/1]).

sort_with(CompareFun, List) ->
    lists:sort(fun(A, B) ->
        case CompareFun(A, B) of
            {std_base_Lt} -> true;
            {std_base_Eq} -> true;
            {std_base_Gt} -> false
        end
    end, List).

sort_by(KeyFun, List) ->
    lists:sort(fun(A, B) -> KeyFun(A) =< KeyFun(B) end, List).

nth(N, List) ->
    try lists:nth(N + 1, List) of
        V -> V
    catch
        _:_ -> undefined
    end.

enumerate(List) ->
    enumerate(List, 0).

enumerate([], _N) ->
    [];
enumerate([H | T], N) ->
    [{N, H} | enumerate(T, N + 1)].
