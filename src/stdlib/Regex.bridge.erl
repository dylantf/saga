-module(std_regex_bridge).
-export([match/2, find/2, find_all/2, replace/3, replace_all/3]).

match(Pattern, S) ->
    case re:run(S, Pattern) of
        nomatch -> false;
        _ -> true
    end.

find(Pattern, S) ->
    case re:run(S, Pattern, [{capture, first, list}]) of
        {match, [V]} -> V;
        _ -> undefined
    end.

find_all(Pattern, S) ->
    case re:run(S, Pattern, [global, {capture, first, list}]) of
        {match, Matches} -> lists:map(fun([X]) -> X end, Matches);
        nomatch -> []
    end.

replace(Pattern, S, Replacement) ->
    re:replace(S, Pattern, Replacement, [{return, list}]).

replace_all(Pattern, S, Replacement) ->
    re:replace(S, Pattern, Replacement, [global, {return, list}]).
