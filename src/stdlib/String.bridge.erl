-module(std_string_bridge).
-export([find/2, strip_prefix/2, contains/2, starts_with/2, ends_with/2, split/2, replace/3, replace_all/3, join/2, graphemes/1]).

find(S, Sub) ->
    case string:find(S, Sub) of
        nomatch -> undefined;
        V -> V
    end.

strip_prefix(S, Prefix) ->
    case string:prefix(S, Prefix) of
        nomatch -> undefined;
        V -> V
    end.

contains(S, Sub) ->
    case string:find(S, Sub) of
        nomatch -> false;
        _ -> true
    end.

starts_with(S, Prefix) ->
    case string:prefix(S, Prefix) of
        nomatch -> false;
        _ -> true
    end.

ends_with(S, Suffix) ->
    case string:prefix(string:reverse(S), string:reverse(Suffix)) of
        nomatch -> false;
        _ -> true
    end.

split(S, Sep) ->
    string:split(S, Sep, all).

replace(S, Pattern, Replacement) ->
    iolist_to_binary(string:replace(S, Pattern, Replacement)).

replace_all(S, Pattern, Replacement) ->
    iolist_to_binary(string:replace(S, Pattern, Replacement, all)).

join(Sep, Parts) ->
    unicode:characters_to_binary(lists:join(Sep, Parts)).

graphemes(String) ->
    graphemes(String, []).

graphemes(String, Acc) ->
    case string:next_grapheme(String) of
        [Next | Rest] ->
            graphemes(Rest, [unicode:characters_to_binary([Next]) | Acc]);
        _ ->
            lists:reverse(Acc)
    end.
