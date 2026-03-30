-module(std_string_bridge).
-export([find/2, strip_prefix/2, contains/2, starts_with/2, ends_with/2, split/2, replace/3, replace_all/3, join/2, graphemes/1, slice/3]).

find(Sub, S) ->
    case string:find(S, Sub) of
        nomatch -> {nothing};
        V -> {just, V}
    end.

strip_prefix(Prefix, S) ->
    case string:prefix(S, Prefix) of
        nomatch -> {nothing};
        V -> {just, V}
    end.

contains(Sub, S) ->
    case string:find(S, Sub) of
        nomatch -> false;
        _ -> true
    end.

starts_with(Prefix, S) ->
    case string:prefix(S, Prefix) of
        nomatch -> false;
        _ -> true
    end.

ends_with(Suffix, S) ->
    case string:prefix(string:reverse(S), string:reverse(Suffix)) of
        nomatch -> false;
        _ -> true
    end.

split(Sep, S) ->
    string:split(S, Sep, all).

replace(Pattern, Replacement, S) ->
    iolist_to_binary(string:replace(S, Pattern, Replacement)).

replace_all(Pattern, Replacement, S) ->
    iolist_to_binary(string:replace(S, Pattern, Replacement, all)).

join(Sep, Parts) ->
    unicode:characters_to_binary(lists:join(Sep, Parts)).

slice(Start, Len, S) ->
    string:slice(S, Start, Len).

graphemes(String) ->
    graphemes(String, []).

graphemes(String, Acc) ->
    case string:next_grapheme(String) of
        [Next | Rest] ->
            graphemes(Rest, [unicode:characters_to_binary([Next]) | Acc]);
        _ ->
            lists:reverse(Acc)
    end.
