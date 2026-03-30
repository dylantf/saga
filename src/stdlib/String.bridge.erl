-module(std_string_bridge).
-export([find/2, strip_prefix/2, contains/2, starts_with/2, ends_with/2, split/2, replace/3, replace_all/3, join/2, graphemes/1, slice/3,
         is_alpha/1, is_digit/1, is_alphanumeric/1, is_upper/1, is_lower/1, is_whitespace/1, reverse/1]).

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

reverse(S) ->
    unicode:characters_to_binary(string:reverse(S)).

graphemes(String) ->
    graphemes(String, []).

graphemes(String, Acc) ->
    case string:next_grapheme(String) of
        [Next | Rest] ->
            graphemes(Rest, [unicode:characters_to_binary([Next]) | Acc]);
        _ ->
            lists:reverse(Acc)
    end.

is_alpha(<<>>) -> false;
is_alpha(S) -> check_all(S, fun(C) -> (C >= $A andalso C =< $Z) orelse (C >= $a andalso C =< $z) end).

is_digit(<<>>) -> false;
is_digit(S) -> check_all(S, fun(C) -> C >= $0 andalso C =< $9 end).

is_alphanumeric(<<>>) -> false;
is_alphanumeric(S) -> check_all(S, fun(C) -> (C >= $A andalso C =< $Z) orelse (C >= $a andalso C =< $z) orelse (C >= $0 andalso C =< $9) end).

is_upper(<<>>) -> false;
is_upper(S) -> check_all(S, fun(C) -> C >= $A andalso C =< $Z end).

is_lower(<<>>) -> false;
is_lower(S) -> check_all(S, fun(C) -> C >= $a andalso C =< $z end).

is_whitespace(<<>>) -> false;
is_whitespace(S) -> check_all(S, fun(C) -> C =:= $\s orelse C =:= $\t orelse C =:= $\n orelse C =:= $\r end).

check_all(<<>>, _Fun) -> true;
check_all(<<C/utf8, Rest/binary>>, Fun) ->
    case Fun(C) of
        true -> check_all(Rest, Fun);
        false -> false
    end.
