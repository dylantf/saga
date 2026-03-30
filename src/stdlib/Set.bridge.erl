-module(std_set_bridge).
-export([new/0, from_list/1, to_list/1, insert/2, remove/2,
         member/2, size/1, union/2, intersection/2, difference/2,
         is_subset/2, map/2, filter/2, fold/3]).

new() ->
    sets:new([{version, 2}]).

from_list(List) ->
    sets:from_list(List, [{version, 2}]).

to_list(Set) ->
    sets:to_list(Set).

insert(Elem, Set) ->
    sets:add_element(Elem, Set).

remove(Elem, Set) ->
    sets:del_element(Elem, Set).

member(Elem, Set) ->
    sets:is_element(Elem, Set).

size(Set) ->
    sets:size(Set).

union(A, B) ->
    sets:union(A, B).

intersection(A, B) ->
    sets:intersection(A, B).

difference(A, B) ->
    sets:subtract(A, B).

is_subset(Sub, Super) ->
    sets:is_subset(Sub, Super).

map(Fun, Set) ->
    sets:map(Fun, Set).

filter(Fun, Set) ->
    sets:filter(Fun, Set).

fold(Fun, Init, Set) ->
    sets:fold(fun(Elem, Acc) -> Fun(Acc, Elem) end, Init, Set).
