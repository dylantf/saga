-module(std_evidence_bridge).
-export([find_evidence/2, insert_canonical/2, project_evidence/2]).

%% Evidence vector layout: a tuple of {EffectTag, OpTuple} entries sorted
%% canonically (alphabetically) by EffectTag. Within each OpTuple, op
%% closures are sorted alphabetically by op name. The outer tuple is
%% typically <= 5 entries, so linear walks are fine.

%% Look up the OpTuple for a given effect tag. Used on open-row paths;
%% closed-row sites are expected to compute the index statically and use
%% erlang:element/2 directly.
find_evidence(Evidence, Tag) ->
    find_evidence_at(Evidence, Tag, 1, tuple_size(Evidence)).

find_evidence_at(_Evidence, Tag, I, N) when I > N ->
    erlang:error({evidence_tag_not_found, Tag});
find_evidence_at(Evidence, Tag, I, N) ->
    case element(I, Evidence) of
        {Tag, OpTuple} -> OpTuple;
        _ -> find_evidence_at(Evidence, Tag, I + 1, N)
    end.

%% Insert a new {Tag, OpTuple} entry at its canonical position. If an entry
%% with the same tag already exists, replace it (innermost-wins semantics
%% for nested `with` blocks).
insert_canonical(Evidence, {NewTag, _NewOps} = NewEntry) ->
    insert_at(tuple_to_list(Evidence), NewTag, NewEntry, []).

insert_at([], _NewTag, NewEntry, Acc) ->
    list_to_tuple(lists:reverse([NewEntry | Acc]));
insert_at([{Tag, _} | Rest], NewTag, NewEntry, Acc) when Tag =:= NewTag ->
    list_to_tuple(lists:reverse([NewEntry | Acc]) ++ Rest);
insert_at([{Tag, _} = Old | Rest], NewTag, NewEntry, Acc) when Tag < NewTag ->
    insert_at(Rest, NewTag, NewEntry, [Old | Acc]);
insert_at([{Tag, _} = Old | Rest], NewTag, NewEntry, Acc) when Tag > NewTag ->
    list_to_tuple(lists:reverse([NewEntry | Acc]) ++ [Old | Rest]).

%% Build a new evidence tuple containing only the named tags, in the order
%% supplied (the caller is expected to pass them in canonical order).
project_evidence(Evidence, Tags) ->
    list_to_tuple([entry_for(Evidence, T) || T <- Tags]).

entry_for(Evidence, Tag) ->
    entry_at(Evidence, Tag, 1, tuple_size(Evidence)).

entry_at(_Evidence, Tag, I, N) when I > N ->
    erlang:error({evidence_tag_not_found, Tag});
entry_at(Evidence, Tag, I, N) ->
    case element(I, Evidence) of
        {Tag, _} = Entry -> Entry;
        _ -> entry_at(Evidence, Tag, I + 1, N)
    end.
