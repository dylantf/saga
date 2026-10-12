-module(std_evidence_bridge).
-export([find_evidence/2, insert_canonical/2, insert_static/3,
         select_evidence/2, reframe_evidence/3,
         append_tail/2]).

%% Evidence vector layout: a tuple of {EffectTag, OpTuple} entries sorted
%% canonically (alphabetically) by EffectTag. Within each OpTuple, op
%% closures are sorted alphabetically by op name. The outer tuple is
%% typically <= 5 entries, so linear walks are fine.

%% Look up the OpTuple for a given effect tag. Used on open-row paths;
%% closed-row sites are expected to compute the index statically and use
%% erlang:element/2 directly.
find_evidence(Evidence, Tag) ->
    case find_evidence_at(Evidence, Tag, 1, tuple_size(Evidence)) of
        {ok, OpTuple} -> OpTuple;
        not_found -> erlang:error({evidence_tag_not_found, Tag})
    end.

find_evidence_at(_Evidence, _Tag, I, N) when I > N -> not_found;
find_evidence_at(Evidence, Tag, I, N) ->
    case element(I, Evidence) of
        {Tag, OpTuple} -> {ok, OpTuple};
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

%% Install a handler into an open evidence frame. Only the known positional
%% prefix is canonicalized; globally sorting would move static slots behind
%% unknown tail entries. An exact entry is removed from either part before the
%% replacement is inserted into the prefix.
insert_static(Evidence, StaticCount, {NewTag, _} = NewEntry) ->
    Entries = tuple_to_list(Evidence),
    {Prefix, Tail} = lists:split(StaticCount, Entries),
    CleanPrefix = [Entry || {Tag, _} = Entry <- Prefix, Tag =/= NewTag],
    CleanTail = [Entry || {Tag, _} = Entry <- Tail, Tag =/= NewTag],
    NewPrefix = tuple_to_list(insert_at(CleanPrefix, NewTag, NewEntry, [])),
    list_to_tuple(NewPrefix ++ CleanTail).

%% Build a closed callee frame from positional/tag selectors. Unlike
%% reframe_evidence/3, this deliberately drops every unselected entry. It is
%% used when a closed CPS function value is adapted to an open callback slot:
%% the surrounding HOF's tail belongs to the adapter ABI, not to the closed
%% function it invokes.
select_evidence(Evidence, Selectors) ->
    list_to_tuple([element(selector_position(Evidence, Selector), Evidence)
                   || Selector <- Selectors]).

%% Build a callee-shaped open-row vector. Selectors identify the callee's
%% positional static prefix: integers address the caller's own static prefix,
%% while atoms select an entry by its tag from the forwarded remainder.
%% FramePlan names the source prefix length and the source-static positions
%% that instantiate the target row variable. The already-tagged source tail is
%% always forwarded; omitted declaration-prefix slots are not implicitly
%% leaked into it.
reframe_evidence(Evidence, {StaticCount, ForwardStaticPositions}, Selectors) ->
    Positions = [selector_position(Evidence, S) || S <- Selectors],
    SelectedPositions = unique_positions(Positions),
    Selected = [element(I, Evidence) || I <- Positions],
    ForwardPositions = unique_positions(
        ForwardStaticPositions ++ lists:seq(StaticCount + 1, tuple_size(Evidence))),
    Remaining = [element(I, Evidence)
                 || I <- ForwardPositions,
                    not lists:member(I, SelectedPositions)],
    list_to_tuple(Selected ++ Remaining).

%% An effect-operation callback with an open row receives its named effects
%% from the handler that invokes it, while the unknown row tail comes from the
%% original perform site. Keep the call-time frame, whose static prefix is
%% already in the callback's order, and append the captured entries it does not
%% replace. The callback's named effects therefore come from the nested handler
%% while its `..r` effects survive from the perform site.
append_tail(CallEvidence, CapturedEvidence) ->
    CallEntries = tuple_to_list(CallEvidence),
    CallTags = [Tag || {Tag, _} <- CallEntries],
    ExtraTail = [Entry || {Tag, _} = Entry <- tuple_to_list(CapturedEvidence),
                          not lists:member(Tag, CallTags)],
    list_to_tuple(CallEntries ++ ExtraTail).

unique_positions(Positions) -> unique_positions(Positions, []).

unique_positions([], Acc) -> lists:reverse(Acc);
unique_positions([Position | Rest], Acc) ->
    case lists:member(Position, Acc) of
        true -> unique_positions(Rest, Acc);
        false -> unique_positions(Rest, [Position | Acc])
    end.

selector_position(Evidence, I) when is_integer(I), I >= 1,
                                      I =< tuple_size(Evidence) -> I;
selector_position(Evidence, Tag) when is_atom(Tag) ->
    case entry_position(Evidence, Tag, 1, tuple_size(Evidence)) of
        {ok, Position} -> Position;
        not_found -> erlang:error({evidence_tag_not_found, Tag})
    end.

entry_position(_Evidence, _Tag, I, N) when I > N -> not_found;
entry_position(Evidence, Tag, I, N) ->
    case element(I, Evidence) of
        {Tag, _} -> {ok, I};
        _ -> entry_position(Evidence, Tag, I + 1, N)
    end.
