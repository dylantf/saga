-module(std_evidence_bridge).
-export([find_evidence/2, insert_canonical/2, insert_static/3,
         project_evidence/2, reframe_evidence/3, append_tail/3]).

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
        not_found -> find_unique_family_evidence(Evidence, Tag)
    end.

find_evidence_at(_Evidence, _Tag, I, N) when I > N -> not_found;
find_evidence_at(Evidence, Tag, I, N) ->
    case element(I, Evidence) of
        {Tag, OpTuple} -> {ok, OpTuple};
        _ -> find_evidence_at(Evidence, Tag, I + 1, N)
    end.

%% A handler installed inside code polymorphic in an effect argument cannot
%% mint the caller's concrete applied tag: there is deliberately no runtime
%% type witness.  Such slots are still safe to use when their effect family is
%% unique in the frame.  Exact applied tags always win; multiple family
%% matches remain an error rather than choosing by order.
find_unique_family_evidence(Evidence, Tag) ->
    Family = effect_family(Tag),
    Matches = [Ops || I <- lists:seq(1, tuple_size(Evidence)),
                       {EntryTag, Ops} <- [element(I, Evidence)],
                       effect_family(EntryTag) =:= Family],
    case Matches of
        [OpTuple] -> OpTuple;
        [] -> erlang:error({evidence_tag_not_found, Tag});
        _ -> erlang:error({ambiguous_evidence_family, Family})
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

%% Build a new evidence tuple containing only the named tags, in the order
%% supplied (the caller is expected to pass them in canonical order).
project_evidence(Evidence, Tags) ->
    list_to_tuple([entry_for(Evidence, T) || T <- Tags]).

%% Build a callee-shaped open-row vector. Selectors identify the callee's
%% positional static prefix: integers address the caller's own static prefix,
%% while atoms select a concrete applied tag from the forwarded remainder.
%% Every unselected caller entry follows as the callee's tagged open tail.
reframe_evidence(Evidence, _StaticCount, Selectors) ->
    SelectedPositions = unique_positions(
        [selector_position(Evidence, S) || S <- Selectors]),
    Selected = [selected_entry(Evidence, Selector,
                               selector_position(Evidence, Selector))
                || Selector <- Selectors],
    Remaining = [element(I, Evidence)
                 || I <- lists:seq(1, tuple_size(Evidence)),
                    not lists:member(I, SelectedPositions)],
    list_to_tuple(Selected ++ Remaining).

%% An effect-operation callback with an open row receives its named effects
%% from the handler that invokes it, while the unknown row tail comes from the
%% original perform site. Keep the call-time frame as the static prefix and
%% append captured entries it does not already replace. Exact duplicates are
%% removed with call-time evidence winning; distinct applications of one family
%% remain independent. The callback's concrete named effects therefore come
%% from the nested handler while its `..r` effects survive from the perform site.
append_tail(CallEvidence, CapturedEvidence, StaticTags) ->
    CallEntries = tuple_to_list(CallEvidence),
    {StaticPrefix, CallTail} = lists:split(length(StaticTags), CallEntries),
    SpecializedPrefix = [{Tag, Ops}
                         || {Tag, {_OldTag, Ops}}
                                <- lists:zip(StaticTags, StaticPrefix)],
    SpecializedCall = SpecializedPrefix ++ CallTail,
    CallTags = [Tag || {Tag, _} <- SpecializedCall],
    ExtraTail = [Entry || {Tag, _} = Entry <- tuple_to_list(CapturedEvidence),
                          not lists:member(Tag, CallTags)],
    list_to_tuple(SpecializedCall ++ ExtraTail).

unique_positions(Positions) -> unique_positions(Positions, []).

unique_positions([], Acc) -> lists:reverse(Acc);
unique_positions([Position | Rest], Acc) ->
    case lists:member(Position, Acc) of
        true -> unique_positions(Rest, Acc);
        false -> unique_positions(Rest, [Position | Acc])
    end.

selector_position(Evidence, I) when is_integer(I), I >= 1,
                                      I =< tuple_size(Evidence) -> I;
selector_position(Evidence, {I, _Tag}) when is_integer(I), I >= 1,
                                               I =< tuple_size(Evidence) -> I;
selector_position(Evidence, Tag) when is_atom(Tag) ->
    case entry_position(Evidence, Tag, 1, tuple_size(Evidence)) of
        {ok, Position} -> Position;
        not_found -> unique_family_position(Evidence, Tag)
    end.

%% Atom selectors carry the callee's requested identity, so selecting a
%% unique polymorphic family also specializes the entry's runtime tag.
selected_entry(Evidence, {_Position, Tag}, Position) when is_atom(Tag) ->
    {_OldTag, Ops} = element(Position, Evidence),
    {Tag, Ops};
selected_entry(Evidence, Selector, Position) when is_atom(Selector) ->
    {_OldTag, Ops} = element(Position, Evidence),
    {Selector, Ops};
selected_entry(Evidence, _Selector, Position) ->
    element(Position, Evidence).

entry_position(_Evidence, _Tag, I, N) when I > N -> not_found;
entry_position(Evidence, Tag, I, N) ->
    case element(I, Evidence) of
        {Tag, _} -> {ok, I};
        _ -> entry_position(Evidence, Tag, I + 1, N)
    end.

unique_family_position(Evidence, Tag) ->
    Family = effect_family(Tag),
    Matches = [I || I <- lists:seq(1, tuple_size(Evidence)),
                    {EntryTag, _} <- [element(I, Evidence)],
                    effect_family(EntryTag) =:= Family],
    case Matches of
        [Position] -> Position;
        [] -> erlang:error({evidence_tag_not_found, Tag});
        _ -> erlang:error({ambiguous_evidence_family, Family})
    end.

effect_family(Tag) ->
    [Family | _] = binary:split(atom_to_binary(Tag, utf8), <<"<">>),
    Family.

entry_for(Evidence, Tag) ->
    case entry_at(Evidence, Tag, 1, tuple_size(Evidence)) of
        {ok, Ops} -> {Tag, Ops};
        not_found ->
            Position = unique_family_position(Evidence, Tag),
            {_OldTag, Ops} = element(Position, Evidence),
            {Tag, Ops}
    end.

entry_at(_Evidence, _Tag, I, N) when I > N -> not_found;
entry_at(Evidence, Tag, I, N) ->
    case element(I, Evidence) of
        {Tag, Ops} -> {ok, Ops};
        _ -> entry_at(Evidence, Tag, I + 1, N)
    end.
