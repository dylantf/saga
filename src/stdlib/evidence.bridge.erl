-module(std_evidence_bridge).
-export([find_evidence/2, insert_canonical/2, insert_static/3,
         select_evidence/2, reframe_evidence/3,
         append_tail/3,
         lift_evidence/1, bind/2, mbind/2, run/1]).

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
%% original perform site. Take the entries for NamedTags from the call-time
%% frame and every other entry from the captured perform-site frame. Nothing
%% else in the call-time frame is kept: a handler of an effect in `..r` that
%% happens to surround the handler arm must not shadow the perform site's.
%% A named effect the call-time frame lacks (one provided natively, such as
%% `Actor` under `spawn`) falls back to the captured entry if there is one.
%% The result is only ever read by tag.
append_tail(CallEvidence, CapturedEvidence, NamedTags) ->
    Named = [Entry || {Tag, _} = Entry <- tuple_to_list(CallEvidence),
                      lists:member(Tag, NamedTags)],
    Supplied = [Tag || {Tag, _} <- Named],
    Tail = [Entry || {Tag, _} = Entry <- tuple_to_list(CapturedEvidence),
                     not lists:member(Tag, Supplied)],
    list_to_tuple(Named ++ Tail).

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


%% ---------------------------------------------------------------------------
%% The continuation of a `with` (see docs/effect-implementation.md).
%%
%% Inside a `with`, CPS code returns a plain value or a suspension
%% {'$saga_meta', M}: an operation handled further out was performed, and M
%% takes the meta continuation, everything that happens once the handled
%% computation has a value (the code after `resume` in the arms that resumed,
%% then the code after the `with`).

%% The frame a `with` inherits, with every operation suspending instead of
%% calling its handler. Tags and positions are unchanged. This is the only
%% function that knows the frame's representation.
lift_evidence(Evidence) ->
    list_to_tuple([{Tag, list_to_tuple([lift_op(Op) || Op <- tuple_to_list(Ops)])}
                   || {Tag, Ops} <- tuple_to_list(Evidence)]).

%% An operation closure takes its arguments and then the continuation. Once
%% the meta continuation is known, the handler gets a continuation that runs
%% the rest of the handled computation and then the meta continuation.
%%
%% An operation given a callback (a tagged closure) is not suspended: its
%% handler's arm runs the callback and then resumes, and the meta continuation
%% current at that resume cannot be passed through the arm's code. It is
%% performed where it stands, as the handled computation would be by `run'.
lift_op(Op) ->
    {arity, N} = erlang:fun_info(Op, arity),
    nary(N, Op, fun(All) ->
        {Args, [K]} = lists:split(N - 1, All),
        case lists:any(fun({'$saga_cps', _}) -> true; (_) -> false end, Args) of
            true -> erlang:apply(Op, All);
            false ->
                {'$saga_meta',
                 fun(Mk) -> erlang:apply(Op, Args ++ [fun(V) -> bind(K(V), Mk) end]) end}
        end
    end).

%% A fun of N arguments that passes them to Body as a list. An operation of
%% more arguments is left as it is.
nary(1, _, Body) -> fun(A) -> Body([A]) end;
nary(2, _, Body) -> fun(A, B) -> Body([A, B]) end;
nary(3, _, Body) -> fun(A, B, C) -> Body([A, B, C]) end;
nary(4, _, Body) -> fun(A, B, C, D) -> Body([A, B, C, D]) end;
nary(5, _, Body) -> fun(A, B, C, D, E) -> Body([A, B, C, D, E]) end;
nary(6, _, Body) -> fun(A, B, C, D, E, F) -> Body([A, B, C, D, E, F]) end;
nary(7, _, Body) -> fun(A, B, C, D, E, F, G) -> Body([A, B, C, D, E, F, G]) end;
nary(8, _, Body) -> fun(A, B, C, D, E, F, G, H) -> Body([A, B, C, D, E, F, G, H]) end;
nary(_, Op, _) -> Op.

%% The value of a handled computation goes to the continuation of its `with`.
bind({'$saga_meta', M}, Mk) -> M(Mk);
bind(Value, Mk) -> Mk(Value).

%% `let r = resume x; F(r)' in a handler arm: F runs on the value of the
%% handled computation, before the continuation of the `with'.
mbind({'$saga_meta', M}, F) ->
    {'$saga_meta', fun(Mk) -> M(fun(Value) -> bind(F(Value), Mk) end) end};
mbind(Value, F) -> F(Value).

%% `bind' with the identity continuation, where the caller is not CPS code
%% and needs a plain value. A handler further out that aborts returns here.
run({'$saga_meta', M}) -> run(M(fun(Value) -> Value end));
run(Value) -> Value.
