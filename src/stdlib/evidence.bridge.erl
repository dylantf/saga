-module(std_evidence_bridge).
-export([find_evidence/2, insert_canonical/2, insert_static/3,
         select_evidence/2, reframe_evidence/3,
         append_tail/3,
         lift_evidence/2, bind/2, mbind/3, run/1,
         abort/3, resume_into/4, fin_resume/4, run_process/1]).

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
%% takes the meta continuation Mk, everything that happens once the handled
%% computation has a value. Mk is the continuation of the `with` (a fun), or a
%% list of frames ending in one:
%%
%%   {k, Ref, F}   the code after a `resume' in an arm of the `with' Ref
%%   {fin, Key}    the end of a `finally' region (its cleanup is stored under
%%                 Key in the process dictionary until it has run)
%%   {held, Keys}  regions that a suspension carried out of themselves
%%   run           in place of the continuation, at a `run' site
%%
%% An arm that does not resume aborts: it throws {'$saga_abort', Ref, Tag, V},
%% caught where the `with' Ref delimits the computation: at its entry, at
%% every resumption of it through its lifted frame, after a non-tail
%% `resume' in its arms, and around the code after such a `resume'.

%% The frame a `with` inherits, with every operation suspending instead of
%% calling its handler. Tags and positions are unchanged. This is the only
%% function that knows the frame's representation.
lift_evidence(Evidence, Ref) ->
    list_to_tuple([{Tag, list_to_tuple([lift_op(Op, Ref) || Op <- tuple_to_list(Ops)])}
                   || {Tag, Ops} <- tuple_to_list(Evidence)]).

%% An operation closure takes its arguments and then the continuation. Once
%% the meta continuation is known, the handler gets a continuation that runs
%% the rest of the handled computation, delimited again by the `with', and
%% then the meta continuation.
%%
%% An operation given a callback (a tagged closure) is not suspended: its
%% handler's arm runs the callback and then resumes, and the meta continuation
%% current at that resume cannot be passed through the arm's code. It is
%% performed where it stands.
lift_op(Op, Ref) ->
    {arity, N} = erlang:fun_info(Op, arity),
    nary(N, Op, fun(All) ->
        {Args, [K]} = lists:split(N - 1, All),
        case lists:any(fun({'$saga_cps', _}) -> true; (_) -> false end, Args) of
            true -> erlang:apply(Op, All);
            false ->
                {'$saga_meta',
                 fun(Mk) -> erlang:apply(Op, Args ++ [fun(V) -> resume_into(Ref, K, V, Mk) end]) end}
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

%% The abort of an arm of the `with' Ref, from effect Tag.
abort(Ref, Tag, Value) -> throw({'$saga_abort', Ref, Tag, Value}).

%% Resume a computation suspended inside the `with' Ref: its aborts are
%% caught here again, and an exception leaving it runs the cleanups of the
%% `finally' regions it is inside of.
resume_into(Ref, K, V, Mk) ->
    R = case {owns_aborts(Mk), pending(Mk)} of
            {false, []} -> K(V);
            {Owns, Keys} ->
                try K(V)
                catch
                    throw:{'$saga_abort', Ref, _, A} when Owns ->
                        cleanup(held(Mk)),
                        A;
                    C:E:S ->
                        cleanup(Keys),
                        erlang:raise(C, E, S)
                end
        end,
    bind(R, Mk).

%% The value of a handled computation goes to the continuation of its `with`.
%% A suspension passing out of `finally' regions takes them along: they are
%% held by whatever handles it, and cleaned up if that handler aborts.
bind({'$saga_meta', M}, Mk) when is_function(Mk) -> M(Mk);
bind({'$saga_meta', M}, Mk) -> guard(pending(Mk), fun() -> M(Mk) end);
bind(Value, Mk) when is_function(Mk) -> Mk(Value);
bind(Value, [Mk]) when is_function(Mk) -> Mk(Value);
bind(Value, [run]) -> Value;
bind(Value, [{k, Ref, F} | Rest]) ->
    R = case {Ref =/= none andalso owns_aborts(Rest), pending(Rest)} of
            {false, []} -> F(Value);
            {Owns, Keys} ->
                try F(Value)
                catch
                    throw:{'$saga_abort', Ref, _, A} when Owns -> A;
                    C:E:S -> cleanup(Keys), erlang:raise(C, E, S)
                end
        end,
    bind(R, Rest);
bind(Value, [{fin, Key} | Rest]) -> fin_exit(Key), bind(Value, Rest);
bind(Value, [{held, _} | Rest]) -> bind(Value, Rest).

%% `let r = resume x; F(r)' in an arm of the `with' Ref: F runs on the value
%% of the handled computation, before the continuation of the `with'.
mbind({'$saga_meta', M}, F, Ref) ->
    {'$saga_meta', fun(Mk) -> M([{k, Ref, F} | frames(Mk)]) end};
mbind(Value, F, _Ref) -> F(Value).

%% `resume' in an arm with a `finally' block, Cleanup: the resumed
%% computation is a region. Cleanup runs once, when the region ends: with a
%% value, with an exception (a panic, or the abort of a `with' further out),
%% or when the handler holding it after a suspension aborts.
fin_resume(Ref, Cleanup, K, V) ->
    Key = make_ref(),
    put(Key, Cleanup),
    R = try K(V)
        catch
            throw:{'$saga_abort', Ref, _, A} -> A;
            C:E:S -> fin_exit(Key), erlang:raise(C, E, S)
        end,
    case R of
        {'$saga_meta', M} ->
            {'$saga_meta', fun(Mk) -> guard([Key], fun() -> M([{fin, Key} | frames(Mk)]) end) end};
        _ -> fin_exit(Key), R
    end.

%% Hand a suspension that left the regions Keys to its handler. While the
%% handler runs, an exception ends the regions; if it suspends in turn, the
%% regions go along with that suspension, held by whatever handles it.
guard([], Thunk) -> Thunk();
guard(Keys, Thunk) ->
    R = try Thunk()
        catch C:E:S -> cleanup(Keys), erlang:raise(C, E, S)
        end,
    case R of
        {'$saga_meta', M} ->
            {'$saga_meta', fun(Mk) -> guard(Keys, fun() -> M([{held, Keys} | frames(Mk)]) end) end};
        _ -> R
    end.

fin_exit(Key) ->
    case erase(Key) of
        undefined -> ok;
        Cleanup -> _ = Cleanup(), ok
    end.

cleanup(Keys) -> lists:foreach(fun fin_exit/1, Keys).

frames(Mk) when is_function(Mk) -> [Mk];
frames(Mk) -> Mk.

%% The regions a meta continuation is inside of, innermost first.
pending(Mk) when is_function(Mk) -> [];
pending(Mk) -> pending(Mk, []).
pending([{fin, Key} | Rest], Acc) -> pending(Rest, [Key | Acc]);
pending([{held, Keys} | Rest], Acc) -> pending(Rest, lists:reverse(Keys, Acc));
pending([_ | Rest], Acc) -> pending(Rest, Acc);
pending([], Acc) -> lists:reverse(Acc).

held(Mk) -> lists:append([Keys || {held, Keys} <- frames(Mk)]).

%% A `run' site does not delimit any `with': an abort passes through it to the
%% `with' it belongs to.
owns_aborts(Mk) when is_function(Mk) -> true;
owns_aborts(Mk) -> lists:last(Mk) =/= run.

%% `bind' where the caller is not CPS code and needs a plain value.
run({'$saga_meta', M}) -> run(M([run]));
run(Value) -> Value.

%% The computation of a spawned process. An abort of a `with' in the process
%% that spawned it cannot be delivered here.
run_process(Thunk) ->
    try run(Thunk())
    catch
        throw:{'$saga_abort', _, Tag, _} ->
            Msg = unicode:characters_to_binary(
                    io_lib:format("the handler of effect ~ts aborted in a process spawned "
                                  "inside its `with`: an abort cannot cross a process boundary",
                                  [Tag])),
            erlang:error({saga_error, panic, Msg, <<>>, <<>>, <<>>, 0})
    end.
