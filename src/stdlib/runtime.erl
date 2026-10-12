-module(saga_runtime).
-export([format_crash/3, format_caught_panic/2, await_signal/1]).

%% Slow path of the arity-checked call emitted for function values whose
%% arity the compiler does not know statically.
-export([apply_n/2]).

%% gen_event callbacks for the per-await signal handler installed below.
-export([init/1, handle_event/2, handle_call/2, handle_info/2, terminate/2, code_change/3]).

%% Block the calling process until the given OS signal arrives.
%% `Kind' is a saga `SignalKind' constructor tuple. Installs an OS-level
%% handler for the signal and registers a `gen_event' subscriber on
%% `erl_signal_server' that forwards the signal back to this process. The
%% default OTP handler (which would call `init:stop/0' for SIGTERM, etc.)
%% is removed for the duration so saga code gets to run instead.
await_signal(Kind) ->
    Sig = signal_atom(Kind),
    Self = self(),
    Ref = make_ref(),
    HandlerId = {?MODULE, Ref},
    ok = os:set_signal(Sig, handle),
    %% Remove the OTP default for this signal so it doesn't fire alongside us.
    %% Idempotent across concurrent awaits — first removal wins, rest are no-ops.
    _ = catch gen_event:delete_handler(erl_signal_server, erl_signal_handler, []),
    ok = gen_event:add_handler(erl_signal_server, HandlerId, {Self, Sig, Ref}),
    receive
        {saga_signal, Ref} ->
            _ = catch gen_event:delete_handler(erl_signal_server, HandlerId, []),
            unit
    end.

%% Apply a function value to `Args' when its arity is not known to match.
%%
%% Saga functions are curried in the type system but compiled uncurried, so a
%% value of type `a -> b' reaching generic code may be a fun of any arity. Call
%% sites test `is_function(F, N)' inline and only come here on a mismatch:
%%
%%   - arity < N: call with the arguments the fun takes, then apply the
%%     result to the rest
%%   - arity > N: build a partial application closure for the remainder
%%
%% Effectful function values are bare funs with trailing `_Evidence' and
%% `_ReturnK' parameters; a partial application simply leaves those in place.
%%
%% Anything that is not a fun raises the same `badfun' a direct call would.
%% A zero-arity fun is never a Saga function value, so it is a `badarity'
%% rather than something to call and re-apply.
apply_n(F, Args) when is_function(F) ->
    {arity, Arity} = erlang:fun_info(F, arity),
    N = length(Args),
    if
        Arity =:= N ->
            erlang:apply(F, Args);
        Arity =:= 0 ->
            erlang:error({badarity, {F, Args}});
        Arity < N ->
            {Now, Later} = lists:split(Arity, Args),
            apply_n(erlang:apply(F, Now), Later);
        true ->
            partial(F, Args, Arity - N)
    end;
apply_n(F, _Args) ->
    erlang:error({badfun, F}).

%% A closure taking the `Remaining' arguments `F' still needs. Erlang cannot
%% build a fun of computed arity, hence one clause per arity.
partial(F, Args, 1) ->
    fun(A) -> erlang:apply(F, Args ++ [A]) end;
partial(F, Args, 2) ->
    fun(A, B) -> erlang:apply(F, Args ++ [A, B]) end;
partial(F, Args, 3) ->
    fun(A, B, C) -> erlang:apply(F, Args ++ [A, B, C]) end;
partial(F, Args, 4) ->
    fun(A, B, C, D) -> erlang:apply(F, Args ++ [A, B, C, D]) end;
partial(F, Args, 5) ->
    fun(A, B, C, D, E) -> erlang:apply(F, Args ++ [A, B, C, D, E]) end;
partial(F, Args, 6) ->
    fun(A, B, C, D, E, G) -> erlang:apply(F, Args ++ [A, B, C, D, E, G]) end;
partial(F, Args, 7) ->
    fun(A, B, C, D, E, G, H) -> erlang:apply(F, Args ++ [A, B, C, D, E, G, H]) end;
partial(F, Args, 8) ->
    fun(A, B, C, D, E, G, H, I) -> erlang:apply(F, Args ++ [A, B, C, D, E, G, H, I]) end;
partial(F, Args, 9) ->
    fun(A, B, C, D, E, G, H, I, J) -> erlang:apply(F, Args ++ [A, B, C, D, E, G, H, I, J]) end;
partial(F, Args, 10) ->
    fun(A, B, C, D, E, G, H, I, J, K) ->
        erlang:apply(F, Args ++ [A, B, C, D, E, G, H, I, J, K])
    end;
partial(F, Args, 11) ->
    fun(A, B, C, D, E, G, H, I, J, K, L) ->
        erlang:apply(F, Args ++ [A, B, C, D, E, G, H, I, J, K, L])
    end;
partial(F, Args, 12) ->
    fun(A, B, C, D, E, G, H, I, J, K, L, M) ->
        erlang:apply(F, Args ++ [A, B, C, D, E, G, H, I, J, K, L, M])
    end;
partial(F, Args, Remaining) ->
    {arity, Arity} = erlang:fun_info(F, arity),
    erlang:error({saga_partial_application_limit, Arity, length(Args), Remaining}).

signal_atom({'std_process_SigHup'}) -> sighup;
signal_atom({'std_process_SigQuit'}) -> sigquit;
signal_atom({'std_process_SigAbrt'}) -> sigabrt;
signal_atom({'std_process_SigAlrm'}) -> sigalrm;
signal_atom({'std_process_SigTerm'}) -> sigterm;
signal_atom({'std_process_SigUsr1'}) -> sigusr1;
signal_atom({'std_process_SigUsr2'}) -> sigusr2;
signal_atom({'std_process_SigChld'}) -> sigchld;
signal_atom({'std_process_SigTstp'}) -> sigtstp.

%% gen_event callbacks. State is {TargetPid, SubscribedSignal, Ref}.
init({Pid, Sig, Ref}) -> {ok, {Pid, Sig, Ref}}.

handle_event(Sig, {Pid, Sig, Ref} = State) ->
    Pid ! {saga_signal, Ref},
    {ok, State};
handle_event(_Other, State) ->
    {ok, State}.

handle_call(_Req, State) -> {ok, ok, State}.
handle_info(_Info, State) -> {ok, State}.
terminate(_Reason, _State) -> ok.
code_change(_OldVsn, State, _Extra) -> {ok, State}.

%% Format a BEAM runtime crash into a user-friendly error message.
%% Called from the exec_erl catch-all clause.
format_crash(Class, Reason, StackTrace) ->
    case Reason of
        {saga_error, Kind, Msg, Module, Function, File, Line} ->
            format_saga_error(Kind, Msg, Module, Function, File, Line, StackTrace);
        _ ->
            ReasonStr = format_reason(Class, Reason),
            TraceStr = format_stacktrace(StackTrace),
            case TraceStr of
                "" -> io:format(standard_error, "Runtime error: ~ts~n", [ReasonStr]);
                _ -> io:format(standard_error, "Runtime error: ~ts~n~ts", [ReasonStr, TraceStr])
            end
    end.

%% Format a structured saga error with source location.
format_saga_error(Kind, Msg, Module, Function, File, Line, StackTrace) ->
    KindStr =
        case Kind of
            panic -> <<"panic">>;
            todo -> <<"todo">>;
            assert_fail -> <<"assertion failed">>;
            _ -> atom_to_binary(Kind)
        end,
    %% Print the error message
    io:format(standard_error, "~ts: ~ts~n", [KindStr, Msg]),
    %% Print source location if available
    case {File, Line} of
        {<<>>, _} ->
            ok;
        {_, 0} ->
            ok;
        _ ->
            Qualified =
                case Module of
                    <<"_script">> -> Function;
                    <<"_test">> -> Function;
                    _ -> <<Module/binary, ".", Function/binary>>
                end,
            io:format(
                standard_error,
                "  at ~ts (~ts:~B)~n",
                [Qualified, File, Line]
            )
    end,
    %% Print remaining stack trace (skip internal frames)
    TraceStr = format_stacktrace(StackTrace),
    case TraceStr of
        "" -> ok;
        _ -> io:format(standard_error, "~ts", [TraceStr])
    end.

format_caught_panic(_Class, {saga_error, _Kind, Msg, _Module, _Function, _File, _Line}) ->
    Msg;
format_caught_panic(Class, Reason) ->
    iolist_to_binary(format_reason(Class, Reason)).

format_reason(error, badarith) ->
    "arithmetic error (e.g. division by zero)";
format_reason(error, {badmatch, Val}) ->
    io_lib:format("no match for value: ~ts", [safe_inspect(Val)]);
format_reason(error, function_clause) ->
    "no function clause matched the given arguments";
format_reason(error, {case_clause, Val}) ->
    io_lib:format("no case branch matched value: ~ts", [safe_inspect(Val)]);
format_reason(error, if_clause) ->
    "no matching clause for the given arguments";
format_reason(error, {badarg, _}) ->
    "bad argument";
format_reason(error, badarg) ->
    "bad argument";
format_reason(error, {badarity, {Fun, Args}}) ->
    Arity = erlang:fun_info(Fun, arity),
    io_lib:format(
        "function called with ~B argument(s), but expects ~B",
        [length(Args), element(2, Arity)]
    );
format_reason(error, {badfun, Val}) ->
    io_lib:format("tried to call a value that is not a function: ~ts", [safe_inspect(Val)]);
format_reason(error, {saga_partial_application_limit, Arity, Supplied, Remaining}) ->
    io_lib:format(
        "cannot partially apply a function of ~B parameter(s) to ~B argument(s): "
        "~B would remain, and partial applications built at runtime support at most 12",
        [Arity, Supplied, Remaining]
    );
format_reason(error, undef) ->
    "called a function that does not exist";
format_reason(error, {try_clause, Val}) ->
    io_lib:format("no matching clause for value: ~ts", [safe_inspect(Val)]);
format_reason(throw, Reason) ->
    io_lib:format("uncaught throw: ~ts", [safe_inspect(Reason)]);
format_reason(exit, Reason) ->
    io_lib:format("process exited: ~ts", [safe_inspect(Reason)]);
format_reason(Class, Reason) ->
    io_lib:format("~p: ~p", [Class, Reason]).

format_stacktrace([]) ->
    "";
format_stacktrace(Trace) ->
    Filtered = filter_frames(Trace),
    case Filtered of
        [] ->
            "";
        _ ->
            Lines = [format_frame(F) || F <- Filtered],
            ["\n  Stack trace:\n" | Lines]
    end.

format_frame({Mod, Fun, Arity, Opts}) when is_integer(Arity) ->
    Loc = format_location(Opts),
    FunStr =
        case parse_cps_name(atom_to_list(Fun)) of
            {ok, ParentFun} -> ParentFun;
            none -> io_lib:format("~ts/~B", [Fun, Arity])
        end,
    io_lib:format("    ~ts~ts~n", [format_qualified(Mod, FunStr), Loc]);
format_frame({Mod, Fun, Args, Opts}) when is_list(Args) ->
    Loc = format_location(Opts),
    FunStr =
        case parse_cps_name(atom_to_list(Fun)) of
            {ok, ParentFun} -> ParentFun;
            none -> io_lib:format("~ts/~B", [Fun, length(Args)])
        end,
    io_lib:format("    ~ts~ts~n", [format_qualified(Mod, FunStr), Loc]);
format_frame(_) ->
    "".

%% Format "Module:Function" or just "Function" for scripts.
format_qualified(Mod, FunStr) ->
    case format_mod(Mod) of
        "" -> FunStr;
        ModStr -> io_lib:format("~ts:~ts", [ModStr, FunStr])
    end.

%% Detect BEAM-generated CPS continuation names like "-worker/3-anonymous-1-"
%% and extract the parent function name.
parse_cps_name([$- | Rest]) ->
    case string:split(Rest, "/") of
        [FunName, AfterSlash] ->
            case string:find(AfterSlash, "-anonymous-") of
                nomatch -> none;
                _ -> {ok, FunName}
            end;
        _ ->
            none
    end;
parse_cps_name(_) ->
    none.

format_location(Opts) ->
    case proplists:get_value(file, Opts) of
        undefined ->
            "";
        File ->
            case proplists:get_value(line, Opts) of
                undefined -> io_lib:format(" (~ts)", [File]);
                Line -> io_lib:format(" (~ts:~B)", [File, Line])
            end
    end.

format_mod('_script') ->
    "";
format_mod('_test') ->
    "";
format_mod(Mod) ->
    %% Convert mangled Erlang module name back to saga style.
    %% e.g. "myapp_server" stays as-is (we can't recover "MyApp.Server"
    %% without metadata), but at least strip the "std_" prefix for stdlib.
    Name = atom_to_list(Mod),
    case lists:prefix("std_", Name) of
        true -> "Std." ++ capitalize(lists:nthtail(4, Name));
        false -> Name
    end.

capitalize([]) -> [];
capitalize([H | T]) when H >= $a, H =< $z -> [H - 32 | T];
capitalize(S) -> S.

%% Filter out internal frames the user doesn't care about.
filter_frames(Trace) ->
    [
        F
     || F = {Mod, _, _, _} <- Trace,
        not is_internal_frame(Mod)
    ].

is_internal_frame(erlang) -> true;
is_internal_frame(erl_eval) -> true;
is_internal_frame(init) -> true;
is_internal_frame(saga_runtime) -> true;
is_internal_frame(_) -> false.

%% Try to produce a readable representation of a value.
safe_inspect(Val) when is_binary(Val) -> Val;
safe_inspect(Val) ->
    try
        io_lib:format("~p", [Val])
    catch
        _:_ -> io_lib:format("~w", [Val])
    end.
