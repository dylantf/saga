-module(saga_runtime).
-export([format_crash/3]).

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
