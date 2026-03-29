-module(std_math_bridge).
-export([sqrt/1, log/1, log2/1, log10/1,
         asin/1, acos/1,
         pow/2, atan2/2]).

sqrt(X) when is_number(X), X >= 0 -> math:sqrt(X);
sqrt(X) -> panic("Math.sqrt: argument must be non-negative (got " ++ format_num(X) ++ ")").

log(X) when is_number(X), X > 0 -> math:log(X);
log(X) -> panic("Math.log: argument must be positive (got " ++ format_num(X) ++ ")").

log2(X) when is_number(X), X > 0 -> math:log2(X);
log2(X) -> panic("Math.log2: argument must be positive (got " ++ format_num(X) ++ ")").

log10(X) when is_number(X), X > 0 -> math:log10(X);
log10(X) -> panic("Math.log10: argument must be positive (got " ++ format_num(X) ++ ")").

asin(X) when is_number(X), X >= -1, X =< 1 -> math:asin(X);
asin(X) -> panic("Math.asin: argument must be in [-1, 1] (got " ++ format_num(X) ++ ")").

acos(X) when is_number(X), X >= -1, X =< 1 -> math:acos(X);
acos(X) -> panic("Math.acos: argument must be in [-1, 1] (got " ++ format_num(X) ++ ")").

pow(Base, Exp) ->
    case catch math:pow(Base, Exp) of
        {'EXIT', _} -> panic("Math.pow: invalid arguments (" ++ format_num(Base) ++ ", " ++ format_num(Exp) ++ ")");
        Result -> Result
    end.

atan2(Y, X) ->
    case catch math:atan2(Y, X) of
        {'EXIT', _} -> panic("Math.atan2: invalid arguments (" ++ format_num(Y) ++ ", " ++ format_num(X) ++ ")");
        Result -> Result
    end.

%% Internal helpers

panic(Msg) ->
    erlang:error({dylang_panic, "panic: " ++ Msg}).

format_num(X) when is_float(X) -> float_to_list(X, [short]);
format_num(X) when is_integer(X) -> integer_to_list(X);
format_num(X) -> lists:flatten(io_lib:format("~p", [X])).
