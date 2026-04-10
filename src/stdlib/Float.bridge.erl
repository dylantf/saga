-module(std_float_bridge).
-export([parse/1, to_string/1]).

parse(S) ->
    %% try/catch ensures any BIF crash (e.g. unexpected input shape) becomes
    %% {nothing} — parse should never panic, only succeed or report Nothing.
    try
        case string:to_float(S) of
            {F, <<>>} -> {just, F};
            {F, []} -> {just, F};
            _ ->
                %% Fall back to integer parse for inputs like "2" that lack a
                %% decimal point — string:to_float/1 rejects those.
                case string:to_integer(S) of
                    {N, <<>>} -> {just, float(N)};
                    {N, []} -> {just, float(N)};
                    _ -> {nothing}
                end
        end
    catch
        _:_ -> {nothing}
    end.

to_string(X) ->
    float_to_binary(X, [short]).
