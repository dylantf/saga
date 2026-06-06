-module(std_float_bridge).
-export([parse/1, to_string/1]).

parse(S) ->
    %% try/catch ensures any BIF crash (e.g. unexpected input shape) becomes
    %% Nothing — parse should never panic, only succeed or report Nothing.
    try
        case string:to_float(S) of
            {F, <<>>} -> {std_maybe_Just, F};
            {F, []} -> {std_maybe_Just, F};
            _ ->
                %% Fall back to integer parse for inputs like "2" that lack a
                %% decimal point — string:to_float/1 rejects those.
                case string:to_integer(S) of
                    {N, <<>>} -> {std_maybe_Just, float(N)};
                    {N, []} -> {std_maybe_Just, float(N)};
                    _ -> {std_maybe_Nothing}
                end
        end
    catch
        _:_ -> {std_maybe_Nothing}
    end.

to_string(X) ->
    float_to_binary(X, [short]).
