-module(std_env_bridge).
-export([get/1]).

get(Key) ->
    case os:getenv(binary_to_list(Key)) of
        false -> {nothing};
        Value -> {just, list_to_binary(Value)}
    end.
