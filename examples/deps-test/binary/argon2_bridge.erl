-module(argon2_bridge).
-export([hash/1]).

hash(Password) ->
    {ok, Hash} = argon2:hash(Password),
    Hash.
