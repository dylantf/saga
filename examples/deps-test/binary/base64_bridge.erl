-module(base64_bridge).
-export([round_trip/1]).

round_trip(Bin) ->
    Encoded = base64url:encode(Bin),
    Decoded = base64url:decode(Encoded),
    {Encoded, Decoded}.
