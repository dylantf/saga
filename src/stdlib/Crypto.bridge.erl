-module(std_crypto_bridge).
-export([
    hmac_sha256/2,
    base64url_encode/1,
    base64url_decode/1,
    base64_encode/1,
    base64_decode/1,
    sha1_digest/1,
    sha256_digest/1,
    strong_rand_bytes/1,
    secure_equal/2
]).

hmac_sha256(Key, Data) ->
    crypto:mac(hmac, sha256, Key, Data).

base64url_encode(Bin) ->
    Encoded = base64:encode(Bin),
    NoPadding = binary:replace(Encoded, <<"=">>, <<>>, [global]),
    Url1 = binary:replace(NoPadding, <<"+">>, <<"-">>, [global]),
    binary:replace(Url1, <<"/">>, <<"_">>, [global]).

base64url_decode(Text) ->
    case valid_base64url(Text) of
        true ->
            try
                Std1 = binary:replace(Text, <<"-">>, <<"+">>, [global]),
                Std = binary:replace(Std1, <<"_">>, <<"/">>, [global]),
                {ok, base64:decode(add_base64_padding(Std))}
            catch
                _:_ -> {error, <<"invalid_base64url">>}
            end;
        false ->
            {error, <<"invalid_base64url">>}
    end.

base64_encode(Bin) ->
    base64:encode(Bin).

base64_decode(Text) ->
    case valid_base64(Text) of
        true ->
            try
                {ok, base64:decode(add_base64_padding(Text))}
            catch
                _:_ -> {error, <<"invalid_base64">>}
            end;
        false ->
            {error, <<"invalid_base64">>}
    end.

sha1_digest(Data) ->
    crypto:hash(sha, Data).

sha256_digest(Data) ->
    crypto:hash(sha256, Data).

strong_rand_bytes(N) ->
    crypto:strong_rand_bytes(N).

secure_equal(A, B) ->
    SizeA = byte_size(A),
    SizeB = byte_size(B),
    Max = max(SizeA, SizeB),
    Diff = secure_equal_loop(A, B, 0, Max, SizeA bxor SizeB),
    Diff =:= 0.

secure_equal_loop(_A, _B, Index, Max, Diff) when Index >= Max ->
    Diff;
secure_equal_loop(A, B, Index, Max, Diff) ->
    ByteA = byte_at(A, Index),
    ByteB = byte_at(B, Index),
    secure_equal_loop(A, B, Index + 1, Max, Diff bor (ByteA bxor ByteB)).

byte_at(Bin, Index) ->
    case Index < byte_size(Bin) of
        true -> binary:at(Bin, Index);
        false -> 0
    end.

valid_base64url(Text) ->
    byte_size(Text) rem 4 =/= 1 andalso valid_base64url_bytes(binary_to_list(Text)).

valid_base64url_bytes([]) -> true;
valid_base64url_bytes([Byte | Rest]) ->
    valid_base64url_byte(Byte) andalso valid_base64url_bytes(Rest).

valid_base64url_byte(Byte) ->
    (Byte >= $A andalso Byte =< $Z)
        orelse (Byte >= $a andalso Byte =< $z)
        orelse (Byte >= $0 andalso Byte =< $9)
        orelse Byte =:= $-
        orelse Byte =:= $_
        orelse Byte =:= $=.

valid_base64(Text) ->
    byte_size(Text) rem 4 =/= 1 andalso valid_base64_bytes(binary_to_list(Text)).

valid_base64_bytes([]) -> true;
valid_base64_bytes([Byte | Rest]) ->
    valid_base64_byte(Byte) andalso valid_base64_bytes(Rest).

valid_base64_byte(Byte) ->
    (Byte >= $A andalso Byte =< $Z)
        orelse (Byte >= $a andalso Byte =< $z)
        orelse (Byte >= $0 andalso Byte =< $9)
        orelse Byte =:= $+
        orelse Byte =:= $/
        orelse Byte =:= $=.

add_base64_padding(Bin) ->
    case byte_size(Bin) rem 4 of
        0 -> Bin;
        2 -> <<Bin/binary, "==">>;
        3 -> <<Bin/binary, "=">>;
        _ -> Bin
    end.
