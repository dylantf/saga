-module(std_bitstring_bridge).
-export([from_list/1, from_string/1, to_string/1, to_string_unchecked/1,
         at/2, slice/3, append/2, concat/1, zeroes/1, from_byte/1,
         encode_int/2, decode_int/1, encode_int_little/2, decode_int_little/1]).

from_list(Bytes) ->
    list_to_binary(Bytes).

from_string(S) ->
    S.  % Dylan strings are already UTF-8 binaries

to_string(Bs) ->
    case unicode:characters_to_binary(Bs) of
        {error, _, _} -> {error, <<"invalid UTF-8">>};
        {incomplete, _, _} -> {error, <<"incomplete UTF-8">>};
        Result when is_binary(Result) -> {ok, Result}
    end.

%% No validation: Saga strings are already UTF-8 binaries, so this is the
%% identity. Caller must guarantee the bytes are valid UTF-8.
to_string_unchecked(Bs) ->
    Bs.

at(Index, Bs) when Index >= 0, Index < byte_size(Bs) ->
    {just, binary:at(Bs, Index)};
at(_, _) ->
    {nothing}.

slice(Start, Len, Bs) ->
    binary:part(Bs, Start, Len).

append(A, B) ->
    <<A/binary, B/binary>>.

%% Flatten a list of binaries into one binary in a single C pass.
%% iolist_to_binary accepts deep lists too, but the Saga type is a flat
%% List BitString. It does not re-validate UTF-8 (unlike to_string), which
%% is exactly what we want for already-valid fragments.
concat(Parts) ->
    iolist_to_binary(Parts).

zeroes(N) ->
    <<0:(N*8)>>.

from_byte(B) ->
    <<B:8>>.

encode_int(Width, Value) ->
    <<Value:(Width*8)/big>>.

decode_int(Bs) ->
    Size = byte_size(Bs) * 8,
    <<Value:Size/big>> = Bs,
    Value.

encode_int_little(Width, Value) ->
    <<Value:(Width*8)/little>>.

decode_int_little(Bs) ->
    Size = byte_size(Bs) * 8,
    <<Value:Size/little>> = Bs,
    Value.
