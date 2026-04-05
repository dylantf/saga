-module(std_dynamic_bridge).
-export([decode_string/1, decode_int/1, decode_float/1, decode_bool/1,
         field_lookup/2, element_lookup/2, decode_list/2, decode_optional/2,
         classify/1, from_erlang/1]).

%% Primitive decoders

decode_string(V) when is_binary(V) -> {ok, V};
decode_string(V) -> {error, {std_dynamic_DecodeError, <<"String">>, classify(V), []}}.

decode_int(V) when is_integer(V) -> {ok, V};
decode_int(V) -> {error, {std_dynamic_DecodeError, <<"Int">>, classify(V), []}}.

decode_float(V) when is_float(V) -> {ok, V};
decode_float(V) -> {error, {std_dynamic_DecodeError, <<"Float">>, classify(V), []}}.

decode_bool(true) -> {ok, true};
decode_bool(false) -> {ok, false};
decode_bool(V) -> {error, {std_dynamic_DecodeError, <<"Bool">>, classify(V), []}}.

%% Field lookup (maps)

field_lookup(Name, Data) when is_map(Data) ->
    case maps:find(Name, Data) of
        {ok, V} -> {ok, V};
        error ->
            {error, {std_dynamic_DecodeError,
                     <<"field '", Name/binary, "'">>,
                     <<"nothing">>, []}}
    end;
field_lookup(Name, Data) ->
    {error, {std_dynamic_DecodeError,
             <<"Map with field '", Name/binary, "'">>,
             classify(Data), []}}.

%% Element lookup (tuples and lists, 0-indexed)

element_lookup(Index, Data) when is_tuple(Data), Index >= 0, Index < tuple_size(Data) ->
    {ok, element(Index + 1, Data)};
element_lookup(Index, Data) when is_tuple(Data) ->
    Idx = integer_to_binary(Index),
    Size = integer_to_binary(tuple_size(Data)),
    {error, {std_dynamic_DecodeError,
             <<"element at index ", Idx/binary>>,
             <<"Tuple of size ", Size/binary>>, []}};
element_lookup(Index, Data) when is_list(Data), Index >= 0 ->
    case list_nth(Index, Data) of
        {ok, V} -> {ok, V};
        error ->
            Idx = integer_to_binary(Index),
            Len = integer_to_binary(length(Data)),
            {error, {std_dynamic_DecodeError,
                     <<"element at index ", Idx/binary>>,
                     <<"List of length ", Len/binary>>, []}}
    end;
element_lookup(Index, Data) ->
    Idx = integer_to_binary(Index),
    {error, {std_dynamic_DecodeError,
             <<"element at index ", Idx/binary>>,
             classify(Data), []}}.

list_nth(0, [H | _]) -> {ok, H};
list_nth(N, [_ | T]) when N > 0 -> list_nth(N - 1, T);
list_nth(_, _) -> error.

%% List decoder

decode_list(DecoderFun, Data) when is_list(Data) ->
    decode_list_loop(DecoderFun, Data, 0, []);
decode_list(_DecoderFun, Data) ->
    {error, {std_dynamic_DecodeError, <<"List">>, classify(Data), []}}.

decode_list_loop(_DecoderFun, [], _Index, Acc) ->
    {ok, lists:reverse(Acc)};
decode_list_loop(DecoderFun, [H | T], Index, Acc) ->
    case DecoderFun(H) of
        {ok, V} ->
            decode_list_loop(DecoderFun, T, Index + 1, [V | Acc]);
        {error, {std_dynamic_DecodeError, Exp, Found, Path}} ->
            IdxBin = integer_to_binary(Index),
            {error, {std_dynamic_DecodeError, Exp, Found, [IdxBin | Path]}}
    end.

%% Optional decoder

decode_optional(_DecoderFun, nil) -> {ok, {nothing}};
decode_optional(_DecoderFun, undefined) -> {ok, {nothing}};
decode_optional(_DecoderFun, null) -> {ok, {nothing}};
decode_optional(_DecoderFun, {nothing}) -> {ok, {nothing}};
decode_optional(DecoderFun, Data) ->
    case DecoderFun(Data) of
        {ok, V} -> {ok, {just, V}};
        {error, E} -> {error, E}
    end.

%% Classify a BEAM value into a human-readable type string

classify(V) when is_binary(V) -> <<"String">>;
classify(V) when is_integer(V) -> <<"Int">>;
classify(V) when is_float(V) -> <<"Float">>;
classify(true) -> <<"Bool">>;
classify(false) -> <<"Bool">>;
classify(V) when is_atom(V) -> <<"Atom">>;
classify(V) when is_list(V) -> <<"List">>;
classify(V) when is_tuple(V) -> <<"Tuple">>;
classify(V) when is_map(V) -> <<"Map">>;
classify(V) when is_pid(V) -> <<"Pid">>;
classify(V) when is_function(V) -> <<"Function">>;
classify(V) when is_reference(V) -> <<"Reference">>;
classify(V) when is_port(V) -> <<"Port">>;
classify(_) -> <<"Unknown">>.

%% Coerce any Erlang value to Dynamic (identity at runtime)

from_erlang(V) -> V.
