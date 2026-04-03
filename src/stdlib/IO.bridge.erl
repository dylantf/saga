-module(std_io_bridge).
-export([read_line/0, read_char/0]).

read_line() ->
    io:setopts(standard_io, [{binary, true}]),
    case io:get_line("") of
        eof -> <<"">>;
        {error, _} -> <<"">>;
        Bin -> string:trim(Bin, trailing, "\n")
    end.

read_char() ->
    io:setopts(standard_io, [{binary, true}]),
    case io:get_chars("", 1) of
        eof -> <<"">>;
        {error, _} -> <<"">>;
        Bin -> Bin
    end.
