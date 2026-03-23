-module(std_file_bridge).
-export([read_file/1, write_file/2, append_file/2, delete_file/1, file_exists/1]).

read_file(Path) ->
    case file:read_file(Path) of
        {ok, Bin} -> {ok, Bin};
        {error, Reason} -> {error, atom_to_binary(Reason)}
    end.

write_file(Path, Content) ->
    case file:write_file(Path, Content) of
        ok -> {ok, unit};
        {error, Reason} -> {error, atom_to_binary(Reason)}
    end.

append_file(Path, Content) ->
    case file:write_file(Path, Content, [append]) of
        ok -> {ok, unit};
        {error, Reason} -> {error, atom_to_binary(Reason)}
    end.

delete_file(Path) ->
    case file:delete(Path) of
        ok -> {ok, unit};
        {error, Reason} -> {error, atom_to_binary(Reason)}
    end.

file_exists(Path) ->
    filelib:is_file(Path).
