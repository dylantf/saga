-module(std_file_bridge).
-export([read_file/1, write_file/2, append_file/2, delete_file/1, file_exists/1]).

read_file(Path) ->
    case file:read_file(Path) of
        {ok, Bin} -> {ok, Bin};
        {error, Reason} -> {error, map_error(Reason)}
    end.

write_file(Path, Content) ->
    case file:write_file(Path, Content) of
        ok -> {ok, unit};
        {error, Reason} -> {error, map_error(Reason)}
    end.

append_file(Path, Content) ->
    case file:write_file(Path, Content, [append]) of
        ok -> {ok, unit};
        {error, Reason} -> {error, map_error(Reason)}
    end.

delete_file(Path) ->
    case file:delete(Path) of
        ok -> {ok, unit};
        {error, Reason} -> {error, map_error(Reason)}
    end.

file_exists(Path) ->
    filelib:is_file(Path).

map_error(enoent) -> {'std_file_NotFound'};
map_error(eacces) -> {'std_file_PermissionDenied'};
map_error(eisdir) -> {'std_file_IsDirectory'};
map_error(enotdir) -> {'std_file_NotDirectory'};
map_error(enospc) -> {'std_file_NoSpace'};
map_error(eexist) -> {'std_file_AlreadyExists'};
map_error(Reason) -> {'std_file_Other', atom_to_binary(Reason)}.
