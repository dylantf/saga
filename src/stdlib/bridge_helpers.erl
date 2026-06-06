-module(std_bridge_helpers).
-export([wrap_maybe/1]).

wrap_maybe(undefined) -> {std_maybe_Nothing};
wrap_maybe(V) -> {std_maybe_Just, V}.
