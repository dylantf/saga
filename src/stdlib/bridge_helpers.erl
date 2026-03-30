-module(std_bridge_helpers).
-export([wrap_maybe/1]).

wrap_maybe(undefined) -> {nothing};
wrap_maybe(V) -> {just, V}.
