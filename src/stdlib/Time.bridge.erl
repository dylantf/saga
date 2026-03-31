-module(std_time_bridge).
-export([monotonic_ms/0]).

monotonic_ms() ->
    erlang:monotonic_time(millisecond).
