-module(mathlib_bridge).
-export([random_int/2]).

random_int(Min, Max) ->
    Min + rand:uniform(Max - Min + 1) - 1.
