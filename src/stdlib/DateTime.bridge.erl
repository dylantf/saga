-module(std_datetime_bridge).
-export([
    now_utc/1,
    today_utc/1,
    time_of_day_utc/1,
    day_of_week/1,
    is_leap_year/1,
    days_in_month/2,
    valid_date/1,
    add_seconds/2,
    diff_seconds/2
]).

%% Clock handler impls

now_utc(unit) ->
    {{Y, Mo, D}, {H, Mi, S}} = calendar:universal_time(),
    {_, _, Micro} = os:timestamp(),
    {std_datetime_NaiveDateTime, Y, Mo, D, H, Mi, S, Micro}.

today_utc(unit) ->
    {{Y, Mo, D}, _} = calendar:universal_time(),
    {std_datetime_Date, Y, Mo, D}.

time_of_day_utc(unit) ->
    {_, {H, Mi, S}} = calendar:universal_time(),
    {std_datetime_Time, H, Mi, S, 0}.

%% Calendar operations

day_of_week({std_datetime_Date, Y, M, D}) ->
    calendar:day_of_the_week(Y, M, D).

is_leap_year(Year) ->
    calendar:is_leap_year(Year).

days_in_month(Year, Month) ->
    calendar:last_day_of_the_month(Year, Month).

valid_date({std_datetime_Date, Y, M, D}) ->
    calendar:valid_date(Y, M, D).

%% Arithmetic

add_seconds(Secs, {std_datetime_NaiveDateTime, Y, Mo, D, H, Mi, S, Micro}) ->
    GregSecs = calendar:datetime_to_gregorian_seconds({{Y, Mo, D}, {H, Mi, S}}),
    {{Y2, Mo2, D2}, {H2, Mi2, S2}} = calendar:gregorian_seconds_to_datetime(GregSecs + Secs),
    {std_datetime_NaiveDateTime, Y2, Mo2, D2, H2, Mi2, S2, Micro}.

diff_seconds(
    {std_datetime_NaiveDateTime, Y1, Mo1, D1, H1, Mi1, S1, _},
    {std_datetime_NaiveDateTime, Y2, Mo2, D2, H2, Mi2, S2, _}
) ->
    G1 = calendar:datetime_to_gregorian_seconds({{Y1, Mo1, D1}, {H1, Mi1, S1}}),
    G2 = calendar:datetime_to_gregorian_seconds({{Y2, Mo2, D2}, {H2, Mi2, S2}}),
    G1 - G2.
