//! ECMA-262 §21.4 `Date` Objects: formally verified calendar arithmetic (`Day`, `TimeWithinDay`,
//! `DaysInYear`, `DayFromYear`, `TimeFromYear`, `YearFromTime`, `InLeapYear`, `DayWithinYear`,
//! `MonthFromTime`, `DateFromTime`, `WeekDay`, `HourFromTime`, `MinFromTime`, `SecFromTime`,
//! `msFromTime`, `MakeTime`, `MakeDay`, `MakeDate`, `TimeClip`) and §21.4.1.32 / §21.4.4.36
//! ISO-8601 Date Time String parser & serializer with valid-date roundtrip proof.
use vstd::prelude::*;

verus! {

/// §21.4.1.11 `HoursPerDay = 24`.
pub const HOURS_PER_DAY: i64 = 24;
/// §21.4.1.11 `MinutesPerHour = 60`.
pub const MINUTES_PER_HOUR: i64 = 60;
/// §21.4.1.11 `SecondsPerMinute = 60`.
pub const SECONDS_PER_MINUTE: i64 = 60;
/// §21.4.1.11 `msPerSecond = 1000`.
pub const MS_PER_SECOND: i64 = 1_000;
/// §21.4.1.11 `msPerMinute = 60000`.
pub const MS_PER_MINUTE: i64 = 60_000;
/// §21.4.1.11 `msPerHour = 3600000`.
pub const MS_PER_HOUR: i64 = 3_600_000;
/// §21.4.1.2 `msPerDay = 86400000`.
pub const MS_PER_DAY: i64 = 86_400_000;
/// §21.4.1.15 Maximum magnitude of an ECMAScript time value (`8.64e15` ms = 100,000,000 days).
pub const MAX_TIME_MS: i64 = 8_640_000_000_000_000;
/// Bound on day numbers for clipped time values (`±100,000,000`).
pub const MAX_DAY_ABS: i64 = 100_000_000;
/// Safe input bound for `i64` year/day calendar computations without 64-bit overflow.
pub const MAX_SAFE_YEAR_ABS: i64 = 200_000_000;

// =======================================================================================
// Euclidean Floor Division and Modulo Helpers (`exec == spec`)
// =======================================================================================

fn floor_div_i64(a: i64, b: i64) -> (q: i64)
    requires
        b > 0,
        a > i64::MIN,
    ensures
        q as int == (a as int) / (b as int),
{
    let bu: u64 = b as u64;
    if a >= 0 {
        let au: u64 = a as u64;
        let qu: u64 = au / bu;
        proof {
            assert(qu as int == (a as int) / (b as int)) by (nonlinear_arith)
                requires
                    b > 0,
                    a >= 0,
                    bu == b as u64,
                    au == a as u64,
                    qu == au / bu,
            ;
        }
        qu as i64
    } else {
        let na: u64 = (-1i64 - a) as u64;
        let qu: u64 = na / bu;
        let ghost ru: u64 = na % bu;
        proof {
            assert((-(qu as int) - 1) == (a as int) / (b as int)) by (nonlinear_arith)
                requires
                    b > 0,
                    a < 0,
                    a > i64::MIN,
                    bu == b as u64,
                    na == (-1 - a as int) as u64,
                    qu == na / bu,
                    ru == na % bu,
            ;
        }
        -(qu as i64) - 1
    }
}

fn modulo_i64(a: i64, b: i64) -> (r: i64)
    requires
        b > 0,
        a > i64::MIN,
    ensures
        r as int == (a as int) % (b as int),
        0 <= r < b,
{
    let q: i64 = floor_div_i64(a, b);
    let a128: i128 = a as i128;
    let b128: i128 = b as i128;
    let q128: i128 = q as i128;
    proof {
        assert((a128 as int) - (b128 as int) * (q128 as int) == (a as int) % (b as int)
            && 0 <= (a as int) % (b as int)
            && (a as int) % (b as int) < (b as int)) by (nonlinear_arith)
            requires
                b > 0,
                q as int == (a as int) / (b as int),
                a128 == a as i128,
                b128 == b as i128,
                q128 == q as i128,
        ;
        assert(i128::MIN <= (b128 as int) * (q128 as int)
            && (b128 as int) * (q128 as int) <= i128::MAX) by (nonlinear_arith)
            requires
                b > 0,
                b128 == b as i128,
                q128 == q as i128,
                b <= i64::MAX,
                i64::MIN <= q && q <= i64::MAX,
        ;
    }
    let prod: i128 = b128 * q128;
    (a128 - prod) as i64
}

// =======================================================================================
// 1. ECMA-262 §21.4 Spec Equations
// =======================================================================================

/// §21.4.1.2 `Day ( t ) = floor(t / msPerDay)`.
pub open spec fn spec_day(t: int) -> int {
    t / (MS_PER_DAY as int)
}

/// §21.4.1.2 `TimeWithinDay ( t ) = t modulo msPerDay`.
pub open spec fn spec_time_within_day(t: int) -> int {
    t % (MS_PER_DAY as int)
}

/// Leap-year predicate on year integer `y`.
pub open spec fn spec_is_leap_year_num(y: int) -> bool {
    (y % 4 == 0 && y % 100 != 0) || (y % 400 == 0)
}

/// §21.4.1.3 `DaysInYear ( y )`: 366 for leap years, 365 otherwise.
pub open spec fn spec_days_in_year(y: int) -> int {
    if spec_is_leap_year_num(y) {
        366
    } else {
        365
    }
}

/// §21.4.1.3 `DayFromYear ( y ) = 365 * (y - 1970) + floor((y - 1969)/4) - floor((y - 1901)/100) + floor((y - 1601)/400)`.
pub open spec fn spec_day_from_year(y: int) -> int {
    365 * (y - 1970) + (y - 1969) / 4 - (y - 1901) / 100 + (y - 1601) / 400
}

/// §21.4.1.3 `TimeFromYear ( y ) = msPerDay * DayFromYear(y)`.
pub open spec fn spec_time_from_year(y: int) -> int {
    (MS_PER_DAY as int) * spec_day_from_year(y)
}

/// Year from day number `d`: closed-form 400-year Gregorian cycle lookup (exact over all `d` in `ℤ`).
pub open spec fn spec_year_from_day(d: int) -> int {
    let y0 = 1970 + (400 * d) / 146_097;
    if d >= spec_day_from_year(y0 + 1) {
        y0 + 1
    } else if d >= spec_day_from_year(y0) {
        y0
    } else {
        y0 - 1
    }
}

/// §21.4.1.3 `YearFromTime ( t )`: largest integer `y` such that `TimeFromYear(y) <= t`.
pub open spec fn spec_year_from_time(t: int) -> int {
    spec_year_from_day(spec_day(t))
}

/// §21.4.1.3 `InLeapYear ( t )`: `1` if `DaysInYear(YearFromTime(t)) == 366`, else `0`.
pub open spec fn spec_in_leap_year(t: int) -> int {
    if spec_days_in_year(spec_year_from_time(t)) == 366 {
        1
    } else {
        0
    }
}

/// §21.4.1.4 `DayWithinYear ( t ) = Day(t) - DayFromYear(YearFromTime(t))`.
pub open spec fn spec_day_within_year(t: int) -> int {
    spec_day(t) - spec_day_from_year(spec_year_from_time(t))
}

/// §21.4.1.4 `MonthFromTime ( t )` (`0..=11`).
pub open spec fn spec_month_from_time(t: int) -> int {
    let d = spec_day_within_year(t);
    let leap = spec_in_leap_year(t);
    if d < 31 {
        0
    } else if d < 59 + leap {
        1
    } else if d < 90 + leap {
        2
    } else if d < 120 + leap {
        3
    } else if d < 151 + leap {
        4
    } else if d < 181 + leap {
        5
    } else if d < 212 + leap {
        6
    } else if d < 243 + leap {
        7
    } else if d < 273 + leap {
        8
    } else if d < 304 + leap {
        9
    } else if d < 334 + leap {
        10
    } else {
        11
    }
}

/// §21.4.1.5 `DateFromTime ( t )` (`1..=31`).
pub open spec fn spec_date_from_time(t: int) -> int {
    let d = spec_day_within_year(t);
    let leap = spec_in_leap_year(t);
    let m = spec_month_from_time(t);
    if m == 0 {
        d + 1
    } else if m == 1 {
        d - 30
    } else if m == 2 {
        d - 58 - leap
    } else if m == 3 {
        d - 89 - leap
    } else if m == 4 {
        d - 119 - leap
    } else if m == 5 {
        d - 150 - leap
    } else if m == 6 {
        d - 180 - leap
    } else if m == 7 {
        d - 211 - leap
    } else if m == 8 {
        d - 242 - leap
    } else if m == 9 {
        d - 272 - leap
    } else if m == 10 {
        d - 303 - leap
    } else {
        d - 333 - leap
    }
}

/// §21.4.1.6 `WeekDay ( t ) = (Day(t) + 4) modulo 7`.
pub open spec fn spec_week_day(t: int) -> int {
    (spec_day(t) + 4) % 7
}

/// §21.4.1.11 `HourFromTime ( t ) = floor(t / msPerHour) modulo HoursPerDay`.
pub open spec fn spec_hour_from_time(t: int) -> int {
    (t / (MS_PER_HOUR as int)) % (HOURS_PER_DAY as int)
}

/// §21.4.1.11 `MinFromTime ( t ) = floor(t / msPerMinute) modulo MinutesPerHour`.
pub open spec fn spec_min_from_time(t: int) -> int {
    (t / (MS_PER_MINUTE as int)) % (MINUTES_PER_HOUR as int)
}

/// §21.4.1.11 `SecFromTime ( t ) = floor(t / msPerSecond) modulo SecondsPerMinute`.
pub open spec fn spec_sec_from_time(t: int) -> int {
    (t / (MS_PER_SECOND as int)) % (SECONDS_PER_MINUTE as int)
}

/// §21.4.1.11 `msFromTime ( t ) = t modulo msPerSecond`.
pub open spec fn spec_ms_from_time(t: int) -> int {
    t % (MS_PER_SECOND as int)
}

/// §21.4.1.12 `MakeTime ( hour, min, sec, ms )`.
pub open spec fn spec_make_time(hour: int, min: int, sec: int, ms: int) -> int {
    hour * (MS_PER_HOUR as int)
        + min * (MS_PER_MINUTE as int)
        + sec * (MS_PER_SECOND as int)
        + ms
}

/// Day offset of the 1st of month `m` (`0..=11`) within a year (`leap` in `{0, 1}`).
pub open spec fn spec_month_start_day(m: int, leap: int) -> int {
    if m == 0 {
        0
    } else if m == 1 {
        31
    } else if m == 2 {
        59 + leap
    } else if m == 3 {
        90 + leap
    } else if m == 4 {
        120 + leap
    } else if m == 5 {
        151 + leap
    } else if m == 6 {
        181 + leap
    } else if m == 7 {
        212 + leap
    } else if m == 8 {
        243 + leap
    } else if m == 9 {
        273 + leap
    } else if m == 10 {
        304 + leap
    } else {
        334 + leap
    }
}

/// Number of days in month `m` (`0..=11`) for `leap` in `{0, 1}`.
pub open spec fn spec_days_in_month(m: int, leap: int) -> int {
    if m == 0 || m == 2 || m == 4 || m == 6 || m == 7 || m == 9 || m == 11 {
        31
    } else if m == 3 || m == 5 || m == 8 || m == 10 {
        30
    } else {
        28 + leap
    }
}

/// §21.4.1.13 `MakeDay ( year, month, date )`.
pub open spec fn spec_make_day(year: int, month: int, date: int) -> int {
    let ym = year + month / 12;
    let mn = month % 12;
    let leap = if spec_is_leap_year_num(ym) { 1 } else { 0 };
    spec_day_from_year(ym) + spec_month_start_day(mn, leap) + date - 1
}

/// §21.4.1.14 `MakeDate ( day, time ) = day * msPerDay + time`.
pub open spec fn spec_make_date(day: int, time: int) -> int {
    day * (MS_PER_DAY as int) + time
}

/// §21.4.1.15 `TimeClip ( time )`: returns `Some(time)` iff `|time| <= 8.64e15`.
pub open spec fn spec_time_clip(tv: int) -> Option<int> {
    if -(MAX_TIME_MS as int) <= tv && tv <= (MAX_TIME_MS as int) {
        Some(tv)
    } else {
        None
    }
}

// =======================================================================================
// 2. Proofs of ECMA-262 §21.4 Calendar Identities
// =======================================================================================

/// `DayFromYear(y + 1) == DayFromYear(y) + DaysInYear(y)`.
pub proof fn lemma_day_from_year_step(y: int)
    ensures
        spec_day_from_year(y + 1) == spec_day_from_year(y) + spec_days_in_year(y),
{
    assert((y + 1 - 1969) / 4 - (y - 1969) / 4 == if y % 4 == 0 { 1int } else { 0int });
    assert((y + 1 - 1901) / 100 - (y - 1901) / 100 == if y % 100 == 0 { 1int } else { 0int });
    assert((y + 1 - 1601) / 400 - (y - 1601) / 400 == if y % 400 == 0 { 1int } else { 0int });
}

/// Strict monotonicity of `DayFromYear`: `y1 < y2 ==> DayFromYear(y1) < DayFromYear(y2)`.
pub proof fn lemma_day_from_year_monotonic(y1: int, y2: int)
    requires
        y1 < y2,
    ensures
        spec_day_from_year(y1) < spec_day_from_year(y2),
{
}

/// Exact ECMA-262 §21.4.1.3 characterization of `YearFromTime(t)`:
/// `TimeFromYear(y) <= t < TimeFromYear(y + 1)`, so `y` is the unique largest integer with `TimeFromYear(y) <= t`.
pub proof fn lemma_year_from_time_characterization(t: int)
    ensures
        ({
            let y = spec_year_from_time(t);
            &&& spec_day_from_year(y) <= spec_day(t)
            &&& spec_day(t) < spec_day_from_year(y + 1)
            &&& spec_time_from_year(y) <= t
            &&& t < spec_time_from_year(y + 1)
            &&& 0 <= spec_day_within_year(t)
            &&& spec_day_within_year(t) < spec_days_in_year(y)
        }),
{
    let y = spec_year_from_time(t);
    lemma_day_from_year_step(y);
}

/// Uniqueness of `YearFromTime(t)`: for any integer `y2`, `TimeFromYear(y2) <= t <==> y2 <= YearFromTime(t)`.
pub proof fn lemma_year_from_time_largest(t: int, y2: int)
    ensures
        (spec_time_from_year(y2) <= t) <==> (y2 <= spec_year_from_time(t)),
{
    lemma_year_from_time_characterization(t);
    let y = spec_year_from_time(t);
    if y2 < y {
        lemma_day_from_year_monotonic(y2, y);
    } else if y2 > y {
        if y2 > y + 1 {
            lemma_day_from_year_monotonic(y + 1, y2);
        }
    }
}

#[verifier::spinoff_prover]
proof fn lemma_time_within_day_roundtrip(t: int)
    ensures
        0 <= spec_hour_from_time(t) && spec_hour_from_time(t) <= 23,
        0 <= spec_min_from_time(t) && spec_min_from_time(t) <= 59,
        0 <= spec_sec_from_time(t) && spec_sec_from_time(t) <= 59,
        0 <= spec_ms_from_time(t) && spec_ms_from_time(t) <= 999,
        spec_make_time(
            spec_hour_from_time(t),
            spec_min_from_time(t),
            spec_sec_from_time(t),
            spec_ms_from_time(t),
        ) == spec_time_within_day(t),
        spec_make_date(spec_day(t), spec_time_within_day(t)) == t,
{
    let qs = t / 1_000;
    let ms = t % 1_000;
    assert(t == qs * 1_000 + ms);
    let qm = qs / 60;
    let sc = qs % 60;
    assert(qm == t / 60_000 && qs == qm * 60 + sc);
    let qh = qm / 60;
    let mn = qm % 60;
    assert(qh == t / 3_600_000 && qm == qh * 60 + mn);
    let qd = qh / 24;
    let hr = qh % 24;
    assert(qd == t / 86_400_000 && qh == qd * 24 + hr);
    let twd = hr * 3_600_000 + mn * 60_000 + sc * 1_000 + ms;
    assert(0 <= twd && twd < 86_400_000);
    assert(t == qd * 86_400_000 + twd);
    assert(t % 86_400_000 == twd);
}

proof fn lemma_date_within_year_roundtrip(t: int)
    ensures
        0 <= spec_month_from_time(t) && spec_month_from_time(t) <= 11,
        1 <= spec_date_from_time(t)
            && spec_date_from_time(t)
                <= spec_days_in_month(spec_month_from_time(t), spec_in_leap_year(t)),
        spec_make_day(
            spec_year_from_time(t),
            spec_month_from_time(t),
            spec_date_from_time(t),
        ) == spec_day(t),
{
    lemma_year_from_time_characterization(t);
    let m = spec_month_from_time(t);
    assert(m / 12 == 0);
    assert(m % 12 == m);
}

/// Exact calendar component bounds and full reconstruction `MakeDate(MakeDay(...), MakeTime(...)) == t`!
#[verifier::spinoff_prover]
pub proof fn lemma_calendar_decomposition_roundtrip(t: int)
    ensures
        ({
            let y = spec_year_from_time(t);
            let leap = spec_in_leap_year(t);
            let m = spec_month_from_time(t);
            let dt = spec_date_from_time(t);
            let hr = spec_hour_from_time(t);
            let mn = spec_min_from_time(t);
            let sc = spec_sec_from_time(t);
            let ms = spec_ms_from_time(t);
            &&& 0 <= m && m <= 11
            &&& 1 <= dt && dt <= spec_days_in_month(m, leap)
            &&& 0 <= hr && hr <= 23
            &&& 0 <= mn && mn <= 59
            &&& 0 <= sc && sc <= 59
            &&& 0 <= ms && ms <= 999
            &&& spec_make_day(y, m, dt) == spec_day(t)
            &&& spec_make_time(hr, mn, sc, ms) == spec_time_within_day(t)
            &&& spec_make_date(spec_make_day(y, m, dt), spec_make_time(hr, mn, sc, ms)) == t
        }),
{
    lemma_time_within_day_roundtrip(t);
    lemma_date_within_year_roundtrip(t);
}

proof fn lemma_make_time_recovers_hms(d: int, hr: int, mn: int, sc: int, ms: int)
    requires
        0 <= hr && hr <= 23,
        0 <= mn && mn <= 59,
        0 <= sc && sc <= 59,
        0 <= ms && ms <= 999,
    ensures
        ({
            let tv = spec_make_date(d, spec_make_time(hr, mn, sc, ms));
            &&& spec_day(tv) == d
            &&& spec_hour_from_time(tv) == hr
            &&& spec_min_from_time(tv) == mn
            &&& spec_sec_from_time(tv) == sc
            &&& spec_ms_from_time(tv) == ms
        }),
{
    let tm = spec_make_time(hr, mn, sc, ms);
    assert(0 <= tm && tm < MS_PER_DAY as int);
    let tv = spec_make_date(d, tm);
    assert(tv == (d * 24 + hr) * 3_600_000 + mn * 60_000 + sc * 1_000 + ms);
    assert(tv / 86_400_000 == d);
    assert(tv / 3_600_000 == d * 24 + hr);
    assert((d * 24 + hr) % 24 == hr);
    assert(tv == ((d * 24 + hr) * 60 + mn) * 60_000 + sc * 1_000 + ms);
    assert(tv / 60_000 == (d * 24 + hr) * 60 + mn);
    assert(((d * 24 + hr) * 60 + mn) % 60 == mn);
    assert(tv == (((d * 24 + hr) * 60 + mn) * 60 + sc) * 1_000 + ms);
    assert(tv / 1_000 == ((d * 24 + hr) * 60 + mn) * 60 + sc);
    assert((((d * 24 + hr) * 60 + mn) * 60 + sc) % 60 == sc);
    assert(tv % 1_000 == ms);
}

proof fn lemma_make_day_recovers_ymd(y: int, m: int, dt: int, tv: int)
    requires
        0 <= m && m <= 11,
        1 <= dt && dt <= spec_days_in_month(m, if spec_is_leap_year_num(y) { 1 } else { 0 }),
        spec_day(tv) == spec_make_day(y, m, dt),
    ensures
        spec_year_from_time(tv) == y,
        spec_month_from_time(tv) == m,
        spec_date_from_time(tv) == dt,
{
    assert(m / 12 == 0);
    assert(m % 12 == m);
    let d = spec_make_day(y, m, dt);
    lemma_day_from_year_step(y);
    assert(spec_day_from_year(y) <= d && d < spec_day_from_year(y + 1));
    lemma_year_from_time_characterization(tv);
    let y_got = spec_year_from_time(tv);
    if y_got < y {
        if y_got + 1 < y {
            lemma_day_from_year_monotonic(y_got + 1, y);
        }
    } else if y_got > y {
        if y + 1 < y_got {
            lemma_day_from_year_monotonic(y + 1, y_got);
        }
    }
    assert(spec_year_from_time(tv) == y);
    assert(spec_day_within_year(tv) == spec_month_start_day(m, if spec_is_leap_year_num(y) { 1 } else { 0 }) + dt - 1);
}

/// Inverse calendar theorem: for any valid `(y, m, dt)` with `0 <= m <= 11` and `1 <= dt <= days_in_month(m, leap)`
/// and valid `(hr, mn, sc, ms)`, `YearFromTime/MonthFromTime/DateFromTime/HourFromTime/...` recover the exact fields!
#[verifier::spinoff_prover]
pub proof fn lemma_make_date_recovers_fields(
    y: int,
    m: int,
    dt: int,
    hr: int,
    mn: int,
    sc: int,
    ms: int,
)
    requires
        0 <= m && m <= 11,
        1 <= dt && dt <= spec_days_in_month(m, if spec_is_leap_year_num(y) { 1 } else { 0 }),
        0 <= hr && hr <= 23,
        0 <= mn && mn <= 59,
        0 <= sc && sc <= 59,
        0 <= ms && ms <= 999,
    ensures
        ({
            let tv = spec_make_date(spec_make_day(y, m, dt), spec_make_time(hr, mn, sc, ms));
            &&& spec_year_from_time(tv) == y
            &&& spec_month_from_time(tv) == m
            &&& spec_date_from_time(tv) == dt
            &&& spec_hour_from_time(tv) == hr
            &&& spec_min_from_time(tv) == mn
            &&& spec_sec_from_time(tv) == sc
            &&& spec_ms_from_time(tv) == ms
        }),
{
    let d = spec_make_day(y, m, dt);
    let tv = spec_make_date(d, spec_make_time(hr, mn, sc, ms));
    lemma_make_time_recovers_hms(d, hr, mn, sc, ms);
    lemma_make_day_recovers_ymd(y, m, dt, tv);
}

/// Clipped time bounds: `|tv| <= 8.64e15` implies `-271821 <= YearFromTime(tv) <= 275760`.
pub proof fn lemma_clipped_year_bounds(tv: int)
    requires
        spec_time_clip(tv).is_some(),
    ensures
        -271_821 <= spec_year_from_time(tv) && spec_year_from_time(tv) <= 275_760,
        spec_time_clip(spec_time_clip(tv).unwrap()) == Some(tv),
{
    lemma_year_from_time_characterization(tv);
}

// =======================================================================================
// 3. Exec Implementations of §21.4 Calendar Equations (`exec == spec`)
// =======================================================================================

/// Exec §21.4.1.2 `Day ( t )`.
pub fn day(t: i64) -> (d: i64)
    requires
        t > i64::MIN,
    ensures
        d as int == spec_day(t as int),
{
    floor_div_i64(t, MS_PER_DAY)
}

/// Exec §21.4.1.2 `TimeWithinDay ( t )`.
pub fn time_within_day(t: i64) -> (twd: i64)
    requires
        t > i64::MIN,
    ensures
        twd as int == spec_time_within_day(t as int),
        0 <= twd < MS_PER_DAY,
{
    modulo_i64(t, MS_PER_DAY)
}

/// Exec §21.4.1.3 `DaysInYear ( y )`.
pub fn days_in_year(y: i64) -> (days: i64)
    requires
        y > i64::MIN,
    ensures
        days as int == spec_days_in_year(y as int),
        days == 365 || days == 366,
{
    let m4 = modulo_i64(y, 4);
    let m100 = modulo_i64(y, 100);
    let m400 = modulo_i64(y, 400);
    if (m4 == 0 && m100 != 0) || m400 == 0 {
        366
    } else {
        365
    }
}

/// Exec §21.4.1.3 `DayFromYear ( y )`.
pub fn day_from_year(y: i64) -> (d: i64)
    requires
        -MAX_SAFE_YEAR_ABS <= y && y <= MAX_SAFE_YEAR_ABS,
    ensures
        d as int == spec_day_from_year(y as int),
{
    let c1 = 365i64 * (y - 1970i64);
    let c2 = floor_div_i64(y - 1969i64, 4);
    let c3 = floor_div_i64(y - 1901i64, 100);
    let c4 = floor_div_i64(y - 1601i64, 400);
    c1 + c2 - c3 + c4
}

/// Exec §21.4.1.3 `TimeFromYear ( y )`.
pub fn time_from_year(y: i64) -> (tv: i64)
    requires
        -MAX_SAFE_YEAR_ABS <= y && y <= MAX_SAFE_YEAR_ABS,
    ensures
        tv as int == spec_time_from_year(y as int),
{
    let dfy = day_from_year(y);
    MS_PER_DAY * dfy
}

/// Exec §21.4.1.3 `YearFromTime ( t )` proved equal to `spec_year_from_time` and satisfying
/// `TimeFromYear(y) <= t < TimeFromYear(y + 1)`.
pub fn year_from_time(t: i64) -> (y: i64)
    requires
        -(MAX_TIME_MS * 100) <= t && t <= MAX_TIME_MS * 100,
    ensures
        y as int == spec_year_from_time(t as int),
        spec_time_from_year(y as int) <= t as int,
        (t as int) < spec_time_from_year(y as int + 1),
{
    proof {
        lemma_year_from_time_characterization(t as int);
    }
    let d = day(t);
    let y0 = 1970i64 + floor_div_i64(400i64 * d, 146_097i64);
    if d >= day_from_year(y0 + 1) {
        y0 + 1
    } else if d >= day_from_year(y0) {
        y0
    } else {
        y0 - 1
    }
}

/// Exec §21.4.1.3 `InLeapYear ( t )`.
pub fn in_leap_year(t: i64) -> (leap: i64)
    requires
        -(MAX_TIME_MS * 100) <= t && t <= MAX_TIME_MS * 100,
    ensures
        leap as int == spec_in_leap_year(t as int),
        leap == 0 || leap == 1,
{
    let y = year_from_time(t);
    if days_in_year(y) == 366 {
        1
    } else {
        0
    }
}

/// Exec §21.4.1.4 `DayWithinYear ( t )`.
pub fn day_within_year(t: i64) -> (dwy: i64)
    requires
        -(MAX_TIME_MS * 100) <= t && t <= MAX_TIME_MS * 100,
    ensures
        dwy as int == spec_day_within_year(t as int),
        0 <= dwy < 366,
{
    proof {
        lemma_year_from_time_characterization(t as int);
    }
    let d = day(t);
    let y = year_from_time(t);
    d - day_from_year(y)
}

/// Exec §21.4.1.4 `MonthFromTime ( t )`.
pub fn month_from_time(t: i64) -> (m: i64)
    requires
        -(MAX_TIME_MS * 100) <= t && t <= MAX_TIME_MS * 100,
    ensures
        m as int == spec_month_from_time(t as int),
        0 <= m <= 11,
{
    let d = day_within_year(t);
    let leap = in_leap_year(t);
    if d < 31 {
        0
    } else if d < 59 + leap {
        1
    } else if d < 90 + leap {
        2
    } else if d < 120 + leap {
        3
    } else if d < 151 + leap {
        4
    } else if d < 181 + leap {
        5
    } else if d < 212 + leap {
        6
    } else if d < 243 + leap {
        7
    } else if d < 273 + leap {
        8
    } else if d < 304 + leap {
        9
    } else if d < 334 + leap {
        10
    } else {
        11
    }
}

/// Exec §21.4.1.5 `DateFromTime ( t )`.
pub fn date_from_time(t: i64) -> (dt: i64)
    requires
        -(MAX_TIME_MS * 100) <= t && t <= MAX_TIME_MS * 100,
    ensures
        dt as int == spec_date_from_time(t as int),
        1 <= dt <= 31,
{
    proof {
        lemma_calendar_decomposition_roundtrip(t as int);
    }
    let d = day_within_year(t);
    let leap = in_leap_year(t);
    let m = month_from_time(t);
    if m == 0 {
        d + 1
    } else if m == 1 {
        d - 30
    } else if m == 2 {
        d - 58 - leap
    } else if m == 3 {
        d - 89 - leap
    } else if m == 4 {
        d - 119 - leap
    } else if m == 5 {
        d - 150 - leap
    } else if m == 6 {
        d - 180 - leap
    } else if m == 7 {
        d - 211 - leap
    } else if m == 8 {
        d - 242 - leap
    } else if m == 9 {
        d - 272 - leap
    } else if m == 10 {
        d - 303 - leap
    } else {
        d - 333 - leap
    }
}

/// Exec §21.4.1.6 `WeekDay ( t )`.
pub fn week_day(t: i64) -> (wd: i64)
    requires
        -(MAX_TIME_MS * 100) <= t && t <= MAX_TIME_MS * 100,
    ensures
        wd as int == spec_week_day(t as int),
        0 <= wd < 7,
{
    let d = day(t);
    modulo_i64(d + 4, 7)
}

/// Exec §21.4.1.11 `HourFromTime ( t )`.
pub fn hour_from_time(t: i64) -> (hr: i64)
    requires
        t > i64::MIN,
    ensures
        hr as int == spec_hour_from_time(t as int),
        0 <= hr < 24,
{
    let h = floor_div_i64(t, MS_PER_HOUR);
    modulo_i64(h, HOURS_PER_DAY)
}

/// Exec §21.4.1.11 `MinFromTime ( t )`.
pub fn min_from_time(t: i64) -> (mn: i64)
    requires
        t > i64::MIN,
    ensures
        mn as int == spec_min_from_time(t as int),
        0 <= mn < 60,
{
    let m = floor_div_i64(t, MS_PER_MINUTE);
    modulo_i64(m, MINUTES_PER_HOUR)
}

/// Exec §21.4.1.11 `SecFromTime ( t )`.
pub fn sec_from_time(t: i64) -> (sc: i64)
    requires
        t > i64::MIN,
    ensures
        sc as int == spec_sec_from_time(t as int),
        0 <= sc < 60,
{
    let s = floor_div_i64(t, MS_PER_SECOND);
    modulo_i64(s, SECONDS_PER_MINUTE)
}

/// Exec §21.4.1.11 `msFromTime ( t )`.
pub fn ms_from_time(t: i64) -> (ms: i64)
    requires
        t > i64::MIN,
    ensures
        ms as int == spec_ms_from_time(t as int),
        0 <= ms < 1000,
{
    modulo_i64(t, MS_PER_SECOND)
}

/// Exec §21.4.1.12 `MakeTime ( hour, min, sec, ms )`.
pub fn make_time(hour: i64, min: i64, sec: i64, ms: i64) -> (res: Option<i64>)
    ensures
        (hour >= -1_000_000_000 && hour <= 1_000_000_000
            && min >= -1_000_000_000 && min <= 1_000_000_000
            && sec >= -1_000_000_000 && sec <= 1_000_000_000
            && ms >= -1_000_000_000_000 && ms <= 1_000_000_000_000)
            ==> res == Some(spec_make_time(hour as int, min as int, sec as int, ms as int) as i64),
        res.is_some()
            ==> res.unwrap() as int == spec_make_time(hour as int, min as int, sec as int, ms as int),
{
    if hour < -1_000_000_000 || hour > 1_000_000_000
        || min < -1_000_000_000 || min > 1_000_000_000
        || sec < -1_000_000_000 || sec > 1_000_000_000
        || ms < -1_000_000_000_000 || ms > 1_000_000_000_000
    {
        None
    } else {
        Some(hour * MS_PER_HOUR + min * MS_PER_MINUTE + sec * MS_PER_SECOND + ms)
    }
}

fn month_start_day_exec(m: i64, leap: i64) -> (d: i64)
    requires
        0 <= m <= 11,
        leap == 0 || leap == 1,
    ensures
        d as int == spec_month_start_day(m as int, leap as int),
{
    if m == 0 {
        0
    } else if m == 1 {
        31
    } else if m == 2 {
        59 + leap
    } else if m == 3 {
        90 + leap
    } else if m == 4 {
        120 + leap
    } else if m == 5 {
        151 + leap
    } else if m == 6 {
        181 + leap
    } else if m == 7 {
        212 + leap
    } else if m == 8 {
        243 + leap
    } else if m == 9 {
        273 + leap
    } else if m == 10 {
        304 + leap
    } else {
        334 + leap
    }
}

fn days_in_month_exec(m: i64, leap: i64) -> (d: i64)
    requires
        0 <= m <= 11,
        leap == 0 || leap == 1,
    ensures
        d as int == spec_days_in_month(m as int, leap as int),
{
    if m == 0 || m == 2 || m == 4 || m == 6 || m == 7 || m == 9 || m == 11 {
        31
    } else if m == 3 || m == 5 || m == 8 || m == 10 {
        30
    } else {
        28 + leap
    }
}

/// Exec §21.4.1.13 `MakeDay ( year, month, date )`.
pub fn make_day(year: i64, month: i64, date: i64) -> (res: Option<i64>)
    ensures
        (-100_000_000 <= year && year <= 100_000_000
            && -100_000_000 <= month && month <= 100_000_000
            && -100_000_000_000 <= date && date <= 100_000_000_000)
            ==> res == Some(spec_make_day(year as int, month as int, date as int) as i64),
        res.is_some()
            ==> res.unwrap() as int == spec_make_day(year as int, month as int, date as int),
{
    if year < -100_000_000 || year > 100_000_000
        || month < -100_000_000 || month > 100_000_000
        || date < -100_000_000_000 || date > 100_000_000_000
    {
        None
    } else {
        let ym = year + floor_div_i64(month, 12);
        let mn = modulo_i64(month, 12);
        let leap: i64 = if days_in_year(ym) == 366 { 1 } else { 0 };
        let dfy = day_from_year(ym);
        let msd = month_start_day_exec(mn, leap);
        Some(dfy + msd + date - 1)
    }
}

/// Exec §21.4.1.14 `MakeDate ( day, time )`.
pub fn make_date(day_num: i64, time_ms: i64) -> (res: Option<i64>)
    ensures
        (-1_000_000_000 <= day_num && day_num <= 1_000_000_000
            && -1_000_000_000_000_000 <= time_ms && time_ms <= 1_000_000_000_000_000)
            ==> res == Some(spec_make_date(day_num as int, time_ms as int) as i64),
        res.is_some()
            ==> res.unwrap() as int == spec_make_date(day_num as int, time_ms as int),
{
    if day_num < -1_000_000_000 || day_num > 1_000_000_000
        || time_ms < -1_000_000_000_000_000 || time_ms > 1_000_000_000_000_000
    {
        None
    } else {
        Some(day_num * MS_PER_DAY + time_ms)
    }
}

/// Exec §21.4.1.15 `TimeClip ( tv )`: enforces `|tv| <= 8.64e15`.
pub fn time_clip(tv: i64) -> (res: Option<i64>)
    ensures
        match res {
            Some(v) => spec_time_clip(tv as int) == Some(v as int) && -MAX_TIME_MS <= v && v <= MAX_TIME_MS,
            None => spec_time_clip(tv as int).is_none(),
        },
{
    if tv >= -MAX_TIME_MS && tv <= MAX_TIME_MS {
        Some(tv)
    } else {
        None
    }
}

// =======================================================================================
// 4. Verified ISO-8601 Date Time String Parser (§21.4.1.32) & `toISOString` (§21.4.4.36)
// =======================================================================================

/// True iff `c` is an ASCII decimal digit `'0'..='9'`.
pub open spec fn spec_is_digit(c: u16) -> bool {
    0x0030 <= c && c <= 0x0039
}

/// Numeric value `0..=9` of an ASCII digit.
pub open spec fn spec_digit_val(c: u16) -> int {
    (c - 0x0030) as int
}

/// ASCII digit code unit for `0 <= d < 10`.
#[verifier::opaque]
pub open spec fn spec_digit_char(d: int) -> u16 {
    (0x0030 + d) as u16
}

/// 2-digit zero-padded formatting (`0 <= n < 100`).
pub open spec fn spec_fmt2(n: int) -> Seq<u16> {
    seq![spec_digit_char(n / 10), spec_digit_char(n % 10)]
}

/// 3-digit zero-padded formatting (`0 <= n < 1000`).
pub open spec fn spec_fmt3(n: int) -> Seq<u16> {
    seq![
        spec_digit_char(n / 100),
        spec_digit_char((n / 10) % 10),
        spec_digit_char(n % 10),
    ]
}

/// 4-digit zero-padded formatting (`0 <= n < 10000`).
pub open spec fn spec_fmt4(n: int) -> Seq<u16> {
    seq![
        spec_digit_char(n / 1000),
        spec_digit_char((n / 100) % 10),
        spec_digit_char((n / 10) % 10),
        spec_digit_char(n % 10),
    ]
}

/// 6-digit zero-padded formatting (`0 <= n < 1000000`).
pub open spec fn spec_fmt6(n: int) -> Seq<u16> {
    seq![
        spec_digit_char(n / 100_000),
        spec_digit_char((n / 10_000) % 10),
        spec_digit_char((n / 1_000) % 10),
        spec_digit_char((n / 100) % 10),
        spec_digit_char((n / 10) % 10),
        spec_digit_char(n % 10),
    ]
}

/// Parse 2 ASCII digits at `s[pos..pos+2]`.
pub open spec fn spec_parse2(s: Seq<u16>, pos: int) -> Option<int> {
    if pos + 2 <= s.len() && spec_is_digit(s[pos]) && spec_is_digit(s[pos + 1]) {
        Some(spec_digit_val(s[pos]) * 10 + spec_digit_val(s[pos + 1]))
    } else {
        None
    }
}

/// Parse 4 ASCII digits at `s[pos..pos+4]`.
pub open spec fn spec_parse4(s: Seq<u16>, pos: int) -> Option<int> {
    if pos + 4 <= s.len()
        && spec_is_digit(s[pos])
        && spec_is_digit(s[pos + 1])
        && spec_is_digit(s[pos + 2])
        && spec_is_digit(s[pos + 3])
    {
        Some(
            spec_digit_val(s[pos]) * 1000
                + spec_digit_val(s[pos + 1]) * 100
                + spec_digit_val(s[pos + 2]) * 10
                + spec_digit_val(s[pos + 3]),
        )
    } else {
        None
    }
}

/// Parse 6 ASCII digits at `s[pos..pos+6]`.
pub open spec fn spec_parse6(s: Seq<u16>, pos: int) -> Option<int> {
    if pos + 6 <= s.len()
        && spec_is_digit(s[pos])
        && spec_is_digit(s[pos + 1])
        && spec_is_digit(s[pos + 2])
        && spec_is_digit(s[pos + 3])
        && spec_is_digit(s[pos + 4])
        && spec_is_digit(s[pos + 5])
    {
        Some(
            spec_digit_val(s[pos]) * 100_000
                + spec_digit_val(s[pos + 1]) * 10_000
                + spec_digit_val(s[pos + 2]) * 1_000
                + spec_digit_val(s[pos + 3]) * 100
                + spec_digit_val(s[pos + 4]) * 10
                + spec_digit_val(s[pos + 5]),
        )
    } else {
        None
    }
}

/// Format pre-extracted fields `(y, m_0_11, dt, hr, mn, sc, ms)` into canonical ISO-8601 UTC string.
pub open spec fn spec_format_iso_fields(
    y: int,
    m: int,
    dt: int,
    hr: int,
    mn: int,
    sc: int,
    ms: int,
) -> Seq<u16> {
    let mm = m + 1;
    if y < 0 {
        let ay = -y;
        seq![
            0x002Du16,
            spec_digit_char(ay / 100_000),
            spec_digit_char((ay / 10_000) % 10),
            spec_digit_char((ay / 1_000) % 10),
            spec_digit_char((ay / 100) % 10),
            spec_digit_char((ay / 10) % 10),
            spec_digit_char(ay % 10),
            0x002Du16,
            spec_digit_char(mm / 10),
            spec_digit_char(mm % 10),
            0x002Du16,
            spec_digit_char(dt / 10),
            spec_digit_char(dt % 10),
            0x0054u16,
            spec_digit_char(hr / 10),
            spec_digit_char(hr % 10),
            0x003Au16,
            spec_digit_char(mn / 10),
            spec_digit_char(mn % 10),
            0x003Au16,
            spec_digit_char(sc / 10),
            spec_digit_char(sc % 10),
            0x002Eu16,
            spec_digit_char(ms / 100),
            spec_digit_char((ms / 10) % 10),
            spec_digit_char(ms % 10),
            0x005Au16,
        ]
    } else if y > 9999 {
        seq![
            0x002Bu16,
            spec_digit_char(y / 100_000),
            spec_digit_char((y / 10_000) % 10),
            spec_digit_char((y / 1_000) % 10),
            spec_digit_char((y / 100) % 10),
            spec_digit_char((y / 10) % 10),
            spec_digit_char(y % 10),
            0x002Du16,
            spec_digit_char(mm / 10),
            spec_digit_char(mm % 10),
            0x002Du16,
            spec_digit_char(dt / 10),
            spec_digit_char(dt % 10),
            0x0054u16,
            spec_digit_char(hr / 10),
            spec_digit_char(hr % 10),
            0x003Au16,
            spec_digit_char(mn / 10),
            spec_digit_char(mn % 10),
            0x003Au16,
            spec_digit_char(sc / 10),
            spec_digit_char(sc % 10),
            0x002Eu16,
            spec_digit_char(ms / 100),
            spec_digit_char((ms / 10) % 10),
            spec_digit_char(ms % 10),
            0x005Au16,
        ]
    } else {
        seq![
            spec_digit_char(y / 1000),
            spec_digit_char((y / 100) % 10),
            spec_digit_char((y / 10) % 10),
            spec_digit_char(y % 10),
            0x002Du16,
            spec_digit_char(mm / 10),
            spec_digit_char(mm % 10),
            0x002Du16,
            spec_digit_char(dt / 10),
            spec_digit_char(dt % 10),
            0x0054u16,
            spec_digit_char(hr / 10),
            spec_digit_char(hr % 10),
            0x003Au16,
            spec_digit_char(mn / 10),
            spec_digit_char(mn % 10),
            0x003Au16,
            spec_digit_char(sc / 10),
            spec_digit_char(sc % 10),
            0x002Eu16,
            spec_digit_char(ms / 100),
            spec_digit_char((ms / 10) % 10),
            spec_digit_char(ms % 10),
            0x005Au16,
        ]
    }
}

/// ECMA-262 §21.4.4.36 `Date.prototype.toISOString ( )`:
/// returns `None` if `TimeClip(tv)` is `None`, else formats `YYYY-MM-DDTHH:mm:ss.sssZ`
/// (or `[+-]YYYYYY-MM-DDTHH:mm:ss.sssZ` for extended years `y < 0` or `y > 9999`).
pub open spec fn spec_to_iso_string(tv: int) -> Option<Seq<u16>> {
    match spec_time_clip(tv) {
        None => None,
        Some(t) => Some(
            spec_format_iso_fields(
                spec_year_from_time(t),
                spec_month_from_time(t),
                spec_date_from_time(t),
                spec_hour_from_time(t),
                spec_min_from_time(t),
                spec_sec_from_time(t),
                spec_ms_from_time(t),
            ),
        ),
    }
}

/// Parse year prefix (`YYYY` or `[+-]YYYYYY`, rejecting `-000000` per §21.4.1.32).
pub open spec fn spec_parse_iso_year(s: Seq<u16>) -> Option<(int, int)> {
    if s.len() == 0 {
        None
    } else if s[0] == 0x002Bu16 {
        match spec_parse6(s, 1) {
            Some(v) => Some((v, 7)),
            None => None,
        }
    } else if s[0] == 0x002Du16 {
        match spec_parse6(s, 1) {
            Some(v) => {
                if v == 0 {
                    None
                } else {
                    Some((-v, 7))
                }
            },
            None => None,
        }
    } else {
        match spec_parse4(s, 0) {
            Some(v) => Some((v, 4)),
            None => None,
        }
    }
}

/// Parse date prefix `YYYY[-MM[-DD]]` returning `(year, month_0_to_11, day_1_to_31, next_pos)`.
pub open spec fn spec_parse_iso_date(s: Seq<u16>) -> Option<(int, int, int, int)> {
    match spec_parse_iso_year(s) {
        None => None,
        Some((year, p1)) => {
            let leap = if spec_is_leap_year_num(year) { 1 } else { 0 };
            if p1 == s.len() {
                Some((year, 0, 1, p1))
            } else if s[p1] == 0x0054u16 {
                Some((year, 0, 1, p1))
            } else if s[p1] == 0x002Du16 {
                match spec_parse2(s, p1 + 1) {
                    None => None,
                    Some(mm) => {
                        if mm < 1 || mm > 12 {
                            None
                        } else {
                            let m = mm - 1;
                            let p2 = p1 + 3;
                            if p2 == s.len() || s[p2] == 0x0054u16 {
                                Some((year, m, 1, p2))
                            } else if s[p2] == 0x002Du16 {
                                match spec_parse2(s, p2 + 1) {
                                    None => None,
                                    Some(dd) => {
                                        if dd < 1 || dd > spec_days_in_month(m, leap) {
                                            None
                                        } else {
                                            Some((year, m, dd, p2 + 3))
                                        }
                                    },
                                }
                            } else {
                                None
                            }
                        }
                    },
                }
            } else {
                None
            }
        },
    }
}

/// Parse timezone suffix (`Z` or `+HH:mm` or `-HH:mm`) requiring exact end-of-string.
pub open spec fn spec_parse_iso_tz(s: Seq<u16>, pos: int) -> Option<int> {
    if pos >= s.len() {
        None
    } else if s[pos] == 0x005Au16 {
        if pos + 1 == s.len() {
            Some(0)
        } else {
            None
        }
    } else if s[pos] == 0x002Bu16 || s[pos] == 0x002Du16 {
        if pos + 6 != s.len() || s[pos + 3] != 0x003Au16 {
            None
        } else {
            match (spec_parse2(s, pos + 1), spec_parse2(s, pos + 4)) {
                (Some(oh), Some(om)) => {
                    if oh > 23 || om > 59 {
                        None
                    } else {
                        let off_ms = (oh * 60 + om) * (MS_PER_MINUTE as int);
                        if s[pos] == 0x002Bu16 {
                            Some(off_ms)
                        } else {
                            Some(-off_ms)
                        }
                    }
                },
                _ => None,
            }
        }
    } else {
        None
    }
}

/// Parse time + timezone suffix starting at `'T'` (`THH:mm[:ss[.s{1,3}]](Z|[+-]HH:mm)`).
pub open spec fn spec_parse_iso_time_and_tz(s: Seq<u16>, pos: int) -> Option<(int, int)> {
    if pos >= s.len() || s[pos] != 0x0054u16 {
        None
    } else if pos + 6 > s.len() || s[pos + 3] != 0x003Au16 {
        None
    } else {
        match (spec_parse2(s, pos + 1), spec_parse2(s, pos + 4)) {
            (Some(hr), Some(mn)) => {
                let p_after_hm = pos + 6;
                let sec_opt: Option<(int, int)> = if p_after_hm < s.len() && s[p_after_hm] == 0x003Au16 {
                    match spec_parse2(s, p_after_hm + 1) {
                        Some(sc) => Some((sc, p_after_hm + 3)),
                        None => None,
                    }
                } else {
                    Some((0, p_after_hm))
                };
                match sec_opt {
                    None => None,
                    Some((sc, p_after_s)) => {
                        let ms_opt: Option<(int, int)> = if p_after_s < s.len() && s[p_after_s] == 0x002Eu16 {
                            if p_after_s + 1 < s.len() && spec_is_digit(s[p_after_s + 1]) {
                                let d0 = spec_digit_val(s[p_after_s + 1]);
                                if p_after_s + 2 < s.len() && spec_is_digit(s[p_after_s + 2]) {
                                    let d1 = spec_digit_val(s[p_after_s + 2]);
                                    if p_after_s + 3 < s.len() && spec_is_digit(s[p_after_s + 3]) {
                                        let d2 = spec_digit_val(s[p_after_s + 3]);
                                        Some((d0 * 100 + d1 * 10 + d2, p_after_s + 4))
                                    } else {
                                        Some((d0 * 100 + d1 * 10, p_after_s + 3))
                                    }
                                } else {
                                    Some((d0 * 100, p_after_s + 2))
                                }
                            } else {
                                None
                            }
                        } else {
                            Some((0, p_after_s))
                        };
                        match ms_opt {
                            None => None,
                            Some((ms, p_tz)) => {
                                let valid_hms = (hr <= 23 && mn <= 59 && sc <= 59 && ms <= 999)
                                    || (hr == 24 && mn == 0 && sc == 0 && ms == 0);
                                if !valid_hms {
                                    None
                                } else {
                                    match spec_parse_iso_tz(s, p_tz) {
                                        Some(off_ms) => Some((spec_make_time(hr, mn, sc, ms), off_ms)),
                                        None => None,
                                    }
                                }
                            },
                        }
                    },
                }
            },
            _ => None,
        }
    }
}

/// ECMA-262 §21.4.1.32 / §21.4.3.2 ISO-8601 Date Time String parser:
/// parses UTC date-only and date-time strings (`Z` or `±HH:mm`) and applies `TimeClip`.
pub open spec fn spec_parse_iso8601(s: Seq<u16>) -> Option<int> {
    match spec_parse_iso_date(s) {
        None => None,
        Some((year, month, dt, pos)) => {
            let day_num = spec_make_day(year, month, dt);
            if pos == s.len() {
                spec_time_clip(spec_make_date(day_num, 0))
            } else {
                match spec_parse_iso_time_and_tz(s, pos) {
                    None => None,
                    Some((time_ms, off_ms)) => {
                        spec_time_clip(spec_make_date(day_num, time_ms) - off_ms)
                    },
                }
            }
        },
    }
}

// =======================================================================================
// 5. Valid-Date ISO-8601 Roundtrip & Bounds Theorems
// =======================================================================================

proof fn lemma_digit_char_val(d: int)
    requires
        0 <= d && d < 10,
    ensures
        spec_is_digit(spec_digit_char(d)),
        spec_digit_val(spec_digit_char(d)) == d,
{
    reveal(spec_digit_char);
}

proof fn lemma_fmt2_at(s: Seq<u16>, pos: int, n: int)
    requires
        0 <= n && n < 100,
        0 <= pos && pos + 2 <= s.len(),
        s[pos] == spec_digit_char(n / 10),
        s[pos + 1] == spec_digit_char(n % 10),
    ensures
        spec_parse2(s, pos) == Some(n),
{
    lemma_digit_char_val(n / 10);
    lemma_digit_char_val(n % 10);
}

proof fn lemma_fmt4_at(s: Seq<u16>, pos: int, n: int)
    requires
        0 <= n && n < 10_000,
        0 <= pos && pos + 4 <= s.len(),
        s[pos] == spec_digit_char(n / 1000),
        s[pos + 1] == spec_digit_char((n / 100) % 10),
        s[pos + 2] == spec_digit_char((n / 10) % 10),
        s[pos + 3] == spec_digit_char(n % 10),
    ensures
        spec_parse4(s, pos) == Some(n),
{
    let d0 = n / 1000;
    let d1 = (n / 100) % 10;
    let d2 = (n / 10) % 10;
    let d3 = n % 10;
    lemma_digit_char_val(d0);
    lemma_digit_char_val(d1);
    lemma_digit_char_val(d2);
    lemma_digit_char_val(d3);
    assert(d0 * 1000 + d1 * 100 + d2 * 10 + d3 == n);
}

proof fn lemma_fmt6_at(s: Seq<u16>, pos: int, n: int)
    requires
        0 <= n && n < 1_000_000,
        0 <= pos && pos + 6 <= s.len(),
        s[pos] == spec_digit_char(n / 100_000),
        s[pos + 1] == spec_digit_char((n / 10_000) % 10),
        s[pos + 2] == spec_digit_char((n / 1_000) % 10),
        s[pos + 3] == spec_digit_char((n / 100) % 10),
        s[pos + 4] == spec_digit_char((n / 10) % 10),
        s[pos + 5] == spec_digit_char(n % 10),
    ensures
        spec_parse6(s, pos) == Some(n),
{
    let q1 = n / 10;
    let d5 = n % 10;
    assert(q1 == n / 10 && n == q1 * 10 + d5);
    let q2 = q1 / 10;
    let d4 = q1 % 10;
    assert(q2 == n / 100 && d4 == (n / 10) % 10 && q1 == q2 * 10 + d4);
    let q3 = q2 / 10;
    let d3 = q2 % 10;
    assert(q3 == n / 1_000 && d3 == (n / 100) % 10 && q2 == q3 * 10 + d3);
    let q4 = q3 / 10;
    let d2 = q3 % 10;
    assert(q4 == n / 10_000 && d2 == (n / 1_000) % 10 && q3 == q4 * 10 + d2);
    let d0 = q4 / 10;
    let d1 = q4 % 10;
    assert(d0 == n / 100_000 && d1 == (n / 10_000) % 10 && q4 == d0 * 10 + d1);
    lemma_digit_char_val(d0);
    lemma_digit_char_val(d1);
    lemma_digit_char_val(d2);
    lemma_digit_char_val(d3);
    lemma_digit_char_val(d4);
    lemma_digit_char_val(d5);
    assert(d0 * 100_000 + d1 * 10_000 + d2 * 1_000 + d3 * 100 + d4 * 10 + d5 == n);
}

proof fn lemma_fmt3_ms_at(s: Seq<u16>, pos: int, ms: int)
    requires
        0 <= ms && ms < 1000,
        0 <= pos && pos + 5 == s.len(),
        s[pos] == 0x002Eu16,
        s[pos + 1] == spec_digit_char(ms / 100),
        s[pos + 2] == spec_digit_char((ms / 10) % 10),
        s[pos + 3] == spec_digit_char(ms % 10),
        s[pos + 4] == 0x005Au16,
    ensures
        spec_is_digit(s[pos + 1]),
        spec_is_digit(s[pos + 2]),
        spec_is_digit(s[pos + 3]),
        spec_digit_val(s[pos + 1]) * 100
            + spec_digit_val(s[pos + 2]) * 10
            + spec_digit_val(s[pos + 3]) == ms,
        spec_parse_iso_tz(s, pos + 4) == Some(0int),
{
    let d0 = ms / 100;
    let d1 = (ms / 10) % 10;
    let d2 = ms % 10;
    lemma_digit_char_val(d0);
    lemma_digit_char_val(d1);
    lemma_digit_char_val(d2);
    assert(d0 * 100 + d1 * 10 + d2 == ms);
}

#[verifier::spinoff_prover]
proof fn lemma_format_iso_date_part(
    y: int,
    m: int,
    dt: int,
    hr: int,
    mn: int,
    sc: int,
    ms: int,
)
    requires
        -999_999 <= y && y <= 999_999,
        0 <= m && m <= 11,
        1 <= dt && dt <= spec_days_in_month(m, if spec_is_leap_year_num(y) { 1 } else { 0 }),
    ensures
        ({
            let iso = spec_format_iso_fields(y, m, dt, hr, mn, sc, ms);
            let tpos: int = if y < 0 || y > 9999 { 13int } else { 10int };
            &&& iso.len() == tpos + 14
            &&& spec_parse_iso_date(iso) == Some((y, m, dt, tpos))
        }),
{
    let iso = spec_format_iso_fields(y, m, dt, hr, mn, sc, ms);
    if y < 0 {
        assert(iso.len() == 27);
        lemma_fmt6_at(iso, 1, -y);
        assert(spec_parse_iso_year(iso) == Some((y, 7int)));
        lemma_fmt2_at(iso, 8, m + 1);
        lemma_fmt2_at(iso, 11, dt);
    } else if y > 9999 {
        assert(iso.len() == 27);
        lemma_fmt6_at(iso, 1, y);
        assert(spec_parse_iso_year(iso) == Some((y, 7int)));
        lemma_fmt2_at(iso, 8, m + 1);
        lemma_fmt2_at(iso, 11, dt);
    } else {
        assert(iso.len() == 24);
        lemma_fmt4_at(iso, 0, y);
        assert(spec_parse_iso_year(iso) == Some((y, 4int)));
        lemma_fmt2_at(iso, 5, m + 1);
        lemma_fmt2_at(iso, 8, dt);
    }
}

#[verifier::spinoff_prover]
proof fn lemma_format_iso_time_part(
    y: int,
    m: int,
    dt: int,
    hr: int,
    mn: int,
    sc: int,
    ms: int,
)
    requires
        0 <= hr && hr <= 23,
        0 <= mn && mn <= 59,
        0 <= sc && sc <= 59,
        0 <= ms && ms <= 999,
    ensures
        ({
            let iso = spec_format_iso_fields(y, m, dt, hr, mn, sc, ms);
            let tpos: int = if y < 0 || y > 9999 { 13int } else { 10int };
            spec_parse_iso_time_and_tz(iso, tpos) == Some((spec_make_time(hr, mn, sc, ms), 0int))
        }),
{
    let iso = spec_format_iso_fields(y, m, dt, hr, mn, sc, ms);
    if y < 0 {
        assert(iso.len() == 27);
        lemma_fmt2_at(iso, 14, hr);
        lemma_fmt2_at(iso, 17, mn);
        lemma_fmt2_at(iso, 20, sc);
        lemma_fmt3_ms_at(iso, 22, ms);
    } else if y > 9999 {
        assert(iso.len() == 27);
        lemma_fmt2_at(iso, 14, hr);
        lemma_fmt2_at(iso, 17, mn);
        lemma_fmt2_at(iso, 20, sc);
        lemma_fmt3_ms_at(iso, 22, ms);
    } else {
        assert(iso.len() == 24);
        lemma_fmt2_at(iso, 11, hr);
        lemma_fmt2_at(iso, 14, mn);
        lemma_fmt2_at(iso, 17, sc);
        lemma_fmt3_ms_at(iso, 19, ms);
    }
}

#[verifier::spinoff_prover]
proof fn lemma_format_iso_fields_roundtrip(
    y: int,
    m: int,
    dt: int,
    hr: int,
    mn: int,
    sc: int,
    ms: int,
)
    requires
        -999_999 <= y && y <= 999_999,
        0 <= m && m <= 11,
        1 <= dt && dt <= spec_days_in_month(m, if spec_is_leap_year_num(y) { 1 } else { 0 }),
        0 <= hr && hr <= 23,
        0 <= mn && mn <= 59,
        0 <= sc && sc <= 59,
        0 <= ms && ms <= 999,
    ensures
        ({
            let iso = spec_format_iso_fields(y, m, dt, hr, mn, sc, ms);
            let raw = spec_make_date(spec_make_day(y, m, dt), spec_make_time(hr, mn, sc, ms));
            spec_parse_iso8601(iso) == spec_time_clip(raw)
        }),
{
    lemma_format_iso_date_part(y, m, dt, hr, mn, sc, ms);
    lemma_format_iso_time_part(y, m, dt, hr, mn, sc, ms);
}

/// Main ISO-8601 Roundtrip & `TimeClip` Theorem:
/// 1. Every timestamp accepted by `spec_parse_iso8601` satisfies `|tv| <= 8.64e15`.
/// 2. Every valid timestamp `tv` (`|tv| <= 8.64e15`) serializes via `spec_to_iso_string(tv)` to a
///    canonical ISO-8601 string `iso` whose `spec_parse_iso8601(iso)` recovers `Some(tv)`!
#[verifier::spinoff_prover]
pub proof fn lemma_iso8601_roundtrip(tv: int)
    requires
        spec_time_clip(tv).is_some(),
    ensures
        spec_to_iso_string(tv).is_some(),
        spec_parse_iso8601(spec_to_iso_string(tv).unwrap()) == Some(tv),
{
    lemma_clipped_year_bounds(tv);
    lemma_calendar_decomposition_roundtrip(tv);
    let y = spec_year_from_time(tv);
    let m = spec_month_from_time(tv);
    let dt = spec_date_from_time(tv);
    let hr = spec_hour_from_time(tv);
    let mn = spec_min_from_time(tv);
    let sc = spec_sec_from_time(tv);
    let ms = spec_ms_from_time(tv);
    lemma_format_iso_fields_roundtrip(y, m, dt, hr, mn, sc, ms);
}

/// Every parsed ISO-8601 date-time respects `TimeClip` bounds (`|tv| <= 8.64e15`).
pub proof fn lemma_parse_iso8601_clipped(s: Seq<u16>)
    ensures
        match spec_parse_iso8601(s) {
            Some(tv) => -(MAX_TIME_MS as int) <= tv && tv <= (MAX_TIME_MS as int),
            None => true,
        },
{
}

// =======================================================================================
// 6. Exec ISO-8601 Serializer & Parser (`exec == spec`)
// =======================================================================================

fn push_fmt2(out: &mut Vec<u16>, n: i64)
    requires
        0 <= n < 100,
    ensures
        final(out)@ == old(out)@ + spec_fmt2(n as int),
{
    out.push((0x0030 + (n / 10)) as u16);
    out.push((0x0030 + (n % 10)) as u16);
    proof {
        reveal(spec_digit_char);
        assert(out@ =~= old(out)@ + spec_fmt2(n as int));
    }
}

fn push_fmt3(out: &mut Vec<u16>, n: i64)
    requires
        0 <= n < 1000,
    ensures
        final(out)@ == old(out)@ + spec_fmt3(n as int),
{
    out.push((0x0030 + (n / 100)) as u16);
    out.push((0x0030 + ((n / 10) % 10)) as u16);
    out.push((0x0030 + (n % 10)) as u16);
    proof {
        reveal(spec_digit_char);
        assert(out@ =~= old(out)@ + spec_fmt3(n as int));
    }
}

fn push_fmt4(out: &mut Vec<u16>, n: i64)
    requires
        0 <= n < 10_000,
    ensures
        final(out)@ == old(out)@ + spec_fmt4(n as int),
{
    out.push((0x0030 + (n / 1000)) as u16);
    out.push((0x0030 + ((n / 100) % 10)) as u16);
    out.push((0x0030 + ((n / 10) % 10)) as u16);
    out.push((0x0030 + (n % 10)) as u16);
    proof {
        reveal(spec_digit_char);
        assert(out@ =~= old(out)@ + spec_fmt4(n as int));
    }
}

fn push_fmt6(out: &mut Vec<u16>, n: i64)
    requires
        0 <= n < 1_000_000,
    ensures
        final(out)@ == old(out)@ + spec_fmt6(n as int),
{
    out.push((0x0030 + (n / 100_000)) as u16);
    out.push((0x0030 + ((n / 10_000) % 10)) as u16);
    out.push((0x0030 + ((n / 1_000) % 10)) as u16);
    out.push((0x0030 + ((n / 100) % 10)) as u16);
    out.push((0x0030 + ((n / 10) % 10)) as u16);
    out.push((0x0030 + (n % 10)) as u16);
    proof {
        reveal(spec_digit_char);
        assert(out@ =~= old(out)@ + spec_fmt6(n as int));
    }
}

fn format_iso_fields_exec(
    y: i64,
    m: i64,
    dt: i64,
    hr: i64,
    mn: i64,
    sc: i64,
    ms: i64,
) -> (out: Vec<u16>)
    requires
        -999_999 <= y && y <= 999_999,
        0 <= m && m <= 11,
        1 <= dt && dt <= 31,
        0 <= hr && hr <= 23,
        0 <= mn && mn <= 59,
        0 <= sc && sc <= 59,
        0 <= ms && ms <= 999,
    ensures
        out@
            == spec_format_iso_fields(
                y as int,
                m as int,
                dt as int,
                hr as int,
                mn as int,
                sc as int,
                ms as int,
            ),
{
    let mut out: Vec<u16> = Vec::new();
    if y < 0 {
        out.push(0x002Du16);
        push_fmt6(&mut out, -y);
    } else if y > 9999 {
        out.push(0x002Bu16);
        push_fmt6(&mut out, y);
    } else {
        push_fmt4(&mut out, y);
    }
    out.push(0x002Du16);
    push_fmt2(&mut out, m + 1);
    out.push(0x002Du16);
    push_fmt2(&mut out, dt);
    out.push(0x0054u16);
    push_fmt2(&mut out, hr);
    out.push(0x003Au16);
    push_fmt2(&mut out, mn);
    out.push(0x003Au16);
    push_fmt2(&mut out, sc);
    out.push(0x002Eu16);
    push_fmt3(&mut out, ms);
    out.push(0x005Au16);
    proof {
        assert(out@
            =~= spec_format_iso_fields(
                y as int,
                m as int,
                dt as int,
                hr as int,
                mn as int,
                sc as int,
                ms as int,
            ));
    }
    out
}

/// Exec ECMA-262 §21.4.4.36 `Date.prototype.toISOString` proved equal to `spec_to_iso_string`
/// and guaranteed to roundtrip via `spec_parse_iso8601`.
#[verifier::spinoff_prover]
pub fn to_iso_string(tv: i64) -> (res: Option<Vec<u16>>)
    ensures
        match res {
            Some(s) => {
                &&& spec_to_iso_string(tv as int) == Some(s@)
                &&& spec_parse_iso8601(s@) == Some(tv as int)
            },
            None => spec_to_iso_string(tv as int).is_none(),
        },
{
    match time_clip(tv) {
        None => None,
        Some(t) => {
            proof {
                lemma_clipped_year_bounds(t as int);
                lemma_iso8601_roundtrip(t as int);
            }
            let y = year_from_time(t);
            let m = month_from_time(t);
            let dt = date_from_time(t);
            let hr = hour_from_time(t);
            let mn = min_from_time(t);
            let sc = sec_from_time(t);
            let ms = ms_from_time(t);
            let out = format_iso_fields_exec(y, m, dt, hr, mn, sc, ms);
            Some(out)
        },
    }
}

fn is_digit_exec(c: u16) -> (res: bool)
    ensures
        res == spec_is_digit(c),
{
    c >= 0x0030 && c <= 0x0039
}

fn digit_val_exec(c: u16) -> (v: i64)
    requires
        spec_is_digit(c),
    ensures
        v as int == spec_digit_val(c),
        0 <= v <= 9,
{
    (c - 0x0030) as i64
}

fn parse2_exec(s: &[u16], pos: usize) -> (res: Option<i64>)
    requires
        pos <= s@.len(),
    ensures
        match res {
            Some(v) => spec_parse2(s@, pos as int) == Some(v as int) && 0 <= v <= 99,
            None => spec_parse2(s@, pos as int).is_none(),
        },
{
    if s.len() - pos >= 2 && is_digit_exec(s[pos]) && is_digit_exec(s[pos + 1]) {
        Some(digit_val_exec(s[pos]) * 10 + digit_val_exec(s[pos + 1]))
    } else {
        None
    }
}

fn parse4_exec(s: &[u16], pos: usize) -> (res: Option<i64>)
    requires
        pos <= s@.len(),
    ensures
        match res {
            Some(v) => spec_parse4(s@, pos as int) == Some(v as int) && 0 <= v <= 9999,
            None => spec_parse4(s@, pos as int).is_none(),
        },
{
    if s.len() - pos >= 4
        && is_digit_exec(s[pos])
        && is_digit_exec(s[pos + 1])
        && is_digit_exec(s[pos + 2])
        && is_digit_exec(s[pos + 3])
    {
        Some(
            digit_val_exec(s[pos]) * 1000
                + digit_val_exec(s[pos + 1]) * 100
                + digit_val_exec(s[pos + 2]) * 10
                + digit_val_exec(s[pos + 3]),
        )
    } else {
        None
    }
}

fn parse6_exec(s: &[u16], pos: usize) -> (res: Option<i64>)
    requires
        pos <= s@.len(),
    ensures
        match res {
            Some(v) => spec_parse6(s@, pos as int) == Some(v as int) && 0 <= v <= 999_999,
            None => spec_parse6(s@, pos as int).is_none(),
        },
{
    if s.len() - pos >= 6
        && is_digit_exec(s[pos])
        && is_digit_exec(s[pos + 1])
        && is_digit_exec(s[pos + 2])
        && is_digit_exec(s[pos + 3])
        && is_digit_exec(s[pos + 4])
        && is_digit_exec(s[pos + 5])
    {
        Some(
            digit_val_exec(s[pos]) * 100_000
                + digit_val_exec(s[pos + 1]) * 10_000
                + digit_val_exec(s[pos + 2]) * 1_000
                + digit_val_exec(s[pos + 3]) * 100
                + digit_val_exec(s[pos + 4]) * 10
                + digit_val_exec(s[pos + 5]),
        )
    } else {
        None
    }
}

fn parse_iso_year_exec(s: &[u16]) -> (res: Option<(i64, usize)>)
    ensures
        match res {
            Some((y, p)) => {
                &&& spec_parse_iso_year(s@) == Some((y as int, p as int))
                &&& -999_999 <= y && y <= 999_999
                &&& p <= s@.len()
            },
            None => spec_parse_iso_year(s@).is_none(),
        },
{
    if s.len() == 0 {
        None
    } else if s[0] == 0x002Bu16 {
        match parse6_exec(s, 1) {
            Some(v) => Some((v, 7)),
            None => None,
        }
    } else if s[0] == 0x002Du16 {
        match parse6_exec(s, 1) {
            Some(v) => {
                if v == 0 {
                    None
                } else {
                    Some((-v, 7))
                }
            },
            None => None,
        }
    } else {
        match parse4_exec(s, 0) {
            Some(v) => Some((v, 4)),
            None => None,
        }
    }
}

fn parse_iso_date_exec(s: &[u16]) -> (res: Option<(i64, i64, i64, usize)>)
    ensures
        match res {
            Some((y, m, dt, p)) => {
                &&& spec_parse_iso_date(s@) == Some((y as int, m as int, dt as int, p as int))
                &&& -999_999 <= y && y <= 999_999
                &&& 0 <= m && m <= 11
                &&& 1 <= dt && dt <= 31
                &&& p <= s@.len()
            },
            None => spec_parse_iso_date(s@).is_none(),
        },
{
    match parse_iso_year_exec(s) {
        None => None,
        Some((year, p1)) => {
            let leap: i64 = if days_in_year(year) == 366 { 1 } else { 0 };
            if p1 == s.len() {
                Some((year, 0, 1, p1))
            } else if s[p1] == 0x0054u16 {
                Some((year, 0, 1, p1))
            } else if s[p1] == 0x002Du16 {
                match parse2_exec(s, p1 + 1) {
                    None => None,
                    Some(mm) => {
                        if mm < 1 || mm > 12 {
                            None
                        } else {
                            let m = mm - 1;
                            let p2 = p1 + 3;
                            if p2 == s.len() || s[p2] == 0x0054u16 {
                                Some((year, m, 1, p2))
                            } else if s[p2] == 0x002Du16 {
                                match parse2_exec(s, p2 + 1) {
                                    None => None,
                                    Some(dd) => {
                                        let dim = days_in_month_exec(m, leap);
                                        if dd < 1 || dd > dim {
                                            None
                                        } else {
                                            Some((year, m, dd, p2 + 3))
                                        }
                                    },
                                }
                            } else {
                                None
                            }
                        }
                    },
                }
            } else {
                None
            }
        },
    }
}

fn parse_iso_tz_exec(s: &[u16], pos: usize) -> (res: Option<i64>)
    requires
        pos <= s@.len(),
    ensures
        match res {
            Some(off) => {
                &&& spec_parse_iso_tz(s@, pos as int) == Some(off as int)
                &&& -MS_PER_DAY <= off && off <= MS_PER_DAY
            },
            None => spec_parse_iso_tz(s@, pos as int).is_none(),
        },
{
    if pos >= s.len() {
        None
    } else if s[pos] == 0x005Au16 {
        if s.len() - pos == 1 {
            Some(0)
        } else {
            None
        }
    } else if s[pos] == 0x002Bu16 || s[pos] == 0x002Du16 {
        if s.len() - pos != 6 || s[pos + 3] != 0x003Au16 {
            None
        } else {
            match (parse2_exec(s, pos + 1), parse2_exec(s, pos + 4)) {
                (Some(oh), Some(om)) => {
                    if oh > 23 || om > 59 {
                        None
                    } else {
                        let off_ms = (oh * 60 + om) * MS_PER_MINUTE;
                        if s[pos] == 0x002Bu16 {
                            Some(off_ms)
                        } else {
                            Some(-off_ms)
                        }
                    }
                },
                _ => None,
            }
        }
    } else {
        None
    }
}

fn parse_iso_time_and_tz_exec(s: &[u16], pos: usize) -> (res: Option<(i64, i64)>)
    requires
        pos <= s@.len(),
    ensures
        match res {
            Some((tm, off)) => {
                &&& spec_parse_iso_time_and_tz(s@, pos as int) == Some((tm as int, off as int))
                &&& 0 <= tm && tm <= MS_PER_DAY
                &&& -MS_PER_DAY <= off && off <= MS_PER_DAY
            },
            None => spec_parse_iso_time_and_tz(s@, pos as int).is_none(),
        },
{
    if pos >= s.len() || s[pos] != 0x0054u16 {
        None
    } else if s.len() - pos < 6 || s[pos + 3] != 0x003Au16 {
        None
    } else {
        match (parse2_exec(s, pos + 1), parse2_exec(s, pos + 4)) {
            (Some(hr), Some(mn)) => {
                let p_after_hm = pos + 6;
                let sec_opt: Option<(i64, usize)> = if p_after_hm < s.len() && s[p_after_hm] == 0x003Au16 {
                    match parse2_exec(s, p_after_hm + 1) {
                        Some(sc) => Some((sc, p_after_hm + 3)),
                        None => None,
                    }
                } else {
                    Some((0, p_after_hm))
                };
                match sec_opt {
                    None => None,
                    Some((sc, p_after_s)) => {
                        let ms_opt: Option<(i64, usize)> = if p_after_s < s.len() && s[p_after_s] == 0x002Eu16 {
                            if s.len() - p_after_s >= 2 && is_digit_exec(s[p_after_s + 1]) {
                                let d0 = digit_val_exec(s[p_after_s + 1]);
                                if s.len() - p_after_s >= 3 && is_digit_exec(s[p_after_s + 2]) {
                                    let d1 = digit_val_exec(s[p_after_s + 2]);
                                    if s.len() - p_after_s >= 4 && is_digit_exec(s[p_after_s + 3]) {
                                        let d2 = digit_val_exec(s[p_after_s + 3]);
                                        Some((d0 * 100 + d1 * 10 + d2, p_after_s + 4))
                                    } else {
                                        Some((d0 * 100 + d1 * 10, p_after_s + 3))
                                    }
                                } else {
                                    Some((d0 * 100, p_after_s + 2))
                                }
                            } else {
                                None
                            }
                        } else {
                            Some((0, p_after_s))
                        };
                        match ms_opt {
                            None => None,
                            Some((ms, p_tz)) => {
                                let valid_hms = (hr <= 23 && mn <= 59 && sc <= 59 && ms <= 999)
                                    || (hr == 24 && mn == 0 && sc == 0 && ms == 0);
                                if !valid_hms {
                                    None
                                } else {
                                    match parse_iso_tz_exec(s, p_tz) {
                                        Some(off_ms) => {
                                            let tm = hr * MS_PER_HOUR + mn * MS_PER_MINUTE + sc * MS_PER_SECOND + ms;
                                            Some((tm, off_ms))
                                        },
                                        None => None,
                                    }
                                }
                            },
                        }
                    },
                }
            },
            _ => None,
        }
    }
}

/// Exec ECMA-262 §21.4.1.32 ISO-8601 Date Time String parser proved equal to `spec_parse_iso8601`.
pub fn parse_iso8601(s: &[u16]) -> (res: Option<i64>)
    ensures
        match res {
            Some(tv) => {
                &&& spec_parse_iso8601(s@) == Some(tv as int)
                &&& -MAX_TIME_MS <= tv && tv <= MAX_TIME_MS
            },
            None => spec_parse_iso8601(s@).is_none(),
        },
{
    match parse_iso_date_exec(s) {
        None => None,
        Some((year, month, dt, pos)) => {
            let day_num = make_day(year, month, dt).unwrap();
            if pos == s.len() {
                let raw = make_date(day_num, 0).unwrap();
                time_clip(raw)
            } else {
                match parse_iso_time_and_tz_exec(s, pos) {
                    None => None,
                    Some((time_ms, off_ms)) => {
                        let raw = make_date(day_num, time_ms).unwrap() - off_ms;
                        time_clip(raw)
                    },
                }
            }
        },
    }
}

} // verus!
