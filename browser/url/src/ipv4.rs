//! WHATWG URL §3.5 host parsing: the ends-in-a-number checker, the IPv4 parser and the IPv4
//! number parser, transcribed from url.bs at whatwg/url@4f461b81 (2026-11-19).
//!
//! Validation errors are not modeled yet; only the return values are. Inputs are ASCII strings
//! as bytes (the host parser runs domain-to-ASCII first).
use crate::percent::{hex_val, is_hex};
// Spec-only items are erased in non-Verus builds.
#[cfg(verus_keep_ghost)]
use crate::percent::{hex_value, is_ascii_hex_digit};
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::power::pow;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------------------
// Spec
// ---------------------------------------------------------------------------------------

/// Infra "strictly split a string on U+002E (.)": every '.' ends a token, empty tokens kept.
/// Stated by recursion on the last byte, which yields the same token list.
pub open spec fn spec_split_dots(s: Seq<u8>) -> Seq<Seq<u8>>
    decreases s.len(),
{
    if s.len() == 0 {
        seq![Seq::<u8>::empty()]
    } else {
        let rest = spec_split_dots(s.drop_last());
        if s.last() == 0x2E {
            rest.push(Seq::<u8>::empty())
        } else {
            rest.update(rest.len() - 1, rest.last().push(s.last()))
        }
    }
}

pub open spec fn is_ascii_digit(c: u8) -> bool {
    0x30 <= c <= 0x39
}

/// Value of c as a radix-R digit, if it is one (R is 8, 10 or 16).
pub open spec fn radix_digit(c: u8, r: nat) -> Option<nat> {
    if r == 16 {
        if is_ascii_hex_digit(c) {
            Some(hex_value(c))
        } else {
            None
        }
    } else if r == 8 {
        if 0x30 <= c <= 0x37 {
            Some((c - 0x30) as nat)
        } else {
            None
        }
    } else {
        if is_ascii_digit(c) {
            Some((c - 0x30) as nat)
        } else {
            None
        }
    }
}

/// "the mathematical integer value that is represented by input in radix-R notation", or None
/// if "input contains a code point that is not a radix-R digit".
pub open spec fn spec_radix_value(s: Seq<u8>, r: nat) -> Option<nat>
    decreases s.len(),
{
    if s.len() == 0 {
        Some(0)
    } else {
        match (spec_radix_value(s.drop_last(), r), radix_digit(s.last(), r)) {
            (Some(a), Some(d)) => Some(a * r + d),
            _ => None,
        }
    }
}

pub open spec fn has_hex_prefix(input: Seq<u8>) -> bool {
    input.len() >= 2 && input[0] == 0x30 && (input[1] == 0x58 || input[1] == 0x78)
}

pub open spec fn has_octal_prefix(input: Seq<u8>) -> bool {
    input.len() >= 2 && input[0] == 0x30 && !has_hex_prefix(input)
}

pub open spec fn ipv4_number_radix(input: Seq<u8>) -> nat {
    if has_hex_prefix(input) {
        16
    } else if has_octal_prefix(input) {
        8
    } else {
        10
    }
}

pub open spec fn ipv4_number_digits(input: Seq<u8>) -> Seq<u8> {
    if has_hex_prefix(input) {
        input.subrange(2, input.len() as int)
    } else if has_octal_prefix(input) {
        input.subrange(1, input.len() as int)
    } else {
        input
    }
}

/// The IPv4 number parser (the validationError flag is not modeled).
pub open spec fn spec_ipv4_number(input: Seq<u8>) -> Option<nat> {
    if input.len() == 0 {
        None
    } else if ipv4_number_digits(input).len() == 0 {
        Some(0)
    } else {
        spec_radix_value(ipv4_number_digits(input), ipv4_number_radix(input))
    }
}

/// IPv4 parser steps 1-2: split, then drop a trailing empty part if there is more than one part.
pub open spec fn spec_ipv4_parts(input: Seq<u8>) -> Seq<Seq<u8>> {
    let parts = spec_split_dots(input);
    if parts.last().len() == 0 && parts.len() > 1 {
        parts.drop_last()
    } else {
        parts
    }
}

/// "For each n of numbers: increment ipv4 by n × 256^(3 − counter)", over the first k numbers.
pub open spec fn spec_ipv4_sum(numbers: Seq<nat>, k: nat) -> int
    decreases k,
{
    if k == 0 {
        0
    } else {
        spec_ipv4_sum(numbers, (k - 1) as nat) + numbers[k - 1] * pow(256, (3 - (k - 1)) as nat)
    }
}

pub open spec fn spec_ipv4_numbers(parts: Seq<Seq<u8>>) -> Seq<nat> {
    parts.map_values(|p: Seq<u8>| spec_ipv4_number(p).unwrap())
}

/// The IPv4 parser. Returns the address as a number, or None for failure.
pub open spec fn spec_ipv4_parse(input: Seq<u8>) -> Option<nat> {
    let parts = spec_ipv4_parts(input);
    if parts.len() > 4 {
        None
    } else if exists|i: int| 0 <= i < parts.len() && spec_ipv4_number(parts[i]) is None {
        None
    } else {
        let numbers = spec_ipv4_numbers(parts);
        if exists|i: int| 0 <= i < numbers.len() - 1 && numbers[i] > 255 {
            None
        } else if numbers.last() >= pow(256, (5 - numbers.len()) as nat) {
            None
        } else {
            Some((numbers.last() + spec_ipv4_sum(numbers, (numbers.len() - 1) as nat)) as nat)
        }
    }
}

/// Ends-in-a-number checker steps 1-3: split, drop a trailing empty part, take the last part.
pub open spec fn spec_ends_in_a_number_last(input: Seq<u8>) -> Seq<u8> {
    let parts0 = spec_split_dots(input);
    let parts = if parts0.last().len() == 0 {
        parts0.drop_last()
    } else {
        parts0
    };
    parts.last()
}

/// "last is not the empty string and contains only ASCII digits"
pub open spec fn is_nonempty_ascii_digits(s: Seq<u8>) -> bool {
    s.len() > 0 && forall|i: int| 0 <= i < s.len() ==> is_ascii_digit(#[trigger] s[i])
}

/// The ends-in-a-number checker. Requires a non-empty input (the spec asserts this).
pub open spec fn spec_ends_in_a_number(input: Seq<u8>) -> bool {
    let last = spec_ends_in_a_number_last(input);
    is_nonempty_ascii_digits(last) || spec_ipv4_number(last) is Some
}

// ---------------------------------------------------------------------------------------
// Lemmas
// ---------------------------------------------------------------------------------------

pub proof fn lemma_split_nonempty(s: Seq<u8>)
    ensures
        spec_split_dots(s).len() >= 1,
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_split_nonempty(s.drop_last());
    }
}

/// A radix value exists iff every byte is a radix-R digit.
pub proof fn lemma_radix_some_iff_digits(s: Seq<u8>, r: nat)
    ensures
        spec_radix_value(s, r) is Some <==> forall|i: int|
            0 <= i < s.len() ==> radix_digit(#[trigger] s[i], r) is Some,
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_radix_some_iff_digits(s.drop_last(), r);
        if spec_radix_value(s, r) is Some {
            assert forall|i: int| 0 <= i < s.len() implies radix_digit(#[trigger] s[i], r) is Some by {
                if i < s.len() - 1 {
                    assert(s[i] == s.drop_last()[i]);
                }
            }
        }
        if forall|i: int| 0 <= i < s.len() ==> radix_digit(#[trigger] s[i], r) is Some {
            assert forall|i: int| 0 <= i < s.drop_last().len() implies radix_digit(
                #[trigger] s.drop_last()[i],
                r,
            ) is Some by {
                assert(s.drop_last()[i] == s[i]);
            }
            assert(radix_digit(s[s.len() - 1], r) is Some);
        }
    }
}

/// The spec's note on step 5 of the ends-in-a-number checker: once `last` is not a non-empty
/// all-digit string, "parsing last as an IPv4 number does not return failure" "is equivalent to
/// checking that last is "0X" or "0x", followed by zero or more ASCII hex digits."
pub proof fn lemma_ends_in_number_note(last: Seq<u8>)
    requires
        !is_nonempty_ascii_digits(last),
    ensures
        spec_ipv4_number(last) is Some <==> (has_hex_prefix(last) && forall|i: int|
            2 <= i < last.len() ==> is_ascii_hex_digit(#[trigger] last[i])),
{
    let d = ipv4_number_digits(last);
    let r = ipv4_number_radix(last);
    lemma_radix_some_iff_digits(d, r);
    if has_hex_prefix(last) {
        if forall|i: int| 2 <= i < last.len() ==> is_ascii_hex_digit(#[trigger] last[i]) {
            assert forall|i: int| 0 <= i < d.len() implies radix_digit(#[trigger] d[i], r) is Some by {
                assert(d[i] == last[i + 2]);
            }
        }
        if spec_ipv4_number(last) is Some && d.len() > 0 {
            assert forall|i: int| 2 <= i < last.len() implies is_ascii_hex_digit(
                #[trigger] last[i],
            ) by {
                assert(last[i] == d[i - 2]);
                assert(radix_digit(d[i - 2], r) is Some);
            }
        }
    } else if has_octal_prefix(last) {
        // d is non-empty here (last.len() >= 2); all-octal d would make last all digits.
        if spec_ipv4_number(last) is Some {
            assert(d.len() > 0);
            assert forall|i: int| 0 <= i < last.len() implies is_ascii_digit(last[i]) by {
                if i > 0 {
                    assert(last[i] == d[i - 1]);
                    assert(radix_digit(d[i - 1], r) is Some);
                }
            }
            assert(false);
        }
    } else {
        if spec_ipv4_number(last) is Some {
            assert(last.len() > 0);
            assert(d == last);
            assert forall|i: int| 0 <= i < last.len() implies is_ascii_digit(last[i]) by {
                assert(radix_digit(d[i], r) is Some);
            }
            assert(false);
        }
    }
}

proof fn lemma_pow256()
    ensures
        pow(256, 0) == 1,
        pow(256, 1) == 256,
        pow(256, 2) == 65536,
        pow(256, 3) == 16777216,
        pow(256, 4) == 4294967296,
{
    reveal_with_fuel(pow, 5);
}

// ---------------------------------------------------------------------------------------
// Exec
// ---------------------------------------------------------------------------------------

/// Sentinel standing for "some value > u32::MAX": every such IPv4 number makes the parser fail.
pub const BIG: u64 = 0x1_0000_0000;

/// For byte vectors, deep_view and view coincide.
pub proof fn lemma_dv(v: Vec<u8>)
    ensures
        v.deep_view() == v@,
{
    assert(v.deep_view() =~= v@);
}

pub open spec fn sat_eq(v: u64, x: nat) -> bool {
    if x <= 0xFFFF_FFFF {
        v as nat == x
    } else {
        v == BIG
    }
}

pub fn split_dots(input: &[u8]) -> (parts: Vec<Vec<u8>>)
    ensures
        parts.deep_view() == spec_split_dots(input@),
{
    let n = input.len();
    let mut done: Vec<Vec<u8>> = Vec::new();
    let mut cur: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(input@.subrange(0, 0) =~= Seq::<u8>::empty());
        assert(done.deep_view().push(cur@) =~= seq![Seq::<u8>::empty()]);
    }
    while i < n
        invariant
            i <= n,
            n == input@.len(),
            done.deep_view().push(cur@) == spec_split_dots(input@.subrange(0, i as int)),
        decreases n - i,
    {
        let b = input[i];
        let ghost prev = done.deep_view();
        let ghost prev_cur = cur@;
        proof {
            assert(input@.subrange(0, i + 1).drop_last() =~= input@.subrange(0, i as int));
        }
        if b == 0x2E {
            proof {
                lemma_dv(cur);
            }
            done.push(cur);
            cur = Vec::new();
            proof {
                assert(done.deep_view() =~= prev.push(prev_cur));
                assert(done.deep_view().push(cur@) =~= prev.push(prev_cur).push(Seq::<u8>::empty()));
            }
        } else {
            cur.push(b);
            proof {
                let rest = prev.push(prev_cur);
                assert(done.deep_view().push(cur@) =~= rest.update(
                    rest.len() - 1,
                    rest.last().push(b),
                ));
            }
        }
        i += 1;
    }
    proof {
        assert(input@.subrange(0, n as int) =~= input@);
    }
    let ghost prev = done.deep_view();
    let ghost prev_cur = cur@;
    proof {
        lemma_dv(cur);
    }
    done.push(cur);
    proof {
        assert(done.deep_view() =~= prev.push(prev_cur));
    }
    done
}

fn digit(c: u8, r: u64) -> (res: Option<u64>)
    requires
        r == 8 || r == 10 || r == 16,
    ensures
        match radix_digit(c, r as nat) {
            Some(d) => res matches Some(v) && v as nat == d && v < 16,
            None => res is None,
        },
{
    if r == 16 {
        if is_hex(c) {
            Some(hex_val(c) as u64)
        } else {
            None
        }
    } else if r == 8 {
        if c >= 0x30 && c <= 0x37 {
            Some((c - 0x30) as u64)
        } else {
            None
        }
    } else {
        if c >= 0x30 && c <= 0x39 {
            Some((c - 0x30) as u64)
        } else {
            None
        }
    }
}

/// The IPv4 number parser. Values above u32::MAX are reported as `BIG`.
pub fn ipv4_number(input: &[u8]) -> (res: Option<u64>)
    ensures
        match spec_ipv4_number(input@) {
            Some(x) => res matches Some(v) && sat_eq(v, x),
            None => res is None,
        },
{
    let n = input.len();
    if n == 0 {
        return None;
    }
    let (start, r): (usize, u64) = if n >= 2 && input[0] == 0x30 && (input[1] == 0x58 || input[1]
        == 0x78) {
        (2, 16)
    } else if n >= 2 && input[0] == 0x30 {
        (1, 8)
    } else {
        (0, 10)
    };
    let ghost digits = ipv4_number_digits(input@);
    proof {
        assert(digits =~= input@.subrange(start as int, n as int));
        assert(r as nat == ipv4_number_radix(input@));
    }
    if start == n {
        return Some(0);
    }
    let mut v: u64 = 0;
    let mut ok = true;
    let mut j = start;
    proof {
        assert(input@.subrange(start as int, start as int) =~= Seq::<u8>::empty());
    }
    while j < n
        invariant
            start <= j <= n,
            n == input@.len(),
            r == 8 || r == 10 || r == 16,
            ok ==> (spec_radix_value(input@.subrange(start as int, j as int), r as nat) matches Some(
                x,
            ) && sat_eq(v, x)),
            !ok ==> spec_radix_value(input@.subrange(start as int, j as int), r as nat) is None,
            v <= BIG,
        decreases n - j,
    {
        let ghost pre = input@.subrange(start as int, j as int);
        proof {
            assert(input@.subrange(start as int, j + 1).drop_last() =~= pre);
            assert(input@.subrange(start as int, j + 1).last() == input@[j as int]);
        }
        match digit(input[j], r) {
            Some(d) => {
                if ok {
                    let ghost x = spec_radix_value(pre, r as nat).unwrap();
                    if v == BIG {
                        proof {
                            assert(x * (r as nat) + d as nat >= x) by (nonlinear_arith)
                                requires r >= 8;
                        }
                    } else {
                        proof {
                            assert(v * r <= 0xFFFF_FFFFu64 * 16) by (nonlinear_arith)
                                requires v <= 0xFFFF_FFFFu64, r <= 16;
                        }
                        let w = v * r + d;
                        proof {
                            assert(w == x * (r as nat) + d as nat);
                        }
                        v = if w > 0xFFFF_FFFF { BIG } else { w };
                    }
                }
            },
            None => {
                ok = false;
            },
        }
        j += 1;
    }
    proof {
        assert(input@.subrange(start as int, n as int) =~= digits);
    }
    if ok {
        Some(v)
    } else {
        None
    }
}

/// The IPv4 parser.
pub fn ipv4_parse(input: &[u8]) -> (res: Option<u32>)
    ensures
        match spec_ipv4_parse(input@) {
            Some(x) => res matches Some(v) && v as nat == x,
            None => res is None,
        },
{
    let mut parts = split_dots(input);
    proof {
        lemma_split_nonempty(input@);
    }
    let ghost all = parts.deep_view();
    if parts[parts.len() - 1].len() == 0 && parts.len() > 1 {
        parts.pop();
        proof {
            assert(parts.deep_view() =~= all.drop_last());
        }
    }
    let ghost ps = parts.deep_view();
    proof {
        assert(ps == spec_ipv4_parts(input@));
    }
    let np = parts.len();
    proof {
        assert(ps.len() == np);
    }
    if np > 4 {
        proof { assert(spec_ipv4_parse(input@) is None); }
        return None;
    }
    let mut nums: Vec<u64> = Vec::new();
    let mut k: usize = 0;
    while k < np
        invariant
            k <= np,
            np == parts.len(),
            np <= 4,
            ps == parts.deep_view(),
            ps.len() == np,
            ps == spec_ipv4_parts(input@),
            nums.len() == k,
            forall|j: int|
                0 <= j < k ==> (spec_ipv4_number(#[trigger] ps[j]) matches Some(x) && sat_eq(
                    nums[j],
                    x,
                )),
        decreases np - k,
    {
        proof {
            lemma_dv(parts[k as int]);
            assert(parts[k as int]@ == ps[k as int]);
        }
        match ipv4_number(parts[k].as_slice()) {
            Some(v) => {
                nums.push(v);
            },
            None => {
                proof {
                    assert(spec_ipv4_number(ps[k as int]) is None);
                    assert(exists|i: int| 0 <= i < ps.len() && spec_ipv4_number(ps[i]) is None);
                    assert(spec_ipv4_parse(input@) is None);
                }
                return None;
            },
        }
        k += 1;
    }
    let ghost numbers = spec_ipv4_numbers(ps);
    proof {
        assert forall|j: int| 0 <= j < np implies sat_eq(nums[j], #[trigger] numbers[j]) by {
            assert(spec_ipv4_number(ps[j]) is Some);
        }
        assert(!(exists|i: int| 0 <= i < ps.len() && spec_ipv4_number(ps[i]) is None));
        lemma_pow256();
    }
    let mut j: usize = 0;
    while j + 1 < np
        invariant
            j <= np,
            ps.len() == np,
            ps == spec_ipv4_parts(input@),
            numbers == spec_ipv4_numbers(ps),
            !(exists|i: int| 0 <= i < ps.len() && spec_ipv4_number(ps[i]) is None),
            np == nums.len(),
            np <= 4,
            numbers.len() == np,
            forall|i: int| 0 <= i < np ==> sat_eq(nums[i], #[trigger] numbers[i]),
            forall|i: int| 0 <= i < j ==> #[trigger] numbers[i] <= 255,
        decreases np - j,
    {
        if nums[j] > 255 {
            proof {
                assert(numbers[j as int] > 255);
                assert(exists|i: int| 0 <= i < numbers.len() - 1 && numbers[i] > 255);
                assert(spec_ipv4_parse(input@) is None);
            }
            return None;
        }
        j += 1;
    }
    let last = nums[np - 1];
    let limit: u64 = if np == 1 {
        0x1_0000_0000
    } else if np == 2 {
        0x100_0000
    } else if np == 3 {
        0x1_0000
    } else {
        0x100
    };
    proof {
        assert(limit as nat == pow(256, (5 - np) as nat));
    }
    proof {
        assert(sat_eq(last, numbers.last()));
        assert(!(exists|i: int| 0 <= i < numbers.len() - 1 && numbers[i] > 255));
    }
    if last >= limit {
        proof {
            assert(numbers.last() >= pow(256, (5 - numbers.len()) as nat));
            assert(spec_ipv4_parse(input@) is None);
        }
        return None;
    }
    proof {
        reveal_with_fuel(spec_ipv4_sum, 4);
    }
    let v: u64 = if np == 1 {
        last
    } else if np == 2 {
        nums[0] * 0x100_0000 + last
    } else if np == 3 {
        nums[0] * 0x100_0000 + nums[1] * 0x1_0000 + last
    } else {
        nums[0] * 0x100_0000 + nums[1] * 0x1_0000 + nums[2] * 0x100 + last
    };
    proof {
        assert(last as nat == numbers.last());
        assert(forall|i: int| 0 <= i < np - 1 ==> nums[i] as nat == #[trigger] numbers[i]);
        assert(v as nat == numbers.last() + spec_ipv4_sum(numbers, (numbers.len() - 1) as nat));
        assert(spec_ipv4_parse(input@) == Some(v as nat));
    }
    Some(v as u32)
}

/// The ends-in-a-number checker.
pub fn ends_in_a_number(input: &[u8]) -> (res: bool)
    requires
        input@.len() > 0,
    ensures
        res == spec_ends_in_a_number(input@),
{
    let mut parts = split_dots(input);
    proof {
        lemma_split_nonempty(input@);
    }
    let ghost all = parts.deep_view();
    let ghost sp = if all.last().len() == 0 {
        all.drop_last()
    } else {
        all
    };
    proof {
        lemma_dv(parts[parts.len() - 1]);
    }
    if parts[parts.len() - 1].len() == 0 {
        parts.pop();
        proof {
            assert(parts.deep_view() =~= all.drop_last());
        }
    }
    // A non-empty input never splits to a single empty part, so at least one part remains.
    proof {
        if all.len() == 1 && all.last().len() == 0 {
            lemma_split_single_empty(input@);
        }
    }
    let last = &parts[parts.len() - 1];
    proof {
        lemma_dv(*last);
        assert(parts.deep_view() == sp);
        assert(last@ == sp.last());
    }
    let mut all_digits = last.len() > 0;
    let mut i: usize = 0;
    while i < last.len()
        invariant
            i <= last.len(),
            all_digits == (last@.len() > 0 && forall|j: int|
                0 <= j < i ==> is_ascii_digit(#[trigger] last@[j])),
        decreases last.len() - i,
    {
        if !(last[i] >= 0x30 && last[i] <= 0x39) {
            all_digits = false;
        }
        i += 1;
    }
    proof {
        assert(all == spec_split_dots(input@));
        assert(sp.last() == spec_ends_in_a_number_last(input@));
        assert(all_digits == is_nonempty_ascii_digits(sp.last()));
    }
    if all_digits {
        proof {
            assert(spec_ends_in_a_number(input@));
        }
        return true;
    }
    let r = ipv4_number(last.as_slice()).is_some();
    proof {
        assert(r == spec_ipv4_number(sp.last()) is Some);
        assert(r == spec_ends_in_a_number(input@));
    }
    r
}

/// Splitting yields exactly [""] only for the empty input.
proof fn lemma_split_single_empty(s: Seq<u8>)
    requires
        spec_split_dots(s).len() == 1,
        spec_split_dots(s).last().len() == 0,
    ensures
        s.len() == 0,
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_split_nonempty(s.drop_last());
    }
}

} // verus!
