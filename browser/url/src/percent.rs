//! WHATWG URL §1.3 "Percent-encoded bytes", transcribed from url.bs at
//! whatwg/url@4f461b81a748443b235840599cea6290df40329a (2026-11-19).
//!
//! Byte-level transcription: the spec's percent-encode sets are sets of code points, but
//! "percent-encode after encoding" tests each *byte* by its isomorphic code point, so a
//! byte b is in a set iff code point U+00bb is. Bytes >= 0x80 map to code points > U+007E
//! and are therefore in every set (all sets contain the C0 control percent-encode set).
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------------------
// Spec
// ---------------------------------------------------------------------------------------

/// Infra: ASCII hex digit (0-9, A-F, a-f).
pub open spec fn is_ascii_hex_digit(b: u8) -> bool {
    (0x30 <= b <= 0x39) || (0x41 <= b <= 0x46) || (0x61 <= b <= 0x66)
}

pub open spec fn hex_value(b: u8) -> nat {
    if 0x30 <= b <= 0x39 {
        (b - 0x30) as nat
    } else if 0x41 <= b <= 0x46 {
        (b - 0x41 + 10) as nat
    } else {
        (b - 0x61 + 10) as nat
    }
}

/// ASCII upper hex digit for a nibble.
pub open spec fn upper_hex_digit(n: nat) -> u8 {
    if n < 10 {
        (0x30 + n) as u8
    } else {
        (0x41 + n - 10) as u8
    }
}

/// "To percent-encode a byte byte, return a string consisting of U+0025 (%), followed by two
/// ASCII upper hex digits representing byte."
pub open spec fn spec_percent_encode_byte(b: u8) -> Seq<u8> {
    seq![0x25u8, upper_hex_digit(b as nat / 16), upper_hex_digit(b as nat % 16)]
}

/// "To percent-decode a byte sequence input": for each byte, if it is not '%' append it;
/// if it is '%' and the next two bytes are not both hex digits, append it; otherwise append
/// the byte they encode and skip them.
pub open spec fn spec_percent_decode(input: Seq<u8>) -> Seq<u8>
    decreases input.len(),
{
    if input.len() == 0 {
        seq![]
    } else if input[0] == 0x25 && input.len() >= 3 && is_ascii_hex_digit(input[1])
        && is_ascii_hex_digit(input[2]) {
        seq![(hex_value(input[1]) * 16 + hex_value(input[2])) as u8] + spec_percent_decode(
            input.subrange(3, input.len() as int),
        )
    } else {
        seq![input[0]] + spec_percent_decode(input.subrange(1, input.len() as int))
    }
}

/// The percent-encode sets of §1.3.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum EncodeSet {
    C0Control,
    Fragment,
    Query,
    SpecialQuery,
    Path,
    Userinfo,
    Component,
    FormUrlencoded,
}

/// "C0 controls and all code points greater than U+007E (~)."
pub open spec fn in_c0_control_set(c: u8) -> bool {
    c <= 0x1F || c > 0x7E
}

/// "... and U+0020 SPACE, U+0022 ("), U+003C (<), U+003E (>), and U+0060 (`)."
pub open spec fn in_fragment_set(c: u8) -> bool {
    in_c0_control_set(c) || c == 0x20 || c == 0x22 || c == 0x3C || c == 0x3E || c == 0x60
}

/// "... and U+0020 SPACE, U+0022 ("), U+0023 (#), U+003C (<), and U+003E (>)."
pub open spec fn in_query_set(c: u8) -> bool {
    in_c0_control_set(c) || c == 0x20 || c == 0x22 || c == 0x23 || c == 0x3C || c == 0x3E
}

/// "the query percent-encode set and U+0027 (')."
pub open spec fn in_special_query_set(c: u8) -> bool {
    in_query_set(c) || c == 0x27
}

/// "the query percent-encode set and U+003F (?), U+005E (^), U+0060 (`), U+007B ({), and U+007D (})."
pub open spec fn in_path_set(c: u8) -> bool {
    in_query_set(c) || c == 0x3F || c == 0x5E || c == 0x60 || c == 0x7B || c == 0x7D
}

/// "the path percent-encode set and U+002F (/), U+003A (:), U+003B (;), U+003D (=), U+0040 (@),
/// U+005B ([) to U+005D (]), inclusive, and U+007C (|)."
pub open spec fn in_userinfo_set(c: u8) -> bool {
    in_path_set(c) || c == 0x2F || c == 0x3A || c == 0x3B || c == 0x3D || c == 0x40 || (0x5B <= c
        <= 0x5D) || c == 0x7C
}

/// "the userinfo percent-encode set and U+0024 ($) to U+0026 (&), inclusive, U+002B (+), and U+002C (,)."
pub open spec fn in_component_set(c: u8) -> bool {
    in_userinfo_set(c) || (0x24 <= c <= 0x26) || c == 0x2B || c == 0x2C
}

/// "the component percent-encode set and U+0021 (!), U+0027 (') to U+0029 RIGHT PARENTHESIS,
/// inclusive, and U+007E (~)."
pub open spec fn in_form_urlencoded_set(c: u8) -> bool {
    in_component_set(c) || c == 0x21 || (0x27 <= c <= 0x29) || c == 0x7E
}

pub open spec fn spec_in_set(set: EncodeSet, c: u8) -> bool {
    match set {
        EncodeSet::C0Control => in_c0_control_set(c),
        EncodeSet::Fragment => in_fragment_set(c),
        EncodeSet::Query => in_query_set(c),
        EncodeSet::SpecialQuery => in_special_query_set(c),
        EncodeSet::Path => in_path_set(c),
        EncodeSet::Userinfo => in_userinfo_set(c),
        EncodeSet::Component => in_component_set(c),
        EncodeSet::FormUrlencoded => in_form_urlencoded_set(c),
    }
}

/// "Percent-encode after encoding" with UTF-8 (already-encoded bytes) and spaceAsPlus = false:
/// a byte in the set is percent-encoded, any other byte is kept.
pub open spec fn spec_percent_encode(input: Seq<u8>, set: EncodeSet) -> Seq<u8>
    decreases input.len(),
{
    if input.len() == 0 {
        seq![]
    } else {
        (if spec_in_set(set, input[0]) {
            spec_percent_encode_byte(input[0])
        } else {
            seq![input[0]]
        }) + spec_percent_encode(input.subrange(1, input.len() as int), set)
    }
}

// ---------------------------------------------------------------------------------------
// Theorems about the spec itself
// ---------------------------------------------------------------------------------------

/// The spec's note on the application/x-www-form-urlencoded set: it "contains all code points,
/// except the ASCII alphanumeric, U+002A (*), U+002D (-), U+002E (.), and U+005F (_)."
pub proof fn lemma_form_urlencoded_note(c: u8)
    ensures
        in_form_urlencoded_set(c) <==> !((0x30 <= c <= 0x39) || (0x41 <= c <= 0x5A) || (0x61 <= c
            <= 0x7A) || c == 0x2A || c == 0x2D || c == 0x2E || c == 0x5F),
{
}

/// The spec's note that the query set "cannot be defined in terms of the fragment percent-encode
/// set due to the omission of U+0060 (`)": ` is in the fragment set but not the query set.
pub proof fn lemma_query_not_superset_of_fragment()
    ensures
        in_fragment_set(0x60) && !in_query_set(0x60),
{
}

/// Each set in the chain C0 ⊆ query ⊆ special-query, query ⊆ path ⊆ userinfo ⊆ component ⊆
/// form-urlencoded, as the definitions intend.
pub proof fn lemma_set_chain(c: u8)
    ensures
        in_c0_control_set(c) ==> in_query_set(c),
        in_c0_control_set(c) ==> in_fragment_set(c),
        in_query_set(c) ==> in_special_query_set(c),
        in_query_set(c) ==> in_path_set(c),
        in_path_set(c) ==> in_userinfo_set(c),
        in_userinfo_set(c) ==> in_component_set(c),
        in_component_set(c) ==> in_form_urlencoded_set(c),
{
}

proof fn lemma_nibble_roundtrip(b: u8)
    ensures
        is_ascii_hex_digit(upper_hex_digit(b as nat / 16)),
        is_ascii_hex_digit(upper_hex_digit(b as nat % 16)),
        hex_value(upper_hex_digit(b as nat / 16)) * 16 + hex_value(upper_hex_digit(b as nat % 16))
            == b as nat,
{
}

/// Decoding inverts encoding **whenever '%' itself is in the encode set**. Of the standard
/// sets only the component and application/x-www-form-urlencoded sets contain '%'
/// (`lemma_sets_containing_percent`), which is why encodeURIComponent output always decodes
/// back exactly; for the other six it fails (`lemma_roundtrip_fails_without_percent`).
pub proof fn lemma_decode_encode_roundtrip(s: Seq<u8>, set: EncodeSet)
    requires
        spec_in_set(set, 0x25),
    ensures
        spec_percent_decode(spec_percent_encode(s, set)) == s,
    decreases s.len(),
{
    if s.len() > 0 {
        let rest = s.subrange(1, s.len() as int);
        lemma_decode_encode_roundtrip(rest, set);
        let er = spec_percent_encode(rest, set);
        if spec_in_set(set, s[0]) {
            lemma_nibble_roundtrip(s[0]);
            let e = spec_percent_encode_byte(s[0]) + er;
            assert(e.subrange(3, e.len() as int) =~= er);
            assert(spec_percent_decode(e) =~= seq![s[0]] + rest);
        } else {
            let e = seq![s[0]] + er;
            assert(e.subrange(1, e.len() as int) =~= er);
            assert(spec_percent_decode(e) =~= seq![s[0]] + rest);
        }
        assert(seq![s[0]] + rest =~= s);
    }
}

/// '%' (U+0025) is in exactly two standard sets: component (via "U+0024 ($) to U+0026 (&)")
/// and form-urlencoded, which contains component.
pub proof fn lemma_sets_containing_percent(set: EncodeSet)
    ensures
        spec_in_set(set, 0x25) <==> (set == EncodeSet::Component || set == EncodeSet::FormUrlencoded),
{
}

/// For the six sets without '%', decode(encode(s)) != s for s = "%41": it encodes to itself
/// and decodes to "A".
pub proof fn lemma_roundtrip_fails_without_percent(set: EncodeSet)
    requires
        !spec_in_set(set, 0x25),
    ensures
        spec_percent_decode(spec_percent_encode(seq![0x25u8, 0x34, 0x31], set)) == seq![0x41u8],
{
    let s = seq![0x25u8, 0x34, 0x31];
    assert(s.subrange(1, 3) =~= seq![0x34u8, 0x31]);
    assert(s.subrange(1, 3).subrange(1, 2) =~= seq![0x31u8]);
    assert(s.subrange(1, 3).subrange(1, 2).subrange(1, 1) =~= Seq::<u8>::empty());
    reveal_with_fuel(spec_percent_encode, 4);
    assert(spec_percent_encode(s, set) =~= s);
    assert(s.subrange(3, 3) =~= Seq::<u8>::empty());
    reveal_with_fuel(spec_percent_decode, 2);
    assert(spec_percent_decode(s) =~= seq![0x41u8]);
}

// ---------------------------------------------------------------------------------------
// Exec, each proved equal to the spec
// ---------------------------------------------------------------------------------------

pub fn is_hex(b: u8) -> (r: bool)
    ensures
        r == is_ascii_hex_digit(b),
{
    (b >= 0x30 && b <= 0x39) || (b >= 0x41 && b <= 0x46) || (b >= 0x61 && b <= 0x66)
}

pub fn hex_val(b: u8) -> (r: u8)
    requires
        is_ascii_hex_digit(b),
    ensures
        r as nat == hex_value(b),
        r < 16,
{
    if b <= 0x39 {
        b - 0x30
    } else if b <= 0x46 {
        b - 0x41 + 10
    } else {
        b - 0x61 + 10
    }
}

fn upper_hex(n: u8) -> (r: u8)
    requires
        n < 16,
    ensures
        r == upper_hex_digit(n as nat),
{
    if n < 10 {
        0x30 + n
    } else {
        0x41 + n - 10
    }
}

pub fn in_set(set: EncodeSet, c: u8) -> (r: bool)
    ensures
        r == spec_in_set(set, c),
{
    let c0 = c <= 0x1F || c > 0x7E;
    let query = c0 || c == 0x20 || c == 0x22 || c == 0x23 || c == 0x3C || c == 0x3E;
    let path = query || c == 0x3F || c == 0x5E || c == 0x60 || c == 0x7B || c == 0x7D;
    let userinfo = path || c == 0x2F || c == 0x3A || c == 0x3B || c == 0x3D || c == 0x40 || (c
        >= 0x5B && c <= 0x5D) || c == 0x7C;
    let component = userinfo || (c >= 0x24 && c <= 0x26) || c == 0x2B || c == 0x2C;
    match set {
        EncodeSet::C0Control => c0,
        EncodeSet::Fragment => c0 || c == 0x20 || c == 0x22 || c == 0x3C || c == 0x3E || c == 0x60,
        EncodeSet::Query => query,
        EncodeSet::SpecialQuery => query || c == 0x27,
        EncodeSet::Path => path,
        EncodeSet::Userinfo => userinfo,
        EncodeSet::Component => component,
        EncodeSet::FormUrlencoded => component || c == 0x21 || (c >= 0x27 && c <= 0x29) || c
            == 0x7E,
    }
}

pub fn percent_encode(input: &[u8], set: EncodeSet) -> (out: Vec<u8>)
    ensures
        out@ == spec_percent_encode(input@, set),
{
    let n = input.len();
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(input@.subrange(0, n as int) =~= input@);
        assert(out@ =~= Seq::<u8>::empty());
    }
    while i < n
        invariant
            i <= n,
            n == input@.len(),
            spec_percent_encode(input@, set) == out@ + spec_percent_encode(
                input@.subrange(i as int, n as int),
                set,
            ),
        decreases n - i,
    {
        let b = input[i];
        let ghost rest = input@.subrange(i as int, n as int);
        proof {
            assert(rest.subrange(1, rest.len() as int) =~= input@.subrange(i + 1, n as int));
        }
        let ghost old_out = out@;
        if in_set(set, b) {
            out.push(0x25);
            out.push(upper_hex(b / 16));
            out.push(upper_hex(b % 16));
            proof {
                assert(out@ =~= old_out + spec_percent_encode_byte(b));
            }
        } else {
            out.push(b);
            proof {
                assert(out@ =~= old_out + seq![b]);
            }
        }
        i += 1;
        proof {
            let piece = if spec_in_set(set, b) {
                spec_percent_encode_byte(b)
            } else {
                seq![b]
            };
            assert(old_out + (piece + spec_percent_encode(input@.subrange(i as int, n as int), set))
                =~= (old_out + piece) + spec_percent_encode(
                input@.subrange(i as int, n as int),
                set,
            ));
        }
    }
    proof {
        assert(input@.subrange(n as int, n as int) =~= Seq::<u8>::empty());
        assert(out@ + Seq::<u8>::empty() =~= out@);
    }
    out
}

pub fn percent_decode(input: &[u8]) -> (out: Vec<u8>)
    ensures
        out@ == spec_percent_decode(input@),
{
    let n = input.len();
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(input@.subrange(0, n as int) =~= input@);
        assert(out@ =~= Seq::<u8>::empty());
    }
    while i < n
        invariant
            i <= n,
            n == input@.len(),
            spec_percent_decode(input@) == out@ + spec_percent_decode(
                input@.subrange(i as int, n as int),
            ),
        decreases n - i,
    {
        let b = input[i];
        let ghost rest = input@.subrange(i as int, n as int);
        let ghost old_out = out@;
        if b == 0x25 && n - i >= 3 && is_hex(input[i + 1]) && is_hex(input[i + 2]) {
            let v = hex_val(input[i + 1]) * 16 + hex_val(input[i + 2]);
            proof {
                assert(rest.subrange(3, rest.len() as int) =~= input@.subrange(i + 3, n as int));
            }
            out.push(v);
            i += 3;
            proof {
                assert(old_out + (seq![v] + spec_percent_decode(input@.subrange(i as int, n as int)))
                    =~= out@ + spec_percent_decode(input@.subrange(i as int, n as int)));
            }
        } else {
            proof {
                assert(rest.subrange(1, rest.len() as int) =~= input@.subrange(i + 1, n as int));
            }
            out.push(b);
            i += 1;
            proof {
                assert(old_out + (seq![b] + spec_percent_decode(input@.subrange(i as int, n as int)))
                    =~= out@ + spec_percent_decode(input@.subrange(i as int, n as int)));
            }
        }
    }
    proof {
        assert(input@.subrange(n as int, n as int) =~= Seq::<u8>::empty());
        assert(out@ + Seq::<u8>::empty() =~= out@);
    }
    out
}

} // verus!
