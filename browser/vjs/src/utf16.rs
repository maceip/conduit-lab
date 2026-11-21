//! ECMA-262 §6.1.4 The String Type & §11.1.4 Static Semantics: UTF16EncodeCodePoint / CodePointAt.
//!
//! Models ECMAScript strings as sequences of 16-bit unsigned integer code units (`Vec<u16>`),
//! with machine-checked Verus specifications and proofs for surrogate pair decoding, UTF-8 and
//! lossless WTF-8 conversions, slicing, concatenation, `StringIndexOf`, `TrimString` (§7.1.4.1 /
//! WhiteSpace + LineTerminator), and `IsLessThan` code-unit ordering (§7.2.13).

use vstd::prelude::*;

verus! {

/// ECMAScript String value backed by UTF-16 code units (§6.1.4).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Utf16Str {
    pub units: Vec<u16>,
}

impl View for Utf16Str {
    type V = Seq<u16>;

    open spec fn view(&self) -> Seq<u16> {
        self.units@
    }
}

/// ECMA-262 §11.1.4 CodePointRecord returned by `CodePointAt(string, position)`.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct CodePointRecord {
    pub code_point: u32,
    pub code_unit_count: u8,
    pub is_unpaired_surrogate: bool,
}

// -------------------------------------------------------------------------------------------
// Specifications
// -------------------------------------------------------------------------------------------

/// Leading (high) surrogate: `0xD800..=0xDBFF`.
pub open spec fn spec_is_leading_surrogate(u: u16) -> bool {
    0xD800 <= u && u <= 0xDBFF
}

/// Trailing (low) surrogate: `0xDC00..=0xDFFF`.
pub open spec fn spec_is_trailing_surrogate(u: u16) -> bool {
    0xDC00 <= u && u <= 0xDFFF
}

/// Any UTF-16 surrogate code unit: `0xD800..=0xDFFF`.
pub open spec fn spec_is_surrogate(u: u16) -> bool {
    0xD800 <= u && u <= 0xDFFF
}

/// ECMA-262 §11.1.4 UTF16SurrogatePairToCodePoint(lead, trail).
pub open spec fn spec_surrogate_pair_to_code_point(lead: u16, trail: u16) -> u32 {
    (((lead as int - 0xD800) * 0x400) + (trail as int - 0xDC00) + 0x10000) as u32
}

/// ECMA-262 §11.1.4 CodePointAt(string, position).
pub open spec fn spec_code_point_at(s: Seq<u16>, position: int) -> CodePointRecord {
    let size = s.len();
    let first = s[position];
    if !spec_is_leading_surrogate(first) && !spec_is_trailing_surrogate(first) {
        CodePointRecord {
            code_point: first as u32,
            code_unit_count: 1,
            is_unpaired_surrogate: false,
        }
    } else if spec_is_trailing_surrogate(first) || position + 1 == size {
        CodePointRecord {
            code_point: first as u32,
            code_unit_count: 1,
            is_unpaired_surrogate: true,
        }
    } else {
        let second = s[position + 1];
        if !spec_is_trailing_surrogate(second) {
            CodePointRecord {
                code_point: first as u32,
                code_unit_count: 1,
                is_unpaired_surrogate: true,
            }
        } else {
            CodePointRecord {
                code_point: spec_surrogate_pair_to_code_point(first, second),
                code_unit_count: 2,
                is_unpaired_surrogate: false,
            }
        }
    }
}

/// ECMA-262 §11.1.4 UTF16EncodeCodePoint(cp) for `cp <= 0x10FFFF`.
pub open spec fn spec_utf16_encode_code_point(cp: u32) -> Seq<u16> {
    if cp <= 0xFFFF {
        seq![cp as u16]
    } else {
        let cu1 = (((cp as int - 0x10000) / 0x400) + 0xD800) as u16;
        let cu2 = (((cp as int - 0x10000) % 0x400) + 0xDC00) as u16;
        seq![cu1, cu2]
    }
}

/// ECMA-262 §7.2.9 IsStringWellFormedUnicode(string) from `pos`.
pub open spec fn spec_is_well_formed_from(s: Seq<u16>, pos: nat) -> bool
    decreases s.len() - pos,
{
    if pos >= s.len() {
        true
    } else {
        let cp = spec_code_point_at(s, pos as int);
        if cp.is_unpaired_surrogate {
            false
        } else {
            let next = pos + cp.code_unit_count as nat;
            if next <= pos || next > s.len() {
                false
            } else {
                spec_is_well_formed_from(s, next)
            }
        }
    }
}

/// Strict UTF-8 single scalar value decode at `pos` (RFC 3629: rejects overlongs, surrogates, > U+10FFFF).
pub open spec fn spec_utf8_decode_step(bytes: Seq<u8>, pos: nat) -> Option<(u32, nat)> {
    if pos >= bytes.len() {
        None
    } else {
        let b0 = bytes[pos as int];
        if b0 < 0x80 {
            Some((b0 as u32, 1))
        } else if b0 < 0xC2 {
            None
        } else if b0 <= 0xDF {
            if pos + 2 > bytes.len() {
                None
            } else {
                let b1 = bytes[(pos + 1) as int];
                if (b1 & 0xC0) != 0x80 {
                    None
                } else {
                    let cp = (((b0 & 0x1F) as u32) << 6) | ((b1 & 0x3F) as u32);
                    Some((cp, 2))
                }
            }
        } else if b0 <= 0xEF {
            if pos + 3 > bytes.len() {
                None
            } else {
                let b1 = bytes[(pos + 1) as int];
                let b2 = bytes[(pos + 2) as int];
                if (b1 & 0xC0) != 0x80 || (b2 & 0xC0) != 0x80 {
                    None
                } else if b0 == 0xE0 && b1 < 0xA0 {
                    None
                } else if b0 == 0xED && b1 >= 0xA0 {
                    // Reject UTF-16 surrogates U+D800..=U+DFFF in strict UTF-8.
                    None
                } else {
                    let cp = (((b0 & 0x0F) as u32) << 12)
                        | (((b1 & 0x3F) as u32) << 6)
                        | ((b2 & 0x3F) as u32);
                    Some((cp, 3))
                }
            }
        } else if b0 <= 0xF4 {
            if pos + 4 > bytes.len() {
                None
            } else {
                let b1 = bytes[(pos + 1) as int];
                let b2 = bytes[(pos + 2) as int];
                let b3 = bytes[(pos + 3) as int];
                if (b1 & 0xC0) != 0x80 || (b2 & 0xC0) != 0x80 || (b3 & 0xC0) != 0x80 {
                    None
                } else if b0 == 0xF0 && b1 < 0x90 {
                    None
                } else if b0 == 0xF4 && b1 >= 0x90 {
                    None
                } else {
                    let cp = (((b0 & 0x07) as u32) << 18)
                        | (((b1 & 0x3F) as u32) << 12)
                        | (((b2 & 0x3F) as u32) << 6)
                        | ((b3 & 0x3F) as u32);
                    Some((cp, 4))
                }
            }
        } else {
            None
        }
    }
}

/// Strict UTF-8 byte sequence to UTF-16 code units from `pos`.
pub open spec fn spec_utf8_to_utf16_from(bytes: Seq<u8>, pos: nat) -> Option<Seq<u16>>
    decreases bytes.len() - pos,
{
    if pos >= bytes.len() {
        Some(Seq::<u16>::empty())
    } else {
        match spec_utf8_decode_step(bytes, pos) {
            None => None,
            Some((cp, used)) => {
                if used == 0 || pos + used > bytes.len() {
                    None
                } else {
                    match spec_utf8_to_utf16_from(bytes, pos + used) {
                        None => None,
                        Some(rest) => Some(spec_utf16_encode_code_point(cp) + rest),
                    }
                }
            }
        }
    }
}

pub open spec fn spec_utf8_to_utf16(bytes: Seq<u8>) -> Option<Seq<u16>> {
    spec_utf8_to_utf16_from(bytes, 0)
}

/// Encode a single code point `0 <= cp <= 0x10FFFF` (including lone surrogates for WTF-8) as 1..4 bytes.
pub open spec fn spec_wtf8_encode_code_point(cp: u32) -> Seq<u8> {
    if cp <= 0x7F {
        seq![cp as u8]
    } else if cp <= 0x7FF {
        seq![
            (0xC0u32 | (cp >> 6)) as u8,
            (0x80u32 | (cp & 0x3F)) as u8,
        ]
    } else if cp <= 0xFFFF {
        seq![
            (0xE0u32 | (cp >> 12)) as u8,
            (0x80u32 | ((cp >> 6) & 0x3F)) as u8,
            (0x80u32 | (cp & 0x3F)) as u8,
        ]
    } else {
        seq![
            (0xF0u32 | (cp >> 18)) as u8,
            (0x80u32 | ((cp >> 12) & 0x3F)) as u8,
            (0x80u32 | ((cp >> 6) & 0x3F)) as u8,
            (0x80u32 | (cp & 0x3F)) as u8,
        ]
    }
}

/// Lossless WTF-8 encoding of `Seq<u16>` from `pos`: valid surrogate pairs encode as 4-byte scalar
/// sequences while unpaired surrogates encode as 3-byte WTF-8 sequences (`0xED 0xA0..0xBF 0x80..0xBF`).
pub open spec fn spec_utf16_to_wtf8_from(s: Seq<u16>, pos: nat) -> Seq<u8>
    decreases s.len() - pos,
{
    if pos >= s.len() {
        Seq::<u8>::empty()
    } else {
        let rec = spec_code_point_at(s, pos as int);
        let step: nat = if rec.code_unit_count == 2 && pos + 2 <= s.len() { 2 } else { 1 };
        spec_wtf8_encode_code_point(rec.code_point) + spec_utf16_to_wtf8_from(s, pos + step)
    }
}

pub open spec fn spec_utf16_to_wtf8(s: Seq<u16>) -> Seq<u8> {
    spec_utf16_to_wtf8_from(s, 0)
}

/// Clamped slice `[min(start, len) .. max(min(start, len), min(end, len))]`.
pub open spec fn spec_slice(s: Seq<u16>, start: nat, end: nat) -> Seq<u16> {
    let st: int = if start <= s.len() { start as int } else { s.len() as int };
    let en_raw: int = if end <= s.len() { end as int } else { s.len() as int };
    let en: int = if en_raw >= st { en_raw } else { st };
    s.subrange(st, en)
}

/// ECMA-262 §6.1.4 StringIndexOf(string, searchValue, fromIndex) search helper.
pub open spec fn spec_index_of_from(s: Seq<u16>, search: Seq<u16>, idx: nat) -> Option<nat>
    decreases (s.len() + 1) - idx,
{
    if idx + search.len() > s.len() {
        None
    } else if s.subrange(idx as int, (idx + search.len()) as int) == search {
        Some(idx)
    } else if idx >= s.len() {
        None
    } else {
        spec_index_of_from(s, search, idx + 1)
    }
}

/// ECMA-262 §6.1.4 StringIndexOf(string, searchValue, fromIndex).
pub open spec fn spec_string_index_of(s: Seq<u16>, search: Seq<u16>, from_index: nat) -> Option<nat> {
    if search.len() == 0 && from_index <= s.len() {
        Some(from_index)
    } else {
        spec_index_of_from(s, search, from_index)
    }
}

/// ECMA-262 §12.2 WhiteSpace + §12.3 LineTerminator (`StrWhiteSpaceChar` in §7.1.4.1).
/// Includes TAB (0x0009), LF (0x000A), VT (0x000B), FF (0x000C), CR (0x000D), SP (0x0020),
/// NBSP (0x00A0), OGHAM SPACE MARK (0x1680), EN QUAD..HAIR SPACE (0x2000..=0x200A),
/// LS (0x2028), PS (0x2029), NNBSP (0x202F), MMSP (0x205F), IDEOGRAPHIC SPACE (0x3000),
/// and ZWNBSP/BOM (0xFEFF). Excludes U+180E per ES2016+.
pub open spec fn spec_is_str_white_space(u: u16) -> bool {
    u == 0x0009
        || u == 0x000A
        || u == 0x000B
        || u == 0x000C
        || u == 0x000D
        || u == 0x0020
        || u == 0x00A0
        || u == 0x1680
        || (0x2000 <= u && u <= 0x200A)
        || u == 0x2028
        || u == 0x2029
        || u == 0x202F
        || u == 0x205F
        || u == 0x3000
        || u == 0xFEFF
}

pub open spec fn spec_first_non_ws(s: Seq<u16>, pos: nat) -> nat
    decreases s.len() - pos,
{
    if pos >= s.len() {
        s.len()
    } else if spec_is_str_white_space(s[pos as int]) {
        spec_first_non_ws(s, pos + 1)
    } else {
        pos
    }
}

pub open spec fn spec_last_non_ws_end(s: Seq<u16>, start: nat, end: nat) -> nat
    decreases end,
{
    if end <= start || end > s.len() {
        start
    } else if spec_is_str_white_space(s[(end - 1) as int]) {
        spec_last_non_ws_end(s, start, (end - 1) as nat)
    } else {
        end
    }
}

pub open spec fn spec_trim_start(s: Seq<u16>) -> Seq<u16> {
    let st = spec_first_non_ws(s, 0);
    s.subrange(st as int, s.len() as int)
}

pub open spec fn spec_trim_end(s: Seq<u16>) -> Seq<u16> {
    let en = spec_last_non_ws_end(s, 0, s.len());
    s.subrange(0, en as int)
}

/// ECMA-262 §7.1.4.1 / §22.1.3.32.1 TrimString(string, START+END).
pub open spec fn spec_trim(s: Seq<u16>) -> Seq<u16> {
    let st = spec_first_non_ws(s, 0);
    let en = spec_last_non_ws_end(s, st, s.len());
    s.subrange(st as int, en as int)
}

/// ECMA-262 §7.2.13 IsLessThan lexicographic UTF-16 code-unit comparison from `pos`.
pub open spec fn spec_utf16_lt_from(a: Seq<u16>, b: Seq<u16>, pos: nat) -> bool
    decreases a.len() - pos,
{
    if pos >= b.len() {
        false
    } else if pos >= a.len() {
        true
    } else if a[pos as int] < b[pos as int] {
        true
    } else if a[pos as int] > b[pos as int] {
        false
    } else {
        spec_utf16_lt_from(a, b, pos + 1)
    }
}

pub open spec fn spec_utf16_lt(a: Seq<u16>, b: Seq<u16>) -> bool {
    spec_utf16_lt_from(a, b, 0)
}

// -------------------------------------------------------------------------------------------
// Proofs & Lemmas
// -------------------------------------------------------------------------------------------

/// Bounds, surrogate classification, and scalar-value guarantees of `CodePointAt`.
pub proof fn lemma_code_point_at_properties(s: Seq<u16>, pos: int)
    requires
        0 <= pos < s.len(),
    ensures
        ({
            let r = spec_code_point_at(s, pos);
            &&& (r.code_unit_count == 1 || r.code_unit_count == 2)
            &&& pos + (r.code_unit_count as int) <= s.len()
            &&& r.code_point <= 0x10FFFF
            &&& (r.is_unpaired_surrogate <==> (0xD800 <= r.code_point && r.code_point <= 0xDFFF))
            &&& (r.code_unit_count == 2 ==> (0x10000 <= r.code_point && r.code_point <= 0x10FFFF && !r.is_unpaired_surrogate))
        }),
{
    let first = s[pos];
    if spec_is_leading_surrogate(first) && pos + 1 < s.len() && spec_is_trailing_surrogate(s[pos + 1]) {
        let second = s[pos + 1];
        assert(0 <= first as int - 0xD800 <= 0x3FF);
        assert(0 <= second as int - 0xDC00 <= 0x3FF);
        assert(((first as int - 0xD800) * 0x400) + (second as int - 0xDC00) + 0x10000 <= 0x10FFFF);
        assert(((first as int - 0xD800) * 0x400) + (second as int - 0xDC00) + 0x10000 >= 0x10000);
    }
}

/// Bijection / roundtrip between `UTF16EncodeCodePoint` and `CodePointAt` on Unicode scalar values.
pub proof fn lemma_utf16_encode_decode_roundtrip(cp: u32)
    requires
        cp <= 0x10FFFF,
        !(0xD800 <= cp && cp <= 0xDFFF),
    ensures
        ({
            let enc = spec_utf16_encode_code_point(cp);
            &&& (enc.len() == 1 || enc.len() == 2)
            &&& spec_code_point_at(enc, 0) == CodePointRecord {
                code_point: cp,
                code_unit_count: enc.len() as u8,
                is_unpaired_surrogate: false,
            }
        }),
{
    if cp <= 0xFFFF {
        let enc = spec_utf16_encode_code_point(cp);
        assert(enc.len() == 1);
        assert(enc[0] == cp as u16);
    } else {
        let d = cp as int - 0x10000;
        assert(0 <= d <= 0xFFFFF);
        let q = d / 0x400;
        let r = d % 0x400;
        assert(0 <= q <= 0x3FF);
        assert(0 <= r <= 0x3FF);
        assert(d == q * 0x400 + r);
        let cu1 = (q + 0xD800) as u16;
        let cu2 = (r + 0xDC00) as u16;
        assert(spec_is_leading_surrogate(cu1));
        assert(spec_is_trailing_surrogate(cu2));
        let enc = spec_utf16_encode_code_point(cp);
        assert(enc.len() == 2);
        assert(enc[0] == cu1);
        assert(enc[1] == cu2);
        assert(spec_surrogate_pair_to_code_point(cu1, cu2) == cp);
    }
}

pub proof fn lemma_utf8_decode_step_bounds(bytes: Seq<u8>, pos: nat)
    ensures
        match spec_utf8_decode_step(bytes, pos) {
            None => true,
            Some((cp, used)) => {
                &&& 1 <= used <= 4
                &&& pos + used <= bytes.len()
                &&& cp <= 0x10FFFF
                &&& !(0xD800 <= cp && cp <= 0xDFFF)
            }
        },
{
    if pos < bytes.len() {
        let b0 = bytes[pos as int];
        if b0 >= 0xC2 && b0 <= 0xDF && pos + 2 <= bytes.len() {
            let b1 = bytes[(pos + 1) as int];
            if (b1 & 0xC0) == 0x80 {
                let cp = (((b0 & 0x1F) as u32) << 6) | ((b1 & 0x3F) as u32);
                assert(cp <= 0x7FF) by (bit_vector)
                    requires b0 >= 0xC2u8, b0 <= 0xDFu8, (b1 & 0xC0u8) == 0x80u8,
                    cp == (((b0 & 0x1Fu8) as u32) << 6) | ((b1 & 0x3Fu8) as u32);
            }
        } else if b0 >= 0xE0 && b0 <= 0xEF && pos + 3 <= bytes.len() {
            let b1 = bytes[(pos + 1) as int];
            let b2 = bytes[(pos + 2) as int];
            if (b1 & 0xC0) == 0x80 && (b2 & 0xC0) == 0x80
                && !(b0 == 0xE0 && b1 < 0xA0)
                && !(b0 == 0xED && b1 >= 0xA0)
            {
                let cp = (((b0 & 0x0F) as u32) << 12)
                    | (((b1 & 0x3F) as u32) << 6)
                    | ((b2 & 0x3F) as u32);
                assert(cp <= 0xFFFF && !(0xD800 <= cp && cp <= 0xDFFF)) by (bit_vector)
                    requires
                        b0 >= 0xE0u8, b0 <= 0xEFu8,
                        (b1 & 0xC0u8) == 0x80u8, (b2 & 0xC0u8) == 0x80u8,
                        !(b0 == 0xE0u8 && b1 < 0xA0u8),
                        !(b0 == 0xEDu8 && b1 >= 0xA0u8),
                        cp == (((b0 & 0x0Fu8) as u32) << 12)
                            | (((b1 & 0x3Fu8) as u32) << 6)
                            | ((b2 & 0x3Fu8) as u32);
            }
        } else if b0 >= 0xF0 && b0 <= 0xF4 && pos + 4 <= bytes.len() {
            let b1 = bytes[(pos + 1) as int];
            let b2 = bytes[(pos + 2) as int];
            let b3 = bytes[(pos + 3) as int];
            if (b1 & 0xC0) == 0x80 && (b2 & 0xC0) == 0x80 && (b3 & 0xC0) == 0x80
                && !(b0 == 0xF0 && b1 < 0x90)
                && !(b0 == 0xF4 && b1 >= 0x90)
            {
                let cp = (((b0 & 0x07) as u32) << 18)
                    | (((b1 & 0x3F) as u32) << 12)
                    | (((b2 & 0x3F) as u32) << 6)
                    | ((b3 & 0x3F) as u32);
                assert(0x10000 <= cp && cp <= 0x10FFFF) by (bit_vector)
                    requires
                        b0 >= 0xF0u8, b0 <= 0xF4u8,
                        (b1 & 0xC0u8) == 0x80u8, (b2 & 0xC0u8) == 0x80u8, (b3 & 0xC0u8) == 0x80u8,
                        !(b0 == 0xF0u8 && b1 < 0x90u8),
                        !(b0 == 0xF4u8 && b1 >= 0x90u8),
                        cp == (((b0 & 0x07u8) as u32) << 18)
                            | (((b1 & 0x3Fu8) as u32) << 12)
                            | (((b2 & 0x3Fu8) as u32) << 6)
                            | ((b3 & 0x3Fu8) as u32);
            }
        }
    }
}

/// Slice length bound lemma.
pub proof fn lemma_slice_bounds(s: Seq<u16>, start: nat, end: nat)
    ensures
        spec_slice(s, start, end).len() <= s.len(),
        start <= end && end <= s.len() ==> spec_slice(s, start, end).len() == end - start,
{
}

/// Soundness and minimality of `spec_string_index_of`.
pub proof fn lemma_index_of_from_sound_and_minimal(s: Seq<u16>, search: Seq<u16>, idx: nat)
    ensures
        match spec_index_of_from(s, search, idx) {
            None => forall|j: int| idx <= j && j + search.len() <= s.len() ==>
                #[trigger] s.subrange(j, j + search.len()) != search,
            Some(found) => {
                &&& idx <= found
                &&& found + search.len() <= s.len()
                &&& s.subrange(found as int, (found + search.len()) as int) == search
                &&& forall|j: int| idx <= j && j < found ==>
                    #[trigger] s.subrange(j, j + search.len()) != search
            }
        },
    decreases (s.len() + 1) - idx,
{
    if idx + search.len() > s.len() {
    } else if s.subrange(idx as int, (idx + search.len()) as int) == search {
    } else if idx >= s.len() {
    } else {
        lemma_index_of_from_sound_and_minimal(s, search, idx + 1);
    }
}

pub proof fn lemma_first_non_ws_props(s: Seq<u16>, pos: nat)
    requires
        pos <= s.len(),
    ensures
        ({
            let r = spec_first_non_ws(s, pos);
            &&& pos <= r <= s.len()
            &&& (forall|k: int| pos <= k < r ==> spec_is_str_white_space(#[trigger] s[k]))
            &&& (r < s.len() ==> !spec_is_str_white_space(s[r as int]))
        }),
    decreases s.len() - pos,
{
    if pos < s.len() && spec_is_str_white_space(s[pos as int]) {
        lemma_first_non_ws_props(s, pos + 1);
    }
}

pub proof fn lemma_last_non_ws_end_props(s: Seq<u16>, start: nat, end: nat)
    requires
        start <= end <= s.len(),
    ensures
        ({
            let r = spec_last_non_ws_end(s, start, end);
            &&& start <= r <= end
            &&& (forall|k: int| r <= k < end ==> spec_is_str_white_space(#[trigger] s[k]))
            &&& (r > start ==> !spec_is_str_white_space(s[(r - 1) as int]))
        }),
    decreases end,
{
    if end > start && spec_is_str_white_space(s[(end - 1) as int]) {
        lemma_last_non_ws_end_props(s, start, (end - 1) as nat);
    }
}

/// Trimmed strings have no leading or trailing whitespace, and `spec_trim` is idempotent.
pub proof fn lemma_trim_clean_and_idempotent(s: Seq<u16>)
    ensures
        ({
            let t = spec_trim(s);
            &&& t.len() <= s.len()
            &&& (t.len() > 0 ==> !spec_is_str_white_space(t[0]) && !spec_is_str_white_space(t[t.len() - 1]))
            &&& spec_trim(t) == t
        }),
{
    lemma_first_non_ws_props(s, 0);
    let st = spec_first_non_ws(s, 0);
    lemma_last_non_ws_end_props(s, st, s.len());
    let en = spec_last_non_ws_end(s, st, s.len());
    let t = spec_trim(s);
    if t.len() > 0 {
        assert(st < en);
        assert(t[0] == s[st as int]);
        assert(t[t.len() - 1] == s[(en - 1) as int]);
        assert(!spec_is_str_white_space(t[0]));
        assert(!spec_is_str_white_space(t[t.len() - 1]));
        assert(spec_first_non_ws(t, 0) == 0);
        assert(spec_last_non_ws_end(t, 0, t.len()) == t.len());
        assert(spec_trim(t) =~= t);
    } else {
        assert(spec_first_non_ws(t, 0) == 0);
        assert(spec_last_non_ws_end(t, 0, 0) == 0);
        assert(spec_trim(t) =~= t);
    }
}

proof fn lemma_utf16_lt_from_irreflexive(a: Seq<u16>, pos: nat)
    ensures
        !spec_utf16_lt_from(a, a, pos),
    decreases a.len() - pos,
{
    if pos < a.len() {
        lemma_utf16_lt_from_irreflexive(a, pos + 1);
    }
}

proof fn lemma_utf16_lt_from_strict_order(a: Seq<u16>, b: Seq<u16>, pos: nat)
    requires
        pos <= a.len(),
        pos <= b.len(),
    ensures
        spec_utf16_lt_from(a, b, pos) ==> !spec_utf16_lt_from(b, a, pos),
        (!spec_utf16_lt_from(a, b, pos) && !spec_utf16_lt_from(b, a, pos)) <==>
            a.subrange(pos as int, a.len() as int) == b.subrange(pos as int, b.len() as int),
    decreases a.len() - pos,
{
    if pos >= a.len() || pos >= b.len() {
        if pos >= a.len() && pos >= b.len() {
            assert(a.subrange(pos as int, a.len() as int) =~= Seq::<u16>::empty());
            assert(b.subrange(pos as int, b.len() as int) =~= Seq::<u16>::empty());
        }
    } else {
        if a[pos as int] == b[pos as int] {
            lemma_utf16_lt_from_strict_order(a, b, pos + 1);
            if a.subrange((pos + 1) as int, a.len() as int) == b.subrange((pos + 1) as int, b.len() as int) {
                assert(a.subrange(pos as int, a.len() as int) =~=
                    seq![a[pos as int]] + a.subrange((pos + 1) as int, a.len() as int));
                assert(b.subrange(pos as int, b.len() as int) =~=
                    seq![b[pos as int]] + b.subrange((pos + 1) as int, b.len() as int));
            }
            if a.subrange(pos as int, a.len() as int) == b.subrange(pos as int, b.len() as int) {
                assert(a.subrange((pos + 1) as int, a.len() as int) =~=
                    a.subrange(pos as int, a.len() as int).subrange(1, (a.len() - pos) as int));
                assert(b.subrange((pos + 1) as int, b.len() as int) =~=
                    b.subrange(pos as int, b.len() as int).subrange(1, (b.len() - pos) as int));
            }
        } else {
            if a.subrange(pos as int, a.len() as int) == b.subrange(pos as int, b.len() as int) {
                assert(a[pos as int] == a.subrange(pos as int, a.len() as int)[0]);
                assert(b[pos as int] == b.subrange(pos as int, b.len() as int)[0]);
                assert(false);
            }
        }
    }
}

proof fn lemma_utf16_lt_from_transitive(a: Seq<u16>, b: Seq<u16>, c: Seq<u16>, pos: nat)
    requires
        spec_utf16_lt_from(a, b, pos),
        spec_utf16_lt_from(b, c, pos),
    ensures
        spec_utf16_lt_from(a, c, pos),
    decreases a.len() - pos,
{
    if pos < a.len() && pos < b.len() && pos < c.len() {
        if a[pos as int] == b[pos as int] && b[pos as int] == c[pos as int] {
            lemma_utf16_lt_from_transitive(a, b, c, pos + 1);
        }
    }
}

/// Strict total order (irreflexivity, asymmetry, transitivity, trichotomy) of `spec_utf16_lt`.
pub proof fn lemma_utf16_lt_strict_total_order(a: Seq<u16>, b: Seq<u16>)
    ensures
        !spec_utf16_lt(a, a),
        spec_utf16_lt(a, b) ==> !spec_utf16_lt(b, a),
        (!spec_utf16_lt(a, b) && !spec_utf16_lt(b, a)) <==> (a == b),
{
    lemma_utf16_lt_from_irreflexive(a, 0);
    lemma_utf16_lt_from_strict_order(a, b, 0);
    assert(a.subrange(0, a.len() as int) =~= a);
    assert(b.subrange(0, b.len() as int) =~= b);
}

pub proof fn lemma_utf16_lt_transitive(a: Seq<u16>, b: Seq<u16>, c: Seq<u16>)
    requires
        spec_utf16_lt(a, b),
        spec_utf16_lt(b, c),
    ensures
        spec_utf16_lt(a, c),
{
    lemma_utf16_lt_from_transitive(a, b, c, 0);
}

// -------------------------------------------------------------------------------------------
// Executable Implementations
// -------------------------------------------------------------------------------------------

pub fn is_leading_surrogate(u: u16) -> (r: bool)
    ensures
        r == spec_is_leading_surrogate(u),
{
    u >= 0xD800 && u <= 0xDBFF
}

pub fn is_trailing_surrogate(u: u16) -> (r: bool)
    ensures
        r == spec_is_trailing_surrogate(u),
{
    u >= 0xDC00 && u <= 0xDFFF
}

pub fn is_surrogate(u: u16) -> (r: bool)
    ensures
        r == spec_is_surrogate(u),
{
    u >= 0xD800 && u <= 0xDFFF
}

pub open spec fn spec_is_line_terminator(u: u16) -> bool {
    u == 0x000Au16 || u == 0x000Du16 || u == 0x2028u16 || u == 0x2029u16
}

pub open spec fn spec_is_white_space(u: u16) -> bool {
    spec_is_str_white_space(u) && !spec_is_line_terminator(u)
}

pub fn is_line_terminator(u: u16) -> (r: bool)
    ensures
        r == spec_is_line_terminator(u),
{
    u == 0x000A || u == 0x000D || u == 0x2028 || u == 0x2029
}

pub fn is_white_space(u: u16) -> (r: bool)
    ensures
        r == spec_is_white_space(u),
{
    is_str_white_space(u) && !is_line_terminator(u)
}

pub fn is_str_white_space(u: u16) -> (r: bool)
    ensures
        r == spec_is_str_white_space(u),
{
    u == 0x0009
        || u == 0x000A
        || u == 0x000B
        || u == 0x000C
        || u == 0x000D
        || u == 0x0020
        || u == 0x00A0
        || u == 0x1680
        || (u >= 0x2000 && u <= 0x200A)
        || u == 0x2028
        || u == 0x2029
        || u == 0x202F
        || u == 0x205F
        || u == 0x3000
        || u == 0xFEFF
}

pub fn utf16_encode_code_point(cp: u32) -> (out: Vec<u16>)
    requires
        cp <= 0x10FFFF,
    ensures
        out@ == spec_utf16_encode_code_point(cp),
{
    if cp <= 0xFFFF {
        let mut v: Vec<u16> = Vec::with_capacity(1);
        v.push(cp as u16);
        proof {
            assert(v@ =~= seq![cp as u16]);
        }
        v
    } else {
        let d: u32 = cp - 0x10000;
        let cu1: u16 = ((d / 0x400) + 0xD800) as u16;
        let cu2: u16 = ((d % 0x400) + 0xDC00) as u16;
        let mut v: Vec<u16> = Vec::with_capacity(2);
        v.push(cu1);
        v.push(cu2);
        proof {
            assert(v@ =~= seq![cu1, cu2]);
        }
        v
    }
}

fn utf8_decode_step_exec(bytes: &[u8], pos: usize) -> (res: Option<(u32, usize)>)
    requires
        pos <= bytes@.len(),
    ensures
        match (res, spec_utf8_decode_step(bytes@, pos as nat)) {
            (None, None) => true,
            (Some((cp, u)), Some((scp, su))) =>
                cp == scp && u as nat == su && 1 <= u && u <= 4 && pos + u <= bytes@.len() && cp <= 0x10FFFF,
            _ => false,
        },
{
    let n = bytes.len();
    if pos >= n {
        return None;
    }
    let b0 = bytes[pos];
    if b0 < 0x80 {
        return Some((b0 as u32, 1));
    }
    if b0 < 0xC2 {
        return None;
    }
    if b0 <= 0xDF {
        if n - pos < 2 {
            return None;
        }
        let b1 = bytes[pos + 1];
        if (b1 & 0xC0) != 0x80 {
            return None;
        }
        let cp = (((b0 & 0x1F) as u32) << 6) | ((b1 & 0x3F) as u32);
        proof {
            lemma_utf8_decode_step_bounds(bytes@, pos as nat);
        }
        return Some((cp, 2));
    }
    if b0 <= 0xEF {
        if n - pos < 3 {
            return None;
        }
        let b1 = bytes[pos + 1];
        let b2 = bytes[pos + 2];
        if (b1 & 0xC0) != 0x80 || (b2 & 0xC0) != 0x80 {
            return None;
        }
        if b0 == 0xE0 && b1 < 0xA0 {
            return None;
        }
        if b0 == 0xED && b1 >= 0xA0 {
            return None;
        }
        let cp = (((b0 & 0x0F) as u32) << 12)
            | (((b1 & 0x3F) as u32) << 6)
            | ((b2 & 0x3F) as u32);
        proof {
            lemma_utf8_decode_step_bounds(bytes@, pos as nat);
        }
        return Some((cp, 3));
    }
    if b0 <= 0xF4 {
        if n - pos < 4 {
            return None;
        }
        let b1 = bytes[pos + 1];
        let b2 = bytes[pos + 2];
        let b3 = bytes[pos + 3];
        if (b1 & 0xC0) != 0x80 || (b2 & 0xC0) != 0x80 || (b3 & 0xC0) != 0x80 {
            return None;
        }
        if b0 == 0xF0 && b1 < 0x90 {
            return None;
        }
        if b0 == 0xF4 && b1 >= 0x90 {
            return None;
        }
        let cp = (((b0 & 0x07) as u32) << 18)
            | (((b1 & 0x3F) as u32) << 12)
            | (((b2 & 0x3F) as u32) << 6)
            | ((b3 & 0x3F) as u32);
        proof {
            lemma_utf8_decode_step_bounds(bytes@, pos as nat);
        }
        return Some((cp, 4));
    }
    None
}

/// Strict UTF-8 decoder producing `Utf16Str`, proved equal to `spec_utf8_to_utf16`.
pub fn utf8_to_utf16(bytes: &[u8]) -> (res: Option<Utf16Str>)
    ensures
        match (res, spec_utf8_to_utf16(bytes@)) {
            (None, None) => true,
            (Some(s), Some(ss)) => s@ == ss,
            _ => false,
        },
{
    let n = bytes.len();
    let mut out: Vec<u16> = Vec::new();
    let mut pos: usize = 0;
    while pos < n
        invariant
            pos <= n,
            n == bytes@.len(),
            match spec_utf8_to_utf16_from(bytes@, pos as nat) {
                None => spec_utf8_to_utf16(bytes@) is None,
                Some(rest) => spec_utf8_to_utf16(bytes@) == Some(out@ + rest),
            },
        decreases n - pos,
    {
        match utf8_decode_step_exec(bytes, pos) {
            None => {
                return None;
            }
            Some((cp, used)) => {
                let enc = utf16_encode_code_point(cp);
                let ghost old_out = out@;
                let mut k: usize = 0;
                while k < enc.len()
                    invariant
                        k <= enc@.len(),
                        out@ == old_out + enc@.subrange(0, k as int),
                    decreases enc@.len() - k,
                {
                    out.push(enc[k]);
                    proof {
                        assert(out@ =~= old_out + enc@.subrange(0, (k + 1) as int));
                    }
                    k = k + 1;
                }
                proof {
                    assert(enc@.subrange(0, enc@.len() as int) =~= enc@);
                    assert(out@ =~= old_out + enc@);
                    match spec_utf8_to_utf16_from(bytes@, (pos + used) as nat) {
                        None => {}
                        Some(rest) => {
                            assert((old_out + enc@) + rest =~= old_out + (enc@ + rest));
                        }
                    }
                }
                pos = pos + used;
            }
        }
    }
    proof {
        assert(out@ + Seq::<u16>::empty() =~= out@);
    }
    Some(Utf16Str { units: out })
}

fn push_wtf8_code_point(out: &mut Vec<u8>, cp: u32)
    requires
        cp <= 0x10FFFF,
    ensures
        final(out)@ == old(out)@ + spec_wtf8_encode_code_point(cp),
{
    let ghost pre = out@;
    if cp <= 0x7F {
        out.push(cp as u8);
        proof {
            assert(out@ =~= pre + spec_wtf8_encode_code_point(cp));
        }
    } else if cp <= 0x7FF {
        let b0 = (0xC0u32 | (cp >> 6)) as u8;
        let b1 = (0x80u32 | (cp & 0x3F)) as u8;
        out.push(b0);
        out.push(b1);
        proof {
            assert(out@ =~= pre + spec_wtf8_encode_code_point(cp));
        }
    } else if cp <= 0xFFFF {
        let b0 = (0xE0u32 | (cp >> 12)) as u8;
        let b1 = (0x80u32 | ((cp >> 6) & 0x3F)) as u8;
        let b2 = (0x80u32 | (cp & 0x3F)) as u8;
        out.push(b0);
        out.push(b1);
        out.push(b2);
        proof {
            assert(out@ =~= pre + spec_wtf8_encode_code_point(cp));
        }
    } else {
        let b0 = (0xF0u32 | (cp >> 18)) as u8;
        let b1 = (0x80u32 | ((cp >> 12) & 0x3F)) as u8;
        let b2 = (0x80u32 | ((cp >> 6) & 0x3F)) as u8;
        let b3 = (0x80u32 | (cp & 0x3F)) as u8;
        out.push(b0);
        out.push(b1);
        out.push(b2);
        out.push(b3);
        proof {
            assert(out@ =~= pre + spec_wtf8_encode_code_point(cp));
        }
    }
}

impl Utf16Str {
    pub fn new() -> (s: Self)
        ensures
            s@ == Seq::<u16>::empty(),
    {
        Utf16Str { units: Vec::new() }
    }

    pub fn from_vec(units: Vec<u16>) -> (s: Self)
        ensures
            s@ == units@,
    {
        Utf16Str { units }
    }

    pub fn from_ascii(bytes: &[u8]) -> (s: Self)
        ensures
            s@.len() == bytes@.len(),
            forall|i: int| 0 <= i < bytes@.len() ==> #[trigger] s@[i] == bytes@[i] as u16,
    {
        let n = bytes.len();
        let mut units: Vec<u16> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                n == bytes@.len(),
                units@.len() == i,
                forall|k: int| 0 <= k < i ==> #[trigger] units@[k] == bytes@[k] as u16,
            decreases n - i,
        {
            units.push(bytes[i] as u16);
            i = i + 1;
        }
        Utf16Str { units }
    }

    pub fn len(&self) -> (n: usize)
        ensures
            n == self@.len(),
    {
        self.units.len()
    }

    pub fn is_empty(&self) -> (b: bool)
        ensures
            b == (self@.len() == 0),
    {
        self.units.len() == 0
    }

    pub fn code_unit_at(&self, index: usize) -> (u: u16)
        requires
            index < self@.len(),
        ensures
            u == self@[index as int],
    {
        self.units[index]
    }

    pub fn clone_str(&self) -> (out: Self)
        ensures
            out@ == self@,
    {
        let n = self.units.len();
        let mut v: Vec<u16> = Vec::with_capacity(n);
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                n == self@.len(),
                v@ == self@.subrange(0, i as int),
            decreases n - i,
        {
            v.push(self.units[i]);
            proof {
                assert(v@ =~= self@.subrange(0, (i + 1) as int));
            }
            i = i + 1;
        }
        proof {
            assert(self@.subrange(0, n as int) =~= self@);
        }
        Utf16Str { units: v }
    }

    pub fn eq_str(&self, other: &Self) -> (eq: bool)
        ensures
            eq == (self@ == other@),
    {
        let n = self.units.len();
        if n != other.units.len() {
            return false;
        }
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                n == self@.len(),
                n == other@.len(),
                forall|k: int| 0 <= k < i ==> self@[k] == other@[k],
            decreases n - i,
        {
            if self.units[i] != other.units[i] {
                return false;
            }
            i = i + 1;
        }
        proof {
            assert(self@ =~= other@);
        }
        true
    }

    /// ECMA-262 §11.1.4 CodePointAt(string, position).
    pub fn code_point_at(&self, position: usize) -> (rec: CodePointRecord)
        requires
            position < self@.len(),
        ensures
            rec == spec_code_point_at(self@, position as int),
    {
        let size = self.units.len();
        let first = self.units[position];
        if !is_leading_surrogate(first) && !is_trailing_surrogate(first) {
            CodePointRecord {
                code_point: first as u32,
                code_unit_count: 1,
                is_unpaired_surrogate: false,
            }
        } else if is_trailing_surrogate(first) || position + 1 == size {
            CodePointRecord {
                code_point: first as u32,
                code_unit_count: 1,
                is_unpaired_surrogate: true,
            }
        } else {
            let second = self.units[position + 1];
            if !is_trailing_surrogate(second) {
                CodePointRecord {
                    code_point: first as u32,
                    code_unit_count: 1,
                    is_unpaired_surrogate: true,
                }
            } else {
                let cp: u32 = ((first as u32 - 0xD800) * 0x400) + (second as u32 - 0xDC00) + 0x10000;
                CodePointRecord {
                    code_point: cp,
                    code_unit_count: 2,
                    is_unpaired_surrogate: false,
                }
            }
        }
    }

    /// ECMA-262 §7.2.9 IsStringWellFormedUnicode(string).
    pub fn is_well_formed_unicode(&self) -> (ok: bool)
        ensures
            ok == spec_is_well_formed_from(self@, 0),
    {
        let n = self.units.len();
        let mut pos: usize = 0;
        while pos < n
            invariant
                pos <= n,
                n == self@.len(),
                spec_is_well_formed_from(self@, 0) == spec_is_well_formed_from(self@, pos as nat),
            decreases n - pos,
        {
            proof {
                lemma_code_point_at_properties(self@, pos as int);
            }
            let rec = self.code_point_at(pos);
            if rec.is_unpaired_surrogate {
                return false;
            }
            pos = pos + (rec.code_unit_count as usize);
        }
        true
    }

    /// Lossless WTF-8 encoding of `self`, proved equal to `spec_utf16_to_wtf8(self@)`.
    pub fn utf16_to_wtf8_or_lossless(&self) -> (out: Vec<u8>)
        ensures
            out@ == spec_utf16_to_wtf8(self@),
    {
        let n = self.units.len();
        let mut out: Vec<u8> = Vec::new();
        let mut pos: usize = 0;
        while pos < n
            invariant
                pos <= n,
                n == self@.len(),
                spec_utf16_to_wtf8(self@) == out@ + spec_utf16_to_wtf8_from(self@, pos as nat),
            decreases n - pos,
        {
            proof {
                lemma_code_point_at_properties(self@, pos as int);
            }
            let rec = self.code_point_at(pos);
            let ghost pre = out@;
            let step: usize = if rec.code_unit_count == 2 { 2 } else { 1 };
            push_wtf8_code_point(&mut out, rec.code_point);
            proof {
                let enc = spec_wtf8_encode_code_point(rec.code_point);
                let tail = spec_utf16_to_wtf8_from(self@, (pos + step) as nat);
                assert((pre + enc) + tail =~= pre + (enc + tail));
            }
            pos = pos + step;
        }
        proof {
            assert(out@ + Seq::<u8>::empty() =~= out@);
        }
        out
    }

    /// Substring slice `[start..end]` clamped to `[0..len]`, proved equal to `spec_slice`.
    pub fn slice(&self, start: usize, end: usize) -> (out: Self)
        ensures
            out@ == spec_slice(self@, start as nat, end as nat),
    {
        let n = self.units.len();
        let st: usize = if start <= n { start } else { n };
        let en_raw: usize = if end <= n { end } else { n };
        let en: usize = if en_raw >= st { en_raw } else { st };
        let mut v: Vec<u16> = Vec::with_capacity(en - st);
        let mut i: usize = st;
        while i < en
            invariant
                st <= i <= en <= n,
                n == self@.len(),
                v@ == self@.subrange(st as int, i as int),
            decreases en - i,
        {
            v.push(self.units[i]);
            proof {
                assert(v@ =~= self@.subrange(st as int, (i + 1) as int));
            }
            i = i + 1;
        }
        Utf16Str { units: v }
    }

    /// Concatenation `self + other`, proved equal to `self@ + other@`.
    pub fn concat(&self, other: &Self) -> (out: Self)
        ensures
            out@ == self@ + other@,
    {
        let n1 = self.units.len();
        let n2 = other.units.len();
        let mut v: Vec<u16> = Vec::new();
        let mut i: usize = 0;
        while i < n1
            invariant
                i <= n1,
                n1 == self@.len(),
                v@ == self@.subrange(0, i as int),
            decreases n1 - i,
        {
            v.push(self.units[i]);
            proof {
                assert(v@ =~= self@.subrange(0, (i + 1) as int));
            }
            i = i + 1;
        }
        proof {
            assert(self@.subrange(0, n1 as int) =~= self@);
        }
        let mut j: usize = 0;
        while j < n2
            invariant
                j <= n2,
                n2 == other@.len(),
                v@ == self@ + other@.subrange(0, j as int),
            decreases n2 - j,
        {
            v.push(other.units[j]);
            proof {
                assert(v@ =~= self@ + other@.subrange(0, (j + 1) as int));
            }
            j = j + 1;
        }
        proof {
            assert(other@.subrange(0, n2 as int) =~= other@);
        }
        Utf16Str { units: v }
    }

    /// ECMA-262 §6.1.4 StringIndexOf(string, searchValue, fromIndex).
    pub fn index_of(&self, search: &Self, from_index: usize) -> (res: Option<usize>)
        ensures
            match (res, spec_string_index_of(self@, search@, from_index as nat)) {
                (None, None) => true,
                (Some(r), Some(sr)) => r as nat == sr,
                _ => false,
            },
    {
        let n = self.units.len();
        let m = search.units.len();
        if m == 0 && from_index <= n {
            return Some(from_index);
        }
        if from_index > n || m > n - from_index {
            return None;
        }
        let limit = n - m;
        let mut idx: usize = from_index;
        while idx <= limit
            invariant
                from_index <= idx,
                limit == n - m,
                m <= n,
                m > 0,
                n == self@.len(),
                m == search@.len(),
                spec_index_of_from(self@, search@, from_index as nat)
                    == spec_index_of_from(self@, search@, idx as nat),
            decreases (limit + 1) - idx,
        {
            let mut k: usize = 0;
            let mut matched: bool = true;
            while k < m && matched
                invariant
                    k <= m,
                    idx <= limit,
                    limit == n - m,
                    n == self@.len(),
                    m == search@.len(),
                    matched ==> forall|q: int| 0 <= q < k ==> self@[idx as int + q] == search@[q],
                    !matched ==> exists|q: int| 0 <= q < m && self@[idx as int + q] != search@[q],
                decreases (if matched { 1int } else { 0int }), m - k,
            {
                if self.units[idx + k] != search.units[k] {
                    matched = false;
                } else {
                    k = k + 1;
                }
            }
            if matched {
                proof {
                    assert(k == m);
                    assert(self@.subrange(idx as int, (idx + m) as int) =~= search@);
                }
                return Some(idx);
            } else {
                proof {
                    let q = choose|q: int| 0 <= q < m && self@[idx as int + q] != search@[q];
                    assert(self@.subrange(idx as int, (idx + m) as int)[q] == self@[idx as int + q]);
                    assert(self@.subrange(idx as int, (idx + m) as int) != search@);
                }
            }
            if idx == limit {
                proof {
                    assert((idx + 1) + m > n);
                    assert(spec_index_of_from(self@, search@, (idx + 1) as nat) is None);
                }
                return None;
            }
            idx = idx + 1;
        }
        None
    }

    pub fn trim_start(&self) -> (out: Self)
        ensures
            out@ == spec_trim_start(self@),
    {
        let n = self.units.len();
        let mut st: usize = 0;
        while st < n && is_str_white_space(self.units[st])
            invariant
                st <= n,
                n == self@.len(),
                spec_first_non_ws(self@, 0) == spec_first_non_ws(self@, st as nat),
            decreases n - st,
        {
            st = st + 1;
        }
        self.slice(st, n)
    }

    pub fn trim_end(&self) -> (out: Self)
        ensures
            out@ == spec_trim_end(self@),
    {
        let n = self.units.len();
        let mut en: usize = n;
        while en > 0 && is_str_white_space(self.units[en - 1])
            invariant
                en <= n,
                n == self@.len(),
                spec_last_non_ws_end(self@, 0, n as nat) == spec_last_non_ws_end(self@, 0, en as nat),
            decreases en,
        {
            en = en - 1;
        }
        self.slice(0, en)
    }

    /// ECMA-262 §7.1.4.1 / §22.1.3.32.1 TrimString(string, START+END).
    pub fn trim(&self) -> (out: Self)
        ensures
            out@ == spec_trim(self@),
    {
        let n = self.units.len();
        let mut st: usize = 0;
        while st < n && is_str_white_space(self.units[st])
            invariant
                st <= n,
                n == self@.len(),
                spec_first_non_ws(self@, 0) == spec_first_non_ws(self@, st as nat),
            decreases n - st,
        {
            st = st + 1;
        }
        let mut en: usize = n;
        while en > st && is_str_white_space(self.units[en - 1])
            invariant
                st <= en <= n,
                n == self@.len(),
                st as nat == spec_first_non_ws(self@, 0),
                spec_last_non_ws_end(self@, st as nat, n as nat)
                    == spec_last_non_ws_end(self@, st as nat, en as nat),
            decreases en - st,
        {
            en = en - 1;
        }
        self.slice(st, en)
    }

    /// ECMA-262 §7.2.13 IsLessThan lexicographic UTF-16 code-unit comparison.
    pub fn is_less_than(&self, other: &Self) -> (lt: bool)
        ensures
            lt == spec_utf16_lt(self@, other@),
    {
        let na = self.units.len();
        let nb = other.units.len();
        let mut pos: usize = 0;
        while pos < na && pos < nb
            invariant
                pos <= na,
                pos <= nb,
                na == self@.len(),
                nb == other@.len(),
                spec_utf16_lt(self@, other@) == spec_utf16_lt_from(self@, other@, pos as nat),
            decreases na - pos,
        {
            let ca = self.units[pos];
            let cb = other.units[pos];
            if ca < cb {
                return true;
            }
            if ca > cb {
                return false;
            }
            pos = pos + 1;
        }
        pos < nb
    }
}

} // verus!
