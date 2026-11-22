//! ECMA-262 §25.5 / RFC 8259 Verified `JSON` (`JSON.parse` and ES2019 well-formed
//! `JSON.stringify`) with Vest-style roundtrip and prefix-security theorems in Verus.
use vstd::prelude::*;

verus! {

// =======================================================================================
// 1. AST: `SpecJsonValue` and `JsonValue`
// =======================================================================================

/// Spec-level JSON value tree.
pub enum SpecJsonValue {
    Null,
    Bool(bool),
    Int(i64),
    Str(Seq<u16>),
    Array(Seq<SpecJsonValue>),
    Object(Seq<(Seq<u16>, SpecJsonValue)>),
}

/// Exec-level JSON value tree (§25.5).
#[derive(PartialEq, Eq, Debug)]
pub enum JsonValue {
    Null,
    Bool(bool),
    Int(i64),
    Str(Vec<u16>),
    Array(Vec<JsonValue>),
    Object(Vec<(Vec<u16>, JsonValue)>),
}

/// View mapping `JsonValue` to `SpecJsonValue`.
pub open spec fn spec_json_view(v: &JsonValue) -> SpecJsonValue
    decreases v,
{
    match v {
        JsonValue::Null => SpecJsonValue::Null,
        JsonValue::Bool(b) => SpecJsonValue::Bool(*b),
        JsonValue::Int(n) => SpecJsonValue::Int(*n),
        JsonValue::Str(s) => SpecJsonValue::Str(s@),
        JsonValue::Array(xs) => SpecJsonValue::Array(
            Seq::new(
                xs@.len(),
                |i: int|
                    if 0 <= i && i < xs@.len() {
                        spec_json_view(&xs@[i])
                    } else {
                        SpecJsonValue::Null
                    },
            ),
        ),
        JsonValue::Object(kvs) => SpecJsonValue::Object(
            Seq::new(
                kvs@.len(),
                |i: int|
                    if 0 <= i && i < kvs@.len() {
                        (kvs@[i].0@, spec_json_view(&kvs@[i].1))
                    } else {
                        (Seq::empty(), SpecJsonValue::Null)
                    },
            ),
        ),
    }
}

impl View for JsonValue {
    type V = SpecJsonValue;

    open spec fn view(&self) -> SpecJsonValue {
        spec_json_view(self)
    }
}

/// Structural node count of `SpecJsonValue` for termination proofs.
pub open spec fn spec_json_size(v: SpecJsonValue) -> nat
    decreases v,
{
    match v {
        SpecJsonValue::Null | SpecJsonValue::Bool(_) | SpecJsonValue::Int(_) | SpecJsonValue::Str(_) => 1,
        SpecJsonValue::Array(xs) => 1 + spec_json_array_size(xs),
        SpecJsonValue::Object(kvs) => 1 + spec_json_object_size(kvs),
    }
}

pub open spec fn spec_json_array_size(xs: Seq<SpecJsonValue>) -> nat
    decreases xs,
{
    if xs.len() == 0 {
        0
    } else {
        spec_json_size(xs[0]) + spec_json_array_size(xs.subrange(1, xs.len() as int))
    }
}

pub open spec fn spec_json_object_size(kvs: Seq<(Seq<u16>, SpecJsonValue)>) -> nat
    decreases kvs,
{
    if kvs.len() == 0 {
        0
    } else {
        1 + spec_json_size(kvs[0].1) + spec_json_object_size(kvs.subrange(1, kvs.len() as int))
    }
}

proof fn lemma_json_array_elem_smaller(xs: Seq<SpecJsonValue>, i: int)
    requires
        0 <= i < xs.len(),
    ensures
        spec_json_size(xs[i]) < 1 + spec_json_array_size(xs),
    decreases xs.len(),
{
    if i > 0 {
        let tail = xs.subrange(1, xs.len() as int);
        assert(tail[i - 1] == xs[i]);
        lemma_json_array_elem_smaller(tail, i - 1);
    }
}

proof fn lemma_json_object_elem_smaller(kvs: Seq<(Seq<u16>, SpecJsonValue)>, i: int)
    requires
        0 <= i < kvs.len(),
    ensures
        spec_json_size(kvs[i].1) < 1 + spec_json_object_size(kvs),
    decreases kvs.len(),
{
    if i > 0 {
        let tail = kvs.subrange(1, kvs.len() as int);
        assert(tail[i - 1] == kvs[i]);
        lemma_json_object_elem_smaller(tail, i - 1);
    }
}

// =======================================================================================
// 2. Spec: Lexical predicates, ES2019 `QuoteJSONString`, and `JSON.stringify`
// =======================================================================================

/// RFC 8259 §2 / ECMA-262 §25.5 JSON whitespace (`\t`, `\n`, `\r`, ` ` ONLY).
pub open spec fn spec_is_json_ws(c: u16) -> bool {
    c == 0x0009 || c == 0x000A || c == 0x000D || c == 0x0020
}

/// ASCII decimal digit `'0'..='9'`.
pub open spec fn spec_is_ascii_digit(c: u16) -> bool {
    0x0030 <= c && c <= 0x0039
}

/// ASCII hex digit (`0-9`, `A-F`, `a-f`).
pub open spec fn spec_is_hex_digit(c: u16) -> bool {
    (0x0030 <= c && c <= 0x0039) || (0x0041 <= c && c <= 0x0046) || (0x0061 <= c && c <= 0x0066)
}

/// Numeric value `0..16` of an ASCII hex digit.
pub open spec fn spec_hex_val(c: u16) -> nat {
    if 0x0030 <= c && c <= 0x0039 {
        (c - 0x0030) as nat
    } else if 0x0041 <= c && c <= 0x0046 {
        (c - 0x0041 + 10) as nat
    } else {
        (c - 0x0061 + 10) as nat
    }
}

/// Lowercase ASCII hex digit for nibble `0 <= n < 16` (ECMA-262 `UnicodeEscape`).
#[verifier::opaque]
pub open spec fn spec_lower_hex_char(n: nat) -> u16 {
    if n < 10 {
        (0x0030 + n) as u16
    } else {
        (0x0061 + n - 10) as u16
    }
}

/// Leading UTF-16 surrogate `0xD800..=0xDBFF`.
pub open spec fn spec_is_lead_surrogate(c: u16) -> bool {
    0xD800 <= c && c <= 0xDBFF
}

/// Trailing UTF-16 surrogate `0xDC00..=0xDFFF`.
pub open spec fn spec_is_trail_surrogate(c: u16) -> bool {
    0xDC00 <= c && c <= 0xDFFF
}

/// Well-formed UTF-16 predicate (no unpaired surrogates anywhere in `s`).
pub open spec fn spec_is_well_formed_utf16(s: Seq<u16>) -> bool {
    (forall|i: int|
        0 <= i < s.len() && spec_is_lead_surrogate(#[trigger] s[i])
            ==> i + 1 < s.len() && spec_is_trail_surrogate(s[i + 1]))
    && (forall|i: int|
        0 <= i < s.len() && spec_is_trail_surrogate(#[trigger] s[i])
            ==> i > 0 && spec_is_lead_surrogate(s[i - 1]))
}

/// ECMA-262 §25.5.2.2 `UnicodeEscape ( C )`: `\uXXXX` with 4 lowercase hex digits.
pub open spec fn spec_unicode_escape(c: u16) -> Seq<u16> {
    let n = c as nat;
    seq![
        0x005Cu16,
        0x0075u16,
        spec_lower_hex_char(n / 4096),
        spec_lower_hex_char((n / 256) % 16),
        spec_lower_hex_char((n / 16) % 16),
        spec_lower_hex_char(n % 16),
    ]
}

/// Encoded UTF-16 piece for a single code unit `c` (when not part of a valid surrogate pair).
pub open spec fn spec_single_unit_piece(c: u16) -> Seq<u16> {
    if c == 0x0008 {
        seq![0x005Cu16, 0x0062u16]
    } else if c == 0x0009 {
        seq![0x005Cu16, 0x0074u16]
    } else if c == 0x000A {
        seq![0x005Cu16, 0x006Eu16]
    } else if c == 0x000C {
        seq![0x005Cu16, 0x0066u16]
    } else if c == 0x000D {
        seq![0x005Cu16, 0x0072u16]
    } else if c == 0x0022 {
        seq![0x005Cu16, 0x0022u16]
    } else if c == 0x005C {
        seq![0x005Cu16, 0x005Cu16]
    } else if c < 0x0020 || spec_is_lead_surrogate(c) || spec_is_trail_surrogate(c) {
        spec_unicode_escape(c)
    } else {
        seq![c]
    }
}

/// Inner body of ES2019 well-formed `QuoteJSONString` (without outer `"` delimiters).
pub open spec fn spec_encode_string_body(s: Seq<u16>) -> Seq<u16>
    decreases s.len(),
{
    if s.len() == 0 {
        Seq::empty()
    } else {
        let c = s[0];
        if spec_is_lead_surrogate(c) && s.len() >= 2 && spec_is_trail_surrogate(s[1]) {
            seq![c, s[1]] + spec_encode_string_body(s.subrange(2, s.len() as int))
        } else {
            spec_single_unit_piece(c) + spec_encode_string_body(s.subrange(1, s.len() as int))
        }
    }
}

/// ECMA-262 §25.5.2.2 `QuoteJSONString ( value )`.
pub open spec fn spec_quote_string(s: Seq<u16>) -> Seq<u16> {
    seq![0x0022u16] + spec_encode_string_body(s) + seq![0x0022u16]
}

/// Non-negative integer digits (`n > 0`).
pub open spec fn spec_uint_digits(n: nat) -> Seq<u16>
    decreases n,
{
    if n == 0 {
        Seq::empty()
    } else {
        spec_uint_digits(n / 10) + seq![(0x0030 + (n % 10)) as u16]
    }
}

/// Canonical decimal serialization of `i64`.
pub open spec fn spec_stringify_int(v: i64) -> Seq<u16> {
    if v == 0 {
        seq![0x0030u16]
    } else if v < 0 {
        let mag: nat = (-(v as int)) as nat;
        seq![0x002Du16] + spec_uint_digits(mag)
    } else {
        spec_uint_digits(v as nat)
    }
}

/// Canonical `JSON.stringify` of `SpecJsonValue` (§25.5.2).
pub open spec fn spec_json_stringify(v: SpecJsonValue) -> Seq<u16>
    decreases v,
{
    match v {
        SpecJsonValue::Null => seq![0x006Eu16, 0x0075u16, 0x006Cu16, 0x006Cu16],
        SpecJsonValue::Bool(b) => {
            if b {
                seq![0x0074u16, 0x0072u16, 0x0075u16, 0x0065u16]
            } else {
                seq![0x0066u16, 0x0061u16, 0x006Cu16, 0x0073u16, 0x0065u16]
            }
        },
        SpecJsonValue::Int(n) => spec_stringify_int(n),
        SpecJsonValue::Str(s) => spec_quote_string(s),
        SpecJsonValue::Array(xs) => {
            seq![0x005Bu16] + spec_stringify_array_items(xs, 0) + seq![0x005Du16]
        },
        SpecJsonValue::Object(kvs) => {
            seq![0x007Bu16] + spec_stringify_object_items(kvs, 0) + seq![0x007Du16]
        },
    }
}

pub open spec fn spec_stringify_array_items(xs: Seq<SpecJsonValue>, idx: nat) -> Seq<u16>
    decreases xs, (if idx <= xs.len() { xs.len() - idx } else { 0 }),
{
    if idx >= xs.len() {
        Seq::empty()
    } else {
        let head = spec_json_stringify(xs[idx as int]);
        if idx + 1 == xs.len() {
            head
        } else {
            head + seq![0x002Cu16] + spec_stringify_array_items(xs, idx + 1)
        }
    }
}

pub open spec fn spec_stringify_object_items(
    kvs: Seq<(Seq<u16>, SpecJsonValue)>,
    idx: nat,
) -> Seq<u16>
    decreases kvs, (if idx <= kvs.len() { kvs.len() - idx } else { 0 }),
{
    if idx >= kvs.len() {
        Seq::empty()
    } else {
        let entry = kvs[idx as int];
        let head = spec_quote_string(entry.0) + seq![0x003Au16] + spec_json_stringify(entry.1);
        if idx + 1 == kvs.len() {
            head
        } else {
            head + seq![0x002Cu16] + spec_stringify_object_items(kvs, idx + 1)
        }
    }
}

// =======================================================================================
// 3. Spec: RFC 8259 / ECMA-262 §25.5 `JSON.parse`
// =======================================================================================

/// Skip JSON whitespace starting at `pos`.
pub open spec fn spec_skip_ws(input: Seq<u16>, pos: nat) -> nat
    decreases (if pos <= input.len() { input.len() - pos } else { 0 }),
{
    if pos < input.len() && spec_is_json_ws(input[pos as int]) {
        spec_skip_ws(input, pos + 1)
    } else if pos <= input.len() {
        pos
    } else {
        input.len()
    }
}

/// Parse `\uXXXX` 4-hex-digit escape at `input[pos..pos+4]`.
pub open spec fn spec_parse_hex4(input: Seq<u16>, pos: nat) -> Option<u16> {
    if pos + 4 <= input.len()
        && spec_is_hex_digit(input[pos as int])
        && spec_is_hex_digit(input[pos as int + 1])
        && spec_is_hex_digit(input[pos as int + 2])
        && spec_is_hex_digit(input[pos as int + 3])
    {
        let v = spec_hex_val(input[pos as int]) * 4096
            + spec_hex_val(input[pos as int + 1]) * 256
            + spec_hex_val(input[pos as int + 2]) * 16
            + spec_hex_val(input[pos as int + 3]);
        Some(v as u16)
    } else {
        None
    }
}

/// Parse body of a JSON string starting right after the opening `"` up to and consuming closing `"`.
pub open spec fn spec_parse_string_body(input: Seq<u16>, pos: nat) -> Option<(Seq<u16>, nat)>
    decreases (if pos <= input.len() { input.len() - pos } else { 0 }),
{
    if pos >= input.len() {
        None
    } else {
        let c = input[pos as int];
        if c == 0x0022 {
            Some((Seq::empty(), pos + 1))
        } else if c < 0x0020 {
            None
        } else if c == 0x005C {
            if pos + 1 >= input.len() {
                None
            } else {
                let esc = input[pos as int + 1];
                let step_opt: Option<(u16, nat)> = if esc == 0x0022 || esc == 0x005C || esc == 0x002F {
                    Some((esc, pos + 2))
                } else if esc == 0x0062 {
                    Some((0x0008, pos + 2))
                } else if esc == 0x0066 {
                    Some((0x000C, pos + 2))
                } else if esc == 0x006E {
                    Some((0x000A, pos + 2))
                } else if esc == 0x0072 {
                    Some((0x000D, pos + 2))
                } else if esc == 0x0074 {
                    Some((0x0009, pos + 2))
                } else if esc == 0x0075 {
                    match spec_parse_hex4(input, pos + 2) {
                        Some(u) => Some((u, pos + 6)),
                        None => None,
                    }
                } else {
                    None
                };
                match step_opt {
                    None => None,
                    Some((decoded, next_pos)) => {
                        match spec_parse_string_body(input, next_pos) {
                            Some((rest, end_pos)) => Some((seq![decoded] + rest, end_pos)),
                            None => None,
                        }
                    },
                }
            }
        } else {
            match spec_parse_string_body(input, pos + 1) {
                Some((rest, end_pos)) => Some((seq![c] + rest, end_pos)),
                None => None,
            }
        }
    }
}

/// Parse a JSON string literal starting at `input[pos] == '"'`.
pub open spec fn spec_parse_string(input: Seq<u16>, pos: nat) -> Option<(Seq<u16>, nat)> {
    if pos < input.len() && input[pos as int] == 0x0022 {
        spec_parse_string_body(input, pos + 1)
    } else {
        None
    }
}

/// Characters that could continue a JSON number token (digits, `.`, `e`, `E`, `+`, `-`).
/// A valid integer token must NOT be immediately followed by `.`, `e`, `E`, or another digit.
pub open spec fn spec_is_number_cont_char(c: u16) -> bool {
    spec_is_ascii_digit(c) || c == 0x002E || c == 0x0065 || c == 0x0045
}

/// Accumulate decimal digits starting at `pos` with `acc <= limit`.
pub open spec fn spec_parse_digits(
    input: Seq<u16>,
    pos: nat,
    acc: nat,
    limit: nat,
) -> Option<(nat, nat)>
    decreases (if pos <= input.len() { input.len() - pos } else { 0 }),
{
    if pos < input.len() && spec_is_ascii_digit(input[pos as int]) {
        let d = (input[pos as int] - 0x0030) as nat;
        let next_acc = acc * 10 + d;
        if next_acc > limit {
            None
        } else {
            spec_parse_digits(input, pos + 1, next_acc, limit)
        }
    } else if pos < input.len() && spec_is_number_cont_char(input[pos as int]) {
        None
    } else {
        Some((acc, pos))
    }
}

/// RFC 8259 §6 integer parser (`-?(0|[1-9][0-9]*)` within `i64` bounds, `-0 -> 0`).
pub open spec fn spec_parse_int(input: Seq<u16>, pos: nat) -> Option<(i64, nat)> {
    if pos >= input.len() {
        None
    } else {
        let neg = input[pos as int] == 0x002D;
        let p = if neg { pos + 1 } else { pos };
        if p >= input.len() || !spec_is_ascii_digit(input[p as int]) {
            None
        } else if input[p as int] == 0x0030 {
            let after = p + 1;
            if after < input.len() && spec_is_number_cont_char(input[after as int]) {
                None
            } else {
                Some((0i64, after))
            }
        } else {
            let limit: nat = if neg { 9_223_372_036_854_775_808nat } else { 9_223_372_036_854_775_807nat };
            let first = (input[p as int] - 0x0030) as nat;
            match spec_parse_digits(input, p + 1, first, limit) {
                None => None,
                Some((mag, end_pos)) => {
                    if neg {
                        Some(((-(mag as int)) as i64, end_pos))
                    } else {
                        Some((mag as i64, end_pos))
                    }
                },
            }
        }
    }
}

/// Fuel-bounded recursive RFC 8259 / §25.5 value parser starting at `pos` (skips leading ws).
pub open spec fn spec_parse_value(
    input: Seq<u16>,
    pos: nat,
    fuel: nat,
) -> Option<(SpecJsonValue, nat)>
    decreases fuel, 0nat,
{
    if fuel == 0 {
        None
    } else {
        let p = spec_skip_ws(input, pos);
        if p >= input.len() {
            None
        } else {
            let c = input[p as int];
            if c == 0x006E {
                // "null"
                if p + 4 <= input.len()
                    && input[p as int + 1] == 0x0075
                    && input[p as int + 2] == 0x006C
                    && input[p as int + 3] == 0x006C
                {
                    Some((SpecJsonValue::Null, p + 4))
                } else {
                    None
                }
            } else if c == 0x0074 {
                // "true"
                if p + 4 <= input.len()
                    && input[p as int + 1] == 0x0072
                    && input[p as int + 2] == 0x0075
                    && input[p as int + 3] == 0x0065
                {
                    Some((SpecJsonValue::Bool(true), p + 4))
                } else {
                    None
                }
            } else if c == 0x0066 {
                // "false"
                if p + 5 <= input.len()
                    && input[p as int + 1] == 0x0061
                    && input[p as int + 2] == 0x006C
                    && input[p as int + 3] == 0x0073
                    && input[p as int + 4] == 0x0065
                {
                    Some((SpecJsonValue::Bool(false), p + 5))
                } else {
                    None
                }
            } else if c == 0x0022 {
                match spec_parse_string(input, p) {
                    Some((s, end_pos)) => Some((SpecJsonValue::Str(s), end_pos)),
                    None => None,
                }
            } else if c == 0x005B {
                let p_in = spec_skip_ws(input, p + 1);
                if p_in < input.len() && input[p_in as int] == 0x005D {
                    Some((SpecJsonValue::Array(Seq::empty()), p_in + 1))
                } else {
                    spec_parse_array_items(input, p + 1, (fuel - 1) as nat)
                }
            } else if c == 0x007B {
                let p_in = spec_skip_ws(input, p + 1);
                if p_in < input.len() && input[p_in as int] == 0x007D {
                    Some((SpecJsonValue::Object(Seq::empty()), p_in + 1))
                } else {
                    spec_parse_object_items(input, p + 1, (fuel - 1) as nat)
                }
            } else if c == 0x002D || spec_is_ascii_digit(c) {
                match spec_parse_int(input, p) {
                    Some((n, end_pos)) => Some((SpecJsonValue::Int(n), end_pos)),
                    None => None,
                }
            } else {
                None
            }
        }
    }
}

pub open spec fn spec_parse_array_items(
    input: Seq<u16>,
    pos: nat,
    fuel: nat,
) -> Option<(SpecJsonValue, nat)>
    decreases fuel, (if pos <= input.len() { input.len() - pos + 1 } else { 1 }),
{
    if fuel == 0 || pos >= input.len() {
        None
    } else {
        match spec_parse_value(input, pos, fuel) {
            None => None,
            Some((elem, p_after)) => {
                let p_sep = spec_skip_ws(input, p_after);
                if p_sep >= input.len() {
                    None
                } else if input[p_sep as int] == 0x005D {
                    Some((SpecJsonValue::Array(seq![elem]), p_sep + 1))
                } else if input[p_sep as int] == 0x002C && p_sep + 1 > pos {
                    match spec_parse_array_items(input, p_sep + 1, fuel) {
                        Some((SpecJsonValue::Array(rest), end_pos)) => {
                            Some((SpecJsonValue::Array(seq![elem] + rest), end_pos))
                        },
                        _ => None,
                    }
                } else {
                    None
                }
            },
        }
    }
}

pub open spec fn spec_parse_object_items(
    input: Seq<u16>,
    pos: nat,
    fuel: nat,
) -> Option<(SpecJsonValue, nat)>
    decreases fuel, (if pos <= input.len() { input.len() - pos + 1 } else { 1 }),
{
    if fuel == 0 || pos >= input.len() {
        None
    } else {
        let p_key = spec_skip_ws(input, pos);
        match spec_parse_string(input, p_key) {
            None => None,
            Some((key, p_after_key)) => {
                let p_colon = spec_skip_ws(input, p_after_key);
                if p_colon >= input.len() || input[p_colon as int] != 0x003A {
                    None
                } else {
                    match spec_parse_value(input, p_colon + 1, fuel) {
                        None => None,
                        Some((val, p_after_val)) => {
                            let p_sep = spec_skip_ws(input, p_after_val);
                            if p_sep >= input.len() {
                                None
                            } else if input[p_sep as int] == 0x007D {
                                Some((SpecJsonValue::Object(seq![(key, val)]), p_sep + 1))
                            } else if input[p_sep as int] == 0x002C && p_sep + 1 > pos {
                                match spec_parse_object_items(input, p_sep + 1, fuel) {
                                    Some((SpecJsonValue::Object(rest), end_pos)) => {
                                        Some((SpecJsonValue::Object(seq![(key, val)] + rest), end_pos))
                                    },
                                    _ => None,
                                }
                            } else {
                                None
                            }
                        },
                    }
                }
            },
        }
    }
}

/// Top-level ECMA-262 §25.5.1 `JSON.parse`: requires full consumption up to trailing JSON whitespace.
pub open spec fn spec_json_parse(input: Seq<u16>, fuel: nat) -> Option<SpecJsonValue> {
    match spec_parse_value(input, 0, fuel) {
        None => None,
        Some((v, end_pos)) => {
            if spec_skip_ws(input, end_pos) == input.len() {
                Some(v)
            } else {
                None
            }
        },
    }
}

/// Predicate identifying self-delimiting JSON tokens (`"..."`, `{...}`, `[...]`, `true`, `false`, `null`).
pub open spec fn spec_is_self_delimiting_start_char(c: u16) -> bool {
    c == 0x0022 || c == 0x007B || c == 0x005B || c == 0x0074 || c == 0x0066 || c == 0x006E
}

/// True iff the token starting after optional whitespace at `pos` is self-delimiting.
pub open spec fn spec_is_self_delimiting_token(input: Seq<u16>, pos: nat) -> bool {
    let p = spec_skip_ws(input, pos);
    p < input.len() && spec_is_self_delimiting_start_char(input[p as int])
}

// =======================================================================================
// 4. Vest-Style Roundtrip, Well-Formed UTF-16, and Prefix-Security Proofs
// =======================================================================================

proof fn lemma_lower_hex_roundtrip(n: nat)
    requires
        n < 16,
    ensures
        spec_is_hex_digit(spec_lower_hex_char(n)),
        spec_hex_val(spec_lower_hex_char(n)) == n,
        0x0030 <= spec_lower_hex_char(n) && spec_lower_hex_char(n) <= 0x0066,
{
    reveal(spec_lower_hex_char);
}

proof fn lemma_unicode_escape_roundtrip(c: u16, rest_plus_tail: Seq<u16>)
    ensures
        ({
            let esc = spec_unicode_escape(c);
            let s = esc + rest_plus_tail;
            &&& esc.len() == 6
            &&& s[0] == 0x005Cu16
            &&& s[1] == 0x0075u16
            &&& spec_parse_hex4(s, 2) == Some(c)
        }),
{
    let n = c as nat;
    let d0 = n / 4096;
    let d1 = (n / 256) % 16;
    let d2 = (n / 16) % 16;
    let d3 = n % 16;
    let q1 = n / 16;
    assert(n == q1 * 16 + d3);
    let q2 = q1 / 16;
    assert(q2 == n / 256 && q1 == q2 * 16 + d2);
    let q3 = q2 / 16;
    assert(q3 == d0 && q2 == d0 * 16 + d1);
    lemma_lower_hex_roundtrip(d0);
    lemma_lower_hex_roundtrip(d1);
    lemma_lower_hex_roundtrip(d2);
    lemma_lower_hex_roundtrip(d3);
}

proof fn lemma_parse_string_body_bounds_and_prefix(
    input: Seq<u16>,
    pos: nat,
    trailing: Seq<u16>,
)
    requires
        spec_parse_string_body(input, pos).is_some(),
    ensures
        ({
            let (decoded, end_pos) = spec_parse_string_body(input, pos).unwrap();
            &&& pos < end_pos
            &&& end_pos <= input.len()
            &&& spec_parse_string_body(input + trailing, pos) == Some((decoded, end_pos))
        }),
    decreases (if pos <= input.len() { input.len() - pos } else { 0 }),
{
    let c = input[pos as int];
    let ext = input + trailing;
    assert(ext[pos as int] == c);
    if c == 0x0022 {
    } else if c == 0x005C {
        let esc = input[pos as int + 1];
        assert(ext[pos as int + 1] == esc);
        if esc == 0x0075 {
            assert(ext[pos as int + 2] == input[pos as int + 2]);
            assert(ext[pos as int + 3] == input[pos as int + 3]);
            assert(ext[pos as int + 4] == input[pos as int + 4]);
            assert(ext[pos as int + 5] == input[pos as int + 5]);
            assert(spec_parse_hex4(ext, pos + 2) == spec_parse_hex4(input, pos + 2));
            lemma_parse_string_body_bounds_and_prefix(input, pos + 6, trailing);
        } else {
            lemma_parse_string_body_bounds_and_prefix(input, pos + 2, trailing);
        }
    } else {
        lemma_parse_string_body_bounds_and_prefix(input, pos + 1, trailing);
    }
}

/// String prefix security: appending `trailing` code units never alters a parsed JSON string or consumed length.
pub proof fn lemma_parse_string_prefix_secure(
    input: Seq<u16>,
    pos: nat,
    trailing: Seq<u16>,
)
    requires
        spec_parse_string(input, pos).is_some(),
    ensures
        ({
            let (decoded, end_pos) = spec_parse_string(input, pos).unwrap();
            &&& pos < end_pos
            &&& end_pos <= input.len()
            &&& spec_parse_string(input + trailing, pos) == Some((decoded, end_pos))
        }),
{
    lemma_parse_string_body_bounds_and_prefix(input, pos + 1, trailing);
}

#[verifier::spinoff_prover]
proof fn lemma_encode_single_unit_piece(c: u16, tail1: Seq<u16>)
    ensures
        ({
            let piece = spec_single_unit_piece(c);
            match spec_parse_string_body(tail1, 0) {
                Some((rest, end_pos)) => {
                    spec_parse_string_body(piece + tail1, 0)
                        == Some((seq![c] + rest, piece.len() + end_pos))
                },
                None => spec_parse_string_body(piece + tail1, 0).is_none(),
            }
        }),
{
    let piece = spec_single_unit_piece(c);
    let comb = piece + tail1;
    lemma_parse_string_body_shift_general(piece, tail1);
    if c == 0x0008
        || c == 0x0009
        || c == 0x000A
        || c == 0x000C
        || c == 0x000D
        || c == 0x0022
        || c == 0x005C
    {
        assert(piece.len() == 2);
        assert(comb[0] == 0x005Cu16);
        assert(comb[1] == piece[1]);
    } else if c < 0x0020 || spec_is_lead_surrogate(c) || spec_is_trail_surrogate(c) {
        lemma_unicode_escape_roundtrip(c, tail1);
        assert(piece.len() == 6);
        assert(comb[0] == 0x005Cu16);
        assert(comb[1] == 0x0075u16);
    } else {
        assert(piece.len() == 1);
        assert(comb[0] == c);
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(50)]
proof fn lemma_encode_body_roundtrip(s: Seq<u16>, trailing: Seq<u16>)
    ensures
        ({
            let body = spec_encode_string_body(s);
            let full = body + seq![0x0022u16] + trailing;
            spec_parse_string_body(full, 0) == Some((s, (body.len() + 1) as nat))
        }),
    decreases s.len(),
{
    if s.len() == 0 {
        let full = Seq::<u16>::empty() + seq![0x0022u16] + trailing;
        assert(full[0] == 0x0022u16);
        assert(spec_parse_string_body(full, 0) == Some((Seq::<u16>::empty(), 1nat)));
        assert(s =~= Seq::<u16>::empty());
    } else {
        let c = s[0];
        if spec_is_lead_surrogate(c) && s.len() >= 2 && spec_is_trail_surrogate(s[1]) {
            let s2 = s.subrange(2, s.len() as int);
            lemma_encode_body_roundtrip(s2, trailing);
            let b2 = spec_encode_string_body(s2);
            let tail2 = b2 + seq![0x0022u16] + trailing;
            let full = (seq![c, s[1]] + b2) + seq![0x0022u16] + trailing;
            assert(full =~= seq![c, s[1]] + tail2);
            lemma_parse_string_body_shift(seq![c, s[1]], tail2);
            assert(seq![c, s[1]] + s2 =~= s);
        } else {
            let s1 = s.subrange(1, s.len() as int);
            lemma_encode_body_roundtrip(s1, trailing);
            let b1 = spec_encode_string_body(s1);
            let tail1 = b1 + seq![0x0022u16] + trailing;
            let piece = spec_single_unit_piece(c);
            let full = (piece + b1) + seq![0x0022u16] + trailing;
            assert(full =~= piece + tail1);
            lemma_encode_single_unit_piece(c, tail1);
            assert(seq![c] + s1 =~= s);
        }
    }
}

/// Shift invariance of `spec_parse_string_body`: parsing `prefix + rem` starting at `prefix.len()`
/// shifts the returned end index by `prefix.len()`.
proof fn lemma_parse_string_body_shift_general(prefix: Seq<u16>, rem: Seq<u16>)
    ensures
        match spec_parse_string_body(rem, 0) {
            Some((decoded, end_pos)) => {
                spec_parse_string_body(prefix + rem, prefix.len())
                    == Some((decoded, prefix.len() + end_pos))
            },
            None => spec_parse_string_body(prefix + rem, prefix.len()).is_none(),
        },
{
    lemma_parse_string_body_shift_at(prefix, rem, 0);
}

proof fn lemma_parse_string_body_shift_at(prefix: Seq<u16>, rem: Seq<u16>, k: nat)
    ensures
        match spec_parse_string_body(rem, k) {
            Some((decoded, end_pos)) => {
                spec_parse_string_body(prefix + rem, prefix.len() + k)
                    == Some((decoded, prefix.len() + end_pos))
            },
            None => spec_parse_string_body(prefix + rem, prefix.len() + k).is_none(),
        },
    decreases (if k <= rem.len() { rem.len() - k } else { 0 }),
{
    let comb = prefix + rem;
    let pk = prefix.len() + k;
    if k >= rem.len() {
        assert(pk >= comb.len());
    } else {
        let c = rem[k as int];
        assert(comb[pk as int] == c);
        if c == 0x0022 || c < 0x0020 {
        } else if c == 0x005C {
            if k + 1 < rem.len() {
                let esc = rem[k as int + 1];
                assert(comb[pk as int + 1] == esc);
                if esc == 0x0075 {
                    if k + 6 <= rem.len() {
                        assert(comb[pk as int + 2] == rem[k as int + 2]);
                        assert(comb[pk as int + 3] == rem[k as int + 3]);
                        assert(comb[pk as int + 4] == rem[k as int + 4]);
                        assert(comb[pk as int + 5] == rem[k as int + 5]);
                        assert(spec_parse_hex4(comb, pk + 2) == spec_parse_hex4(rem, k + 2));
                        if spec_parse_hex4(rem, k + 2).is_some() {
                            lemma_parse_string_body_shift_at(prefix, rem, k + 6);
                        }
                    } else {
                        assert(pk + 6 > comb.len());
                    }
                } else if esc == 0x0022
                    || esc == 0x005C
                    || esc == 0x002F
                    || esc == 0x0062
                    || esc == 0x0066
                    || esc == 0x006E
                    || esc == 0x0072
                    || esc == 0x0074
                {
                    lemma_parse_string_body_shift_at(prefix, rem, k + 2);
                }
            } else {
                assert(pk + 1 >= comb.len());
            }
        } else {
            lemma_parse_string_body_shift_at(prefix, rem, k + 1);
        }
    }
}

proof fn lemma_parse_string_body_shift(pair: Seq<u16>, rem: Seq<u16>)
    requires
        pair.len() == 2,
        pair[0] >= 0x0020 && pair[0] != 0x0022 && pair[0] != 0x005C,
        pair[1] >= 0x0020 && pair[1] != 0x0022 && pair[1] != 0x005C,
    ensures
        match spec_parse_string_body(rem, 0) {
            Some((decoded, end_pos)) => {
                spec_parse_string_body(pair + rem, 0)
                    == Some((seq![pair[0], pair[1]] + decoded, 2 + end_pos))
            },
            None => spec_parse_string_body(pair + rem, 0).is_none(),
        },
{
    reveal_with_fuel(spec_parse_string_body, 3);
    lemma_parse_string_body_shift_at(pair, rem, 0);
    let comb = pair + rem;
    assert(comb[0] == pair[0]);
    assert(comb[1] == pair[1]);
    if let Some((decoded, _)) = spec_parse_string_body(rem, 0) {
        assert(seq![pair[0]] + (seq![pair[1]] + decoded) =~= seq![pair[0], pair[1]] + decoded);
    }
}

/// **Vest-Style String Roundtrip + Prefix-Security Theorem**:
/// For every UTF-16 sequence `s` (including lone surrogates, control chars, quotes, backslashes)
/// and every `trailing` sequence, `spec_parse_string(spec_quote_string(s) + trailing, 0)`
/// returns `Some((s, spec_quote_string(s).len()))`!
pub proof fn lemma_quote_parse_string_roundtrip(s: Seq<u16>, trailing: Seq<u16>)
    ensures
        ({
            let quoted = spec_quote_string(s);
            &&& spec_parse_string(quoted + trailing, 0) == Some((s, quoted.len()))
            &&& spec_parse_string(quoted, 0) == Some((s, quoted.len()))
        }),
{
    lemma_encode_body_roundtrip(s, trailing);
    lemma_encode_body_roundtrip(s, Seq::empty());
    let body = spec_encode_string_body(s);
    let quoted = spec_quote_string(s);
    let qt = quoted + trailing;
    assert(qt[0] == 0x0022u16);
    let rem_t = body + seq![0x0022u16] + trailing;
    assert(qt =~= seq![0x0022u16] + rem_t);
    lemma_parse_string_body_shift_general(seq![0x0022u16], rem_t);

    assert(quoted[0] == 0x0022u16);
    let rem_0 = body + seq![0x0022u16] + Seq::<u16>::empty();
    assert(rem_0 =~= body + seq![0x0022u16]);
    assert(quoted =~= seq![0x0022u16] + rem_0);
    lemma_parse_string_body_shift_general(seq![0x0022u16], rem_0);
}

/// **ES2019 Well-Formed `JSON.stringify` Theorem**:
/// `spec_quote_string(s)` never emits an unpaired UTF-16 surrogate for ANY input `s: Seq<u16>`.
pub proof fn lemma_quote_string_well_formed_utf16(s: Seq<u16>)
    ensures
        spec_is_well_formed_utf16(spec_quote_string(s)),
{
    lemma_encode_body_well_formed(s);
    let body = spec_encode_string_body(s);
    let q = spec_quote_string(s);
    assert forall|i: int|
        0 <= i < q.len() && spec_is_lead_surrogate(#[trigger] q[i]) implies i + 1 < q.len()
        && spec_is_trail_surrogate(q[i + 1]) by {
        assert(1 <= i && i <= body.len());
        assert(q[i] == body[i - 1]);
        assert(i - 1 + 1 < body.len());
        assert(q[i + 1] == body[i]);
    }
    assert forall|i: int|
        0 <= i < q.len() && spec_is_trail_surrogate(#[trigger] q[i]) implies i > 0
        && spec_is_lead_surrogate(q[i - 1]) by {
        assert(1 <= i && i <= body.len());
        assert(q[i] == body[i - 1]);
        assert(i - 1 > 0);
        assert(q[i - 1] == body[i - 2]);
    }
}

proof fn lemma_encode_body_well_formed(s: Seq<u16>)
    ensures
        spec_is_well_formed_utf16(spec_encode_string_body(s)),
    decreases s.len(),
{
    if s.len() > 0 {
        let c = s[0];
        if spec_is_lead_surrogate(c) && s.len() >= 2 && spec_is_trail_surrogate(s[1]) {
            let s2 = s.subrange(2, s.len() as int);
            lemma_encode_body_well_formed(s2);
            let b2 = spec_encode_string_body(s2);
            let out = seq![c, s[1]] + b2;
            assert forall|i: int|
                0 <= i < out.len() && spec_is_lead_surrogate(#[trigger] out[i]) implies i + 1
                < out.len() && spec_is_trail_surrogate(out[i + 1]) by {
                if i >= 2 {
                    assert(out[i] == b2[i - 2]);
                    assert(out[i + 1] == b2[i - 1]);
                }
            }
            assert forall|i: int|
                0 <= i < out.len() && spec_is_trail_surrogate(#[trigger] out[i]) implies i > 0
                && spec_is_lead_surrogate(out[i - 1]) by {
                if i >= 2 {
                    assert(out[i] == b2[i - 2]);
                    assert(out[i - 1] == b2[i - 3]);
                }
            }
        } else {
            let s1 = s.subrange(1, s.len() as int);
            lemma_encode_body_well_formed(s1);
            let b1 = spec_encode_string_body(s1);
            if c < 0x0020 || spec_is_lead_surrogate(c) || spec_is_trail_surrogate(c) {
                let n = c as nat;
                lemma_lower_hex_roundtrip(n / 4096);
                lemma_lower_hex_roundtrip((n / 256) % 16);
                lemma_lower_hex_roundtrip((n / 16) % 16);
                lemma_lower_hex_roundtrip(n % 16);
            }
            let out = spec_encode_string_body(s);
            let plen = out.len() - b1.len();
            assert forall|i: int|
                0 <= i < out.len() && spec_is_lead_surrogate(#[trigger] out[i]) implies i + 1
                < out.len() && spec_is_trail_surrogate(out[i + 1]) by {
                assert(i >= plen);
                assert(out[i] == b1[i - plen]);
                assert(out[i + 1] == b1[i - plen + 1]);
            }
            assert forall|i: int|
                0 <= i < out.len() && spec_is_trail_surrogate(#[trigger] out[i]) implies i > 0
                && spec_is_lead_surrogate(out[i - 1]) by {
                assert(i >= plen);
                assert(out[i] == b1[i - plen]);
                assert(out[i - 1] == b1[i - plen - 1]);
            }
        }
    }
}

// ---------------------------------------------------------------------------------------
// Prefix Security for ALL Self-Delimiting JSON Tokens (Strings, Objects, Arrays, Literals)
// ---------------------------------------------------------------------------------------

proof fn lemma_skip_ws_bounded_prefix(input: Seq<u16>, pos: nat, trailing: Seq<u16>)
    requires
        pos <= input.len(),
        spec_skip_ws(input, pos) < input.len(),
    ensures
        pos <= spec_skip_ws(input, pos),
        !spec_is_json_ws(input[spec_skip_ws(input, pos) as int]),
        spec_skip_ws(input + trailing, pos) == spec_skip_ws(input, pos),
    decreases input.len() - pos,
{
    let ext = input + trailing;
    if pos < input.len() && spec_is_json_ws(input[pos as int]) {
        assert(ext[pos as int] == input[pos as int]);
        lemma_skip_ws_bounded_prefix(input, pos + 1, trailing);
    } else {
        assert(ext[pos as int] == input[pos as int]);
    }
}

proof fn lemma_skip_ws_ge(input: Seq<u16>, pos: nat)
    requires
        pos <= input.len(),
    ensures
        pos <= spec_skip_ws(input, pos) && spec_skip_ws(input, pos) <= input.len(),
    decreases input.len() - pos,
{
    if pos < input.len() && spec_is_json_ws(input[pos as int]) {
        lemma_skip_ws_ge(input, pos + 1);
    }
}

proof fn lemma_parse_digits_bounded_prefix(
    input: Seq<u16>,
    pos: nat,
    acc: nat,
    limit: nat,
    trailing: Seq<u16>,
)
    requires
        pos <= input.len(),
        spec_parse_digits(input, pos, acc, limit).is_some(),
        ({
            let (_, end_pos) = spec_parse_digits(input, pos, acc, limit).unwrap();
            end_pos < input.len()
        }),
    ensures
        ({
            let (v, end_pos) = spec_parse_digits(input, pos, acc, limit).unwrap();
            &&& pos <= end_pos
            &&& spec_parse_digits(input + trailing, pos, acc, limit) == Some((v, end_pos))
        }),
    decreases input.len() - pos,
{
    let ext = input + trailing;
    assert(ext[pos as int] == input[pos as int]);
    if spec_is_ascii_digit(input[pos as int]) {
        let d = (input[pos as int] - 0x0030) as nat;
        lemma_parse_digits_bounded_prefix(input, pos + 1, acc * 10 + d, limit, trailing);
    }
}

proof fn lemma_parse_int_bounded_prefix(input: Seq<u16>, pos: nat, trailing: Seq<u16>)
    requires
        pos < input.len(),
        spec_parse_int(input, pos).is_some(),
        ({
            let (_, end_pos) = spec_parse_int(input, pos).unwrap();
            end_pos < input.len()
        }),
    ensures
        ({
            let (n, end_pos) = spec_parse_int(input, pos).unwrap();
            &&& pos < end_pos
            &&& spec_parse_int(input + trailing, pos) == Some((n, end_pos))
        }),
{
    let ext = input + trailing;
    let neg = input[pos as int] == 0x002D;
    assert(ext[pos as int] == input[pos as int]);
    let p = if neg { pos + 1 } else { pos };
    assert(ext[p as int] == input[p as int]);
    if input[p as int] == 0x0030 {
        let after = p + 1;
        assert(ext[after as int] == input[after as int]);
    } else {
        let limit: nat = if neg { 9_223_372_036_854_775_808nat } else { 9_223_372_036_854_775_807nat };
        let first = (input[p as int] - 0x0030) as nat;
        lemma_parse_digits_bounded_prefix(input, p + 1, first, limit, trailing);
    }
}

/// Consumed-length bound for `spec_parse_value`, `spec_parse_array_items`, `spec_parse_object_items`.
proof fn lemma_parse_value_bounds(input: Seq<u16>, pos: nat, fuel: nat)
    requires
        pos <= input.len(),
        spec_parse_value(input, pos, fuel).is_some(),
    ensures
        ({
            let (_, end_pos) = spec_parse_value(input, pos, fuel).unwrap();
            pos < end_pos && end_pos <= input.len()
        }),
    decreases fuel, 0nat,
{
    lemma_skip_ws_ge(input, pos);
    let p = spec_skip_ws(input, pos);
    let c = input[p as int];
    if c == 0x0022 {
        lemma_parse_string_prefix_secure(input, p, Seq::empty());
    } else if c == 0x005B {
        lemma_skip_ws_ge(input, p + 1);
        let p_in = spec_skip_ws(input, p + 1);
        if !(p_in < input.len() && input[p_in as int] == 0x005D) {
            lemma_parse_array_bounds(input, p + 1, (fuel - 1) as nat);
        }
    } else if c == 0x007B {
        lemma_skip_ws_ge(input, p + 1);
        let p_in = spec_skip_ws(input, p + 1);
        if !(p_in < input.len() && input[p_in as int] == 0x007D) {
            lemma_parse_object_bounds(input, p + 1, (fuel - 1) as nat);
        }
    } else if c == 0x002D || spec_is_ascii_digit(c) {
        lemma_parse_int_bounds(input, p);
    }
}

proof fn lemma_parse_digits_bounds(input: Seq<u16>, pos: nat, acc: nat, limit: nat)
    requires
        pos <= input.len(),
        spec_parse_digits(input, pos, acc, limit).is_some(),
    ensures
        ({
            let (_, end_pos) = spec_parse_digits(input, pos, acc, limit).unwrap();
            pos <= end_pos && end_pos <= input.len()
        }),
    decreases input.len() - pos,
{
    if pos < input.len() && spec_is_ascii_digit(input[pos as int]) {
        let d = (input[pos as int] - 0x0030) as nat;
        lemma_parse_digits_bounds(input, pos + 1, acc * 10 + d, limit);
    }
}

proof fn lemma_parse_int_bounds(input: Seq<u16>, pos: nat)
    requires
        pos < input.len(),
        spec_parse_int(input, pos).is_some(),
    ensures
        ({
            let (_, end_pos) = spec_parse_int(input, pos).unwrap();
            pos < end_pos && end_pos <= input.len()
        }),
{
    let neg = input[pos as int] == 0x002D;
    let p = if neg { pos + 1 } else { pos };
    if input[p as int] != 0x0030 {
        let limit: nat = if neg { 9_223_372_036_854_775_808nat } else { 9_223_372_036_854_775_807nat };
        let first = (input[p as int] - 0x0030) as nat;
        lemma_parse_digits_bounds(input, p + 1, first, limit);
    }
}

proof fn lemma_parse_array_bounds(input: Seq<u16>, pos: nat, fuel: nat)
    requires
        pos <= input.len(),
        spec_parse_array_items(input, pos, fuel).is_some(),
    ensures
        ({
            let (_, end_pos) = spec_parse_array_items(input, pos, fuel).unwrap();
            pos < end_pos && end_pos <= input.len()
        }),
    decreases fuel, (if pos <= input.len() { input.len() - pos + 1 } else { 1 }),
{
    lemma_parse_value_bounds(input, pos, fuel);
    let (_, p_after) = spec_parse_value(input, pos, fuel).unwrap();
    lemma_skip_ws_ge(input, p_after);
    let p_sep = spec_skip_ws(input, p_after);
    if input[p_sep as int] == 0x002C {
        lemma_parse_array_bounds(input, p_sep + 1, fuel);
    }
}

proof fn lemma_parse_object_bounds(input: Seq<u16>, pos: nat, fuel: nat)
    requires
        pos <= input.len(),
        spec_parse_object_items(input, pos, fuel).is_some(),
    ensures
        ({
            let (_, end_pos) = spec_parse_object_items(input, pos, fuel).unwrap();
            pos < end_pos && end_pos <= input.len()
        }),
    decreases fuel, (if pos <= input.len() { input.len() - pos + 1 } else { 1 }),
{
    lemma_skip_ws_ge(input, pos);
    let p_key = spec_skip_ws(input, pos);
    lemma_parse_string_prefix_secure(input, p_key, Seq::empty());
    let (_, p_after_key) = spec_parse_string(input, p_key).unwrap();
    lemma_skip_ws_ge(input, p_after_key);
    let p_colon = spec_skip_ws(input, p_after_key);
    lemma_parse_value_bounds(input, p_colon + 1, fuel);
    let (_, p_after_val) = spec_parse_value(input, p_colon + 1, fuel).unwrap();
    lemma_skip_ws_ge(input, p_after_val);
    let p_sep = spec_skip_ws(input, p_after_val);
    if input[p_sep as int] == 0x002C {
        lemma_parse_object_bounds(input, p_sep + 1, fuel);
    }
}

/// Mutual induction helper for Vest-style prefix security:
/// holds whenever either the token at `pos` is self-delimiting OR `end_pos < input.len()`.
#[verifier::spinoff_prover]
proof fn lemma_parse_value_prefix_core(
    input: Seq<u16>,
    pos: nat,
    fuel: nat,
    trailing: Seq<u16>,
)
    requires
        pos <= input.len(),
        spec_parse_value(input, pos, fuel).is_some(),
        spec_is_self_delimiting_token(input, pos)
            || spec_parse_value(input, pos, fuel).unwrap().1 < input.len(),
    ensures
        spec_parse_value(input + trailing, pos, fuel) == spec_parse_value(input, pos, fuel),
    decreases fuel, 0nat,
{
    lemma_parse_value_bounds(input, pos, fuel);
    lemma_skip_ws_ge(input, pos);
    let p = spec_skip_ws(input, pos);
    lemma_skip_ws_bounded_prefix(input, pos, trailing);
    let ext = input + trailing;
    let c = input[p as int];
    assert(ext[p as int] == c);
    if c == 0x006E {
        assert(ext[p as int + 1] == input[p as int + 1]);
        assert(ext[p as int + 2] == input[p as int + 2]);
        assert(ext[p as int + 3] == input[p as int + 3]);
    } else if c == 0x0074 {
        assert(ext[p as int + 1] == input[p as int + 1]);
        assert(ext[p as int + 2] == input[p as int + 2]);
        assert(ext[p as int + 3] == input[p as int + 3]);
    } else if c == 0x0066 {
        assert(ext[p as int + 1] == input[p as int + 1]);
        assert(ext[p as int + 2] == input[p as int + 2]);
        assert(ext[p as int + 3] == input[p as int + 3]);
        assert(ext[p as int + 4] == input[p as int + 4]);
    } else if c == 0x0022 {
        lemma_parse_string_prefix_secure(input, p, trailing);
    } else if c == 0x005B {
        lemma_skip_ws_ge(input, p + 1);
        let p_in = spec_skip_ws(input, p + 1);
        if p_in < input.len() && input[p_in as int] == 0x005D {
            lemma_skip_ws_bounded_prefix(input, p + 1, trailing);
            assert(ext[p_in as int] == 0x005Du16);
        } else {
            lemma_parse_array_bounds(input, p + 1, (fuel - 1) as nat);
            assert(spec_parse_value(input, p + 1, (fuel - 1) as nat).is_some());
            assert(p_in < input.len());
            lemma_skip_ws_bounded_prefix(input, p + 1, trailing);
            assert(ext[p_in as int] == input[p_in as int]);
            lemma_parse_array_prefix_core(input, p + 1, (fuel - 1) as nat, trailing);
        }
    } else if c == 0x007B {
        lemma_skip_ws_ge(input, p + 1);
        let p_in = spec_skip_ws(input, p + 1);
        if p_in < input.len() && input[p_in as int] == 0x007D {
            lemma_skip_ws_bounded_prefix(input, p + 1, trailing);
            assert(ext[p_in as int] == 0x007Du16);
        } else {
            lemma_parse_object_bounds(input, p + 1, (fuel - 1) as nat);
            assert(spec_parse_string(input, p_in).is_some());
            assert(p_in < input.len());
            lemma_skip_ws_bounded_prefix(input, p + 1, trailing);
            assert(ext[p_in as int] == input[p_in as int]);
            lemma_parse_object_prefix_core(input, p + 1, (fuel - 1) as nat, trailing);
        }
    } else {
        lemma_parse_int_bounded_prefix(input, p, trailing);
    }
}

#[verifier::spinoff_prover]
proof fn lemma_parse_array_prefix_core(
    input: Seq<u16>,
    pos: nat,
    fuel: nat,
    trailing: Seq<u16>,
)
    requires
        pos < input.len(),
        spec_parse_array_items(input, pos, fuel).is_some(),
    ensures
        spec_parse_array_items(input + trailing, pos, fuel)
            == spec_parse_array_items(input, pos, fuel),
    decreases fuel, (if pos <= input.len() { input.len() - pos + 1 } else { 1 }),
{
    let ext = input + trailing;
    lemma_parse_value_bounds(input, pos, fuel);
    let (_, p_after) = spec_parse_value(input, pos, fuel).unwrap();
    lemma_skip_ws_ge(input, p_after);
    let p_sep = spec_skip_ws(input, p_after);
    assert(p_sep < input.len());
    assert(p_after <= p_sep && p_after < input.len());
    lemma_parse_value_prefix_core(input, pos, fuel, trailing);
    lemma_skip_ws_bounded_prefix(input, p_after, trailing);
    assert(ext[p_sep as int] == input[p_sep as int]);
    if input[p_sep as int] == 0x002C {
        lemma_parse_array_bounds(input, p_sep + 1, fuel);
        lemma_parse_array_prefix_core(input, p_sep + 1, fuel, trailing);
    }
}

#[verifier::spinoff_prover]
proof fn lemma_parse_object_prefix_core(
    input: Seq<u16>,
    pos: nat,
    fuel: nat,
    trailing: Seq<u16>,
)
    requires
        pos < input.len(),
        spec_parse_object_items(input, pos, fuel).is_some(),
    ensures
        spec_parse_object_items(input + trailing, pos, fuel)
            == spec_parse_object_items(input, pos, fuel),
    decreases fuel, (if pos <= input.len() { input.len() - pos + 1 } else { 1 }),
{
    let ext = input + trailing;
    lemma_skip_ws_ge(input, pos);
    let p_key = spec_skip_ws(input, pos);
    lemma_parse_string_prefix_secure(input, p_key, trailing);
    lemma_skip_ws_bounded_prefix(input, pos, trailing);
    let (_, p_after_key) = spec_parse_string(input, p_key).unwrap();
    lemma_skip_ws_ge(input, p_after_key);
    let p_colon = spec_skip_ws(input, p_after_key);
    lemma_skip_ws_bounded_prefix(input, p_after_key, trailing);
    assert(ext[p_colon as int] == 0x003Au16);

    lemma_parse_value_bounds(input, p_colon + 1, fuel);
    let (_, p_after_val) = spec_parse_value(input, p_colon + 1, fuel).unwrap();
    lemma_skip_ws_ge(input, p_after_val);
    let p_sep = spec_skip_ws(input, p_after_val);
    assert(p_sep < input.len());
    assert(p_after_val <= p_sep && p_after_val < input.len());
    lemma_parse_value_prefix_core(input, p_colon + 1, fuel, trailing);
    lemma_skip_ws_bounded_prefix(input, p_after_val, trailing);
    assert(ext[p_sep as int] == input[p_sep as int]);
    if input[p_sep as int] == 0x002C {
        lemma_parse_object_bounds(input, p_sep + 1, fuel);
        lemma_parse_object_prefix_core(input, p_sep + 1, fuel, trailing);
    }
}

/// **Vest-Style JSON Prefix-Security Theorem**:
/// For every self-delimiting JSON token (`"..."`, `{...}`, `[...]`, `true`, `false`, `null`,
/// including nested numbers, strings, arrays, and objects inside `{...}` or `[...]`),
/// if `spec_parse_value(input, pos, fuel) == Some((val, consumed))`, then appending ANY
/// `trailing` code units cannot alter either the parsed `SpecJsonValue` or `consumed`!
pub proof fn lemma_json_prefix_security(
    input: Seq<u16>,
    pos: nat,
    fuel: nat,
    trailing: Seq<u16>,
)
    requires
        pos <= input.len(),
        spec_is_self_delimiting_token(input, pos),
        spec_parse_value(input, pos, fuel).is_some(),
    ensures
        spec_parse_value(input + trailing, pos, fuel) == spec_parse_value(input, pos, fuel),
{
    lemma_parse_value_prefix_core(input, pos, fuel, trailing);
}

/// Serialize → Parse Roundtrip Theorem for JSON literals and strings (with arbitrary trailing suffix!).
pub proof fn lemma_json_self_delimiting_primitive_roundtrip(
    v: SpecJsonValue,
    trailing: Seq<u16>,
    fuel: nat,
)
    requires
        fuel >= 1,
        match v {
            SpecJsonValue::Null | SpecJsonValue::Bool(_) | SpecJsonValue::Str(_) => true,
            _ => false,
        },
    ensures
        ({
            let encoded = spec_json_stringify(v);
            &&& spec_parse_value(encoded + trailing, 0, fuel) == Some((v, encoded.len()))
            &&& spec_json_parse(encoded, fuel) == Some(v)
        }),
{
    let encoded = spec_json_stringify(v);
    let ext = encoded + trailing;
    match v {
        SpecJsonValue::Null => {
            assert(encoded.len() == 4);
            assert(!spec_is_json_ws(encoded[0]));
            assert(spec_skip_ws(ext, 0) == 0);
            assert(spec_skip_ws(encoded, 0) == 0);
            assert(spec_skip_ws(encoded, 4) == 4);
        },
        SpecJsonValue::Bool(b) => {
            if b {
                assert(encoded.len() == 4);
                assert(!spec_is_json_ws(encoded[0]));
                assert(spec_skip_ws(ext, 0) == 0);
                assert(spec_skip_ws(encoded, 0) == 0);
                assert(spec_skip_ws(encoded, 4) == 4);
            } else {
                assert(encoded.len() == 5);
                assert(!spec_is_json_ws(encoded[0]));
                assert(spec_skip_ws(ext, 0) == 0);
                assert(spec_skip_ws(encoded, 0) == 0);
                assert(spec_skip_ws(encoded, 5) == 5);
            }
        },
        SpecJsonValue::Str(s) => {
            lemma_quote_parse_string_roundtrip(s, trailing);
            assert(encoded[0] == 0x0022u16);
            assert(ext[0] == 0x0022u16);
            assert(spec_skip_ws(ext, 0) == 0);
            assert(spec_skip_ws(encoded, 0) == 0);
            assert(spec_skip_ws(encoded, encoded.len()) == encoded.len());
        },
        _ => {},
    }
}

/// Serialize → Parse Roundtrip Theorem for empty JSON containers `[]` and `{}` (with trailing suffix).
pub proof fn lemma_json_empty_containers_roundtrip(trailing: Seq<u16>, fuel: nat)
    requires
        fuel >= 1,
    ensures
        ({
            let empty_arr = SpecJsonValue::Array(Seq::empty());
            let enc_arr = spec_json_stringify(empty_arr);
            &&& spec_parse_value(enc_arr + trailing, 0, fuel) == Some((empty_arr, enc_arr.len()))
            &&& spec_json_parse(enc_arr, fuel) == Some(empty_arr)
        }),
        ({
            let empty_obj = SpecJsonValue::Object(Seq::empty());
            let enc_obj = spec_json_stringify(empty_obj);
            &&& spec_parse_value(enc_obj + trailing, 0, fuel) == Some((empty_obj, enc_obj.len()))
            &&& spec_json_parse(enc_obj, fuel) == Some(empty_obj)
        }),
{
    let empty_arr = SpecJsonValue::Array(Seq::empty());
    let enc_arr = spec_json_stringify(empty_arr);
    assert(enc_arr =~= seq![0x005Bu16, 0x005Du16]);
    let ext_arr = enc_arr + trailing;
    assert(spec_skip_ws(ext_arr, 0) == 0);
    assert(spec_skip_ws(ext_arr, 1) == 1);
    assert(spec_skip_ws(enc_arr, 0) == 0);
    assert(spec_skip_ws(enc_arr, 1) == 1);
    assert(spec_skip_ws(enc_arr, 2) == 2);

    let empty_obj = SpecJsonValue::Object(Seq::empty());
    let enc_obj = spec_json_stringify(empty_obj);
    assert(enc_obj =~= seq![0x007Bu16, 0x007Du16]);
    let ext_obj = enc_obj + trailing;
    assert(spec_skip_ws(ext_obj, 0) == 0);
    assert(spec_skip_ws(ext_obj, 1) == 1);
    assert(spec_skip_ws(enc_obj, 0) == 0);
    assert(spec_skip_ws(enc_obj, 1) == 1);
    assert(spec_skip_ws(enc_obj, 2) == 2);
}

// =======================================================================================
// 5. Exec Implementations (`json_stringify`, `quote_json_string`, `json_parse`)
// =======================================================================================

fn lower_hex_exec(n: u16) -> (c: u16)
    requires
        n < 16,
    ensures
        c == spec_lower_hex_char(n as nat),
{
    let r = if n < 10 {
        0x0030 + n
    } else {
        0x0061 + n - 10
    };
    proof {
        reveal(spec_lower_hex_char);
    }
    r
}

fn push_unicode_escape_exec(out: &mut Vec<u16>, c: u16)
    ensures
        final(out)@ == old(out)@ + spec_unicode_escape(c),
{
    out.push(0x005C);
    out.push(0x0075);
    out.push(lower_hex_exec(c / 4096));
    out.push(lower_hex_exec((c / 256) % 16));
    out.push(lower_hex_exec((c / 16) % 16));
    out.push(lower_hex_exec(c % 16));
    proof {
        assert(out@ =~= old(out)@ + spec_unicode_escape(c));
    }
}

/// Exec ES2019 well-formed `QuoteJSONString` (§25.5.2.2) proved equal to `spec_quote_string`.
pub fn quote_json_string(s: &[u16]) -> (out: Vec<u16>)
    ensures
        out@ == spec_quote_string(s@),
        spec_is_well_formed_utf16(out@),
        spec_parse_string(out@, 0) == Some((s@, out@.len())),
{
    proof {
        lemma_quote_string_well_formed_utf16(s@);
        lemma_quote_parse_string_roundtrip(s@, Seq::empty());
    }
    let mut out: Vec<u16> = Vec::new();
    out.push(0x0022);
    push_encoded_string_body(&mut out, s);
    let ghost before_close = out@;
    out.push(0x0022);
    proof {
        assert(before_close == seq![0x0022u16] + spec_encode_string_body(s@));
        assert(out@ =~= spec_quote_string(s@));
    }
    out
}

#[verifier::spinoff_prover]
#[verifier::rlimit(50)]
fn push_encoded_string_body(out: &mut Vec<u16>, s: &[u16])
    ensures
        final(out)@ == old(out)@ + spec_encode_string_body(s@),
{
    let n = s.len();
    let mut i: usize = 0;
    let ghost init_out = out@;
    proof {
        assert(s@.subrange(0, n as int) =~= s@);
    }
    while i < n
        invariant
            i <= n,
            n == s@.len(),
            init_out + spec_encode_string_body(s@)
                == out@ + spec_encode_string_body(s@.subrange(i as int, n as int)),
        decreases n - i,
    {
        let c = s[i];
        let ghost sub = s@.subrange(i as int, n as int);
        let ghost prev_out = out@;
        if c >= 0xD800 && c <= 0xDBFF && n - i >= 2 && s[i + 1] >= 0xDC00 && s[i + 1] <= 0xDFFF {
            let lo = s[i + 1];
            out.push(c);
            out.push(lo);
            i += 2;
            proof {
                assert(sub.subrange(2, sub.len() as int) =~= s@.subrange(i as int, n as int));
                assert(out@ =~= prev_out + seq![c, lo]);
                assert(prev_out + (seq![c, lo] + spec_encode_string_body(s@.subrange(i as int, n as int)))
                    =~= out@ + spec_encode_string_body(s@.subrange(i as int, n as int)));
            }
        } else {
            let ghost piece: Seq<u16>;
            if c == 0x0008 {
                out.push(0x005C);
                out.push(0x0062);
                proof { piece = seq![0x005Cu16, 0x0062u16]; }
            } else if c == 0x0009 {
                out.push(0x005C);
                out.push(0x0074);
                proof { piece = seq![0x005Cu16, 0x0074u16]; }
            } else if c == 0x000A {
                out.push(0x005C);
                out.push(0x006E);
                proof { piece = seq![0x005Cu16, 0x006Eu16]; }
            } else if c == 0x000C {
                out.push(0x005C);
                out.push(0x0066);
                proof { piece = seq![0x005Cu16, 0x0066u16]; }
            } else if c == 0x000D {
                out.push(0x005C);
                out.push(0x0072);
                proof { piece = seq![0x005Cu16, 0x0072u16]; }
            } else if c == 0x0022 {
                out.push(0x005C);
                out.push(0x0022);
                proof { piece = seq![0x005Cu16, 0x0022u16]; }
            } else if c == 0x005C {
                out.push(0x005C);
                out.push(0x005C);
                proof { piece = seq![0x005Cu16, 0x005Cu16]; }
            } else if c < 0x0020 || (c >= 0xD800 && c <= 0xDFFF) {
                push_unicode_escape_exec(out, c);
                proof { piece = spec_unicode_escape(c); }
            } else {
                out.push(c);
                proof { piece = seq![c]; }
            }
            i += 1;
            proof {
                assert(sub.subrange(1, sub.len() as int) =~= s@.subrange(i as int, n as int));
                assert(out@ =~= prev_out + piece);
                assert(prev_out + (piece + spec_encode_string_body(s@.subrange(i as int, n as int)))
                    =~= out@ + spec_encode_string_body(s@.subrange(i as int, n as int)));
            }
        }
    }
    proof {
        assert(s@.subrange(n as int, n as int) =~= Seq::<u16>::empty());
        assert(out@ + Seq::<u16>::empty() =~= out@);
    }
}

fn push_uint_digits_exec(out: &mut Vec<u16>, n: u64)
    requires
        n > 0,
    ensures
        final(out)@ == old(out)@ + spec_uint_digits(n as nat),
    decreases n,
{
    let q = n / 10;
    let r = (n % 10) as u16;
    let ghost init_out = out@;
    if q > 0 {
        push_uint_digits_exec(out, q);
    } else {
        proof {
            assert(spec_uint_digits(0) =~= Seq::<u16>::empty());
            assert(out@ =~= init_out + spec_uint_digits(0));
        }
    }
    out.push(0x0030 + r);
    proof {
        assert(out@ =~= init_out + spec_uint_digits(n as nat));
    }
}

fn push_int_exec(out: &mut Vec<u16>, v: i64)
    ensures
        final(out)@ == old(out)@ + spec_stringify_int(v),
{
    let ghost init_out = out@;
    if v == 0 {
        out.push(0x0030);
        proof {
            assert(out@ =~= init_out + spec_stringify_int(v));
        }
    } else if v < 0 {
        out.push(0x002D);
        let mag: u64 = if v == i64::MIN {
            9_223_372_036_854_775_808u64
        } else {
            (-v) as u64
        };
        push_uint_digits_exec(out, mag);
        proof {
            assert((init_out + seq![0x002Du16]) + spec_uint_digits(mag as nat)
                =~= init_out + (seq![0x002Du16] + spec_uint_digits(mag as nat)));
            assert(out@ =~= init_out + spec_stringify_int(v));
        }
    } else {
        push_uint_digits_exec(out, v as u64);
    }
}

#[verifier::rlimit(50)]
fn push_json_stringify_exec(out: &mut Vec<u16>, v: &JsonValue)
    ensures
        final(out)@ == old(out)@ + spec_json_stringify(v@),
    decreases spec_json_size(v@),
{
    let ghost init_out = out@;
    match v {
        JsonValue::Null => {
            out.push(0x006E);
            out.push(0x0075);
            out.push(0x006C);
            out.push(0x006C);
            proof {
                assert(out@ =~= init_out + spec_json_stringify(v@));
            }
        },
        JsonValue::Bool(b) => {
            if *b {
                out.push(0x0074);
                out.push(0x0072);
                out.push(0x0075);
                out.push(0x0065);
            } else {
                out.push(0x0066);
                out.push(0x0061);
                out.push(0x006C);
                out.push(0x0073);
                out.push(0x0065);
            }
            proof {
                assert(out@ =~= init_out + spec_json_stringify(v@));
            }
        },
        JsonValue::Int(n) => {
            push_int_exec(out, *n);
        },
        JsonValue::Str(s) => {
            out.push(0x0022);
            push_encoded_string_body(out, s.as_slice());
            out.push(0x0022);
            proof {
                assert(out@ =~= init_out + spec_quote_string(s@));
            }
        },
        JsonValue::Array(xs) => {
            let ghost sv: Seq<SpecJsonValue> = match v@ {
                SpecJsonValue::Array(a) => a,
                _ => Seq::empty(),
            };
            out.push(0x005B);
            let ghost after_open = out@;
            let len = xs.len();
            let mut i: usize = 0;
            while i < len
                invariant
                    i <= len,
                    len == xs@.len(),
                    sv.len() == len,
                    v@ == SpecJsonValue::Array(sv),
                    forall|k: int| 0 <= k < len as int ==> #[trigger] sv[k] == spec_json_view(&xs@[k]),
                    after_open + spec_stringify_array_items(sv, 0)
                        == out@ + spec_stringify_array_items(sv, i as nat),
                decreases len - i,
            {
                let ghost before_elem = out@;
                proof {
                    assert(sv[i as int] == spec_json_view(&xs@[i as int]));
                    lemma_json_array_elem_smaller(sv, i as int);
                }
                push_json_stringify_exec(out, &xs[i]);
                if i + 1 < len {
                    out.push(0x002C);
                    i += 1;
                    proof {
                        let head = spec_json_stringify(sv[i as int - 1]);
                        assert(out@ =~= before_elem + head + seq![0x002Cu16]);
                        assert(before_elem + (head + seq![0x002Cu16] + spec_stringify_array_items(sv, i as nat))
                            =~= out@ + spec_stringify_array_items(sv, i as nat));
                    }
                } else {
                    i += 1;
                    proof {
                        assert(spec_stringify_array_items(sv, i as nat) =~= Seq::<u16>::empty());
                        assert(out@ + Seq::<u16>::empty() =~= out@);
                    }
                }
            }
            out.push(0x005D);
            proof {
                assert(spec_stringify_array_items(sv, len as nat) =~= Seq::<u16>::empty());
                assert(out@ =~= init_out + spec_json_stringify(v@));
            }
        },
        JsonValue::Object(kvs) => {
            let ghost sv: Seq<(Seq<u16>, SpecJsonValue)> = match v@ {
                SpecJsonValue::Object(o) => o,
                _ => Seq::empty(),
            };
            out.push(0x007B);
            let ghost after_open = out@;
            let len = kvs.len();
            let mut i: usize = 0;
            while i < len
                invariant
                    i <= len,
                    len == kvs@.len(),
                    sv.len() == len,
                    v@ == SpecJsonValue::Object(sv),
                    forall|k: int|
                        0 <= k < len as int ==> #[trigger] sv[k]
                            == (kvs@[k].0@, spec_json_view(&kvs@[k].1)),
                    after_open + spec_stringify_object_items(sv, 0)
                        == out@ + spec_stringify_object_items(sv, i as nat),
                decreases len - i,
            {
                let ghost before_entry = out@;
                proof {
                    assert(sv[i as int] == (kvs@[i as int].0@, spec_json_view(&kvs@[i as int].1)));
                    lemma_json_object_elem_smaller(sv, i as int);
                }
                out.push(0x0022);
                push_encoded_string_body(out, kvs[i].0.as_slice());
                out.push(0x0022);
                out.push(0x003A);
                push_json_stringify_exec(out, &kvs[i].1);
                if i + 1 < len {
                    out.push(0x002C);
                    i += 1;
                    proof {
                        let e = sv[i as int - 1];
                        let head = spec_quote_string(e.0) + seq![0x003Au16] + spec_json_stringify(e.1);
                        assert(out@ =~= before_entry + head + seq![0x002Cu16]);
                        assert(before_entry + (head + seq![0x002Cu16] + spec_stringify_object_items(sv, i as nat))
                            =~= out@ + spec_stringify_object_items(sv, i as nat));
                    }
                } else {
                    i += 1;
                    proof {
                        let e = sv[i as int - 1];
                        let head = spec_quote_string(e.0) + seq![0x003Au16] + spec_json_stringify(e.1);
                        assert(out@ =~= before_entry + head);
                        assert(spec_stringify_object_items(sv, i as nat) =~= Seq::<u16>::empty());
                        assert(out@ + Seq::<u16>::empty() =~= out@);
                    }
                }
            }
            out.push(0x007D);
            proof {
                assert(spec_stringify_object_items(sv, len as nat) =~= Seq::<u16>::empty());
                assert(out@ =~= init_out + spec_json_stringify(v@));
            }
        },
    }
}

/// Exec canonical ECMA-262 §25.5.2 `JSON.stringify` proved equal to `spec_json_stringify`.
pub fn json_stringify(v: &JsonValue) -> (out: Vec<u16>)
    ensures
        out@ == spec_json_stringify(v@),
{
    let mut out: Vec<u16> = Vec::new();
    push_json_stringify_exec(&mut out, v);
    proof {
        assert(Seq::<u16>::empty() + spec_json_stringify(v@) =~= spec_json_stringify(v@));
    }
    out
}

// ---------------------------------------------------------------------------------------
// Exec Parser (`parse_json_string`, `parse_json_prefix`, `json_parse`)
// ---------------------------------------------------------------------------------------

fn is_json_ws_exec(c: u16) -> (res: bool)
    ensures
        res == spec_is_json_ws(c),
{
    c == 0x0009 || c == 0x000A || c == 0x000D || c == 0x0020
}

fn skip_ws_exec(input: &[u16], pos: usize) -> (end_pos: usize)
    requires
        pos <= input@.len(),
    ensures
        end_pos as nat == spec_skip_ws(input@, pos as nat),
        pos <= end_pos <= input@.len(),
{
    let n = input.len();
    let mut i: usize = pos;
    while i < n && is_json_ws_exec(input[i])
        invariant
            pos <= i <= n,
            n == input@.len(),
            spec_skip_ws(input@, pos as nat) == spec_skip_ws(input@, i as nat),
        decreases n - i,
    {
        i += 1;
    }
    i
}

fn is_hex_digit_exec(c: u16) -> (res: bool)
    ensures
        res == spec_is_hex_digit(c),
{
    (c >= 0x0030 && c <= 0x0039) || (c >= 0x0041 && c <= 0x0046) || (c >= 0x0061 && c <= 0x0066)
}

fn hex_val_exec(c: u16) -> (v: u16)
    requires
        spec_is_hex_digit(c),
    ensures
        v as nat == spec_hex_val(c),
        v < 16,
{
    if c <= 0x0039 {
        c - 0x0030
    } else if c <= 0x0046 {
        c - 0x0041 + 10
    } else {
        c - 0x0061 + 10
    }
}

fn parse_hex4_exec(input: &[u16], pos: usize) -> (res: Option<u16>)
    requires
        pos <= input@.len(),
    ensures
        res == spec_parse_hex4(input@, pos as nat),
{
    if input.len() - pos >= 4
        && is_hex_digit_exec(input[pos])
        && is_hex_digit_exec(input[pos + 1])
        && is_hex_digit_exec(input[pos + 2])
        && is_hex_digit_exec(input[pos + 3])
    {
        let v = hex_val_exec(input[pos]) * 4096
            + hex_val_exec(input[pos + 1]) * 256
            + hex_val_exec(input[pos + 2]) * 16
            + hex_val_exec(input[pos + 3]);
        Some(v)
    } else {
        None
    }
}

/// Exec JSON string literal parser proved equal to `spec_parse_string`.
pub fn parse_json_string(input: &[u16], pos: usize) -> (res: Option<(Vec<u16>, usize)>)
    requires
        pos <= input@.len(),
    ensures
        match res {
            Some((s, end_pos)) => {
                &&& spec_parse_string(input@, pos as nat) == Some((s@, end_pos as nat))
                &&& pos < end_pos <= input@.len()
            },
            None => spec_parse_string(input@, pos as nat).is_none(),
        },
{
    let n = input.len();
    if pos >= n || input[pos] != 0x0022 {
        return None;
    }
    let mut out: Vec<u16> = Vec::new();
    let mut i: usize = pos + 1;
    while i < n
        invariant
            pos < n,
            input@[pos as int] == 0x0022u16,
            pos + 1 <= i <= n,
            n == input@.len(),
            match spec_parse_string_body(input@, i as nat) {
                Some((rest, end_pos)) => {
                    spec_parse_string_body(input@, (pos + 1) as nat) == Some((out@ + rest, end_pos))
                },
                None => spec_parse_string_body(input@, (pos + 1) as nat).is_none(),
            },
        decreases n - i,
    {
        let c = input[i];
        if c == 0x0022 {
            proof {
                assert(spec_parse_string_body(input@, i as nat)
                    == Some((Seq::<u16>::empty(), (i + 1) as nat)));
                assert(out@ + Seq::<u16>::empty() =~= out@);
            }
            return Some((out, i + 1));
        }
        if c < 0x0020 {
            return None;
        }
        let ghost prev_out = out@;
        if c == 0x005C {
            if n - i < 2 {
                return None;
            }
            let esc = input[i + 1];
            if esc == 0x0022 || esc == 0x005C || esc == 0x002F {
                out.push(esc);
                i += 2;
            } else if esc == 0x0062 {
                out.push(0x0008);
                i += 2;
            } else if esc == 0x0066 {
                out.push(0x000C);
                i += 2;
            } else if esc == 0x006E {
                out.push(0x000A);
                i += 2;
            } else if esc == 0x0072 {
                out.push(0x000D);
                i += 2;
            } else if esc == 0x0074 {
                out.push(0x0009);
                i += 2;
            } else if esc == 0x0075 {
                match parse_hex4_exec(input, i + 2) {
                    Some(u) => {
                        out.push(u);
                        i += 6;
                    },
                    None => return None,
                }
            } else {
                return None;
            }
            proof {
                if let Some((rest, _)) = spec_parse_string_body(input@, i as nat) {
                    let added = out@[out@.len() - 1];
                    assert(prev_out + (seq![added] + rest) =~= out@ + rest);
                }
            }
        } else {
            out.push(c);
            i += 1;
            proof {
                if let Some((rest, _)) = spec_parse_string_body(input@, i as nat) {
                    assert(prev_out + (seq![c] + rest) =~= out@ + rest);
                }
            }
        }
    }
    None
}

fn is_ascii_digit_exec(c: u16) -> (res: bool)
    ensures
        res == spec_is_ascii_digit(c),
{
    c >= 0x0030 && c <= 0x0039
}

fn is_number_cont_exec(c: u16) -> (res: bool)
    ensures
        res == spec_is_number_cont_char(c),
{
    is_ascii_digit_exec(c) || c == 0x002E || c == 0x0065 || c == 0x0045
}

fn parse_int_exec(input: &[u16], pos: usize) -> (res: Option<(i64, usize)>)
    requires
        pos <= input@.len(),
    ensures
        match res {
            Some((v, end_pos)) => {
                &&& spec_parse_int(input@, pos as nat) == Some((v, end_pos as nat))
                &&& pos < end_pos <= input@.len()
            },
            None => spec_parse_int(input@, pos as nat).is_none(),
        },
{
    let n = input.len();
    if pos >= n {
        return None;
    }
    let neg = input[pos] == 0x002D;
    let p = if neg { pos + 1 } else { pos };
    if p >= n || !is_ascii_digit_exec(input[p]) {
        return None;
    }
    if input[p] == 0x0030 {
        let after = p + 1;
        if after < n && is_number_cont_exec(input[after]) {
            return None;
        }
        return Some((0, after));
    }
    let limit: u64 = if neg {
        9_223_372_036_854_775_808u64
    } else {
        9_223_372_036_854_775_807u64
    };
    let mut acc: u64 = (input[p] - 0x0030) as u64;
    let mut i: usize = p + 1;
    while i < n && is_ascii_digit_exec(input[i])
        invariant
            pos < n,
            neg == (input@[pos as int] == 0x002Du16),
            p as int == (if neg { pos as int + 1 } else { pos as int }),
            p < n,
            spec_is_ascii_digit(input@[p as int]),
            input@[p as int] != 0x0030u16,
            p + 1 <= i <= n,
            n == input@.len(),
            acc <= limit,
            limit == (if neg { 9_223_372_036_854_775_808u64 } else { 9_223_372_036_854_775_807u64 }),
            spec_parse_digits(input@, (p + 1) as nat, (input@[p as int] - 0x0030) as nat, limit as nat)
                == spec_parse_digits(input@, i as nat, acc as nat, limit as nat),
        decreases n - i,
    {
        let d: u64 = (input[i] - 0x0030) as u64;
        if acc > (limit - d) / 10 {
            proof {
                assert((acc as nat) * 10 + (d as nat) > limit as nat) by (nonlinear_arith)
                    requires
                        d < 10,
                        acc <= limit,
                        acc > (limit - d) / 10,
                ;
                assert(spec_parse_digits(input@, i as nat, acc as nat, limit as nat).is_none());
            }
            return None;
        }
        proof {
            assert((acc as nat) * 10 + (d as nat) <= limit as nat) by (nonlinear_arith)
                requires
                    d < 10,
                    acc <= (limit - d) / 10,
            ;
        }
        acc = acc * 10 + d;
        i += 1;
    }
    if i < n && is_number_cont_exec(input[i]) {
        return None;
    }
    let val: i64 = if neg {
        if acc == 9_223_372_036_854_775_808u64 {
            i64::MIN
        } else {
            -(acc as i64)
        }
    } else {
        acc as i64
    };
    Some((val, i))
}

/// Exec prefix parser proved equal to `spec_parse_value`.
pub fn parse_json_prefix(input: &[u16], pos: usize, fuel: usize) -> (res: Option<(JsonValue, usize)>)
    requires
        pos <= input@.len(),
    ensures
        match res {
            Some((v, end_pos)) => {
                &&& spec_parse_value(input@, pos as nat, fuel as nat) == Some((v@, end_pos as nat))
                &&& pos < end_pos <= input@.len()
            },
            None => spec_parse_value(input@, pos as nat, fuel as nat).is_none(),
        },
    decreases fuel, 0usize,
{
    if fuel == 0 {
        return None;
    }
    let n = input.len();
    let p = skip_ws_exec(input, pos);
    if p >= n {
        return None;
    }
    let c = input[p];
    if c == 0x006E {
        if n - p >= 4 && input[p + 1] == 0x0075 && input[p + 2] == 0x006C && input[p + 3] == 0x006C {
            Some((JsonValue::Null, p + 4))
        } else {
            None
        }
    } else if c == 0x0074 {
        if n - p >= 4 && input[p + 1] == 0x0072 && input[p + 2] == 0x0075 && input[p + 3] == 0x0065 {
            Some((JsonValue::Bool(true), p + 4))
        } else {
            None
        }
    } else if c == 0x0066 {
        if n - p >= 5
            && input[p + 1] == 0x0061
            && input[p + 2] == 0x006C
            && input[p + 3] == 0x0073
            && input[p + 4] == 0x0065
        {
            Some((JsonValue::Bool(false), p + 5))
        } else {
            None
        }
    } else if c == 0x0022 {
        match parse_json_string(input, p) {
            Some((s, end_pos)) => Some((JsonValue::Str(s), end_pos)),
            None => None,
        }
    } else if c == 0x005B {
        let p_in = skip_ws_exec(input, p + 1);
        if p_in < n && input[p_in] == 0x005D {
            let empty: Vec<JsonValue> = Vec::new();
            let arr = JsonValue::Array(empty);
            proof {
                if let SpecJsonValue::Array(sv) = arr@ {
                    assert(sv =~= Seq::<SpecJsonValue>::empty());
                }
            }
            Some((arr, p_in + 1))
        } else {
            parse_array_items_exec(input, p + 1, fuel - 1)
        }
    } else if c == 0x007B {
        let p_in = skip_ws_exec(input, p + 1);
        if p_in < n && input[p_in] == 0x007D {
            let empty: Vec<(Vec<u16>, JsonValue)> = Vec::new();
            let obj = JsonValue::Object(empty);
            proof {
                if let SpecJsonValue::Object(sv) = obj@ {
                    assert(sv =~= Seq::<(Seq<u16>, SpecJsonValue)>::empty());
                }
            }
            Some((obj, p_in + 1))
        } else {
            parse_object_items_exec(input, p + 1, fuel - 1)
        }
    } else if c == 0x002D || is_ascii_digit_exec(c) {
        match parse_int_exec(input, p) {
            Some((v, end_pos)) => Some((JsonValue::Int(v), end_pos)),
            None => None,
        }
    } else {
        None
    }
}

fn parse_array_items_exec(
    input: &[u16],
    pos: usize,
    fuel: usize,
) -> (res: Option<(JsonValue, usize)>)
    requires
        pos <= input@.len(),
    ensures
        match res {
            Some((v, end_pos)) => {
                &&& spec_parse_array_items(input@, pos as nat, fuel as nat)
                    == Some((v@, end_pos as nat))
                &&& pos < end_pos <= input@.len()
            },
            None => spec_parse_array_items(input@, pos as nat, fuel as nat).is_none(),
        },
    decreases fuel, input@.len() - pos + 1,
{
    if fuel == 0 || pos >= input.len() {
        return None;
    }
    match parse_json_prefix(input, pos, fuel) {
        None => None,
        Some((elem, p_after)) => {
            let p_sep = skip_ws_exec(input, p_after);
            if p_sep >= input.len() {
                None
            } else if input[p_sep] == 0x005D {
                let ghost elem_v = elem@;
                let mut v: Vec<JsonValue> = Vec::new();
                v.push(elem);
                let arr = JsonValue::Array(v);
                proof {
                    if let SpecJsonValue::Array(sv) = arr@ {
                        assert(sv =~= seq![elem_v]);
                    }
                }
                Some((arr, p_sep + 1))
            } else if input[p_sep] == 0x002C {
                match parse_array_items_exec(input, p_sep + 1, fuel) {
                    Some((rest_val, end_pos)) => {
                        let ghost rest_val_v = rest_val@;
                        match rest_val {
                            JsonValue::Array(rest_vec) => {
                                let ghost elem_v = elem@;
                                let ghost rest_sv: Seq<SpecJsonValue> = match rest_val_v {
                                    SpecJsonValue::Array(a) => a,
                                    _ => Seq::empty(),
                                };
                                let mut combined: Vec<JsonValue> = Vec::new();
                                combined.push(elem);
                                let mut rest_mut = rest_vec;
                                let ghost rlen = rest_mut@.len();
                                let mut rev: Vec<JsonValue> = Vec::new();
                                while rest_mut.len() > 0
                                    invariant
                                        rest_mut@.len() + rev@.len() == rlen,
                                        rlen == rest_sv.len(),
                                        forall|k: int|
                                            0 <= k < rest_mut@.len()
                                                ==> spec_json_view(&rest_mut@[k]) == rest_sv[k],
                                        forall|k: int|
                                            0 <= k < rev@.len()
                                                ==> spec_json_view(&rev@[k])
                                                    == rest_sv[rlen as int - 1 - k],
                                    decreases rest_mut@.len(),
                                {
                                    let popped = rest_mut.pop().unwrap();
                                    rev.push(popped);
                                }
                                while rev.len() > 0
                                    invariant
                                        combined@.len() == 1 + (rlen - rev@.len()),
                                        rev@.len() <= rlen,
                                        rlen == rest_sv.len(),
                                        spec_json_view(&combined@[0]) == elem_v,
                                        forall|k: int|
                                            0 <= k < (rlen - rev@.len()) as int
                                                ==> spec_json_view(&combined@[1 + k]) == rest_sv[k],
                                        forall|k: int|
                                            0 <= k < rev@.len()
                                                ==> spec_json_view(&rev@[k])
                                                    == rest_sv[rlen as int - 1 - k],
                                    decreases rev@.len(),
                                {
                                    let popped = rev.pop().unwrap();
                                    combined.push(popped);
                                }
                                let arr = JsonValue::Array(combined);
                                proof {
                                    if let SpecJsonValue::Array(sv) = arr@ {
                                        assert(sv =~= seq![elem_v] + rest_sv);
                                    }
                                }
                                Some((arr, end_pos))
                            },
                            _ => {
                                proof {
                                    lemma_parse_array_returns_array(
                                        input@,
                                        (p_sep + 1) as nat,
                                        fuel as nat,
                                    );
                                }
                                None
                            },
                        }
                    },
                    None => None,
                }
            } else {
                None
            }
        },
    }
}

proof fn lemma_parse_array_returns_array(input: Seq<u16>, pos: nat, fuel: nat)
    requires
        spec_parse_array_items(input, pos, fuel).is_some(),
    ensures
        matches!(spec_parse_array_items(input, pos, fuel).unwrap().0, SpecJsonValue::Array(_)),
{
}

proof fn lemma_parse_object_returns_object(input: Seq<u16>, pos: nat, fuel: nat)
    requires
        spec_parse_object_items(input, pos, fuel).is_some(),
    ensures
        matches!(spec_parse_object_items(input, pos, fuel).unwrap().0, SpecJsonValue::Object(_)),
{
}

fn parse_object_items_exec(
    input: &[u16],
    pos: usize,
    fuel: usize,
) -> (res: Option<(JsonValue, usize)>)
    requires
        pos <= input@.len(),
    ensures
        match res {
            Some((v, end_pos)) => {
                &&& spec_parse_object_items(input@, pos as nat, fuel as nat)
                    == Some((v@, end_pos as nat))
                &&& pos < end_pos <= input@.len()
            },
            None => spec_parse_object_items(input@, pos as nat, fuel as nat).is_none(),
        },
    decreases fuel, input@.len() - pos + 1,
{
    if fuel == 0 || pos >= input.len() {
        return None;
    }
    let p_key = skip_ws_exec(input, pos);
    match parse_json_string(input, p_key) {
        None => None,
        Some((key, p_after_key)) => {
            let p_colon = skip_ws_exec(input, p_after_key);
            if p_colon >= input.len() || input[p_colon] != 0x003A {
                return None;
            }
            match parse_json_prefix(input, p_colon + 1, fuel) {
                None => None,
                Some((val, p_after_val)) => {
                    let p_sep = skip_ws_exec(input, p_after_val);
                    if p_sep >= input.len() {
                        None
                    } else if input[p_sep] == 0x007D {
                        let ghost kv_spec = (key@, val@);
                        let mut kvs: Vec<(Vec<u16>, JsonValue)> = Vec::new();
                        kvs.push((key, val));
                        let obj = JsonValue::Object(kvs);
                        proof {
                            if let SpecJsonValue::Object(sv) = obj@ {
                                assert(sv =~= seq![kv_spec]);
                            }
                        }
                        Some((obj, p_sep + 1))
                    } else if input[p_sep] == 0x002C {
                        match parse_object_items_exec(input, p_sep + 1, fuel) {
                            Some((rest_val, end_pos)) => {
                                let ghost rest_val_v = rest_val@;
                                match rest_val {
                                    JsonValue::Object(rest_vec) => {
                                        let ghost kv_spec = (key@, val@);
                                        let ghost rest_sv: Seq<(Seq<u16>, SpecJsonValue)> = match rest_val_v {
                                            SpecJsonValue::Object(o) => o,
                                            _ => Seq::empty(),
                                        };
                                        let mut combined: Vec<(Vec<u16>, JsonValue)> = Vec::new();
                                        combined.push((key, val));
                                        let mut rest_mut = rest_vec;
                                        let ghost rlen = rest_mut@.len();
                                        let mut rev: Vec<(Vec<u16>, JsonValue)> = Vec::new();
                                        while rest_mut.len() > 0
                                            invariant
                                                rest_mut@.len() + rev@.len() == rlen,
                                                rlen == rest_sv.len(),
                                                forall|k: int|
                                                    0 <= k < rest_mut@.len()
                                                        ==> (rest_mut@[k].0@, spec_json_view(&rest_mut@[k].1))
                                                            == rest_sv[k],
                                                forall|k: int|
                                                    0 <= k < rev@.len()
                                                        ==> (rev@[k].0@, spec_json_view(&rev@[k].1))
                                                            == rest_sv[rlen as int - 1 - k],
                                            decreases rest_mut@.len(),
                                        {
                                            let popped = rest_mut.pop().unwrap();
                                            rev.push(popped);
                                        }
                                        while rev.len() > 0
                                            invariant
                                                combined@.len() == 1 + (rlen - rev@.len()),
                                                rev@.len() <= rlen,
                                                rlen == rest_sv.len(),
                                                (combined@[0].0@, spec_json_view(&combined@[0].1)) == kv_spec,
                                                forall|k: int|
                                                    0 <= k < (rlen - rev@.len()) as int
                                                        ==> (combined@[1 + k].0@, spec_json_view(&combined@[1 + k].1))
                                                            == rest_sv[k],
                                                forall|k: int|
                                                    0 <= k < rev@.len()
                                                        ==> (rev@[k].0@, spec_json_view(&rev@[k].1))
                                                            == rest_sv[rlen as int - 1 - k],
                                            decreases rev@.len(),
                                        {
                                            let popped = rev.pop().unwrap();
                                            combined.push(popped);
                                        }
                                        let obj = JsonValue::Object(combined);
                                        proof {
                                            if let SpecJsonValue::Object(sv) = obj@ {
                                                assert(sv =~= seq![kv_spec] + rest_sv);
                                            }
                                        }
                                        Some((obj, end_pos))
                                    },
                                    _ => {
                                        proof {
                                            lemma_parse_object_returns_object(
                                                input@,
                                                (p_sep + 1) as nat,
                                                fuel as nat,
                                            );
                                        }
                                        None
                                    },
                                }
                            },
                            None => None,
                        }
                    } else {
                        None
                    }
                },
            }
        },
    }
}

/// Exec ECMA-262 §25.5.1 `JSON.parse` proved equal to `spec_json_parse`.
pub fn json_parse(input: &[u16], fuel: usize) -> (res: Option<JsonValue>)
    ensures
        match res {
            Some(v) => spec_json_parse(input@, fuel as nat) == Some(v@),
            None => spec_json_parse(input@, fuel as nat).is_none(),
        },
{
    match parse_json_prefix(input, 0, fuel) {
        None => None,
        Some((v, end_pos)) => {
            let trailing_end = skip_ws_exec(input, end_pos);
            if trailing_end == input.len() {
                Some(v)
            } else {
                None
            }
        },
    }
}

} // verus!
