//! ECMA-262 §11–12 Verified Lexer.
//!
//! Operates over arbitrary `&[u8]` byte streams (with full UTF-8 whitespace/line-terminator/scalar
//! decoding) as well as `&[u16]` UTF-16 code-unit slices (`tokenize_utf16`). Every helper and loop
//! is specified as a total Verus `spec fn` over `nat` cursors with `decreases`, and every executable
//! function is machine-checked to refine its spec (`exec == spec`) with zero panics on all inputs.
use crate::token::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------------------
// Outcomes & Views
// ---------------------------------------------------------------------------------------

/// Outcome of lexical analysis.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum LexOutcome {
    Ok(Vec<Token>),
    SyntaxError(SyntaxDiagnostic),
    Unsupported(UnsupportedSyntax),
}

/// Spec-level outcome of lexical analysis.
pub enum SpecLexOutcome {
    Ok(Seq<SpecToken>),
    SyntaxError(SyntaxDiagnostic),
    Unsupported(UnsupportedSyntax),
}

impl View for LexOutcome {
    type V = SpecLexOutcome;

    open spec fn view(&self) -> SpecLexOutcome {
        match self {
            LexOutcome::Ok(toks) => SpecLexOutcome::Ok(spec_tokens_view(toks@)),
            LexOutcome::SyntaxError(d) => SpecLexOutcome::SyntaxError(*d),
            LexOutcome::Unsupported(u) => SpecLexOutcome::Unsupported(*u),
        }
    }
}

/// Internal step result for lexing a single token starting at `pos` (`pos < input.len()`).
pub enum SpecStepOutcome {
    Token { tok: SpecToken, next_pos: nat },
    SyntaxError(SyntaxDiagnostic),
    Unsupported(UnsupportedSyntax),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum StepOutcome {
    Token { tok: Token, next_pos: usize },
    SyntaxError(SyntaxDiagnostic),
    Unsupported(UnsupportedSyntax),
}

impl View for StepOutcome {
    type V = SpecStepOutcome;

    open spec fn view(&self) -> SpecStepOutcome {
        match self {
            StepOutcome::Token { tok, next_pos } => SpecStepOutcome::Token {
                tok: tok@,
                next_pos: *next_pos as nat,
            },
            StepOutcome::SyntaxError(d) => SpecStepOutcome::SyntaxError(*d),
            StepOutcome::Unsupported(u) => SpecStepOutcome::Unsupported(*u),
        }
    }
}

// ---------------------------------------------------------------------------------------
// Character & UTF-8 / UTF-16 Predicates (Spec + Exec)
// ---------------------------------------------------------------------------------------

pub open spec fn spec_span(start: nat, end: nat) -> Span {
    Span {
        start: #[verifier::truncate] (start as usize),
        end: #[verifier::truncate] (end as usize),
    }
}

pub open spec fn spec_is_ascii_digit(b: u8) -> bool {
    0x30 <= b && b <= 0x39
}

pub fn is_ascii_digit(b: u8) -> (r: bool)
    ensures
        r == spec_is_ascii_digit(b),
{
    b >= 0x30 && b <= 0x39
}

pub open spec fn spec_is_hex_digit(b: u8) -> bool {
    (0x30 <= b && b <= 0x39) || (0x41 <= b && b <= 0x46) || (0x61 <= b && b <= 0x66)
}

pub fn is_hex_digit(b: u8) -> (r: bool)
    ensures
        r == spec_is_hex_digit(b),
{
    (b >= 0x30 && b <= 0x39) || (b >= 0x41 && b <= 0x46) || (b >= 0x61 && b <= 0x66)
}

pub open spec fn spec_hex_val(b: u8) -> u32 {
    if 0x30 <= b && b <= 0x39 {
        (b - 0x30) as u32
    } else if 0x41 <= b && b <= 0x46 {
        (b - 0x41 + 10) as u32
    } else {
        (b - 0x61 + 10) as u32
    }
}

pub fn hex_val(b: u8) -> (r: u32)
    requires
        spec_is_hex_digit(b),
    ensures
        r == spec_hex_val(b),
        r < 16,
{
    if b >= 0x30 && b <= 0x39 {
        (b - 0x30) as u32
    } else if b >= 0x41 && b <= 0x46 {
        (b - 0x41 + 10) as u32
    } else {
        (b - 0x61 + 10) as u32
    }
}

pub open spec fn spec_is_octal_digit(b: u8) -> bool {
    0x30 <= b && b <= 0x37
}

pub fn is_octal_digit(b: u8) -> (r: bool)
    ensures
        r == spec_is_octal_digit(b),
{
    b >= 0x30 && b <= 0x37
}

pub open spec fn spec_is_binary_digit(b: u8) -> bool {
    b == 0x30 || b == 0x31
}

pub fn is_binary_digit(b: u8) -> (r: bool)
    ensures
        r == spec_is_binary_digit(b),
{
    b == 0x30 || b == 0x31
}

pub open spec fn spec_is_radix_digit(b: u8, radix: u8) -> bool {
    if radix == 16 {
        spec_is_hex_digit(b)
    } else if radix == 8 {
        spec_is_octal_digit(b)
    } else if radix == 2 {
        spec_is_binary_digit(b)
    } else {
        spec_is_ascii_digit(b)
    }
}

pub fn is_radix_digit(b: u8, radix: u8) -> (r: bool)
    ensures
        r == spec_is_radix_digit(b, radix),
{
    if radix == 16 {
        is_hex_digit(b)
    } else if radix == 8 {
        is_octal_digit(b)
    } else if radix == 2 {
        is_binary_digit(b)
    } else {
        is_ascii_digit(b)
    }
}

pub open spec fn spec_is_ascii_ident_start(b: u8) -> bool {
    (0x41 <= b && b <= 0x5A) || (0x61 <= b && b <= 0x7A) || b == 0x24 || b == 0x5F
}

pub fn is_ascii_ident_start(b: u8) -> (r: bool)
    ensures
        r == spec_is_ascii_ident_start(b),
{
    (b >= 0x41 && b <= 0x5A) || (b >= 0x61 && b <= 0x7A) || b == 0x24 || b == 0x5F
}

pub open spec fn spec_is_ascii_ident_continue(b: u8) -> bool {
    spec_is_ascii_ident_start(b) || spec_is_ascii_digit(b)
}

pub fn is_ascii_ident_continue(b: u8) -> (r: bool)
    ensures
        r == spec_is_ascii_ident_continue(b),
{
    is_ascii_ident_start(b) || is_ascii_digit(b)
}

/// ECMA-262 §12.2 WhiteSpace byte length at `pos`:
/// TAB (0x09), VT (0x0B), FF (0x0C), SP (0x20), NBSP (U+00A0 = C2 A0), ZWNBSP/BOM (U+FEFF = EF BB BF),
/// and all Unicode `<USP>` (`Space_Separator`): U+1680 (E1 9A 80), U+2000..=U+200A (E2 80 80..=8A),
/// U+202F (E2 80 AF), U+205F (E2 81 9F), and U+3000 (E3 80 80).
pub open spec fn spec_utf8_whitespace_len(input: Seq<u8>, pos: nat) -> nat {
    if pos >= input.len() {
        0
    } else {
        let b0 = input[pos as int];
        if b0 == 0x09 || b0 == 0x0B || b0 == 0x0C || b0 == 0x20 {
            1
        } else if b0 == 0xC2 && pos + 1 < input.len() && input[(pos + 1) as int] == 0xA0 {
            2
        } else if pos + 2 < input.len() {
            let b1 = input[(pos + 1) as int];
            let b2 = input[(pos + 2) as int];
            if (b0 == 0xE1 && b1 == 0x9A && b2 == 0x80)
                || (b0 == 0xE2 && b1 == 0x80 && ((0x80 <= b2 && b2 <= 0x8A) || b2 == 0xAF))
                || (b0 == 0xE2 && b1 == 0x81 && b2 == 0x9F)
                || (b0 == 0xE3 && b1 == 0x80 && b2 == 0x80)
                || (b0 == 0xEF && b1 == 0xBB && b2 == 0xBF)
            {
                3
            } else {
                0
            }
        } else {
            0
        }
    }
}

pub fn utf8_whitespace_len(input: &[u8], pos: usize) -> (r: usize)
    ensures
        r as nat == spec_utf8_whitespace_len(input@, pos as nat),
        r > 0 ==> pos + r <= input@.len(),
{
    let n = input.len();
    if pos >= n {
        0
    } else {
        let rem = n - pos;
        let b0 = input[pos];
        if b0 == 0x09 || b0 == 0x0B || b0 == 0x0C || b0 == 0x20 {
            1
        } else if b0 == 0xC2 && rem >= 2 && input[pos + 1] == 0xA0 {
            2
        } else if rem >= 3 {
            let b1 = input[pos + 1];
            let b2 = input[pos + 2];
            if (b0 == 0xE1 && b1 == 0x9A && b2 == 0x80)
                || (b0 == 0xE2 && b1 >= 0x80 && b1 == 0x80 && ((b2 >= 0x80 && b2 <= 0x8A) || b2 == 0xAF))
                || (b0 == 0xE2 && b1 == 0x81 && b2 == 0x9F)
                || (b0 == 0xE3 && b1 == 0x80 && b2 == 0x80)
                || (b0 == 0xEF && b1 == 0xBB && b2 == 0xBF)
            {
                3
            } else {
                0
            }
        } else {
            0
        }
    }
}

/// ECMA-262 §12.3 LineTerminatorSequence byte length at `pos`:
/// `<CR><LF>` (2), `<LF>` (1), `<CR>` (1), `<LS>` U+2028 = E2 80 A8 (3), `<PS>` U+2029 = E2 80 A9 (3).
pub open spec fn spec_utf8_line_terminator_len(input: Seq<u8>, pos: nat) -> nat {
    if pos >= input.len() {
        0
    } else {
        let b0 = input[pos as int];
        if b0 == 0x0A {
            1
        } else if b0 == 0x0D {
            if pos + 1 < input.len() && input[(pos + 1) as int] == 0x0A {
                2
            } else {
                1
            }
        } else if b0 == 0xE2
            && pos + 2 < input.len()
            && input[(pos + 1) as int] == 0x80
            && (input[(pos + 2) as int] == 0xA8 || input[(pos + 2) as int] == 0xA9)
        {
            3
        } else {
            0
        }
    }
}

pub fn utf8_line_terminator_len(input: &[u8], pos: usize) -> (r: usize)
    ensures
        r as nat == spec_utf8_line_terminator_len(input@, pos as nat),
        r > 0 ==> pos + r <= input@.len(),
{
    let n = input.len();
    if pos >= n {
        0
    } else {
        let rem = n - pos;
        let b0 = input[pos];
        if b0 == 0x0A {
            1
        } else if b0 == 0x0D {
            if rem >= 2 && input[pos + 1] == 0x0A {
                2
            } else {
                1
            }
        } else if b0 == 0xE2
            && rem >= 3
            && input[pos + 1] == 0x80
            && (input[pos + 2] == 0xA8 || input[pos + 2] == 0xA9)
        {
            3
        } else {
            0
        }
    }
}

/// Decode a valid non-overlong UTF-8 scalar value at `pos`.
pub open spec fn spec_decode_utf8_scalar(input: Seq<u8>, pos: nat) -> Option<(u32, usize)> {
    if pos >= input.len() {
        None
    } else {
        let b0 = input[pos as int];
        if b0 < 0x80 {
            Some((b0 as u32, 1usize))
        } else if 0xC2 <= b0 && b0 <= 0xDF {
            if pos + 1 < input.len() {
                let b1 = input[(pos + 1) as int];
                if 0x80 <= b1 && b1 <= 0xBF {
                    let cp = ((b0 - 0xC0) * 64 + (b1 - 0x80)) as u32;
                    Some((cp, 2usize))
                } else {
                    None
                }
            } else {
                None
            }
        } else if 0xE0 <= b0 && b0 <= 0xEF {
            if pos + 2 < input.len() {
                let b1 = input[(pos + 1) as int];
                let b2 = input[(pos + 2) as int];
                let valid_b1 = if b0 == 0xE0 {
                    0xA0 <= b1 && b1 <= 0xBF
                } else if b0 == 0xED {
                    0x80 <= b1 && b1 <= 0x9F
                } else {
                    0x80 <= b1 && b1 <= 0xBF
                };
                if valid_b1 && 0x80 <= b2 && b2 <= 0xBF {
                    let cp = ((b0 - 0xE0) * 4096 + (b1 - 0x80) * 64 + (b2 - 0x80)) as u32;
                    Some((cp, 3usize))
                } else {
                    None
                }
            } else {
                None
            }
        } else if 0xF0 <= b0 && b0 <= 0xF4 {
            if pos + 3 < input.len() {
                let b1 = input[(pos + 1) as int];
                let b2 = input[(pos + 2) as int];
                let b3 = input[(pos + 3) as int];
                let valid_b1 = if b0 == 0xF0 {
                    0x90 <= b1 && b1 <= 0xBF
                } else if b0 == 0xF4 {
                    0x80 <= b1 && b1 <= 0x8F
                } else {
                    0x80 <= b1 && b1 <= 0xBF
                };
                if valid_b1 && 0x80 <= b2 && b2 <= 0xBF && 0x80 <= b3 && b3 <= 0xBF {
                    let cp = ((b0 - 0xF0) * 262144
                        + (b1 - 0x80) * 4096
                        + (b2 - 0x80) * 64
                        + (b3 - 0x80)) as u32;
                    Some((cp, 4usize))
                } else {
                    None
                }
            } else {
                None
            }
        } else {
            None
        }
    }
}

pub fn decode_utf8_scalar(input: &[u8], pos: usize) -> (r: Option<(u32, usize)>)
    ensures
        r == spec_decode_utf8_scalar(input@, pos as nat),
        match r {
            Some((cp, len)) => 1 <= len && len <= 4 && pos + len <= input@.len() && cp <= 0x10FFFF && !(0xD800 <= cp && cp <= 0xDFFF),
            None => true,
        },
{
    let n = input.len();
    if pos >= n {
        None
    } else {
        let rem = n - pos;
        let b0 = input[pos];
        if b0 < 0x80 {
            Some((b0 as u32, 1))
        } else if b0 >= 0xC2 && b0 <= 0xDF {
            if rem >= 2 {
                let b1 = input[pos + 1];
                if b1 >= 0x80 && b1 <= 0xBF {
                    let cp = ((b0 - 0xC0) as u32) * 64 + ((b1 - 0x80) as u32);
                    Some((cp, 2))
                } else {
                    None
                }
            } else {
                None
            }
        } else if b0 >= 0xE0 && b0 <= 0xEF {
            if rem >= 3 {
                let b1 = input[pos + 1];
                let b2 = input[pos + 2];
                let valid_b1 = if b0 == 0xE0 {
                    b1 >= 0xA0 && b1 <= 0xBF
                } else if b0 == 0xED {
                    b1 >= 0x80 && b1 <= 0x9F
                } else {
                    b1 >= 0x80 && b1 <= 0xBF
                };
                if valid_b1 && b2 >= 0x80 && b2 <= 0xBF {
                    let cp = ((b0 - 0xE0) as u32) * 4096
                        + ((b1 - 0x80) as u32) * 64
                        + ((b2 - 0x80) as u32);
                    Some((cp, 3))
                } else {
                    None
                }
            } else {
                None
            }
        } else if b0 >= 0xF0 && b0 <= 0xF4 {
            if rem >= 4 {
                let b1 = input[pos + 1];
                let b2 = input[pos + 2];
                let b3 = input[pos + 3];
                let valid_b1 = if b0 == 0xF0 {
                    b1 >= 0x90 && b1 <= 0xBF
                } else if b0 == 0xF4 {
                    b1 >= 0x80 && b1 <= 0x8F
                } else {
                    b1 >= 0x80 && b1 <= 0xBF
                };
                if valid_b1 && b2 >= 0x80 && b2 <= 0xBF && b3 >= 0x80 && b3 <= 0xBF {
                    let cp = ((b0 - 0xF0) as u32) * 262144
                        + ((b1 - 0x80) as u32) * 4096
                        + ((b2 - 0x80) as u32) * 64
                        + ((b3 - 0x80) as u32);
                    Some((cp, 4))
                } else {
                    None
                }
            } else {
                None
            }
        } else {
            None
        }
    }
}

/// ECMA-262 §11.1.4 `UTF16EncodeCodePoint`: append 1 or 2 UTF-16 code units for `cp <= 0x10FFFF`.
pub open spec fn spec_append_utf16_cp(acc: Seq<u16>, cp: u32) -> Seq<u16> {
    if cp <= 0xFFFF {
        acc.push(cp as u16)
    } else {
        let u: int = cp - 0x10000;
        let high = (0xD800 + (u / 1024)) as u16;
        let low = (0xDC00 + (u % 1024)) as u16;
        acc.push(high).push(low)
    }
}

pub fn append_utf16_cp(out: &mut Vec<u16>, cp: u32)
    requires
        cp <= 0x10FFFF,
    ensures
        final(out)@ == spec_append_utf16_cp(old(out)@, cp),
{
    if cp <= 0xFFFF {
        out.push(cp as u16);
    } else {
        let u: u32 = cp - 0x10000;
        let high: u16 = (0xD800 + (u / 1024)) as u16;
        let low: u16 = (0xDC00 + (u % 1024)) as u16;
        out.push(high);
        out.push(low);
    }
}

/// Append canonical UTF-8 bytes for Unicode scalar `cp` (`cp <= 0x10FFFF`, non-surrogate).
pub open spec fn spec_append_utf8_cp(acc: Seq<u8>, cp: u32) -> Seq<u8> {
    let c: int = cp as int;
    if cp <= 0x7F {
        acc.push(cp as u8)
    } else if cp <= 0x7FF {
        let b0 = (0xC0 + (c / 64)) as u8;
        let b1 = (0x80 + (c % 64)) as u8;
        acc.push(b0).push(b1)
    } else if cp <= 0xFFFF {
        let b0 = (0xE0 + (c / 4096)) as u8;
        let b1 = (0x80 + ((c / 64) % 64)) as u8;
        let b2 = (0x80 + (c % 64)) as u8;
        acc.push(b0).push(b1).push(b2)
    } else {
        let b0 = (0xF0 + (c / 262144)) as u8;
        let b1 = (0x80 + ((c / 4096) % 64)) as u8;
        let b2 = (0x80 + ((c / 64) % 64)) as u8;
        let b3 = (0x80 + (c % 64)) as u8;
        acc.push(b0).push(b1).push(b2).push(b3)
    }
}

pub fn append_utf8_cp(out: &mut Vec<u8>, cp: u32)
    requires
        cp <= 0x10FFFF,
    ensures
        final(out)@ == spec_append_utf8_cp(old(out)@, cp),
{
    if cp <= 0x7F {
        out.push(cp as u8);
    } else if cp <= 0x7FF {
        let b0 = (0xC0 + (cp / 64)) as u8;
        let b1 = (0x80 + (cp % 64)) as u8;
        out.push(b0);
        out.push(b1);
    } else if cp <= 0xFFFF {
        let b0 = (0xE0 + (cp / 4096)) as u8;
        let b1 = (0x80 + ((cp / 64) % 64)) as u8;
        let b2 = (0x80 + (cp % 64)) as u8;
        out.push(b0);
        out.push(b1);
        out.push(b2);
    } else {
        let b0 = (0xF0 + (cp / 262144)) as u8;
        let b1 = (0x80 + ((cp / 4096) % 64)) as u8;
        let b2 = (0x80 + ((cp / 64) % 64)) as u8;
        let b3 = (0x80 + (cp % 64)) as u8;
        out.push(b0);
        out.push(b1);
        out.push(b2);
        out.push(b3);
    }
}

/// Identifier code-point validity (§12.7).
pub open spec fn spec_is_ident_start_cp(cp: u32) -> bool {
    if cp < 0x80 {
        spec_is_ascii_ident_start(cp as u8)
    } else if cp <= 0xBF {
        cp == 0xAA || cp == 0xB5 || cp == 0xBA
    } else if cp == 0xD7 || cp == 0xF7 || cp == 0x1680 || cp == 0x180E {
        false
    } else if 0x2000 <= cp && cp <= 0x2BFF {
        cp == 0x2071 || cp == 0x207F || (0x2090 <= cp && cp <= 0x209C) || (0x2102 <= cp && cp <= 0x218F)
    } else if cp == 0x3000 || (0xD800 <= cp && cp <= 0xDFFF) || cp == 0xFEFF || (0xFFFE <= cp && cp <= 0xFFFF) {
        false
    } else {
        cp <= 0x10FFFF
    }
}

pub fn is_ident_start_cp(cp: u32) -> (r: bool)
    ensures
        r == spec_is_ident_start_cp(cp),
{
    if cp < 0x80 {
        is_ascii_ident_start(cp as u8)
    } else if cp <= 0xBF {
        cp == 0xAA || cp == 0xB5 || cp == 0xBA
    } else if cp == 0xD7 || cp == 0xF7 || cp == 0x1680 || cp == 0x180E {
        false
    } else if cp >= 0x2000 && cp <= 0x2BFF {
        cp == 0x2071 || cp == 0x207F || (cp >= 0x2090 && cp <= 0x209C) || (cp >= 0x2102 && cp <= 0x218F)
    } else if cp == 0x3000 || (cp >= 0xD800 && cp <= 0xDFFF) || cp == 0xFEFF || (cp >= 0xFFFE && cp <= 0xFFFF) {
        false
    } else {
        cp <= 0x10FFFF
    }
}

pub open spec fn spec_is_ident_part_cp(cp: u32) -> bool {
    if cp < 0x80 {
        spec_is_ascii_ident_continue(cp as u8)
    } else if cp == 0x00B7
        || (0x0300 <= cp && cp <= 0x036F)
        || cp == 0x0387
        || (0x1369 <= cp && cp <= 0x1371)
        || cp == 0x19DA
        || cp == 0x200C
        || cp == 0x200D
        || cp == 0x203F
        || cp == 0x2040
        || cp == 0x2054
    {
        true
    } else {
        spec_is_ident_start_cp(cp)
    }
}

pub fn is_ident_part_cp(cp: u32) -> (r: bool)
    ensures
        r == spec_is_ident_part_cp(cp),
{
    if cp < 0x80 {
        is_ascii_ident_continue(cp as u8)
    } else if cp == 0x00B7
        || (cp >= 0x0300 && cp <= 0x036F)
        || cp == 0x0387
        || (cp >= 0x1369 && cp <= 0x1371)
        || cp == 0x19DA
        || cp == 0x200C
        || cp == 0x200D
        || cp == 0x203F
        || cp == 0x2040
        || cp == 0x2054
    {
        true
    } else {
        is_ident_start_cp(cp)
    }
}

// ---------------------------------------------------------------------------------------
// Trivia & Comments (§12.2, §12.3, §12.4, §12.5) — all spec cursors in `nat`
// ---------------------------------------------------------------------------------------

pub open spec fn spec_skip_line_comment(input: Seq<u8>, pos: nat) -> nat
    decreases input.len() - pos,
{
    if pos >= input.len() || spec_utf8_line_terminator_len(input, pos) > 0 {
        pos
    } else {
        spec_skip_line_comment(input, pos + 1)
    }
}

pub proof fn lemma_skip_line_comment_bounds(input: Seq<u8>, pos: nat)
    requires
        pos <= input.len(),
    ensures
        pos <= spec_skip_line_comment(input, pos),
        spec_skip_line_comment(input, pos) <= input.len(),
    decreases input.len() - pos,
{
    if pos < input.len() && spec_utf8_line_terminator_len(input, pos) == 0 {
        lemma_skip_line_comment_bounds(input, pos + 1);
    }
}

pub fn skip_line_comment(input: &[u8], pos0: usize) -> (r: usize)
    requires
        pos0 <= input@.len(),
    ensures
        r as nat == spec_skip_line_comment(input@, pos0 as nat),
        pos0 <= r && r <= input@.len(),
{
    let n = input.len();
    let mut pos = pos0;
    while pos < n && utf8_line_terminator_len(input, pos) == 0
        invariant
            pos0 <= pos && pos <= n,
            n == input@.len(),
            spec_skip_line_comment(input@, pos as nat) == spec_skip_line_comment(input@, pos0 as nat),
        decreases n - pos,
    {
        pos = pos + 1;
    }
    pos
}

/// Skip multi-line comment body after `/*` (`pos` is `comment_start + 2`).
/// Per ECMA-262 §12.4: if a `MultiLineComment` contains any `LineTerminator` code point,
/// the entire comment acts as a `LineTerminator` for Automatic Semicolon Insertion!
pub open spec fn spec_skip_block_comment(
    input: Seq<u8>,
    comment_start: nat,
    pos: nat,
    saw_lt: bool,
) -> Result<(nat, bool), SyntaxDiagnostic>
    decreases input.len() - pos,
{
    if pos >= input.len() {
        Err(SyntaxDiagnostic {
            kind: DiagnosticKind::UnterminatedComment,
            span: spec_span(comment_start, input.len()),
        })
    } else if pos + 1 < input.len() && input[pos as int] == 0x2A && input[(pos + 1) as int] == 0x2F {
        Ok((pos + 2, saw_lt))
    } else {
        let lt_len = spec_utf8_line_terminator_len(input, pos);
        if lt_len > 0 && pos + lt_len <= input.len() {
            spec_skip_block_comment(input, comment_start, pos + lt_len, true)
        } else {
            spec_skip_block_comment(input, comment_start, pos + 1, saw_lt)
        }
    }
}

pub proof fn lemma_skip_block_comment_bounds(
    input: Seq<u8>,
    comment_start: nat,
    pos: nat,
    saw_lt: bool,
)
    requires
        pos <= input.len(),
    ensures
        match spec_skip_block_comment(input, comment_start, pos, saw_lt) {
            Ok((next_pos, out_lt)) => pos < next_pos && next_pos <= input.len() && (saw_lt ==> out_lt),
            Err(_) => true,
        },
    decreases input.len() - pos,
{
    if pos < input.len() {
        if !(pos + 1 < input.len() && input[pos as int] == 0x2A && input[(pos + 1) as int] == 0x2F) {
            let lt_len = spec_utf8_line_terminator_len(input, pos);
            if lt_len > 0 && pos + lt_len <= input.len() {
                lemma_skip_block_comment_bounds(input, comment_start, pos + lt_len, true);
            } else {
                lemma_skip_block_comment_bounds(input, comment_start, pos + 1, saw_lt);
            }
        }
    }
}

pub fn skip_block_comment(
    input: &[u8],
    comment_start: usize,
    pos0: usize,
    saw_lt0: bool,
) -> (r: Result<(usize, bool), SyntaxDiagnostic>)
    requires
        pos0 <= input@.len(),
    ensures
        match r {
            Ok((next_pos, out_lt)) => {
                spec_skip_block_comment(input@, comment_start as nat, pos0 as nat, saw_lt0)
                    == Ok::<(nat, bool), SyntaxDiagnostic>((next_pos as nat, out_lt))
                    && pos0 < next_pos
                    && next_pos <= input@.len()
                    && (saw_lt0 ==> out_lt)
            },
            Err(e) => spec_skip_block_comment(input@, comment_start as nat, pos0 as nat, saw_lt0) == Err(e),
        },
{
    let n = input.len();
    let mut pos = pos0;
    let mut saw_lt = saw_lt0;
    while pos < n
        invariant
            pos0 <= pos && pos <= n,
            n == input@.len(),
            saw_lt0 ==> saw_lt,
            spec_skip_block_comment(input@, comment_start as nat, pos as nat, saw_lt)
                == spec_skip_block_comment(input@, comment_start as nat, pos0 as nat, saw_lt0),
        decreases n - pos,
    {
        if n - pos >= 2 && input[pos] == 0x2A && input[pos + 1] == 0x2F {
            return Ok((pos + 2, saw_lt));
        }
        let lt_len = utf8_line_terminator_len(input, pos);
        if lt_len > 0 {
            pos = pos + lt_len;
            saw_lt = true;
        } else {
            pos = pos + 1;
        }
    }
    Err(SyntaxDiagnostic {
        kind: DiagnosticKind::UnterminatedComment,
        span: Span { start: comment_start, end: n },
    })
}

pub open spec fn spec_skip_trivia(
    input: Seq<u8>,
    pos: nat,
    saw_lt: bool,
) -> Result<(nat, bool), SyntaxDiagnostic>
    decreases input.len() - pos,
{
    if pos >= input.len() {
        Ok((pos, saw_lt))
    } else {
        let ws_len = spec_utf8_whitespace_len(input, pos);
        if ws_len > 0 && pos + ws_len <= input.len() {
            spec_skip_trivia(input, pos + ws_len, saw_lt)
        } else {
            let lt_len = spec_utf8_line_terminator_len(input, pos);
            if lt_len > 0 && pos + lt_len <= input.len() {
                spec_skip_trivia(input, pos + lt_len, true)
            } else if pos + 1 < input.len() && input[pos as int] == 0x2F && input[(pos + 1) as int] == 0x2F {
                let after = spec_skip_line_comment(input, pos + 2);
                if after > pos && after <= input.len() {
                    spec_skip_trivia(input, after, saw_lt)
                } else {
                    Ok((pos, saw_lt))
                }
            } else if pos + 1 < input.len() && input[pos as int] == 0x2F && input[(pos + 1) as int] == 0x2A {
                match spec_skip_block_comment(input, pos, pos + 2, saw_lt) {
                    Ok((after, next_lt)) => {
                        if after > pos && after <= input.len() {
                            spec_skip_trivia(input, after, next_lt)
                        } else {
                            Ok((pos, next_lt))
                        }
                    },
                    Err(e) => Err(e),
                }
            } else {
                Ok((pos, saw_lt))
            }
        }
    }
}

pub proof fn lemma_skip_trivia_bounds(input: Seq<u8>, pos: nat, saw_lt: bool)
    requires
        pos <= input.len(),
    ensures
        match spec_skip_trivia(input, pos, saw_lt) {
            Ok((next_pos, out_lt)) => pos <= next_pos && next_pos <= input.len() && (saw_lt ==> out_lt),
            Err(_) => true,
        },
    decreases input.len() - pos,
{
    if pos < input.len() {
        let ws_len = spec_utf8_whitespace_len(input, pos);
        if ws_len > 0 && pos + ws_len <= input.len() {
            lemma_skip_trivia_bounds(input, pos + ws_len, saw_lt);
        } else {
            let lt_len = spec_utf8_line_terminator_len(input, pos);
            if lt_len > 0 && pos + lt_len <= input.len() {
                lemma_skip_trivia_bounds(input, pos + lt_len, true);
            } else if pos + 1 < input.len() && input[pos as int] == 0x2F && input[(pos + 1) as int] == 0x2F {
                lemma_skip_line_comment_bounds(input, pos + 2);
                let after = spec_skip_line_comment(input, pos + 2);
                lemma_skip_trivia_bounds(input, after, saw_lt);
            } else if pos + 1 < input.len() && input[pos as int] == 0x2F && input[(pos + 1) as int] == 0x2A {
                lemma_skip_block_comment_bounds(input, pos, pos + 2, saw_lt);
                if let Ok((after, next_lt)) = spec_skip_block_comment(input, pos, pos + 2, saw_lt) {
                    lemma_skip_trivia_bounds(input, after, next_lt);
                }
            }
        }
    }
}

pub fn skip_trivia(input: &[u8], pos0: usize, saw_lt0: bool) -> (r: Result<(usize, bool), SyntaxDiagnostic>)
    requires
        pos0 <= input@.len(),
    ensures
        match r {
            Ok((next_pos, out_lt)) => {
                spec_skip_trivia(input@, pos0 as nat, saw_lt0)
                    == Ok::<(nat, bool), SyntaxDiagnostic>((next_pos as nat, out_lt))
                    && pos0 <= next_pos
                    && next_pos <= input@.len()
                    && (saw_lt0 ==> out_lt)
            },
            Err(e) => spec_skip_trivia(input@, pos0 as nat, saw_lt0) == Err(e),
        },
{
    let n = input.len();
    let mut pos = pos0;
    let mut saw_lt = saw_lt0;
    while pos < n
        invariant
            pos0 <= pos && pos <= n,
            n == input@.len(),
            saw_lt0 ==> saw_lt,
            spec_skip_trivia(input@, pos as nat, saw_lt) == spec_skip_trivia(input@, pos0 as nat, saw_lt0),
        decreases n - pos,
    {
        let ws_len = utf8_whitespace_len(input, pos);
        if ws_len > 0 {
            pos = pos + ws_len;
        } else {
            let lt_len = utf8_line_terminator_len(input, pos);
            if lt_len > 0 {
                pos = pos + lt_len;
                saw_lt = true;
            } else if n - pos >= 2 && input[pos] == 0x2F && input[pos + 1] == 0x2F {
                let after = skip_line_comment(input, pos + 2);
                pos = after;
            } else if n - pos >= 2 && input[pos] == 0x2F && input[pos + 1] == 0x2A {
                match skip_block_comment(input, pos, pos + 2, saw_lt) {
                    Ok((after, next_lt)) => {
                        pos = after;
                        saw_lt = next_lt;
                    },
                    Err(e) => {
                        return Err(e);
                    },
                }
            } else {
                return Ok((pos, saw_lt));
            }
        }
    }
    Ok((pos, saw_lt))
}

// ---------------------------------------------------------------------------------------
// Unicode Escape Decoding (`\uHHHH` and `\u{H...}`)
// ---------------------------------------------------------------------------------------

pub open spec fn spec_parse_braced_hex(
    input: Seq<u8>,
    pos: nat,
    acc: u32,
    has_digit: bool,
) -> Result<(u32, nat), DiagnosticKind>
    decreases input.len() - pos,
{
    if pos >= input.len() {
        Err(DiagnosticKind::InvalidUnicodeEscape)
    } else {
        let b = input[pos as int];
        if b == 0x7D {
            if has_digit && acc <= 0x10FFFF {
                Ok((acc, pos + 1))
            } else {
                Err(DiagnosticKind::InvalidUnicodeEscape)
            }
        } else if spec_is_hex_digit(b) {
            let d = spec_hex_val(b);
            if acc <= (0x10FFFF - d) / 16 {
                spec_parse_braced_hex(input, pos + 1, (acc * 16 + d) as u32, true)
            } else {
                Err(DiagnosticKind::InvalidUnicodeEscape)
            }
        } else {
            Err(DiagnosticKind::InvalidUnicodeEscape)
        }
    }
}

pub proof fn lemma_parse_braced_hex_bounds(
    input: Seq<u8>,
    pos: nat,
    acc: u32,
    has_digit: bool,
)
    requires
        pos <= input.len(),
        acc <= 0x10FFFF,
    ensures
        match spec_parse_braced_hex(input, pos, acc, has_digit) {
            Ok((cp, next_pos)) => cp <= 0x10FFFF && pos < next_pos && next_pos <= input.len(),
            Err(_) => true,
        },
    decreases input.len() - pos,
{
    if pos < input.len() {
        let b = input[pos as int];
        if b != 0x7D && spec_is_hex_digit(b) {
            let d = spec_hex_val(b);
            if acc <= (0x10FFFF - d) / 16 {
                lemma_parse_braced_hex_bounds(input, pos + 1, (acc * 16 + d) as u32, true);
            }
        }
    }
}

pub fn parse_braced_hex(input: &[u8], pos0: usize) -> (r: Result<(u32, usize), DiagnosticKind>)
    requires
        pos0 <= input@.len(),
    ensures
        match r {
            Ok((cp, next_pos)) => {
                spec_parse_braced_hex(input@, pos0 as nat, 0, false)
                    == Ok::<(u32, nat), DiagnosticKind>((cp, next_pos as nat))
                    && cp <= 0x10FFFF
                    && pos0 < next_pos
                    && next_pos <= input@.len()
            },
            Err(k) => spec_parse_braced_hex(input@, pos0 as nat, 0, false) == Err(k),
        },
{
    let n = input.len();
    let mut pos = pos0;
    let mut acc: u32 = 0;
    let mut has_digit = false;
    while pos < n
        invariant
            pos0 <= pos && pos <= n,
            n == input@.len(),
            acc <= 0x10FFFF,
            has_digit ==> pos0 < pos,
            spec_parse_braced_hex(input@, pos as nat, acc, has_digit)
                == spec_parse_braced_hex(input@, pos0 as nat, 0, false),
        decreases n - pos,
    {
        let b = input[pos];
        if b == 0x7D {
            if has_digit {
                return Ok((acc, pos + 1));
            } else {
                return Err(DiagnosticKind::InvalidUnicodeEscape);
            }
        } else if is_hex_digit(b) {
            let d = hex_val(b);
            if acc <= (0x10FFFF - d) / 16 {
                acc = acc * 16 + d;
                has_digit = true;
                pos = pos + 1;
            } else {
                return Err(DiagnosticKind::InvalidUnicodeEscape);
            }
        } else {
            return Err(DiagnosticKind::InvalidUnicodeEscape);
        }
    }
    Err(DiagnosticKind::InvalidUnicodeEscape)
}

pub open spec fn spec_decode_unicode_escape_after_u(
    input: Seq<u8>,
    pos: nat,
) -> Result<(u32, nat), DiagnosticKind> {
    if pos < input.len() && input[pos as int] == 0x7B {
        spec_parse_braced_hex(input, pos + 1, 0, false)
    } else if pos + 4 <= input.len()
        && spec_is_hex_digit(input[pos as int])
        && spec_is_hex_digit(input[(pos + 1) as int])
        && spec_is_hex_digit(input[(pos + 2) as int])
        && spec_is_hex_digit(input[(pos + 3) as int])
    {
        let d0 = spec_hex_val(input[pos as int]);
        let d1 = spec_hex_val(input[(pos + 1) as int]);
        let d2 = spec_hex_val(input[(pos + 2) as int]);
        let d3 = spec_hex_val(input[(pos + 3) as int]);
        Ok(((d0 * 4096 + d1 * 256 + d2 * 16 + d3) as u32, pos + 4))
    } else {
        Err(DiagnosticKind::InvalidUnicodeEscape)
    }
}

pub fn decode_unicode_escape_after_u(
    input: &[u8],
    pos: usize,
) -> (r: Result<(u32, usize), DiagnosticKind>)
    requires
        pos <= input@.len(),
    ensures
        match r {
            Ok((cp, next_pos)) => {
                spec_decode_unicode_escape_after_u(input@, pos as nat)
                    == Ok::<(u32, nat), DiagnosticKind>((cp, next_pos as nat))
                    && cp <= 0x10FFFF
                    && pos < next_pos
                    && next_pos <= input@.len()
            },
            Err(k) => spec_decode_unicode_escape_after_u(input@, pos as nat) == Err(k),
        },
{
    let n = input.len();
    if pos < n && input[pos] == 0x7B {
        parse_braced_hex(input, pos + 1)
    } else if n - pos >= 4
        && is_hex_digit(input[pos])
        && is_hex_digit(input[pos + 1])
        && is_hex_digit(input[pos + 2])
        && is_hex_digit(input[pos + 3])
    {
        let d0 = hex_val(input[pos]);
        let d1 = hex_val(input[pos + 1]);
        let d2 = hex_val(input[pos + 2]);
        let d3 = hex_val(input[pos + 3]);
        Ok((d0 * 4096 + d1 * 256 + d2 * 16 + d3, pos + 4))
    } else {
        Err(DiagnosticKind::InvalidUnicodeEscape)
    }
}

// ---------------------------------------------------------------------------------------
// Identifier & Keyword Scanning (§12.7)
// ---------------------------------------------------------------------------------------

/// Single step of identifier continuation at `pos` (`pos < input.len()`):
/// returns `Ok(Some((cp_bytes_op, escaped, next_pos)))` to continue, `Ok(None)` when identifier ends,
/// or `Err(diag)` on malformed escape/UTF-8.
pub enum SpecIdentContStep {
    Ascii(u8, nat),
    CodePoint { cp: u32, escaped: bool, next_pos: nat },
    Done,
    Err(SyntaxDiagnostic),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum IdentContStep {
    Ascii(u8, usize),
    CodePoint { cp: u32, escaped: bool, next_pos: usize },
    Done,
    Err(SyntaxDiagnostic),
}

pub open spec fn spec_ident_cont_step(
    input: Seq<u8>,
    start_pos: nat,
    pos: nat,
) -> SpecIdentContStep {
    let b = input[pos as int];
    if spec_is_ascii_ident_continue(b) {
        SpecIdentContStep::Ascii(b, pos + 1)
    } else if b == 0x5C {
        if pos + 1 < input.len() && input[(pos + 1) as int] == 0x75 {
            match spec_decode_unicode_escape_after_u(input, pos + 2) {
                Ok((cp, next_pos)) => {
                    if spec_is_ident_part_cp(cp) {
                        SpecIdentContStep::CodePoint { cp, escaped: true, next_pos }
                    } else {
                        SpecIdentContStep::Err(SyntaxDiagnostic {
                            kind: DiagnosticKind::InvalidUnicodeEscape,
                            span: spec_span(start_pos, next_pos),
                        })
                    }
                },
                Err(kind) => SpecIdentContStep::Err(SyntaxDiagnostic {
                    kind,
                    span: spec_span(pos, input.len()),
                }),
            }
        } else {
            SpecIdentContStep::Err(SyntaxDiagnostic {
                kind: DiagnosticKind::InvalidUnicodeEscape,
                span: spec_span(pos, pos + 1),
            })
        }
    } else if b >= 0x80
        && spec_utf8_whitespace_len(input, pos) == 0
        && spec_utf8_line_terminator_len(input, pos) == 0
    {
        match spec_decode_utf8_scalar(input, pos) {
            Some((cp, ulen)) => {
                if spec_is_ident_part_cp(cp) {
                    SpecIdentContStep::CodePoint { cp, escaped: false, next_pos: pos + (ulen as nat) }
                } else {
                    SpecIdentContStep::Done
                }
            },
            None => SpecIdentContStep::Err(SyntaxDiagnostic {
                kind: DiagnosticKind::InvalidUtf8Encoding,
                span: spec_span(pos, pos + 1),
            }),
        }
    } else {
        SpecIdentContStep::Done
    }
}

pub proof fn lemma_ident_cont_step_bounds(input: Seq<u8>, start_pos: nat, pos: nat)
    requires
        pos < input.len(),
    ensures
        match spec_ident_cont_step(input, start_pos, pos) {
            SpecIdentContStep::Ascii(_, next_pos) => pos < next_pos && next_pos <= input.len(),
            SpecIdentContStep::CodePoint { cp, next_pos, .. } => {
                cp <= 0x10FFFF && pos < next_pos && next_pos <= input.len()
            },
            _ => true,
        },
{
    let b = input[pos as int];
    if !spec_is_ascii_ident_continue(b) && b == 0x5C {
        if pos + 1 < input.len() && input[(pos + 1) as int] == 0x75 {
            if pos + 2 < input.len() && input[(pos + 2) as int] == 0x7B {
                lemma_parse_braced_hex_bounds(input, pos + 3, 0, false);
            }
        }
    }
}

pub fn ident_cont_step(input: &[u8], start_pos: usize, pos: usize) -> (r: IdentContStep)
    requires
        start_pos <= input@.len(),
        pos < input@.len(),
    ensures
        match r {
            IdentContStep::Ascii(b, next_pos) => {
                spec_ident_cont_step(input@, start_pos as nat, pos as nat)
                    == SpecIdentContStep::Ascii(b, next_pos as nat)
                    && pos < next_pos
                    && next_pos <= input@.len()
            },
            IdentContStep::CodePoint { cp, escaped, next_pos } => {
                spec_ident_cont_step(input@, start_pos as nat, pos as nat)
                    == SpecIdentContStep::CodePoint { cp, escaped, next_pos: next_pos as nat }
                    && cp <= 0x10FFFF
                    && pos < next_pos
                    && next_pos <= input@.len()
            },
            IdentContStep::Done => {
                spec_ident_cont_step(input@, start_pos as nat, pos as nat) == SpecIdentContStep::Done
            },
            IdentContStep::Err(e) => {
                spec_ident_cont_step(input@, start_pos as nat, pos as nat) == SpecIdentContStep::Err(e)
            },
        },
{
    let n = input.len();
    let b = input[pos];
    if is_ascii_ident_continue(b) {
        IdentContStep::Ascii(b, pos + 1)
    } else if b == 0x5C {
        if n - pos >= 2 && input[pos + 1] == 0x75 {
            match decode_unicode_escape_after_u(input, pos + 2) {
                Ok((cp, next_pos)) => {
                    if is_ident_part_cp(cp) {
                        IdentContStep::CodePoint { cp, escaped: true, next_pos }
                    } else {
                        IdentContStep::Err(SyntaxDiagnostic {
                            kind: DiagnosticKind::InvalidUnicodeEscape,
                            span: Span { start: start_pos, end: next_pos },
                        })
                    }
                },
                Err(kind) => IdentContStep::Err(SyntaxDiagnostic {
                    kind,
                    span: Span { start: pos, end: n },
                }),
            }
        } else {
            IdentContStep::Err(SyntaxDiagnostic {
                kind: DiagnosticKind::InvalidUnicodeEscape,
                span: Span { start: pos, end: pos + 1 },
            })
        }
    } else if b >= 0x80
        && utf8_whitespace_len(input, pos) == 0
        && utf8_line_terminator_len(input, pos) == 0
    {
        match decode_utf8_scalar(input, pos) {
            Some((cp, ulen)) => {
                if is_ident_part_cp(cp) {
                    IdentContStep::CodePoint { cp, escaped: false, next_pos: pos + ulen }
                } else {
                    IdentContStep::Done
                }
            },
            None => IdentContStep::Err(SyntaxDiagnostic {
                kind: DiagnosticKind::InvalidUtf8Encoding,
                span: Span { start: pos, end: pos + 1 },
            }),
        }
    } else {
        IdentContStep::Done
    }
}

pub open spec fn spec_lex_ident_continue(
    input: Seq<u8>,
    start_pos: nat,
    pos: nat,
    acc: Seq<u8>,
    has_escape: bool,
) -> Result<(Seq<u8>, bool, nat), SyntaxDiagnostic>
    decreases input.len() - pos,
{
    if pos >= input.len() {
        Ok((acc, has_escape, pos))
    } else {
        match spec_ident_cont_step(input, start_pos, pos) {
            SpecIdentContStep::Ascii(b, next_pos) => {
                if next_pos > pos && next_pos <= input.len() {
                    spec_lex_ident_continue(input, start_pos, next_pos, acc.push(b), has_escape)
                } else {
                    Ok((acc, has_escape, pos))
                }
            },
            SpecIdentContStep::CodePoint { cp, escaped, next_pos } => {
                if next_pos > pos && next_pos <= input.len() {
                    spec_lex_ident_continue(
                        input,
                        start_pos,
                        next_pos,
                        spec_append_utf8_cp(acc, cp),
                        has_escape || escaped,
                    )
                } else {
                    Ok((acc, has_escape, pos))
                }
            },
            SpecIdentContStep::Done => Ok((acc, has_escape, pos)),
            SpecIdentContStep::Err(e) => Err(e),
        }
    }
}

pub proof fn lemma_lex_ident_continue_bounds(
    input: Seq<u8>,
    start_pos: nat,
    pos: nat,
    acc: Seq<u8>,
    has_escape: bool,
)
    requires
        pos <= input.len(),
    ensures
        match spec_lex_ident_continue(input, start_pos, pos, acc, has_escape) {
            Ok((_, _, next_pos)) => pos <= next_pos && next_pos <= input.len(),
            Err(_) => true,
        },
    decreases input.len() - pos,
{
    if pos < input.len() {
        lemma_ident_cont_step_bounds(input, start_pos, pos);
        match spec_ident_cont_step(input, start_pos, pos) {
            SpecIdentContStep::Ascii(b, next_pos) => {
                lemma_lex_ident_continue_bounds(input, start_pos, next_pos, acc.push(b), has_escape);
            },
            SpecIdentContStep::CodePoint { cp, escaped, next_pos } => {
                lemma_lex_ident_continue_bounds(
                    input,
                    start_pos,
                    next_pos,
                    spec_append_utf8_cp(acc, cp),
                    has_escape || escaped,
                );
            },
            _ => {},
        }
    }
}

pub fn lex_ident_continue(
    input: &[u8],
    start_pos: usize,
    pos0: usize,
    acc_in: Vec<u8>,
    has_escape_in: bool,
) -> (r: Result<(Vec<u8>, bool, usize), SyntaxDiagnostic>)
    requires
        start_pos <= input@.len(),
        pos0 <= input@.len(),
    ensures
        match r {
            Ok((name, esc, next_pos)) => {
                spec_lex_ident_continue(input@, start_pos as nat, pos0 as nat, acc_in@, has_escape_in)
                    == Ok::<(Seq<u8>, bool, nat), SyntaxDiagnostic>((name@, esc, next_pos as nat))
                    && pos0 <= next_pos
                    && next_pos <= input@.len()
            },
            Err(e) => {
                spec_lex_ident_continue(input@, start_pos as nat, pos0 as nat, acc_in@, has_escape_in)
                    == Err(e)
            },
        },
{
    let n = input.len();
    let mut acc = acc_in;
    let mut has_escape = has_escape_in;
    let mut pos = pos0;
    while pos < n
        invariant
            start_pos <= n,
            pos0 <= pos && pos <= n,
            n == input@.len(),
            spec_lex_ident_continue(input@, start_pos as nat, pos as nat, acc@, has_escape)
                == spec_lex_ident_continue(input@, start_pos as nat, pos0 as nat, acc_in@, has_escape_in),
        decreases n - pos,
    {
        match ident_cont_step(input, start_pos, pos) {
            IdentContStep::Ascii(b, next_pos) => {
                acc.push(b);
                pos = next_pos;
            },
            IdentContStep::CodePoint { cp, escaped, next_pos } => {
                append_utf8_cp(&mut acc, cp);
                has_escape = has_escape || escaped;
                pos = next_pos;
            },
            IdentContStep::Done => {
                return Ok((acc, has_escape, pos));
            },
            IdentContStep::Err(e) => {
                return Err(e);
            },
        }
    }
    Ok((acc, has_escape, pos))
}

pub open spec fn spec_finish_ident_token(
    name: Seq<u8>,
    has_escape: bool,
    span: Span,
    saw_lt: bool,
) -> SpecToken {
    let kind = if !has_escape {
        match spec_classify_ident(name) {
            Some(kw) => SpecTokenKind::Keyword(kw),
            None => SpecTokenKind::Ident { name, has_escape: false },
        }
    } else {
        SpecTokenKind::Ident { name, has_escape: true }
    };
    SpecToken { kind, span, preceded_by_line_terminator: saw_lt }
}

pub fn finish_ident_token(name: Vec<u8>, has_escape: bool, span: Span, saw_lt: bool) -> (t: Token)
    ensures
        t@ == spec_finish_ident_token(name@, has_escape, span, saw_lt),
{
    let kind = if !has_escape {
        match classify_ident(name.as_slice()) {
            Some(kw) => TokenKind::Keyword(kw),
            None => TokenKind::Ident { name, has_escape: false },
        }
    } else {
        TokenKind::Ident { name, has_escape: true }
    };
    Token { kind, span, preceded_by_line_terminator: saw_lt }
}

// ---------------------------------------------------------------------------------------
// Numeric Literal Scanning (§12.8.3)
// ---------------------------------------------------------------------------------------

pub open spec fn spec_scan_digits_loop(
    input: Seq<u8>,
    pos: nat,
    radix: u8,
    allow_sep: bool,
    has_any_digit: bool,
    prev_sep: bool,
    has_89: bool,
) -> Result<(nat, bool, bool), DiagnosticKind>
    decreases input.len() - pos,
{
    if pos >= input.len() {
        if prev_sep {
            Err(DiagnosticKind::InvalidNumericLiteral)
        } else {
            Ok((pos, has_any_digit, has_89))
        }
    } else {
        let b = input[pos as int];
        if spec_is_radix_digit(b, radix) {
            let next_89 = has_89 || b == 0x38 || b == 0x39;
            spec_scan_digits_loop(input, pos + 1, radix, allow_sep, true, false, next_89)
        } else if b == 0x5F {
            if !allow_sep || !has_any_digit || prev_sep {
                Err(DiagnosticKind::InvalidNumericLiteral)
            } else {
                spec_scan_digits_loop(input, pos + 1, radix, allow_sep, has_any_digit, true, has_89)
            }
        } else if prev_sep {
            Err(DiagnosticKind::InvalidNumericLiteral)
        } else {
            Ok((pos, has_any_digit, has_89))
        }
    }
}

pub proof fn lemma_scan_digits_bounds(
    input: Seq<u8>,
    pos: nat,
    radix: u8,
    allow_sep: bool,
    has_any_digit: bool,
    prev_sep: bool,
    has_89: bool,
)
    requires
        pos <= input.len(),
    ensures
        match spec_scan_digits_loop(input, pos, radix, allow_sep, has_any_digit, prev_sep, has_89) {
            Ok((end_pos, out_any, _)) => {
                pos <= end_pos
                    && end_pos <= input.len()
                    && (has_any_digit ==> out_any)
                    && ((!has_any_digit && out_any) ==> pos < end_pos)
            },
            Err(_) => true,
        },
    decreases input.len() - pos,
{
    if pos < input.len() {
        let b = input[pos as int];
        if spec_is_radix_digit(b, radix) {
            let next_89 = has_89 || b == 0x38 || b == 0x39;
            lemma_scan_digits_bounds(input, pos + 1, radix, allow_sep, true, false, next_89);
        } else if b == 0x5F && allow_sep && has_any_digit && !prev_sep {
            lemma_scan_digits_bounds(input, pos + 1, radix, allow_sep, has_any_digit, true, has_89);
        }
    }
}

pub fn scan_digits(
    input: &[u8],
    pos0: usize,
    radix: u8,
    allow_sep: bool,
) -> (r: Result<(usize, bool, bool), DiagnosticKind>)
    requires
        pos0 <= input@.len(),
    ensures
        match r {
            Ok((end_pos, has_any, has_89)) => {
                spec_scan_digits_loop(input@, pos0 as nat, radix, allow_sep, false, false, false)
                    == Ok::<(nat, bool, bool), DiagnosticKind>((end_pos as nat, has_any, has_89))
                    && pos0 <= end_pos
                    && end_pos <= input@.len()
                    && (has_any ==> pos0 < end_pos)
            },
            Err(k) => {
                spec_scan_digits_loop(input@, pos0 as nat, radix, allow_sep, false, false, false) == Err(k)
            },
        },
{
    let n = input.len();
    let mut pos = pos0;
    let mut has_any = false;
    let mut prev_sep = false;
    let mut has_89 = false;
    while pos < n
        invariant
            pos0 <= pos && pos <= n,
            n == input@.len(),
            has_any ==> pos0 < pos,
            spec_scan_digits_loop(input@, pos as nat, radix, allow_sep, has_any, prev_sep, has_89)
                == spec_scan_digits_loop(input@, pos0 as nat, radix, allow_sep, false, false, false),
        decreases n - pos,
    {
        let b = input[pos];
        if is_radix_digit(b, radix) {
            if b == 0x38 || b == 0x39 {
                has_89 = true;
            }
            has_any = true;
            prev_sep = false;
            pos = pos + 1;
        } else if b == 0x5F {
            if !allow_sep || !has_any || prev_sep {
                return Err(DiagnosticKind::InvalidNumericLiteral);
            }
            prev_sep = true;
            pos = pos + 1;
        } else if prev_sep {
            return Err(DiagnosticKind::InvalidNumericLiteral);
        } else {
            return Ok((pos, has_any, has_89));
        }
    }
    if prev_sep {
        Err(DiagnosticKind::InvalidNumericLiteral)
    } else {
        Ok((pos, has_any, has_89))
    }
}

pub open spec fn spec_invalid_after_numeric(input: Seq<u8>, pos: nat) -> bool {
    if pos >= input.len() {
        false
    } else {
        let b = input[pos as int];
        if spec_is_ascii_ident_continue(b) || b == 0x5C {
            true
        } else if b >= 0x80
            && spec_utf8_whitespace_len(input, pos) == 0
            && spec_utf8_line_terminator_len(input, pos) == 0
        {
            match spec_decode_utf8_scalar(input, pos) {
                Some((cp, _)) => spec_is_ident_start_cp(cp),
                None => false,
            }
        } else {
            false
        }
    }
}

pub fn invalid_after_numeric(input: &[u8], pos: usize) -> (r: bool)
    requires
        pos <= input@.len(),
    ensures
        r == spec_invalid_after_numeric(input@, pos as nat),
{
    let n = input.len();
    if pos >= n {
        false
    } else {
        let b = input[pos];
        if is_ascii_ident_continue(b) || b == 0x5C {
            true
        } else if b >= 0x80
            && utf8_whitespace_len(input, pos) == 0
            && utf8_line_terminator_len(input, pos) == 0
        {
            match decode_utf8_scalar(input, pos) {
                Some((cp, _)) => is_ident_start_cp(cp),
                None => false,
            }
        } else {
            false
        }
    }
}

pub open spec fn spec_slice_bytes(input: Seq<u8>, start: nat, end: nat) -> Seq<u8> {
    input.subrange(start as int, end as int)
}

pub fn slice_bytes(input: &[u8], start: usize, end: usize) -> (v: Vec<u8>)
    requires
        start <= end && end <= input@.len(),
    ensures
        v@ == spec_slice_bytes(input@, start as nat, end as nat),
{
    let mut out: Vec<u8> = Vec::new();
    let mut i = start;
    proof {
        assert(out@ =~= input@.subrange(start as int, start as int));
    }
    while i < end
        invariant
            start <= i && i <= end && end <= input@.len(),
            out@ == input@.subrange(start as int, i as int),
        decreases end - i,
    {
        out.push(input[i]);
        i = i + 1;
        proof {
            assert(out@ =~= input@.subrange(start as int, i as int));
        }
    }
    out
}

pub open spec fn spec_scan_optional_exponent(
    input: Seq<u8>,
    pos: nat,
) -> Result<(nat, bool), DiagnosticKind> {
    if pos < input.len() && (input[pos as int] == 0x65 || input[pos as int] == 0x45) {
        let after_e = pos + 1;
        let after_sign = if after_e < input.len()
            && (input[after_e as int] == 0x2B || input[after_e as int] == 0x2D)
        {
            after_e + 1
        } else {
            after_e
        };
        match spec_scan_digits_loop(input, after_sign, 10, true, false, false, false) {
            Ok((end_pos, has_any, _)) => {
                if !has_any {
                    Err(DiagnosticKind::InvalidNumericLiteral)
                } else {
                    Ok((end_pos, true))
                }
            },
            Err(k) => Err(k),
        }
    } else {
        Ok((pos, false))
    }
}

pub proof fn lemma_scan_optional_exponent_bounds(input: Seq<u8>, pos: nat)
    requires
        pos <= input.len(),
    ensures
        match spec_scan_optional_exponent(input, pos) {
            Ok((end_pos, _)) => pos <= end_pos && end_pos <= input.len(),
            Err(_) => true,
        },
{
    if pos < input.len() && (input[pos as int] == 0x65 || input[pos as int] == 0x45) {
        let after_e = pos + 1;
        let after_sign = if after_e < input.len()
            && (input[after_e as int] == 0x2B || input[after_e as int] == 0x2D)
        {
            after_e + 1
        } else {
            after_e
        };
        lemma_scan_digits_bounds(input, after_sign, 10, true, false, false, false);
    }
}

pub fn scan_optional_exponent(input: &[u8], pos: usize) -> (r: Result<(usize, bool), DiagnosticKind>)
    requires
        pos <= input@.len(),
    ensures
        match r {
            Ok((end_pos, has_exp)) => {
                spec_scan_optional_exponent(input@, pos as nat)
                    == Ok::<(nat, bool), DiagnosticKind>((end_pos as nat, has_exp))
                    && pos <= end_pos
                    && end_pos <= input@.len()
            },
            Err(k) => spec_scan_optional_exponent(input@, pos as nat) == Err(k),
        },
{
    let n = input.len();
    if pos < n && (input[pos] == 0x65 || input[pos] == 0x45) {
        let after_e = pos + 1;
        let after_sign = if after_e < n && (input[after_e] == 0x2B || input[after_e] == 0x2D) {
            after_e + 1
        } else {
            after_e
        };
        match scan_digits(input, after_sign, 10, true) {
            Ok((end_pos, has_any, _)) => {
                if !has_any {
                    Err(DiagnosticKind::InvalidNumericLiteral)
                } else {
                    Ok((end_pos, true))
                }
            },
            Err(k) => Err(k),
        }
    } else {
        Ok((pos, false))
    }
}

/// Finalize a numeric literal token from `[start, after_exp)` with optional `n` BigInt suffix.
pub open spec fn spec_finalize_number_token(
    input: Seq<u8>,
    start: nat,
    end_before_n: nat,
    allow_bigint: bool,
    has_legacy_octal_or_leading_zero: bool,
    saw_lt: bool,
) -> SpecStepOutcome {
    if end_before_n < input.len() && input[end_before_n as int] == 0x6E {
        if !allow_bigint {
            SpecStepOutcome::SyntaxError(SyntaxDiagnostic {
                kind: DiagnosticKind::InvalidNumericLiteral,
                span: spec_span(start, end_before_n + 1),
            })
        } else {
            let end_pos = end_before_n + 1;
            if spec_invalid_after_numeric(input, end_pos) {
                SpecStepOutcome::SyntaxError(SyntaxDiagnostic {
                    kind: DiagnosticKind::NumericFollowedByIdent,
                    span: spec_span(start, end_pos + 1),
                })
            } else {
                SpecStepOutcome::Token {
                    tok: SpecToken {
                        kind: SpecTokenKind::Number {
                            raw: spec_slice_bytes(input, start, end_pos),
                            is_bigint: true,
                            has_legacy_octal_or_leading_zero,
                        },
                        span: spec_span(start, end_pos),
                        preceded_by_line_terminator: saw_lt,
                    },
                    next_pos: end_pos,
                }
            }
        }
    } else if spec_invalid_after_numeric(input, end_before_n) {
        SpecStepOutcome::SyntaxError(SyntaxDiagnostic {
            kind: DiagnosticKind::NumericFollowedByIdent,
            span: spec_span(start, end_before_n + 1),
        })
    } else {
        SpecStepOutcome::Token {
            tok: SpecToken {
                kind: SpecTokenKind::Number {
                    raw: spec_slice_bytes(input, start, end_before_n),
                    is_bigint: false,
                    has_legacy_octal_or_leading_zero,
                },
                span: spec_span(start, end_before_n),
                preceded_by_line_terminator: saw_lt,
            },
            next_pos: end_before_n,
        }
    }
}

pub fn finalize_number_token(
    input: &[u8],
    start: usize,
    end_before_n: usize,
    allow_bigint: bool,
    has_legacy_octal_or_leading_zero: bool,
    saw_lt: bool,
) -> (r: StepOutcome)
    requires
        start < end_before_n && end_before_n <= input@.len(),
    ensures
        r@ == spec_finalize_number_token(
            input@,
            start as nat,
            end_before_n as nat,
            allow_bigint,
            has_legacy_octal_or_leading_zero,
            saw_lt,
        ),
        match r@ {
            SpecStepOutcome::Token { tok, next_pos } => {
                start < next_pos
                    && next_pos <= input@.len()
                    && tok.span == spec_span(start as nat, next_pos)
            },
            _ => true,
        },
{
    let n = input.len();
    if end_before_n < n && input[end_before_n] == 0x6E {
        let end_pos = end_before_n + 1;
        if !allow_bigint {
            StepOutcome::SyntaxError(SyntaxDiagnostic {
                kind: DiagnosticKind::InvalidNumericLiteral,
                span: Span { start, end: end_pos },
            })
        } else if invalid_after_numeric(input, end_pos) {
            StepOutcome::SyntaxError(SyntaxDiagnostic {
                kind: DiagnosticKind::NumericFollowedByIdent,
                span: Span { start, end: end_pos + 1 },
            })
        } else {
            StepOutcome::Token {
                tok: Token {
                    kind: TokenKind::Number {
                        raw: slice_bytes(input, start, end_pos),
                        is_bigint: true,
                        has_legacy_octal_or_leading_zero,
                    },
                    span: Span { start, end: end_pos },
                    preceded_by_line_terminator: saw_lt,
                },
                next_pos: end_pos,
            }
        }
    } else if invalid_after_numeric(input, end_before_n) {
        StepOutcome::SyntaxError(SyntaxDiagnostic {
            kind: DiagnosticKind::NumericFollowedByIdent,
            span: Span { start, end: end_before_n + 1 },
        })
    } else {
        StepOutcome::Token {
            tok: Token {
                kind: TokenKind::Number {
                    raw: slice_bytes(input, start, end_before_n),
                    is_bigint: false,
                    has_legacy_octal_or_leading_zero,
                },
                span: Span { start, end: end_before_n },
                preceded_by_line_terminator: saw_lt,
            },
            next_pos: end_before_n,
        }
    }
}

/// Optional `. DecimalDigits? ExponentPart?` tail starting at `after_int`.
pub open spec fn spec_lex_decimal_tail(
    input: Seq<u8>,
    start: nat,
    after_int: nat,
    allow_bigint_if_int: bool,
    has_legacy_zero: bool,
    saw_lt: bool,
) -> SpecStepOutcome {
    let (frac_res, has_dot): (Result<nat, DiagnosticKind>, bool) =
        if after_int < input.len() && input[after_int as int] == 0x2E {
            match spec_scan_digits_loop(input, after_int + 1, 10, true, false, false, false) {
                Ok((af, _, _)) => (Ok(af), true),
                Err(k) => (Err(k), true),
            }
        } else {
            (Ok(after_int), false)
        };
    match frac_res {
        Ok(after_frac) => match spec_scan_optional_exponent(input, after_frac) {
            Ok((after_exp, has_exp)) => spec_finalize_number_token(
                input,
                start,
                after_exp,
                allow_bigint_if_int && !has_dot && !has_exp,
                has_legacy_zero,
                saw_lt,
            ),
            Err(kind) => SpecStepOutcome::SyntaxError(SyntaxDiagnostic {
                kind,
                span: spec_span(start, after_frac),
            }),
        },
        Err(kind) => SpecStepOutcome::SyntaxError(SyntaxDiagnostic {
            kind,
            span: spec_span(start, after_int),
        }),
    }
}

pub proof fn lemma_lex_decimal_tail_bounds(
    input: Seq<u8>,
    start: nat,
    after_int: nat,
    allow_bigint_if_int: bool,
    has_legacy_zero: bool,
    saw_lt: bool,
)
    requires
        start < after_int && after_int <= input.len(),
    ensures
        match spec_lex_decimal_tail(input, start, after_int, allow_bigint_if_int, has_legacy_zero, saw_lt) {
            SpecStepOutcome::Token { tok, next_pos } => {
                start < next_pos && next_pos <= input.len() && tok.span == spec_span(start, next_pos)
            },
            _ => true,
        },
{
    if after_int < input.len() && input[after_int as int] == 0x2E {
        lemma_scan_digits_bounds(input, after_int + 1, 10, true, false, false, false);
        if let Ok((af, _, _)) = spec_scan_digits_loop(input, after_int + 1, 10, true, false, false, false) {
            lemma_scan_optional_exponent_bounds(input, af);
        }
    } else {
        lemma_scan_optional_exponent_bounds(input, after_int);
    }
}

pub fn lex_decimal_tail(
    input: &[u8],
    start: usize,
    after_int: usize,
    allow_bigint_if_int: bool,
    has_legacy_zero: bool,
    saw_lt: bool,
) -> (r: StepOutcome)
    requires
        start < after_int && after_int <= input@.len(),
    ensures
        r@ == spec_lex_decimal_tail(
            input@,
            start as nat,
            after_int as nat,
            allow_bigint_if_int,
            has_legacy_zero,
            saw_lt,
        ),
        match r@ {
            SpecStepOutcome::Token { tok, next_pos } => {
                start < next_pos && next_pos <= input@.len() && tok.span == spec_span(start as nat, next_pos)
            },
            _ => true,
        },
{
    let n = input.len();
    let (frac_res, has_dot): (Result<usize, DiagnosticKind>, bool) =
        if after_int < n && input[after_int] == 0x2E {
            match scan_digits(input, after_int + 1, 10, true) {
                Ok((af, _, _)) => (Ok(af), true),
                Err(k) => (Err(k), true),
            }
        } else {
            (Ok(after_int), false)
        };
    match frac_res {
        Ok(after_frac) => match scan_optional_exponent(input, after_frac) {
            Ok((after_exp, has_exp)) => finalize_number_token(
                input,
                start,
                after_exp,
                allow_bigint_if_int && !has_dot && !has_exp,
                has_legacy_zero,
                saw_lt,
            ),
            Err(kind) => StepOutcome::SyntaxError(SyntaxDiagnostic {
                kind,
                span: Span { start, end: after_frac },
            }),
        },
        Err(kind) => StepOutcome::SyntaxError(SyntaxDiagnostic {
            kind,
            span: Span { start, end: after_int },
        }),
    }
}

pub open spec fn spec_lex_number(input: Seq<u8>, start: nat, saw_lt: bool) -> SpecStepOutcome {
    let b0 = input[start as int];
    if b0 == 0x2E {
        match spec_scan_digits_loop(input, start + 1, 10, true, false, false, false) {
            Ok((after_frac, has_any, _)) => {
                if !has_any {
                    SpecStepOutcome::SyntaxError(SyntaxDiagnostic {
                        kind: DiagnosticKind::InvalidNumericLiteral,
                        span: spec_span(start, start + 1),
                    })
                } else {
                    match spec_scan_optional_exponent(input, after_frac) {
                        Ok((after_exp, _)) => {
                            spec_finalize_number_token(input, start, after_exp, false, false, saw_lt)
                        },
                        Err(kind) => SpecStepOutcome::SyntaxError(SyntaxDiagnostic {
                            kind,
                            span: spec_span(start, after_frac),
                        }),
                    }
                }
            },
            Err(kind) => SpecStepOutcome::SyntaxError(SyntaxDiagnostic {
                kind,
                span: spec_span(start, start + 1),
            }),
        }
    } else if b0 == 0x30
        && start + 1 < input.len()
        && (input[(start + 1) as int] == 0x78
            || input[(start + 1) as int] == 0x58
            || input[(start + 1) as int] == 0x62
            || input[(start + 1) as int] == 0x42
            || input[(start + 1) as int] == 0x6F
            || input[(start + 1) as int] == 0x4F)
    {
        let pfx = input[(start + 1) as int];
        let radix: u8 = if pfx == 0x78 || pfx == 0x58 {
            16
        } else if pfx == 0x62 || pfx == 0x42 {
            2
        } else {
            8
        };
        match spec_scan_digits_loop(input, start + 2, radix, true, false, false, false) {
            Ok((after_digits, has_any, _)) => {
                if !has_any {
                    SpecStepOutcome::SyntaxError(SyntaxDiagnostic {
                        kind: DiagnosticKind::InvalidNumericLiteral,
                        span: spec_span(start, start + 2),
                    })
                } else {
                    spec_finalize_number_token(input, start, after_digits, true, false, saw_lt)
                }
            },
            Err(kind) => SpecStepOutcome::SyntaxError(SyntaxDiagnostic {
                kind,
                span: spec_span(start, start + 2),
            }),
        }
    } else if b0 == 0x30 && start + 1 < input.len() && input[(start + 1) as int] == 0x5F {
        SpecStepOutcome::SyntaxError(SyntaxDiagnostic {
            kind: DiagnosticKind::InvalidNumericLiteral,
            span: spec_span(start, start + 2),
        })
    } else if b0 == 0x30 && start + 1 < input.len() && spec_is_ascii_digit(input[(start + 1) as int]) {
        match spec_scan_digits_loop(input, start + 1, 10, false, false, false, false) {
            Ok((after_int, _, has_89)) => {
                if !has_89 {
                    if after_int < input.len()
                        && (input[after_int as int] == 0x2E
                            || input[after_int as int] == 0x65
                            || input[after_int as int] == 0x45)
                    {
                        SpecStepOutcome::SyntaxError(SyntaxDiagnostic {
                            kind: DiagnosticKind::InvalidNumericLiteral,
                            span: spec_span(start, after_int + 1),
                        })
                    } else {
                        spec_finalize_number_token(input, start, after_int, false, true, saw_lt)
                    }
                } else {
                    spec_lex_decimal_tail(input, start, after_int, false, true, saw_lt)
                }
            },
            Err(kind) => SpecStepOutcome::SyntaxError(SyntaxDiagnostic {
                kind,
                span: spec_span(start, start + 1),
            }),
        }
    } else {
        match spec_scan_digits_loop(input, start, 10, true, false, false, false) {
            Ok((after_int, _, _)) => {
                spec_lex_decimal_tail(input, start, after_int, true, false, saw_lt)
            },
            Err(kind) => SpecStepOutcome::SyntaxError(SyntaxDiagnostic {
                kind,
                span: spec_span(start, start + 1),
            }),
        }
    }
}

pub proof fn lemma_lex_number_bounds(input: Seq<u8>, start: nat, saw_lt: bool)
    requires
        start < input.len(),
        spec_is_ascii_digit(input[start as int])
            || (input[start as int] == 0x2E
                && start + 1 < input.len()
                && spec_is_ascii_digit(input[(start + 1) as int])),
    ensures
        match spec_lex_number(input, start, saw_lt) {
            SpecStepOutcome::Token { tok, next_pos } => {
                start < next_pos && next_pos <= input.len() && tok.span == spec_span(start, next_pos)
            },
            _ => true,
        },
{
    let b0 = input[start as int];
    if b0 == 0x2E {
        lemma_scan_digits_bounds(input, start + 1, 10, true, false, false, false);
        if let Ok((after_frac, has_any, _)) = spec_scan_digits_loop(input, start + 1, 10, true, false, false, false) {
            if has_any {
                lemma_scan_optional_exponent_bounds(input, after_frac);
            }
        }
    } else if b0 == 0x30
        && start + 1 < input.len()
        && (input[(start + 1) as int] == 0x78
            || input[(start + 1) as int] == 0x58
            || input[(start + 1) as int] == 0x62
            || input[(start + 1) as int] == 0x42
            || input[(start + 1) as int] == 0x6F
            || input[(start + 1) as int] == 0x4F)
    {
        let pfx = input[(start + 1) as int];
        let r: u8 = if pfx == 0x78 || pfx == 0x58 { 16 } else if pfx == 0x62 || pfx == 0x42 { 2 } else { 8 };
        lemma_scan_digits_bounds(input, start + 2, r, true, false, false, false);
    } else if b0 == 0x30 && start + 1 < input.len() && input[(start + 1) as int] == 0x5F {
    } else if b0 == 0x30 && start + 1 < input.len() && spec_is_ascii_digit(input[(start + 1) as int]) {
        let b1 = input[(start + 1) as int];
        lemma_scan_digits_bounds(input, start + 2, 10, false, true, false, b1 == 0x38 || b1 == 0x39);
        if let Ok((after_int, _, has_89)) = spec_scan_digits_loop(input, start + 1, 10, false, false, false, false) {
            if has_89 {
                lemma_lex_decimal_tail_bounds(input, start, after_int, false, true, saw_lt);
            }
        }
    } else {
        lemma_scan_digits_bounds(input, start + 1, 10, true, true, false, b0 == 0x38 || b0 == 0x39);
        if let Ok((after_int, _, _)) = spec_scan_digits_loop(input, start, 10, true, false, false, false) {
            lemma_lex_decimal_tail_bounds(input, start, after_int, true, false, saw_lt);
        }
    }
}

pub fn lex_number(input: &[u8], start: usize, saw_lt: bool) -> (r: StepOutcome)
    requires
        start < input@.len(),
        spec_is_ascii_digit(input@[start as int])
            || (input@[start as int] == 0x2E
                && start + 1 < input@.len()
                && spec_is_ascii_digit(input@[(start + 1) as int])),
    ensures
        r@ == spec_lex_number(input@, start as nat, saw_lt),
        match r@ {
            SpecStepOutcome::Token { tok, next_pos } => {
                start < next_pos && next_pos <= input@.len() && tok.span == spec_span(start as nat, next_pos)
            },
            _ => true,
        },
{
    let n = input.len();
    let rem = n - start;
    let b0 = input[start];
    if b0 == 0x2E {
        match scan_digits(input, start + 1, 10, true) {
            Ok((after_frac, has_any, _)) => {
                if !has_any {
                    StepOutcome::SyntaxError(SyntaxDiagnostic {
                        kind: DiagnosticKind::InvalidNumericLiteral,
                        span: Span { start, end: start + 1 },
                    })
                } else {
                    match scan_optional_exponent(input, after_frac) {
                        Ok((after_exp, _)) => {
                            finalize_number_token(input, start, after_exp, false, false, saw_lt)
                        },
                        Err(kind) => StepOutcome::SyntaxError(SyntaxDiagnostic {
                            kind,
                            span: Span { start, end: after_frac },
                        }),
                    }
                }
            },
            Err(kind) => StepOutcome::SyntaxError(SyntaxDiagnostic {
                kind,
                span: Span { start, end: start + 1 },
            }),
        }
    } else if b0 == 0x30
        && rem >= 2
        && (input[start + 1] == 0x78
            || input[start + 1] == 0x58
            || input[start + 1] == 0x62
            || input[start + 1] == 0x42
            || input[start + 1] == 0x6F
            || input[start + 1] == 0x4F)
    {
        let pfx = input[start + 1];
        let radix: u8 = if pfx == 0x78 || pfx == 0x58 {
            16
        } else if pfx == 0x62 || pfx == 0x42 {
            2
        } else {
            8
        };
        match scan_digits(input, start + 2, radix, true) {
            Ok((after_digits, has_any, _)) => {
                if !has_any {
                    StepOutcome::SyntaxError(SyntaxDiagnostic {
                        kind: DiagnosticKind::InvalidNumericLiteral,
                        span: Span { start, end: start + 2 },
                    })
                } else {
                    finalize_number_token(input, start, after_digits, true, false, saw_lt)
                }
            },
            Err(kind) => StepOutcome::SyntaxError(SyntaxDiagnostic {
                kind,
                span: Span { start, end: start + 2 },
            }),
        }
    } else if b0 == 0x30 && rem >= 2 && input[start + 1] == 0x5F {
        StepOutcome::SyntaxError(SyntaxDiagnostic {
            kind: DiagnosticKind::InvalidNumericLiteral,
            span: Span { start, end: start + 2 },
        })
    } else if b0 == 0x30 && rem >= 2 && is_ascii_digit(input[start + 1]) {
        proof {
            let b1 = input@[(start + 1) as int];
            lemma_scan_digits_bounds(input@, (start + 2) as nat, 10, false, true, false, b1 == 0x38 || b1 == 0x39);
        }
        match scan_digits(input, start + 1, 10, false) {
            Ok((after_int, _, has_89)) => {
                if !has_89 {
                    if after_int < n
                        && (input[after_int] == 0x2E
                            || input[after_int] == 0x65
                            || input[after_int] == 0x45)
                    {
                        StepOutcome::SyntaxError(SyntaxDiagnostic {
                            kind: DiagnosticKind::InvalidNumericLiteral,
                            span: Span { start, end: after_int + 1 },
                        })
                    } else {
                        finalize_number_token(input, start, after_int, false, true, saw_lt)
                    }
                } else {
                    lex_decimal_tail(input, start, after_int, false, true, saw_lt)
                }
            },
            Err(kind) => StepOutcome::SyntaxError(SyntaxDiagnostic {
                kind,
                span: Span { start, end: start + 1 },
            }),
        }
    } else {
        proof {
            lemma_scan_digits_bounds(input@, (start + 1) as nat, 10, true, true, false, b0 == 0x38 || b0 == 0x39);
        }
        match scan_digits(input, start, 10, true) {
            Ok((after_int, _, _)) => {
                lex_decimal_tail(input, start, after_int, true, false, saw_lt)
            },
            Err(kind) => StepOutcome::SyntaxError(SyntaxDiagnostic {
                kind,
                span: Span { start, end: start + 1 },
            }),
        }
    }
}

// ---------------------------------------------------------------------------------------
// String & Template Literal Scanning (§12.8.4, §12.8.6)
// ---------------------------------------------------------------------------------------

pub open spec fn spec_is_exact_use_strict_slice(input: Seq<u8>, start: nat, end: nat) -> bool {
    end >= start
        && end - start == 12
        && end <= input.len()
        && input[(start + 1) as int] == 0x75
        && input[(start + 2) as int] == 0x73
        && input[(start + 3) as int] == 0x65
        && input[(start + 4) as int] == 0x20
        && input[(start + 5) as int] == 0x73
        && input[(start + 6) as int] == 0x74
        && input[(start + 7) as int] == 0x72
        && input[(start + 8) as int] == 0x69
        && input[(start + 9) as int] == 0x63
        && input[(start + 10) as int] == 0x74
}

pub fn is_exact_use_strict_slice(input: &[u8], start: usize, end: usize) -> (r: bool)
    requires
        start <= end && end <= input@.len(),
    ensures
        r == spec_is_exact_use_strict_slice(input@, start as nat, end as nat),
{
    end - start == 12
        && input[start + 1] == 0x75
        && input[start + 2] == 0x73
        && input[start + 3] == 0x65
        && input[start + 4] == 0x20
        && input[start + 5] == 0x73
        && input[start + 6] == 0x74
        && input[start + 7] == 0x72
        && input[start + 8] == 0x69
        && input[start + 9] == 0x63
        && input[start + 10] == 0x74
}

pub open spec fn spec_decode_legacy_octal_escape(input: Seq<u8>, esc_pos: nat) -> (u16, nat) {
    let d0 = (input[esc_pos as int] - 0x30) as u16;
    if esc_pos + 1 < input.len() && spec_is_octal_digit(input[(esc_pos + 1) as int]) {
        let d1 = (input[(esc_pos + 1) as int] - 0x30) as u16;
        let v2 = (d0 * 8 + d1) as u16;
        if d0 <= 3 && esc_pos + 2 < input.len() && spec_is_octal_digit(input[(esc_pos + 2) as int]) {
            let d2 = (input[(esc_pos + 2) as int] - 0x30) as u16;
            ((v2 * 8 + d2) as u16, esc_pos + 3)
        } else {
            (v2, esc_pos + 2)
        }
    } else {
        (d0, esc_pos + 1)
    }
}

pub fn decode_legacy_octal_escape(input: &[u8], esc_pos: usize) -> (r: (u16, usize))
    requires
        esc_pos < input@.len(),
        spec_is_octal_digit(input@[esc_pos as int]),
    ensures
        (r.0, r.1 as nat) == spec_decode_legacy_octal_escape(input@, esc_pos as nat),
        esc_pos < r.1 && r.1 <= input@.len(),
{
    let n = input.len();
    let rem = n - esc_pos;
    let d0 = (input[esc_pos] - 0x30) as u16;
    if rem >= 2 && is_octal_digit(input[esc_pos + 1]) {
        let d1 = (input[esc_pos + 1] - 0x30) as u16;
        let v2 = d0 * 8 + d1;
        if d0 <= 3 && rem >= 3 && is_octal_digit(input[esc_pos + 2]) {
            let d2 = (input[esc_pos + 2] - 0x30) as u16;
            (v2 * 8 + d2, esc_pos + 3)
        } else {
            (v2, esc_pos + 2)
        }
    } else {
        (d0, esc_pos + 1)
    }
}

/// Decoded single character or escape inside a string literal (`pos` is at backslash `\` or normal byte).
pub enum SpecStrStep {
    ClosingQuote(nat),
    SkipLineCont(nat),
    Unit { u: u16, octal_esc: bool, next_pos: nat },
    CodePoint { cp: u32, next_pos: nat },
    Err(SyntaxDiagnostic),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum StrStep {
    ClosingQuote(usize),
    SkipLineCont(usize),
    Unit { u: u16, octal_esc: bool, next_pos: usize },
    CodePoint { cp: u32, next_pos: usize },
    Err(SyntaxDiagnostic),
}

#[verifier::opaque]
pub open spec fn spec_string_step(
    input: Seq<u8>,
    quote: u8,
    start: nat,
    pos: nat,
) -> SpecStrStep {
    let b = input[pos as int];
    if b == quote {
        SpecStrStep::ClosingQuote(pos + 1)
    } else if b == 0x0A || b == 0x0D {
        SpecStrStep::Err(SyntaxDiagnostic {
            kind: DiagnosticKind::UnterminatedStringLiteral,
            span: spec_span(start, pos),
        })
    } else if b == 0x5C {
        let ep = pos + 1;
        if ep >= input.len() {
            SpecStrStep::Err(SyntaxDiagnostic {
                kind: DiagnosticKind::UnterminatedStringLiteral,
                span: spec_span(start, input.len()),
            })
        } else {
            let lt_len = spec_utf8_line_terminator_len(input, ep);
            if lt_len > 0 {
                SpecStrStep::SkipLineCont(ep + lt_len)
            } else {
                let e = input[ep as int];
                if e == 0x6E {
                    SpecStrStep::Unit { u: 0x000A, octal_esc: false, next_pos: ep + 1 }
                } else if e == 0x72 {
                    SpecStrStep::Unit { u: 0x000D, octal_esc: false, next_pos: ep + 1 }
                } else if e == 0x74 {
                    SpecStrStep::Unit { u: 0x0009, octal_esc: false, next_pos: ep + 1 }
                } else if e == 0x62 {
                    SpecStrStep::Unit { u: 0x0008, octal_esc: false, next_pos: ep + 1 }
                } else if e == 0x66 {
                    SpecStrStep::Unit { u: 0x000C, octal_esc: false, next_pos: ep + 1 }
                } else if e == 0x76 {
                    SpecStrStep::Unit { u: 0x000B, octal_esc: false, next_pos: ep + 1 }
                } else if e == 0x5C {
                    SpecStrStep::Unit { u: 0x005C, octal_esc: false, next_pos: ep + 1 }
                } else if e == 0x27 {
                    SpecStrStep::Unit { u: 0x0027, octal_esc: false, next_pos: ep + 1 }
                } else if e == 0x22 {
                    SpecStrStep::Unit { u: 0x0022, octal_esc: false, next_pos: ep + 1 }
                } else if e == 0x30 && !(ep + 1 < input.len() && spec_is_ascii_digit(input[(ep + 1) as int])) {
                    SpecStrStep::Unit { u: 0x0000, octal_esc: false, next_pos: ep + 1 }
                } else if spec_is_octal_digit(e) {
                    let (val, next_pos) = spec_decode_legacy_octal_escape(input, ep);
                    SpecStrStep::Unit { u: val, octal_esc: true, next_pos }
                } else if e == 0x38 || e == 0x39 {
                    SpecStrStep::Unit { u: e as u16, octal_esc: true, next_pos: ep + 1 }
                } else if e == 0x78 {
                    if ep + 2 < input.len()
                        && spec_is_hex_digit(input[(ep + 1) as int])
                        && spec_is_hex_digit(input[(ep + 2) as int])
                    {
                        let v = (spec_hex_val(input[(ep + 1) as int]) * 16
                            + spec_hex_val(input[(ep + 2) as int])) as u16;
                        SpecStrStep::Unit { u: v, octal_esc: false, next_pos: ep + 3 }
                    } else {
                        SpecStrStep::Err(SyntaxDiagnostic {
                            kind: DiagnosticKind::InvalidHexEscape,
                            span: spec_span(pos, ep + 1),
                        })
                    }
                } else if e == 0x75 {
                    match spec_decode_unicode_escape_after_u(input, ep + 1) {
                        Ok((cp, next_pos)) => SpecStrStep::CodePoint { cp, next_pos },
                        Err(kind) => SpecStrStep::Err(SyntaxDiagnostic {
                            kind,
                            span: spec_span(pos, input.len()),
                        }),
                    }
                } else {
                    match spec_decode_utf8_scalar(input, ep) {
                        Some((cp, ulen)) => SpecStrStep::CodePoint { cp, next_pos: ep + (ulen as nat) },
                        None => SpecStrStep::Err(SyntaxDiagnostic {
                            kind: DiagnosticKind::InvalidUtf8Encoding,
                            span: spec_span(ep, ep + 1),
                        }),
                    }
                }
            }
        }
    } else {
        match spec_decode_utf8_scalar(input, pos) {
            Some((cp, ulen)) => SpecStrStep::CodePoint { cp, next_pos: pos + (ulen as nat) },
            None => SpecStrStep::Err(SyntaxDiagnostic {
                kind: DiagnosticKind::InvalidUtf8Encoding,
                span: spec_span(pos, pos + 1),
            }),
        }
    }
}

pub proof fn lemma_string_step_bounds(input: Seq<u8>, quote: u8, start: nat, pos: nat)
    requires
        pos < input.len(),
    ensures
        match spec_string_step(input, quote, start, pos) {
            SpecStrStep::ClosingQuote(next_pos) => pos < next_pos && next_pos <= input.len(),
            SpecStrStep::SkipLineCont(next_pos) => pos < next_pos && next_pos <= input.len(),
            SpecStrStep::Unit { next_pos, .. } => pos < next_pos && next_pos <= input.len(),
            SpecStrStep::CodePoint { cp, next_pos } => cp <= 0x10FFFF && pos < next_pos && next_pos <= input.len(),
            SpecStrStep::Err(_) => true,
        },
{
    reveal(spec_string_step);
    let b = input[pos as int];
    if b != quote && b != 0x0A && b != 0x0D && b == 0x5C {
        let ep = pos + 1;
        if ep < input.len() && spec_utf8_line_terminator_len(input, ep) == 0 && input[ep as int] == 0x75 {
            if ep + 1 < input.len() && input[(ep + 1) as int] == 0x7B {
                lemma_parse_braced_hex_bounds(input, ep + 2, 0, false);
            }
        }
    }
}

#[verifier::rlimit(40)]
pub fn string_step(input: &[u8], quote: u8, start: usize, pos: usize) -> (r: StrStep)
    requires
        start <= pos && pos < input@.len(),
    ensures
        match r {
            StrStep::ClosingQuote(next_pos) => {
                spec_string_step(input@, quote, start as nat, pos as nat)
                    == SpecStrStep::ClosingQuote(next_pos as nat)
                    && pos < next_pos && next_pos <= input@.len()
            },
            StrStep::SkipLineCont(next_pos) => {
                spec_string_step(input@, quote, start as nat, pos as nat)
                    == SpecStrStep::SkipLineCont(next_pos as nat)
                    && pos < next_pos && next_pos <= input@.len()
            },
            StrStep::Unit { u, octal_esc, next_pos } => {
                spec_string_step(input@, quote, start as nat, pos as nat)
                    == SpecStrStep::Unit { u, octal_esc, next_pos: next_pos as nat }
                    && pos < next_pos && next_pos <= input@.len()
            },
            StrStep::CodePoint { cp, next_pos } => {
                spec_string_step(input@, quote, start as nat, pos as nat)
                    == SpecStrStep::CodePoint { cp, next_pos: next_pos as nat }
                    && cp <= 0x10FFFF && pos < next_pos && next_pos <= input@.len()
            },
            StrStep::Err(e) => {
                spec_string_step(input@, quote, start as nat, pos as nat) == SpecStrStep::Err(e)
            },
        },
{
    proof {
        reveal(spec_string_step);
    }
    let n = input.len();
    let b = input[pos];
    if b == quote {
        StrStep::ClosingQuote(pos + 1)
    } else if b == 0x0A || b == 0x0D {
        StrStep::Err(SyntaxDiagnostic {
            kind: DiagnosticKind::UnterminatedStringLiteral,
            span: Span { start, end: pos },
        })
    } else if b == 0x5C {
        let ep = pos + 1;
        if ep >= n {
            StrStep::Err(SyntaxDiagnostic {
                kind: DiagnosticKind::UnterminatedStringLiteral,
                span: Span { start, end: n },
            })
        } else {
            let lt_len = utf8_line_terminator_len(input, ep);
            if lt_len > 0 {
                StrStep::SkipLineCont(ep + lt_len)
            } else {
                let rem_ep = n - ep;
                let e = input[ep];
                if e == 0x6E {
                    StrStep::Unit { u: 0x000A, octal_esc: false, next_pos: ep + 1 }
                } else if e == 0x72 {
                    StrStep::Unit { u: 0x000D, octal_esc: false, next_pos: ep + 1 }
                } else if e == 0x74 {
                    StrStep::Unit { u: 0x0009, octal_esc: false, next_pos: ep + 1 }
                } else if e == 0x62 {
                    StrStep::Unit { u: 0x0008, octal_esc: false, next_pos: ep + 1 }
                } else if e == 0x66 {
                    StrStep::Unit { u: 0x000C, octal_esc: false, next_pos: ep + 1 }
                } else if e == 0x76 {
                    StrStep::Unit { u: 0x000B, octal_esc: false, next_pos: ep + 1 }
                } else if e == 0x5C {
                    StrStep::Unit { u: 0x005C, octal_esc: false, next_pos: ep + 1 }
                } else if e == 0x27 {
                    StrStep::Unit { u: 0x0027, octal_esc: false, next_pos: ep + 1 }
                } else if e == 0x22 {
                    StrStep::Unit { u: 0x0022, octal_esc: false, next_pos: ep + 1 }
                } else if e == 0x30 && !(rem_ep >= 2 && is_ascii_digit(input[ep + 1])) {
                    StrStep::Unit { u: 0x0000, octal_esc: false, next_pos: ep + 1 }
                } else if is_octal_digit(e) {
                    let (val, next_pos) = decode_legacy_octal_escape(input, ep);
                    StrStep::Unit { u: val, octal_esc: true, next_pos }
                } else if e == 0x38 || e == 0x39 {
                    StrStep::Unit { u: e as u16, octal_esc: true, next_pos: ep + 1 }
                } else if e == 0x78 {
                    if rem_ep >= 3 && is_hex_digit(input[ep + 1]) && is_hex_digit(input[ep + 2]) {
                        let v = (hex_val(input[ep + 1]) * 16 + hex_val(input[ep + 2])) as u16;
                        StrStep::Unit { u: v, octal_esc: false, next_pos: ep + 3 }
                    } else {
                        StrStep::Err(SyntaxDiagnostic {
                            kind: DiagnosticKind::InvalidHexEscape,
                            span: Span { start: pos, end: ep + 1 },
                        })
                    }
                } else if e == 0x75 {
                    match decode_unicode_escape_after_u(input, ep + 1) {
                        Ok((cp, next_pos)) => StrStep::CodePoint { cp, next_pos },
                        Err(kind) => StrStep::Err(SyntaxDiagnostic {
                            kind,
                            span: Span { start: pos, end: n },
                        }),
                    }
                } else {
                    match decode_utf8_scalar(input, ep) {
                        Some((cp, ulen)) => StrStep::CodePoint { cp, next_pos: ep + ulen },
                        None => StrStep::Err(SyntaxDiagnostic {
                            kind: DiagnosticKind::InvalidUtf8Encoding,
                            span: Span { start: ep, end: ep + 1 },
                        }),
                    }
                }
            }
        }
    } else {
        match decode_utf8_scalar(input, pos) {
            Some((cp, ulen)) => StrStep::CodePoint { cp, next_pos: pos + ulen },
            None => StrStep::Err(SyntaxDiagnostic {
                kind: DiagnosticKind::InvalidUtf8Encoding,
                span: Span { start: pos, end: pos + 1 },
            }),
        }
    }
}

pub open spec fn spec_lex_string_loop(
    input: Seq<u8>,
    quote: u8,
    start: nat,
    pos: nat,
    units: Seq<u16>,
    has_octal_esc: bool,
) -> Result<(Seq<u16>, bool, nat), SyntaxDiagnostic>
    decreases input.len() - pos,
{
    if pos >= input.len() {
        Err(SyntaxDiagnostic {
            kind: DiagnosticKind::UnterminatedStringLiteral,
            span: spec_span(start, input.len()),
        })
    } else {
        match spec_string_step(input, quote, start, pos) {
            SpecStrStep::ClosingQuote(end_pos) => Ok((units, has_octal_esc, end_pos)),
            SpecStrStep::SkipLineCont(next_pos) => {
                if next_pos > pos && next_pos <= input.len() {
                    spec_lex_string_loop(input, quote, start, next_pos, units, has_octal_esc)
                } else {
                    Err(SyntaxDiagnostic {
                        kind: DiagnosticKind::UnterminatedStringLiteral,
                        span: spec_span(start, input.len()),
                    })
                }
            },
            SpecStrStep::Unit { u, octal_esc, next_pos } => {
                if next_pos > pos && next_pos <= input.len() {
                    spec_lex_string_loop(input, quote, start, next_pos, units.push(u), has_octal_esc || octal_esc)
                } else {
                    Err(SyntaxDiagnostic {
                        kind: DiagnosticKind::UnterminatedStringLiteral,
                        span: spec_span(start, input.len()),
                    })
                }
            },
            SpecStrStep::CodePoint { cp, next_pos } => {
                if next_pos > pos && next_pos <= input.len() {
                    spec_lex_string_loop(
                        input,
                        quote,
                        start,
                        next_pos,
                        spec_append_utf16_cp(units, cp),
                        has_octal_esc,
                    )
                } else {
                    Err(SyntaxDiagnostic {
                        kind: DiagnosticKind::UnterminatedStringLiteral,
                        span: spec_span(start, input.len()),
                    })
                }
            },
            SpecStrStep::Err(e) => Err(e),
        }
    }
}

pub proof fn lemma_lex_string_bounds(
    input: Seq<u8>,
    quote: u8,
    start: nat,
    pos: nat,
    units: Seq<u16>,
    has_octal_esc: bool,
)
    requires
        pos <= input.len(),
    ensures
        match spec_lex_string_loop(input, quote, start, pos, units, has_octal_esc) {
            Ok((_, _, end_pos)) => pos < end_pos && end_pos <= input.len(),
            Err(_) => true,
        },
    decreases input.len() - pos,
{
    if pos < input.len() {
        lemma_string_step_bounds(input, quote, start, pos);
        match spec_string_step(input, quote, start, pos) {
            SpecStrStep::SkipLineCont(next_pos) => {
                lemma_lex_string_bounds(input, quote, start, next_pos, units, has_octal_esc);
            },
            SpecStrStep::Unit { u, octal_esc, next_pos } => {
                lemma_lex_string_bounds(input, quote, start, next_pos, units.push(u), has_octal_esc || octal_esc);
            },
            SpecStrStep::CodePoint { cp, next_pos } => {
                lemma_lex_string_bounds(input, quote, start, next_pos, spec_append_utf16_cp(units, cp), has_octal_esc);
            },
            _ => {},
        }
    }
}

pub open spec fn spec_lex_string(input: Seq<u8>, start: nat, saw_lt: bool) -> SpecStepOutcome {
    let quote = input[start as int];
    match spec_lex_string_loop(input, quote, start, start + 1, Seq::<u16>::empty(), false) {
        Ok((units, has_legacy_octal_escape, end_pos)) => {
            let is_exact_use_strict = spec_is_exact_use_strict_slice(input, start, end_pos);
            SpecStepOutcome::Token {
                tok: SpecToken {
                    kind: SpecTokenKind::StringLit {
                        units,
                        has_legacy_octal_escape,
                        is_exact_use_strict,
                    },
                    span: spec_span(start, end_pos),
                    preceded_by_line_terminator: saw_lt,
                },
                next_pos: end_pos,
            }
        },
        Err(e) => SpecStepOutcome::SyntaxError(e),
    }
}

pub fn lex_string(input: &[u8], start: usize, saw_lt: bool) -> (r: StepOutcome)
    requires
        start < input@.len(),
        input@[start as int] == 0x22 || input@[start as int] == 0x27,
    ensures
        r@ == spec_lex_string(input@, start as nat, saw_lt),
        match r@ {
            SpecStepOutcome::Token { tok, next_pos } => {
                start < next_pos && next_pos <= input@.len() && tok.span == spec_span(start as nat, next_pos)
            },
            _ => true,
        },
{
    let n = input.len();
    let quote = input[start];
    let mut pos = start + 1;
    let mut units: Vec<u16> = Vec::new();
    let mut has_octal_esc = false;
    proof {
        assert(units@ =~= Seq::<u16>::empty());
    }
    while pos < n
        invariant
            start < pos && pos <= n,
            n == input@.len(),
            quote == input@[start as int],
            spec_lex_string_loop(input@, quote, start as nat, pos as nat, units@, has_octal_esc)
                == spec_lex_string_loop(input@, quote, start as nat, (start + 1) as nat, Seq::<u16>::empty(), false),
        decreases n - pos,
    {
        match string_step(input, quote, start, pos) {
            StrStep::ClosingQuote(end_pos) => {
                proof {
                    lemma_lex_string_bounds(input@, quote, start as nat, (start + 1) as nat, Seq::<u16>::empty(), false);
                }
                let is_exact_use_strict = is_exact_use_strict_slice(input, start, end_pos);
                return StepOutcome::Token {
                    tok: Token {
                        kind: TokenKind::StringLit {
                            units,
                            has_legacy_octal_escape: has_octal_esc,
                            is_exact_use_strict,
                        },
                        span: Span { start, end: end_pos },
                        preceded_by_line_terminator: saw_lt,
                    },
                    next_pos: end_pos,
                };
            },
            StrStep::SkipLineCont(next_pos) => {
                pos = next_pos;
            },
            StrStep::Unit { u, octal_esc, next_pos } => {
                units.push(u);
                has_octal_esc = has_octal_esc || octal_esc;
                pos = next_pos;
            },
            StrStep::CodePoint { cp, next_pos } => {
                append_utf16_cp(&mut units, cp);
                pos = next_pos;
            },
            StrStep::Err(e) => {
                return StepOutcome::SyntaxError(e);
            },
        }
    }
    StepOutcome::SyntaxError(SyntaxDiagnostic {
        kind: DiagnosticKind::UnterminatedStringLiteral,
        span: Span { start, end: n },
    })
}

/// Backtick template scanner (§12.8.6): decodes full `EscapeSequence` (`\n`, `\r`, `\t`, `\b`, `\f`,
/// `\v`, `\0` when not followed by `DecimalDigit`, `\xHH`, `\uHHHH`, `\u{H...}`, line continuations,
/// and `<CR>`/`<CR><LF>` -> `<LF>`), records `NotEscapeSequence` in `has_invalid_escape` (§13.2.8.1),
/// and flags `${` template substitutions as `Unsupported(TemplateSubstitution)`.
pub enum SpecTplStep {
    ClosingBacktick(nat),
    Substitution(nat),
    SkipOrInvalid { mark_invalid: bool, next_pos: nat },
    Unit { u: u16, next_pos: nat },
    CodePoint { cp: u32, next_pos: nat },
    Err(SyntaxDiagnostic),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TplStep {
    ClosingBacktick(usize),
    Substitution(usize),
    SkipOrInvalid { mark_invalid: bool, next_pos: usize },
    Unit { u: u16, next_pos: usize },
    CodePoint { cp: u32, next_pos: usize },
    Err(SyntaxDiagnostic),
}

#[verifier::opaque]
pub open spec fn spec_template_step(input: Seq<u8>, start: nat, pos: nat) -> SpecTplStep {
    let b = input[pos as int];
    if b == 0x60 {
        SpecTplStep::ClosingBacktick(pos + 1)
    } else if b == 0x24 && pos + 1 < input.len() && input[(pos + 1) as int] == 0x7B {
        SpecTplStep::Substitution(pos + 2)
    } else if b == 0x0D {
        let step: nat = if pos + 1 < input.len() && input[(pos + 1) as int] == 0x0A { 2 } else { 1 };
        SpecTplStep::Unit { u: 0x000A, next_pos: pos + step }
    } else if b == 0x5C {
        let ep = pos + 1;
        if ep >= input.len() {
            SpecTplStep::Err(SyntaxDiagnostic {
                kind: DiagnosticKind::UnterminatedTemplateLiteral,
                span: spec_span(start, input.len()),
            })
        } else {
            let lt_len = spec_utf8_line_terminator_len(input, ep);
            if lt_len > 0 {
                SpecTplStep::SkipOrInvalid { mark_invalid: false, next_pos: ep + lt_len }
            } else {
                let e = input[ep as int];
                if e == 0x6E {
                    SpecTplStep::Unit { u: 0x000A, next_pos: ep + 1 }
                } else if e == 0x72 {
                    SpecTplStep::Unit { u: 0x000D, next_pos: ep + 1 }
                } else if e == 0x74 {
                    SpecTplStep::Unit { u: 0x0009, next_pos: ep + 1 }
                } else if e == 0x62 {
                    SpecTplStep::Unit { u: 0x0008, next_pos: ep + 1 }
                } else if e == 0x66 {
                    SpecTplStep::Unit { u: 0x000C, next_pos: ep + 1 }
                } else if e == 0x76 {
                    SpecTplStep::Unit { u: 0x000B, next_pos: ep + 1 }
                } else if e == 0x5C {
                    SpecTplStep::Unit { u: 0x005C, next_pos: ep + 1 }
                } else if e == 0x27 {
                    SpecTplStep::Unit { u: 0x0027, next_pos: ep + 1 }
                } else if e == 0x22 {
                    SpecTplStep::Unit { u: 0x0022, next_pos: ep + 1 }
                } else if e == 0x30 {
                    if ep + 1 < input.len() && spec_is_ascii_digit(input[(ep + 1) as int]) {
                        SpecTplStep::SkipOrInvalid { mark_invalid: true, next_pos: ep + 1 }
                    } else {
                        SpecTplStep::Unit { u: 0x0000, next_pos: ep + 1 }
                    }
                } else if 0x31 <= e && e <= 0x39 {
                    SpecTplStep::SkipOrInvalid { mark_invalid: true, next_pos: ep + 1 }
                } else if e == 0x78 {
                    if ep + 2 < input.len()
                        && spec_is_hex_digit(input[(ep + 1) as int])
                        && spec_is_hex_digit(input[(ep + 2) as int])
                    {
                        let v = (spec_hex_val(input[(ep + 1) as int]) * 16
                            + spec_hex_val(input[(ep + 2) as int])) as u16;
                        SpecTplStep::Unit { u: v, next_pos: ep + 3 }
                    } else {
                        SpecTplStep::SkipOrInvalid { mark_invalid: true, next_pos: ep + 1 }
                    }
                } else if e == 0x75 {
                    match spec_decode_unicode_escape_after_u(input, ep + 1) {
                        Ok((cp, next_pos)) => SpecTplStep::CodePoint { cp, next_pos },
                        Err(_) => SpecTplStep::SkipOrInvalid { mark_invalid: true, next_pos: ep + 1 },
                    }
                } else {
                    match spec_decode_utf8_scalar(input, ep) {
                        Some((cp, ulen)) => SpecTplStep::CodePoint { cp, next_pos: ep + (ulen as nat) },
                        None => SpecTplStep::Err(SyntaxDiagnostic {
                            kind: DiagnosticKind::InvalidUtf8Encoding,
                            span: spec_span(ep, ep + 1),
                        }),
                    }
                }
            }
        }
    } else {
        match spec_decode_utf8_scalar(input, pos) {
            Some((cp, ulen)) => SpecTplStep::CodePoint { cp, next_pos: pos + (ulen as nat) },
            None => SpecTplStep::Err(SyntaxDiagnostic {
                kind: DiagnosticKind::InvalidUtf8Encoding,
                span: spec_span(pos, pos + 1),
            }),
        }
    }
}

pub proof fn lemma_template_step_bounds(input: Seq<u8>, start: nat, pos: nat)
    requires
        pos < input.len(),
    ensures
        match spec_template_step(input, start, pos) {
            SpecTplStep::ClosingBacktick(next_pos) => next_pos == pos + 1 && next_pos <= input.len(),
            SpecTplStep::Substitution(next_pos) => next_pos == pos + 2 && next_pos <= input.len(),
            SpecTplStep::SkipOrInvalid { next_pos, .. } => pos < next_pos && next_pos <= input.len(),
            SpecTplStep::Unit { next_pos, .. } => pos < next_pos && next_pos <= input.len(),
            SpecTplStep::CodePoint { cp, next_pos } => cp <= 0x10FFFF && pos < next_pos && next_pos <= input.len(),
            SpecTplStep::Err(_) => true,
        },
{
    reveal(spec_template_step);
    let b = input[pos as int];
    if b == 0x5C {
        let ep = pos + 1;
        if ep < input.len() && spec_utf8_line_terminator_len(input, ep) == 0 && input[ep as int] == 0x75 {
            if ep + 1 < input.len() && input[(ep + 1) as int] == 0x7B {
                lemma_parse_braced_hex_bounds(input, ep + 2, 0, false);
            }
        }
    }
}

#[verifier::rlimit(40)]
pub fn template_step(input: &[u8], start: usize, pos: usize) -> (r: TplStep)
    requires
        start < pos && pos < input@.len(),
    ensures
        match r {
            TplStep::ClosingBacktick(next_pos) => {
                spec_template_step(input@, start as nat, pos as nat)
                    == SpecTplStep::ClosingBacktick(next_pos as nat)
                    && next_pos == pos + 1 && next_pos <= input@.len()
            },
            TplStep::Substitution(next_pos) => {
                spec_template_step(input@, start as nat, pos as nat)
                    == SpecTplStep::Substitution(next_pos as nat)
                    && next_pos == pos + 2 && next_pos <= input@.len()
            },
            TplStep::SkipOrInvalid { mark_invalid, next_pos } => {
                spec_template_step(input@, start as nat, pos as nat)
                    == SpecTplStep::SkipOrInvalid { mark_invalid, next_pos: next_pos as nat }
                    && pos < next_pos && next_pos <= input@.len()
            },
            TplStep::Unit { u, next_pos } => {
                spec_template_step(input@, start as nat, pos as nat)
                    == SpecTplStep::Unit { u, next_pos: next_pos as nat }
                    && pos < next_pos && next_pos <= input@.len()
            },
            TplStep::CodePoint { cp, next_pos } => {
                spec_template_step(input@, start as nat, pos as nat)
                    == SpecTplStep::CodePoint { cp, next_pos: next_pos as nat }
                    && cp <= 0x10FFFF && pos < next_pos && next_pos <= input@.len()
            },
            TplStep::Err(e) => {
                spec_template_step(input@, start as nat, pos as nat) == SpecTplStep::Err(e)
            },
        },
{
    proof {
        reveal(spec_template_step);
    }
    let n = input.len();
    let rem = n - pos;
    let b = input[pos];
    if b == 0x60 {
        TplStep::ClosingBacktick(pos + 1)
    } else if b == 0x24 && rem >= 2 && input[pos + 1] == 0x7B {
        TplStep::Substitution(pos + 2)
    } else if b == 0x0D {
        let step: usize = if rem >= 2 && input[pos + 1] == 0x0A { 2 } else { 1 };
        TplStep::Unit { u: 0x000A, next_pos: pos + step }
    } else if b == 0x5C {
        if rem < 2 {
            TplStep::Err(SyntaxDiagnostic {
                kind: DiagnosticKind::UnterminatedTemplateLiteral,
                span: Span { start, end: n },
            })
        } else {
            let ep = pos + 1;
            let lt_len = utf8_line_terminator_len(input, ep);
            if lt_len > 0 {
                TplStep::SkipOrInvalid { mark_invalid: false, next_pos: ep + lt_len }
            } else {
                let rem_ep = n - ep;
                let e = input[ep];
                if e == 0x6E {
                    TplStep::Unit { u: 0x000A, next_pos: ep + 1 }
                } else if e == 0x72 {
                    TplStep::Unit { u: 0x000D, next_pos: ep + 1 }
                } else if e == 0x74 {
                    TplStep::Unit { u: 0x0009, next_pos: ep + 1 }
                } else if e == 0x62 {
                    TplStep::Unit { u: 0x0008, next_pos: ep + 1 }
                } else if e == 0x66 {
                    TplStep::Unit { u: 0x000C, next_pos: ep + 1 }
                } else if e == 0x76 {
                    TplStep::Unit { u: 0x000B, next_pos: ep + 1 }
                } else if e == 0x5C {
                    TplStep::Unit { u: 0x005C, next_pos: ep + 1 }
                } else if e == 0x27 {
                    TplStep::Unit { u: 0x0027, next_pos: ep + 1 }
                } else if e == 0x22 {
                    TplStep::Unit { u: 0x0022, next_pos: ep + 1 }
                } else if e == 0x30 {
                    if rem_ep >= 2 && is_ascii_digit(input[ep + 1]) {
                        TplStep::SkipOrInvalid { mark_invalid: true, next_pos: ep + 1 }
                    } else {
                        TplStep::Unit { u: 0x0000, next_pos: ep + 1 }
                    }
                } else if e >= 0x31 && e <= 0x39 {
                    TplStep::SkipOrInvalid { mark_invalid: true, next_pos: ep + 1 }
                } else if e == 0x78 {
                    if rem_ep >= 3 && is_hex_digit(input[ep + 1]) && is_hex_digit(input[ep + 2]) {
                        let v = (hex_val(input[ep + 1]) * 16 + hex_val(input[ep + 2])) as u16;
                        TplStep::Unit { u: v, next_pos: ep + 3 }
                    } else {
                        TplStep::SkipOrInvalid { mark_invalid: true, next_pos: ep + 1 }
                    }
                } else if e == 0x75 {
                    match decode_unicode_escape_after_u(input, ep + 1) {
                        Ok((cp, next_pos)) => TplStep::CodePoint { cp, next_pos },
                        Err(_) => TplStep::SkipOrInvalid { mark_invalid: true, next_pos: ep + 1 },
                    }
                } else {
                    match decode_utf8_scalar(input, ep) {
                        Some((cp, ulen)) => TplStep::CodePoint { cp, next_pos: ep + ulen },
                        None => TplStep::Err(SyntaxDiagnostic {
                            kind: DiagnosticKind::InvalidUtf8Encoding,
                            span: Span { start: ep, end: ep + 1 },
                        }),
                    }
                }
            }
        }
    } else {
        match decode_utf8_scalar(input, pos) {
            Some((cp, ulen)) => TplStep::CodePoint { cp, next_pos: pos + ulen },
            None => TplStep::Err(SyntaxDiagnostic {
                kind: DiagnosticKind::InvalidUtf8Encoding,
                span: Span { start: pos, end: pos + 1 },
            }),
        }
    }
}

pub open spec fn spec_lex_template_loop(
    input: Seq<u8>,
    start: nat,
    pos: nat,
    units: Seq<u16>,
    has_inv: bool,
    saw_lt: bool,
) -> SpecStepOutcome
    decreases input.len() - pos,
{
    if pos >= input.len() {
        SpecStepOutcome::SyntaxError(SyntaxDiagnostic {
            kind: DiagnosticKind::UnterminatedTemplateLiteral,
            span: spec_span(start, input.len()),
        })
    } else {
        match spec_template_step(input, start, pos) {
            SpecTplStep::ClosingBacktick(end_pos) => SpecStepOutcome::Token {
                tok: SpecToken {
                    kind: SpecTokenKind::NoSubTemplate { units, has_invalid_escape: has_inv },
                    span: spec_span(start, end_pos),
                    preceded_by_line_terminator: saw_lt,
                },
                next_pos: end_pos,
            },
            SpecTplStep::Substitution(sub_end) => SpecStepOutcome::Unsupported(UnsupportedSyntax {
                kind: UnsupportedSyntaxKind::TemplateSubstitution,
                span: spec_span(start, sub_end),
            }),
            SpecTplStep::SkipOrInvalid { mark_invalid, next_pos } => {
                if next_pos > pos && next_pos <= input.len() {
                    spec_lex_template_loop(input, start, next_pos, units, has_inv || mark_invalid, saw_lt)
                } else {
                    SpecStepOutcome::SyntaxError(SyntaxDiagnostic {
                        kind: DiagnosticKind::UnterminatedTemplateLiteral,
                        span: spec_span(start, input.len()),
                    })
                }
            },
            SpecTplStep::Unit { u, next_pos } => {
                if next_pos > pos && next_pos <= input.len() {
                    spec_lex_template_loop(input, start, next_pos, units.push(u), has_inv, saw_lt)
                } else {
                    SpecStepOutcome::SyntaxError(SyntaxDiagnostic {
                        kind: DiagnosticKind::UnterminatedTemplateLiteral,
                        span: spec_span(start, input.len()),
                    })
                }
            },
            SpecTplStep::CodePoint { cp, next_pos } => {
                if next_pos > pos && next_pos <= input.len() {
                    spec_lex_template_loop(
                        input,
                        start,
                        next_pos,
                        spec_append_utf16_cp(units, cp),
                        has_inv,
                        saw_lt,
                    )
                } else {
                    SpecStepOutcome::SyntaxError(SyntaxDiagnostic {
                        kind: DiagnosticKind::UnterminatedTemplateLiteral,
                        span: spec_span(start, input.len()),
                    })
                }
            },
            SpecTplStep::Err(e) => SpecStepOutcome::SyntaxError(e),
        }
    }
}

pub proof fn lemma_lex_template_bounds(
    input: Seq<u8>,
    start: nat,
    pos: nat,
    units: Seq<u16>,
    has_inv: bool,
    saw_lt: bool,
)
    requires
        start < pos && pos <= input.len(),
    ensures
        match spec_lex_template_loop(input, start, pos, units, has_inv, saw_lt) {
            SpecStepOutcome::Token { tok, next_pos } => {
                start < next_pos && next_pos <= input.len() && tok.span == spec_span(start, next_pos)
            },
            _ => true,
        },
    decreases input.len() - pos,
{
    if pos < input.len() {
        lemma_template_step_bounds(input, start, pos);
        match spec_template_step(input, start, pos) {
            SpecTplStep::SkipOrInvalid { mark_invalid, next_pos } => {
                lemma_lex_template_bounds(input, start, next_pos, units, has_inv || mark_invalid, saw_lt);
            },
            SpecTplStep::Unit { u, next_pos } => {
                lemma_lex_template_bounds(input, start, next_pos, units.push(u), has_inv, saw_lt);
            },
            SpecTplStep::CodePoint { cp, next_pos } => {
                lemma_lex_template_bounds(
                    input,
                    start,
                    next_pos,
                    spec_append_utf16_cp(units, cp),
                    has_inv,
                    saw_lt,
                );
            },
            _ => {},
        }
    }
}

pub open spec fn spec_lex_template(input: Seq<u8>, start: nat, saw_lt: bool) -> SpecStepOutcome {
    spec_lex_template_loop(input, start, start + 1, Seq::<u16>::empty(), false, saw_lt)
}

pub fn lex_template(input: &[u8], start: usize, saw_lt: bool) -> (r: StepOutcome)
    requires
        start < input@.len(),
        input@[start as int] == 0x60,
    ensures
        r@ == spec_lex_template(input@, start as nat, saw_lt),
        match r@ {
            SpecStepOutcome::Token { tok, next_pos } => {
                start < next_pos && next_pos <= input@.len() && tok.span == spec_span(start as nat, next_pos)
            },
            _ => true,
        },
{
    let n = input.len();
    let mut pos = start + 1;
    let mut units: Vec<u16> = Vec::new();
    let mut has_inv = false;
    proof {
        assert(units@ =~= Seq::<u16>::empty());
    }
    while pos < n
        invariant
            start < pos && pos <= n,
            n == input@.len(),
            spec_lex_template_loop(input@, start as nat, pos as nat, units@, has_inv, saw_lt)
                == spec_lex_template_loop(input@, start as nat, (start + 1) as nat, Seq::<u16>::empty(), false, saw_lt),
        decreases n - pos,
    {
        match template_step(input, start, pos) {
            TplStep::ClosingBacktick(end_pos) => {
                return StepOutcome::Token {
                    tok: Token {
                        kind: TokenKind::NoSubTemplate { units, has_invalid_escape: has_inv },
                        span: Span { start, end: end_pos },
                        preceded_by_line_terminator: saw_lt,
                    },
                    next_pos: end_pos,
                };
            },
            TplStep::Substitution(sub_end) => {
                return StepOutcome::Unsupported(UnsupportedSyntax {
                    kind: UnsupportedSyntaxKind::TemplateSubstitution,
                    span: Span { start, end: sub_end },
                });
            },
            TplStep::SkipOrInvalid { mark_invalid, next_pos } => {
                has_inv = has_inv || mark_invalid;
                pos = next_pos;
            },
            TplStep::Unit { u, next_pos } => {
                units.push(u);
                pos = next_pos;
            },
            TplStep::CodePoint { cp, next_pos } => {
                append_utf16_cp(&mut units, cp);
                pos = next_pos;
            },
            TplStep::Err(e) => {
                return StepOutcome::SyntaxError(e);
            },
        }
    }
    StepOutcome::SyntaxError(SyntaxDiagnostic {
        kind: DiagnosticKind::UnterminatedTemplateLiteral,
        span: Span { start, end: n },
    })
}

// ---------------------------------------------------------------------------------------
// Punctuator Longest-Match Scanner (§12.8.1)
// ---------------------------------------------------------------------------------------

pub open spec fn spec_lex_punctuator(input: Seq<u8>, pos: nat) -> Option<(Punctuator, usize)> {
    let n = input.len();
    let b0 = input[pos as int];
    let b1: u8 = if pos + 1 < n { input[(pos + 1) as int] } else { 0 };
    let b2: u8 = if pos + 2 < n { input[(pos + 2) as int] } else { 0 };
    let b3: u8 = if pos + 3 < n { input[(pos + 3) as int] } else { 0 };

    if b0 == 0x7B {
        Some((Punctuator::LBrace, 1))
    } else if b0 == 0x7D {
        Some((Punctuator::RBrace, 1))
    } else if b0 == 0x28 {
        Some((Punctuator::LParen, 1))
    } else if b0 == 0x29 {
        Some((Punctuator::RParen, 1))
    } else if b0 == 0x5B {
        Some((Punctuator::LBracket, 1))
    } else if b0 == 0x5D {
        Some((Punctuator::RBracket, 1))
    } else if b0 == 0x3B {
        Some((Punctuator::Semicolon, 1))
    } else if b0 == 0x2C {
        Some((Punctuator::Comma, 1))
    } else if b0 == 0x7E {
        Some((Punctuator::Tilde, 1))
    } else if b0 == 0x3A {
        Some((Punctuator::Colon, 1))
    } else if b0 == 0x2E {
        if pos + 2 < n && b1 == 0x2E && b2 == 0x2E {
            Some((Punctuator::Ellipsis, 3))
        } else {
            Some((Punctuator::Dot, 1))
        }
    } else if b0 == 0x3D {
        if pos + 2 < n && b1 == 0x3D && b2 == 0x3D {
            Some((Punctuator::EqEqEq, 3))
        } else if pos + 1 < n && b1 == 0x3D {
            Some((Punctuator::EqEq, 2))
        } else if pos + 1 < n && b1 == 0x3E {
            Some((Punctuator::Arrow, 2))
        } else {
            Some((Punctuator::Eq, 1))
        }
    } else if b0 == 0x21 {
        if pos + 2 < n && b1 == 0x3D && b2 == 0x3D {
            Some((Punctuator::NeEq, 3))
        } else if pos + 1 < n && b1 == 0x3D {
            Some((Punctuator::Ne, 2))
        } else {
            Some((Punctuator::Bang, 1))
        }
    } else if b0 == 0x3C {
        if pos + 2 < n && b1 == 0x3C && b2 == 0x3D {
            Some((Punctuator::ShlEq, 3))
        } else if pos + 1 < n && b1 == 0x3C {
            Some((Punctuator::Shl, 2))
        } else if pos + 1 < n && b1 == 0x3D {
            Some((Punctuator::Le, 2))
        } else {
            Some((Punctuator::Lt, 1))
        }
    } else if b0 == 0x3E {
        if pos + 3 < n && b1 == 0x3E && b2 == 0x3E && b3 == 0x3D {
            Some((Punctuator::UShrEq, 4))
        } else if pos + 2 < n && b1 == 0x3E && b2 == 0x3E {
            Some((Punctuator::UShr, 3))
        } else if pos + 2 < n && b1 == 0x3E && b2 == 0x3D {
            Some((Punctuator::ShrEq, 3))
        } else if pos + 1 < n && b1 == 0x3E {
            Some((Punctuator::Shr, 2))
        } else if pos + 1 < n && b1 == 0x3D {
            Some((Punctuator::Ge, 2))
        } else {
            Some((Punctuator::Gt, 1))
        }
    } else if b0 == 0x2B {
        if pos + 1 < n && b1 == 0x2B {
            Some((Punctuator::PlusPlus, 2))
        } else if pos + 1 < n && b1 == 0x3D {
            Some((Punctuator::PlusEq, 2))
        } else {
            Some((Punctuator::Plus, 1))
        }
    } else if b0 == 0x2D {
        if pos + 1 < n && b1 == 0x2D {
            Some((Punctuator::MinusMinus, 2))
        } else if pos + 1 < n && b1 == 0x3D {
            Some((Punctuator::MinusEq, 2))
        } else {
            Some((Punctuator::Minus, 1))
        }
    } else if b0 == 0x2A {
        if pos + 2 < n && b1 == 0x2A && b2 == 0x3D {
            Some((Punctuator::StarStarEq, 3))
        } else if pos + 1 < n && b1 == 0x2A {
            Some((Punctuator::StarStar, 2))
        } else if pos + 1 < n && b1 == 0x3D {
            Some((Punctuator::StarEq, 2))
        } else {
            Some((Punctuator::Star, 1))
        }
    } else if b0 == 0x2F {
        if pos + 1 < n && b1 == 0x3D {
            Some((Punctuator::SlashEq, 2))
        } else {
            Some((Punctuator::Slash, 1))
        }
    } else if b0 == 0x25 {
        if pos + 1 < n && b1 == 0x3D {
            Some((Punctuator::PercentEq, 2))
        } else {
            Some((Punctuator::Percent, 1))
        }
    } else if b0 == 0x26 {
        if pos + 2 < n && b1 == 0x26 && b2 == 0x3D {
            Some((Punctuator::AmpAmpEq, 3))
        } else if pos + 1 < n && b1 == 0x26 {
            Some((Punctuator::AmpAmp, 2))
        } else if pos + 1 < n && b1 == 0x3D {
            Some((Punctuator::AmpEq, 2))
        } else {
            Some((Punctuator::Amp, 1))
        }
    } else if b0 == 0x7C {
        if pos + 2 < n && b1 == 0x7C && b2 == 0x3D {
            Some((Punctuator::PipePipeEq, 3))
        } else if pos + 1 < n && b1 == 0x7C {
            Some((Punctuator::PipePipe, 2))
        } else if pos + 1 < n && b1 == 0x3D {
            Some((Punctuator::PipeEq, 2))
        } else {
            Some((Punctuator::Pipe, 1))
        }
    } else if b0 == 0x5E {
        if pos + 1 < n && b1 == 0x3D {
            Some((Punctuator::CaretEq, 2))
        } else {
            Some((Punctuator::Caret, 1))
        }
    } else if b0 == 0x3F {
        if pos + 2 < n && b1 == 0x3F && b2 == 0x3D {
            Some((Punctuator::QuestionQuestionEq, 3))
        } else if pos + 1 < n && b1 == 0x3F {
            Some((Punctuator::QuestionQuestion, 2))
        } else if pos + 1 < n && b1 == 0x2E && !(pos + 2 < n && spec_is_ascii_digit(b2)) {
            Some((Punctuator::OptionalChain, 2))
        } else {
            Some((Punctuator::Question, 1))
        }
    } else {
        None
    }
}

pub fn lex_punctuator(input: &[u8], pos: usize) -> (r: Option<(Punctuator, usize)>)
    requires
        pos < input@.len(),
    ensures
        r == spec_lex_punctuator(input@, pos as nat),
        match r {
            Some((_, plen)) => 1 <= plen && plen <= 4 && pos + plen <= input@.len(),
            None => true,
        },
{
    let n = input.len();
    let rem = n - pos;
    let b0 = input[pos];
    let b1: u8 = if rem >= 2 { input[pos + 1] } else { 0 };
    let b2: u8 = if rem >= 3 { input[pos + 2] } else { 0 };
    let b3: u8 = if rem >= 4 { input[pos + 3] } else { 0 };

    if b0 == 0x7B {
        Some((Punctuator::LBrace, 1))
    } else if b0 == 0x7D {
        Some((Punctuator::RBrace, 1))
    } else if b0 == 0x28 {
        Some((Punctuator::LParen, 1))
    } else if b0 == 0x29 {
        Some((Punctuator::RParen, 1))
    } else if b0 == 0x5B {
        Some((Punctuator::LBracket, 1))
    } else if b0 == 0x5D {
        Some((Punctuator::RBracket, 1))
    } else if b0 == 0x3B {
        Some((Punctuator::Semicolon, 1))
    } else if b0 == 0x2C {
        Some((Punctuator::Comma, 1))
    } else if b0 == 0x7E {
        Some((Punctuator::Tilde, 1))
    } else if b0 == 0x3A {
        Some((Punctuator::Colon, 1))
    } else if b0 == 0x2E {
        if rem >= 3 && b1 == 0x2E && b2 == 0x2E {
            Some((Punctuator::Ellipsis, 3))
        } else {
            Some((Punctuator::Dot, 1))
        }
    } else if b0 == 0x3D {
        if rem >= 3 && b1 == 0x3D && b2 == 0x3D {
            Some((Punctuator::EqEqEq, 3))
        } else if rem >= 2 && b1 == 0x3D {
            Some((Punctuator::EqEq, 2))
        } else if rem >= 2 && b1 == 0x3E {
            Some((Punctuator::Arrow, 2))
        } else {
            Some((Punctuator::Eq, 1))
        }
    } else if b0 == 0x21 {
        if rem >= 3 && b1 == 0x3D && b2 == 0x3D {
            Some((Punctuator::NeEq, 3))
        } else if rem >= 2 && b1 == 0x3D {
            Some((Punctuator::Ne, 2))
        } else {
            Some((Punctuator::Bang, 1))
        }
    } else if b0 == 0x3C {
        if rem >= 3 && b1 == 0x3C && b2 == 0x3D {
            Some((Punctuator::ShlEq, 3))
        } else if rem >= 2 && b1 == 0x3C {
            Some((Punctuator::Shl, 2))
        } else if rem >= 2 && b1 == 0x3D {
            Some((Punctuator::Le, 2))
        } else {
            Some((Punctuator::Lt, 1))
        }
    } else if b0 == 0x3E {
        if rem >= 4 && b1 == 0x3E && b2 == 0x3E && b3 == 0x3D {
            Some((Punctuator::UShrEq, 4))
        } else if rem >= 3 && b1 == 0x3E && b2 == 0x3E {
            Some((Punctuator::UShr, 3))
        } else if rem >= 3 && b1 == 0x3E && b2 == 0x3D {
            Some((Punctuator::ShrEq, 3))
        } else if rem >= 2 && b1 == 0x3E {
            Some((Punctuator::Shr, 2))
        } else if rem >= 2 && b1 == 0x3D {
            Some((Punctuator::Ge, 2))
        } else {
            Some((Punctuator::Gt, 1))
        }
    } else if b0 == 0x2B {
        if rem >= 2 && b1 == 0x2B {
            Some((Punctuator::PlusPlus, 2))
        } else if rem >= 2 && b1 == 0x3D {
            Some((Punctuator::PlusEq, 2))
        } else {
            Some((Punctuator::Plus, 1))
        }
    } else if b0 == 0x2D {
        if rem >= 2 && b1 == 0x2D {
            Some((Punctuator::MinusMinus, 2))
        } else if rem >= 2 && b1 == 0x3D {
            Some((Punctuator::MinusEq, 2))
        } else {
            Some((Punctuator::Minus, 1))
        }
    } else if b0 == 0x2A {
        if rem >= 3 && b1 == 0x2A && b2 == 0x3D {
            Some((Punctuator::StarStarEq, 3))
        } else if rem >= 2 && b1 == 0x2A {
            Some((Punctuator::StarStar, 2))
        } else if rem >= 2 && b1 == 0x3D {
            Some((Punctuator::StarEq, 2))
        } else {
            Some((Punctuator::Star, 1))
        }
    } else if b0 == 0x2F {
        if rem >= 2 && b1 == 0x3D {
            Some((Punctuator::SlashEq, 2))
        } else {
            Some((Punctuator::Slash, 1))
        }
    } else if b0 == 0x25 {
        if rem >= 2 && b1 == 0x3D {
            Some((Punctuator::PercentEq, 2))
        } else {
            Some((Punctuator::Percent, 1))
        }
    } else if b0 == 0x26 {
        if rem >= 3 && b1 == 0x26 && b2 == 0x3D {
            Some((Punctuator::AmpAmpEq, 3))
        } else if rem >= 2 && b1 == 0x26 {
            Some((Punctuator::AmpAmp, 2))
        } else if rem >= 2 && b1 == 0x3D {
            Some((Punctuator::AmpEq, 2))
        } else {
            Some((Punctuator::Amp, 1))
        }
    } else if b0 == 0x7C {
        if rem >= 3 && b1 == 0x7C && b2 == 0x3D {
            Some((Punctuator::PipePipeEq, 3))
        } else if rem >= 2 && b1 == 0x7C {
            Some((Punctuator::PipePipe, 2))
        } else if rem >= 2 && b1 == 0x3D {
            Some((Punctuator::PipeEq, 2))
        } else {
            Some((Punctuator::Pipe, 1))
        }
    } else if b0 == 0x5E {
        if rem >= 2 && b1 == 0x3D {
            Some((Punctuator::CaretEq, 2))
        } else {
            Some((Punctuator::Caret, 1))
        }
    } else if b0 == 0x3F {
        if rem >= 3 && b1 == 0x3F && b2 == 0x3D {
            Some((Punctuator::QuestionQuestionEq, 3))
        } else if rem >= 2 && b1 == 0x3F {
            Some((Punctuator::QuestionQuestion, 2))
        } else if rem >= 2 && b1 == 0x2E && !(rem >= 3 && is_ascii_digit(b2)) {
            Some((Punctuator::OptionalChain, 2))
        } else {
            Some((Punctuator::Question, 1))
        }
    } else {
        None
    }
}

// ---------------------------------------------------------------------------------------
// Single-Token Dispatcher & Top-Level `tokenize` Loop (`decreases input.len() - pos`)
// ---------------------------------------------------------------------------------------

pub open spec fn spec_lex_non_trivia_token(
    input: Seq<u8>,
    pos: nat,
    saw_lt: bool,
) -> SpecStepOutcome {
    let b = input[pos as int];
    if spec_is_ascii_ident_start(b) {
        match spec_lex_ident_continue(input, pos, pos + 1, seq![b], false) {
            Ok((name, esc, next_pos)) => SpecStepOutcome::Token {
                tok: spec_finish_ident_token(name, esc, spec_span(pos, next_pos), saw_lt),
                next_pos,
            },
            Err(e) => SpecStepOutcome::SyntaxError(e),
        }
    } else if b == 0x5C {
        if pos + 1 < input.len() && input[(pos + 1) as int] == 0x75 {
            match spec_decode_unicode_escape_after_u(input, pos + 2) {
                Ok((cp, after_esc)) => {
                    if spec_is_ident_start_cp(cp) {
                        match spec_lex_ident_continue(
                            input,
                            pos,
                            after_esc,
                            spec_append_utf8_cp(Seq::<u8>::empty(), cp),
                            true,
                        ) {
                            Ok((name, esc, next_pos)) => SpecStepOutcome::Token {
                                tok: spec_finish_ident_token(
                                    name,
                                    esc,
                                    spec_span(pos, next_pos),
                                    saw_lt,
                                ),
                                next_pos,
                            },
                            Err(e) => SpecStepOutcome::SyntaxError(e),
                        }
                    } else {
                        SpecStepOutcome::SyntaxError(SyntaxDiagnostic {
                            kind: DiagnosticKind::InvalidUnicodeEscape,
                            span: spec_span(pos, after_esc),
                        })
                    }
                },
                Err(kind) => SpecStepOutcome::SyntaxError(SyntaxDiagnostic {
                    kind,
                    span: spec_span(pos, input.len()),
                }),
            }
        } else {
            SpecStepOutcome::SyntaxError(SyntaxDiagnostic {
                kind: DiagnosticKind::InvalidUnicodeEscape,
                span: spec_span(pos, pos + 1),
            })
        }
    } else if spec_is_ascii_digit(b)
        || (b == 0x2E && pos + 1 < input.len() && spec_is_ascii_digit(input[(pos + 1) as int]))
    {
        spec_lex_number(input, pos, saw_lt)
    } else if b == 0x22 || b == 0x27 {
        spec_lex_string(input, pos, saw_lt)
    } else if b == 0x60 {
        spec_lex_template(input, pos, saw_lt)
    } else if b == 0x23 {
        if pos + 1 < input.len() && spec_is_ascii_ident_start(input[(pos + 1) as int]) {
            SpecStepOutcome::Unsupported(UnsupportedSyntax {
                kind: UnsupportedSyntaxKind::PrivateIdentifier,
                span: spec_span(pos, pos + 2),
            })
        } else {
            SpecStepOutcome::SyntaxError(SyntaxDiagnostic {
                kind: DiagnosticKind::UnexpectedCharacter,
                span: spec_span(pos, pos + 1),
            })
        }
    } else {
        match spec_lex_punctuator(input, pos) {
            Some((punct, plen)) => {
                let next_pos = pos + (plen as nat);
                SpecStepOutcome::Token {
                    tok: SpecToken {
                        kind: SpecTokenKind::Punct(punct),
                        span: spec_span(pos, next_pos),
                        preceded_by_line_terminator: saw_lt,
                    },
                    next_pos,
                }
            },
            None => {
                if b >= 0x80 {
                    match spec_decode_utf8_scalar(input, pos) {
                        Some((cp, ulen)) => {
                            let after_cp = pos + (ulen as nat);
                            if spec_is_ident_start_cp(cp) {
                                match spec_lex_ident_continue(
                                    input,
                                    pos,
                                    after_cp,
                                    spec_append_utf8_cp(Seq::<u8>::empty(), cp),
                                    false,
                                ) {
                                    Ok((name, esc, next_pos)) => SpecStepOutcome::Token {
                                        tok: spec_finish_ident_token(
                                            name,
                                            esc,
                                            spec_span(pos, next_pos),
                                            saw_lt,
                                        ),
                                        next_pos,
                                    },
                                    Err(e) => SpecStepOutcome::SyntaxError(e),
                                }
                            } else {
                                SpecStepOutcome::SyntaxError(SyntaxDiagnostic {
                                    kind: DiagnosticKind::UnexpectedCharacter,
                                    span: spec_span(pos, after_cp),
                                })
                            }
                        },
                        None => SpecStepOutcome::SyntaxError(SyntaxDiagnostic {
                            kind: DiagnosticKind::InvalidUtf8Encoding,
                            span: spec_span(pos, pos + 1),
                        }),
                    }
                } else {
                    SpecStepOutcome::SyntaxError(SyntaxDiagnostic {
                        kind: DiagnosticKind::UnexpectedCharacter,
                        span: spec_span(pos, pos + 1),
                    })
                }
            },
        }
    }
}

/// Core cursor-progress theorem: every successful token step strictly advances `pos < next_pos <= input.len()`.
pub proof fn lemma_lex_token_step_advances(input: Seq<u8>, pos: nat, saw_lt: bool)
    requires
        pos < input.len(),
    ensures
        match spec_lex_non_trivia_token(input, pos, saw_lt) {
            SpecStepOutcome::Token { tok, next_pos } => {
                pos < next_pos && next_pos <= input.len() && tok.span == spec_span(pos, next_pos)
            },
            _ => true,
        },
{
    let b = input[pos as int];
    if spec_is_ascii_ident_start(b) {
        lemma_lex_ident_continue_bounds(input, pos, pos + 1, seq![b], false);
    } else if b == 0x5C {
        if pos + 1 < input.len() && input[(pos + 1) as int] == 0x75 {
            if pos + 2 < input.len() && input[(pos + 2) as int] == 0x7B {
                lemma_parse_braced_hex_bounds(input, pos + 3, 0, false);
            }
            if let Ok((cp, after_esc)) = spec_decode_unicode_escape_after_u(input, pos + 2) {
                if spec_is_ident_start_cp(cp) {
                    lemma_lex_ident_continue_bounds(
                        input,
                        pos,
                        after_esc,
                        spec_append_utf8_cp(Seq::<u8>::empty(), cp),
                        true,
                    );
                }
            }
        }
    } else if spec_is_ascii_digit(b)
        || (b == 0x2E && pos + 1 < input.len() && spec_is_ascii_digit(input[(pos + 1) as int]))
    {
        lemma_lex_number_bounds(input, pos, saw_lt);
    } else if b == 0x22 || b == 0x27 {
        lemma_lex_string_bounds(input, b, pos, pos + 1, Seq::<u16>::empty(), false);
    } else if b == 0x60 {
        lemma_lex_template_bounds(input, pos, pos + 1, Seq::<u16>::empty(), false, saw_lt);
    } else if b != 0x23 && spec_lex_punctuator(input, pos) is None && b >= 0x80 {
        if let Some((cp, ulen)) = spec_decode_utf8_scalar(input, pos) {
            if spec_is_ident_start_cp(cp) {
                lemma_lex_ident_continue_bounds(
                    input,
                    pos,
                    pos + (ulen as nat),
                    spec_append_utf8_cp(Seq::<u8>::empty(), cp),
                    false,
                );
            }
        }
    }
}

pub fn lex_non_trivia_token(input: &[u8], pos: usize, saw_lt: bool) -> (r: StepOutcome)
    requires
        pos < input@.len(),
    ensures
        r@ == spec_lex_non_trivia_token(input@, pos as nat, saw_lt),
        match r@ {
            SpecStepOutcome::Token { tok, next_pos } => {
                pos < next_pos && next_pos <= input@.len() && tok.span == spec_span(pos as nat, next_pos)
            },
            _ => true,
        },
{
    let n = input.len();
    let rem = n - pos;
    let b = input[pos];
    if is_ascii_ident_start(b) {
        let mut init: Vec<u8> = Vec::new();
        init.push(b);
        proof {
            assert(init@ =~= seq![b]);
        }
        match lex_ident_continue(input, pos, pos + 1, init, false) {
            Ok((name, esc, next_pos)) => StepOutcome::Token {
                tok: finish_ident_token(name, esc, Span { start: pos, end: next_pos }, saw_lt),
                next_pos,
            },
            Err(e) => StepOutcome::SyntaxError(e),
        }
    } else if b == 0x5C {
        if rem >= 2 && input[pos + 1] == 0x75 {
            match decode_unicode_escape_after_u(input, pos + 2) {
                Ok((cp, after_esc)) => {
                    if is_ident_start_cp(cp) {
                        let mut init: Vec<u8> = Vec::new();
                        proof {
                            assert(init@ =~= Seq::<u8>::empty());
                        }
                        append_utf8_cp(&mut init, cp);
                        match lex_ident_continue(input, pos, after_esc, init, true) {
                            Ok((name, esc, next_pos)) => StepOutcome::Token {
                                tok: finish_ident_token(
                                    name,
                                    esc,
                                    Span { start: pos, end: next_pos },
                                    saw_lt,
                                ),
                                next_pos,
                            },
                            Err(e) => StepOutcome::SyntaxError(e),
                        }
                    } else {
                        StepOutcome::SyntaxError(SyntaxDiagnostic {
                            kind: DiagnosticKind::InvalidUnicodeEscape,
                            span: Span { start: pos, end: after_esc },
                        })
                    }
                },
                Err(kind) => StepOutcome::SyntaxError(SyntaxDiagnostic {
                    kind,
                    span: Span { start: pos, end: n },
                }),
            }
        } else {
            StepOutcome::SyntaxError(SyntaxDiagnostic {
                kind: DiagnosticKind::InvalidUnicodeEscape,
                span: Span { start: pos, end: pos + 1 },
            })
        }
    } else if is_ascii_digit(b) || (b == 0x2E && rem >= 2 && is_ascii_digit(input[pos + 1])) {
        lex_number(input, pos, saw_lt)
    } else if b == 0x22 || b == 0x27 {
        lex_string(input, pos, saw_lt)
    } else if b == 0x60 {
        lex_template(input, pos, saw_lt)
    } else if b == 0x23 {
        if rem >= 2 && is_ascii_ident_start(input[pos + 1]) {
            StepOutcome::Unsupported(UnsupportedSyntax {
                kind: UnsupportedSyntaxKind::PrivateIdentifier,
                span: Span { start: pos, end: pos + 2 },
            })
        } else {
            StepOutcome::SyntaxError(SyntaxDiagnostic {
                kind: DiagnosticKind::UnexpectedCharacter,
                span: Span { start: pos, end: pos + 1 },
            })
        }
    } else {
        match lex_punctuator(input, pos) {
            Some((punct, plen)) => StepOutcome::Token {
                tok: Token {
                    kind: TokenKind::Punct(punct),
                    span: Span { start: pos, end: pos + plen },
                    preceded_by_line_terminator: saw_lt,
                },
                next_pos: pos + plen,
            },
            None => {
                if b >= 0x80 {
                    match decode_utf8_scalar(input, pos) {
                        Some((cp, ulen)) => {
                            if is_ident_start_cp(cp) {
                                let mut init: Vec<u8> = Vec::new();
                                proof {
                                    assert(init@ =~= Seq::<u8>::empty());
                                }
                                append_utf8_cp(&mut init, cp);
                                match lex_ident_continue(input, pos, pos + ulen, init, false) {
                                    Ok((name, esc, next_pos)) => StepOutcome::Token {
                                        tok: finish_ident_token(
                                            name,
                                            esc,
                                            Span { start: pos, end: next_pos },
                                            saw_lt,
                                        ),
                                        next_pos,
                                    },
                                    Err(e) => StepOutcome::SyntaxError(e),
                                }
                            } else {
                                StepOutcome::SyntaxError(SyntaxDiagnostic {
                                    kind: DiagnosticKind::UnexpectedCharacter,
                                    span: Span { start: pos, end: pos + ulen },
                                })
                            }
                        },
                        None => StepOutcome::SyntaxError(SyntaxDiagnostic {
                            kind: DiagnosticKind::InvalidUtf8Encoding,
                            span: Span { start: pos, end: pos + 1 },
                        }),
                    }
                } else {
                    StepOutcome::SyntaxError(SyntaxDiagnostic {
                        kind: DiagnosticKind::UnexpectedCharacter,
                        span: Span { start: pos, end: pos + 1 },
                    })
                }
            },
        }
    }
}

pub open spec fn spec_initial_pos_after_hashbang(input: Seq<u8>) -> nat {
    if input.len() >= 2 && input[0] == 0x23 && input[1] == 0x21 {
        spec_skip_line_comment(input, 2)
    } else {
        0
    }
}

pub fn initial_pos_after_hashbang(input: &[u8]) -> (r: usize)
    ensures
        r as nat == spec_initial_pos_after_hashbang(input@),
        r <= input@.len(),
{
    if input.len() >= 2 && input[0] == 0x23 && input[1] == 0x21 {
        skip_line_comment(input, 2)
    } else {
        0
    }
}

/// Tail-recursive full tokenization spec with strict `decreases input.len() - pos`.
pub open spec fn spec_tokenize_loop(
    input: Seq<u8>,
    pos: nat,
    acc: Seq<SpecToken>,
) -> SpecLexOutcome
    decreases input.len() - pos,
{
    match spec_skip_trivia(input, pos, false) {
        Err(e) => SpecLexOutcome::SyntaxError(e),
        Ok((tpos, saw_lt)) => {
            if tpos >= input.len() || tpos < pos {
                let eof_tok = SpecToken {
                    kind: SpecTokenKind::Eof,
                    span: spec_span(input.len(), input.len()),
                    preceded_by_line_terminator: saw_lt,
                };
                SpecLexOutcome::Ok(acc.push(eof_tok))
            } else {
                match spec_lex_non_trivia_token(input, tpos, saw_lt) {
                    SpecStepOutcome::Token { tok, next_pos } => {
                        if next_pos > tpos && next_pos <= input.len() {
                            spec_tokenize_loop(input, next_pos, acc.push(tok))
                        } else {
                            SpecLexOutcome::SyntaxError(SyntaxDiagnostic {
                                kind: DiagnosticKind::UnexpectedCharacter,
                                span: spec_span(tpos, tpos),
                            })
                        }
                    },
                    SpecStepOutcome::SyntaxError(e) => SpecLexOutcome::SyntaxError(e),
                    SpecStepOutcome::Unsupported(u) => SpecLexOutcome::Unsupported(u),
                }
            }
        },
    }
}

/// Top-level ECMA-262 lexical specification on arbitrary byte sequences `Seq<u8>`.
pub open spec fn spec_tokenize(input: Seq<u8>) -> SpecLexOutcome {
    let start_pos = spec_initial_pos_after_hashbang(input);
    spec_tokenize_loop(input, start_pos, Seq::<SpecToken>::empty())
}

pub proof fn lemma_tokens_push_view(old_toks: Seq<Token>, tok: Token)
    ensures
        spec_tokens_view(old_toks.push(tok)) == spec_tokens_view(old_toks).push(tok@),
{
    assert(spec_tokens_view(old_toks.push(tok)) =~= spec_tokens_view(old_toks).push(tok@));
}

/// Verified ECMAScript tokenizer over `&[u8]`. Total and panic-free on ALL byte slices.
pub fn tokenize(input: &[u8]) -> (out: LexOutcome)
    ensures
        out@ == spec_tokenize(input@),
{
    let n = input.len();
    let start_pos = initial_pos_after_hashbang(input);
    let mut pos = start_pos;
    let mut tokens: Vec<Token> = Vec::new();
    proof {
        assert(spec_tokens_view(tokens@) =~= Seq::<SpecToken>::empty());
    }
    loop
        invariant
            start_pos <= pos && pos <= n,
            n == input@.len(),
            spec_tokenize_loop(input@, pos as nat, spec_tokens_view(tokens@))
                == spec_tokenize(input@),
        decreases n - pos,
    {
        match skip_trivia(input, pos, false) {
            Err(e) => {
                return LexOutcome::SyntaxError(e);
            },
            Ok((tpos, saw_lt)) => {
                if tpos >= n {
                    let ghost old_t = tokens@;
                    let eof_tok = Token {
                        kind: TokenKind::Eof,
                        span: Span { start: n, end: n },
                        preceded_by_line_terminator: saw_lt,
                    };
                    tokens.push(eof_tok);
                    proof {
                        lemma_tokens_push_view(old_t, eof_tok);
                    }
                    return LexOutcome::Ok(tokens);
                }
                match lex_non_trivia_token(input, tpos, saw_lt) {
                    StepOutcome::Token { tok, next_pos } => {
                        let ghost old_t = tokens@;
                        let ghost g_tok = tok;
                        tokens.push(tok);
                        proof {
                            lemma_tokens_push_view(old_t, g_tok);
                        }
                        pos = next_pos;
                    },
                    StepOutcome::SyntaxError(e) => {
                        return LexOutcome::SyntaxError(e);
                    },
                    StepOutcome::Unsupported(u) => {
                        return LexOutcome::Unsupported(u);
                    },
                }
            },
        }
    }
}

// ---------------------------------------------------------------------------------------
// UTF-16 Source Entry Point (`tokenize_utf16`, ECMA-262 §11.1.4)
// ---------------------------------------------------------------------------------------

pub open spec fn spec_utf16_units_to_utf8_loop(
    units: Seq<u16>,
    pos: nat,
    acc: Seq<u8>,
) -> Result<Seq<u8>, SyntaxDiagnostic>
    decreases units.len() - pos,
{
    if pos >= units.len() {
        Ok(acc)
    } else {
        let u0 = units[pos as int];
        if 0xD800 <= u0 && u0 <= 0xDBFF {
            if pos + 1 < units.len() && 0xDC00 <= units[(pos + 1) as int] && units[(pos + 1) as int] <= 0xDFFF {
                let u1 = units[(pos + 1) as int];
                let cp = (0x10000 + (u0 - 0xD800) * 1024 + (u1 - 0xDC00)) as u32;
                spec_utf16_units_to_utf8_loop(units, pos + 2, spec_append_utf8_cp(acc, cp))
            } else {
                Err(SyntaxDiagnostic {
                    kind: DiagnosticKind::LoneSurrogateInSource,
                    span: spec_span(pos, pos + 1),
                })
            }
        } else if 0xDC00 <= u0 && u0 <= 0xDFFF {
            Err(SyntaxDiagnostic {
                kind: DiagnosticKind::LoneSurrogateInSource,
                span: spec_span(pos, pos + 1),
            })
        } else {
            spec_utf16_units_to_utf8_loop(units, pos + 1, spec_append_utf8_cp(acc, u0 as u32))
        }
    }
}

pub fn utf16_units_to_utf8(units: &[u16]) -> (r: Result<Vec<u8>, SyntaxDiagnostic>)
    ensures
        match r {
            Ok(bytes) => spec_utf16_units_to_utf8_loop(units@, 0, Seq::<u8>::empty()) == Ok::<Seq<u8>, SyntaxDiagnostic>(bytes@),
            Err(e) => spec_utf16_units_to_utf8_loop(units@, 0, Seq::<u8>::empty()) == Err(e),
        },
{
    let n = units.len();
    let mut pos: usize = 0;
    let mut out: Vec<u8> = Vec::new();
    proof {
        assert(out@ =~= Seq::<u8>::empty());
    }
    while pos < n
        invariant
            pos <= n,
            n == units@.len(),
            spec_utf16_units_to_utf8_loop(units@, pos as nat, out@)
                == spec_utf16_units_to_utf8_loop(units@, 0, Seq::<u8>::empty()),
        decreases n - pos,
    {
        let rem = n - pos;
        let u0 = units[pos];
        if u0 >= 0xD800 && u0 <= 0xDBFF {
            if rem >= 2 && units[pos + 1] >= 0xDC00 && units[pos + 1] <= 0xDFFF {
                let u1 = units[pos + 1];
                let cp: u32 = 0x10000 + ((u0 - 0xD800) as u32) * 1024 + ((u1 - 0xDC00) as u32);
                append_utf8_cp(&mut out, cp);
                pos = pos + 2;
            } else {
                return Err(SyntaxDiagnostic {
                    kind: DiagnosticKind::LoneSurrogateInSource,
                    span: Span { start: pos, end: pos + 1 },
                });
            }
        } else if u0 >= 0xDC00 && u0 <= 0xDFFF {
            return Err(SyntaxDiagnostic {
                kind: DiagnosticKind::LoneSurrogateInSource,
                span: Span { start: pos, end: pos + 1 },
            });
        } else {
            append_utf8_cp(&mut out, u0 as u32);
            pos = pos + 1;
        }
    }
    Ok(out)
}

pub open spec fn spec_tokenize_utf16(units: Seq<u16>) -> SpecLexOutcome {
    match spec_utf16_units_to_utf8_loop(units, 0, Seq::<u8>::empty()) {
        Ok(bytes) => spec_tokenize(bytes),
        Err(e) => SpecLexOutcome::SyntaxError(e),
    }
}

/// Verified ECMAScript tokenizer over UTF-16 code units `&[u16]`.
pub fn tokenize_utf16(units: &[u16]) -> (out: LexOutcome)
    ensures
        out@ == spec_tokenize_utf16(units@),
{
    match utf16_units_to_utf8(units) {
        Ok(bytes) => tokenize(bytes.as_slice()),
        Err(e) => LexOutcome::SyntaxError(e),
    }
}

// ---------------------------------------------------------------------------------------
// Metatheory & Spec Lemmas on the Lexer
// ---------------------------------------------------------------------------------------

pub proof fn lemma_tokenize_loop_ends_with_eof(
    input: Seq<u8>,
    pos: nat,
    acc: Seq<SpecToken>,
)
    requires
        pos <= input.len(),
    ensures
        match spec_tokenize_loop(input, pos, acc) {
            SpecLexOutcome::Ok(toks) => toks.len() >= acc.len() + 1 && toks.last().kind == SpecTokenKind::Eof,
            _ => true,
        },
    decreases input.len() - pos,
{
    lemma_skip_trivia_bounds(input, pos, false);
    if let Ok((tpos, saw_lt)) = spec_skip_trivia(input, pos, false) {
        if tpos < input.len() {
            lemma_lex_token_step_advances(input, tpos, saw_lt);
            if let SpecStepOutcome::Token { tok, next_pos } = spec_lex_non_trivia_token(input, tpos, saw_lt) {
                lemma_tokenize_loop_ends_with_eof(input, next_pos, acc.push(tok));
            }
        }
    }
}

/// Theorem: Every successful `tokenize` output is non-empty and terminates with an explicit `Eof` token.
pub proof fn lemma_tokenize_ends_with_eof(input: Seq<u8>)
    ensures
        match spec_tokenize(input) {
            SpecLexOutcome::Ok(toks) => toks.len() >= 1 && toks.last().kind == SpecTokenKind::Eof,
            _ => true,
        },
{
    if input.len() >= 2 && input[0] == 0x23 && input[1] == 0x21 {
        lemma_skip_line_comment_bounds(input, 2);
    }
    let start_pos = spec_initial_pos_after_hashbang(input);
    lemma_tokenize_loop_ends_with_eof(input, start_pos, Seq::<SpecToken>::empty());
}

/// Theorem (§12.4 ASI comment rule): A multi-line comment `/*\n*/` sets `preceded_by_line_terminator = true`,
/// whereas `/**/` without a line terminator leaves `preceded_by_line_terminator = false`.
pub proof fn lemma_multiline_comment_asi_semantics()
    ensures
        spec_skip_trivia(seq![0x2Fu8, 0x2A, 0x0A, 0x2A, 0x2F, 0x78], 0, false)
            == Ok::<(nat, bool), SyntaxDiagnostic>((5nat, true)),
        spec_skip_trivia(seq![0x2Fu8, 0x2A, 0x20, 0x2A, 0x2F, 0x78], 0, false)
            == Ok::<(nat, bool), SyntaxDiagnostic>((5nat, false)),
{
    let s_nl = seq![0x2Fu8, 0x2A, 0x0A, 0x2A, 0x2F, 0x78];
    let s_sp = seq![0x2Fu8, 0x2A, 0x20, 0x2A, 0x2F, 0x78];
    reveal_with_fuel(spec_skip_block_comment, 4);
    reveal_with_fuel(spec_skip_trivia, 3);
    assert(s_nl.len() == 6);
    assert(s_sp.len() == 6);
}

} // verus!
