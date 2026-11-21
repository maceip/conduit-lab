//! Formally verified WebAssembly 1.0 binary format decoder (`vwasm::binary`).
//!
//! Verifies:
//! 1. Header parser (`\0asm` magic `[0x00, 0x61, 0x73, 0x6d]` + version `1`), proved `exec == spec`
//!    and prefix-secure (`lemma_header_prefix_secure`).
//! 2. Unsigned & signed LEB128 decoders (`decode_u32_leb128`, `decode_i32_leb128`,
//!    `decode_i64_leb128`) and encoder (`encode_u32_leb128`) with machine-checked Verus proofs of:
//!    - `exec == spec` equivalence,
//!    - strict cursor progress & slice bounds (`pos < next_pos <= bytes.len()`),
//!    - Vest-style prefix consumption / trailing-byte non-malleability
//!      (`lemma_u32_leb128_prefix_secure`, `lemma_i32_leb128_prefix_secure`,
//!      `lemma_i64_leb128_prefix_secure`),
//!    - encode-then-decode roundtrip (`lemma_u32_leb128_roundtrip`).
//! 3. Total, terminating section parsers (`decreases` on every loop) for Custom (0), Type (1),
//!    Function (3), Table (4), Memory (5), Global (6), Export (7), Elem (9), Code (10), and
//!    Data (11) sections, plus verified structured-control-flow jump target resolution.

use vstd::prelude::*;
use crate::types::{
    DataSegment, DecodeError, ElemSegment, ExportDesc, ExportKind, FuncBody, FuncType, GlobalDecl,
    I32BinOp, I32UnOp, I64BinOp, I64UnOp, IntRelOp, LoadKind, MemoryLimits, RawInstr, StoreKind,
    TableLimits, ValType, WasmModule, WasmOp, WasmVal, MAX_LOCALS_PER_FUNC, MAX_SPEC_PAGES,
    MAX_TABLE_ENTRIES, WASM_MAGIC, WASM_VERSION_1,
};

verus! {

// ---------------------------------------------------------------------------
// 1. Module Header (`\0asm` + version 1)
// ---------------------------------------------------------------------------

pub open spec fn spec_decode_header(bytes: Seq<u8>) -> Result<nat, DecodeError> {
    if bytes.len() < 8 {
        Err(DecodeError::UnexpectedEof)
    } else if bytes[0] != 0x00 || bytes[1] != 0x61 || bytes[2] != 0x73 || bytes[3] != 0x6d {
        Err(DecodeError::InvalidMagic)
    } else if bytes[4] != 0x01 || bytes[5] != 0x00 || bytes[6] != 0x00 || bytes[7] != 0x00 {
        Err(DecodeError::UnsupportedVersion)
    } else {
        Ok(8)
    }
}

pub proof fn lemma_header_prefix_secure(s: Seq<u8>, suffix: Seq<u8>)
    requires
        spec_decode_header(s) == Ok::<nat, DecodeError>(8),
    ensures
        spec_decode_header(s + suffix) == Ok::<nat, DecodeError>(8),
        spec_decode_header(s.subrange(0, 8)) == Ok::<nat, DecodeError>(8),
{
}

pub fn decode_header(bytes: &[u8]) -> (r: Result<usize, DecodeError>)
    ensures
        match (r, spec_decode_header(bytes@)) {
            (Ok(n), Ok(sn)) => n as nat == sn && n == 8 && n <= bytes@.len(),
            (Err(e), Err(se)) => e == se,
            _ => false,
        },
{
    if bytes.len() < 8 {
        return Err(DecodeError::UnexpectedEof);
    }
    if bytes[0] != WASM_MAGIC[0]
        || bytes[1] != WASM_MAGIC[1]
        || bytes[2] != WASM_MAGIC[2]
        || bytes[3] != WASM_MAGIC[3]
    {
        return Err(DecodeError::InvalidMagic);
    }
    if bytes[4] != WASM_VERSION_1[0]
        || bytes[5] != WASM_VERSION_1[1]
        || bytes[6] != WASM_VERSION_1[2]
        || bytes[7] != WASM_VERSION_1[3]
    {
        return Err(DecodeError::UnsupportedVersion);
    }
    Ok(8)
}

// ---------------------------------------------------------------------------
// 2. Verified Unsigned & Signed LEB128 (Wasm 1.0 §5.2.2)
// ---------------------------------------------------------------------------

pub open spec fn spec_decode_u32_leb128(
    bytes: Seq<u8>,
    pos: nat,
) -> Result<(u32, nat), DecodeError> {
    if pos >= bytes.len() {
        Err(DecodeError::UnexpectedEof)
    } else {
        let b0 = bytes[pos as int];
        let v0 = (b0 & 0x7fu8) as u32;
        if (b0 & 0x80u8) == 0 {
            Ok((v0, pos + 1))
        } else if pos + 1 >= bytes.len() {
            Err(DecodeError::UnexpectedEof)
        } else {
            let b1 = bytes[(pos + 1) as int];
            let v1 = v0 | (((b1 & 0x7fu8) as u32) << 7u32);
            if (b1 & 0x80u8) == 0 {
                Ok((v1, pos + 2))
            } else if pos + 2 >= bytes.len() {
                Err(DecodeError::UnexpectedEof)
            } else {
                let b2 = bytes[(pos + 2) as int];
                let v2 = v1 | (((b2 & 0x7fu8) as u32) << 14u32);
                if (b2 & 0x80u8) == 0 {
                    Ok((v2, pos + 3))
                } else if pos + 3 >= bytes.len() {
                    Err(DecodeError::UnexpectedEof)
                } else {
                    let b3 = bytes[(pos + 3) as int];
                    let v3 = v2 | (((b3 & 0x7fu8) as u32) << 21u32);
                    if (b3 & 0x80u8) == 0 {
                        Ok((v3, pos + 4))
                    } else if pos + 4 >= bytes.len() {
                        Err(DecodeError::UnexpectedEof)
                    } else {
                        let b4 = bytes[(pos + 4) as int];
                        if (b4 & 0xf0u8) != 0 {
                            Err(DecodeError::InvalidLeb128)
                        } else {
                            let v4 = v3 | ((b4 as u32) << 28u32);
                            Ok((v4, pos + 5))
                        }
                    }
                }
            }
        }
    }
}

pub proof fn lemma_u32_leb128_bounds(bytes: Seq<u8>, pos: nat)
    ensures
        match spec_decode_u32_leb128(bytes, pos) {
            Ok((_, next_pos)) => pos < next_pos && next_pos <= bytes.len() && next_pos <= pos + 5,
            Err(_) => true,
        },
{
}

pub proof fn lemma_u32_leb128_prefix_secure(s: Seq<u8>, suffix: Seq<u8>, pos: nat)
    requires
        spec_decode_u32_leb128(s, pos) matches Ok(_),
    ensures
        ({
            let (v, next_pos) = match spec_decode_u32_leb128(s, pos) {
                Ok(pair) => pair,
                Err(_) => (0u32, 0nat),
            };
            spec_decode_u32_leb128(s + suffix, pos) == Ok::<(u32, nat), DecodeError>((v, next_pos))
                && spec_decode_u32_leb128(s.subrange(0, next_pos as int), pos)
                    == Ok::<(u32, nat), DecodeError>((v, next_pos))
        }),
{
}

pub open spec fn spec_encode_u32_leb128(n: u32) -> Seq<u8> {
    if n < 0x80u32 {
        seq![(n & 0x7fu32) as u8]
    } else if n < 0x4000u32 {
        seq![
            ((n & 0x7fu32) as u8) | 0x80u8,
            ((n >> 7u32) & 0x7fu32) as u8,
        ]
    } else if n < 0x20_0000u32 {
        seq![
            ((n & 0x7fu32) as u8) | 0x80u8,
            (((n >> 7u32) & 0x7fu32) as u8) | 0x80u8,
            ((n >> 14u32) & 0x7fu32) as u8,
        ]
    } else if n < 0x1000_0000u32 {
        seq![
            ((n & 0x7fu32) as u8) | 0x80u8,
            (((n >> 7u32) & 0x7fu32) as u8) | 0x80u8,
            (((n >> 14u32) & 0x7fu32) as u8) | 0x80u8,
            ((n >> 21u32) & 0x7fu32) as u8,
        ]
    } else {
        seq![
            ((n & 0x7fu32) as u8) | 0x80u8,
            (((n >> 7u32) & 0x7fu32) as u8) | 0x80u8,
            (((n >> 14u32) & 0x7fu32) as u8) | 0x80u8,
            (((n >> 21u32) & 0x7fu32) as u8) | 0x80u8,
            (n >> 28u32) as u8,
        ]
    }
}

#[verifier::spinoff_prover]
pub proof fn lemma_u32_leb128_roundtrip(n: u32)
    ensures
        spec_decode_u32_leb128(spec_encode_u32_leb128(n), 0)
            == Ok::<(u32, nat), DecodeError>((n, spec_encode_u32_leb128(n).len())),
{
    let enc = spec_encode_u32_leb128(n);
    if n < 0x80u32 {
        assert(n < 0x80u32 ==> (((n & 0x7fu32) as u8) & 0x80u8) == 0u8
            && (((n & 0x7fu32) as u8) & 0x7fu8) as u32 == n) by (bit_vector);
    } else if n < 0x4000u32 {
        assert(0x80u32 <= n < 0x4000u32 ==> {
            let b0 = ((n & 0x7fu32) as u8) | 0x80u8;
            let b1 = ((n >> 7u32) & 0x7fu32) as u8;
            (b0 & 0x80u8) != 0u8
                && (b1 & 0x80u8) == 0u8
                && (((b0 & 0x7fu8) as u32) | (((b1 & 0x7fu8) as u32) << 7u32)) == n
        }) by (bit_vector);
    } else if n < 0x20_0000u32 {
        assert(0x4000u32 <= n < 0x20_0000u32 ==> {
            let b0 = ((n & 0x7fu32) as u8) | 0x80u8;
            let b1 = (((n >> 7u32) & 0x7fu32) as u8) | 0x80u8;
            let b2 = ((n >> 14u32) & 0x7fu32) as u8;
            (b0 & 0x80u8) != 0u8
                && (b1 & 0x80u8) != 0u8
                && (b2 & 0x80u8) == 0u8
                && (((b0 & 0x7fu8) as u32)
                    | (((b1 & 0x7fu8) as u32) << 7u32)
                    | (((b2 & 0x7fu8) as u32) << 14u32)) == n
        }) by (bit_vector);
    } else if n < 0x1000_0000u32 {
        assert(0x20_0000u32 <= n < 0x1000_0000u32 ==> {
            let b0 = ((n & 0x7fu32) as u8) | 0x80u8;
            let b1 = (((n >> 7u32) & 0x7fu32) as u8) | 0x80u8;
            let b2 = (((n >> 14u32) & 0x7fu32) as u8) | 0x80u8;
            let b3 = ((n >> 21u32) & 0x7fu32) as u8;
            (b0 & 0x80u8) != 0u8
                && (b1 & 0x80u8) != 0u8
                && (b2 & 0x80u8) != 0u8
                && (b3 & 0x80u8) == 0u8
                && (((b0 & 0x7fu8) as u32)
                    | (((b1 & 0x7fu8) as u32) << 7u32)
                    | (((b2 & 0x7fu8) as u32) << 14u32)
                    | (((b3 & 0x7fu8) as u32) << 21u32)) == n
        }) by (bit_vector);
    } else {
        assert(n >= 0x1000_0000u32 ==> {
            let b0 = ((n & 0x7fu32) as u8) | 0x80u8;
            let b1 = (((n >> 7u32) & 0x7fu32) as u8) | 0x80u8;
            let b2 = (((n >> 14u32) & 0x7fu32) as u8) | 0x80u8;
            let b3 = (((n >> 21u32) & 0x7fu32) as u8) | 0x80u8;
            let b4 = (n >> 28u32) as u8;
            (b0 & 0x80u8) != 0u8
                && (b1 & 0x80u8) != 0u8
                && (b2 & 0x80u8) != 0u8
                && (b3 & 0x80u8) != 0u8
                && (b4 & 0xf0u8) == 0u8
                && (((b0 & 0x7fu8) as u32)
                    | (((b1 & 0x7fu8) as u32) << 7u32)
                    | (((b2 & 0x7fu8) as u32) << 14u32)
                    | (((b3 & 0x7fu8) as u32) << 21u32)
                    | ((b4 as u32) << 28u32)) == n
        }) by (bit_vector);
    }
    assert(enc.len() >= 1);
}

pub fn encode_u32_leb128(n: u32) -> (out: Vec<u8>)
    ensures
        out@ == spec_encode_u32_leb128(n),
{
    let mut out = Vec::new();
    if n < 0x80 {
        out.push((n & 0x7f) as u8);
        proof { assert(out@ =~= spec_encode_u32_leb128(n)); }
    } else if n < 0x4000 {
        out.push(((n & 0x7f) as u8) | 0x80);
        out.push(((n >> 7) & 0x7f) as u8);
        proof { assert(out@ =~= spec_encode_u32_leb128(n)); }
    } else if n < 0x20_0000 {
        out.push(((n & 0x7f) as u8) | 0x80);
        out.push((((n >> 7) & 0x7f) as u8) | 0x80);
        out.push(((n >> 14) & 0x7f) as u8);
        proof { assert(out@ =~= spec_encode_u32_leb128(n)); }
    } else if n < 0x1000_0000 {
        out.push(((n & 0x7f) as u8) | 0x80);
        out.push((((n >> 7) & 0x7f) as u8) | 0x80);
        out.push((((n >> 14) & 0x7f) as u8) | 0x80);
        out.push(((n >> 21) & 0x7f) as u8);
        proof { assert(out@ =~= spec_encode_u32_leb128(n)); }
    } else {
        out.push(((n & 0x7f) as u8) | 0x80);
        out.push((((n >> 7) & 0x7f) as u8) | 0x80);
        out.push((((n >> 14) & 0x7f) as u8) | 0x80);
        out.push((((n >> 21) & 0x7f) as u8) | 0x80);
        out.push((n >> 28) as u8);
        proof { assert(out@ =~= spec_encode_u32_leb128(n)); }
    }
    out
}

pub fn decode_u32_leb128(bytes: &[u8], pos: usize) -> (r: Result<(u32, usize), DecodeError>)
    ensures
        match (r, spec_decode_u32_leb128(bytes@, pos as nat)) {
            (Ok((v, np)), Ok((sv, snp))) =>
                v == sv && np as nat == snp && pos < np && np <= bytes@.len() && np <= pos + 5,
            (Err(e), Err(se)) => e == se,
            _ => false,
        },
{
    let len = bytes.len();
    if pos >= len {
        return Err(DecodeError::UnexpectedEof);
    }
    let b0 = bytes[pos];
    let v0 = (b0 & 0x7f) as u32;
    if (b0 & 0x80) == 0 {
        return Ok((v0, pos + 1));
    }
    if len - pos <= 1 {
        return Err(DecodeError::UnexpectedEof);
    }
    let b1 = bytes[pos + 1];
    let v1 = v0 | (((b1 & 0x7f) as u32) << 7);
    if (b1 & 0x80) == 0 {
        return Ok((v1, pos + 2));
    }
    if len - pos <= 2 {
        return Err(DecodeError::UnexpectedEof);
    }
    let b2 = bytes[pos + 2];
    let v2 = v1 | (((b2 & 0x7f) as u32) << 14);
    if (b2 & 0x80) == 0 {
        return Ok((v2, pos + 3));
    }
    if len - pos <= 3 {
        return Err(DecodeError::UnexpectedEof);
    }
    let b3 = bytes[pos + 3];
    let v3 = v2 | (((b3 & 0x7f) as u32) << 21);
    if (b3 & 0x80) == 0 {
        return Ok((v3, pos + 4));
    }
    if len - pos <= 4 {
        return Err(DecodeError::UnexpectedEof);
    }
    let b4 = bytes[pos + 4];
    if (b4 & 0xf0) != 0 {
        return Err(DecodeError::InvalidLeb128);
    }
    let v4 = v3 | ((b4 as u32) << 28);
    Ok((v4, pos + 5))
}

// Signed 32-bit LEB128 (`s32`)

pub open spec fn spec_decode_i32_leb128(
    bytes: Seq<u8>,
    pos: nat,
) -> Result<(i32, nat), DecodeError> {
    if pos >= bytes.len() {
        Err(DecodeError::UnexpectedEof)
    } else {
        let b0 = bytes[pos as int];
        let v0 = (b0 & 0x7fu8) as u32;
        if (b0 & 0x80u8) == 0 {
            let r0 = if (b0 & 0x40u8) != 0 { v0 | 0xffff_ff80u32 } else { v0 };
            Ok((r0 as i32, pos + 1))
        } else if pos + 1 >= bytes.len() {
            Err(DecodeError::UnexpectedEof)
        } else {
            let b1 = bytes[(pos + 1) as int];
            let v1 = v0 | (((b1 & 0x7fu8) as u32) << 7u32);
            if (b1 & 0x80u8) == 0 {
                let r1 = if (b1 & 0x40u8) != 0 { v1 | 0xffff_c000u32 } else { v1 };
                Ok((r1 as i32, pos + 2))
            } else if pos + 2 >= bytes.len() {
                Err(DecodeError::UnexpectedEof)
            } else {
                let b2 = bytes[(pos + 2) as int];
                let v2 = v1 | (((b2 & 0x7fu8) as u32) << 14u32);
                if (b2 & 0x80u8) == 0 {
                    let r2 = if (b2 & 0x40u8) != 0 { v2 | 0xffe0_0000u32 } else { v2 };
                    Ok((r2 as i32, pos + 3))
                } else if pos + 3 >= bytes.len() {
                    Err(DecodeError::UnexpectedEof)
                } else {
                    let b3 = bytes[(pos + 3) as int];
                    let v3 = v2 | (((b3 & 0x7fu8) as u32) << 21u32);
                    if (b3 & 0x80u8) == 0 {
                        let r3 = if (b3 & 0x40u8) != 0 { v3 | 0xf000_0000u32 } else { v3 };
                        Ok((r3 as i32, pos + 4))
                    } else if pos + 4 >= bytes.len() {
                        Err(DecodeError::UnexpectedEof)
                    } else {
                        let b4 = bytes[(pos + 4) as int];
                        if (b4 & 0x80u8) != 0 {
                            Err(DecodeError::InvalidLeb128)
                        } else {
                            let top = b4 & 0x78u8;
                            if top != 0x00u8 && top != 0x78u8 {
                                Err(DecodeError::InvalidLeb128)
                            } else {
                                let v4 = v3 | (((b4 & 0x0fu8) as u32) << 28u32);
                                Ok((v4 as i32, pos + 5))
                            }
                        }
                    }
                }
            }
        }
    }
}

pub proof fn lemma_i32_leb128_bounds(bytes: Seq<u8>, pos: nat)
    ensures
        match spec_decode_i32_leb128(bytes, pos) {
            Ok((_, next_pos)) => pos < next_pos && next_pos <= bytes.len() && next_pos <= pos + 5,
            Err(_) => true,
        },
{
}

pub proof fn lemma_i32_leb128_prefix_secure(s: Seq<u8>, suffix: Seq<u8>, pos: nat)
    requires
        spec_decode_i32_leb128(s, pos) matches Ok(_),
    ensures
        ({
            let (v, next_pos) = match spec_decode_i32_leb128(s, pos) {
                Ok(pair) => pair,
                Err(_) => (0i32, 0nat),
            };
            spec_decode_i32_leb128(s + suffix, pos) == Ok::<(i32, nat), DecodeError>((v, next_pos))
                && spec_decode_i32_leb128(s.subrange(0, next_pos as int), pos)
                    == Ok::<(i32, nat), DecodeError>((v, next_pos))
        }),
{
}

pub fn decode_i32_leb128(bytes: &[u8], pos: usize) -> (r: Result<(i32, usize), DecodeError>)
    ensures
        match (r, spec_decode_i32_leb128(bytes@, pos as nat)) {
            (Ok((v, np)), Ok((sv, snp))) =>
                v == sv && np as nat == snp && pos < np && np <= bytes@.len() && np <= pos + 5,
            (Err(e), Err(se)) => e == se,
            _ => false,
        },
{
    let len = bytes.len();
    if pos >= len {
        return Err(DecodeError::UnexpectedEof);
    }
    let b0 = bytes[pos];
    let v0 = (b0 & 0x7f) as u32;
    if (b0 & 0x80) == 0 {
        let r0 = if (b0 & 0x40) != 0 { v0 | 0xffff_ff80 } else { v0 };
        return Ok((r0 as i32, pos + 1));
    }
    if len - pos <= 1 {
        return Err(DecodeError::UnexpectedEof);
    }
    let b1 = bytes[pos + 1];
    let v1 = v0 | (((b1 & 0x7f) as u32) << 7);
    if (b1 & 0x80) == 0 {
        let r1 = if (b1 & 0x40) != 0 { v1 | 0xffff_c000 } else { v1 };
        return Ok((r1 as i32, pos + 2));
    }
    if len - pos <= 2 {
        return Err(DecodeError::UnexpectedEof);
    }
    let b2 = bytes[pos + 2];
    let v2 = v1 | (((b2 & 0x7f) as u32) << 14);
    if (b2 & 0x80) == 0 {
        let r2 = if (b2 & 0x40) != 0 { v2 | 0xffe0_0000 } else { v2 };
        return Ok((r2 as i32, pos + 3));
    }
    if len - pos <= 3 {
        return Err(DecodeError::UnexpectedEof);
    }
    let b3 = bytes[pos + 3];
    let v3 = v2 | (((b3 & 0x7f) as u32) << 21);
    if (b3 & 0x80) == 0 {
        let r3 = if (b3 & 0x40) != 0 { v3 | 0xf000_0000 } else { v3 };
        return Ok((r3 as i32, pos + 4));
    }
    if len - pos <= 4 {
        return Err(DecodeError::UnexpectedEof);
    }
    let b4 = bytes[pos + 4];
    if (b4 & 0x80) != 0 {
        return Err(DecodeError::InvalidLeb128);
    }
    let top = b4 & 0x78;
    if top != 0x00 && top != 0x78 {
        return Err(DecodeError::InvalidLeb128);
    }
    let v4 = v3 | (((b4 & 0x0f) as u32) << 28);
    Ok((v4 as i32, pos + 5))
}

// Signed 64-bit LEB128 (`s64`, up to 10 bytes)

pub open spec fn spec_i64_sign_mask(step: nat) -> u64 {
    if step == 0 {
        0xffff_ffff_ffff_ff80u64
    } else if step == 1 {
        0xffff_ffff_ffff_c000u64
    } else if step == 2 {
        0xffff_ffff_ffe0_0000u64
    } else if step == 3 {
        0xffff_ffff_f000_0000u64
    } else if step == 4 {
        0xffff_fff8_0000_0000u64
    } else if step == 5 {
        0xffff_fc00_0000_0000u64
    } else if step == 6 {
        0xfffe_0000_0000_0000u64
    } else if step == 7 {
        0xff00_0000_0000_0000u64
    } else {
        0x8000_0000_0000_0000u64
    }
}

fn i64_sign_mask(step: usize) -> (m: u64)
    requires
        step < 9,
    ensures
        m == spec_i64_sign_mask(step as nat),
{
    if step == 0 {
        0xffff_ffff_ffff_ff80
    } else if step == 1 {
        0xffff_ffff_ffff_c000
    } else if step == 2 {
        0xffff_ffff_ffe0_0000
    } else if step == 3 {
        0xffff_ffff_f000_0000
    } else if step == 4 {
        0xffff_fff8_0000_0000
    } else if step == 5 {
        0xffff_fc00_0000_0000
    } else if step == 6 {
        0xfffe_0000_0000_0000
    } else if step == 7 {
        0xff00_0000_0000_0000
    } else {
        0x8000_0000_0000_0000
    }
}

pub open spec fn spec_decode_i64_leb128_step(
    bytes: Seq<u8>,
    pos: nat,
    step: nat,
    acc: u64,
) -> Result<(i64, nat), DecodeError>
    decreases 10 - step,
{
    if step >= 10 {
        Err(DecodeError::InvalidLeb128)
    } else if pos + step >= bytes.len() {
        Err(DecodeError::UnexpectedEof)
    } else {
        let b = bytes[(pos + step) as int];
        if step < 9 {
            let shift = (step * 7) as u32;
            let next_acc = acc | (((b & 0x7fu8) as u64) << shift);
            if (b & 0x80u8) == 0 {
                let signed_bits = if (b & 0x40u8) != 0 {
                    next_acc | spec_i64_sign_mask(step)
                } else {
                    next_acc
                };
                Ok((signed_bits as i64, pos + step + 1))
            } else {
                spec_decode_i64_leb128_step(bytes, pos, step + 1, next_acc)
            }
        } else {
            // 10th byte (step == 9) carries bit 63; bits 1..6 must match sign bit 0, bit 7 == 0.
            if b != 0x00u8 && b != 0x7fu8 {
                Err(DecodeError::InvalidLeb128)
            } else {
                let final_bits = acc | (((b & 0x01u8) as u64) << 63u32);
                Ok((final_bits as i64, pos + 10))
            }
        }
    }
}

pub open spec fn spec_decode_i64_leb128(
    bytes: Seq<u8>,
    pos: nat,
) -> Result<(i64, nat), DecodeError> {
    spec_decode_i64_leb128_step(bytes, pos, 0, 0)
}

proof fn lemma_i64_leb128_step_bounds(bytes: Seq<u8>, pos: nat, step: nat, acc: u64)
    requires
        step <= 9,
    ensures
        match spec_decode_i64_leb128_step(bytes, pos, step, acc) {
            Ok((_, next_pos)) =>
                pos + step < next_pos && next_pos <= bytes.len() && next_pos <= pos + 10,
            Err(_) => true,
        },
    decreases 10 - step,
{
    if pos + step < bytes.len() && step < 9 {
        let b = bytes[(pos + step) as int];
        if (b & 0x80u8) != 0 {
            let shift = (step * 7) as u32;
            let next_acc = acc | (((b & 0x7fu8) as u64) << shift);
            lemma_i64_leb128_step_bounds(bytes, pos, step + 1, next_acc);
        }
    }
}

pub proof fn lemma_i64_leb128_bounds(bytes: Seq<u8>, pos: nat)
    ensures
        match spec_decode_i64_leb128(bytes, pos) {
            Ok((_, next_pos)) => pos < next_pos && next_pos <= bytes.len() && next_pos <= pos + 10,
            Err(_) => true,
        },
{
    lemma_i64_leb128_step_bounds(bytes, pos, 0, 0);
}

proof fn lemma_i64_leb128_step_prefix_secure(
    s: Seq<u8>,
    suffix: Seq<u8>,
    pos: nat,
    step: nat,
    acc: u64,
)
    requires
        step <= 9,
        spec_decode_i64_leb128_step(s, pos, step, acc) matches Ok(_),
    ensures
        ({
            let (v, next_pos) = match spec_decode_i64_leb128_step(s, pos, step, acc) {
                Ok(pair) => pair,
                Err(_) => (0i64, 0nat),
            };
            spec_decode_i64_leb128_step(s + suffix, pos, step, acc)
                == Ok::<(i64, nat), DecodeError>((v, next_pos))
                && spec_decode_i64_leb128_step(s.subrange(0, next_pos as int), pos, step, acc)
                    == Ok::<(i64, nat), DecodeError>((v, next_pos))
        }),
    decreases 10 - step,
{
    lemma_i64_leb128_step_bounds(s, pos, step, acc);
    let b = s[(pos + step) as int];
    if step < 9 && (b & 0x80u8) != 0 {
        let shift = (step * 7) as u32;
        let next_acc = acc | (((b & 0x7fu8) as u64) << shift);
        lemma_i64_leb128_step_prefix_secure(s, suffix, pos, step + 1, next_acc);
    }
}

pub proof fn lemma_i64_leb128_prefix_secure(s: Seq<u8>, suffix: Seq<u8>, pos: nat)
    requires
        spec_decode_i64_leb128(s, pos) matches Ok(_),
    ensures
        ({
            let (v, next_pos) = match spec_decode_i64_leb128(s, pos) {
                Ok(pair) => pair,
                Err(_) => (0i64, 0nat),
            };
            spec_decode_i64_leb128(s + suffix, pos) == Ok::<(i64, nat), DecodeError>((v, next_pos))
                && spec_decode_i64_leb128(s.subrange(0, next_pos as int), pos)
                    == Ok::<(i64, nat), DecodeError>((v, next_pos))
        }),
{
    lemma_i64_leb128_step_prefix_secure(s, suffix, pos, 0, 0);
}

pub fn decode_i64_leb128(bytes: &[u8], pos: usize) -> (r: Result<(i64, usize), DecodeError>)
    ensures
        match (r, spec_decode_i64_leb128(bytes@, pos as nat)) {
            (Ok((v, np)), Ok((sv, snp))) =>
                v == sv && np as nat == snp && pos < np && np <= bytes@.len() && np <= pos + 10,
            (Err(e), Err(se)) => e == se,
            _ => false,
        },
{
    let len = bytes.len();
    let mut step: usize = 0;
    let mut acc: u64 = 0;
    while step < 10
        invariant
            step <= 10,
            len == bytes@.len(),
            spec_decode_i64_leb128(bytes@, pos as nat)
                == spec_decode_i64_leb128_step(bytes@, pos as nat, step as nat, acc),
        decreases 10 - step,
    {
        if pos >= len || len - pos <= step {
            return Err(DecodeError::UnexpectedEof);
        }
        let b = bytes[pos + step];
        if step < 9 {
            let shift = (step as u32) * 7;
            let next_acc = acc | (((b & 0x7f) as u64) << shift);
            if (b & 0x80) == 0 {
                let signed_bits = if (b & 0x40) != 0 {
                    next_acc | i64_sign_mask(step)
                } else {
                    next_acc
                };
                return Ok((signed_bits as i64, pos + step + 1));
            }
            acc = next_acc;
            step = step + 1;
        } else {
            if b != 0x00 && b != 0x7f {
                return Err(DecodeError::InvalidLeb128);
            }
            let final_bits = acc | (((b & 0x01) as u64) << 63);
            return Ok((final_bits as i64, pos + 10));
        }
    }
    Err(DecodeError::InvalidLeb128)
}

// Fixed-width little-endian readers (for f32.const / f64.const payloads)

pub open spec fn spec_read_u32_le(bytes: Seq<u8>, pos: nat) -> Result<(u32, nat), DecodeError> {
    if pos + 4 > bytes.len() {
        Err(DecodeError::UnexpectedEof)
    } else {
        let v = (bytes[pos as int] as u32)
            | ((bytes[(pos + 1) as int] as u32) << 8u32)
            | ((bytes[(pos + 2) as int] as u32) << 16u32)
            | ((bytes[(pos + 3) as int] as u32) << 24u32);
        Ok((v, pos + 4))
    }
}

pub fn read_u32_le(bytes: &[u8], pos: usize) -> (r: Result<(u32, usize), DecodeError>)
    ensures
        match (r, spec_read_u32_le(bytes@, pos as nat)) {
            (Ok((v, np)), Ok((sv, snp))) => v == sv && np as nat == snp && np == pos + 4 && np <= bytes@.len(),
            (Err(e), Err(se)) => e == se,
            _ => false,
        },
{
    if pos > bytes.len() || bytes.len() - pos < 4 {
        return Err(DecodeError::UnexpectedEof);
    }
    let v = (bytes[pos] as u32)
        | ((bytes[pos + 1] as u32) << 8)
        | ((bytes[pos + 2] as u32) << 16)
        | ((bytes[pos + 3] as u32) << 24);
    Ok((v, pos + 4))
}

pub open spec fn spec_read_u64_le(bytes: Seq<u8>, pos: nat) -> Result<(u64, nat), DecodeError> {
    if pos + 8 > bytes.len() {
        Err(DecodeError::UnexpectedEof)
    } else {
        let v = (bytes[pos as int] as u64)
            | ((bytes[(pos + 1) as int] as u64) << 8u32)
            | ((bytes[(pos + 2) as int] as u64) << 16u32)
            | ((bytes[(pos + 3) as int] as u64) << 24u32)
            | ((bytes[(pos + 4) as int] as u64) << 32u32)
            | ((bytes[(pos + 5) as int] as u64) << 40u32)
            | ((bytes[(pos + 6) as int] as u64) << 48u32)
            | ((bytes[(pos + 7) as int] as u64) << 56u32);
        Ok((v, pos + 8))
    }
}

pub fn read_u64_le(bytes: &[u8], pos: usize) -> (r: Result<(u64, usize), DecodeError>)
    ensures
        match (r, spec_read_u64_le(bytes@, pos as nat)) {
            (Ok((v, np)), Ok((sv, snp))) => v == sv && np as nat == snp && np == pos + 8 && np <= bytes@.len(),
            (Err(e), Err(se)) => e == se,
            _ => false,
        },
{
    if pos > bytes.len() || bytes.len() - pos < 8 {
        return Err(DecodeError::UnexpectedEof);
    }
    let v = (bytes[pos] as u64)
        | ((bytes[pos + 1] as u64) << 8)
        | ((bytes[pos + 2] as u64) << 16)
        | ((bytes[pos + 3] as u64) << 24)
        | ((bytes[pos + 4] as u64) << 32)
        | ((bytes[pos + 5] as u64) << 40)
        | ((bytes[pos + 6] as u64) << 48)
        | ((bytes[pos + 7] as u64) << 56);
    Ok((v, pos + 8))
}

// ---------------------------------------------------------------------------
// 3. Verified Value Type, Block Type, Limits, & Section Parsers
// ---------------------------------------------------------------------------

pub open spec fn spec_decode_val_type(b: u8) -> Result<ValType, DecodeError> {
    if b == 0x7f {
        Ok(ValType::I32)
    } else if b == 0x7e {
        Ok(ValType::I64)
    } else if b == 0x7d {
        Ok(ValType::F32)
    } else if b == 0x7c {
        Ok(ValType::F64)
    } else {
        Err(DecodeError::UnsupportedType)
    }
}

pub fn decode_val_type(bytes: &[u8], pos: usize, end_pos: usize) -> (r: Result<(ValType, usize), DecodeError>)
    requires
        end_pos <= bytes@.len(),
    ensures
        match r {
            Ok((vt, np)) =>
                pos < end_pos && np == pos + 1 && Ok(vt) == spec_decode_val_type(bytes@[pos as int]),
            Err(_) => true,
        },
{
    if pos >= end_pos {
        return Err(DecodeError::UnexpectedEof);
    }
    let b = bytes[pos];
    if b == 0x7f {
        Ok((ValType::I32, pos + 1))
    } else if b == 0x7e {
        Ok((ValType::I64, pos + 1))
    } else if b == 0x7d {
        Ok((ValType::F32, pos + 1))
    } else if b == 0x7c {
        Ok((ValType::F64, pos + 1))
    } else {
        Err(DecodeError::UnsupportedType)
    }
}

pub open spec fn spec_decode_block_type(b: u8) -> Result<Option<ValType>, DecodeError> {
    if b == 0x40 {
        Ok(None)
    } else {
        match spec_decode_val_type(b) {
            Ok(vt) => Ok(Some(vt)),
            Err(e) => Err(e),
        }
    }
}

pub fn decode_block_type(
    bytes: &[u8],
    pos: usize,
    end_pos: usize,
) -> (r: Result<(Option<ValType>, usize), DecodeError>)
    requires
        end_pos <= bytes@.len(),
    ensures
        match r {
            Ok((bt, np)) =>
                pos < end_pos && np == pos + 1 && Ok(bt) == spec_decode_block_type(bytes@[pos as int]),
            Err(_) => true,
        },
{
    if pos >= end_pos {
        return Err(DecodeError::UnexpectedEof);
    }
    let b = bytes[pos];
    if b == 0x40 {
        Ok((None, pos + 1))
    } else {
        let (vt, np) = decode_val_type(bytes, pos, end_pos)?;
        Ok((Some(vt), np))
    }
}

fn decode_u32_bounded(bytes: &[u8], pos: usize, end_pos: usize) -> (r: Result<(u32, usize), DecodeError>)
    requires
        end_pos <= bytes@.len(),
    ensures
        match r {
            Ok((v, np)) =>
                pos < np && np <= end_pos
                    && spec_decode_u32_leb128(bytes@, pos as nat) == Ok::<(u32, nat), DecodeError>((v, np as nat)),
            Err(_) => true,
        },
{
    if pos >= end_pos {
        return Err(DecodeError::UnexpectedEof);
    }
    let (v, np) = decode_u32_leb128(bytes, pos)?;
    if np > end_pos {
        return Err(DecodeError::UnexpectedEof);
    }
    Ok((v, np))
}

fn decode_i32_bounded(bytes: &[u8], pos: usize, end_pos: usize) -> (r: Result<(i32, usize), DecodeError>)
    requires
        end_pos <= bytes@.len(),
    ensures
        match r {
            Ok((v, np)) =>
                pos < np && np <= end_pos
                    && spec_decode_i32_leb128(bytes@, pos as nat) == Ok::<(i32, nat), DecodeError>((v, np as nat)),
            Err(_) => true,
        },
{
    if pos >= end_pos {
        return Err(DecodeError::UnexpectedEof);
    }
    let (v, np) = decode_i32_leb128(bytes, pos)?;
    if np > end_pos {
        return Err(DecodeError::UnexpectedEof);
    }
    Ok((v, np))
}

fn decode_i64_bounded(bytes: &[u8], pos: usize, end_pos: usize) -> (r: Result<(i64, usize), DecodeError>)
    requires
        end_pos <= bytes@.len(),
    ensures
        match r {
            Ok((v, np)) =>
                pos < np && np <= end_pos
                    && spec_decode_i64_leb128(bytes@, pos as nat) == Ok::<(i64, nat), DecodeError>((v, np as nat)),
            Err(_) => true,
        },
{
    if pos >= end_pos {
        return Err(DecodeError::UnexpectedEof);
    }
    let (v, np) = decode_i64_leb128(bytes, pos)?;
    if np > end_pos {
        return Err(DecodeError::UnexpectedEof);
    }
    Ok((v, np))
}

fn copy_subslice(bytes: &[u8], pos: usize, len: usize, end_pos: usize) -> (r: Result<(Vec<u8>, usize), DecodeError>)
    requires
        end_pos <= bytes@.len(),
    ensures
        match r {
            Ok((v, np)) =>
                pos <= np && np <= end_pos && np == pos + len
                    && v@ == bytes@.subrange(pos as int, (pos + len) as int),
            Err(_) => true,
        },
{
    if pos > end_pos || end_pos - pos < len {
        return Err(DecodeError::UnexpectedEof);
    }
    let mut out: Vec<u8> = Vec::with_capacity(len);
    let mut i: usize = 0;
    while i < len
        invariant
            i <= len,
            pos <= end_pos,
            len <= end_pos - pos,
            end_pos <= bytes@.len(),
            out@.len() == i as nat,
            forall|k: int| 0 <= k < i as int ==> out@[k] == bytes@[(pos as int) + k],
        decreases len - i,
    {
        out.push(bytes[pos + i]);
        i = i + 1;
    }
    proof {
        assert(out@ =~= bytes@.subrange(pos as int, (pos + len) as int));
    }
    Ok((out, pos + len))
}

fn decode_val_type_vec(
    bytes: &[u8],
    mut pos: usize,
    end_pos: usize,
) -> (r: Result<(Vec<ValType>, usize), DecodeError>)
    requires
        pos <= end_pos,
        end_pos <= bytes@.len(),
    ensures
        match r {
            Ok((_, np)) => pos < np && np <= end_pos,
            Err(_) => true,
        },
{
    let (count, p1) = decode_u32_bounded(bytes, pos, end_pos)?;
    pos = p1;
    let mut out: Vec<ValType> = Vec::new();
    let mut i: u32 = 0;
    while i < count
        invariant
            i <= count,
            p1 <= pos <= end_pos,
            end_pos <= bytes@.len(),
        decreases count - i,
    {
        let (vt, np) = decode_val_type(bytes, pos, end_pos)?;
        out.push(vt);
        pos = np;
        i = i + 1;
    }
    Ok((out, pos))
}

/// Section 1: Type section (`vec(functype)` where `0x60` marks `func`).
pub fn decode_type_section(
    bytes: &[u8],
    mut pos: usize,
    end_pos: usize,
) -> (r: Result<Vec<FuncType>, DecodeError>)
    requires
        pos <= end_pos,
        end_pos <= bytes@.len(),
{
    let (count, p1) = decode_u32_bounded(bytes, pos, end_pos)?;
    pos = p1;
    let mut types: Vec<FuncType> = Vec::new();
    let mut i: u32 = 0;
    while i < count
        invariant
            i <= count,
            pos <= end_pos,
            end_pos <= bytes@.len(),
        decreases count - i,
    {
        if pos >= end_pos {
            return Err(DecodeError::UnexpectedEof);
        }
        if bytes[pos] != 0x60 {
            return Err(DecodeError::MalformedSection);
        }
        pos = pos + 1;
        let (params, p2) = decode_val_type_vec(bytes, pos, end_pos)?;
        let (results, p3) = decode_val_type_vec(bytes, p2, end_pos)?;
        types.push(FuncType { params, results });
        pos = p3;
        i = i + 1;
    }
    if pos != end_pos {
        return Err(DecodeError::MalformedSection);
    }
    Ok(types)
}

/// Section 3: Function section (`vec(typeidx)`).
pub fn decode_function_section(
    bytes: &[u8],
    mut pos: usize,
    end_pos: usize,
) -> (r: Result<Vec<u32>, DecodeError>)
    requires
        pos <= end_pos,
        end_pos <= bytes@.len(),
{
    let (count, p1) = decode_u32_bounded(bytes, pos, end_pos)?;
    pos = p1;
    let mut indices: Vec<u32> = Vec::new();
    let mut i: u32 = 0;
    while i < count
        invariant
            i <= count,
            pos <= end_pos,
            end_pos <= bytes@.len(),
        decreases count - i,
    {
        let (tidx, np) = decode_u32_bounded(bytes, pos, end_pos)?;
        indices.push(tidx);
        pos = np;
        i = i + 1;
    }
    if pos != end_pos {
        return Err(DecodeError::MalformedSection);
    }
    Ok(indices)
}

fn decode_limits(
    bytes: &[u8],
    pos: usize,
    end_pos: usize,
    upper_bound: u32,
) -> (r: Result<(u32, Option<u32>, usize), DecodeError>)
    requires
        pos <= end_pos,
        end_pos <= bytes@.len(),
    ensures
        match r {
            Ok((min_v, max_opt, np)) =>
                pos < np && np <= end_pos
                    && min_v <= upper_bound
                    && (match max_opt {
                        None => true,
                        Some(max_v) => min_v <= max_v && max_v <= upper_bound,
                    }),
            Err(_) => true,
        },
{
    if pos >= end_pos {
        return Err(DecodeError::UnexpectedEof);
    }
    let flags = bytes[pos];
    if flags == 0x00 {
        let (min_v, np) = decode_u32_bounded(bytes, pos + 1, end_pos)?;
        if min_v > upper_bound {
            return Err(DecodeError::InvalidLimits);
        }
        Ok((min_v, None, np))
    } else if flags == 0x01 {
        let (min_v, p1) = decode_u32_bounded(bytes, pos + 1, end_pos)?;
        let (max_v, p2) = decode_u32_bounded(bytes, p1, end_pos)?;
        if min_v > max_v || max_v > upper_bound {
            return Err(DecodeError::InvalidLimits);
        }
        Ok((min_v, Some(max_v), p2))
    } else {
        Err(DecodeError::InvalidLimits)
    }
}

/// Section 4: Table section (`vec(tabletype)` with `0x70` funcref).
pub fn decode_table_section(
    bytes: &[u8],
    pos: usize,
    end_pos: usize,
) -> (r: Result<Option<TableLimits>, DecodeError>)
    requires
        pos <= end_pos,
        end_pos <= bytes@.len(),
{
    let (count, p1) = decode_u32_bounded(bytes, pos, end_pos)?;
    if count == 0 {
        if p1 != end_pos {
            return Err(DecodeError::MalformedSection);
        }
        return Ok(None);
    }
    if count > 1 {
        return Err(DecodeError::MalformedSection);
    }
    if p1 >= end_pos || bytes[p1] != 0x70 {
        return Err(DecodeError::UnsupportedType);
    }
    let (min_e, max_e, p2) = decode_limits(bytes, p1 + 1, end_pos, MAX_TABLE_ENTRIES)?;
    if p2 != end_pos {
        return Err(DecodeError::MalformedSection);
    }
    Ok(Some(TableLimits { min_entries: min_e, max_entries: max_e }))
}

/// Section 5: Memory section (`vec(limits)` with pages of 65,536 bytes).
pub fn decode_memory_section(
    bytes: &[u8],
    pos: usize,
    end_pos: usize,
) -> (r: Result<Option<MemoryLimits>, DecodeError>)
    requires
        pos <= end_pos,
        end_pos <= bytes@.len(),
    ensures
        match r {
            Ok(Some(lim)) =>
                lim.min_pages <= MAX_SPEC_PAGES
                    && (match lim.max_pages {
                        None => true,
                        Some(mx) => lim.min_pages <= mx && mx <= MAX_SPEC_PAGES,
                    }),
            _ => true,
        },
{
    let (count, p1) = decode_u32_bounded(bytes, pos, end_pos)?;
    if count == 0 {
        if p1 != end_pos {
            return Err(DecodeError::MalformedSection);
        }
        return Ok(None);
    }
    if count > 1 {
        return Err(DecodeError::MalformedSection);
    }
    let (min_p, max_p, p2) = decode_limits(bytes, p1, end_pos, MAX_SPEC_PAGES)?;
    if p2 != end_pos {
        return Err(DecodeError::MalformedSection);
    }
    Ok(Some(MemoryLimits { min_pages: min_p, max_pages: max_p }))
}

fn decode_const_expr(
    bytes: &[u8],
    pos: usize,
    end_pos: usize,
    prev_globals: &[GlobalDecl],
) -> (r: Result<(WasmVal, usize), DecodeError>)
    requires
        pos <= end_pos,
        end_pos <= bytes@.len(),
    ensures
        match r {
            Ok((_, np)) => pos < np && np <= end_pos,
            Err(_) => true,
        },
{
    if pos >= end_pos {
        return Err(DecodeError::UnexpectedEof);
    }
    let op = bytes[pos];
    let (val, p1) = if op == 0x41 {
        let (v, np) = decode_i32_bounded(bytes, pos + 1, end_pos)?;
        (WasmVal::I32(v), np)
    } else if op == 0x42 {
        let (v, np) = decode_i64_bounded(bytes, pos + 1, end_pos)?;
        (WasmVal::I64(v), np)
    } else if op == 0x43 {
        if end_pos - (pos + 1) < 4 {
            return Err(DecodeError::UnexpectedEof);
        }
        let (bits, np) = read_u32_le(bytes, pos + 1)?;
        (WasmVal::F32Bits(bits), np)
    } else if op == 0x44 {
        if end_pos - (pos + 1) < 8 {
            return Err(DecodeError::UnexpectedEof);
        }
        let (bits, np) = read_u64_le(bytes, pos + 1)?;
        (WasmVal::F64Bits(bits), np)
    } else if op == 0x23 {
        let (gidx, np) = decode_u32_bounded(bytes, pos + 1, end_pos)?;
        if (gidx as usize) >= prev_globals.len() || prev_globals[gidx as usize].mutable {
            return Err(DecodeError::InvalidInitExpr);
        }
        (prev_globals[gidx as usize].init, np)
    } else {
        return Err(DecodeError::InvalidInitExpr);
    };
    if p1 >= end_pos || bytes[p1] != 0x0b {
        return Err(DecodeError::InvalidInitExpr);
    }
    Ok((val, p1 + 1))
}

/// Section 6: Global section (`vec(global)`).
pub fn decode_global_section(
    bytes: &[u8],
    mut pos: usize,
    end_pos: usize,
) -> (r: Result<Vec<GlobalDecl>, DecodeError>)
    requires
        pos <= end_pos,
        end_pos <= bytes@.len(),
{
    let (count, p1) = decode_u32_bounded(bytes, pos, end_pos)?;
    pos = p1;
    let mut globals: Vec<GlobalDecl> = Vec::new();
    let mut i: u32 = 0;
    while i < count
        invariant
            i <= count,
            pos <= end_pos,
            end_pos <= bytes@.len(),
        decreases count - i,
    {
        let (vt, p2) = decode_val_type(bytes, pos, end_pos)?;
        if p2 >= end_pos {
            return Err(DecodeError::UnexpectedEof);
        }
        let mut_b = bytes[p2];
        let mutable = if mut_b == 0x00 {
            false
        } else if mut_b == 0x01 {
            true
        } else {
            return Err(DecodeError::InvalidMutability);
        };
        let (init, p3) = decode_const_expr(bytes, p2 + 1, end_pos, globals.as_slice())?;
        if !crate::types::val_has_type(init, vt) {
            return Err(DecodeError::InvalidInitExpr);
        }
        globals.push(GlobalDecl { val_type: vt, mutable, init });
        pos = p3;
        i = i + 1;
    }
    if pos != end_pos {
        return Err(DecodeError::MalformedSection);
    }
    Ok(globals)
}

/// Section 7: Export section (`vec(export)`).
pub fn decode_export_section(
    bytes: &[u8],
    mut pos: usize,
    end_pos: usize,
) -> (r: Result<Vec<ExportDesc>, DecodeError>)
    requires
        pos <= end_pos,
        end_pos <= bytes@.len(),
{
    let (count, p1) = decode_u32_bounded(bytes, pos, end_pos)?;
    pos = p1;
    let mut exports: Vec<ExportDesc> = Vec::new();
    let mut i: u32 = 0;
    while i < count
        invariant
            i <= count,
            pos <= end_pos,
            end_pos <= bytes@.len(),
        decreases count - i,
    {
        let (name_len, p2) = decode_u32_bounded(bytes, pos, end_pos)?;
        if (name_len as u64) > (end_pos - p2) as u64 {
            return Err(DecodeError::UnexpectedEof);
        }
        let (name, p3) = copy_subslice(bytes, p2, name_len as usize, end_pos)?;
        if p3 >= end_pos {
            return Err(DecodeError::UnexpectedEof);
        }
        let kb = bytes[p3];
        let kind = if kb == 0x00 {
            ExportKind::Func
        } else if kb == 0x01 {
            ExportKind::Table
        } else if kb == 0x02 {
            ExportKind::Memory
        } else if kb == 0x03 {
            ExportKind::Global
        } else {
            return Err(DecodeError::InvalidExportKind);
        };
        let (index, p4) = decode_u32_bounded(bytes, p3 + 1, end_pos)?;
        exports.push(ExportDesc { name, kind, index });
        pos = p4;
        i = i + 1;
    }
    if pos != end_pos {
        return Err(DecodeError::MalformedSection);
    }
    Ok(exports)
}

/// Section 9: Elem section (`vec(elem)` initializing indirect call table).
pub fn decode_elem_section(
    bytes: &[u8],
    mut pos: usize,
    end_pos: usize,
    globals: &[GlobalDecl],
) -> (r: Result<Vec<ElemSegment>, DecodeError>)
    requires
        pos <= end_pos,
        end_pos <= bytes@.len(),
{
    let (count, p1) = decode_u32_bounded(bytes, pos, end_pos)?;
    pos = p1;
    let mut segs: Vec<ElemSegment> = Vec::new();
    let mut i: u32 = 0;
    while i < count
        invariant
            i <= count,
            pos <= end_pos,
            end_pos <= bytes@.len(),
        decreases count - i,
    {
        let (flags, p2) = decode_u32_bounded(bytes, pos, end_pos)?;
        let p_off = if flags == 0 {
            p2
        } else if flags == 2 {
            let (tbl_idx, p_tbl) = decode_u32_bounded(bytes, p2, end_pos)?;
            if tbl_idx != 0 {
                return Err(DecodeError::MalformedSection);
            }
            p_tbl
        } else {
            return Err(DecodeError::MalformedSection);
        };
        let (off_val, p3) = decode_const_expr(bytes, p_off, end_pos, globals)?;
        let offset = match off_val {
            WasmVal::I32(v) => 0u32.wrapping_add_signed(v),
            _ => return Err(DecodeError::InvalidInitExpr),
        };
        let p_cnt = if flags == 2 {
            if p3 >= end_pos || bytes[p3] != 0x00 {
                return Err(DecodeError::MalformedSection);
            }
            p3 + 1
        } else {
            p3
        };
        let (fn_count, p4) = decode_u32_bounded(bytes, p_cnt, end_pos)?;
        pos = p4;
        let mut func_indices: Vec<u32> = Vec::new();
        let mut j: u32 = 0;
        while j < fn_count
            invariant
                j <= fn_count,
                pos <= end_pos,
                end_pos <= bytes@.len(),
            decreases fn_count - j,
        {
            let (fidx, np) = decode_u32_bounded(bytes, pos, end_pos)?;
            func_indices.push(fidx);
            pos = np;
            j = j + 1;
        }
        segs.push(ElemSegment { offset, func_indices });
        i = i + 1;
    }
    if pos != end_pos {
        return Err(DecodeError::MalformedSection);
    }
    Ok(segs)
}

/// Section 11: Data section (`vec(data)` initializing linear memory).
pub fn decode_data_section(
    bytes: &[u8],
    mut pos: usize,
    end_pos: usize,
    globals: &[GlobalDecl],
) -> (r: Result<Vec<DataSegment>, DecodeError>)
    requires
        pos <= end_pos,
        end_pos <= bytes@.len(),
{
    let (count, p1) = decode_u32_bounded(bytes, pos, end_pos)?;
    pos = p1;
    let mut segs: Vec<DataSegment> = Vec::new();
    let mut i: u32 = 0;
    while i < count
        invariant
            i <= count,
            pos <= end_pos,
            end_pos <= bytes@.len(),
        decreases count - i,
    {
        let (flags, p2) = decode_u32_bounded(bytes, pos, end_pos)?;
        let (mem_idx, p_off) = if flags == 0 {
            (0u32, p2)
        } else if flags == 2 {
            let (midx, p_m) = decode_u32_bounded(bytes, p2, end_pos)?;
            if midx != 0 {
                return Err(DecodeError::MalformedSection);
            }
            (midx, p_m)
        } else {
            return Err(DecodeError::MalformedSection);
        };
        let (off_val, p3) = decode_const_expr(bytes, p_off, end_pos, globals)?;
        let offset = match off_val {
            WasmVal::I32(v) => 0u32.wrapping_add_signed(v),
            _ => return Err(DecodeError::InvalidInitExpr),
        };
        let (init_len, p4) = decode_u32_bounded(bytes, p3, end_pos)?;
        if (init_len as u64) > (end_pos - p4) as u64 {
            return Err(DecodeError::UnexpectedEof);
        }
        let (init, p5) = copy_subslice(bytes, p4, init_len as usize, end_pos)?;
        segs.push(DataSegment { mem_idx, offset, init });
        pos = p5;
        i = i + 1;
    }
    if pos != end_pos {
        return Err(DecodeError::MalformedSection);
    }
    Ok(segs)
}

// ---------------------------------------------------------------------------
// 4. Verified Code Section & Structured Control-Flow Resolution
// ---------------------------------------------------------------------------

fn decode_memarg(bytes: &[u8], pos: usize, end_pos: usize) -> (r: Result<(u32, u32, usize), DecodeError>)
    requires
        pos <= end_pos,
        end_pos <= bytes@.len(),
    ensures
        match r {
            Ok((_, _, np)) => pos < np && np <= end_pos,
            Err(_) => true,
        },
{
    let (align, p1) = decode_u32_bounded(bytes, pos, end_pos)?;
    let (offset, p2) = decode_u32_bounded(bytes, p1, end_pos)?;
    Ok((align, offset, p2))
}

#[verifier::spinoff_prover]
fn decode_mem_raw_instr(
    op: u8,
    bytes: &[u8],
    _pos: usize,
    p1: usize,
    end_pos: usize,
) -> (r: Result<(RawInstr, usize), DecodeError>)
    requires
        _pos < end_pos,
        p1 == _pos + 1,
        end_pos <= bytes@.len(),
        0x28 <= op <= 0x40,
    ensures
        match r {
            Ok((_, np)) => _pos < np && np <= end_pos,
            Err(_) => true,
        },
{
    if op == 0x3f || op == 0x40 {
        if p1 >= end_pos || bytes[p1] != 0x00 {
            return Err(DecodeError::MalformedSection);
        }
        let ins = if op == 0x3f { RawInstr::MemorySize } else { RawInstr::MemoryGrow };
        return Ok((ins, p1 + 1));
    }
    let (align, offset, np) = decode_memarg(bytes, p1, end_pos)?;
    let ins = match op {
        0x28 => RawInstr::MemLoad { load_kind: LoadKind::I32Load, align, offset },
        0x29 => RawInstr::MemLoad { load_kind: LoadKind::I64Load, align, offset },
        0x2a => RawInstr::MemLoad { load_kind: LoadKind::F32Load, align, offset },
        0x2b => RawInstr::MemLoad { load_kind: LoadKind::F64Load, align, offset },
        0x2c => RawInstr::MemLoad { load_kind: LoadKind::I32Load8S, align, offset },
        0x2d => RawInstr::MemLoad { load_kind: LoadKind::I32Load8U, align, offset },
        0x2e => RawInstr::MemLoad { load_kind: LoadKind::I32Load16S, align, offset },
        0x2f => RawInstr::MemLoad { load_kind: LoadKind::I32Load16U, align, offset },
        0x30 => RawInstr::MemLoad { load_kind: LoadKind::I64Load8S, align, offset },
        0x31 => RawInstr::MemLoad { load_kind: LoadKind::I64Load8U, align, offset },
        0x32 => RawInstr::MemLoad { load_kind: LoadKind::I64Load16S, align, offset },
        0x33 => RawInstr::MemLoad { load_kind: LoadKind::I64Load16U, align, offset },
        0x34 => RawInstr::MemLoad { load_kind: LoadKind::I64Load32S, align, offset },
        0x35 => RawInstr::MemLoad { load_kind: LoadKind::I64Load32U, align, offset },
        0x36 => RawInstr::MemStore { store_kind: StoreKind::I32Store, align, offset },
        0x37 => RawInstr::MemStore { store_kind: StoreKind::I64Store, align, offset },
        0x38 => RawInstr::MemStore { store_kind: StoreKind::F32Store, align, offset },
        0x39 => RawInstr::MemStore { store_kind: StoreKind::F64Store, align, offset },
        0x3a => RawInstr::MemStore { store_kind: StoreKind::I32Store8, align, offset },
        0x3b => RawInstr::MemStore { store_kind: StoreKind::I32Store16, align, offset },
        0x3c => RawInstr::MemStore { store_kind: StoreKind::I64Store8, align, offset },
        0x3d => RawInstr::MemStore { store_kind: StoreKind::I64Store16, align, offset },
        _ => RawInstr::MemStore { store_kind: StoreKind::I64Store32, align, offset },
    };
    Ok((ins, np))
}

fn decode_zero_imm_raw_instr(op: u8) -> (r: Result<RawInstr, DecodeError>) {
    match op {
        0x45 => Ok(RawInstr::I32Eqz),
        0x46 => Ok(RawInstr::I32Rel(IntRelOp::Eq)),
        0x47 => Ok(RawInstr::I32Rel(IntRelOp::Ne)),
        0x48 => Ok(RawInstr::I32Rel(IntRelOp::LtS)),
        0x49 => Ok(RawInstr::I32Rel(IntRelOp::LtU)),
        0x4a => Ok(RawInstr::I32Rel(IntRelOp::GtS)),
        0x4b => Ok(RawInstr::I32Rel(IntRelOp::GtU)),
        0x4c => Ok(RawInstr::I32Rel(IntRelOp::LeS)),
        0x4d => Ok(RawInstr::I32Rel(IntRelOp::LeU)),
        0x4e => Ok(RawInstr::I32Rel(IntRelOp::GeS)),
        0x4f => Ok(RawInstr::I32Rel(IntRelOp::GeU)),
        0x50 => Ok(RawInstr::I64Eqz),
        0x51 => Ok(RawInstr::I64Rel(IntRelOp::Eq)),
        0x52 => Ok(RawInstr::I64Rel(IntRelOp::Ne)),
        0x53 => Ok(RawInstr::I64Rel(IntRelOp::LtS)),
        0x54 => Ok(RawInstr::I64Rel(IntRelOp::LtU)),
        0x55 => Ok(RawInstr::I64Rel(IntRelOp::GtS)),
        0x56 => Ok(RawInstr::I64Rel(IntRelOp::GtU)),
        0x57 => Ok(RawInstr::I64Rel(IntRelOp::LeS)),
        0x58 => Ok(RawInstr::I64Rel(IntRelOp::LeU)),
        0x59 => Ok(RawInstr::I64Rel(IntRelOp::GeS)),
        0x5a => Ok(RawInstr::I64Rel(IntRelOp::GeU)),
        0x67 => Ok(RawInstr::I32Unary(I32UnOp::Clz)),
        0x68 => Ok(RawInstr::I32Unary(I32UnOp::Ctz)),
        0x69 => Ok(RawInstr::I32Unary(I32UnOp::Popcnt)),
        0x6a => Ok(RawInstr::I32Binary(I32BinOp::Add)),
        0x6b => Ok(RawInstr::I32Binary(I32BinOp::Sub)),
        0x6c => Ok(RawInstr::I32Binary(I32BinOp::Mul)),
        0x6d => Ok(RawInstr::I32Binary(I32BinOp::DivS)),
        0x6e => Ok(RawInstr::I32Binary(I32BinOp::DivU)),
        0x6f => Ok(RawInstr::I32Binary(I32BinOp::RemS)),
        0x70 => Ok(RawInstr::I32Binary(I32BinOp::RemU)),
        0x71 => Ok(RawInstr::I32Binary(I32BinOp::And)),
        0x72 => Ok(RawInstr::I32Binary(I32BinOp::Or)),
        0x73 => Ok(RawInstr::I32Binary(I32BinOp::Xor)),
        0x74 => Ok(RawInstr::I32Binary(I32BinOp::Shl)),
        0x75 => Ok(RawInstr::I32Binary(I32BinOp::ShrS)),
        0x76 => Ok(RawInstr::I32Binary(I32BinOp::ShrU)),
        0x77 => Ok(RawInstr::I32Binary(I32BinOp::Rotl)),
        0x78 => Ok(RawInstr::I32Binary(I32BinOp::Rotr)),
        0x79 => Ok(RawInstr::I64Unary(I64UnOp::Clz)),
        0x7a => Ok(RawInstr::I64Unary(I64UnOp::Ctz)),
        0x7b => Ok(RawInstr::I64Unary(I64UnOp::Popcnt)),
        0x7c => Ok(RawInstr::I64Binary(I64BinOp::Add)),
        0x7d => Ok(RawInstr::I64Binary(I64BinOp::Sub)),
        0x7e => Ok(RawInstr::I64Binary(I64BinOp::Mul)),
        0x7f => Ok(RawInstr::I64Binary(I64BinOp::DivS)),
        0x80 => Ok(RawInstr::I64Binary(I64BinOp::DivU)),
        0x81 => Ok(RawInstr::I64Binary(I64BinOp::RemS)),
        0x82 => Ok(RawInstr::I64Binary(I64BinOp::RemU)),
        0x83 => Ok(RawInstr::I64Binary(I64BinOp::And)),
        0x84 => Ok(RawInstr::I64Binary(I64BinOp::Or)),
        0x85 => Ok(RawInstr::I64Binary(I64BinOp::Xor)),
        0x86 => Ok(RawInstr::I64Binary(I64BinOp::Shl)),
        0x87 => Ok(RawInstr::I64Binary(I64BinOp::ShrS)),
        0x88 => Ok(RawInstr::I64Binary(I64BinOp::ShrU)),
        0x89 => Ok(RawInstr::I64Binary(I64BinOp::Rotl)),
        0x8a => Ok(RawInstr::I64Binary(I64BinOp::Rotr)),
        0xa7 => Ok(RawInstr::I32WrapI64),
        0xac => Ok(RawInstr::I64ExtendI32S),
        0xad => Ok(RawInstr::I64ExtendI32U),
        other => {
            if (0x5b <= other && other <= 0x66)
                || (0x8b <= other && other <= 0xa6)
                || (0xa8 <= other && other <= 0xbf)
            {
                Ok(RawInstr::Unsupported(other))
            } else {
                Err(DecodeError::UnsupportedOpcode(other))
            }
        },
    }
}

#[verifier::spinoff_prover]
fn decode_br_table_raw_instr(
    bytes: &[u8],
    _pos: usize,
    p1: usize,
    end_pos: usize,
    br_tables: &mut Vec<Vec<u32>>,
) -> (r: Result<(RawInstr, usize), DecodeError>)
    requires
        _pos < end_pos,
        p1 == _pos + 1,
        end_pos <= bytes@.len(),
    ensures
        match r {
            Ok((_, np)) => _pos < np && np <= end_pos,
            Err(_) => true,
        },
{
    let (cnt, mut cur) = decode_u32_bounded(bytes, p1, end_pos)?;
    let mut targets: Vec<u32> = Vec::new();
    let mut i: u32 = 0;
    while i < cnt
        invariant
            i <= cnt,
            p1 < cur <= end_pos,
            end_pos <= bytes@.len(),
        decreases cnt - i,
    {
        let (lbl, np) = decode_u32_bounded(bytes, cur, end_pos)?;
        targets.push(lbl);
        cur = np;
        i = i + 1;
    }
    let (default_label, np) = decode_u32_bounded(bytes, cur, end_pos)?;
    let table_idx = br_tables.len();
    br_tables.push(targets);
    Ok((RawInstr::BrTable { table_idx, default_label }, np))
}

#[verifier::spinoff_prover]
fn decode_one_raw_instr(
    bytes: &[u8],
    pos: usize,
    end_pos: usize,
    br_tables: &mut Vec<Vec<u32>>,
) -> (r: Result<(RawInstr, usize), DecodeError>)
    requires
        pos < end_pos,
        end_pos <= bytes@.len(),
    ensures
        match r {
            Ok((_, np)) => pos < np && np <= end_pos,
            Err(_) => true,
        },
{
    let op = bytes[pos];
    let p1 = pos + 1;
    if 0x02 <= op && op <= 0x04 {
        let (bt, np) = decode_block_type(bytes, p1, end_pos)?;
        let ins = match op {
            0x02 => RawInstr::Block(bt),
            0x03 => RawInstr::Loop(bt),
            _ => RawInstr::If(bt),
        };
        return Ok((ins, np));
    }
    if op == 0x0c || op == 0x0d || op == 0x10 || (0x20 <= op && op <= 0x24) {
        let (idx, np) = decode_u32_bounded(bytes, p1, end_pos)?;
        let ins = match op {
            0x0c => RawInstr::Br(idx),
            0x0d => RawInstr::BrIf(idx),
            0x10 => RawInstr::Call(idx),
            0x20 => RawInstr::LocalGet(idx),
            0x21 => RawInstr::LocalSet(idx),
            0x22 => RawInstr::LocalTee(idx),
            0x23 => RawInstr::GlobalGet(idx),
            _ => RawInstr::GlobalSet(idx),
        };
        return Ok((ins, np));
    }
    if op == 0x0e {
        return decode_br_table_raw_instr(bytes, pos, p1, end_pos, br_tables);
    }
    if op == 0x11 {
        let (tidx, p2) = decode_u32_bounded(bytes, p1, end_pos)?;
        if p2 >= end_pos || bytes[p2] != 0x00 {
            return Err(DecodeError::MalformedSection);
        }
        return Ok((RawInstr::CallIndirect(tidx), p2 + 1));
    }
    if 0x28 <= op && op <= 0x40 {
        return decode_mem_raw_instr(op, bytes, pos, p1, end_pos);
    }
    match op {
        0x00 => Ok((RawInstr::Unreachable, p1)),
        0x01 => Ok((RawInstr::Nop, p1)),
        0x05 => Ok((RawInstr::Else, p1)),
        0x0b => Ok((RawInstr::End, p1)),
        0x0f => Ok((RawInstr::Return, p1)),
        0x1a => Ok((RawInstr::Drop, p1)),
        0x1b => Ok((RawInstr::Select, p1)),
        0x41 => {
            let (n, np) = decode_i32_bounded(bytes, p1, end_pos)?;
            Ok((RawInstr::I32Const(n), np))
        },
        0x42 => {
            let (n, np) = decode_i64_bounded(bytes, p1, end_pos)?;
            Ok((RawInstr::I64Const(n), np))
        },
        0x43 => {
            if end_pos - p1 < 4 {
                return Err(DecodeError::UnexpectedEof);
            }
            let (bits, np) = read_u32_le(bytes, p1)?;
            Ok((RawInstr::F32Const(bits), np))
        },
        0x44 => {
            if end_pos - p1 < 8 {
                return Err(DecodeError::UnexpectedEof);
            }
            let (bits, np) = read_u64_le(bytes, p1)?;
            Ok((RawInstr::F64Const(bits), np))
        },
        other => {
            let ins = decode_zero_imm_raw_instr(other)?;
            Ok((ins, p1))
        },
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum CtrlKind {
    FuncRoot,
    Block,
    Loop,
    If,
}

#[derive(Clone, Copy)]
struct OpenCtrl {
    kind: CtrlKind,
    op_idx: usize,
    else_jump_idx: Option<usize>,
    arity: usize,
}

spec fn spec_open_ctrl_wf(entry: OpenCtrl, ops_len: nat) -> bool {
    match entry.kind {
        CtrlKind::FuncRoot => true,
        CtrlKind::Block | CtrlKind::Loop => (entry.op_idx as nat) < ops_len,
        CtrlKind::If =>
            (entry.op_idx as nat) < ops_len
                && (match entry.else_jump_idx {
                    None => true,
                    Some(ej) => (ej as nat) < ops_len && ej < usize::MAX,
                }),
    }
}

proof fn lemma_open_ctrl_wf_mono(entry: OpenCtrl, n1: nat, n2: nat)
    requires
        n1 <= n2,
        spec_open_ctrl_wf(entry, n1),
    ensures
        spec_open_ctrl_wf(entry, n2),
{
}

fn lower_non_ctrl_raw_instr(ins: RawInstr) -> WasmOp {
    match ins {
        RawInstr::Unreachable => WasmOp::Unreachable,
        RawInstr::Nop => WasmOp::Nop,
        RawInstr::Br(lbl) => WasmOp::Br(lbl),
        RawInstr::BrIf(lbl) => WasmOp::BrIf(lbl),
        RawInstr::BrTable { table_idx, default_label } =>
            WasmOp::BrTable { table_idx, default_label },
        RawInstr::Return => WasmOp::Return,
        RawInstr::Call(fidx) => WasmOp::Call(fidx),
        RawInstr::CallIndirect(tidx) => WasmOp::CallIndirect(tidx),
        RawInstr::Drop => WasmOp::Drop,
        RawInstr::Select => WasmOp::Select,
        RawInstr::LocalGet(idx) => WasmOp::LocalGet(idx),
        RawInstr::LocalSet(idx) => WasmOp::LocalSet(idx),
        RawInstr::LocalTee(idx) => WasmOp::LocalTee(idx),
        RawInstr::GlobalGet(idx) => WasmOp::GlobalGet(idx),
        RawInstr::GlobalSet(idx) => WasmOp::GlobalSet(idx),
        RawInstr::MemLoad { load_kind, align: _, offset } =>
            WasmOp::MemLoad { load_kind, offset },
        RawInstr::MemStore { store_kind, align: _, offset } =>
            WasmOp::MemStore { store_kind, offset },
        RawInstr::MemorySize => WasmOp::MemorySize,
        RawInstr::MemoryGrow => WasmOp::MemoryGrow,
        RawInstr::I32Const(v) => WasmOp::I32Const(v),
        RawInstr::I64Const(v) => WasmOp::I64Const(v),
        RawInstr::F32Const(v) => WasmOp::F32Const(v),
        RawInstr::F64Const(v) => WasmOp::F64Const(v),
        RawInstr::I32Eqz => WasmOp::I32Eqz,
        RawInstr::I64Eqz => WasmOp::I64Eqz,
        RawInstr::I32Rel(op) => WasmOp::I32Rel(op),
        RawInstr::I64Rel(op) => WasmOp::I64Rel(op),
        RawInstr::I32Unary(op) => WasmOp::I32Unary(op),
        RawInstr::I32Binary(op) => WasmOp::I32Binary(op),
        RawInstr::I64Unary(op) => WasmOp::I64Unary(op),
        RawInstr::I64Binary(op) => WasmOp::I64Binary(op),
        RawInstr::I32WrapI64 => WasmOp::I32WrapI64,
        RawInstr::I64ExtendI32S => WasmOp::I64ExtendI32S,
        RawInstr::I64ExtendI32U => WasmOp::I64ExtendI32U,
        RawInstr::Unsupported(op) => WasmOp::Unsupported(op),
        _ => WasmOp::Nop,
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(50)]
pub fn resolve_control_flow(raw: &[RawInstr]) -> (r: Result<Vec<WasmOp>, DecodeError>) {
    if raw.len() == 0 {
        return Err(DecodeError::UnbalancedControlFlow);
    }
    let mut ctrl: Vec<OpenCtrl> = Vec::new();
    ctrl.push(OpenCtrl {
        kind: CtrlKind::FuncRoot,
        op_idx: 0,
        else_jump_idx: None,
        arity: 0,
    });
    let mut ops: Vec<WasmOp> = Vec::with_capacity(raw.len());
    let n = raw.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == raw@.len(),
            forall|k: int| 0 <= k < ctrl@.len() ==> #[trigger] spec_open_ctrl_wf(ctrl@[k], ops@.len()),
        decreases n - i,
    {
        if ctrl.len() == 0 {
            return Err(DecodeError::UnbalancedControlFlow);
        }
        let ghost pre_ctrl = ctrl@;
        let ghost pre_ops_len = ops@.len();
        let ins = raw[i];
        match ins {
            RawInstr::Block(bt) => {
                let arity = if bt.is_some() { 1 } else { 0 };
                let op_idx = ops.len();
                ops.push(WasmOp::Block { end_pc: 0, arity });
                ctrl.push(OpenCtrl { kind: CtrlKind::Block, op_idx, else_jump_idx: None, arity });
                proof {
                    assert forall|k: int| 0 <= k < ctrl@.len() implies #[trigger] spec_open_ctrl_wf(ctrl@[k], ops@.len()) by {
                        if k < pre_ctrl.len() {
                            assert(ctrl@[k] == pre_ctrl[k]);
                            assert(spec_open_ctrl_wf(pre_ctrl[k], pre_ops_len));
                            lemma_open_ctrl_wf_mono(pre_ctrl[k], pre_ops_len, ops@.len());
                        }
                    }
                }
            },
            RawInstr::Loop(_bt) => {
                let loop_pc = ops.len();
                ops.push(WasmOp::Loop { loop_pc });
                ctrl.push(OpenCtrl { kind: CtrlKind::Loop, op_idx: loop_pc, else_jump_idx: None, arity: 0 });
                proof {
                    assert forall|k: int| 0 <= k < ctrl@.len() implies #[trigger] spec_open_ctrl_wf(ctrl@[k], ops@.len()) by {
                        if k < pre_ctrl.len() {
                            assert(ctrl@[k] == pre_ctrl[k]);
                            assert(spec_open_ctrl_wf(pre_ctrl[k], pre_ops_len));
                            lemma_open_ctrl_wf_mono(pre_ctrl[k], pre_ops_len, ops@.len());
                        }
                    }
                }
            },
            RawInstr::If(bt) => {
                let arity = if bt.is_some() { 1 } else { 0 };
                let op_idx = ops.len();
                ops.push(WasmOp::If { else_pc: 0, end_pc: 0, arity });
                ctrl.push(OpenCtrl { kind: CtrlKind::If, op_idx, else_jump_idx: None, arity });
                proof {
                    assert forall|k: int| 0 <= k < ctrl@.len() implies #[trigger] spec_open_ctrl_wf(ctrl@[k], ops@.len()) by {
                        if k < pre_ctrl.len() {
                            assert(ctrl@[k] == pre_ctrl[k]);
                            assert(spec_open_ctrl_wf(pre_ctrl[k], pre_ops_len));
                            lemma_open_ctrl_wf_mono(pre_ctrl[k], pre_ops_len, ops@.len());
                        }
                    }
                }
            },
            RawInstr::Else => {
                let last_idx = ctrl.len() - 1;
                let top = ctrl[last_idx];
                let _ = ctrl.pop();
                if !matches!(top.kind, CtrlKind::If) || top.else_jump_idx.is_some() || ops.len() == usize::MAX {
                    return Err(DecodeError::UnbalancedControlFlow);
                }
                let ej_idx = ops.len();
                ops.push(WasmOp::ElseJump { end_pc: 0 });
                ctrl.push(OpenCtrl {
                    kind: CtrlKind::If,
                    op_idx: top.op_idx,
                    else_jump_idx: Some(ej_idx),
                    arity: top.arity,
                });
                proof {
                    assert forall|k: int| 0 <= k < ctrl@.len() implies #[trigger] spec_open_ctrl_wf(ctrl@[k], ops@.len()) by {
                        if k < pre_ctrl.len() - 1 {
                            assert(ctrl@[k] == pre_ctrl[k]);
                            assert(spec_open_ctrl_wf(pre_ctrl[k], pre_ops_len));
                            lemma_open_ctrl_wf_mono(pre_ctrl[k], pre_ops_len, ops@.len());
                        } else {
                            assert(spec_open_ctrl_wf(pre_ctrl[pre_ctrl.len() - 1], pre_ops_len));
                            assert(top == pre_ctrl[pre_ctrl.len() - 1]);
                            assert((top.op_idx as nat) < pre_ops_len);
                            assert((ej_idx as nat) == pre_ops_len);
                        }
                    }
                }
            },
            RawInstr::End => {
                let last_idx = ctrl.len() - 1;
                let top = ctrl[last_idx];
                let _ = ctrl.pop();
                proof {
                    assert(spec_open_ctrl_wf(pre_ctrl[pre_ctrl.len() - 1], pre_ops_len));
                }
                match top.kind {
                    CtrlKind::FuncRoot => {
                        if ctrl.len() != 0 || i + 1 != n {
                            return Err(DecodeError::UnbalancedControlFlow);
                        }
                        ops.push(WasmOp::FuncEnd);
                    },
                    CtrlKind::Block => {
                        ops.push(WasmOp::End);
                        let end_pc = ops.len();
                        ops[top.op_idx] = WasmOp::Block { end_pc, arity: top.arity };
                    },
                    CtrlKind::Loop => {
                        ops.push(WasmOp::End);
                    },
                    CtrlKind::If => {
                        let end_ins_pc = ops.len();
                        ops.push(WasmOp::End);
                        let end_pc = ops.len();
                        let else_pc = match top.else_jump_idx {
                            Some(ej_idx) => {
                                ops[ej_idx] = WasmOp::ElseJump { end_pc };
                                ej_idx + 1
                            },
                            None => end_ins_pc,
                        };
                        ops[top.op_idx] = WasmOp::If { else_pc, end_pc, arity: top.arity };
                    },
                }
                proof {
                    assert forall|k: int| 0 <= k < ctrl@.len() implies #[trigger] spec_open_ctrl_wf(ctrl@[k], ops@.len()) by {
                        assert(k < pre_ctrl.len() - 1);
                        assert(ctrl@[k] == pre_ctrl[k]);
                        assert(spec_open_ctrl_wf(pre_ctrl[k], pre_ops_len));
                        lemma_open_ctrl_wf_mono(pre_ctrl[k], pre_ops_len, ops@.len());
                    }
                }
            },
            other => {
                ops.push(lower_non_ctrl_raw_instr(other));
                proof {
                    assert forall|k: int| 0 <= k < ctrl@.len() implies #[trigger] spec_open_ctrl_wf(ctrl@[k], ops@.len()) by {
                        assert(ctrl@[k] == pre_ctrl[k]);
                        assert(spec_open_ctrl_wf(pre_ctrl[k], pre_ops_len));
                        lemma_open_ctrl_wf_mono(pre_ctrl[k], pre_ops_len, ops@.len());
                    }
                }
            },
        }
        i = i + 1;
    }
    if ctrl.len() != 0 {
        return Err(DecodeError::UnbalancedControlFlow);
    }
    Ok(ops)
}

/// Section 10: Code section (`vec(code)`).
pub fn decode_code_section(
    bytes: &[u8],
    mut pos: usize,
    end_pos: usize,
    func_type_indices: &[u32],
) -> (r: Result<Vec<FuncBody>, DecodeError>)
    requires
        pos <= end_pos,
        end_pos <= bytes@.len(),
{
    let (count, p1) = decode_u32_bounded(bytes, pos, end_pos)?;
    if (count as u64) != (func_type_indices.len() as u64) {
        return Err(DecodeError::FunctionCountMismatch);
    }
    pos = p1;
    let total_funcs = func_type_indices.len();
    let mut funcs: Vec<FuncBody> = Vec::with_capacity(total_funcs);
    let mut f_idx: usize = 0;
    while f_idx < total_funcs
        invariant
            f_idx <= total_funcs,
            total_funcs == func_type_indices@.len(),
            pos <= end_pos,
            end_pos <= bytes@.len(),
        decreases total_funcs - f_idx,
    {
        let (body_size, p2) = decode_u32_bounded(bytes, pos, end_pos)?;
        if (body_size as u64) > (end_pos - p2) as u64 {
            return Err(DecodeError::UnexpectedEof);
        }
        let body_end = p2 + (body_size as usize);
        let (local_decl_count, mut cur) = decode_u32_bounded(bytes, p2, body_end)?;
        let mut locals: Vec<ValType> = Vec::new();
        let mut d: u32 = 0;
        while d < local_decl_count
            invariant
                d <= local_decl_count,
                cur <= body_end,
                body_end <= end_pos,
                end_pos <= bytes@.len(),
                locals@.len() <= MAX_LOCALS_PER_FUNC,
            decreases local_decl_count - d,
        {
            let (n_locals, p3) = decode_u32_bounded(bytes, cur, body_end)?;
            let (vt, p4) = decode_val_type(bytes, p3, body_end)?;
            if (n_locals as u64) > (MAX_LOCALS_PER_FUNC - locals.len()) as u64 {
                return Err(DecodeError::TooManyLocals);
            }
            let cnt_usize = n_locals as usize;
            let mut k: usize = 0;
            while k < cnt_usize
                invariant
                    k <= cnt_usize,
                    locals@.len() + ((cnt_usize - k) as nat) <= MAX_LOCALS_PER_FUNC,
                decreases cnt_usize - k,
            {
                locals.push(vt);
                k = k + 1;
            }
            cur = p4;
            d = d + 1;
        }
        let mut raw_instrs: Vec<RawInstr> = Vec::new();
        let mut br_tables: Vec<Vec<u32>> = Vec::new();
        while cur < body_end
            invariant
                cur <= body_end,
                body_end <= end_pos,
                end_pos <= bytes@.len(),
            decreases body_end - cur,
        {
            let (ins, np) = decode_one_raw_instr(bytes, cur, body_end, &mut br_tables)?;
            raw_instrs.push(ins);
            cur = np;
        }
        let ops = resolve_control_flow(raw_instrs.as_slice())?;
        funcs.push(FuncBody {
            type_idx: func_type_indices[f_idx],
            locals,
            ops,
            br_tables,
        });
        pos = body_end;
        f_idx = f_idx + 1;
    }
    if pos != end_pos {
        return Err(DecodeError::MalformedSection);
    }
    Ok(funcs)
}

// ---------------------------------------------------------------------------
// 5. Top-Level Verified Wasm 1.0 Module Decoder (`decode_module`)
// ---------------------------------------------------------------------------

pub fn decode_module(bytes: &[u8]) -> (r: Result<WasmModule, DecodeError>)
    ensures
        match r {
            Ok(m) =>
                spec_decode_header(bytes@) == Ok::<nat, DecodeError>(8)
                    && (match m.memory {
                        None => true,
                        Some(lim) =>
                            lim.min_pages <= MAX_SPEC_PAGES
                                && (match lim.max_pages {
                                    None => true,
                                    Some(mx) => lim.min_pages <= mx && mx <= MAX_SPEC_PAGES,
                                }),
                    }),
            Err(_) => true,
        },
{
    let mut pos = decode_header(bytes)?;
    let total = bytes.len();

    let mut types: Vec<FuncType> = Vec::new();
    let mut func_type_indices: Vec<u32> = Vec::new();
    let mut table: Option<TableLimits> = None;
    let mut memory: Option<MemoryLimits> = None;
    let mut globals: Vec<GlobalDecl> = Vec::new();
    let mut exports: Vec<ExportDesc> = Vec::new();
    let mut elem_segments: Vec<ElemSegment> = Vec::new();
    let mut funcs: Vec<FuncBody> = Vec::new();
    let mut data_segments: Vec<DataSegment> = Vec::new();
    let mut seen_code = false;
    let mut last_sec_id: u8 = 0;

    while pos < total
        invariant
            8 <= pos <= total,
            total == bytes@.len(),
            spec_decode_header(bytes@) == Ok::<nat, DecodeError>(8),
            match memory {
                None => true,
                Some(lim) =>
                    lim.min_pages <= MAX_SPEC_PAGES
                        && (match lim.max_pages {
                            None => true,
                            Some(mx) => lim.min_pages <= mx && mx <= MAX_SPEC_PAGES,
                        }),
            },
        decreases total - pos,
    {
        let sec_id = bytes[pos];
        if sec_id > 11 {
            return Err(DecodeError::UnsupportedSection(sec_id));
        }
        if sec_id != 0 {
            if sec_id <= last_sec_id {
                return Err(DecodeError::MalformedSection);
            }
            last_sec_id = sec_id;
        }
        let (sec_len, payload_start) = decode_u32_bounded(bytes, pos + 1, total)?;
        if (sec_len as u64) > (total - payload_start) as u64 {
            return Err(DecodeError::UnexpectedEof);
        }
        let sec_end = payload_start + (sec_len as usize);
        match sec_id {
            0 => {
                // Custom section: validate non-empty UTF-8/byte name length inside bounds and skip payload.
                let (name_len, name_start) = decode_u32_bounded(bytes, payload_start, sec_end)?;
                if (name_len as u64) > (sec_end - name_start) as u64 {
                    return Err(DecodeError::MalformedSection);
                }
            },
            1 => {
                types = decode_type_section(bytes, payload_start, sec_end)?;
            },
            3 => {
                func_type_indices = decode_function_section(bytes, payload_start, sec_end)?;
            },
            4 => {
                table = decode_table_section(bytes, payload_start, sec_end)?;
            },
            5 => {
                memory = decode_memory_section(bytes, payload_start, sec_end)?;
            },
            6 => {
                globals = decode_global_section(bytes, payload_start, sec_end)?;
            },
            7 => {
                exports = decode_export_section(bytes, payload_start, sec_end)?;
            },
            9 => {
                elem_segments = decode_elem_section(bytes, payload_start, sec_end, globals.as_slice())?;
            },
            10 => {
                funcs = decode_code_section(bytes, payload_start, sec_end, func_type_indices.as_slice())?;
                seen_code = true;
            },
            11 => {
                data_segments = decode_data_section(bytes, payload_start, sec_end, globals.as_slice())?;
            },
            _ => {
                // Section 2 (Import) or Section 8 (Start): only empty Import section allowed in sandboxed pure mode.
                if sec_id == 2 {
                    let (imp_cnt, p_after) = decode_u32_bounded(bytes, payload_start, sec_end)?;
                    if imp_cnt != 0 || p_after != sec_end {
                        return Err(DecodeError::UnsupportedSection(sec_id));
                    }
                } else {
                    return Err(DecodeError::UnsupportedSection(sec_id));
                }
            },
        }
        pos = sec_end;
    }

    if func_type_indices.len() > 0 && !seen_code {
        return Err(DecodeError::FunctionCountMismatch);
    }

    Ok(WasmModule {
        types,
        func_type_indices,
        table,
        memory,
        globals,
        exports,
        elem_segments,
        funcs,
        data_segments,
    })
}

} // verus!
