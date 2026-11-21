//! ECMA-262 §6.1.6.1 The Number Type, §7.1.4.1 StringToNumber, & §7.1.6–7.1.8 Integer Conversions.
//!
//! Represents ECMAScript `Number` values at the exact 64-bit IEEE-754 binary64 bit level
//! (`JsNumber(pub u64)`), requiring zero floating-point `external_body` escape hatches.
//!
//! Verified operations (`exec == spec` + algebraic & structural lemmas):
//! - Classification (`is_nan`, `is_zero`, `is_pos_zero`, `is_neg_zero`, `is_infinite`,
//!   `is_pos_infinite`, `is_neg_infinite`, `is_finite`, `is_integral_number`, `is_safe_integer`),
//! - Sign manipulation (`canonicalize_nan`, `negate`, `abs`),
//! - Comparisons (`equal`, `less_than`, `same_value`, `same_value_zero`),
//! - Round-to-nearest-even IEEE-754 binary64 arithmetic (`add`, `sub`, `mul`, `div`),
//! - Exact modular integer conversions (`to_int32`, `to_uint32`, `to_uint16`, `from_i32`, `from_u32`,
//!   `to_exact_bigint`),
//! - Shortest round-trip decimal formatting `Number::toString` (§6.1.6.1.20, Burger-Dybvig with
//!   ECMA-262 even-`s` tie-breaking) and exact `StringToNumber` (§7.1.4.1.1).

use crate::bigint::{
    add_limbs, clone_limbs, cmp_limbs, mul_limb_add, mul_limbs, pow_u32_limbs, shl_limbs,
    sub_limbs, JsBigInt,
};
#[cfg(verus_keep_ghost)]
use crate::bigint::{
    lemma_bigint_canonical_unique, lemma_bigint_from_int_props, lemma_limbs_upper_bound,
    lemma_limbs_wf_lower_bound, lemma_limbs_wf_zero_iff_empty, lemma_pow2_add, lemma_pow2_pos,
    lemma_pow32_pos, pow2_nat, pow32, pow_nat, spec_bigint_from_int, spec_bigint_zero,
    spec_limbs_nat, spec_limbs_wf, SpecBigInt,
};
#[cfg(verus_keep_ghost)]
use crate::utf16::spec_trim;
use crate::utf16::Utf16Str;
use vstd::prelude::*;

verus! {

/// IEEE-754 binary64 ECMAScript Number represented by its exact 64-bit pattern.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct JsNumber(pub u64);

impl View for JsNumber {
    type V = u64;

    open spec fn view(&self) -> u64 {
        self.0
    }
}

impl JsNumber {
    pub const POS_ZERO: JsNumber = JsNumber(0x0000_0000_0000_0000u64);
    pub const NEG_ZERO: JsNumber = JsNumber(0x8000_0000_0000_0000u64);
    pub const POS_INFINITY: JsNumber = JsNumber(0x7FF0_0000_0000_0000u64);
    pub const NEG_INFINITY: JsNumber = JsNumber(0xFFF0_0000_0000_0000u64);
    pub const NAN: JsNumber = JsNumber(0x7FF8_0000_0000_0000u64);
    pub const ONE: JsNumber = JsNumber(0x3FF0_0000_0000_0000u64);
    pub const NEG_ONE: JsNumber = JsNumber(0xBFF0_0000_0000_0000u64);
    pub const MAX_VALUE: JsNumber = JsNumber(0x7FEF_FFFF_FFFF_FFFFu64);
    pub const MIN_VALUE: JsNumber = JsNumber(0x0000_0000_0000_0001u64);
    pub const EPSILON: JsNumber = JsNumber(0x3CB0_0000_0000_0000u64);
    pub const MAX_SAFE_INTEGER: JsNumber = JsNumber(0x433F_FFFF_FFFF_FFFFu64);
    pub const MIN_SAFE_INTEGER: JsNumber = JsNumber(0xC33F_FFFF_FFFF_FFFFu64);
}

// -------------------------------------------------------------------------------------------
// Bit-Level Classification, Sign, & Comparison Specifications
// -------------------------------------------------------------------------------------------

pub open spec fn spec_sign_bit(b: u64) -> bool {
    (b >> 63u64) != 0
}

pub open spec fn spec_exp_bits(b: u64) -> u64 {
    (b >> 52u64) & 0x7FFu64
}

pub open spec fn spec_mant_bits(b: u64) -> u64 {
    b & 0x000F_FFFF_FFFF_FFFFu64
}

pub open spec fn spec_is_nan(x: JsNumber) -> bool {
    spec_exp_bits(x.0) == 0x7FFu64 && spec_mant_bits(x.0) != 0
}

pub open spec fn spec_is_pos_zero(x: JsNumber) -> bool {
    x.0 == 0x0000_0000_0000_0000u64
}

pub open spec fn spec_is_neg_zero(x: JsNumber) -> bool {
    x.0 == 0x8000_0000_0000_0000u64
}

pub open spec fn spec_is_zero(x: JsNumber) -> bool {
    (x.0 & 0x7FFF_FFFF_FFFF_FFFFu64) == 0
}

pub open spec fn spec_is_infinite(x: JsNumber) -> bool {
    spec_exp_bits(x.0) == 0x7FFu64 && spec_mant_bits(x.0) == 0
}

pub open spec fn spec_is_pos_infinite(x: JsNumber) -> bool {
    x.0 == 0x7FF0_0000_0000_0000u64
}

pub open spec fn spec_is_neg_infinite(x: JsNumber) -> bool {
    x.0 == 0xFFF0_0000_0000_0000u64
}

pub open spec fn spec_is_finite(x: JsNumber) -> bool {
    spec_exp_bits(x.0) < 0x7FFu64
}

/// ECMA-262 §7.2.6 IsIntegralNumber(argument).
pub open spec fn spec_is_integral_number(x: JsNumber) -> bool {
    let exp = spec_exp_bits(x.0);
    let mant = spec_mant_bits(x.0);
    if exp == 0x7FFu64 {
        false
    } else if spec_is_zero(x) {
        true
    } else if exp < 1023u64 {
        false
    } else if exp >= 1075u64 {
        true
    } else {
        let frac_bits: u64 = (1075 - exp) as u64;
        (mant & (((1u64 << frac_bits) - 1) as u64)) == 0
    }
}

/// ECMA-262 §21.1.2.5 Number.isSafeInteger(number).
pub open spec fn spec_is_safe_integer(x: JsNumber) -> bool {
    spec_is_integral_number(x) && (x.0 & 0x7FFF_FFFF_FFFF_FFFFu64) <= 0x433F_FFFF_FFFF_FFFFu64
}

pub open spec fn spec_canonicalize_nan(x: JsNumber) -> JsNumber {
    if spec_is_nan(x) {
        JsNumber(0x7FF8_0000_0000_0000u64)
    } else {
        x
    }
}

/// ECMA-262 §6.1.6.1.1 Number::unaryMinus(x).
pub open spec fn spec_number_negate(x: JsNumber) -> JsNumber {
    if spec_is_nan(x) {
        JsNumber(0x7FF8_0000_0000_0000u64)
    } else {
        JsNumber(x.0 ^ 0x8000_0000_0000_0000u64)
    }
}

/// ECMA-262 §21.3.2.1 Math.abs(x).
pub open spec fn spec_number_abs(x: JsNumber) -> JsNumber {
    if spec_is_nan(x) {
        JsNumber(0x7FF8_0000_0000_0000u64)
    } else {
        JsNumber(x.0 & 0x7FFF_FFFF_FFFF_FFFFu64)
    }
}

/// ECMA-262 §6.1.6.1.13 Number::equal(x, y).
pub open spec fn spec_number_equal(x: JsNumber, y: JsNumber) -> bool {
    if spec_is_nan(x) || spec_is_nan(y) {
        false
    } else if spec_is_zero(x) && spec_is_zero(y) {
        true
    } else {
        x.0 == y.0
    }
}

/// ECMA-262 §6.1.6.1.12 Number::lessThan(x, y); `None` represents `undefined` (unordered NaN).
pub open spec fn spec_number_less_than(x: JsNumber, y: JsNumber) -> Option<bool> {
    if spec_is_nan(x) || spec_is_nan(y) {
        None
    } else if spec_is_zero(x) && spec_is_zero(y) {
        Some(false)
    } else if x.0 == y.0 {
        Some(false)
    } else {
        let sx = spec_sign_bit(x.0);
        let sy = spec_sign_bit(y.0);
        if sx != sy {
            Some(sx)
        } else if !sx {
            Some(x.0 < y.0)
        } else {
            Some(x.0 > y.0)
        }
    }
}

/// ECMA-262 §6.1.6.1.14 Number::sameValue(x, y).
pub open spec fn spec_number_same_value(x: JsNumber, y: JsNumber) -> bool {
    if spec_is_nan(x) || spec_is_nan(y) {
        spec_is_nan(x) && spec_is_nan(y)
    } else {
        x.0 == y.0
    }
}

/// ECMA-262 §6.1.6.1.15 Number::sameValueZero(x, y).
pub open spec fn spec_number_same_value_zero(x: JsNumber, y: JsNumber) -> bool {
    if spec_is_nan(x) || spec_is_nan(y) {
        spec_is_nan(x) && spec_is_nan(y)
    } else if spec_is_zero(x) && spec_is_zero(y) {
        true
    } else {
        x.0 == y.0
    }
}

// -------------------------------------------------------------------------------------------
// ToUint32 / ToInt32 / ToUint16 (§7.1.6–7.1.8) Specifications
// -------------------------------------------------------------------------------------------

/// ECMA-262 §7.1.7 ToUint32(argument) on a Number.
pub open spec fn spec_to_uint32(x: JsNumber) -> u32 {
    let exp = spec_exp_bits(x.0);
    let mant = spec_mant_bits(x.0);
    let sign = spec_sign_bit(x.0);
    if exp == 0x7FFu64 || spec_is_zero(x) || exp < 1023u64 || exp >= 1107u64 {
        0u32
    } else {
        let sig: u64 = 0x0010_0000_0000_0000u64 | mant;
        let mag_mod32: u32 = if exp < 1075u64 {
            let rsh: u64 = (1075 - exp) as u64;
            ((sig >> rsh) & 0xFFFF_FFFFu64) as u32
        } else {
            let lsh: u64 = (exp - 1075) as u64;
            (((sig & 0xFFFF_FFFFu64) << lsh) & 0xFFFF_FFFFu64) as u32
        };
        if sign && mag_mod32 != 0u32 {
            (0x1_0000_0000u64 - (mag_mod32 as u64)) as u32
        } else {
            mag_mod32
        }
    }
}

/// ECMA-262 §7.1.6 ToInt32(argument) on a Number.
pub open spec fn spec_to_int32(x: JsNumber) -> i32 {
    let u = spec_to_uint32(x);
    if u >= 0x8000_0000u32 {
        ((u as int) - 0x1_0000_0000int) as i32
    } else {
        u as i32
    }
}

/// ECMA-262 §7.1.8 ToUint16(argument) on a Number.
pub open spec fn spec_to_uint16(x: JsNumber) -> u16 {
    (spec_to_uint32(x) & 0xFFFFu32) as u16
}

/// Mathematical integer truncation toward zero (`truncate(ℝ(x))`) of a finite `JsNumber`,
/// defined directly over unpacked `(sign, sig, exp2)` and `pow2_nat`.
pub open spec fn spec_trunc_finite_int(x: JsNumber) -> int {
    if spec_is_zero(x) {
        0int
    } else {
        let (sign, sig, exp2) = spec_unpack_finite_nonzero(x);
        let mag: nat = if exp2 >= 0 {
            (sig as nat) * pow2_nat(exp2 as nat)
        } else {
            (sig as nat) / pow2_nat((-exp2) as nat)
        };
        if sign { -(mag as int) } else { mag as int }
    }
}

/// Exact conversion of an integral `JsNumber` to `SpecBigInt` (for `IsLooselyEqual` Number vs BigInt).
pub open spec fn spec_number_to_exact_bigint(x: JsNumber) -> Option<SpecBigInt> {
    if !spec_is_integral_number(x) {
        None
    } else if spec_is_zero(x) {
        Some(spec_bigint_zero())
    } else {
        let sign = spec_sign_bit(x.0);
        let exp = spec_exp_bits(x.0);
        let mant = spec_mant_bits(x.0);
        let sig: u64 = 0x0010_0000_0000_0000u64 | mant;
        let mag: nat = if exp < 1075u64 {
            let rsh: u64 = (1075 - exp) as u64;
            (sig >> rsh) as nat
        } else {
            let lsh: nat = (exp - 1075) as nat;
            (sig as nat) * pow2_nat(lsh)
        };
        Some(spec_bigint_from_int(if sign { -(mag as int) } else { mag as int }))
    }
}

// -------------------------------------------------------------------------------------------
// IEEE-754 binary64 Round-to-Nearest-Even Arithmetic Specifications
// -------------------------------------------------------------------------------------------

pub open spec fn spec_bit_len_u64(x: u64) -> u32 {
    if x == 0 {
        0u32
    } else {
        let x32: u64 = if x >= 0x1_0000_0000u64 { x >> 32u64 } else { x };
        let n32: u32 = if x >= 0x1_0000_0000u64 { 32u32 } else { 0u32 };
        let x16: u64 = if x32 >= 0x1_0000u64 { x32 >> 16u64 } else { x32 };
        let n16: u32 = if x32 >= 0x1_0000u64 { add(n32, 16u32) } else { n32 };
        let x8: u64 = if x16 >= 0x100u64 { x16 >> 8u64 } else { x16 };
        let n8: u32 = if x16 >= 0x100u64 { add(n16, 8u32) } else { n16 };
        let x4: u64 = if x8 >= 0x10u64 { x8 >> 4u64 } else { x8 };
        let n4: u32 = if x8 >= 0x10u64 { add(n8, 4u32) } else { n8 };
        let x2: u64 = if x4 >= 0x4u64 { x4 >> 2u64 } else { x4 };
        let n2: u32 = if x4 >= 0x4u64 { add(n4, 2u32) } else { n4 };
        if x2 >= 0x2u64 { add(n2, 2u32) } else { add(n2, 1u32) }
    }
}

pub open spec fn spec_bit_len_u128(m: u128) -> u32 {
    let hi: u64 = (m >> 64u128) as u64;
    let lo: u64 = (m & 0xFFFF_FFFF_FFFF_FFFFu128) as u64;
    if hi != 0 {
        add(64u32, spec_bit_len_u64(hi))
    } else {
        spec_bit_len_u64(lo)
    }
}

/// Unpack a finite non-zero binary64 into `(sign, normalized_sig_53, exp2)` where
/// `2^52 <= normalized_sig_53 < 2^53` and `-1126 <= exp2 <= 971`.
pub open spec fn spec_unpack_finite_nonzero(x: JsNumber) -> (bool, u64, i32) {
    let sign = spec_sign_bit(x.0);
    let exp = spec_exp_bits(x.0);
    let mant = spec_mant_bits(x.0);
    if exp == 0 {
        let bl = spec_bit_len_u64(mant);
        let sh: u64 = (53 - bl) as u64;
        (sign, mant << sh, (-1074 - (sh as int)) as i32)
    } else {
        (sign, 0x0010_0000_0000_0000u64 | mant, (exp as int - 1075) as i32)
    }
}

/// Unified single-step IEEE-754 binary64 round-to-nearest-even packer for `(-1)^sign * m * 2^exp2` (`m > 0`).
pub open spec fn spec_pack_rne(sign: bool, m: u128, exp2: i32) -> JsNumber {
    let sign_mask: u64 = if sign { 0x8000_0000_0000_0000u64 } else { 0u64 };
    let inf: JsNumber = if sign { JsNumber(0xFFF0_0000_0000_0000u64) } else { JsNumber(0x7FF0_0000_0000_0000u64) };
    let zero: JsNumber = JsNumber(sign_mask);
    let bl = spec_bit_len_u128(m);
    let unbiased_e: int = (exp2 as int) + (bl as int) - 1;
    if unbiased_e > 1023 {
        inf
    } else {
        let target_exp2: int = if unbiased_e - 52 > -1074 { unbiased_e - 52 } else { -1074 };
        if (exp2 as int) >= target_exp2 {
            let lsh: u64 = ((exp2 as int) - target_exp2) as u64;
            let q: u64 = (m as u64) << lsh;
            if target_exp2 == -1074 {
                JsNumber(sign_mask | q)
            } else {
                let biased_exp: u64 = (target_exp2 + 1075) as u64;
                JsNumber(sign_mask | (biased_exp << 52u64) | (q & 0x000F_FFFF_FFFF_FFFFu64))
            }
        } else {
            let rsh: int = target_exp2 - (exp2 as int);
            if rsh > 128 {
                zero
            } else if rsh == 128 {
                let half128: u128 = 1u128 << 127u128;
                if m > half128 {
                    JsNumber(sign_mask | 1u64)
                } else {
                    zero
                }
            } else {
                let sh: u128 = rsh as u128;
                let q: u64 = (m >> sh) as u64;
                let half: u128 = 1u128 << ((sh - 1) as u128);
                let mask: u128 = ((1u128 << sh) - 1) as u128;
                let rem: u128 = m & mask;
                let round_up: bool = (rem > half) || (rem == half && (q & 1u64) == 1u64);
                let q_rounded: u64 = if round_up { (q + 1) as u64 } else { q };
                if target_exp2 == -1074 {
                    JsNumber(sign_mask | q_rounded)
                } else if q_rounded >= 0x0020_0000_0000_0000u64 {
                    let q_final: u64 = q_rounded >> 1u64;
                    let exp_final: int = target_exp2 + 1;
                    if exp_final > 971 {
                        inf
                    } else {
                        let biased_exp: u64 = (exp_final + 1075) as u64;
                        JsNumber(sign_mask | (biased_exp << 52u64) | (q_final & 0x000F_FFFF_FFFF_FFFFu64))
                    }
                } else {
                    let biased_exp: u64 = (target_exp2 + 1075) as u64;
                    JsNumber(sign_mask | (biased_exp << 52u64) | (q_rounded & 0x000F_FFFF_FFFF_FFFFu64))
                }
            }
        }
    }
}

/// ECMA-262 §6.1.6.1.7 Number::add(x, y).
pub open spec fn spec_number_add(x: JsNumber, y: JsNumber) -> JsNumber {
    if spec_is_nan(x) || spec_is_nan(y) {
        JsNumber(0x7FF8_0000_0000_0000u64)
    } else {
        let sx = spec_sign_bit(x.0);
        let sy = spec_sign_bit(y.0);
        if spec_is_infinite(x) && spec_is_infinite(y) {
            if sx == sy {
                if sx { JsNumber(0xFFF0_0000_0000_0000u64) } else { JsNumber(0x7FF0_0000_0000_0000u64) }
            } else {
                JsNumber(0x7FF8_0000_0000_0000u64)
            }
        } else if spec_is_infinite(x) {
            x
        } else if spec_is_infinite(y) {
            y
        } else if spec_is_zero(x) && spec_is_zero(y) {
            if sx && sy { JsNumber(0x8000_0000_0000_0000u64) } else { JsNumber(0u64) }
        } else if spec_is_zero(x) {
            y
        } else if spec_is_zero(y) {
            x
        } else {
            let (sx_u, sig_x, exp_x) = spec_unpack_finite_nonzero(x);
            let (sy_u, sig_y, exp_y) = spec_unpack_finite_nonzero(y);
            if sx_u != sy_u && exp_x == exp_y && sig_x == sig_y {
                JsNumber(0u64)
            } else {
                let (sa, sig_a, exp_a, sb, sig_b, exp_b) =
                    if exp_x > exp_y || (exp_x == exp_y && sig_x >= sig_y) {
                        (sx_u, sig_x, exp_x, sy_u, sig_y, exp_y)
                    } else {
                        (sy_u, sig_y, exp_y, sx_u, sig_x, exp_x)
                    };
                let diff: int = (exp_a as int) - (exp_b as int);
                let ma: u128 = (sig_a as u128) << 3u128;
                let raw_b: u128 = (sig_b as u128) << 3u128;
                let mb: u128 = if diff == 0 {
                    raw_b
                } else if diff <= 60 {
                    let d_u: u128 = diff as u128;
                    let shifted: u128 = raw_b >> d_u;
                    let rem_mask: u128 = ((1u128 << d_u) - 1) as u128;
                    let sticky: u128 = if (raw_b & rem_mask) != 0 { 1u128 } else { 0u128 };
                    shifted | sticky
                } else {
                    1u128
                };
                let m: u128 = if sa == sb { (ma + mb) as u128 } else { (ma - mb) as u128 };
                spec_pack_rne(sa, m, (exp_a - 3) as i32)
            }
        }
    }
}

/// ECMA-262 §6.1.6.1.8 Number::subtract(x, y).
pub open spec fn spec_number_sub(x: JsNumber, y: JsNumber) -> JsNumber {
    if spec_is_nan(x) || spec_is_nan(y) {
        JsNumber(0x7FF8_0000_0000_0000u64)
    } else {
        spec_number_add(x, spec_number_negate(y))
    }
}

/// ECMA-262 §6.1.6.1.4 Number::multiply(x, y).
pub open spec fn spec_number_mul(x: JsNumber, y: JsNumber) -> JsNumber {
    if spec_is_nan(x) || spec_is_nan(y) {
        JsNumber(0x7FF8_0000_0000_0000u64)
    } else {
        let sign = spec_sign_bit(x.0) != spec_sign_bit(y.0);
        if (spec_is_infinite(x) && spec_is_zero(y)) || (spec_is_zero(x) && spec_is_infinite(y)) {
            JsNumber(0x7FF8_0000_0000_0000u64)
        } else if spec_is_infinite(x) || spec_is_infinite(y) {
            if sign { JsNumber(0xFFF0_0000_0000_0000u64) } else { JsNumber(0x7FF0_0000_0000_0000u64) }
        } else if spec_is_zero(x) || spec_is_zero(y) {
            if sign { JsNumber(0x8000_0000_0000_0000u64) } else { JsNumber(0u64) }
        } else {
            let (_, sig_x, exp_x) = spec_unpack_finite_nonzero(x);
            let (_, sig_y, exp_y) = spec_unpack_finite_nonzero(y);
            let prod: u128 = ((sig_x as int) * (sig_y as int)) as u128;
            let exp_sum: i32 = ((exp_x as int) + (exp_y as int)) as i32;
            spec_pack_rne(sign, prod, exp_sum)
        }
    }
}

/// ECMA-262 §6.1.6.1.5 Number::divide(x, y).
pub open spec fn spec_number_div(x: JsNumber, y: JsNumber) -> JsNumber {
    if spec_is_nan(x) || spec_is_nan(y) {
        JsNumber(0x7FF8_0000_0000_0000u64)
    } else {
        let sign = spec_sign_bit(x.0) != spec_sign_bit(y.0);
        let inf = if sign { JsNumber(0xFFF0_0000_0000_0000u64) } else { JsNumber(0x7FF0_0000_0000_0000u64) };
        let zero = if sign { JsNumber(0x8000_0000_0000_0000u64) } else { JsNumber(0u64) };
        if spec_is_infinite(x) && spec_is_infinite(y) {
            JsNumber(0x7FF8_0000_0000_0000u64)
        } else if spec_is_infinite(x) {
            inf
        } else if spec_is_infinite(y) {
            zero
        } else if spec_is_zero(x) && spec_is_zero(y) {
            JsNumber(0x7FF8_0000_0000_0000u64)
        } else if spec_is_zero(x) {
            zero
        } else if spec_is_zero(y) {
            inf
        } else {
            let (_, sig_x, exp_x) = spec_unpack_finite_nonzero(x);
            let (_, sig_y, exp_y) = spec_unpack_finite_nonzero(y);
            let num: u128 = (sig_x as u128) << 55u128;
            let den: u128 = sig_y as u128;
            let quot: u128 = num / den;
            let rem: u128 = num % den;
            let m: u128 = (quot << 1u128) | (if rem != 0 { 1u128 } else { 0u128 });
            let exp_out: i32 = ((exp_x as int) - (exp_y as int) - 56) as i32;
            spec_pack_rne(sign, m, exp_out)
        }
    }
}

pub open spec fn spec_from_u32(v: u32) -> JsNumber {
    if v == 0 {
        JsNumber(0u64)
    } else {
        spec_pack_rne(false, v as u128, 0)
    }
}

pub open spec fn spec_from_i32(v: i32) -> JsNumber {
    if v == 0 {
        JsNumber(0u64)
    } else if v > 0 {
        spec_pack_rne(false, v as u128, 0)
    } else {
        let mag: u128 = (-(v as int)) as u128;
        spec_pack_rne(true, mag, 0)
    }
}

// -------------------------------------------------------------------------------------------
// Exact Mathematical Specifications for `StringToNumber` & `Number::toString`
// -------------------------------------------------------------------------------------------

pub open spec fn spec_nat_bit_len(v: nat) -> nat
    decreases v,
{
    if v == 0 {
        0
    } else {
        1 + spec_nat_bit_len(v / 2)
    }
}

/// Round exact positive rational `(num / den) * 2^base_exp2` (`num >= 1, den >= 1`) to binary64 RNE.
pub open spec fn spec_rational_to_number_rne(sign: bool, num: nat, den: nat, base_exp2: int) -> JsNumber {
    let bl_num = spec_nat_bit_len(num);
    let bl_den = spec_nat_bit_len(den);
    let approx_exp2: int = base_exp2 + (bl_num as int) - (bl_den as int);
    if approx_exp2 > 1025 {
        if sign { JsNumber(0xFFF0_0000_0000_0000u64) } else { JsNumber(0x7FF0_0000_0000_0000u64) }
    } else if approx_exp2 < -1080 {
        if sign { JsNumber(0x8000_0000_0000_0000u64) } else { JsNumber(0u64) }
    } else {
        let shift: int = 55 - ((bl_num as int) - (bl_den as int));
        let (num_s, den_s) = if shift >= 0 {
            (num * pow2_nat(shift as nat), den)
        } else {
            (num, den * pow2_nat((-shift) as nat))
        };
        let adj_exp2: i32 = (base_exp2 - shift) as i32;
        let quot: nat = if den_s > 0 { num_s / den_s } else { 0 };
        let rem_nz: bool = if den_s > 0 { (num_s % den_s) != 0 } else { false };
        let m: u128 = (((quot as u128) << 1u128) | (if rem_nz { 1u128 } else { 0u128 }));
        spec_pack_rne(sign, m, (adj_exp2 - 1) as i32)
    }
}

pub open spec fn spec_is_ascii_dec(u: u16) -> bool {
    0x30 <= u && u <= 0x39
}

pub open spec fn spec_match_infinity(s: Seq<u16>) -> bool {
    s.len() == 8
        && s[0] == 0x49u16 // 'I'
        && s[1] == 0x6Eu16 // 'n'
        && s[2] == 0x66u16 // 'f'
        && s[3] == 0x69u16 // 'i'
        && s[4] == 0x6Eu16 // 'n'
        && s[5] == 0x69u16 // 'i'
        && s[6] == 0x74u16 // 't'
        && s[7] == 0x79u16 // 'y'
}

/// State accumulated while scanning significant digits of `StrUnsignedDecimalLiteral`.
pub struct SpecDecMantissa {
    pub sig: nat,
    pub sig_count: nat,
    pub exp_adj: int,
    pub tail_nz: bool,
    pub total_digits: nat,
}

pub open spec fn spec_feed_dec_digit(st: SpecDecMantissa, d: nat, is_frac: bool) -> SpecDecMantissa {
    let total_digits = st.total_digits + 1;
    if st.sig_count == 0 && d == 0 {
        SpecDecMantissa {
            sig: 0,
            sig_count: 0,
            exp_adj: if is_frac { st.exp_adj - 1 } else { st.exp_adj },
            tail_nz: false,
            total_digits,
        }
    } else if st.sig_count < 800 {
        SpecDecMantissa {
            sig: st.sig * 10 + d,
            sig_count: st.sig_count + 1,
            exp_adj: if is_frac { st.exp_adj - 1 } else { st.exp_adj },
            tail_nz: st.tail_nz,
            total_digits,
        }
    } else {
        SpecDecMantissa {
            sig: st.sig,
            sig_count: st.sig_count,
            exp_adj: if is_frac { st.exp_adj } else { st.exp_adj + 1 },
            tail_nz: st.tail_nz || (d != 0),
            total_digits,
        }
    }
}

pub open spec fn spec_scan_dec_digits(
    s: Seq<u16>,
    pos: nat,
    st: SpecDecMantissa,
    is_frac: bool,
) -> (nat, SpecDecMantissa)
    decreases s.len() - pos,
{
    if pos >= s.len() || !spec_is_ascii_dec(s[pos as int]) {
        (pos, st)
    } else {
        let d = (s[pos as int] - 0x30) as nat;
        spec_scan_dec_digits(s, pos + 1, spec_feed_dec_digit(st, d, is_frac), is_frac)
    }
}

pub open spec fn spec_scan_exp_digits(s: Seq<u16>, pos: nat, acc: int, count: nat) -> (nat, int, nat)
    decreases s.len() - pos,
{
    if pos >= s.len() || !spec_is_ascii_dec(s[pos as int]) {
        (pos, acc, count)
    } else {
        let d = (s[pos as int] - 0x30) as int;
        spec_scan_exp_digits(s, pos + 1, acc * 10 + d, count + 1)
    }
}

pub open spec fn spec_parse_unsigned_decimal(s: Seq<u16>, sign: bool) -> JsNumber {
    let init = SpecDecMantissa { sig: 0, sig_count: 0, exp_adj: 0, tail_nz: false, total_digits: 0 };
    let (pos1, st1) = spec_scan_dec_digits(s, 0, init, false);
    let (pos2, st2) = if pos1 < s.len() && s[pos1 as int] == 0x2Eu16 {
        spec_scan_dec_digits(s, pos1 + 1, st1, true)
    } else {
        (pos1, st1)
    };
    if st2.total_digits == 0 {
        JsNumber(0x7FF8_0000_0000_0000u64)
    } else {
        let (ok, exp_part): (bool, int) = if pos2 == s.len() {
            (true, 0int)
        } else if s[pos2 as int] == 0x65u16 || s[pos2 as int] == 0x45u16 {
            let p_sign = pos2 + 1;
            if p_sign >= s.len() {
                (false, 0int)
            } else {
                let (exp_neg, p_dig) = if s[p_sign as int] == 0x2Du16 {
                    (true, p_sign + 1)
                } else if s[p_sign as int] == 0x2Bu16 {
                    (false, p_sign + 1)
                } else {
                    (false, p_sign)
                };
                let (p_end, mag, cnt) = spec_scan_exp_digits(s, p_dig, 0, 0);
                if cnt == 0 || p_end != s.len() {
                    (false, 0int)
                } else {
                    (true, if exp_neg { -mag } else { mag })
                }
            }
        } else {
            (false, 0int)
        };
        if !ok {
            JsNumber(0x7FF8_0000_0000_0000u64)
        } else if st2.sig_count == 0 {
            if sign { JsNumber(0x8000_0000_0000_0000u64) } else { JsNumber(0u64) }
        } else {
            let (final_sig, final_cnt, final_adj): (nat, nat, int) = if st2.tail_nz {
                (st2.sig * 10 + 1, st2.sig_count + 1, st2.exp_adj - 1)
            } else {
                (st2.sig, st2.sig_count, st2.exp_adj)
            };
            let exp10: int = final_adj + exp_part;
            let sci_exp10: int = exp10 + (final_cnt as int) - 1;
            if sci_exp10 > 310 {
                if sign { JsNumber(0xFFF0_0000_0000_0000u64) } else { JsNumber(0x7FF0_0000_0000_0000u64) }
            } else if sci_exp10 < -326 {
                if sign { JsNumber(0x8000_0000_0000_0000u64) } else { JsNumber(0u64) }
            } else if exp10 >= 0 {
                let num = final_sig * pow_nat(10, exp10 as nat);
                spec_rational_to_number_rne(sign, num, 1, 0)
            } else {
                let k: nat = (-exp10) as nat;
                let den = pow_nat(5, k);
                spec_rational_to_number_rne(sign, final_sig, den, exp10)
            }
        }
    }
}

/// ECMA-262 §7.1.4.1.1 StringToNumber(str).
pub open spec fn spec_string_to_number(s: Seq<u16>) -> JsNumber {
    let t = spec_trim(s);
    if t.len() == 0 {
        JsNumber(0u64)
    } else if t.len() >= 2 && t[0] == 0x30u16 && (t[1] == 0x62u16 || t[1] == 0x42u16) {
        let digits = t.subrange(2, t.len() as int);
        if digits.len() == 0 {
            JsNumber(0x7FF8_0000_0000_0000u64)
        } else {
            match crate::bigint::spec_parse_radix_digits(digits, 2) {
                None => JsNumber(0x7FF8_0000_0000_0000u64),
                Some(v) => if v == 0 { JsNumber(0u64) } else { spec_rational_to_number_rne(false, v, 1, 0) },
            }
        }
    } else if t.len() >= 2 && t[0] == 0x30u16 && (t[1] == 0x6Fu16 || t[1] == 0x4Fu16) {
        let digits = t.subrange(2, t.len() as int);
        if digits.len() == 0 {
            JsNumber(0x7FF8_0000_0000_0000u64)
        } else {
            match crate::bigint::spec_parse_radix_digits(digits, 8) {
                None => JsNumber(0x7FF8_0000_0000_0000u64),
                Some(v) => if v == 0 { JsNumber(0u64) } else { spec_rational_to_number_rne(false, v, 1, 0) },
            }
        }
    } else if t.len() >= 2 && t[0] == 0x30u16 && (t[1] == 0x78u16 || t[1] == 0x58u16) {
        let digits = t.subrange(2, t.len() as int);
        if digits.len() == 0 {
            JsNumber(0x7FF8_0000_0000_0000u64)
        } else {
            match crate::bigint::spec_parse_radix_digits(digits, 16) {
                None => JsNumber(0x7FF8_0000_0000_0000u64),
                Some(v) => if v == 0 { JsNumber(0u64) } else { spec_rational_to_number_rne(false, v, 1, 0) },
            }
        }
    } else {
        let (sign, body) = if t[0] == 0x2Du16 {
            (true, t.subrange(1, t.len() as int))
        } else if t[0] == 0x2Bu16 {
            (false, t.subrange(1, t.len() as int))
        } else {
            (false, t)
        };
        if body.len() == 0 {
            JsNumber(0x7FF8_0000_0000_0000u64)
        } else if spec_match_infinity(body) {
            if sign { JsNumber(0xFFF0_0000_0000_0000u64) } else { JsNumber(0x7FF0_0000_0000_0000u64) }
        } else {
            spec_parse_unsigned_decimal(body, sign)
        }
    }
}

// Burger-Dybvig shortest decimal `Number::toString` (§6.1.6.1.20) specification over `nat` / `int`:

pub open spec fn spec_bd_scale_up(
    r: nat,
    s_den: nat,
    m_plus: nat,
    n: int,
    even: bool,
    fuel: nat,
) -> (nat, int)
    decreases fuel,
{
    if fuel == 0 {
        (s_den, n)
    } else {
        let need_up = if even { r + m_plus >= s_den } else { r + m_plus > s_den };
        if need_up {
            spec_bd_scale_up(r, s_den * 10, m_plus, n + 1, even, (fuel - 1) as nat)
        } else {
            (s_den, n)
        }
    }
}

pub open spec fn spec_bd_scale_down(
    r: nat,
    s_den: nat,
    m_plus: nat,
    m_minus: nat,
    n: int,
    even: bool,
    fuel: nat,
) -> (nat, nat, nat, int)
    decreases fuel,
{
    if fuel == 0 {
        (r, m_plus, m_minus, n)
    } else {
        let top10 = (r + m_plus) * 10;
        let need_down = if even { top10 < s_den } else { top10 <= s_den };
        if need_down {
            spec_bd_scale_down(r * 10, s_den, m_plus * 10, m_minus * 10, n - 1, even, (fuel - 1) as nat)
        } else {
            (r, m_plus, m_minus, n)
        }
    }
}

/// Extract next decimal digit `d` (`0 <= d <= 9`) via bounded subtraction of `s_den`.
pub open spec fn spec_div_digit_10(rem: nat, s_den: nat, d: u8) -> (u8, nat)
    decreases 9 - d,
{
    if d >= 9 || rem < s_den {
        (d, rem)
    } else {
        spec_div_digit_10((rem - s_den) as nat, s_den, (d + 1) as u8)
    }
}

pub open spec fn spec_bd_generate_digits(
    r: nat,
    s_den: nat,
    m_plus: nat,
    m_minus: nat,
    even: bool,
    fuel: nat,
) -> Seq<u16>
    decreases fuel,
{
    if fuel == 0 {
        Seq::<u16>::empty()
    } else {
        let r10 = r * 10;
        let mp10 = m_plus * 10;
        let mm10 = m_minus * 10;
        let (d, rem) = spec_div_digit_10(r10, s_den, 0u8);
        let low = if even { rem <= mm10 } else { rem < mm10 };
        let high = if even { rem + mp10 >= s_den } else { rem + mp10 > s_den };
        if !low && !high {
            seq![(0x30u16 + (d as u16)) as u16]
                + spec_bd_generate_digits(rem, s_den, mp10, mm10, even, (fuel - 1) as nat)
        } else if low && !high {
            seq![(0x30u16 + (d as u16)) as u16]
        } else if !low && high {
            let d1: u8 = if d < 9 { (d + 1) as u8 } else { 9u8 };
            seq![(0x30u16 + (d1 as u16)) as u16]
        } else {
            // Both `d` and `d + 1` round to `m`: ECMA-262 §6.1.6.1.20 step 5 chooses closest, ties to even `s`.
            let r2 = rem * 2;
            let pick_high: bool = (r2 > s_den) || (r2 == s_den && (d & 1u8) == 1u8);
            let df: u8 = if pick_high && d < 9 { (d + 1) as u8 } else { d };
            seq![(0x30u16 + (df as u16)) as u16]
        }
    }
}

pub open spec fn spec_repeat_zero_u16(count: nat) -> Seq<u16>
    decreases count,
{
    if count == 0 {
        Seq::<u16>::empty()
    } else {
        spec_repeat_zero_u16((count - 1) as nat).push(0x30u16)
    }
}

/// Format positive integer `e >= 1` in base 10 (`|n - 1|` for scientific exponent).
pub open spec fn spec_uint_to_dec_u16(v: nat) -> Seq<u16> {
    crate::bigint::spec_nat_to_radix_nonempty(v, 10)
}

/// ECMA-262 §6.1.6.1.20 steps 6–10 decimal layout given shortest `digits` (`k = digits.len() >= 1`) and `n`.
pub open spec fn spec_format_ecmascript_decimal(digits: Seq<u16>, n: int) -> Seq<u16> {
    let k: int = digits.len() as int;
    if k <= n && n <= 21 {
        digits + spec_repeat_zero_u16((n - k) as nat)
    } else if 0 < n && n <= 21 {
        digits.subrange(0, n) + seq![0x2Eu16] + digits.subrange(n, k)
    } else if -6 < n && n <= 0 {
        seq![0x30u16, 0x2Eu16] + spec_repeat_zero_u16((-n) as nat) + digits
    } else {
        let exp_val: int = n - 1;
        let exp_sign: u16 = if exp_val > 0 { 0x2Bu16 } else { 0x2Du16 };
        let exp_mag: nat = if exp_val >= 0 { exp_val as nat } else { (-exp_val) as nat };
        let exp_str = seq![0x65u16, exp_sign] + spec_uint_to_dec_u16(exp_mag);
        if k <= 1 {
            digits + exp_str
        } else {
            seq![digits[0], 0x2Eu16] + digits.subrange(1, k) + exp_str
        }
    }
}

pub open spec fn spec_positive_finite_to_string(b: u64) -> Seq<u16> {
    let exp_bits = spec_exp_bits(b);
    let mant_bits = spec_mant_bits(b);
    let f: u64 = if exp_bits == 0 { mant_bits } else { 0x0010_0000_0000_0000u64 | mant_bits };
    let e: int = if exp_bits == 0 { -1074 } else { (exp_bits as int) - 1075 };
    let even: bool = (f & 1u64) == 0;
    let lower_boundary: bool = exp_bits > 1 && mant_bits == 0;
    let fnat: nat = f as nat;
    let (r0, s0, mp0, mm0): (nat, nat, nat, nat) = if !lower_boundary {
        if e >= 0 {
            let fe = fnat * pow2_nat(e as nat);
            (fe * 2, 2nat, pow2_nat(e as nat), pow2_nat(e as nat))
        } else {
            (fnat * 2, pow2_nat((1 - e) as nat), 1nat, 1nat)
        }
    } else {
        if e >= 0 {
            let fe = fnat * pow2_nat(e as nat);
            (fe * 4, 4nat, pow2_nat((e + 1) as nat), pow2_nat(e as nat))
        } else {
            (fnat * 4, pow2_nat((2 - e) as nat), 2nat, 1nat)
        }
    };
    let eb: int = e + (spec_bit_len_u64(f) as int) - 1;
    let est: int = if eb >= 0 {
        (eb * 30103) / 100000
    } else {
        -(((-eb) * 30103) / 100000)
    };
    let (r1, s1, mp1, mm1, n1): (nat, nat, nat, nat, int) = if est > 0 {
        let p10 = pow_nat(10, est as nat);
        (r0, s0 * p10, mp0, mm0, est)
    } else if est < 0 {
        let p10 = pow_nat(10, (-est) as nat);
        (r0 * p10, s0, mp0 * p10, mm0 * p10, est)
    } else {
        (r0, s0, mp0, mm0, 0)
    };
    let (s2, n2) = spec_bd_scale_up(r1, s1, mp1, n1, even, 16);
    let (r3, mp3, mm3, n3) = spec_bd_scale_down(r1, s2, mp1, mm1, n2, even, 16);
    let digits = spec_bd_generate_digits(r3, s2, mp3, mm3, even, 25);
    spec_format_ecmascript_decimal(digits, n3)
}

/// ECMA-262 §6.1.6.1.20 Number::toString(x, 10).
pub open spec fn spec_number_to_string(x: JsNumber) -> Seq<u16> {
    if spec_is_nan(x) {
        seq![0x4Eu16, 0x61u16, 0x4Eu16] // "NaN"
    } else if spec_is_zero(x) {
        seq![0x30u16] // "0"
    } else if spec_sign_bit(x.0) {
        let abs_b: u64 = x.0 & 0x7FFF_FFFF_FFFF_FFFFu64;
        if spec_is_pos_infinite(JsNumber(abs_b)) {
            seq![0x2Du16, 0x49u16, 0x6Eu16, 0x66u16, 0x69u16, 0x6Eu16, 0x69u16, 0x74u16, 0x79u16]
        } else {
            seq![0x2Du16] + spec_positive_finite_to_string(abs_b)
        }
    } else if spec_is_pos_infinite(x) {
        seq![0x49u16, 0x6Eu16, 0x66u16, 0x69u16, 0x6Eu16, 0x69u16, 0x74u16, 0x79u16]
    } else {
        spec_positive_finite_to_string(x.0)
    }
}

// -------------------------------------------------------------------------------------------
// Algebraic & IEEE-754 Lemmas
// -------------------------------------------------------------------------------------------

/// `Number::sameValue` is an equivalence relation on `JsNumber`.
pub proof fn lemma_number_same_value_equivalence(x: JsNumber, y: JsNumber, z: JsNumber)
    ensures
        spec_number_same_value(x, x),
        spec_number_same_value(x, y) == spec_number_same_value(y, x),
        (spec_number_same_value(x, y) && spec_number_same_value(y, z)) ==> spec_number_same_value(x, z),
{
}

/// `Number::sameValueZero` is an equivalence relation on `JsNumber`.
pub proof fn lemma_number_same_value_zero_equivalence(x: JsNumber, y: JsNumber, z: JsNumber)
    ensures
        spec_number_same_value_zero(x, x),
        spec_number_same_value_zero(x, y) == spec_number_same_value_zero(y, x),
        (spec_number_same_value_zero(x, y) && spec_number_same_value_zero(y, z))
            ==> spec_number_same_value_zero(x, z),
{
}

/// `+0` and `-0` are `Number::equal` and `sameValueZero`, yet distinguished by `sameValue`.
pub proof fn lemma_pos_neg_zero_distinction()
    ensures
        spec_number_equal(JsNumber(0u64), JsNumber(0x8000_0000_0000_0000u64)),
        spec_number_same_value_zero(JsNumber(0u64), JsNumber(0x8000_0000_0000_0000u64)),
        !spec_number_same_value(JsNumber(0u64), JsNumber(0x8000_0000_0000_0000u64)),
        !spec_number_equal(JsNumber(0x7FF8_0000_0000_0000u64), JsNumber(0x7FF8_0000_0000_0000u64)),
        spec_number_same_value(JsNumber(0x7FF8_0000_0000_0000u64), JsNumber(0x7FF8_0000_0000_0001u64)),
{
    assert(((0u64 >> 52u64) & 0x7FFu64) == 0u64) by (bit_vector);
    assert((0u64 & 0x7FFF_FFFF_FFFF_FFFFu64) == 0u64) by (bit_vector);
    assert(((0x8000_0000_0000_0000u64 >> 52u64) & 0x7FFu64) == 0u64) by (bit_vector);
    assert((0x8000_0000_0000_0000u64 & 0x7FFF_FFFF_FFFF_FFFFu64) == 0u64) by (bit_vector);
    assert(((0x7FF8_0000_0000_0000u64 >> 52u64) & 0x7FFu64) == 0x7FFu64) by (bit_vector);
    assert((0x7FF8_0000_0000_0000u64 & 0x000F_FFFF_FFFF_FFFFu64) != 0u64) by (bit_vector);
    assert(((0x7FF8_0000_0000_0001u64 >> 52u64) & 0x7FFu64) == 0x7FFu64) by (bit_vector);
    assert((0x7FF8_0000_0000_0001u64 & 0x000F_FFFF_FFFF_FFFFu64) != 0u64) by (bit_vector);
}

/// `Number::equal` is symmetric, and `Number::lessThan` is irreflexive and asymmetric.
pub proof fn lemma_number_order_properties(x: JsNumber, y: JsNumber)
    ensures
        spec_number_equal(x, y) == spec_number_equal(y, x),
        spec_number_less_than(x, x) != Some(true),
        spec_number_less_than(x, y) == Some(true) ==> spec_number_less_than(y, x) == Some(false),
{
}

/// Burger-Dybvig invariant: whenever the previous remainder satisfied `!high` (`r + m_plus < s_den` for
/// `even`, `<= s_den` for `!even`) and `d = (r * 10) / s_den` (`rem = (r * 10) % s_den`), reaching
/// `high` at the current step implies `d < 9` (so `d + 1 <= 9` never carries past a single decimal digit).
pub proof fn lemma_bd_high_implies_d_lt_9(r: nat, s_den: nat, m_plus: nat, rem: nat, d: nat, even: bool)
    requires
        s_den >= 1,
        even ==> (r + m_plus < s_den),
        !even ==> (r + m_plus <= s_den),
        r * 10 == d * s_den + rem,
        even ==> (rem + m_plus * 10 >= s_den),
        !even ==> (rem + m_plus * 10 > s_den),
    ensures
        d < 9,
{
    if d >= 9 {
        if even {
            assert(false) by (nonlinear_arith)
                requires
                    r + m_plus < s_den,
                    r * 10 == d * s_den + rem,
                    d >= 9,
                    s_den >= 1,
                    rem + m_plus * 10 >= s_den;
        } else {
            assert(false) by (nonlinear_arith)
                requires
                    r + m_plus <= s_den,
                    r * 10 == d * s_den + rem,
                    d >= 9,
                    s_den >= 1,
                    rem + m_plus * 10 > s_den;
        }
    }
}

/// IEEE-754 binary64 addition and multiplication are commutative on all bit patterns.
pub proof fn lemma_number_add_mul_commutative(x: JsNumber, y: JsNumber)
    ensures
        spec_number_add(x, y) == spec_number_add(y, x),
        spec_number_mul(x, y) == spec_number_mul(y, x),
{
    let (_, sig_x, _) = spec_unpack_finite_nonzero(x);
    let (_, sig_y, _) = spec_unpack_finite_nonzero(y);
    let ix = sig_x as int;
    let iy = sig_y as int;
    assert(ix * iy == iy * ix) by (nonlinear_arith);
}

proof fn lemma_neg_mod_u32(mag: nat)
    ensures
        (if (mag % 0x1_0000_0000nat) == 0 {
            0int
        } else {
            (0x1_0000_0000nat - (mag % 0x1_0000_0000nat)) as int
        }) == (-(mag as int)) % 0x1_0000_0000int,
{
    let m: int = 0x1_0000_0000int;
    let z: int = mag as int;
    let r: int = z % m;
    if r == 0 {
        assert((-z) % m == 0) by (nonlinear_arith)
            requires m == 0x1_0000_0000int, z >= 0, z % m == 0;
    } else {
        assert((-z) % m == m - r) by (nonlinear_arith)
            requires m == 0x1_0000_0000int, z >= 0, r == z % m, 0 < r, r < m;
    }
}

proof fn lemma_u64_shr_is_div_pow2(sig: u64, rsh: u64)
    requires
        1 <= rsh <= 52,
    ensures
        (sig >> rsh) as nat == (sig as nat) / pow2_nat(rsh as nat),
    decreases rsh,
{
    if rsh == 1 {
        reveal_with_fuel(pow2_nat, 2);
        assert((sig >> 1u64) == sig / 2u64) by (bit_vector);
    } else {
        let prev = (rsh - 1) as u64;
        lemma_u64_shr_is_div_pow2(sig, prev);
        assert((sig >> rsh) == ((sig >> prev) >> 1u64)) by (bit_vector)
            requires 2u64 <= rsh, rsh <= 52u64, prev == sub(rsh, 1u64);
        let q1: u64 = sig >> prev;
        assert((q1 >> 1u64) == q1 / 2u64) by (bit_vector);
        let p_prev = pow2_nat(prev as nat);
        lemma_pow2_pos(prev as nat);
        assert(pow2_nat(rsh as nat) == 2nat * p_prev);
        let sn = sig as nat;
        assert((sn / p_prev) / 2nat == sn / (2nat * p_prev)) by (nonlinear_arith)
            requires p_prev >= 1;
    }
}

proof fn lemma_u64_shl_mod32_is_mul_pow2(sig: u64, lsh: u64)
    requires
        0 <= lsh <= 31,
    ensures
        (((sig & 0xFFFF_FFFFu64) << lsh) & 0xFFFF_FFFFu64) as nat
            == ((sig as nat) * pow2_nat(lsh as nat)) % 0x1_0000_0000nat,
    decreases lsh,
{
    if lsh == 0 {
        reveal_with_fuel(pow2_nat, 1);
        assert((((sig & 0xFFFF_FFFFu64) << 0u64) & 0xFFFF_FFFFu64) == sig % 0x1_0000_0000u64)
            by (bit_vector);
        assert((sig as nat) * 1nat == sig as nat);
    } else {
        let prev = (lsh - 1) as u64;
        lemma_u64_shl_mod32_is_mul_pow2(sig, prev);
        let prev_lo: u64 = ((sig & 0xFFFF_FFFFu64) << prev) & 0xFFFF_FFFFu64;
        let sh1: u64 = prev_lo << 1u64;
        assert(
            (((sig & 0xFFFF_FFFFu64) << lsh) & 0xFFFF_FFFFu64) == (sh1 & 0xFFFF_FFFFu64)
            && prev_lo <= 0xFFFF_FFFFu64
            && sh1 / 2u64 == prev_lo
            && sh1 % 2u64 == 0u64
            && (sh1 & 0xFFFF_FFFFu64) == sh1 % 0x1_0000_0000u64
        ) by (bit_vector)
            requires
                1u64 <= lsh,
                lsh <= 31u64,
                prev == sub(lsh, 1u64),
                prev_lo == (((sig & 0xFFFF_FFFFu64) << prev) & 0xFFFF_FFFFu64),
                sh1 == (prev_lo << 1u64);
        assert(sh1 as nat == 2nat * (prev_lo as nat));
        let p_prev = pow2_nat(prev as nat);
        assert(pow2_nat(lsh as nat) == 2nat * p_prev);
        let sn = sig as nat;
        let m = 0x1_0000_0000nat;
        assert((2nat * ((sn * p_prev) % m)) % m == (sn * (2nat * p_prev)) % m)
            by (nonlinear_arith)
            requires m == 0x1_0000_0000nat;
    }
}

/// ECMA-262 §7.1.7 soundness theorem: for every finite `JsNumber`, bit-extracted `spec_to_uint32(x)`
/// equals mathematical `truncate(ℝ(x)) modulo 2^32` (`spec_trunc_finite_int(x) % 2^32`).
pub proof fn lemma_to_uint32_matches_ecma_modulo(x: JsNumber)
    requires
        spec_is_finite(x),
    ensures
        spec_to_uint32(x) as int == spec_trunc_finite_int(x) % 0x1_0000_0000int,
{
    if spec_is_zero(x) {
        assert(0int % 0x1_0000_0000int == 0);
    } else {
        let xb = x.0;
        let exp = spec_exp_bits(xb);
        let mant = spec_mant_bits(xb);
        let sign = spec_sign_bit(xb);
        let (_, sig, exp2) = spec_unpack_finite_nonzero(x);
        assert(mant < 0x0010_0000_0000_0000u64) by (bit_vector)
            requires mant == (xb & 0x000F_FFFF_FFFF_FFFFu64);
        if exp < 1023u64 {
            // |x| < 1, so sig < 2^53 <= 2^(-exp2) and integer truncation is 0.
            if exp == 0 {
                assert(mant > 0u64) by (bit_vector)
                    requires
                        ((xb >> 52u64) & 0x7FFu64) == 0u64,
                        (xb & 0x7FFF_FFFF_FFFF_FFFFu64) != 0u64,
                        mant == (xb & 0x000F_FFFF_FFFF_FFFFu64);
                lemma_bit_len_u64_range(mant);
                lemma_subnormal_shift_range(mant, spec_bit_len_u64(mant));
            } else {
                assert((0x0010_0000_0000_0000u64 | mant) < 0x0020_0000_0000_0000u64) by (bit_vector)
                    requires mant < 0x0010_0000_0000_0000u64;
            }
            assert(exp2 <= -53);
            lemma_pow2_54_56_57();
            reveal_with_fuel(pow2_nat, 3);
            assert(pow2_nat(54) == 2nat * pow2_nat(53));
            assert(pow2_nat(53) == 0x0020_0000_0000_0000nat);
            let k = (-exp2) as nat;
            if 53 < k {
                lemma_pow2_strict_mono(53, k);
            }
            let pk = pow2_nat(k);
            let sn = sig as nat;
            assert(sn / pk == 0) by (nonlinear_arith)
                requires sn < pk, pk >= 1;
            assert(spec_trunc_finite_int(x) == 0);
            assert(0int % 0x1_0000_0000int == 0);
        } else if exp < 1075u64 {
            let rsh: u64 = (1075 - exp) as u64;
            lemma_u64_shr_is_div_pow2(sig, rsh);
            let q: u64 = sig >> rsh;
            assert((q & 0xFFFF_FFFFu64) == q % 0x1_0000_0000u64) by (bit_vector);
            let mag: nat = (sig as nat) / pow2_nat(rsh as nat);
            assert(((q & 0xFFFF_FFFFu64) as nat) == mag % 0x1_0000_0000nat);
            if sign {
                lemma_neg_mod_u32(mag);
            } else {
                assert(((mag % 0x1_0000_0000nat) as int) == (mag as int) % 0x1_0000_0000int);
            }
        } else if exp < 1107u64 {
            let lsh: u64 = (exp - 1075) as u64;
            lemma_u64_shl_mod32_is_mul_pow2(sig, lsh);
            let mag: nat = (sig as nat) * pow2_nat(lsh as nat);
            if sign {
                lemma_neg_mod_u32(mag);
            } else {
                assert(((mag % 0x1_0000_0000nat) as int) == (mag as int) % 0x1_0000_0000int);
            }
        } else {
            let lsh: nat = (exp - 1075) as nat;
            assert(lsh >= 32);
            crate::bigint::lemma_pow2_32();
            lemma_pow2_add(32, (lsh - 32) as nat);
            let p_rem = pow2_nat((lsh - 32) as nat);
            let sn = sig as nat;
            let mag: nat = sn * pow2_nat(lsh);
            assert(mag == (sn * p_rem) * 0x1_0000_0000nat) by (nonlinear_arith)
                requires mag == sn * (0x1_0000_0000nat * p_rem);
            assert(mag % 0x1_0000_0000nat == 0) by (nonlinear_arith)
                requires mag == (sn * p_rem) * 0x1_0000_0000nat;
            if sign {
                lemma_neg_mod_u32(mag);
            } else {
                assert((mag as int) % 0x1_0000_0000int == 0);
            }
        }
    }
}

/// ECMA-262 §7.1.6 soundness theorem: for every finite `JsNumber`, `spec_to_int32(x)` equals
/// `let int32bit = truncate(ℝ(x)) modulo 2^32; if int32bit >= 2^31 { int32bit - 2^32 } else { int32bit }`.
pub proof fn lemma_to_int32_matches_ecma_modulo(x: JsNumber)
    requires
        spec_is_finite(x),
    ensures
        ({
            let int32bit = spec_trunc_finite_int(x) % 0x1_0000_0000int;
            spec_to_int32(x) as int == if int32bit >= 0x8000_0000int {
                int32bit - 0x1_0000_0000int
            } else {
                int32bit
            }
        }),
{
    lemma_to_uint32_matches_ecma_modulo(x);
}

proof fn lemma_pack_rne_mag32_extract(sign: bool, mag: u64)
    requires
        1 <= mag <= 0xFFFF_FFFFu64,
    ensures
        ({
            let n = spec_pack_rne(sign, mag as u128, 0);
            let m32 = mag as u32;
            spec_to_uint32(n) == if sign && m32 != 0u32 {
                (0x1_0000_0000u64 - mag) as u32
            } else {
                m32
            }
        }),
{
    let m: u128 = mag as u128;
    assert(((m >> 64u128) as u64) == 0u64 && ((m & 0xFFFF_FFFF_FFFF_FFFFu128) as u64) == mag)
        by (bit_vector)
        requires m == (mag as u128);
    let bl = spec_bit_len_u64(mag);
    assert(1u32 <= bl && bl <= 32u32) by (bit_vector)
        requires 1u64 <= mag, mag <= 0xFFFF_FFFFu64, bl == spec_bit_len_u64(mag);
    let sign_mask: u64 = if sign { 0x8000_0000_0000_0000u64 } else { 0u64 };
    let lsh: u64 = (53 - bl) as u64;
    let q: u64 = mag << lsh;
    let biased_exp: u64 = (bl + 1022) as u64;
    let bits: u64 = sign_mask | (biased_exp << 52u64) | (q & 0x000F_FFFF_FFFF_FFFFu64);
    assert(spec_pack_rne(sign, m, 0) == JsNumber(bits));
    let rsh: u64 = (1075 - biased_exp) as u64;
    assert(
        ((bits >> 52u64) & 0x7FFu64) == biased_exp
        && (bits & 0x7FFF_FFFF_FFFF_FFFFu64) != 0u64
        && (((bits >> 63u64) != 0u64) == sign)
        && (((0x0010_0000_0000_0000u64 | (bits & 0x000F_FFFF_FFFF_FFFFu64)) >> rsh) & 0xFFFF_FFFFu64) == mag
    ) by (bit_vector)
        requires
            1u64 <= mag,
            mag <= 0xFFFF_FFFFu64,
            bl == spec_bit_len_u64(mag),
            1u32 <= bl,
            bl <= 32u32,
            sign_mask == (if sign { 0x8000_0000_0000_0000u64 } else { 0u64 }),
            lsh == sub(53u64, bl as u64),
            q == (mag << lsh),
            biased_exp == add(bl as u64, 1022u64),
            rsh == sub(1075u64, biased_exp),
            bits == (sign_mask | (biased_exp << 52u64) | (q & 0x000F_FFFF_FFFF_FFFFu64));
}

/// Exact roundtrip: `ToUint32(Number::from_u32(v)) == v` for all `u32`.
pub proof fn lemma_from_u32_to_uint32_roundtrip(v: u32)
    ensures
        spec_to_uint32(spec_from_u32(v)) == v,
{
    if v == 0 {
        assert(((0u64 >> 52u64) & 0x7FFu64) == 0u64) by (bit_vector);
        assert((0u64 & 0x7FFF_FFFF_FFFF_FFFFu64) == 0u64) by (bit_vector);
    } else {
        lemma_pack_rne_mag32_extract(false, v as u64);
    }
}

/// Exact roundtrip: `ToInt32(Number::from_i32(v)) == v` for all `i32` (including `i32::MIN`).
pub proof fn lemma_from_i32_to_int32_roundtrip(v: i32)
    ensures
        spec_to_int32(spec_from_i32(v)) == v,
{
    if v == 0 {
        assert(((0u64 >> 52u64) & 0x7FFu64) == 0u64) by (bit_vector);
        assert((0u64 & 0x7FFF_FFFF_FFFF_FFFFu64) == 0u64) by (bit_vector);
    } else if v > 0 {
        lemma_pack_rne_mag32_extract(false, v as u64);
    } else {
        let mag: u64 = (-(v as int)) as u64;
        lemma_pack_rne_mag32_extract(true, mag);
    }
}

proof fn lemma_bit_len_u64_range(x: u64)
    ensures
        x == 0 ==> spec_bit_len_u64(x) == 0,
        x > 0 ==> (1 <= spec_bit_len_u64(x) && spec_bit_len_u64(x) <= 64),
        (0 < x && x < 0x0010_0000_0000_0000u64) ==> (1 <= spec_bit_len_u64(x) && spec_bit_len_u64(x) <= 52),
{
    if x > 0 {
        assert(1u32 <= spec_bit_len_u64(x) && spec_bit_len_u64(x) <= 64u32) by (bit_vector)
            requires x > 0u64;
    }
    if x > 0 && x < 0x0010_0000_0000_0000u64 {
        assert(1u32 <= spec_bit_len_u64(x) && spec_bit_len_u64(x) <= 52u32) by (bit_vector)
            requires x > 0u64, x < 0x0010_0000_0000_0000u64;
    }
}

proof fn lemma_subnormal_shift_range(mant: u64, bl: u32)
    requires
        0 < mant < 0x0010_0000_0000_0000u64,
        bl == spec_bit_len_u64(mant),
    ensures
        1 <= 53 - bl <= 52,
        0x0010_0000_0000_0000u64 <= (mant << ((53 - bl) as u64)) < 0x0020_0000_0000_0000u64,
{
    assert(1u32 <= 53u32 - bl && 53u32 - bl <= 52u32
        && 0x0010_0000_0000_0000u64 <= (mant << ((53u32 - bl) as u64))
        && (mant << ((53u32 - bl) as u64)) < 0x0020_0000_0000_0000u64)
        by (bit_vector)
        requires
            0u64 < mant,
            mant < 0x0010_0000_0000_0000u64,
            bl == spec_bit_len_u64(mant);
}

proof fn lemma_bit_len_u128_pack_bounds(m: u128, bl: u32)
    requires
        m > 0,
        bl == spec_bit_len_u128(m),
    ensures
        1 <= bl <= 128,
        bl <= 53 ==> m < 0x0020_0000_0000_0000u128,
{
    let hi: u64 = (m >> 64u128) as u64;
    let lo: u64 = (m & 0xFFFF_FFFF_FFFF_FFFFu128) as u64;
    if hi != 0 {
        lemma_bit_len_u64_range(hi);
    } else {
        assert(lo > 0u64) by (bit_vector)
            requires m > 0u128, (m >> 64u128) as u64 == 0u64, lo == (m & 0xFFFF_FFFF_FFFF_FFFFu128) as u64;
        lemma_bit_len_u64_range(lo);
    }
    if bl <= 53 {
        assert(m < 0x0020_0000_0000_0000u128) by (bit_vector)
            requires m > 0u128, bl == spec_bit_len_u128(m), bl <= 53u32;
    }
}

proof fn lemma_pack_lsh_bound(m: u128, bl: u32, lsh: u32)
    requires
        m > 0,
        bl == spec_bit_len_u128(m),
        bl + lsh <= 53,
    ensures
        ((m as u64) << (lsh as u64)) < 0x0020_0000_0000_0000u64,
{
    assert(((m as u64) << (lsh as u64)) < 0x0020_0000_0000_0000u64) by (bit_vector)
        requires m > 0u128, bl == spec_bit_len_u128(m), bl <= 53u32, lsh <= sub(53u32, bl);
}

proof fn lemma_pack_rsh_bound(m: u128, bl: u32, sh: u32)
    requires
        m > 0,
        bl == spec_bit_len_u128(m),
        1 <= sh <= 127,
        (bl as int) - (sh as int) <= 53,
    ensures
        (m >> (sh as u128)) < 0x0020_0000_0000_0000u128,
{
    assert((m >> (sh as u128)) < 0x0020_0000_0000_0000u128) by (bit_vector)
        requires
            m > 0u128,
            bl == spec_bit_len_u128(m),
            1u32 <= sh,
            sh <= 127u32,
            bl <= add(sh, 53u32);
}

proof fn lemma_nat_bit_len_bounds(v: nat)
    requires
        v >= 1,
    ensures
        spec_nat_bit_len(v) >= 1,
        pow2_nat((spec_nat_bit_len(v) - 1) as nat) <= v,
        v < pow2_nat(spec_nat_bit_len(v)),
    decreases v,
{
    if v == 1 {
        assert(v / 2 == 0);
        assert(spec_nat_bit_len(1) == 1);
    } else {
        let half = v / 2;
        assert(half >= 1 && half < v) by (nonlinear_arith)
            requires v >= 2, half == v / 2;
        lemma_nat_bit_len_bounds(half);
        let bh = spec_nat_bit_len(half);
        let p_lo = pow2_nat((bh - 1) as nat);
        let p_hi = pow2_nat(bh);
        assert(pow2_nat(bh) == 2nat * p_lo);
        assert(pow2_nat(bh + 1) == 2nat * p_hi);
        assert(2nat * p_lo <= v && v < 2nat * p_hi) by (nonlinear_arith)
            requires p_lo <= half, half < p_hi, half == v / 2;
    }
}

proof fn lemma_pow2_strict_mono(a: nat, b: nat)
    requires
        a < b,
    ensures
        pow2_nat(a) < pow2_nat(b),
    decreases b - a,
{
    lemma_pow2_pos(a);
    if a + 1 < b {
        lemma_pow2_strict_mono(a, (b - 1) as nat);
    }
}

proof fn lemma_nat_bit_len_unique(v: nat, k: nat)
    requires
        v >= 1,
        k >= 1,
        pow2_nat((k - 1) as nat) <= v,
        v < pow2_nat(k),
    ensures
        spec_nat_bit_len(v) == k,
{
    lemma_nat_bit_len_bounds(v);
    let b = spec_nat_bit_len(v);
    if k < b {
        if k < (b - 1) as nat {
            lemma_pow2_strict_mono(k, (b - 1) as nat);
        }
        assert(false);
    } else if b < k {
        if b < (k - 1) as nat {
            lemma_pow2_strict_mono(b, (k - 1) as nat);
        }
        assert(false);
    }
}

// -------------------------------------------------------------------------------------------
// Executable Implementations
// -------------------------------------------------------------------------------------------

fn sign_bit_exec(b: u64) -> (s: bool)
    ensures
        s == spec_sign_bit(b),
{
    (b >> 63u64) != 0
}

fn exp_bits_exec(b: u64) -> (e: u64)
    ensures
        e == spec_exp_bits(b),
        e <= 0x7FFu64,
{
    let e = (b >> 52u64) & 0x7FFu64;
    proof {
        assert(((b >> 52u64) & 0x7FFu64) <= 0x7FFu64) by (bit_vector);
    }
    e
}

fn mant_bits_exec(b: u64) -> (m: u64)
    ensures
        m == spec_mant_bits(b),
        m < 0x0010_0000_0000_0000u64,
{
    let m = b & 0x000F_FFFF_FFFF_FFFFu64;
    proof {
        assert((b & 0x000F_FFFF_FFFF_FFFFu64) < 0x0010_0000_0000_0000u64) by (bit_vector);
    }
    m
}

fn bit_len_u64_exec(x: u64) -> (bl: u32)
    ensures
        bl == spec_bit_len_u64(x),
        x == 0 ==> bl == 0,
        x > 0 ==> (1 <= bl && bl <= 64),
{
    if x == 0 {
        return 0;
    }
    let x32: u64 = if x >= 0x1_0000_0000u64 { x >> 32u64 } else { x };
    let n32: u32 = if x >= 0x1_0000_0000u64 { 32u32 } else { 0u32 };
    let x16: u64 = if x32 >= 0x1_0000u64 { x32 >> 16u64 } else { x32 };
    let n16: u32 = if x32 >= 0x1_0000u64 { n32 + 16u32 } else { n32 };
    let x8: u64 = if x16 >= 0x100u64 { x16 >> 8u64 } else { x16 };
    let n8: u32 = if x16 >= 0x100u64 { n16 + 8u32 } else { n16 };
    let x4: u64 = if x8 >= 0x10u64 { x8 >> 4u64 } else { x8 };
    let n4: u32 = if x8 >= 0x10u64 { n8 + 4u32 } else { n8 };
    let x2: u64 = if x4 >= 0x4u64 { x4 >> 2u64 } else { x4 };
    let n2: u32 = if x4 >= 0x4u64 { n4 + 2u32 } else { n4 };
    let bl = if x2 >= 0x2u64 { n2 + 2u32 } else { n2 + 1u32 };
    proof {
        lemma_bit_len_u64_range(x);
    }
    bl
}

fn bit_len_u128_exec(m: u128) -> (bl: u32)
    requires
        m > 0,
    ensures
        bl == spec_bit_len_u128(m),
        1 <= bl <= 128,
{
    let hi: u64 = (m >> 64u128) as u64;
    let lo: u64 = (m & 0xFFFF_FFFF_FFFF_FFFFu128) as u64;
    if hi != 0 {
        64u32 + bit_len_u64_exec(hi)
    } else {
        proof {
            assert(lo > 0u64) by (bit_vector)
                requires m > 0u128, (m >> 64u128) as u64 == 0u64, lo == (m & 0xFFFF_FFFF_FFFF_FFFFu128) as u64;
        }
        bit_len_u64_exec(lo)
    }
}

proof fn lemma_not_nan_not_inf_is_finite(x: JsNumber)
    requires
        !spec_is_nan(x),
        !spec_is_infinite(x),
    ensures
        spec_is_finite(x),
{
    let xb: u64 = x.0;
    assert(((xb >> 52u64) & 0x7FFu64) <= 0x7FFu64) by (bit_vector);
}

fn unpack_finite_nonzero_exec(x: JsNumber) -> (u: (bool, u64, i32))
    requires
        spec_is_finite(x),
        !spec_is_zero(x),
    ensures
        u == spec_unpack_finite_nonzero(x),
        0x0010_0000_0000_0000u64 <= u.1 < 0x0020_0000_0000_0000u64,
        -1126 <= u.2 <= 971,
{
    let xb: u64 = x.0;
    let sign = sign_bit_exec(xb);
    let exp = exp_bits_exec(xb);
    let mant = mant_bits_exec(xb);
    if exp == 0 {
        proof {
            assert(mant > 0u64) by (bit_vector)
                requires
                    ((xb >> 52u64) & 0x7FFu64) == 0u64,
                    (xb & 0x7FFF_FFFF_FFFF_FFFFu64) != 0u64,
                    mant == (xb & 0x000F_FFFF_FFFF_FFFFu64);
            lemma_bit_len_u64_range(mant);
        }
        let bl = bit_len_u64_exec(mant);
        proof {
            lemma_subnormal_shift_range(mant, bl);
        }
        let sh: u64 = (53u32 - bl) as u64;
        (sign, mant << sh, -1074i32 - (sh as i32))
    } else {
        let sig = 0x0010_0000_0000_0000u64 | mant;
        proof {
            assert(0x0010_0000_0000_0000u64 <= sig && sig < 0x0020_0000_0000_0000u64)
                by (bit_vector)
                requires mant < 0x0010_0000_0000_0000u64, sig == (0x0010_0000_0000_0000u64 | mant);
        }
        (sign, sig, (exp as i32) - 1075i32)
    }
}

pub fn pack_rne_exec(sign: bool, m: u128, exp2: i32) -> (out: JsNumber)
    requires
        m > 0,
        -5000 <= exp2 <= 5000,
    ensures
        out == spec_pack_rne(sign, m, exp2),
{
    let sign_mask: u64 = if sign { 0x8000_0000_0000_0000u64 } else { 0u64 };
    let inf: JsNumber = if sign { JsNumber::NEG_INFINITY } else { JsNumber::POS_INFINITY };
    let zero: JsNumber = JsNumber(sign_mask);
    let bl = bit_len_u128_exec(m);
    proof {
        lemma_bit_len_u128_pack_bounds(m, bl);
    }
    let unbiased_e: i32 = exp2 + (bl as i32) - 1;
    if unbiased_e > 1023 {
        return inf;
    }
    let target_exp2: i32 = if unbiased_e - 52 > -1074 { unbiased_e - 52 } else { -1074 };
    if exp2 >= target_exp2 {
        let lsh_u32: u32 = (exp2 - target_exp2) as u32;
        proof {
            lemma_pack_lsh_bound(m, bl, lsh_u32);
        }
        let lsh: u64 = lsh_u32 as u64;
        let q: u64 = (m as u64) << lsh;
        if target_exp2 == -1074 {
            JsNumber(sign_mask | q)
        } else {
            let biased_exp: u64 = (target_exp2 + 1075) as u64;
            JsNumber(sign_mask | (biased_exp << 52u64) | (q & 0x000F_FFFF_FFFF_FFFFu64))
        }
    } else {
        let rsh: i32 = target_exp2 - exp2;
        if rsh > 128 {
            zero
        } else if rsh == 128 {
            let half128: u128 = 1u128 << 127u128;
            if m > half128 {
                JsNumber(sign_mask | 1u64)
            } else {
                zero
            }
        } else {
            let sh_u32: u32 = rsh as u32;
            proof {
                lemma_pack_rsh_bound(m, bl, sh_u32);
            }
            let sh: u128 = sh_u32 as u128;
            let q: u64 = (m >> sh) as u64;
            let half: u128 = 1u128 << ((sh - 1u128) as u128);
            proof {
                assert((1u128 << sh) >= 2u128) by (bit_vector)
                    requires 1u128 <= sh, sh <= 127u128;
            }
            let mask: u128 = (1u128 << sh) - 1u128;
            let rem: u128 = m & mask;
            let round_up: bool = (rem > half) || (rem == half && (q & 1u64) == 1u64);
            let q_rounded: u64 = if round_up { q + 1u64 } else { q };
            if target_exp2 == -1074 {
                JsNumber(sign_mask | q_rounded)
            } else if q_rounded >= 0x0020_0000_0000_0000u64 {
                let q_final: u64 = q_rounded >> 1u64;
                let exp_final: i32 = target_exp2 + 1;
                if exp_final > 971 {
                    inf
                } else {
                    let biased_exp: u64 = (exp_final + 1075) as u64;
                    JsNumber(sign_mask | (biased_exp << 52u64) | (q_final & 0x000F_FFFF_FFFF_FFFFu64))
                }
            } else {
                let biased_exp: u64 = (target_exp2 + 1075) as u64;
                JsNumber(sign_mask | (biased_exp << 52u64) | (q_rounded & 0x000F_FFFF_FFFF_FFFFu64))
            }
        }
    }
}

impl JsNumber {
    pub fn is_nan(self) -> (r: bool)
        ensures
            r == spec_is_nan(self),
    {
        exp_bits_exec(self.0) == 0x7FFu64 && mant_bits_exec(self.0) != 0
    }

    pub fn is_pos_zero(self) -> (r: bool)
        ensures
            r == spec_is_pos_zero(self),
    {
        self.0 == 0x0000_0000_0000_0000u64
    }

    pub fn is_neg_zero(self) -> (r: bool)
        ensures
            r == spec_is_neg_zero(self),
    {
        self.0 == 0x8000_0000_0000_0000u64
    }

    pub fn is_zero(self) -> (r: bool)
        ensures
            r == spec_is_zero(self),
    {
        (self.0 & 0x7FFF_FFFF_FFFF_FFFFu64) == 0
    }

    pub fn is_infinite(self) -> (r: bool)
        ensures
            r == spec_is_infinite(self),
    {
        exp_bits_exec(self.0) == 0x7FFu64 && mant_bits_exec(self.0) == 0
    }

    pub fn is_pos_infinite(self) -> (r: bool)
        ensures
            r == spec_is_pos_infinite(self),
    {
        self.0 == 0x7FF0_0000_0000_0000u64
    }

    pub fn is_neg_infinite(self) -> (r: bool)
        ensures
            r == spec_is_neg_infinite(self),
    {
        self.0 == 0xFFF0_0000_0000_0000u64
    }

    pub fn is_finite(self) -> (r: bool)
        ensures
            r == spec_is_finite(self),
    {
        exp_bits_exec(self.0) < 0x7FFu64
    }

    /// ECMA-262 §7.2.6 IsIntegralNumber(argument).
    pub fn is_integral_number(self) -> (r: bool)
        ensures
            r == spec_is_integral_number(self),
    {
        let exp = exp_bits_exec(self.0);
        let mant = mant_bits_exec(self.0);
        if exp == 0x7FFu64 {
            false
        } else if self.is_zero() {
            true
        } else if exp < 1023u64 {
            false
        } else if exp >= 1075u64 {
            true
        } else {
            let frac_bits: u64 = 1075u64 - exp;
            proof {
                assert((1u64 << frac_bits) >= 2u64) by (bit_vector)
                    requires 1u64 <= frac_bits, frac_bits <= 52u64;
            }
            (mant & ((1u64 << frac_bits) - 1u64)) == 0
        }
    }

    /// ECMA-262 §21.1.2.5 Number.isSafeInteger(number).
    pub fn is_safe_integer(self) -> (r: bool)
        ensures
            r == spec_is_safe_integer(self),
    {
        self.is_integral_number() && (self.0 & 0x7FFF_FFFF_FFFF_FFFFu64) <= 0x433F_FFFF_FFFF_FFFFu64
    }

    pub fn canonicalize_nan(self) -> (out: JsNumber)
        ensures
            out == spec_canonicalize_nan(self),
    {
        if self.is_nan() {
            JsNumber::NAN
        } else {
            self
        }
    }

    /// ECMA-262 §6.1.6.1.1 Number::unaryMinus(x).
    pub fn negate(self) -> (out: JsNumber)
        ensures
            out == spec_number_negate(self),
    {
        if self.is_nan() {
            JsNumber::NAN
        } else {
            JsNumber(self.0 ^ 0x8000_0000_0000_0000u64)
        }
    }

    /// ECMA-262 §21.3.2.1 Math.abs(x).
    pub fn abs(self) -> (out: JsNumber)
        ensures
            out == spec_number_abs(self),
    {
        if self.is_nan() {
            JsNumber::NAN
        } else {
            JsNumber(self.0 & 0x7FFF_FFFF_FFFF_FFFFu64)
        }
    }

    /// ECMA-262 §6.1.6.1.13 Number::equal(x, y).
    pub fn equal(self, other: JsNumber) -> (eq: bool)
        ensures
            eq == spec_number_equal(self, other),
    {
        if self.is_nan() || other.is_nan() {
            false
        } else if self.is_zero() && other.is_zero() {
            true
        } else {
            self.0 == other.0
        }
    }

    /// ECMA-262 §6.1.6.1.12 Number::lessThan(x, y).
    pub fn less_than(self, other: JsNumber) -> (lt: Option<bool>)
        ensures
            lt == spec_number_less_than(self, other),
    {
        if self.is_nan() || other.is_nan() {
            None
        } else if self.is_zero() && other.is_zero() {
            Some(false)
        } else if self.0 == other.0 {
            Some(false)
        } else {
            let sx = sign_bit_exec(self.0);
            let sy = sign_bit_exec(other.0);
            if sx != sy {
                Some(sx)
            } else if !sx {
                Some(self.0 < other.0)
            } else {
                Some(self.0 > other.0)
            }
        }
    }

    /// ECMA-262 §6.1.6.1.14 Number::sameValue(x, y).
    pub fn same_value(self, other: JsNumber) -> (sv: bool)
        ensures
            sv == spec_number_same_value(self, other),
    {
        if self.is_nan() || other.is_nan() {
            self.is_nan() && other.is_nan()
        } else {
            self.0 == other.0
        }
    }

    /// ECMA-262 §6.1.6.1.15 Number::sameValueZero(x, y).
    pub fn same_value_zero(self, other: JsNumber) -> (svz: bool)
        ensures
            svz == spec_number_same_value_zero(self, other),
    {
        if self.is_nan() || other.is_nan() {
            self.is_nan() && other.is_nan()
        } else if self.is_zero() && other.is_zero() {
            true
        } else {
            self.0 == other.0
        }
    }

    /// ECMA-262 §7.1.7 ToUint32(argument).
    pub fn to_uint32(self) -> (u: u32)
        ensures
            u == spec_to_uint32(self),
    {
        let exp = exp_bits_exec(self.0);
        let mant = mant_bits_exec(self.0);
        let sign = sign_bit_exec(self.0);
        if exp == 0x7FFu64 || self.is_zero() || exp < 1023u64 || exp >= 1107u64 {
            return 0u32;
        }
        let sig: u64 = 0x0010_0000_0000_0000u64 | mant;
        let mag_mod32: u32 = if exp < 1075u64 {
            let rsh: u64 = 1075u64 - exp;
            ((sig >> rsh) & 0xFFFF_FFFFu64) as u32
        } else {
            let lsh: u64 = exp - 1075u64;
            (((sig & 0xFFFF_FFFFu64) << lsh) & 0xFFFF_FFFFu64) as u32
        };
        if sign && mag_mod32 != 0u32 {
            (0x1_0000_0000u64 - (mag_mod32 as u64)) as u32
        } else {
            mag_mod32
        }
    }

    /// ECMA-262 §7.1.6 ToInt32(argument).
    pub fn to_int32(self) -> (i: i32)
        ensures
            i == spec_to_int32(self),
    {
        let u = self.to_uint32();
        if u >= 0x8000_0000u32 {
            ((u as i64) - 0x1_0000_0000i64) as i32
        } else {
            u as i32
        }
    }

    /// ECMA-262 §7.1.8 ToUint16(argument).
    pub fn to_uint16(self) -> (u: u16)
        ensures
            u == spec_to_uint16(self),
    {
        (self.to_uint32() & 0xFFFFu32) as u16
    }

    pub fn from_u32(v: u32) -> (out: JsNumber)
        ensures
            out == spec_from_u32(v),
    {
        if v == 0 {
            JsNumber::POS_ZERO
        } else {
            pack_rne_exec(false, v as u128, 0)
        }
    }

    pub fn from_i32(v: i32) -> (out: JsNumber)
        ensures
            out == spec_from_i32(v),
    {
        if v == 0 {
            JsNumber::POS_ZERO
        } else if v > 0 {
            pack_rne_exec(false, v as u128, 0)
        } else {
            let mag: u128 = (-(v as i64)) as u128;
            pack_rne_exec(true, mag, 0)
        }
    }

    /// Convert an integral `JsNumber` to exact `JsBigInt`, or `None` if non-integral (`NaN`/`±Inf`/fractional).
    pub fn to_exact_bigint(self) -> (res: Option<JsBigInt>)
        ensures
            match (res, spec_number_to_exact_bigint(self)) {
                (None, None) => true,
                (Some(b), Some(sb)) => b.wf() && b@ == sb,
                _ => false,
            },
    {
        if !self.is_integral_number() {
            return None;
        }
        if self.is_zero() {
            return Some(JsBigInt::zero());
        }
        let sign = sign_bit_exec(self.0);
        let exp = exp_bits_exec(self.0);
        let mant = mant_bits_exec(self.0);
        let sig: u64 = 0x0010_0000_0000_0000u64 | mant;
        if exp < 1075u64 {
            let rsh: u64 = 1075u64 - exp;
            let mag: u64 = sig >> rsh;
            proof {
                assert(mag >= 1u64) by (bit_vector)
                    requires
                        1u64 <= rsh, rsh <= 52u64,
                        sig == (0x0010_0000_0000_0000u64 | mant),
                        mag == (sig >> rsh);
            }
            let pos = JsBigInt::from_u64(mag);
            let out = if sign { pos.neg() } else { pos };
            Some(out)
        } else {
            let lsh: u32 = (exp - 1075u64) as u32;
            proof {
                assert(sig >= 1u64) by (bit_vector)
                    requires sig == (0x0010_0000_0000_0000u64 | mant);
            }
            let pos = JsBigInt::from_u64(sig);
            let limbs = shl_limbs(&pos.limbs, lsh);
            proof {
                lemma_pow2_pos(lsh as nat);
                let vs = sig as nat;
                let pl = pow2_nat(lsh as nat);
                assert(vs * pl >= 1) by (nonlinear_arith)
                    requires vs >= 1, pl >= 1;
                lemma_limbs_wf_zero_iff_empty(limbs@);
            }
            let out = JsBigInt { neg: sign, limbs };
            proof {
                let mag = (sig as nat) * pow2_nat(lsh as nat);
                let z: int = if sign { -(mag as int) } else { mag as int };
                lemma_bigint_from_int_props(z);
                lemma_bigint_canonical_unique(out@, spec_bigint_from_int(z));
            }
            Some(out)
        }
    }

    /// ECMA-262 §6.1.6.1.7 Number::add(x, y).
    pub fn add(self, other: JsNumber) -> (out: JsNumber)
        ensures
            out == spec_number_add(self, other),
    {
        if self.is_nan() || other.is_nan() {
            return JsNumber::NAN;
        }
        let sx = sign_bit_exec(self.0);
        let sy = sign_bit_exec(other.0);
        if self.is_infinite() && other.is_infinite() {
            return if sx == sy {
                if sx { JsNumber::NEG_INFINITY } else { JsNumber::POS_INFINITY }
            } else {
                JsNumber::NAN
            };
        }
        if self.is_infinite() {
            return self;
        }
        if other.is_infinite() {
            return other;
        }
        if self.is_zero() && other.is_zero() {
            return if sx && sy { JsNumber::NEG_ZERO } else { JsNumber::POS_ZERO };
        }
        if self.is_zero() {
            return other;
        }
        if other.is_zero() {
            return self;
        }
        proof {
            lemma_not_nan_not_inf_is_finite(self);
            lemma_not_nan_not_inf_is_finite(other);
        }
        let (sx_u, sig_x, exp_x) = unpack_finite_nonzero_exec(self);
        let (sy_u, sig_y, exp_y) = unpack_finite_nonzero_exec(other);
        if sx_u != sy_u && exp_x == exp_y && sig_x == sig_y {
            return JsNumber::POS_ZERO;
        }
        let (sa, sig_a, exp_a, sb, sig_b, exp_b) =
            if exp_x > exp_y || (exp_x == exp_y && sig_x >= sig_y) {
                (sx_u, sig_x, exp_x, sy_u, sig_y, exp_y)
            } else {
                (sy_u, sig_y, exp_y, sx_u, sig_x, exp_x)
            };
        let diff: i32 = exp_a - exp_b;
        let ma: u128 = (sig_a as u128) << 3u128;
        let raw_b: u128 = (sig_b as u128) << 3u128;
        let mb: u128 = if diff == 0 {
            raw_b
        } else if diff <= 60 {
            let d_u: u128 = diff as u128;
            let shifted: u128 = raw_b >> d_u;
            proof {
                assert((1u128 << d_u) >= 2u128) by (bit_vector)
                    requires 1u128 <= d_u, d_u <= 60u128;
            }
            let rem_mask: u128 = (1u128 << d_u) - 1u128;
            let sticky: u128 = if (raw_b & rem_mask) != 0 { 1u128 } else { 0u128 };
            shifted | sticky
        } else {
            1u128
        };
        proof {
            if sa != sb {
                if diff == 0 {
                    assert(sig_a > sig_b);
                    assert(ma > mb) by (bit_vector)
                        requires
                            0x0010_0000_0000_0000u64 <= sig_b,
                            sig_b < sig_a,
                            sig_a < 0x0020_0000_0000_0000u64,
                            ma == ((sig_a as u128) << 3u128),
                            mb == ((sig_b as u128) << 3u128);
                } else if diff <= 60 {
                    let d_u: u128 = diff as u128;
                    assert(ma > mb) by (bit_vector)
                        requires
                            0x0010_0000_0000_0000u64 <= sig_a,
                            sig_a < 0x0020_0000_0000_0000u64,
                            0x0010_0000_0000_0000u64 <= sig_b,
                            sig_b < 0x0020_0000_0000_0000u64,
                            1u128 <= d_u, d_u <= 60u128,
                            ma == ((sig_a as u128) << 3u128),
                            raw_b == ((sig_b as u128) << 3u128),
                            mb == ((raw_b >> d_u) | (if (raw_b & sub(1u128 << d_u, 1u128)) != 0u128 { 1u128 } else { 0u128 }));
                } else {
                    assert(ma > 1u128) by (bit_vector)
                        requires
                            0x0010_0000_0000_0000u64 <= sig_a,
                            ma == ((sig_a as u128) << 3u128);
                }
            } else {
                assert(ma >= 0x0080_0000_0000_0000u128 && ma <= 0x0100_0000_0000_0000u128)
                    by (bit_vector)
                    requires
                        0x0010_0000_0000_0000u64 <= sig_a,
                        sig_a < 0x0020_0000_0000_0000u64,
                        ma == ((sig_a as u128) << 3u128);
                if diff == 0 {
                    assert(mb <= 0x0100_0000_0000_0000u128) by (bit_vector)
                        requires
                            sig_b < 0x0020_0000_0000_0000u64,
                            mb == ((sig_b as u128) << 3u128);
                } else if diff <= 60 {
                    let d_u: u128 = diff as u128;
                    assert(mb <= 0x0100_0000_0000_0000u128) by (bit_vector)
                        requires
                            sig_b < 0x0020_0000_0000_0000u64,
                            1u128 <= d_u, d_u <= 60u128,
                            raw_b == ((sig_b as u128) << 3u128),
                            mb == ((raw_b >> d_u) | (if (raw_b & sub(1u128 << d_u, 1u128)) != 0u128 { 1u128 } else { 0u128 }));
                }
            }
        }
        let m: u128 = if sa == sb { ma + mb } else { ma - mb };
        pack_rne_exec(sa, m, exp_a - 3)
    }

    /// ECMA-262 §6.1.6.1.8 Number::subtract(x, y).
    pub fn sub(self, other: JsNumber) -> (out: JsNumber)
        ensures
            out == spec_number_sub(self, other),
    {
        if self.is_nan() || other.is_nan() {
            JsNumber::NAN
        } else {
            self.add(other.negate())
        }
    }

    /// ECMA-262 §6.1.6.1.4 Number::multiply(x, y).
    pub fn mul(self, other: JsNumber) -> (out: JsNumber)
        ensures
            out == spec_number_mul(self, other),
    {
        if self.is_nan() || other.is_nan() {
            return JsNumber::NAN;
        }
        let sign = sign_bit_exec(self.0) != sign_bit_exec(other.0);
        if (self.is_infinite() && other.is_zero()) || (self.is_zero() && other.is_infinite()) {
            return JsNumber::NAN;
        }
        if self.is_infinite() || other.is_infinite() {
            return if sign { JsNumber::NEG_INFINITY } else { JsNumber::POS_INFINITY };
        }
        if self.is_zero() || other.is_zero() {
            return if sign { JsNumber::NEG_ZERO } else { JsNumber::POS_ZERO };
        }
        proof {
            lemma_not_nan_not_inf_is_finite(self);
            lemma_not_nan_not_inf_is_finite(other);
        }
        let (_, sig_x, exp_x) = unpack_finite_nonzero_exec(self);
        let (_, sig_y, exp_y) = unpack_finite_nonzero_exec(other);
        let sx128: u128 = sig_x as u128;
        let sy128: u128 = sig_y as u128;
        proof {
            assert(1u128 <= sx128 * sy128 && sx128 * sy128 < 0x0400_0000_0000_0000_0000_0000_0000u128)
                by (nonlinear_arith)
                requires
                    0x0010_0000_0000_0000u128 <= sx128,
                    sx128 < 0x0020_0000_0000_0000u128,
                    0x0010_0000_0000_0000u128 <= sy128,
                    sy128 < 0x0020_0000_0000_0000u128;
        }
        let prod: u128 = sx128 * sy128;
        pack_rne_exec(sign, prod, exp_x + exp_y)
    }

    /// ECMA-262 §6.1.6.1.5 Number::divide(x, y).
    pub fn div(self, other: JsNumber) -> (out: JsNumber)
        ensures
            out == spec_number_div(self, other),
    {
        if self.is_nan() || other.is_nan() {
            return JsNumber::NAN;
        }
        let sign = sign_bit_exec(self.0) != sign_bit_exec(other.0);
        let inf = if sign { JsNumber::NEG_INFINITY } else { JsNumber::POS_INFINITY };
        let zero = if sign { JsNumber::NEG_ZERO } else { JsNumber::POS_ZERO };
        if self.is_infinite() && other.is_infinite() {
            return JsNumber::NAN;
        }
        if self.is_infinite() {
            return inf;
        }
        if other.is_infinite() {
            return zero;
        }
        if self.is_zero() && other.is_zero() {
            return JsNumber::NAN;
        }
        if self.is_zero() {
            return zero;
        }
        if other.is_zero() {
            return inf;
        }
        proof {
            lemma_not_nan_not_inf_is_finite(self);
            lemma_not_nan_not_inf_is_finite(other);
        }
        let (_, sig_x, exp_x) = unpack_finite_nonzero_exec(self);
        let (_, sig_y, exp_y) = unpack_finite_nonzero_exec(other);
        let num: u128 = (sig_x as u128) << 55u128;
        let den: u128 = sig_y as u128;
        proof {
            assert(num >= 0x0800_0000_0000_0000_0000_0000_0000u128
                && num < 0x1000_0000_0000_0000_0000_0000_0000u128)
                by (bit_vector)
                requires
                    0x0010_0000_0000_0000u64 <= sig_x,
                    sig_x < 0x0020_0000_0000_0000u64,
                    num == ((sig_x as u128) << 55u128);
            assert(quot_bounds_ok(num, den)) by {
                assert(num / den >= 1u128 && num / den < 0x0100_0000_0000_0000u128)
                    by (nonlinear_arith)
                    requires
                        num >= 0x0800_0000_0000_0000_0000_0000_0000u128,
                        num < 0x1000_0000_0000_0000_0000_0000_0000u128,
                        0x0010_0000_0000_0000u128 <= den,
                        den < 0x0020_0000_0000_0000u128;
            }
        }
        let quot: u128 = num / den;
        let rem: u128 = num % den;
        proof {
            let sticky: u128 = if rem != 0 { 1u128 } else { 0u128 };
            assert(((quot << 1u128) | sticky) >= 2u128) by (bit_vector)
                requires
                    1u128 <= quot,
                    quot < 0x0100_0000_0000_0000u128,
                    sticky <= 1u128;
        }
        let m: u128 = (quot << 1u128) | (if rem != 0 { 1u128 } else { 0u128 });
        pack_rne_exec(sign, m, exp_x - exp_y - 56)
    }

    /// ECMA-262 §6.1.6.1.20 Number::toString(x, 10).
    pub fn to_js_string(self) -> (out: Utf16Str)
        ensures
            out@ == spec_number_to_string(self),
    {
        number_to_string(self)
    }
}

spec fn quot_bounds_ok(num: u128, den: u128) -> bool {
    num / den >= 1u128 && num / den < 0x0100_0000_0000_0000u128
}

// -------------------------------------------------------------------------------------------
// Executable Exact `StringToNumber` (§7.1.4.1.1) & `Number::toString` (§6.1.6.1.20)
// -------------------------------------------------------------------------------------------

fn u32_bit_len_loop(top: u32) -> (b: u32)
    requires
        top >= 1,
    ensures
        1 <= b <= 32,
        b as nat == spec_nat_bit_len(top as nat),
        pow2_nat((b - 1) as nat) <= top as nat,
        (top as nat) < pow2_nat(b as nat),
{
    let mut cur: u32 = top;
    let mut acc: u32 = 0;
    proof {
        crate::bigint::lemma_pow2_32();
    }
    while cur > 0
        invariant
            acc <= 32,
            (cur as nat) < pow2_nat((32 - acc) as nat),
            spec_nat_bit_len(top as nat) == (acc as nat) + spec_nat_bit_len(cur as nat),
        decreases cur,
    {
        proof {
            let c_nat = cur as nat;
            let p_rem = pow2_nat((32 - acc) as nat);
            assert(acc < 32) by {
                if acc == 32 {
                    assert(pow2_nat(0) == 1);
                    assert(false);
                }
            }
            let p_next = pow2_nat((32 - (acc + 1)) as nat);
            assert(p_rem == 2nat * p_next);
            assert(c_nat / 2 < p_next) by (nonlinear_arith)
                requires c_nat < 2nat * p_next;
        }
        cur = cur / 2u32;
        acc = acc + 1u32;
    }
    proof {
        lemma_nat_bit_len_bounds(top as nat);
    }
    acc
}

fn bit_len_limbs_exec(a: &[u32]) -> (bl: usize)
    requires
        spec_limbs_wf(a@),
        a@.len() > 0,
        a@.len() <= 1_000_000,
    ensures
        bl >= 1,
        bl as nat == spec_nat_bit_len(spec_limbs_nat(a@)),
        bl <= a@.len() * 32,
{
    let w = a.len();
    let top = a[w - 1];
    proof {
        assert(top == a@.last());
    }
    let b = u32_bit_len_loop(top);
    let bl: usize = (w - 1) * 32 + (b as usize);
    proof {
        let k_words = (w - 1) as nat;
        let pre = a@.drop_last();
        lemma_limbs_upper_bound(pre);
        lemma_pow32_pos(k_words);
        // pow32(k_words) == pow2_nat(k_words * 32)
        lemma_pow32_eq_pow2_local(k_words);
        let pw = pow2_nat(k_words * 32);
        let vp = spec_limbs_nat(pre);
        let va = spec_limbs_nat(a@);
        let tnat = top as nat;
        let pb_lo = pow2_nat((b - 1) as nat);
        let pb_hi = pow2_nat(b as nat);
        lemma_pow2_add(k_words * 32, (b - 1) as nat);
        lemma_pow2_add(k_words * 32, b as nat);
        assert((bl - 1) as nat == k_words * 32 + ((b - 1) as nat));
        assert((bl as nat) == k_words * 32 + (b as nat));
        assert(pow2_nat((bl - 1) as nat) == pw * pb_lo);
        assert(pow2_nat(bl as nat) == pw * pb_hi);
        assert(pw * pb_lo <= va) by (nonlinear_arith)
            requires va == vp + tnat * pw, pb_lo <= tnat, pw >= 1;
        assert(va < pw * pb_hi) by (nonlinear_arith)
            requires va == vp + tnat * pw, vp < pw, tnat + 1 <= pb_hi, pw >= 1;
        assert(va >= 1) by (nonlinear_arith)
            requires pw >= 1, pb_lo >= 1, pw * pb_lo <= va;
        lemma_nat_bit_len_unique(va, bl as nat);
    }
    bl
}

proof fn lemma_pow32_eq_pow2_local(w: nat)
    ensures
        pow32(w) == pow2_nat(w * 32),
    decreases w,
{
    if w == 0 {
        assert(0nat * 32 == 0);
    } else {
        lemma_pow32_eq_pow2_local((w - 1) as nat);
        assert(w * 32 == (w - 1) * 32 + 32) by (nonlinear_arith)
            requires w >= 1;
        lemma_pow2_add(((w - 1) * 32) as nat, 32);
        crate::bigint::lemma_pow2_32();
        let p = pow2_nat(((w - 1) * 32) as nat);
        assert(p * 0x1_0000_0000nat == 0x1_0000_0000nat * p) by (nonlinear_arith);
    }
}

/// 57-bit binary long division of `num` by `den` when `val(num) < 2^57 * val(den)`.
fn div_57_limbs(num: &[u32], den: &[u32]) -> (qr: (u64, bool))
    requires
        spec_limbs_wf(num@),
        spec_limbs_wf(den@),
        den@.len() > 0,
        spec_limbs_nat(num@) < pow2_nat(57) * spec_limbs_nat(den@),
    ensures
        qr.0 < 0x0200_0000_0000_0000u64,
        qr.0 as nat == spec_limbs_nat(num@) / spec_limbs_nat(den@),
        qr.1 == ((spec_limbs_nat(num@) % spec_limbs_nat(den@)) != 0),
{
    let mut rem: Vec<u32> = clone_limbs(num);
    let mut quot: u64 = 0u64;
    let mut k: u32 = 57u32;
    proof {
        lemma_limbs_wf_lower_bound(den@);
        lemma_pow32_pos((den@.len() - 1) as nat);
        let vd = spec_limbs_nat(den@);
        let p57 = pow2_nat(57);
        assert(0nat * p57 * vd == 0) by (nonlinear_arith);
    }
    while k > 0
        invariant
            k <= 57,
            spec_limbs_wf(den@),
            den@.len() > 0,
            spec_limbs_nat(den@) >= 1,
            spec_limbs_wf(rem@),
            (quot as nat) < pow2_nat((57 - k) as nat),
            spec_limbs_nat(rem@) < pow2_nat(k as nat) * spec_limbs_nat(den@),
            spec_limbs_nat(num@)
                == (quot as nat) * pow2_nat(k as nat) * spec_limbs_nat(den@) + spec_limbs_nat(rem@),
        decreases k,
    {
        let b: u32 = k - 1u32;
        let shifted_den = shl_limbs(den, b);
        let c = cmp_limbs(&rem, &shifted_den);
        proof {
            lemma_pow2_54_56_57();
            let pb = pow2_nat(b as nat);
            let pk = pow2_nat(k as nat);
            assert(pk == 2nat * pb);
            let p_qk = pow2_nat((57 - k) as nat);
            let p_qb = pow2_nat((57 - b) as nat);
            assert(p_qb == 2nat * p_qk);
            if (57 - b) < 57 {
                lemma_pow2_strict_mono((57 - b) as nat, 57);
            }
            assert(p_qb <= 0x0200_0000_0000_0000nat);
            let qn = quot as nat;
            assert(2nat * qn + 1 < p_qb) by (nonlinear_arith)
                requires qn < p_qk, p_qb == 2nat * p_qk;
        }
        if c >= 0 {
            let new_rem = sub_limbs(&rem, &shifted_den);
            let new_quot: u64 = quot * 2u64 + 1u64;
            proof {
                let pb = pow2_nat(b as nat);
                let pk = pow2_nat(k as nat);
                assert(pk == 2nat * pb);
                let vd = spec_limbs_nat(den@);
                let vr = spec_limbs_nat(rem@);
                let vsd = spec_limbs_nat(shifted_den@);
                let vnr = spec_limbs_nat(new_rem@);
                let qn = quot as nat;
                assert(vsd == vd * pb);
                assert(vnr == vr - vsd);
                assert(vnr < pb * vd) by (nonlinear_arith)
                    requires vr < (2nat * pb) * vd, vsd == vd * pb, vnr == vr - vsd;
                assert((2nat * qn + 1) * pb * vd + vnr == qn * (2nat * pb) * vd + vr)
                    by (nonlinear_arith)
                    requires vsd == vd * pb, vnr == vr - vsd;
            }
            rem = new_rem;
            quot = new_quot;
        } else {
            let new_quot: u64 = quot * 2u64;
            proof {
                let pb = pow2_nat(b as nat);
                let pk = pow2_nat(k as nat);
                assert(pk == 2nat * pb);
                let vd = spec_limbs_nat(den@);
                let vr = spec_limbs_nat(rem@);
                let vsd = spec_limbs_nat(shifted_den@);
                let qn = quot as nat;
                assert(vsd == vd * pb);
                assert(vr < pb * vd) by (nonlinear_arith)
                    requires vr < vsd, vsd == vd * pb;
                assert((2nat * qn) * pb * vd + vr == qn * (2nat * pb) * vd + vr)
                    by (nonlinear_arith);
            }
            quot = new_quot;
        }
        k = b;
    }
    let rem_nz = rem.len() > 0;
    proof {
        lemma_pow2_54_56_57();
        assert(pow2_nat(0) == 1);
        assert(pow2_nat(57) == 0x0200_0000_0000_0000nat);
        let vn = spec_limbs_nat(num@);
        let vd = spec_limbs_nat(den@);
        let vr = spec_limbs_nat(rem@);
        let qn = quot as nat;
        assert(qn * 1 * vd == qn * vd) by (nonlinear_arith);
        assert(1nat * vd == vd) by (nonlinear_arith);
        assert(vn / vd == qn && vn % vd == vr) by (nonlinear_arith)
            requires vn == qn * vd + vr, vr < vd, vd >= 1;
        lemma_limbs_wf_zero_iff_empty(rem@);
    }
    (quot, rem_nz)
}

proof fn lemma_pow2_54_56_57()
    ensures
        pow2_nat(0) == 1,
        pow2_nat(54) == 0x0040_0000_0000_0000nat,
        pow2_nat(56) == 0x0100_0000_0000_0000nat,
        pow2_nat(57) == 0x0200_0000_0000_0000nat,
{
    crate::bigint::lemma_pow2_32();
    reveal_with_fuel(pow2_nat, 12);
    assert(pow2_nat(6) == 64nat);
    lemma_pow2_add(16, 6);
    assert(pow2_nat(22) == 0x40_0000nat);
    lemma_pow2_add(32, 22);
    assert(pow2_nat(54) == 0x0040_0000_0000_0000nat);
    lemma_pow2_add(54, 2);
    assert(pow2_nat(56) == 0x0100_0000_0000_0000nat);
    lemma_pow2_add(56, 1);
    assert(pow2_nat(57) == 0x0200_0000_0000_0000nat);
}

proof fn lemma_rational_scaled_bounds(
    vn: nat,
    vd: nat,
    bl_num: usize,
    bl_den: usize,
    shift: i32,
    vns: nat,
    vds: nat,
)
    requires
        vn >= 1,
        vd >= 1,
        1 <= bl_num <= 20_000_000,
        1 <= bl_den <= 20_000_000,
        bl_num as nat == spec_nat_bit_len(vn),
        bl_den as nat == spec_nat_bit_len(vd),
        shift as int == 55 - ((bl_num as int) - (bl_den as int)),
        shift >= 0 ==> (vns == vn * pow2_nat(shift as nat) && vds == vd),
        shift < 0 ==> (vns == vn && vds == vd * pow2_nat((-shift) as nat)),
    ensures
        vds >= 1,
        vns < pow2_nat(57) * vds,
        vns / vds >= 1,
{
    lemma_nat_bit_len_bounds(vn);
    lemma_nat_bit_len_bounds(vd);
    lemma_pow2_54_56_57();
    let p54 = pow2_nat(54);
    let p56 = pow2_nat(56);
    let p57 = pow2_nat(57);
    if shift >= 0 {
        let sh = shift as nat;
        lemma_pow2_pos(sh);
        assert((bl_num as nat) + sh == 56 + ((bl_den - 1) as nat));
        lemma_pow2_add(bl_num as nat, sh);
        lemma_pow2_add(56, (bl_den - 1) as nat);
        let pn = pow2_nat(bl_num as nat);
        let psh = pow2_nat(sh);
        let pd_lo = pow2_nat((bl_den - 1) as nat);
        assert(vn * psh < pn * psh) by (nonlinear_arith)
            requires vn < pn, psh >= 1;
        assert(pn * psh == p56 * pd_lo);
        assert(p56 * pd_lo <= p56 * vd) by (nonlinear_arith)
            requires pd_lo <= vd, p56 >= 1;
        assert(p56 * vd < p57 * vd) by (nonlinear_arith)
            requires vd >= 1, p57 == 2nat * p56, p56 >= 1;

        assert(((bl_num - 1) as nat) + sh == 54 + (bl_den as nat));
        lemma_pow2_add((bl_num - 1) as nat, sh);
        lemma_pow2_add(54, bl_den as nat);
        let pn_lo = pow2_nat((bl_num - 1) as nat);
        let pd_hi = pow2_nat(bl_den as nat);
        assert(pn_lo * psh <= vn * psh) by (nonlinear_arith)
            requires pn_lo <= vn, psh >= 1;
        assert(pn_lo * psh == p54 * pd_hi);
        assert(p54 * vd < p54 * pd_hi) by (nonlinear_arith)
            requires vd < pd_hi, p54 >= 1;
    } else {
        let rsh = (-shift) as nat;
        lemma_pow2_pos(rsh);
        let prsh = pow2_nat(rsh);
        assert(vd * prsh >= 1) by (nonlinear_arith)
            requires vd >= 1, prsh >= 1;
        assert((bl_num as nat) == 56 + (((bl_den - 1) as nat) + rsh));
        lemma_pow2_add(56, ((bl_den - 1) as nat) + rsh);
        lemma_pow2_add((bl_den - 1) as nat, rsh);
        let pd_lo = pow2_nat((bl_den - 1) as nat);
        assert(p56 * (pd_lo * prsh) <= p56 * (vd * prsh)) by (nonlinear_arith)
            requires pd_lo <= vd, prsh >= 1, p56 >= 1;
        assert(p56 * (vd * prsh) < p57 * (vd * prsh)) by (nonlinear_arith)
            requires vd >= 1, prsh >= 1, p57 == 2nat * p56, p56 >= 1;

        assert(((bl_num - 1) as nat) == 54 + ((bl_den as nat) + rsh));
        lemma_pow2_add(54, (bl_den as nat) + rsh);
        lemma_pow2_add(bl_den as nat, rsh);
        let pd_hi = pow2_nat(bl_den as nat);
        assert(p54 * (vd * prsh) < p54 * (pd_hi * prsh)) by (nonlinear_arith)
            requires vd < pd_hi, prsh >= 1, p54 >= 1;
    }
    assert(vns / vds >= 1) by (nonlinear_arith)
        requires vns > p54 * vds, p54 >= 1, vds >= 1;
}

fn one_limbs_vec() -> (v: Vec<u32>)
    ensures
        spec_limbs_wf(v@),
        v@.len() == 1,
        spec_limbs_nat(v@) == 1,
{
    let mut v: Vec<u32> = Vec::with_capacity(1);
    v.push(1u32);
    proof {
        reveal_with_fuel(spec_limbs_nat, 3);
        reveal_with_fuel(pow32, 2);
        assert(v@ =~= seq![1u32]);
        assert((seq![1u32]).drop_last() =~= Seq::<u32>::empty());
    }
    v
}

fn rational_to_number_rne_exec(
    sign: bool,
    num: &[u32],
    den: &[u32],
    base_exp2: i32,
) -> (out: JsNumber)
    requires
        spec_limbs_wf(num@),
        spec_limbs_wf(den@),
        num@.len() > 0,
        den@.len() > 0,
        num@.len() <= 500_000,
        den@.len() <= 200,
        -2000 <= base_exp2 <= 2000,
    ensures
        out == spec_rational_to_number_rne(
            sign,
            spec_limbs_nat(num@),
            spec_limbs_nat(den@),
            base_exp2 as int,
        ),
{
    let bl_num = bit_len_limbs_exec(num);
    let bl_den = bit_len_limbs_exec(den);
    let approx_exp2: i64 = (base_exp2 as i64) + (bl_num as i64) - (bl_den as i64);
    if approx_exp2 > 1025 {
        return if sign { JsNumber::NEG_INFINITY } else { JsNumber::POS_INFINITY };
    }
    if approx_exp2 < -1080 {
        return if sign { JsNumber::NEG_ZERO } else { JsNumber::POS_ZERO };
    }
    let shift: i32 = 55i32 - ((bl_num as i32) - (bl_den as i32));
    let (num_s, den_s) = if shift >= 0 {
        (shl_limbs(num, shift as u32), clone_limbs(den))
    } else {
        (clone_limbs(num), shl_limbs(den, (-shift) as u32))
    };
    let adj_exp2: i32 = base_exp2 - shift;
    proof {
        lemma_limbs_wf_lower_bound(num@);
        lemma_pow32_pos((num@.len() - 1) as nat);
        lemma_limbs_wf_lower_bound(den@);
        lemma_pow32_pos((den@.len() - 1) as nat);
        lemma_rational_scaled_bounds(
            spec_limbs_nat(num@),
            spec_limbs_nat(den@),
            bl_num,
            bl_den,
            shift,
            spec_limbs_nat(num_s@),
            spec_limbs_nat(den_s@),
        );
        lemma_limbs_wf_zero_iff_empty(den_s@);
    }
    let (quot, rem_nz) = div_57_limbs(&num_s, &den_s);
    proof {
        let sticky: u128 = if rem_nz { 1u128 } else { 0u128 };
        assert((((quot as u128) << 1u128) | sticky) >= 2u128) by (bit_vector)
            requires
                1u64 <= quot,
                quot < 0x0200_0000_0000_0000u64,
                sticky <= 1u128;
    }
    let m: u128 = ((quot as u128) << 1u128) | (if rem_nz { 1u128 } else { 0u128 });
    pack_rne_exec(sign, m, adj_exp2 - 1)
}

fn parse_radix_to_number_exec(digits: &Utf16Str, radix: u32) -> (out: JsNumber)
    requires
        radix == 2 || radix == 8 || radix == 16,
        digits@.len() > 0,
    ensures
        out == match crate::bigint::spec_parse_radix_digits(digits@, radix as nat) {
            None => JsNumber(0x7FF8_0000_0000_0000u64),
            Some(v) => if v == 0 { JsNumber(0u64) } else { spec_rational_to_number_rne(false, v, 1, 0) },
        },
{
    let n = digits.len();
    let mut limbs: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    let mut overflow_huge: bool = false;
    proof {
        assert(digits@.subrange(0, 0) =~= Seq::<u16>::empty());
    }
    while i < n
        invariant
            i <= n,
            n == digits@.len(),
            radix == 2 || radix == 8 || radix == 16,
            spec_limbs_wf(limbs@),
            !overflow_huge ==> (
                limbs@.len() <= 200
                && crate::bigint::spec_parse_radix_digits(digits@.subrange(0, i as int), radix as nat)
                    == Some(spec_limbs_nat(limbs@))
            ),
            overflow_huge ==> (
                limbs@.len() > 200
                && match crate::bigint::spec_parse_radix_digits(digits@.subrange(0, i as int), radix as nat) {
                    None => false,
                    Some(v) => v >= pow32(200),
                }
            ),
        decreases n - i,
    {
        let u = digits.code_unit_at(i);
        let d_opt: Option<u32> = if u >= 0x30 && u <= 0x39 {
            let v = (u - 0x30) as u32;
            if v < radix { Some(v) } else { None }
        } else if u >= 0x41 && u <= 0x5A {
            let v = (u - 0x41 + 10) as u32;
            if v < radix { Some(v) } else { None }
        } else if u >= 0x61 && u <= 0x7A {
            let v = (u - 0x61 + 10) as u32;
            if v < radix { Some(v) } else { None }
        } else {
            None
        };
        proof {
            assert(digits@.subrange(0, (i + 1) as int).drop_last() =~= digits@.subrange(0, i as int));
            assert(digits@.subrange(0, (i + 1) as int).last() == u);
        }
        match d_opt {
            None => {
                proof {
                    lemma_radix_none_propagates_local(digits@, radix as nat, (i + 1) as nat);
                }
                return JsNumber::NAN;
            }
            Some(d) => {
                if !overflow_huge {
                    limbs = mul_limb_add(&limbs, radix, d);
                    if limbs.len() > 200 {
                        overflow_huge = true;
                        proof {
                            lemma_limbs_wf_lower_bound(limbs@);
                            crate::bigint::lemma_pow32_mono(200, (limbs@.len() - 1) as nat);
                        }
                    }
                } else {
                    proof {
                        let prev = crate::bigint::spec_parse_radix_digits(
                            digits@.subrange(0, i as int),
                            radix as nat,
                        ).unwrap();
                        let p200 = pow32(200);
                        let nr = radix as nat;
                        let nd = d as nat;
                        assert(prev * nr + nd >= p200) by (nonlinear_arith)
                            requires prev >= p200, nr >= 2;
                    }
                }
            }
        }
        i = i + 1;
    }
    proof {
        assert(digits@.subrange(0, n as int) =~= digits@);
    }
    if overflow_huge {
        proof {
            let v = crate::bigint::spec_parse_radix_digits(digits@, radix as nat).unwrap();
            lemma_pow32_pos(200);
            lemma_pow32_eq_pow2_local(200);
            assert(200nat * 32 == 6400);
            lemma_nat_bit_len_bounds(v);
            let bl = spec_nat_bit_len(v);
            if bl < 6400 {
                lemma_pow2_strict_mono(bl, 6400);
                assert(false);
            } else if bl == 6400 {
                assert(false);
            }
            assert(spec_nat_bit_len(1) == 1) by {
                reveal_with_fuel(spec_nat_bit_len, 3);
                assert(1nat / 2 == 0);
            }
        }
        return JsNumber::POS_INFINITY;
    }
    if limbs.len() == 0 {
        proof {
            lemma_limbs_wf_zero_iff_empty(limbs@);
        }
        return JsNumber::POS_ZERO;
    }
    proof {
        lemma_limbs_wf_zero_iff_empty(limbs@);
    }
    let one = one_limbs_vec();
    rational_to_number_rne_exec(false, &limbs, &one, 0)
}

proof fn lemma_radix_none_propagates_local(s: Seq<u16>, radix: nat, k: nat)
    requires
        k <= s.len(),
        crate::bigint::spec_parse_radix_digits(s.subrange(0, k as int), radix) is None,
    ensures
        crate::bigint::spec_parse_radix_digits(s, radix) is None,
    decreases s.len() - k,
{
    if k == s.len() {
        assert(s.subrange(0, k as int) =~= s);
    } else {
        let next = s.subrange(0, (k + 1) as int);
        assert(next.drop_last() =~= s.subrange(0, k as int));
        lemma_radix_none_propagates_local(s, radix, k + 1);
    }
}

struct ExecDecMantissa {
    sig: Vec<u32>,
    sig_count: usize,
    exp_adj: i128,
    tail_nz: bool,
    total_digits: usize,
}

impl ExecDecMantissa {
    spec fn wf(&self, pos: usize) -> bool {
        &&& spec_limbs_wf(self.sig@)
        &&& self.sig_count <= 800
        &&& self.sig@.len() <= self.sig_count
        &&& (self.sig_count == 0 <==> self.sig@.len() == 0)
        &&& (self.sig_count == 0 ==> !self.tail_nz)
        &&& self.total_digits <= pos
        &&& -(pos as int) <= self.exp_adj <= (pos as int)
    }

    spec fn to_spec(&self) -> SpecDecMantissa {
        SpecDecMantissa {
            sig: spec_limbs_nat(self.sig@),
            sig_count: self.sig_count as nat,
            exp_adj: self.exp_adj as int,
            tail_nz: self.tail_nz,
            total_digits: self.total_digits as nat,
        }
    }
}

proof fn lemma_sig_limbs_len_bound(sig: Seq<u32>, cnt: nat)
    requires
        spec_limbs_wf(sig),
        spec_limbs_nat(sig) < pow_nat(10, cnt) || (cnt == 0 && sig.len() == 0),
    ensures
        sig.len() <= cnt,
{
    if sig.len() > cnt {
        lemma_limbs_wf_lower_bound(sig);
        crate::bigint::lemma_pow32_mono(cnt, (sig.len() - 1) as nat);
        lemma_pow10_le_pow32(cnt);
        assert(false);
    }
}

proof fn lemma_pow10_le_pow32(k: nat)
    ensures
        pow_nat(10, k) <= pow32(k),
    decreases k,
{
    if k > 0 {
        lemma_pow10_le_pow32((k - 1) as nat);
        let a = pow_nat(10, (k - 1) as nat);
        let b = pow32((k - 1) as nat);
        assert(10nat * a <= 0x1_0000_0000nat * b) by (nonlinear_arith)
            requires a <= b;
    }
}

fn match_infinity_exec(s: &Utf16Str) -> (m: bool)
    ensures
        m == spec_match_infinity(s@),
{
    s.len() == 8
        && s.code_unit_at(0) == 0x49u16
        && s.code_unit_at(1) == 0x6Eu16
        && s.code_unit_at(2) == 0x66u16
        && s.code_unit_at(3) == 0x69u16
        && s.code_unit_at(4) == 0x6Eu16
        && s.code_unit_at(5) == 0x69u16
        && s.code_unit_at(6) == 0x74u16
        && s.code_unit_at(7) == 0x79u16
}

fn parse_unsigned_decimal_exec(s: &Utf16Str, sign: bool) -> (out: JsNumber)
    ensures
        out == spec_parse_unsigned_decimal(s@, sign),
{
    let n = s.len();
    let init = ExecDecMantissa {
        sig: Vec::new(),
        sig_count: 0,
        exp_adj: 0,
        tail_nz: false,
        total_digits: 0,
    };
    let (pos1, mut st) = scan_dec_digits_exec_bounded(s, 0, init, false);
    let pos2: usize = if pos1 < n && s.code_unit_at(pos1) == 0x2Eu16 {
        let (p2, st2) = scan_dec_digits_exec_bounded(s, pos1 + 1, st, true);
        st = st2;
        p2
    } else {
        pos1
    };
    if st.total_digits == 0 {
        return JsNumber::NAN;
    }
    let cap: i128 = (n as i128) + 2000i128;
    let ghost spec_exp_part: int;
    let exp_part: i128 = if pos2 == n {
        proof {
            spec_exp_part = 0int;
        }
        0i128
    } else if s.code_unit_at(pos2) == 0x65u16 || s.code_unit_at(pos2) == 0x45u16 {
        let p_sign = pos2 + 1;
        if p_sign >= n {
            return JsNumber::NAN;
        }
        let (exp_neg, p_dig) = if s.code_unit_at(p_sign) == 0x2Du16 {
            (true, p_sign + 1)
        } else if s.code_unit_at(p_sign) == 0x2Bu16 {
            (false, p_sign + 1)
        } else {
            (false, p_sign)
        };
        let mut p_cur: usize = p_dig;
        let mut acc: i128 = 0;
        let mut cnt: usize = 0;
        let ghost mut true_acc: int = 0;
        proof {
            assert(usize::BITS <= 64);
            assert((n as i128) <= 0xFFFF_FFFF_FFFF_FFFFi128);
        }
        while p_cur < n && s.code_unit_at(p_cur) >= 0x30 && s.code_unit_at(p_cur) <= 0x39
            invariant
                p_dig <= p_cur <= n,
                n == s@.len(),
                (n as i128) <= 0xFFFF_FFFF_FFFF_FFFFi128,
                cap == (n as i128) + 2000i128,
                0 <= acc <= cap * 10 + 9,
                acc <= cap ==> (acc as int == true_acc),
                acc > cap ==> (true_acc >= acc as int && true_acc > cap as int),
                cnt == p_cur - p_dig,
                spec_scan_exp_digits(s@, p_dig as nat, 0, 0)
                    == spec_scan_exp_digits(s@, p_cur as nat, true_acc, cnt as nat),
            decreases n - p_cur,
        {
            let d = (s.code_unit_at(p_cur) - 0x30) as i128;
            let ghost old_ta = true_acc;
            let next_acc: i128 = if acc <= cap { acc * 10 + d } else { acc };
            proof {
                true_acc = old_ta * 10 + (d as int);
                if acc > cap {
                    assert(true_acc >= old_ta && true_acc > cap as int) by (nonlinear_arith)
                        requires
                            old_ta >= acc as int,
                            acc > cap,
                            cap >= 2000,
                            d >= 0,
                            true_acc == old_ta * 10 + (d as int);
                }
            }
            acc = next_acc;
            p_cur = p_cur + 1;
            cnt = cnt + 1;
        }
        if cnt == 0 || p_cur != n {
            return JsNumber::NAN;
        }
        proof {
            spec_exp_part = if exp_neg { -true_acc } else { true_acc };
        }
        if exp_neg { -acc } else { acc }
    } else {
        return JsNumber::NAN;
    };
    if st.sig_count == 0 {
        return if sign { JsNumber::NEG_ZERO } else { JsNumber::POS_ZERO };
    }
    let (final_sig, final_cnt, final_adj): (Vec<u32>, usize, i128) = if st.tail_nz {
        let s10 = mul_limb_add(&st.sig, 10, 1);
        proof {
            lemma_limbs_wf_zero_iff_empty(s10@);
            lemma_sig_limbs_len_bound(s10@, (st.sig_count + 1) as nat);
        }
        (s10, st.sig_count + 1, st.exp_adj - 1)
    } else {
        (st.sig, st.sig_count, st.exp_adj)
    };
    proof {
        assert(usize::BITS <= 64);
        assert((n as i128) <= 0xFFFF_FFFF_FFFF_FFFFi128);
        assert(-(n as int) - 1 <= final_adj as int && final_adj as int <= (n as int));
        assert(1 <= final_cnt && final_cnt <= 801);
        if exp_part > cap {
            assert(spec_exp_part > (n as int) + 2000);
            assert((final_adj as int) + (exp_part as int) + (final_cnt as int) - 1 > 310);
            assert((final_adj as int) + spec_exp_part + (final_cnt as int) - 1 > 310);
        } else if exp_part < -cap {
            assert(spec_exp_part < -((n as int) + 2000));
            assert((final_adj as int) + (exp_part as int) + (final_cnt as int) - 1 < -326);
            assert((final_adj as int) + spec_exp_part + (final_cnt as int) - 1 < -326);
        } else {
            assert(exp_part as int == spec_exp_part);
        }
    }
    let exp10: i128 = final_adj + exp_part;
    let sci_exp10: i128 = exp10 + (final_cnt as i128) - 1;
    if sci_exp10 > 310 {
        return if sign { JsNumber::NEG_INFINITY } else { JsNumber::POS_INFINITY };
    }
    if sci_exp10 < -326 {
        return if sign { JsNumber::NEG_ZERO } else { JsNumber::POS_ZERO };
    }
    if exp10 >= 0 {
        let p10 = pow_u32_limbs(10, exp10 as u32);
        let num = mul_limbs(&final_sig, &p10);
        let one = one_limbs_vec();
        proof {
            lemma_limbs_wf_lower_bound(final_sig@);
            lemma_pow32_pos((final_sig@.len() - 1) as nat);
            lemma_limbs_wf_lower_bound(p10@);
            lemma_pow32_pos((p10@.len() - 1) as nat);
            let vs = spec_limbs_nat(final_sig@);
            let vp = spec_limbs_nat(p10@);
            assert(vs * vp >= 1) by (nonlinear_arith)
                requires vs >= 1, vp >= 1;
            lemma_limbs_wf_zero_iff_empty(num@);
            lemma_pow10_mul_bound(vs, final_cnt as nat, exp10 as nat, num@);
        }
        rational_to_number_rne_exec(sign, &num, &one, 0)
    } else {
        let k: u32 = (-exp10) as u32;
        let den = pow_u32_limbs(5, k);
        proof {
            lemma_pow5_limbs_len_bound(den@, k as nat);
        }
        rational_to_number_rne_exec(sign, &final_sig, &den, exp10 as i32)
    }
}

proof fn lemma_pow10_pos(k: nat)
    ensures
        pow_nat(10, k) >= 1,
    decreases k,
{
    if k > 0 {
        lemma_pow10_pos((k - 1) as nat);
    }
}

proof fn lemma_pow10_mul_bound(vs: nat, cnt: nat, e10: nat, num: Seq<u32>)
    requires
        spec_limbs_wf(num),
        vs < pow_nat(10, cnt),
        spec_limbs_nat(num) == vs * pow_nat(10, e10),
        cnt <= 801,
        e10 <= 310,
    ensures
        num.len() <= 500_000,
{
    lemma_pow10_pos(e10);
    lemma_pow10_le_pow32(cnt);
    lemma_pow10_le_pow32(e10);
    let pc = pow32(cnt);
    let pe = pow32(e10);
    let vn = spec_limbs_nat(num);
    let p_ech = pow_nat(10, e10);
    let p_cch = pow_nat(10, cnt);
    assert(vn < p_cch * p_ech) by (nonlinear_arith)
        requires vn == vs * p_ech, vs < p_cch, p_ech >= 1;
    assert(p_cch * p_ech <= pc * pe) by (nonlinear_arith)
        requires p_cch <= pc, p_ech <= pe, p_cch >= 0, p_ech >= 0;
    crate::bigint::lemma_pow32_add(cnt, e10);
    if num.len() > cnt + e10 {
        lemma_limbs_wf_lower_bound(num);
        crate::bigint::lemma_pow32_mono(cnt + e10, (num.len() - 1) as nat);
        assert(false);
    }
}

proof fn lemma_pow5_limbs_len_bound(den: Seq<u32>, k: nat)
    requires
        spec_limbs_wf(den),
        spec_limbs_nat(den) == pow_nat(5, k),
        k <= 1200,
    ensures
        den.len() <= 200,
{
    // 5^8 = 390625 < 2^32, so 5^(8 * q) < (2^32)^q: for k <= 1200, 5^k <= 5^1200 = (5^8)^150 < pow32(150)!
    lemma_pow5_le_pow32_div8(k);
    if den.len() > 200 {
        lemma_limbs_wf_lower_bound(den);
        crate::bigint::lemma_pow32_mono(151, (den.len() - 1) as nat);
        crate::bigint::lemma_pow32_mono((k / 8) + 1, 151);
        assert(false);
    }
}

proof fn lemma_pow5_le_pow32_div8(k: nat)
    ensures
        pow_nat(5, k) < pow32((k / 8) + 1),
    decreases k,
{
    if k < 8 {
        assert(k / 8 == 0);
        reveal_with_fuel(pow_nat, 9);
        reveal_with_fuel(pow32, 2);
        assert(pow32(1) == 0x1_0000_0000nat);
    } else {
        lemma_pow5_le_pow32_div8((k - 8) as nat);
        reveal_with_fuel(pow_nat, 9);
        let prev = pow_nat(5, (k - 8) as nat);
        assert(pow_nat(5, k) == 390625nat * prev) by {
            // Unfold 8 steps of pow_nat(5, ...):
            assert(pow_nat(5, (k - 7) as nat) == 5nat * prev);
            assert(pow_nat(5, (k - 6) as nat) == 5nat * pow_nat(5, (k - 7) as nat));
            assert(pow_nat(5, (k - 5) as nat) == 5nat * pow_nat(5, (k - 6) as nat));
            assert(pow_nat(5, (k - 4) as nat) == 5nat * pow_nat(5, (k - 5) as nat));
            assert(pow_nat(5, (k - 3) as nat) == 5nat * pow_nat(5, (k - 4) as nat));
            assert(pow_nat(5, (k - 2) as nat) == 5nat * pow_nat(5, (k - 3) as nat));
            assert(pow_nat(5, (k - 1) as nat) == 5nat * pow_nat(5, (k - 2) as nat));
            assert(pow_nat(5, k) == 5nat * pow_nat(5, (k - 1) as nat));
            assert(5nat * (5nat * (5nat * (5nat * (5nat * (5nat * (5nat * (5nat * prev))))))) == 390625nat * prev)
                by (nonlinear_arith);
        }
        assert((k / 8) == ((k - 8) as nat) / 8 + 1) by (nonlinear_arith)
            requires k >= 8;
        let q = ((k - 8) as nat) / 8 + 1;
        let pq = pow32(q);
        assert(pow32(q + 1) == 0x1_0000_0000nat * pq);
        lemma_pow32_pos(q);
        assert(390625nat * prev < 0x1_0000_0000nat * pq) by (nonlinear_arith)
            requires prev < pq, pq >= 1;
    }
}

fn scan_dec_digits_exec_bounded(
    s: &Utf16Str,
    start_pos: usize,
    mut st: ExecDecMantissa,
    is_frac: bool,
) -> (res: (usize, ExecDecMantissa))
    requires
        start_pos <= s@.len(),
        st.wf(start_pos),
        st.sig_count == 0 ==> spec_limbs_nat(st.sig@) == 0,
        st.sig_count > 0 ==> (1 <= spec_limbs_nat(st.sig@) && spec_limbs_nat(st.sig@) < pow_nat(10, st.sig_count as nat)),
    ensures
        res.0 <= s@.len(),
        res.1.wf(res.0),
        res.1.sig_count == 0 ==> spec_limbs_nat(res.1.sig@) == 0,
        res.1.sig_count > 0 ==> (1 <= spec_limbs_nat(res.1.sig@) && spec_limbs_nat(res.1.sig@) < pow_nat(10, res.1.sig_count as nat)),
        (res.0 as nat, res.1.to_spec())
            == spec_scan_dec_digits(s@, start_pos as nat, st.to_spec(), is_frac),
{
    let n = s.len();
    let mut pos: usize = start_pos;
    let ghost init_spec = st.to_spec();
    while pos < n && s.code_unit_at(pos) >= 0x30 && s.code_unit_at(pos) <= 0x39
        invariant
            start_pos <= pos <= n,
            n == s@.len(),
            st.wf(pos),
            st.sig_count == 0 ==> spec_limbs_nat(st.sig@) == 0,
            st.sig_count > 0 ==> (1 <= spec_limbs_nat(st.sig@) && spec_limbs_nat(st.sig@) < pow_nat(10, st.sig_count as nat)),
            spec_scan_dec_digits(s@, start_pos as nat, init_spec, is_frac)
                == spec_scan_dec_digits(s@, pos as nat, st.to_spec(), is_frac),
        decreases n - pos,
    {
        let ghost pre_spec = st.to_spec();
        let d: u32 = (s.code_unit_at(pos) - 0x30) as u32;
        st.total_digits = st.total_digits + 1;
        if st.sig_count == 0 && d == 0 {
            if is_frac {
                st.exp_adj = st.exp_adj - 1;
            }
            proof {
                assert(st.to_spec() == spec_feed_dec_digit(pre_spec, d as nat, is_frac));
            }
        } else if st.sig_count < 800 {
            let ghost old_cnt = st.sig_count as nat;
            let ghost old_val = spec_limbs_nat(st.sig@);
            st.sig = mul_limb_add(&st.sig, 10, d);
            st.sig_count = st.sig_count + 1;
            if is_frac {
                st.exp_adj = st.exp_adj - 1;
            }
            proof {
                let new_val = spec_limbs_nat(st.sig@);
                let nd = d as nat;
                if old_cnt == 0 {
                    assert(old_val == 0);
                    assert(d >= 1);
                    reveal_with_fuel(pow_nat, 2);
                    assert(pow_nat(10, 1) == 10);
                    assert(1 <= new_val && new_val < 10) by (nonlinear_arith)
                        requires new_val == 0 * 10 + nd, 1 <= nd, nd <= 9;
                } else {
                    let p_old = pow_nat(10, old_cnt);
                    assert(pow_nat(10, old_cnt + 1) == 10nat * p_old);
                    assert(1 <= new_val && new_val < 10nat * p_old) by (nonlinear_arith)
                        requires new_val == old_val * 10 + nd, 1 <= old_val, old_val < p_old, nd <= 9;
                }
                lemma_limbs_wf_zero_iff_empty(st.sig@);
                lemma_sig_limbs_len_bound(st.sig@, st.sig_count as nat);
                assert(st.to_spec() == spec_feed_dec_digit(pre_spec, d as nat, is_frac));
            }
        } else {
            if !is_frac {
                st.exp_adj = st.exp_adj + 1;
            }
            if d != 0 {
                st.tail_nz = true;
            }
            proof {
                assert(st.to_spec() == spec_feed_dec_digit(pre_spec, d as nat, is_frac));
            }
        }
        pos = pos + 1;
    }
    (pos, st)
}

/// Round an arbitrary-precision `SpecBigInt` to nearest-even `JsNumber` (ECMA-262 §21.1.1.1 step 2.a).
pub open spec fn spec_bigint_to_number_rne(b: SpecBigInt) -> JsNumber {
    if b.limbs.len() == 0 {
        JsNumber(0u64)
    } else {
        spec_rational_to_number_rne(b.neg, spec_limbs_nat(b.limbs), 1, 0)
    }
}

/// Round a canonical `JsBigInt` to nearest-even `JsNumber` (`Number(bigint)`).
pub fn bigint_to_number_rne(b: &JsBigInt) -> (out: JsNumber)
    requires
        b.wf(),
    ensures
        out == spec_bigint_to_number_rne(b@),
{
    if b.limbs.len() == 0 {
        return JsNumber::POS_ZERO;
    }
    if b.limbs.len() > 200 {
        proof {
            let v = spec_limbs_nat(b.limbs@);
            lemma_limbs_wf_lower_bound(b.limbs@);
            crate::bigint::lemma_pow32_mono(200, (b.limbs@.len() - 1) as nat);
            lemma_pow32_pos(200);
            lemma_pow32_eq_pow2_local(200);
            assert(200nat * 32 == 6400);
            lemma_nat_bit_len_bounds(v);
            let bl = spec_nat_bit_len(v);
            if bl < 6400 {
                lemma_pow2_strict_mono(bl, 6400);
                assert(false);
            } else if bl == 6400 {
                assert(false);
            }
            assert(spec_nat_bit_len(1) == 1) by {
                reveal_with_fuel(spec_nat_bit_len, 3);
                assert(1nat / 2 == 0);
            }
        }
        return if b.neg { JsNumber::NEG_INFINITY } else { JsNumber::POS_INFINITY };
    }
    proof {
        lemma_limbs_wf_zero_iff_empty(b.limbs@);
    }
    let one = one_limbs_vec();
    rational_to_number_rne_exec(b.neg, &b.limbs, &one, 0)
}

/// ECMA-262 §7.1.4.1.1 StringToNumber(str), proved equal to `spec_string_to_number`.
pub fn string_to_number(s: &Utf16Str) -> (out: JsNumber)
    ensures
        out == spec_string_to_number(s@),
{
    let t = s.trim();
    proof {
        crate::utf16::lemma_trim_clean_and_idempotent(s@);
    }
    let n = t.len();
    if n == 0 {
        return JsNumber::POS_ZERO;
    }
    let u0 = t.code_unit_at(0);
    if n >= 2 && u0 == 0x30u16 {
        let u1 = t.code_unit_at(1);
        if u1 == 0x62u16 || u1 == 0x42u16 {
            let digits = t.slice(2, n);
            if digits.len() == 0 {
                return JsNumber::NAN;
            }
            return parse_radix_to_number_exec(&digits, 2);
        }
        if u1 == 0x6Fu16 || u1 == 0x4Fu16 {
            let digits = t.slice(2, n);
            if digits.len() == 0 {
                return JsNumber::NAN;
            }
            return parse_radix_to_number_exec(&digits, 8);
        }
        if u1 == 0x78u16 || u1 == 0x58u16 {
            let digits = t.slice(2, n);
            if digits.len() == 0 {
                return JsNumber::NAN;
            }
            return parse_radix_to_number_exec(&digits, 16);
        }
    }
    let (sign, body) = if u0 == 0x2Du16 {
        (true, t.slice(1, n))
    } else if u0 == 0x2Bu16 {
        (false, t.slice(1, n))
    } else {
        (false, t)
    };
    if body.len() == 0 {
        return JsNumber::NAN;
    }
    if match_infinity_exec(&body) {
        return if sign { JsNumber::NEG_INFINITY } else { JsNumber::POS_INFINITY };
    }
    parse_unsigned_decimal_exec(&body, sign)
}

// Executable Burger-Dybvig `Number::toString` (§6.1.6.1.20):

fn push_zeros_u16(out: &mut Vec<u16>, count: usize)
    ensures
        final(out)@ == old(out)@ + spec_repeat_zero_u16(count as nat),
{
    let ghost pre = out@;
    let mut i: usize = 0;
    while i < count
        invariant
            i <= count,
            out@ == pre + spec_repeat_zero_u16(i as nat),
        decreases count - i,
    {
        out.push(0x30u16);
        proof {
            assert(out@ =~= pre + spec_repeat_zero_u16((i + 1) as nat));
        }
        i = i + 1;
    }
}

fn push_slice_u16(out: &mut Vec<u16>, src: &[u16], start: usize, end: usize)
    requires
        start <= end <= src@.len(),
    ensures
        final(out)@ == old(out)@ + src@.subrange(start as int, end as int),
{
    let ghost pre = out@;
    let mut i: usize = start;
    while i < end
        invariant
            start <= i <= end <= src@.len(),
            out@ == pre + src@.subrange(start as int, i as int),
        decreases end - i,
    {
        out.push(src[i]);
        proof {
            assert(out@ =~= pre + src@.subrange(start as int, (i + 1) as int));
        }
        i = i + 1;
    }
}

fn format_ecmascript_decimal_exec(digits: &[u16], n: i32) -> (out: Utf16Str)
    requires
        1 <= digits@.len() <= 30,
        -400 <= n <= 400,
    ensures
        out@ == spec_format_ecmascript_decimal(digits@, n as int),
{
    let k: usize = digits.len();
    let k_i32: i32 = k as i32;
    let mut out: Vec<u16> = Vec::new();
    if k_i32 <= n && n <= 21 {
        push_slice_u16(&mut out, digits, 0, k);
        let zc: usize = (n - k_i32) as usize;
        push_zeros_u16(&mut out, zc);
        proof {
            assert(Seq::<u16>::empty() + digits@.subrange(0, k as int) =~= digits@);
        }
    } else if 0 < n && n <= 21 {
        let nu: usize = n as usize;
        push_slice_u16(&mut out, digits, 0, nu);
        let ghost p1 = out@;
        out.push(0x2Eu16);
        proof {
            assert(p1 =~= digits@.subrange(0, n as int));
            assert(out@ =~= digits@.subrange(0, n as int) + seq![0x2Eu16]);
        }
        push_slice_u16(&mut out, digits, nu, k);
    } else if -6 < n && n <= 0 {
        out.push(0x30u16);
        out.push(0x2Eu16);
        proof {
            assert(out@ =~= seq![0x30u16, 0x2Eu16]);
        }
        let zc: usize = (-n) as usize;
        push_zeros_u16(&mut out, zc);
        push_slice_u16(&mut out, digits, 0, k);
        proof {
            assert(digits@.subrange(0, k as int) =~= digits@);
        }
    } else {
        let exp_val: i32 = n - 1;
        let exp_sign: u16 = if exp_val > 0 { 0x2Bu16 } else { 0x2Du16 };
        let exp_mag: u64 = if exp_val >= 0 { exp_val as u64 } else { (-exp_val) as u64 };
        proof {
            assert(exp_mag >= 1u64);
        }
        let mag_bi = JsBigInt::from_u64(exp_mag);
        let exp_digits_str = mag_bi.to_string_radix10();
        proof {
            lemma_limbs_wf_zero_iff_empty(mag_bi.limbs@);
            assert(exp_digits_str@ == spec_uint_to_dec_u16(exp_mag as nat));
        }
        if k <= 1 {
            push_slice_u16(&mut out, digits, 0, k);
            let ghost p1 = out@;
            out.push(0x65u16);
            out.push(exp_sign);
            let ghost p2 = out@;
            push_slice_u16(&mut out, &exp_digits_str.units, 0, exp_digits_str.len());
            proof {
                assert(p1 =~= digits@);
                assert(p2 =~= digits@ + seq![0x65u16, exp_sign]);
                assert(exp_digits_str@.subrange(0, exp_digits_str@.len() as int) =~= exp_digits_str@);
                assert(out@ =~= digits@ + (seq![0x65u16, exp_sign] + exp_digits_str@));
            }
        } else {
            out.push(digits[0]);
            out.push(0x2Eu16);
            proof {
                assert(out@ =~= seq![digits@[0], 0x2Eu16]);
            }
            push_slice_u16(&mut out, digits, 1, k);
            let ghost p1 = out@;
            out.push(0x65u16);
            out.push(exp_sign);
            let ghost p2 = out@;
            push_slice_u16(&mut out, &exp_digits_str.units, 0, exp_digits_str.len());
            proof {
                assert(exp_digits_str@.subrange(0, exp_digits_str@.len() as int) =~= exp_digits_str@);
                assert(p2 =~= p1 + seq![0x65u16, exp_sign]);
                assert(out@ =~= p1 + (seq![0x65u16, exp_sign] + exp_digits_str@));
            }
        }
    }
    Utf16Str { units: out }
}

fn positive_finite_to_string_exec(b: u64) -> (out: Utf16Str)
    requires
        0 < b,
        spec_exp_bits(b) < 0x7FFu64,
        !spec_sign_bit(b),
    ensures
        out@ == spec_positive_finite_to_string(b),
{
    let exp_bits = exp_bits_exec(b);
    let mant_bits = mant_bits_exec(b);
    let f: u64 = if exp_bits == 0 { mant_bits } else { 0x0010_0000_0000_0000u64 | mant_bits };
    proof {
        if exp_bits == 0 {
            assert(mant_bits > 0u64) by (bit_vector)
                requires
                    b > 0u64,
                    (b >> 63u64) == 0u64,
                    ((b >> 52u64) & 0x7FFu64) == 0u64,
                    mant_bits == (b & 0x000F_FFFF_FFFF_FFFFu64);
        } else {
            assert((0x0010_0000_0000_0000u64 | mant_bits) >= 0x0010_0000_0000_0000u64) by (bit_vector);
        }
        lemma_bit_len_u64_range(f);
    }
    let e: i32 = if exp_bits == 0 { -1074 } else { (exp_bits as i32) - 1075 };
    let even: bool = (f & 1u64) == 0;
    let lower_boundary: bool = exp_bits > 1 && mant_bits == 0;
    let f_limbs = JsBigInt::from_u64(f).limbs;
    let one_limbs = JsBigInt::from_u64(1).limbs;
    let two_limbs = JsBigInt::from_u64(2).limbs;
    let four_limbs = JsBigInt::from_u64(4).limbs;
    let (mut r, mut s_den, mut m_plus, mut m_minus): (Vec<u32>, Vec<u32>, Vec<u32>, Vec<u32>) =
        if !lower_boundary {
            if e >= 0 {
                let fe = shl_limbs(&f_limbs, e as u32);
                let r_v = mul_limb_add(&fe, 2, 0);
                let mp_v = shl_limbs(&one_limbs, e as u32);
                let mm_v = clone_limbs(&mp_v);
                proof {
                    let v1 = spec_limbs_nat(one_limbs@);
                    let pe = pow2_nat(e as nat);
                    assert(v1 == 1);
                    assert(1nat * pe == pe) by (nonlinear_arith);
                }
                (r_v, two_limbs, mp_v, mm_v)
            } else {
                let r_v = mul_limb_add(&f_limbs, 2, 0);
                let s_v = shl_limbs(&one_limbs, (1 - e) as u32);
                let mp_v = clone_limbs(&one_limbs);
                let mm_v = one_limbs;
                proof {
                    let p = pow2_nat((1 - e) as nat);
                    assert(1nat * p == p) by (nonlinear_arith);
                }
                (r_v, s_v, mp_v, mm_v)
            }
        } else {
            if e >= 0 {
                let fe = shl_limbs(&f_limbs, e as u32);
                let r_v = mul_limb_add(&fe, 4, 0);
                let mp_v = shl_limbs(&one_limbs, (e + 1) as u32);
                let mm_v = shl_limbs(&one_limbs, e as u32);
                proof {
                    let pe = pow2_nat(e as nat);
                    let pe1 = pow2_nat((e + 1) as nat);
                    assert(1nat * pe == pe) by (nonlinear_arith);
                    assert(1nat * pe1 == pe1) by (nonlinear_arith);
                }
                (r_v, four_limbs, mp_v, mm_v)
            } else {
                let r_v = mul_limb_add(&f_limbs, 4, 0);
                let s_v = shl_limbs(&one_limbs, (2 - e) as u32);
                let mp_v = two_limbs;
                let mm_v = one_limbs;
                proof {
                    let p = pow2_nat((2 - e) as nat);
                    assert(1nat * p == p) by (nonlinear_arith);
                }
                (r_v, s_v, mp_v, mm_v)
            }
        };

    let bl_f = bit_len_u64_exec(f);
    let eb: i64 = (e as i64) + (bl_f as i64) - 1;
    let est: i32 = if eb >= 0 {
        ((eb * 30103i64) / 100000i64) as i32
    } else {
        (-(((-eb) * 30103i64) / 100000i64)) as i32
    };
    let mut n: i32 = if est > 0 {
        let p10 = pow_u32_limbs(10, est as u32);
        s_den = mul_limbs(&s_den, &p10);
        est
    } else if est < 0 {
        let p10 = pow_u32_limbs(10, (-est) as u32);
        r = mul_limbs(&r, &p10);
        m_plus = mul_limbs(&m_plus, &p10);
        m_minus = mul_limbs(&m_minus, &p10);
        est
    } else {
        0
    };

    let ghost (r1_sp, s1_sp, mp1_sp, mm1_sp, n1_sp) = (
        spec_limbs_nat(r@),
        spec_limbs_nat(s_den@),
        spec_limbs_nat(m_plus@),
        spec_limbs_nat(m_minus@),
        n as int,
    );

    let mut up_fuel: usize = 16;
    while up_fuel > 0
        invariant
            up_fuel <= 16,
            -360 <= n <= 360 - (up_fuel as int) + 16,
            spec_limbs_wf(r@),
            spec_limbs_wf(s_den@),
            spec_limbs_wf(m_plus@),
            spec_limbs_nat(r@) == r1_sp,
            spec_limbs_nat(m_plus@) == mp1_sp,
            spec_bd_scale_up(r1_sp, s1_sp, mp1_sp, n1_sp, even, 16)
                == spec_bd_scale_up(r1_sp, spec_limbs_nat(s_den@), mp1_sp, n as int, even, up_fuel as nat),
        decreases up_fuel,
    {
        let top = add_limbs(&r, &m_plus);
        let c = cmp_limbs(&top, &s_den);
        let need_up = if even { c >= 0 } else { c > 0 };
        if need_up {
            s_den = mul_limb_add(&s_den, 10, 0);
            n = n + 1;
            up_fuel = up_fuel - 1;
        } else {
            up_fuel = 0;
        }
    }

    let ghost (s2_sp, n2_sp) = (spec_limbs_nat(s_den@), n as int);
    let mut down_fuel: usize = 16;
    while down_fuel > 0
        invariant
            down_fuel <= 16,
            -380 + (down_fuel as int) <= n <= 380,
            spec_limbs_wf(r@),
            spec_limbs_wf(s_den@),
            spec_limbs_wf(m_plus@),
            spec_limbs_wf(m_minus@),
            spec_limbs_nat(s_den@) == s2_sp,
            spec_bd_scale_down(r1_sp, s2_sp, mp1_sp, mm1_sp, n2_sp, even, 16)
                == spec_bd_scale_down(
                    spec_limbs_nat(r@),
                    s2_sp,
                    spec_limbs_nat(m_plus@),
                    spec_limbs_nat(m_minus@),
                    n as int,
                    even,
                    down_fuel as nat,
                ),
        decreases down_fuel,
    {
        let top = add_limbs(&r, &m_plus);
        let top10 = mul_limb_add(&top, 10, 0);
        let c = cmp_limbs(&top10, &s_den);
        let need_down = if even { c < 0 } else { c <= 0 };
        if need_down {
            r = mul_limb_add(&r, 10, 0);
            m_plus = mul_limb_add(&m_plus, 10, 0);
            m_minus = mul_limb_add(&m_minus, 10, 0);
            n = n - 1;
            down_fuel = down_fuel - 1;
        } else {
            down_fuel = 0;
        }
    }

    let ghost (r3_sp, mp3_sp, mm3_sp) = (
        spec_limbs_nat(r@),
        spec_limbs_nat(m_plus@),
        spec_limbs_nat(m_minus@),
    );
    let mut digits: Vec<u16> = Vec::new();
    let mut dig_fuel: usize = 25;
    while dig_fuel > 0
        invariant
            dig_fuel <= 25,
            digits@.len() == 25 - dig_fuel || dig_fuel == 0,
            digits@.len() <= 25,
            spec_limbs_wf(r@),
            spec_limbs_wf(s_den@),
            spec_limbs_wf(m_plus@),
            spec_limbs_wf(m_minus@),
            spec_limbs_nat(s_den@) == s2_sp,
            spec_bd_generate_digits(r3_sp, s2_sp, mp3_sp, mm3_sp, even, 25)
                == digits@ + spec_bd_generate_digits(
                    spec_limbs_nat(r@),
                    s2_sp,
                    spec_limbs_nat(m_plus@),
                    spec_limbs_nat(m_minus@),
                    even,
                    dig_fuel as nat,
                ),
            dig_fuel == 0 ==> digits@.len() >= 1,
        decreases dig_fuel,
    {
        let r10 = mul_limb_add(&r, 10, 0);
        let mp10 = mul_limb_add(&m_plus, 10, 0);
        let mm10 = mul_limb_add(&m_minus, 10, 0);
        let mut rem = r10;
        let mut d: u8 = 0;
        let ghost r10_sp = spec_limbs_nat(rem@);
        while d < 9 && cmp_limbs(&rem, &s_den) >= 0
            invariant
                d <= 9,
                spec_limbs_wf(rem@),
                spec_limbs_wf(s_den@),
                spec_limbs_nat(s_den@) == s2_sp,
                spec_div_digit_10(r10_sp, s2_sp, 0u8)
                    == spec_div_digit_10(spec_limbs_nat(rem@), s2_sp, d),
            decreases 9 - d,
        {
            rem = sub_limbs(&rem, &s_den);
            d = d + 1;
        }
        let c_low = cmp_limbs(&rem, &mm10);
        let low = if even { c_low <= 0 } else { c_low < 0 };
        let rem_plus_mp = add_limbs(&rem, &mp10);
        let c_high = cmp_limbs(&rem_plus_mp, &s_den);
        let high = if even { c_high >= 0 } else { c_high > 0 };
        let ghost pre_digits = digits@;
        if !low && !high {
            let ch: u16 = 0x30u16 + (d as u16);
            digits.push(ch);
            r = rem;
            m_plus = mp10;
            m_minus = mm10;
            dig_fuel = dig_fuel - 1;
            proof {
                let tail = spec_bd_generate_digits(
                    spec_limbs_nat(r@),
                    s2_sp,
                    spec_limbs_nat(m_plus@),
                    spec_limbs_nat(m_minus@),
                    even,
                    dig_fuel as nat,
                );
                assert(digits@ =~= pre_digits + seq![ch]);
                assert((pre_digits + seq![ch]) + tail =~= pre_digits + (seq![ch] + tail));
            }
        } else if low && !high {
            let ch: u16 = 0x30u16 + (d as u16);
            digits.push(ch);
            dig_fuel = 0;
            proof {
                assert(digits@ =~= pre_digits + seq![ch]);
                assert(digits@ + Seq::<u16>::empty() =~= digits@);
            }
        } else if !low && high {
            let d1: u8 = if d < 9 { d + 1 } else { 9 };
            let ch: u16 = 0x30u16 + (d1 as u16);
            digits.push(ch);
            dig_fuel = 0;
            proof {
                assert(digits@ =~= pre_digits + seq![ch]);
                assert(digits@ + Seq::<u16>::empty() =~= digits@);
            }
        } else {
            let r2 = mul_limb_add(&rem, 2, 0);
            let c_mid = cmp_limbs(&r2, &s_den);
            let pick_high = (c_mid > 0) || (c_mid == 0 && (d & 1u8) == 1u8);
            let df: u8 = if pick_high && d < 9 { d + 1 } else { d };
            let ch: u16 = 0x30u16 + (df as u16);
            digits.push(ch);
            dig_fuel = 0;
            proof {
                assert(digits@ =~= pre_digits + seq![ch]);
                assert(digits@ + Seq::<u16>::empty() =~= digits@);
            }
        }
    }
    proof {
        assert(digits@ + Seq::<u16>::empty() =~= digits@);
    }
    format_ecmascript_decimal_exec(&digits, n)
}

/// ECMA-262 §6.1.6.1.20 Number::toString(x, 10), proved equal to `spec_number_to_string`.
pub fn number_to_string(x: JsNumber) -> (out: Utf16Str)
    ensures
        out@ == spec_number_to_string(x),
{
    if x.is_nan() {
        let mut v: Vec<u16> = Vec::with_capacity(3);
        v.push(0x4Eu16);
        v.push(0x61u16);
        v.push(0x4Eu16);
        proof {
            assert(v@ =~= seq![0x4Eu16, 0x61u16, 0x4Eu16]);
        }
        return Utf16Str { units: v };
    }
    if x.is_zero() {
        let mut v: Vec<u16> = Vec::with_capacity(1);
        v.push(0x30u16);
        proof {
            assert(v@ =~= seq![0x30u16]);
        }
        return Utf16Str { units: v };
    }
    let xb: u64 = x.0;
    if sign_bit_exec(xb) {
        let abs_b: u64 = xb & 0x7FFF_FFFF_FFFF_FFFFu64;
        if JsNumber(abs_b).is_pos_infinite() {
            let mut v: Vec<u16> = Vec::with_capacity(9);
            v.push(0x2Du16);
            v.push(0x49u16);
            v.push(0x6Eu16);
            v.push(0x66u16);
            v.push(0x69u16);
            v.push(0x6Eu16);
            v.push(0x69u16);
            v.push(0x74u16);
            v.push(0x79u16);
            proof {
                assert(v@ =~= seq![0x2Du16, 0x49u16, 0x6Eu16, 0x66u16, 0x69u16, 0x6Eu16, 0x69u16, 0x74u16, 0x79u16]);
            }
            return Utf16Str { units: v };
        }
        proof {
            assert(abs_b > 0u64 && ((abs_b >> 52u64) & 0x7FFu64) < 0x7FFu64 && (abs_b >> 63u64) == 0u64)
                by (bit_vector)
                requires
                    (xb & 0x7FFF_FFFF_FFFF_FFFFu64) != 0u64,
                    !(((xb >> 52u64) & 0x7FFu64) == 0x7FFu64 && (xb & 0x000F_FFFF_FFFF_FFFFu64) != 0u64),
                    abs_b == (xb & 0x7FFF_FFFF_FFFF_FFFFu64),
                    abs_b != 0x7FF0_0000_0000_0000u64;
        }
        let pos_str = positive_finite_to_string_exec(abs_b);
        let mut minus_vec: Vec<u16> = Vec::with_capacity(1);
        minus_vec.push(0x2Du16);
        let minus_str = Utf16Str { units: minus_vec };
        proof {
            assert(minus_str@ =~= seq![0x2Du16]);
        }
        return minus_str.concat(&pos_str);
    }
    if x.is_pos_infinite() {
        let mut v: Vec<u16> = Vec::with_capacity(8);
        v.push(0x49u16);
        v.push(0x6Eu16);
        v.push(0x66u16);
        v.push(0x69u16);
        v.push(0x6Eu16);
        v.push(0x69u16);
        v.push(0x74u16);
        v.push(0x79u16);
        proof {
            assert(v@ =~= seq![0x49u16, 0x6Eu16, 0x66u16, 0x69u16, 0x6Eu16, 0x69u16, 0x74u16, 0x79u16]);
        }
        return Utf16Str { units: v };
    }
    proof {
        assert(xb > 0u64 && ((xb >> 52u64) & 0x7FFu64) < 0x7FFu64)
            by (bit_vector)
            requires
                (xb & 0x7FFF_FFFF_FFFF_FFFFu64) != 0u64,
                (xb >> 63u64) == 0u64,
                !(((xb >> 52u64) & 0x7FFu64) == 0x7FFu64 && (xb & 0x000F_FFFF_FFFF_FFFFu64) != 0u64),
                xb != 0x7FF0_0000_0000_0000u64;
    }
    positive_finite_to_string_exec(xb)
}

} // verus!
