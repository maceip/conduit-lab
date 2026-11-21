//! Verified ECMAScript language types, exact IEEE-754 binary64 bit-level operations,
//! arbitrary-precision BigInt comparison, and string numeric conversions used by
//! `generated.rs` (compiled from `tc39/ecma262` `<emu-alg>` clauses).
use vstd::prelude::*;

verus! {

// ===============================================================================================
// 1. Completion Records & Tag Types
// ===============================================================================================

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Unused;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Signedness {
    Unsigned,
    Signed,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum BitwiseOp {
    BitAnd,
    BitXor,
    BitOr,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum AbruptOrNormal<T> {
    Normal(T),
    ThrowTypeError,
}

// ===============================================================================================
// 2. Exact IEEE-754 binary64 `JsNumber` (pure bit/integer arithmetic, zero float casts)
// ===============================================================================================

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct JsNumber(pub u64);

pub const POS_ZERO_BITS: u64 = 0x0000_0000_0000_0000u64;
pub const NEG_ZERO_BITS: u64 = 0x8000_0000_0000_0000u64;
pub const POS_INF_BITS: u64 = 0x7FF0_0000_0000_0000u64;
pub const NEG_INF_BITS: u64 = 0xFFF0_0000_0000_0000u64;
pub const CANON_NAN_BITS: u64 = 0x7FF8_0000_0000_0000u64;
pub const ONE_BITS: u64 = 0x3FF0_0000_0000_0000u64;

pub open spec fn spec_pos_zero() -> JsNumber { JsNumber(0x0000_0000_0000_0000u64) }
pub open spec fn spec_neg_zero() -> JsNumber { JsNumber(0x8000_0000_0000_0000u64) }
pub open spec fn spec_pos_inf() -> JsNumber { JsNumber(0x7FF0_0000_0000_0000u64) }
pub open spec fn spec_neg_inf() -> JsNumber { JsNumber(0xFFF0_0000_0000_0000u64) }
pub open spec fn spec_canon_nan() -> JsNumber { JsNumber(0x7FF8_0000_0000_0000u64) }
pub open spec fn spec_one_num() -> JsNumber { JsNumber(0x3FF0_0000_0000_0000u64) }

pub fn js_pos_zero() -> (r: JsNumber) ensures r == spec_pos_zero() { JsNumber(POS_ZERO_BITS) }
pub fn js_neg_zero() -> (r: JsNumber) ensures r == spec_neg_zero() { JsNumber(NEG_ZERO_BITS) }
pub fn js_pos_inf() -> (r: JsNumber) ensures r == spec_pos_inf() { JsNumber(POS_INF_BITS) }
pub fn js_neg_inf() -> (r: JsNumber) ensures r == spec_neg_inf() { JsNumber(NEG_INF_BITS) }
pub fn js_canon_nan() -> (r: JsNumber) ensures r == spec_canon_nan() { JsNumber(CANON_NAN_BITS) }
pub fn js_one_num() -> (r: JsNumber) ensures r == spec_one_num() { JsNumber(ONE_BITS) }

/// Arithmetic decomposition of IEEE-754 binary64 bits so Z3's linear solver can reason
/// directly without needing bitvector mode in outer theorems.
pub open spec fn spec_sign_bit(x: JsNumber) -> u64 {
    x.0 / 0x8000_0000_0000_0000u64
}

pub open spec fn spec_raw_exp(x: JsNumber) -> u64 {
    (x.0 / 0x0010_0000_0000_0000u64) % 0x800u64
}

pub open spec fn spec_raw_mant(x: JsNumber) -> u64 {
    x.0 % 0x0010_0000_0000_0000u64
}

pub fn sign_bit(x: JsNumber) -> (r: u64)
    ensures r == spec_sign_bit(x), r <= 1,
{
    let b = x.0;
    let r = (b >> 63u64) & 1u64;
    proof {
        assert(((b >> 63u64) & 1u64) == b / 0x8000_0000_0000_0000u64) by (bit_vector);
        assert(((b >> 63u64) & 1u64) <= 1u64) by (bit_vector);
    }
    r
}

pub fn raw_exp(x: JsNumber) -> (r: u64)
    ensures r == spec_raw_exp(x), r <= 0x7FF,
{
    let b = x.0;
    let r = (b >> 52u64) & 0x7FFu64;
    proof {
        assert(((b >> 52u64) & 0x7FFu64) == (b / 0x0010_0000_0000_0000u64) % 0x800u64) by (bit_vector);
        assert(((b >> 52u64) & 0x7FFu64) <= 0x7FFu64) by (bit_vector);
    }
    r
}

pub fn raw_mant(x: JsNumber) -> (r: u64)
    ensures r == spec_raw_mant(x), r < 0x0010_0000_0000_0000u64,
{
    let b = x.0;
    let r = b & 0x000F_FFFF_FFFF_FFFFu64;
    proof {
        assert((b & 0x000F_FFFF_FFFF_FFFFu64) == b % 0x0010_0000_0000_0000u64) by (bit_vector);
        assert((b & 0x000F_FFFF_FFFF_FFFFu64) < 0x0010_0000_0000_0000u64) by (bit_vector);
    }
    r
}

pub open spec fn spec_is_nan(x: JsNumber) -> bool {
    spec_raw_exp(x) == 0x7FFu64 && spec_raw_mant(x) != 0u64
}

pub open spec fn spec_is_pos_zero(x: JsNumber) -> bool {
    x.0 == 0x0000_0000_0000_0000u64
}

pub open spec fn spec_is_neg_zero(x: JsNumber) -> bool {
    x.0 == 0x8000_0000_0000_0000u64
}

pub open spec fn spec_is_pos_inf(x: JsNumber) -> bool {
    x.0 == 0x7FF0_0000_0000_0000u64
}

pub open spec fn spec_is_neg_inf(x: JsNumber) -> bool {
    x.0 == 0xFFF0_0000_0000_0000u64
}

pub open spec fn spec_is_finite_num(x: JsNumber) -> bool {
    spec_raw_exp(x) < 0x7FFu64
}

/// ECMA-262 §6.1.6.1 Number value identity ("_x_ is _y_"):
/// all IEEE-754 NaN bit patterns denote the single ECMAScript *NaN* value, while
/// +0_𝔽 and -0_𝔽 have distinct sign bits and are NOT identical.
pub open spec fn spec_number_is(x: JsNumber, y: JsNumber) -> bool {
    (spec_is_nan(x) && spec_is_nan(y)) || (!spec_is_nan(x) && !spec_is_nan(y) && x.0 == y.0)
}

pub fn num_is_nan(x: JsNumber) -> (r: bool) ensures r == spec_is_nan(x) {
    raw_exp(x) == 0x7FFu64 && raw_mant(x) != 0u64
}

pub fn num_is_pos_zero(x: JsNumber) -> (r: bool) ensures r == spec_is_pos_zero(x) {
    x.0 == POS_ZERO_BITS
}

pub fn num_is_neg_zero(x: JsNumber) -> (r: bool) ensures r == spec_is_neg_zero(x) {
    x.0 == NEG_ZERO_BITS
}

pub fn num_is_pos_inf(x: JsNumber) -> (r: bool) ensures r == spec_is_pos_inf(x) {
    x.0 == POS_INF_BITS
}

pub fn num_is_neg_inf(x: JsNumber) -> (r: bool) ensures r == spec_is_neg_inf(x) {
    x.0 == NEG_INF_BITS
}

pub fn num_is_finite(x: JsNumber) -> (r: bool) ensures r == spec_is_finite_num(x) {
    raw_exp(x) < 0x7FFu64
}

pub fn num_is_same(x: JsNumber, y: JsNumber) -> (r: bool) ensures r == spec_number_is(x, y) {
    let xn = num_is_nan(x);
    let yn = num_is_nan(y);
    (xn && yn) || (!xn && !yn && x.0 == y.0)
}

pub proof fn lemma_bits_unique_from_parts(x: u64)
    ensures
        x == (x / 0x8000_0000_0000_0000u64) * 0x8000_0000_0000_0000u64
            + ((x / 0x0010_0000_0000_0000u64) % 0x800u64) * 0x0010_0000_0000_0000u64
            + (x % 0x0010_0000_0000_0000u64),
{
    assert(x == (x / 0x8000_0000_0000_0000u64) * 0x8000_0000_0000_0000u64
        + ((x / 0x0010_0000_0000_0000u64) % 0x800u64) * 0x0010_0000_0000_0000u64
        + (x % 0x0010_0000_0000_0000u64)) by (bit_vector);
}

// ===============================================================================================
// 3. Powers of 2, Exact Truncated Mathematical Integers (`ExactInt`), Modulo & `𝔽(...)`
// ===============================================================================================

pub open spec fn spec_pow2(k: nat) -> nat
    decreases k,
{
    if k == 0 {
        1nat
    } else {
        2nat * spec_pow2((k - 1) as nat)
    }
}

pub proof fn lemma_pow2_pos(k: nat)
    ensures spec_pow2(k) >= 1,
    decreases k,
{
    if k > 0 {
        lemma_pow2_pos((k - 1) as nat);
    }
}

pub proof fn lemma_pow2_add(a: nat, b: nat)
    ensures spec_pow2(a + b) == spec_pow2(a) * spec_pow2(b),
    decreases a,
{
    if a == 0 {
        assert(0nat + b == b);
        assert(spec_pow2(0) == 1nat);
    } else {
        lemma_pow2_add((a - 1) as nat, b);
        assert(((a - 1) as nat) + b == (a + b - 1) as nat);
        let pa1 = spec_pow2((a - 1) as nat);
        let pb = spec_pow2(b);
        assert(spec_pow2(a) == 2nat * pa1);
        assert((2nat * pa1) * pb == 2nat * (pa1 * pb)) by (nonlinear_arith);
    }
}

pub fn pow2_u64(k: u32) -> (r: u64)
    requires k <= 62,
    ensures r as nat == spec_pow2(k as nat), r >= 1,
{
    let mut acc: u64 = 1;
    let mut i: u32 = 0;
    while i < k
        invariant
            0 <= i <= k,
            k <= 62,
            acc as nat == spec_pow2(i as nat),
            acc <= 0x4000_0000_0000_0000u64,
        decreases k - i,
    {
        proof {
            lemma_pow2_u64_bound(i);
        }
        acc = acc * 2;
        i = i + 1;
    }
    proof { lemma_pow2_pos(k as nat); }
    acc
}

proof fn lemma_pow2_u64_bound(k: u32)
    requires k < 62,
    ensures spec_pow2(k as nat) <= 0x2000_0000_0000_0000nat,
    decreases k,
{
    if k == 0 {
        assert(spec_pow2(0) == 1nat);
    } else {
        lemma_pow2_u64_bound((k - 1) as u32);
        if k < 61 {
            //Wait: k == 61 has 2^61 == 0x2000_0000_0000_0000, while k == 60 has 2^60 <= 0x1000_0000_0000_0000!
        }
        lemma_pow2_small_values();
        lemma_pow2_add(53, 8);
        assert(spec_pow2(61) == 0x2000_0000_0000_0000nat) by {
            reveal_with_fuel(spec_pow2, 9);
        };
        lemma_pow2_monotone(k as nat, 61nat);
    }
}

pub proof fn lemma_pow2_small_values()
    ensures
        spec_pow2(7) == 128nat,
        spec_pow2(8) == 256nat,
        spec_pow2(15) == 32768nat,
        spec_pow2(16) == 65536nat,
        spec_pow2(31) == 2147483648nat,
        spec_pow2(32) == 4294967296nat,
        spec_pow2(52) == 0x0010_0000_0000_0000nat,
        spec_pow2(53) == 0x0020_0000_0000_0000nat,
{
    reveal_with_fuel(spec_pow2, 17);
    lemma_pow2_add(16, 15);
    lemma_pow2_add(16, 16);
    lemma_pow2_add(32, 16);
    reveal_with_fuel(spec_pow2, 6);
    lemma_pow2_add(48, 4);
    lemma_pow2_add(48, 5);
}

/// Exact representation of `truncate(ℝ(x))` for ANY finite IEEE-754 binary64 number
/// (up to ±1.7976931348623157e308): `(-1)^neg * sig * 2^shift2`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct ExactInt {
    pub neg: bool,
    pub sig: u64,
    pub shift2: u32,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum MathIntOrInf {
    PosInf,
    NegInf,
    Finite(ExactInt),
}

pub open spec fn spec_exact_int_val(x: ExactInt) -> int {
    let mag: int = (x.sig as int) * (spec_pow2(x.shift2 as nat) as int);
    if x.sig == 0 || !x.neg {
        mag
    } else {
        -mag
    }
}

pub open spec fn spec_exact_int_zero() -> ExactInt {
    ExactInt { neg: false, sig: 0, shift2: 0 }
}

pub fn exact_int_zero() -> (r: ExactInt)
    ensures r == spec_exact_int_zero(), spec_exact_int_val(r) == 0,
{
    ExactInt { neg: false, sig: 0, shift2: 0 }
}

/// Right-shift `v` by `k` (`0 <= k <= 53`) using division by `spec_pow2(k)`.
pub open spec fn spec_shr_u64(v: u64, k: nat) -> u64 {
    if k >= 64 {
        0u64
    } else {
        ((v as nat) / spec_pow2(k)) as u64
    }
}

pub fn shr_u64(v: u64, k: u32) -> (r: u64)
    requires k <= 62,
    ensures r == spec_shr_u64(v, k as nat),
{
    let p = pow2_u64(k);
    v / p
}

/// Truncate the exact mathematical real value `ℝ(n)` of a finite IEEE-754 binary64 number toward 0.
pub open spec fn spec_truncate_finite_number(n: JsNumber) -> ExactInt {
    let e = spec_raw_exp(n);
    if e < 1023u64 {
        spec_exact_int_zero()
    } else {
        let sig: u64 = (0x0010_0000_0000_0000u64 + spec_raw_mant(n)) as u64;
        let neg = spec_sign_bit(n) == 1u64;
        if e <= 1075u64 {
            let m = spec_shr_u64(sig, (1075u64 - e) as nat);
            if m == 0u64 {
                spec_exact_int_zero()
            } else {
                ExactInt { neg, sig: m, shift2: 0 }
            }
        } else {
            ExactInt { neg, sig, shift2: (e - 1075u64) as u32 }
        }
    }
}

pub fn truncate_finite_number(n: JsNumber) -> (r: ExactInt)
    requires spec_is_finite_num(n),
    ensures r == spec_truncate_finite_number(n),
{
    let e = raw_exp(n);
    if e < 1023u64 {
        exact_int_zero()
    } else {
        let mant = raw_mant(n);
        let sig: u64 = 0x0010_0000_0000_0000u64 + mant;
        let neg = sign_bit(n) == 1u64;
        if e <= 1075u64 {
            let frac = (1075u64 - e) as u32;
            let m = shr_u64(sig, frac);
            if m == 0u64 {
                exact_int_zero()
            } else {
                ExactInt { neg, sig: m, shift2: 0 }
            }
        } else {
            ExactInt { neg, sig, shift2: (e - 1075u64) as u32 }
        }
    }
}

/// Exact Euclidean modulo `spec_exact_int_val(x) % 2^bit_width` for `1 <= bit_width <= 32`.
pub open spec fn spec_exact_int_modulo_pow2(x: ExactInt, bit_width: nat) -> int {
    spec_exact_int_val(x) % (spec_pow2(bit_width) as int)
}

proof fn lemma_mul_pow2_mod(sig: nat, shift2: nat, bw: nat)
    requires 1 <= bw <= 32,
    ensures
        shift2 >= bw ==> ((sig * spec_pow2(shift2)) % spec_pow2(bw) == 0),
        shift2 < bw ==> (
            (sig * spec_pow2(shift2)) % spec_pow2(bw)
                == (((sig % spec_pow2(bw)) * spec_pow2(shift2)) % spec_pow2(bw))
        ),
{
    let m = spec_pow2(bw);
    lemma_pow2_pos(bw);
    if shift2 >= bw {
        let diff = (shift2 - bw) as nat;
        lemma_pow2_add(diff, bw);
        assert(diff + bw == shift2);
        let pd = spec_pow2(diff);
        let q = sig * pd;
        assert(sig * spec_pow2(shift2) == sig * (pd * m));
        assert(sig * (pd * m) == (sig * pd) * m) by (nonlinear_arith);
        vstd::arithmetic::div_mod::lemma_mod_multiples_basic(q as int, m as int);
    } else {
        vstd::arithmetic::div_mod::lemma_mul_mod_noop_left(
            sig as int,
            spec_pow2(shift2) as int,
            m as int,
        );
    }
}

proof fn lemma_neg_euclidean_mod(mag: int, m: int)
    requires mag >= 0, m > 0,
    ensures
        (-mag) % m == if (mag % m) == 0 { 0int } else { m - (mag % m) },
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(mag, m);
    let q = mag / m;
    let r = mag % m;
    assert(mag == m * q + r);
    if r == 0 {
        assert(-mag == (-q) * m) by (nonlinear_arith)
            requires mag == m * q;
        vstd::arithmetic::div_mod::lemma_mod_multiples_basic(-q, m);
    } else {
        assert(0 < r < m);
        assert(0 < m - r < m);
        assert(-mag == (-(q + 1)) * m + (m - r)) by (nonlinear_arith)
            requires mag == m * q + r;
        vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(-(q + 1), m - r, m);
        vstd::arithmetic::div_mod::lemma_small_mod((m - r) as nat, m as nat);
    }
}

pub fn exact_int_modulo_pow2(x: ExactInt, bit_width: u32) -> (r: i64)
    requires 1 <= bit_width && bit_width <= 32,
    ensures
        r as int == spec_exact_int_modulo_pow2(x, bit_width as nat),
        0 <= r && (r as int) < (spec_pow2(bit_width as nat) as int),
{
    let m_u64 = pow2_u64(bit_width);
    proof {
        lemma_pow2_small_values();
        lemma_pow2_monotone(bit_width as nat, 32nat);
    }
    if x.sig == 0 || x.shift2 >= bit_width {
        proof {
            if x.sig == 0 {
                assert(spec_exact_int_val(x) == 0);
                vstd::arithmetic::div_mod::lemma_small_mod(0nat, m_u64 as nat);
            } else {
                lemma_mul_pow2_mod(x.sig as nat, x.shift2 as nat, bit_width as nat);
                lemma_pow2_pos(x.shift2 as nat);
                let ps: int = spec_pow2(x.shift2 as nat) as int;
                let xs: int = x.sig as int;
                let mag = xs * ps;
                assert(mag >= 0) by (nonlinear_arith)
                    requires xs >= 0, ps >= 1, mag == xs * ps;
                if x.neg {
                    lemma_neg_euclidean_mod(mag, m_u64 as int);
                }
            }
        }
        0i64
    } else {
        let p_shift = pow2_u64(x.shift2);
        proof {
            lemma_pow2_monotone(x.shift2 as nat, 31nat);
            lemma_pow2_small_values();
        }
        let rem_sig: u64 = x.sig % m_u64;
        // rem_sig < 2^32 and p_shift <= 2^31, so rem_sig * p_shift < 2^63 fits in u64!
        proof {
            assert((rem_sig as nat) < (m_u64 as nat));
            let rs_nat = rem_sig as nat;
            let ps_nat = p_shift as nat;
            assert(rs_nat * ps_nat < 4294967296nat * 2147483648nat) by (nonlinear_arith)
                requires rs_nat < 4294967296nat, ps_nat <= 2147483648nat;
        }
        let low: u64 = (rem_sig * p_shift) % m_u64;
        proof {
            lemma_mul_pow2_mod(x.sig as nat, x.shift2 as nat, bit_width as nat);
            lemma_pow2_pos(x.shift2 as nat);
            let ps: int = spec_pow2(x.shift2 as nat) as int;
            let xs: int = x.sig as int;
            let mag = xs * ps;
            assert(mag >= 0) by (nonlinear_arith)
                requires xs >= 0, ps >= 1, mag == xs * ps;
            assert(mag % (m_u64 as int) == low as int);
            if x.neg {
                lemma_neg_euclidean_mod(mag, m_u64 as int);
            }
        }
        if !x.neg || low == 0 {
            low as i64
        } else {
            (m_u64 - low) as i64
        }
    }
}

pub proof fn lemma_pow2_monotone(a: nat, b: nat)
    requires a <= b,
    ensures spec_pow2(a) <= spec_pow2(b),
    decreases b - a,
{
    if a < b {
        lemma_pow2_monotone(a, (b - 1) as nat);
        lemma_pow2_pos((b - 1) as nat);
    }
}

pub proof fn lemma_pow2_bitwidth_bounds(bw: u32)
    requires 1 <= bw && bw <= 32,
    ensures
        1 <= spec_pow2((bw - 1) as nat),
        spec_pow2(bw as nat) == 2nat * spec_pow2((bw - 1) as nat),
        spec_pow2((bw - 1) as nat) <= 2147483648nat,
        spec_pow2(bw as nat) <= 4294967296nat,
{
    lemma_pow2_small_values();
    lemma_pow2_pos((bw - 1) as nat);
    lemma_pow2_monotone((bw - 1) as nat, 31nat);
    lemma_pow2_monotone(bw as nat, 32nat);
}

/// Highest bit index `b` (`0 <= b <= 53`) such that `2^b <= mag < 2^(b+1)` for `1 <= mag <= 2^53`.
pub open spec fn spec_msb_index_from(mag: u64, b: nat) -> nat
    decreases b,
{
    if b == 0 {
        0nat
    } else if (mag as nat) >= spec_pow2(b) {
        b
    } else {
        spec_msb_index_from(mag, (b - 1) as nat)
    }
}

proof fn lemma_msb_index_bounds(mag: u64, b: nat)
    requires 1 <= mag as nat && (mag as nat) < spec_pow2(b + 1),
    ensures
        spec_msb_index_from(mag, b) <= b,
        spec_pow2(spec_msb_index_from(mag, b)) <= mag as nat,
        (mag as nat) < spec_pow2(spec_msb_index_from(mag, b) + 1),
    decreases b,
{
    if b == 0 {
        assert(spec_pow2(0) == 1nat);
        assert(spec_pow2(1) == 2nat);
    } else if (mag as nat) >= spec_pow2(b) {
    } else {
        assert(b == ((b - 1) as nat) + 1);
        lemma_msb_index_bounds(mag, (b - 1) as nat);
    }
}

fn msb_index_53(mag: u64) -> (r: u32)
    requires 1 <= mag && mag <= 0x0020_0000_0000_0000u64,
    ensures
        r as nat == spec_msb_index_from(mag, 53),
        r <= 53,
        spec_pow2(r as nat) <= mag as nat,
        (mag as nat) < spec_pow2((r + 1) as nat),
{
    proof {
        lemma_pow2_small_values();
        assert(spec_pow2(54) == 2nat * spec_pow2(53));
    }
    let mut b: u32 = 53;
    while b > 0
        invariant
            0 <= b <= 53,
            1 <= mag <= 0x0020_0000_0000_0000u64,
            (mag as nat) < spec_pow2((b + 1) as nat),
            spec_msb_index_from(mag, 53) == spec_msb_index_from(mag, b as nat),
        decreases b,
    {
        let p = pow2_u64(b);
        if mag >= p {
            proof { lemma_msb_index_bounds(mag, b as nat); }
            return b;
        }
        b = b - 1;
    }
    proof { lemma_msb_index_bounds(mag, 0); }
    0
}

/// ECMA-262 `𝔽(x)` conversion from a mathematical integer in `[-2^53, 2^53]` to exact IEEE-754
/// binary64 `JsNumber` (`𝔽(0) = +0_𝔽`).
pub open spec fn spec_number_from_int(k: int) -> JsNumber {
    if k == 0 {
        spec_pos_zero()
    } else {
        let neg = k < 0;
        let mag_nat: nat = if k < 0 { (-k) as nat } else { k as nat };
        if mag_nat > 0x0020_0000_0000_0000nat {
            // Outside exact safe integer range (never reached by ToFixedSizeInteger <= 32 or ToLength)
            if neg { spec_neg_inf() } else { spec_pos_inf() }
        } else {
            let mag = mag_nat as u64;
            let msb = spec_msb_index_from(mag, 53);
            let exp: u64 = (1023nat + msb) as u64;
            let mant: u64 = if msb <= 52 {
                let shifted = (mag as nat) * spec_pow2((52 - msb) as nat);
                (shifted - 0x0010_0000_0000_0000nat) as u64
            } else {
                0u64
            };
            let sign_part: u64 = if neg { 0x8000_0000_0000_0000u64 } else { 0u64 };
            JsNumber((sign_part + exp * 0x0010_0000_0000_0000u64 + mant) as u64)
        }
    }
}

pub fn number_from_i64(k: i64) -> (r: JsNumber)
    requires -0x0020_0000_0000_0000i64 <= k <= 0x0020_0000_0000_0000i64,
    ensures r == spec_number_from_int(k as int),
{
    if k == 0 {
        js_pos_zero()
    } else {
        let neg = k < 0;
        let mag: u64 = if k < 0 { (-k) as u64 } else { k as u64 };
        let msb = msb_index_53(mag);
        let exp: u64 = 1023u64 + (msb as u64);
        let mant: u64 = if msb <= 52 {
            let p = pow2_u64(52 - msb);
            proof {
                lemma_pow2_small_values();
                lemma_pow2_add((msb + 1) as nat, (52 - msb) as nat);
                lemma_pow2_add(msb as nat, (52 - msb) as nat);
                assert(((msb + 1) as nat) + ((52 - msb) as nat) == 53nat);
                assert((msb as nat) + ((52 - msb) as nat) == 52nat);
                let mn = mag as nat;
                let pn = p as nat;
                let pm1 = spec_pow2((msb + 1) as nat);
                let pm0 = spec_pow2(msb as nat);
                let p53 = spec_pow2(53);
                let p52 = spec_pow2(52);
                assert(mn * pn < p53) by (nonlinear_arith)
                    requires mn < pm1, pn >= 1, pm1 * pn == p53;
                assert(mn * pn >= p52) by (nonlinear_arith)
                    requires mn >= pm0, pm0 * pn == p52;
            }
            let shifted: u64 = mag * p;
            shifted - 0x0010_0000_0000_0000u64
        } else {
            0u64
        };
        let sign_part: u64 = if neg { 0x8000_0000_0000_0000u64 } else { 0u64 };
        JsNumber(sign_part + exp * 0x0010_0000_0000_0000u64 + mant)
    }
}

/// Key roundtrip theorem: for any integer `k` in `[-2^53, 2^53]`, `𝔽(k)` is finite,
/// non-NaN, never `-0_𝔽`, and `truncate(ℝ(𝔽(k)))` has exact mathematical value `k`!
pub proof fn lemma_number_from_int_roundtrip(k: int)
    requires -0x0020_0000_0000_0000int <= k <= 0x0020_0000_0000_0000int,
    ensures
        spec_is_finite_num(spec_number_from_int(k)),
        !spec_is_nan(spec_number_from_int(k)),
        !spec_is_neg_zero(spec_number_from_int(k)),
        k == 0 ==> spec_is_pos_zero(spec_number_from_int(k)),
        k != 0 ==> (!spec_is_pos_zero(spec_number_from_int(k))),
        spec_exact_int_val(spec_truncate_finite_number(spec_number_from_int(k))) == k,
{
    lemma_pow2_small_values();
    if k == 0 {
        let n = spec_number_from_int(0);
        assert(n == spec_pos_zero());
        assert(spec_raw_exp(n) == 0u64);
        assert(spec_truncate_finite_number(n) == spec_exact_int_zero());
    } else {
        let neg = k < 0;
        let mag_nat: nat = if k < 0 { (-k) as nat } else { k as nat };
        let mag = mag_nat as u64;
        assert(spec_pow2(54) == 2nat * spec_pow2(53));
        lemma_msb_index_bounds(mag, 53);
        let msb = spec_msb_index_from(mag, 53);
        let exp: u64 = (1023nat + msb) as u64;
        let mant: u64 = if msb <= 52 {
            lemma_pow2_add((msb + 1) as nat, (52 - msb) as nat);
            lemma_pow2_add(msb as nat, (52 - msb) as nat);
            assert(((msb + 1) as nat) + ((52 - msb) as nat) == 53nat);
            assert((msb as nat) + ((52 - msb) as nat) == 52nat);
            let p = spec_pow2((52 - msb) as nat);
            lemma_pow2_pos((52 - msb) as nat);
            let pm1 = spec_pow2(msb + 1);
            let pm0 = spec_pow2(msb);
            let p53 = spec_pow2(53);
            let p52 = spec_pow2(52);
            assert(mag_nat * p < p53) by (nonlinear_arith)
                requires mag_nat < pm1, p >= 1, pm1 * p == p53;
            assert(mag_nat * p >= p52) by (nonlinear_arith)
                requires mag_nat >= pm0, pm0 * p == p52;
            (mag_nat * p - 0x0010_0000_0000_0000nat) as u64
        } else {
            assert(msb == 53);
            assert(mag_nat == 0x0020_0000_0000_0000nat);
            0u64
        };
        assert(mant < 0x0010_0000_0000_0000u64);
        assert(1023u64 <= exp <= 1076u64);
        let sign_val: u64 = if neg { 1u64 } else { 0u64 };
        let sign_part: u64 = if neg { 0x8000_0000_0000_0000u64 } else { 0u64 };
        let n = spec_number_from_int(k);
        assert(n.0 == sign_part + exp * 0x0010_0000_0000_0000u64 + mant);

        // Decompose n.0 by quotient & remainder mod 2^52 and 2^63:
        let q52: u64 = (sign_val * 0x800u64 + exp) as u64;
        assert(n.0 as int == (q52 as int) * 0x0010_0000_0000_0000int + (mant as int));
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
            n.0 as int,
            0x0010_0000_0000_0000int,
            q52 as int,
            mant as int,
        );
        assert(spec_raw_mant(n) == mant);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
            q52 as int,
            0x800int,
            sign_val as int,
            exp as int,
        );
        assert(spec_raw_exp(n) == exp);

        let rem63 = (exp * 0x0010_0000_0000_0000u64 + mant) as int;
        assert(0 <= rem63 < 0x8000_0000_0000_0000int);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
            n.0 as int,
            0x8000_0000_0000_0000int,
            sign_val as int,
            rem63,
        );
        assert(spec_sign_bit(n) == sign_val);

        let sig: u64 = (0x0010_0000_0000_0000u64 + mant) as u64;
        if msb <= 52 {
            let p = spec_pow2((52 - msb) as nat);
            lemma_pow2_pos((52 - msb) as nat);
            assert(sig as nat == mag_nat * p);
            assert((1075u64 - exp) as nat == (52 - msb) as nat);
            vstd::arithmetic::div_mod::lemma_div_by_multiple(mag_nat as int, p as int);
            assert(spec_shr_u64(sig, (52 - msb) as nat) == mag);
            assert(mag > 0u64);
            let tr = spec_truncate_finite_number(n);
            assert(tr == ExactInt { neg, sig: mag, shift2: 0 });
            assert(spec_pow2(0) == 1nat);
            assert((mag as int) * 1int == mag as int);
            assert(spec_exact_int_val(tr) == k);
        } else {
            assert(exp == 1076u64);
            assert(sig == 0x0010_0000_0000_0000u64);
            let tr = spec_truncate_finite_number(n);
            assert(tr == ExactInt { neg, sig: 0x0010_0000_0000_0000u64, shift2: 1 });
            assert(spec_pow2(1) == 2nat);
            assert(0x0010_0000_0000_0000int * 2int == 0x0020_0000_0000_0000int);
            assert(spec_exact_int_val(tr) == k);
        }
    }
}

// ===============================================================================================
// 4. 32-Bit Two's Complement Bitwise & Shift Helpers for §6.1.6.1
// ===============================================================================================

/// Extract the exact mathematical integer in `[-2^31, 2^32 - 1]` represented by an integral
/// `JsNumber` returned by `ToInt32` or `ToUint32`.
pub open spec fn spec_integral_number_to_i64(n: JsNumber) -> int {
    spec_exact_int_val(spec_truncate_finite_number(n))
}

pub fn integral_number_to_i64(n: JsNumber) -> (r: i64)
    requires
        spec_is_finite_num(n),
        -4294967296int <= spec_integral_number_to_i64(n) <= 4294967296int,
    ensures
        r as int == spec_integral_number_to_i64(n),
{
    let ex = truncate_finite_number(n);
    if ex.sig == 0 {
        0i64
    } else {
        proof {
            lemma_pow2_pos(ex.shift2 as nat);
            lemma_pow2_small_values();
            if ex.shift2 > 32 {
                lemma_pow2_monotone(33nat, ex.shift2 as nat);
                assert(spec_pow2(33) == 8589934592nat);
                assert((ex.sig as nat) * spec_pow2(ex.shift2 as nat) >= 8589934592nat) by (nonlinear_arith)
                    requires ex.sig >= 1, spec_pow2(ex.shift2 as nat) >= 8589934592nat;
                assert(false);
            }
        }
        let p = pow2_u64(ex.shift2);
        proof {
            assert((ex.sig as int) * (p as int) <= 4294967296int) by {
                if !ex.neg {
                    assert(spec_exact_int_val(ex) == (ex.sig as int) * (p as int));
                } else {
                    assert(spec_exact_int_val(ex) == -((ex.sig as int) * (p as int)));
                }
            };
        }
        let mag: i64 = (ex.sig * p) as i64;
        if ex.neg { -mag } else { mag }
    }
}

pub open spec fn spec_i32_to_u32_bits(v: int) -> u32 {
    if v >= 0 {
        (v % 4294967296int) as u32
    } else {
        ((v % 4294967296int)) as u32
    }
}

pub open spec fn spec_u32_bits_to_i32_int(b: u32) -> int {
    if b >= 0x8000_0000u32 {
        (b as int) - 4294967296int
    } else {
        b as int
    }
}

pub fn i64_to_u32_bits(v: i64) -> (r: u32)
    requires -2147483648i64 <= v <= 2147483647i64,
    ensures
        r == spec_i32_to_u32_bits(v as int),
        spec_u32_bits_to_i32_int(r) == v as int,
{
    if v >= 0 {
        proof {
            vstd::arithmetic::div_mod::lemma_small_mod(v as nat, 4294967296nat);
        }
        v as u32
    } else {
        let u: i64 = v + 4294967296i64;
        proof {
            vstd::arithmetic::div_mod::lemma_mod_add_multiples_vanish(v as int, 4294967296int);
            vstd::arithmetic::div_mod::lemma_small_mod(u as nat, 4294967296nat);
        }
        u as u32
    }
}

pub fn u32_bits_to_i64(b: u32) -> (r: i64)
    ensures
        r as int == spec_u32_bits_to_i32_int(b),
        -2147483648i64 <= r <= 2147483647i64,
{
    if b >= 0x8000_0000u32 {
        (b as i64) - 4294967296i64
    } else {
        b as i64
    }
}

pub open spec fn spec_bitnot_u32(b: u32) -> u32 { !b }
pub open spec fn spec_bitand_u32(a: u32, b: u32) -> u32 { a & b }
pub open spec fn spec_bitxor_u32(a: u32, b: u32) -> u32 { a ^ b }
pub open spec fn spec_bitor_u32(a: u32, b: u32) -> u32 { a | b }
pub open spec fn spec_shl_u32(a: u32, cnt: u32) -> u32 { a << cnt }
pub open spec fn spec_shr_u32(a: u32, cnt: u32) -> u32 { a >> cnt }
pub open spec fn spec_ashr_u32(a: u32, cnt: u32) -> u32 { ((a as i32) >> cnt) as u32 }

pub fn bitnot_i32_val(v: i64) -> (r: i64)
    requires -2147483648i64 <= v <= 2147483647i64,
    ensures
        r as int == spec_u32_bits_to_i32_int(spec_bitnot_u32(spec_i32_to_u32_bits(v as int))),
        -2147483648i64 <= r <= 2147483647i64,
{
    let b = i64_to_u32_bits(v);
    u32_bits_to_i64(!b)
}

pub fn shl_i32_val(lhs: i64, shift: i64) -> (r: i64)
    requires -2147483648i64 <= lhs <= 2147483647i64, 0 <= shift < 32,
    ensures
        r as int == spec_u32_bits_to_i32_int(spec_shl_u32(spec_i32_to_u32_bits(lhs as int), shift as u32)),
        -2147483648i64 <= r <= 2147483647i64,
{
    let b = i64_to_u32_bits(lhs);
    let cnt = shift as u32;
    u32_bits_to_i64(b << cnt)
}

pub fn ashr_i32_val(lhs: i64, shift: i64) -> (r: i64)
    requires -2147483648i64 <= lhs <= 2147483647i64, 0 <= shift < 32,
    ensures
        r as int == spec_u32_bits_to_i32_int(spec_ashr_u32(spec_i32_to_u32_bits(lhs as int), shift as u32)),
        -2147483648i64 <= r <= 2147483647i64,
{
    let b = i64_to_u32_bits(lhs);
    let cnt = shift as u32;
    let shifted: u32 = ((b as i32) >> cnt) as u32;
    u32_bits_to_i64(shifted)
}

pub fn lshr_u32_val(lhs: i64, shift: i64) -> (r: i64)
    requires 0 <= lhs < 4294967296i64, 0 <= shift < 32,
    ensures
        r as int == (spec_shr_u32(lhs as u32, shift as u32) as int),
        0 <= r < 4294967296i64,
{
    let b = lhs as u32;
    let cnt = shift as u32;
    (b >> cnt) as i64
}

pub fn bitand_u32_exec(a: u32, b: u32) -> (r: u32) ensures r == spec_bitand_u32(a, b) { a & b }
pub fn bitxor_u32_exec(a: u32, b: u32) -> (r: u32) ensures r == spec_bitxor_u32(a, b) { a ^ b }
pub fn bitor_u32_exec(a: u32, b: u32) -> (r: u32) ensures r == spec_bitor_u32(a, b) { a | b }

// ===============================================================================================
// 5. Arbitrary-Precision `JsBigInt` & Exact `ℝ(BigInt) == ℝ(Number)`
// ===============================================================================================

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct JsBigInt {
    pub neg: bool,
    pub limbs: Vec<u32>,
}

pub struct SpecBigInt {
    pub neg: bool,
    pub limbs: Seq<u32>,
}

impl View for JsBigInt {
    type V = SpecBigInt;
    open spec fn view(&self) -> SpecBigInt {
        SpecBigInt { neg: self.neg, limbs: self.limbs@ }
    }
}

pub open spec fn spec_limbs_val(limbs: Seq<u32>) -> nat
    decreases limbs.len(),
{
    if limbs.len() == 0 {
        0nat
    } else {
        (limbs[0] as nat) + 0x1_0000_0000nat * spec_limbs_val(limbs.subrange(1, limbs.len() as int))
    }
}

pub open spec fn spec_bigint_val(b: SpecBigInt) -> int {
    let m = spec_limbs_val(b.limbs);
    if m == 0 {
        0int
    } else if b.neg {
        -(m as int)
    } else {
        m as int
    }
}

pub fn bigint_is_zero(b: &JsBigInt) -> (r: bool)
    ensures r == (spec_bigint_val(b@) == 0),
{
    let n = b.limbs.len();
    let mut i: usize = 0;
    proof {
        assert(b.limbs@.subrange(0, n as int) =~= b.limbs@);
    }
    while i < n
        invariant
            0 <= i <= n,
            n == b.limbs@.len(),
            spec_limbs_val(b.limbs@) == 0 <==> spec_limbs_val(b.limbs@.subrange(i as int, n as int)) == 0,
        decreases n - i,
    {
        let ghost sub = b.limbs@.subrange(i as int, n as int);
        if b.limbs[i] != 0 {
            proof {
                assert(sub[0] == b.limbs@[i as int]);
                assert(spec_limbs_val(sub) >= 1);
            }
            return false;
        }
        proof {
            assert(sub.subrange(1, sub.len() as int) =~= b.limbs@.subrange((i + 1) as int, n as int));
            assert(spec_limbs_val(sub) == 0x1_0000_0000nat * spec_limbs_val(b.limbs@.subrange((i + 1) as int, n as int)));
        }
        i = i + 1;
    }
    proof {
        assert(b.limbs@.subrange(n as int, n as int) =~= Seq::<u32>::empty());
    }
    true
}

/// Effective canonical limb count (stripping any trailing zero limbs).
pub open spec fn spec_canonical_len(limbs: Seq<u32>) -> nat
    decreases limbs.len(),
{
    if limbs.len() == 0 {
        0nat
    } else if limbs.last() != 0u32 {
        limbs.len()
    } else {
        spec_canonical_len(limbs.drop_last())
    }
}

proof fn lemma_limbs_drop_trailing_zero(limbs: Seq<u32>)
    requires limbs.len() > 0, limbs.last() == 0u32,
    ensures spec_limbs_val(limbs) == spec_limbs_val(limbs.drop_last()),
    decreases limbs.len(),
{
    if limbs.len() == 1 {
        assert(limbs.subrange(1, 1) =~= Seq::<u32>::empty());
        assert(limbs.drop_last() =~= Seq::<u32>::empty());
    } else {
        let tail = limbs.subrange(1, limbs.len() as int);
        assert(tail.last() == limbs.last());
        assert(tail.drop_last() =~= limbs.drop_last().subrange(1, limbs.drop_last().len() as int));
        lemma_limbs_drop_trailing_zero(tail);
    }
}

proof fn lemma_limbs_val_canonical(limbs: Seq<u32>)
    ensures
        spec_canonical_len(limbs) <= limbs.len(),
        spec_limbs_val(limbs) == spec_limbs_val(limbs.subrange(0, spec_canonical_len(limbs) as int)),
        spec_canonical_len(limbs) > 0 ==> limbs[spec_canonical_len(limbs) as int - 1] != 0u32,
        (spec_canonical_len(limbs) == 0) <==> (spec_limbs_val(limbs) == 0),
    decreases limbs.len(),
{
    if limbs.len() == 0 {
        assert(limbs.subrange(0, 0) =~= Seq::<u32>::empty());
    } else if limbs.last() != 0u32 {
        assert(limbs.subrange(0, limbs.len() as int) =~= limbs);
        lemma_nonzero_last_implies_pos(limbs);
    } else {
        lemma_limbs_drop_trailing_zero(limbs);
        lemma_limbs_val_canonical(limbs.drop_last());
        let cl = spec_canonical_len(limbs.drop_last());
        assert(limbs.drop_last().subrange(0, cl as int) =~= limbs.subrange(0, cl as int));
    }
}

proof fn lemma_nonzero_last_implies_pos(limbs: Seq<u32>)
    requires limbs.len() > 0, limbs.last() != 0u32,
    ensures spec_limbs_val(limbs) > 0,
    decreases limbs.len(),
{
    if limbs.len() == 1 {
        assert(limbs[0] == limbs.last());
    } else {
        let tail = limbs.subrange(1, limbs.len() as int);
        assert(tail.last() == limbs.last());
        lemma_nonzero_last_implies_pos(tail);
    }
}

proof fn lemma_canonical_limbs_injective(a: Seq<u32>, b: Seq<u32>)
    requires
        a.len() == 0 || a.last() != 0u32,
        b.len() == 0 || b.last() != 0u32,
        spec_limbs_val(a) == spec_limbs_val(b),
    ensures
        a =~= b,
    decreases a.len() + b.len(),
{
    if a.len() == 0 {
        if b.len() > 0 {
            lemma_nonzero_last_implies_pos(b);
            assert(false);
        }
    } else if b.len() == 0 {
        lemma_nonzero_last_implies_pos(a);
        assert(false);
    } else {
        let ta = a.subrange(1, a.len() as int);
        let tb = b.subrange(1, b.len() as int);
        let va = spec_limbs_val(ta);
        let vb = spec_limbs_val(tb);
        assert((a[0] as int) + 0x1_0000_0000int * (va as int) == (b[0] as int) + 0x1_0000_0000int * (vb as int));
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
            spec_limbs_val(a) as int,
            0x1_0000_0000int,
            va as int,
            a[0] as int,
        );
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
            spec_limbs_val(b) as int,
            0x1_0000_0000int,
            vb as int,
            b[0] as int,
        );
        assert(a[0] == b[0]);
        assert(va == vb);
        if ta.len() > 0 && ta.last() == 0u32 {
            assert(ta.last() == a.last());
        }
        if tb.len() > 0 && tb.last() == 0u32 {
            assert(tb.last() == b.last());
        }
        lemma_canonical_limbs_injective(ta, tb);
        assert(a =~= seq![a[0]] + ta);
        assert(b =~= seq![b[0]] + tb);
    }
}

fn canonical_len_exec(limbs: &Vec<u32>) -> (r: usize)
    ensures r as nat == spec_canonical_len(limbs@), r <= limbs.len(),
{
    let mut k = limbs.len();
    proof { assert(limbs@.subrange(0, k as int) =~= limbs@); }
    while k > 0
        invariant
            0 <= k <= limbs.len(),
            spec_canonical_len(limbs@) == spec_canonical_len(limbs@.subrange(0, k as int)),
        decreases k,
    {
        let ghost sub = limbs@.subrange(0, k as int);
        if limbs[k - 1] != 0u32 {
            proof { assert(sub.last() == limbs@[k - 1]); }
            return k;
        }
        proof {
            assert(sub.last() == 0u32);
            assert(sub.drop_last() =~= limbs@.subrange(0, (k - 1) as int));
        }
        k = k - 1;
    }
    proof { assert(limbs@.subrange(0, 0) =~= Seq::<u32>::empty()); }
    0
}

pub fn bigint_equal(x: &JsBigInt, y: &JsBigInt) -> (r: bool)
    ensures r == (spec_bigint_val(x@) == spec_bigint_val(y@)),
{
    let lx = canonical_len_exec(&x.limbs);
    let ly = canonical_len_exec(&y.limbs);
    proof {
        lemma_limbs_val_canonical(x.limbs@);
        lemma_limbs_val_canonical(y.limbs@);
    }
    if lx == 0 && ly == 0 {
        return true;
    }
    if lx != ly || x.neg != y.neg {
        proof {
            let cx = x.limbs@.subrange(0, lx as int);
            let cy = y.limbs@.subrange(0, ly as int);
            if lx == 0 || ly == 0 {
                // One is 0 and the other is non-zero
            } else if x.neg != y.neg {
                // One is strictly positive and the other strictly negative
            } else if spec_limbs_val(cx) == spec_limbs_val(cy) {
                assert(cx.last() == x.limbs@[lx as int - 1]);
                assert(cy.last() == y.limbs@[ly as int - 1]);
                lemma_canonical_limbs_injective(cx, cy);
                assert(cx.len() == cy.len());
            }
        }
        return false;
    }
    let mut i: usize = 0;
    while i < lx
        invariant
            0 <= i <= lx,
            lx == ly,
            lx > 0,
            lx <= x.limbs.len(),
            ly <= y.limbs.len(),
            x.limbs@[lx as int - 1] != 0u32,
            y.limbs@[ly as int - 1] != 0u32,
            spec_limbs_val(x.limbs@) == spec_limbs_val(x.limbs@.subrange(0, lx as int)),
            spec_limbs_val(y.limbs@) == spec_limbs_val(y.limbs@.subrange(0, ly as int)),
            x.neg == y.neg,
            forall|j: int| 0 <= j < i ==> x.limbs@[j] == y.limbs@[j],
        decreases lx - i,
    {
        if x.limbs[i] != y.limbs[i] {
            proof {
                let cx = x.limbs@.subrange(0, lx as int);
                let cy = y.limbs@.subrange(0, ly as int);
                assert(cx.last() == x.limbs@[lx as int - 1]);
                assert(cy.last() == y.limbs@[ly as int - 1]);
                lemma_nonzero_last_implies_pos(cx);
                lemma_nonzero_last_implies_pos(cy);
                if spec_limbs_val(cx) == spec_limbs_val(cy) {
                    lemma_canonical_limbs_injective(cx, cy);
                    assert(cx[i as int] == cy[i as int]);
                    assert(x.limbs@[i as int] == y.limbs@[i as int]);
                }
            }
            return false;
        }
        i = i + 1;
    }
    proof {
        let cx = x.limbs@.subrange(0, lx as int);
        let cy = y.limbs@.subrange(0, ly as int);
        assert(cx =~= cy);
    }
    true
}

/// Does finite IEEE-754 binary64 `n` represent an exact mathematical integer, and if so does
/// `ℝ(n) == spec_bigint_val(b)`?
pub open spec fn spec_finite_number_is_integral(n: JsNumber) -> bool {
    if spec_is_pos_zero(n) || spec_is_neg_zero(n) {
        true
    } else {
        let e = spec_raw_exp(n);
        if e < 1023u64 || e >= 0x7FFu64 {
            false
        } else if e >= 1075u64 {
            true
        } else {
            let sig: nat = (0x0010_0000_0000_0000u64 + spec_raw_mant(n)) as nat;
            (sig % spec_pow2((1075u64 - e) as nat)) == 0
        }
    }
}

pub open spec fn spec_finite_number_real_eq_bigint(n: JsNumber, b: SpecBigInt) -> bool {
    spec_finite_number_is_integral(n)
        && spec_exact_int_val(spec_truncate_finite_number(n)) == spec_bigint_val(b)
}

#[verifier::spinoff_prover]
pub fn finite_number_real_eq_bigint(n: JsNumber, b: &JsBigInt) -> (r: bool)
    requires spec_is_finite_num(n),
    ensures r == spec_finite_number_real_eq_bigint(n, b@),
{
    if num_is_pos_zero(n) || num_is_neg_zero(n) {
        proof {
            if spec_is_pos_zero(n) {
                assert(spec_raw_exp(n) == 0u64);
            } else {
                assert(spec_raw_exp(n) == 0u64);
            }
            assert(spec_truncate_finite_number(n) == spec_exact_int_zero());
        }
        return bigint_is_zero(b);
    }
    let e = raw_exp(n);
    if e < 1023u64 {
        return false;
    }
    let mant = raw_mant(n);
    let sig: u64 = 0x0010_0000_0000_0000u64 + mant;
    if e < 1075u64 {
        let frac = (1075u64 - e) as u32;
        let p = pow2_u64(frac);
        if (sig % p) != 0u64 {
            return false;
        }
    }
    // Now `n` is an exact non-zero integer matching `truncate_finite_number(n)`!
    let ex = truncate_finite_number(n);
    proof {
        if e < 1075u64 {
            let frac = (1075u64 - e) as nat;
            lemma_pow2_monotone(frac, 52nat);
            lemma_pow2_small_values();
            assert(sig as nat >= spec_pow2(52));
            assert(sig as nat >= spec_pow2(frac));
            vstd::arithmetic::div_mod::lemma_div_non_zero(sig as int, spec_pow2(frac) as int);
            assert(ex.sig > 0);
        } else if e == 1075u64 {
            assert(spec_pow2(0) == 1nat);
            assert((sig as nat) / 1nat == sig as nat);
            assert(spec_shr_u64(sig, 0) == sig);
            assert(ex.sig > 0);
        } else {
            assert(ex.sig > 0);
        }
    }
    // Build canonical `JsBigInt` for `ex = (-1)^ex.neg * ex.sig * 2^ex.shift2` and compare via `bigint_equal`!
    let ex_bi = exact_int_to_bigint(ex);
    bigint_equal(&ex_bi, b)
}

proof fn lemma_zero_prefix_limbs(q: nat, tail: Seq<u32>)
    ensures spec_limbs_val(Seq::new(q, |_i: int| 0u32) + tail) == spec_limbs_val(tail) * spec_pow2(32 * q),
    decreases q,
{
    lemma_pow2_small_values();
    if q == 0 {
        assert(Seq::new(0, |_i: int| 0u32) + tail =~= tail);
        assert(32 * 0nat == 0nat);
        assert(spec_pow2(0) == 1nat);
        let vt = spec_limbs_val(tail);
        assert(vt * 1nat == vt) by (nonlinear_arith);
    } else {
        let zq = Seq::new(q, |_i: int| 0u32);
        let zq1 = Seq::new((q - 1) as nat, |_i: int| 0u32);
        assert((zq + tail)[0] == 0u32);
        assert((zq + tail).subrange(1, (zq + tail).len() as int) =~= zq1 + tail);
        lemma_zero_prefix_limbs((q - 1) as nat, tail);
        lemma_pow2_add(32nat, (32 * (q - 1)) as nat);
        assert(32nat + (32 * (q - 1)) as nat == 32 * q);
        let vt = spec_limbs_val(tail);
        let pq1 = spec_pow2((32 * (q - 1)) as nat);
        let p32 = spec_pow2(32);
        assert(p32 == 0x1_0000_0000nat);
        assert(p32 * (vt * pq1) == vt * (p32 * pq1)) by (nonlinear_arith);
    }
}

fn exact_int_to_bigint(ex: ExactInt) -> (out: JsBigInt)
    requires ex.sig > 0,
    ensures spec_bigint_val(out@) == spec_exact_int_val(ex),
{
    let q: u32 = ex.shift2 / 32;
    let r: u32 = ex.shift2 % 32;
    let p_r: u64 = pow2_u64(r);
    let sig128: u128 = ex.sig as u128;
    let pr128: u128 = p_r as u128;
    proof {
        lemma_pow2_monotone(r as nat, 31nat);
        lemma_pow2_small_values();
        assert(sig128 <= 0xFFFF_FFFF_FFFF_FFFFu128);
        assert(pr128 <= 2147483648u128);
        assert(sig128 * pr128 < 0x1_0000_0000_0000_0000_0000_0000u128) by (nonlinear_arith)
            requires sig128 <= 0xFFFF_FFFF_FFFF_FFFFu128, pr128 <= 2147483648u128;
    }
    let prod: u128 = sig128 * pr128;
    let mut limbs: Vec<u32> = Vec::new();
    let mut i: u32 = 0;
    while i < q
        invariant
            0 <= i <= q,
            limbs@ =~= Seq::new(i as nat, |_j: int| 0u32),
        decreases q - i,
    {
        limbs.push(0u32);
        proof {
            assert(limbs@ =~= Seq::new((i + 1) as nat, |_j: int| 0u32));
        }
        i = i + 1;
    }
    let w0: u32 = (prod % 0x1_0000_0000u128) as u32;
    let rest1: u128 = prod / 0x1_0000_0000u128;
    let w1: u32 = (rest1 % 0x1_0000_0000u128) as u32;
    let w2: u32 = (rest1 / 0x1_0000_0000u128) as u32;
    proof {
        // prod = ex.sig * 2^r < 2^64 * 2^31 = 2^95 < 2^96, so rest1 / 2^32 < 2^32!
        assert((ex.sig as nat) <= 0xFFFF_FFFF_FFFF_FFFFnat);
        assert((p_r as nat) <= 2147483648nat);
        assert((prod as nat) == (ex.sig as nat) * (p_r as nat));
        assert((prod as nat) < 0x1_0000_0000nat * 0x1_0000_0000nat * 0x1_0000_0000nat) by (nonlinear_arith)
            requires (prod as nat) == (ex.sig as nat) * (p_r as nat),
                (ex.sig as nat) <= 0xFFFF_FFFF_FFFF_FFFFnat,
                (p_r as nat) <= 2147483648nat;
    }
    let ghost zeros = limbs@;
    let mut tail_vec: Vec<u32> = Vec::new();
    if w2 != 0 {
        tail_vec.push(w0);
        tail_vec.push(w1);
        tail_vec.push(w2);
        limbs.push(w0);
        limbs.push(w1);
        limbs.push(w2);
    } else if w1 != 0 {
        tail_vec.push(w0);
        tail_vec.push(w1);
        limbs.push(w0);
        limbs.push(w1);
    } else {
        tail_vec.push(w0);
        limbs.push(w0);
    }
    proof {
        assert(limbs@ =~= zeros + tail_vec@);
        reveal_with_fuel(spec_limbs_val, 4);
        assert(spec_limbs_val(tail_vec@) == prod as nat);
        lemma_pow2_pos(r as nat);
        assert((prod as nat) >= 1) by (nonlinear_arith)
            requires ex.sig >= 1, (p_r as nat) >= 1, (prod as nat) == (ex.sig as nat) * (p_r as nat);
        lemma_zero_prefix_limbs(q as nat, tail_vec@);
        lemma_pow2_add(r as nat, (32 * (q as nat)) as nat);
        assert(r as nat + 32 * (q as nat) == ex.shift2 as nat);
        assert(spec_limbs_val(limbs@) == (prod as nat) * spec_pow2((32 * (q as nat)) as nat));
        assert((prod as nat) * spec_pow2((32 * (q as nat)) as nat)
            == (ex.sig as nat) * (spec_pow2(r as nat) * spec_pow2((32 * (q as nat)) as nat))) by (nonlinear_arith)
            requires (prod as nat) == (ex.sig as nat) * spec_pow2(r as nat);
        lemma_pow2_pos(ex.shift2 as nat);
        assert(spec_limbs_val(limbs@) == (ex.sig as nat) * spec_pow2(ex.shift2 as nat));
        assert(spec_limbs_val(limbs@) >= 1) by (nonlinear_arith)
            requires ex.sig >= 1, spec_pow2(ex.shift2 as nat) >= 1,
                spec_limbs_val(limbs@) == (ex.sig as nat) * spec_pow2(ex.shift2 as nat);
    }
    JsBigInt { neg: ex.neg, limbs }
}

// ===============================================================================================
// 6. ECMAScript Language Values (`JsValue`, `SpecJsValue`) & Predicates
// ===============================================================================================

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum JsPrim {
    Undefined,
    Null,
    Boolean(bool),
    Number(JsNumber),
    BigInt(JsBigInt),
    Str(Vec<u16>),
    Symbol(u64),
}

pub enum SpecPrim {
    Undefined,
    Null,
    Boolean(bool),
    Number(JsNumber),
    BigInt(SpecBigInt),
    Str(Seq<u16>),
    Symbol(u64),
}

impl View for JsPrim {
    type V = SpecPrim;
    open spec fn view(&self) -> SpecPrim {
        match self {
            JsPrim::Undefined => SpecPrim::Undefined,
            JsPrim::Null => SpecPrim::Null,
            JsPrim::Boolean(b) => SpecPrim::Boolean(*b),
            JsPrim::Number(n) => SpecPrim::Number(*n),
            JsPrim::BigInt(bi) => SpecPrim::BigInt(bi@),
            JsPrim::Str(s) => SpecPrim::Str(s@),
            JsPrim::Symbol(id) => SpecPrim::Symbol(*id),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ObjectCoercion {
    Primitive(JsPrim),
    ThrowTypeError,
}

pub enum SpecObjectCoercion {
    Primitive(SpecPrim),
    ThrowTypeError,
}

impl View for ObjectCoercion {
    type V = SpecObjectCoercion;
    open spec fn view(&self) -> SpecObjectCoercion {
        match self {
            ObjectCoercion::Primitive(p) => SpecObjectCoercion::Primitive(p@),
            ObjectCoercion::ThrowTypeError => SpecObjectCoercion::ThrowTypeError,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct JsObject {
    pub id: u64,
    pub is_htmldda: bool,
    pub prim_default: ObjectCoercion,
    pub prim_number: ObjectCoercion,
}

pub struct SpecObject {
    pub id: u64,
    pub is_htmldda: bool,
    pub prim_default: SpecObjectCoercion,
    pub prim_number: SpecObjectCoercion,
}

impl View for JsObject {
    type V = SpecObject;
    open spec fn view(&self) -> SpecObject {
        SpecObject {
            id: self.id,
            is_htmldda: self.is_htmldda,
            prim_default: self.prim_default@,
            prim_number: self.prim_number@,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum JsValue {
    Undefined,
    Null,
    Boolean(bool),
    Number(JsNumber),
    BigInt(JsBigInt),
    Str(Vec<u16>),
    Symbol(u64),
    Object(JsObject),
}

pub enum SpecJsValue {
    Undefined,
    Null,
    Boolean(bool),
    Number(JsNumber),
    BigInt(SpecBigInt),
    Str(Seq<u16>),
    Symbol(u64),
    Object(SpecObject),
}

impl View for JsValue {
    type V = SpecJsValue;
    open spec fn view(&self) -> SpecJsValue {
        match self {
            JsValue::Undefined => SpecJsValue::Undefined,
            JsValue::Null => SpecJsValue::Null,
            JsValue::Boolean(b) => SpecJsValue::Boolean(*b),
            JsValue::Number(n) => SpecJsValue::Number(*n),
            JsValue::BigInt(bi) => SpecJsValue::BigInt(bi@),
            JsValue::Str(s) => SpecJsValue::Str(s@),
            JsValue::Symbol(id) => SpecJsValue::Symbol(*id),
            JsValue::Object(o) => SpecJsValue::Object(o@),
        }
    }
}

pub open spec fn spec_prim_to_val(p: SpecPrim) -> SpecJsValue {
    match p {
        SpecPrim::Undefined => SpecJsValue::Undefined,
        SpecPrim::Null => SpecJsValue::Null,
        SpecPrim::Boolean(b) => SpecJsValue::Boolean(b),
        SpecPrim::Number(n) => SpecJsValue::Number(n),
        SpecPrim::BigInt(bi) => SpecJsValue::BigInt(bi),
        SpecPrim::Str(s) => SpecJsValue::Str(s),
        SpecPrim::Symbol(id) => SpecJsValue::Symbol(id),
    }
}

fn prim_to_val(p: &JsPrim) -> (r: JsValue)
    ensures r@ == spec_prim_to_val(p@), !spec_is_object(r@),
{
    match p {
        JsPrim::Undefined => JsValue::Undefined,
        JsPrim::Null => JsValue::Null,
        JsPrim::Boolean(b) => JsValue::Boolean(*b),
        JsPrim::Number(n) => JsValue::Number(*n),
        JsPrim::BigInt(bi) => JsValue::BigInt(bi.clone()),
        JsPrim::Str(s) => JsValue::Str(s.clone()),
        JsPrim::Symbol(id) => JsValue::Symbol(*id),
    }
}

// Type predicates on SpecJsValue & JsValue
pub open spec fn spec_is_undefined(v: SpecJsValue) -> bool { v is Undefined }
pub open spec fn spec_is_null(v: SpecJsValue) -> bool { v is Null }
pub open spec fn spec_is_boolean(v: SpecJsValue) -> bool { v is Boolean }
pub open spec fn spec_is_number(v: SpecJsValue) -> bool { v is Number }
pub open spec fn spec_is_bigint(v: SpecJsValue) -> bool { v is BigInt }
pub open spec fn spec_is_string(v: SpecJsValue) -> bool { v is Str }
pub open spec fn spec_is_symbol(v: SpecJsValue) -> bool { v is Symbol }
pub open spec fn spec_is_object(v: SpecJsValue) -> bool { v is Object }

pub open spec fn spec_is_bool_true(v: SpecJsValue) -> bool {
    match v { SpecJsValue::Boolean(b) => b, _ => false }
}
pub open spec fn spec_is_bool_false(v: SpecJsValue) -> bool {
    match v { SpecJsValue::Boolean(b) => !b, _ => false }
}
pub open spec fn spec_unwrap_bool(v: SpecJsValue) -> bool {
    match v { SpecJsValue::Boolean(b) => b, _ => false }
}
pub open spec fn spec_unwrap_number(v: SpecJsValue) -> JsNumber {
    match v { SpecJsValue::Number(n) => n, _ => spec_canon_nan() }
}
pub open spec fn spec_unwrap_bigint(v: SpecJsValue) -> SpecBigInt {
    match v { SpecJsValue::BigInt(b) => b, _ => SpecBigInt { neg: false, limbs: Seq::empty() } }
}

pub open spec fn spec_val_is_nan(v: SpecJsValue) -> bool {
    match v { SpecJsValue::Number(n) => spec_is_nan(n), _ => false }
}
pub open spec fn spec_val_is_pos_zero(v: SpecJsValue) -> bool {
    match v { SpecJsValue::Number(n) => spec_is_pos_zero(n), _ => false }
}
pub open spec fn spec_val_is_neg_zero(v: SpecJsValue) -> bool {
    match v { SpecJsValue::Number(n) => spec_is_neg_zero(n), _ => false }
}
pub open spec fn spec_val_is_pos_inf(v: SpecJsValue) -> bool {
    match v { SpecJsValue::Number(n) => spec_is_pos_inf(n), _ => false }
}
pub open spec fn spec_val_is_neg_inf(v: SpecJsValue) -> bool {
    match v { SpecJsValue::Number(n) => spec_is_neg_inf(n), _ => false }
}
pub open spec fn spec_val_is_finite_number(v: SpecJsValue) -> bool {
    match v { SpecJsValue::Number(n) => spec_is_finite_num(n), _ => false }
}
pub open spec fn spec_val_is_bigint_zero(v: SpecJsValue) -> bool {
    match v { SpecJsValue::BigInt(b) => spec_bigint_val(b) == 0, _ => false }
}
pub open spec fn spec_val_is_empty_string(v: SpecJsValue) -> bool {
    match v { SpecJsValue::Str(s) => s.len() == 0, _ => false }
}
pub open spec fn spec_host_supports_htmldda() -> bool { true }
pub open spec fn spec_has_htmldda_slot(v: SpecJsValue) -> bool {
    match v { SpecJsValue::Object(o) => o.is_htmldda, _ => false }
}

pub fn val_is_undefined(v: &JsValue) -> (r: bool) ensures r == spec_is_undefined(v@) { matches!(v, JsValue::Undefined) }
pub fn val_is_null(v: &JsValue) -> (r: bool) ensures r == spec_is_null(v@) { matches!(v, JsValue::Null) }
pub fn val_is_boolean(v: &JsValue) -> (r: bool) ensures r == spec_is_boolean(v@) { matches!(v, JsValue::Boolean(_)) }
pub fn val_is_number(v: &JsValue) -> (r: bool) ensures r == spec_is_number(v@) { matches!(v, JsValue::Number(_)) }
pub fn val_is_bigint(v: &JsValue) -> (r: bool) ensures r == spec_is_bigint(v@) { matches!(v, JsValue::BigInt(_)) }
pub fn val_is_string(v: &JsValue) -> (r: bool) ensures r == spec_is_string(v@) { matches!(v, JsValue::Str(_)) }
pub fn val_is_symbol(v: &JsValue) -> (r: bool) ensures r == spec_is_symbol(v@) { matches!(v, JsValue::Symbol(_)) }
pub fn val_is_object(v: &JsValue) -> (r: bool) ensures r == spec_is_object(v@) { matches!(v, JsValue::Object(_)) }

pub fn val_is_bool_true(v: &JsValue) -> (r: bool) ensures r == spec_is_bool_true(v@) {
    match v { JsValue::Boolean(b) => *b, _ => false }
}
pub fn val_is_bool_false(v: &JsValue) -> (r: bool) ensures r == spec_is_bool_false(v@) {
    match v { JsValue::Boolean(b) => !(*b), _ => false }
}
pub fn val_unwrap_bool(v: &JsValue) -> (r: bool)
    requires spec_is_boolean(v@),
    ensures r == spec_unwrap_bool(v@),
{
    match v { JsValue::Boolean(b) => *b, _ => false }
}
pub fn val_unwrap_number(v: &JsValue) -> (r: JsNumber)
    requires spec_is_number(v@),
    ensures r == spec_unwrap_number(v@),
{
    match v { JsValue::Number(n) => *n, _ => js_canon_nan() }
}
pub fn val_is_nan(v: &JsValue) -> (r: bool) ensures r == spec_val_is_nan(v@) {
    match v { JsValue::Number(n) => num_is_nan(*n), _ => false }
}
pub fn val_is_pos_zero(v: &JsValue) -> (r: bool) ensures r == spec_val_is_pos_zero(v@) {
    match v { JsValue::Number(n) => num_is_pos_zero(*n), _ => false }
}
pub fn val_is_neg_zero(v: &JsValue) -> (r: bool) ensures r == spec_val_is_neg_zero(v@) {
    match v { JsValue::Number(n) => num_is_neg_zero(*n), _ => false }
}
pub fn val_is_pos_inf(v: &JsValue) -> (r: bool) ensures r == spec_val_is_pos_inf(v@) {
    match v { JsValue::Number(n) => num_is_pos_inf(*n), _ => false }
}
pub fn val_is_neg_inf(v: &JsValue) -> (r: bool) ensures r == spec_val_is_neg_inf(v@) {
    match v { JsValue::Number(n) => num_is_neg_inf(*n), _ => false }
}
pub fn val_is_finite_number(v: &JsValue) -> (r: bool) ensures r == spec_val_is_finite_number(v@) {
    match v { JsValue::Number(n) => num_is_finite(*n), _ => false }
}
pub fn val_is_bigint_zero(v: &JsValue) -> (r: bool) ensures r == spec_val_is_bigint_zero(v@) {
    match v { JsValue::BigInt(b) => bigint_is_zero(b), _ => false }
}
pub fn val_is_empty_string(v: &JsValue) -> (r: bool) ensures r == spec_val_is_empty_string(v@) {
    match v { JsValue::Str(s) => s.len() == 0, _ => false }
}
pub fn host_supports_htmldda() -> (r: bool) ensures r == spec_host_supports_htmldda() { true }
pub fn val_has_htmldda_slot(v: &JsValue) -> (r: bool) ensures r == spec_has_htmldda_slot(v@) {
    match v { JsValue::Object(o) => o.is_htmldda, _ => false }
}

/// String equality by length and code units (§7.2.11 step 4.a).
pub open spec fn spec_same_string_code_units(x: SpecJsValue, y: SpecJsValue) -> bool {
    match (x, y) {
        (SpecJsValue::Str(sx), SpecJsValue::Str(sy)) => sx == sy,
        _ => false,
    }
}

pub fn val_same_string_code_units(x: &JsValue, y: &JsValue) -> (r: bool)
    requires spec_is_string(x@), spec_is_string(y@),
    ensures r == spec_same_string_code_units(x@, y@),
{
    match (x, y) {
        (JsValue::Str(sx), JsValue::Str(sy)) => {
            if sx.len() != sy.len() {
                return false;
            }
            let n = sx.len();
            let mut i: usize = 0;
            while i < n
                invariant
                    0 <= i <= n,
                    n == sx@.len(),
                    n == sy@.len(),
                    x@ == SpecJsValue::Str(sx@),
                    y@ == SpecJsValue::Str(sy@),
                    forall|j: int| 0 <= j < i ==> sx@[j] == sy@[j],
                decreases n - i,
            {
                if sx[i] != sy[i] {
                    proof {
                        if sx@ == sy@ {
                            assert(sx@[i as int] == sy@[i as int]);
                        }
                    }
                    return false;
                }
                i = i + 1;
            }
            proof { assert(sx@ =~= sy@); }
            true
        }
        _ => false,
    }
}

/// BigInt::equal lifted to `JsValue` (§7.2.11 step 3.a).
pub open spec fn spec_val_bigint_equal(x: SpecJsValue, y: SpecJsValue) -> bool {
    match (x, y) {
        (SpecJsValue::BigInt(bx), SpecJsValue::BigInt(by_)) => spec_bigint_val(bx) == spec_bigint_val(by_),
        _ => false,
    }
}

pub fn val_bigint_equal(x: &JsValue, y: &JsValue) -> (r: bool)
    requires spec_is_bigint(x@), spec_is_bigint(y@),
    ensures r == spec_val_bigint_equal(x@, y@),
{
    match (x, y) {
        (JsValue::BigInt(bx), JsValue::BigInt(by_)) => bigint_equal(bx, by_),
        _ => false,
    }
}

/// Identity comparison on non-Number values (`_x_ is _y_` in §7.2.11 step 7).
pub open spec fn spec_val_non_number_is(x: SpecJsValue, y: SpecJsValue) -> bool {
    match (x, y) {
        (SpecJsValue::Undefined, SpecJsValue::Undefined) => true,
        (SpecJsValue::Null, SpecJsValue::Null) => true,
        (SpecJsValue::Boolean(bx), SpecJsValue::Boolean(by_)) => bx == by_,
        (SpecJsValue::BigInt(bx), SpecJsValue::BigInt(by_)) => spec_bigint_val(bx) == spec_bigint_val(by_),
        (SpecJsValue::Str(sx), SpecJsValue::Str(sy)) => sx == sy,
        (SpecJsValue::Symbol(ix), SpecJsValue::Symbol(iy)) => ix == iy,
        (SpecJsValue::Object(ox), SpecJsValue::Object(oy)) => ox.id == oy.id,
        _ => false,
    }
}

pub fn val_non_number_is(x: &JsValue, y: &JsValue) -> (r: bool)
    requires !spec_is_number(x@), !spec_is_number(y@),
    ensures r == spec_val_non_number_is(x@, y@),
{
    match (x, y) {
        (JsValue::Undefined, JsValue::Undefined) => true,
        (JsValue::Null, JsValue::Null) => true,
        (JsValue::Boolean(bx), JsValue::Boolean(by_)) => *bx == *by_,
        (JsValue::BigInt(bx), JsValue::BigInt(by_)) => bigint_equal(bx, by_),
        (JsValue::Str(_), JsValue::Str(_)) => val_same_string_code_units(x, y),
        (JsValue::Symbol(ix), JsValue::Symbol(iy)) => *ix == *iy,
        (JsValue::Object(ox), JsValue::Object(oy)) => ox.id == oy.id,
        _ => false,
    }
}

/// `ℝ(_x_) = ℝ(_y_)` when one is a BigInt and the other is a finite Number (§7.2.13 step 13.a).
pub open spec fn spec_val_real_equal(x: SpecJsValue, y: SpecJsValue) -> bool {
    match (x, y) {
        (SpecJsValue::BigInt(bx), SpecJsValue::Number(ny)) => spec_finite_number_real_eq_bigint(ny, bx),
        (SpecJsValue::Number(nx), SpecJsValue::BigInt(by_)) => spec_finite_number_real_eq_bigint(nx, by_),
        _ => false,
    }
}

pub fn val_real_equal(x: &JsValue, y: &JsValue) -> (r: bool)
    requires
        (spec_is_bigint(x@) && spec_val_is_finite_number(y@))
            || (spec_val_is_finite_number(x@) && spec_is_bigint(y@)),
    ensures r == spec_val_real_equal(x@, y@),
{
    match (x, y) {
        (JsValue::BigInt(bx), JsValue::Number(ny)) => finite_number_real_eq_bigint(*ny, bx),
        (JsValue::Number(nx), JsValue::BigInt(by_)) => finite_number_real_eq_bigint(*nx, by_),
        _ => false,
    }
}

/// `ToPrimitive` (§7.1.1) on `JsValue` with default or number hint.
pub open spec fn spec_to_primitive_default(v: SpecJsValue) -> AbruptOrNormal<SpecJsValue> {
    match v {
        SpecJsValue::Object(o) => match o.prim_default {
            SpecObjectCoercion::Primitive(p) => AbruptOrNormal::Normal(spec_prim_to_val(p)),
            SpecObjectCoercion::ThrowTypeError => AbruptOrNormal::ThrowTypeError,
        },
        _ => AbruptOrNormal::Normal(v),
    }
}

pub open spec fn spec_to_primitive_number(v: SpecJsValue) -> AbruptOrNormal<SpecJsValue> {
    match v {
        SpecJsValue::Object(o) => match o.prim_number {
            SpecObjectCoercion::Primitive(p) => AbruptOrNormal::Normal(spec_prim_to_val(p)),
            SpecObjectCoercion::ThrowTypeError => AbruptOrNormal::ThrowTypeError,
        },
        _ => AbruptOrNormal::Normal(v),
    }
}

pub fn to_primitive_default(v: &JsValue) -> (r: AbruptOrNormal<JsValue>)
    ensures
        match r {
            AbruptOrNormal::Normal(rv) =>
                spec_to_primitive_default(v@) == AbruptOrNormal::Normal(rv@)
                    && !spec_is_object(rv@),
            AbruptOrNormal::ThrowTypeError =>
                spec_to_primitive_default(v@) == AbruptOrNormal::ThrowTypeError,
        },
{
    match v {
        JsValue::Object(o) => match &o.prim_default {
            ObjectCoercion::Primitive(p) => AbruptOrNormal::Normal(prim_to_val(p)),
            ObjectCoercion::ThrowTypeError => AbruptOrNormal::ThrowTypeError,
        },
        _ => AbruptOrNormal::Normal(v.clone()),
    }
}

pub fn to_primitive_number(v: &JsValue) -> (r: AbruptOrNormal<JsValue>)
    ensures
        match r {
            AbruptOrNormal::Normal(rv) =>
                spec_to_primitive_number(v@) == AbruptOrNormal::Normal(rv@)
                    && !spec_is_object(rv@),
            AbruptOrNormal::ThrowTypeError =>
                spec_to_primitive_number(v@) == AbruptOrNormal::ThrowTypeError,
        },
{
    match v {
        JsValue::Object(o) => match &o.prim_number {
            ObjectCoercion::Primitive(p) => AbruptOrNormal::Normal(prim_to_val(p)),
            ObjectCoercion::ThrowTypeError => AbruptOrNormal::ThrowTypeError,
        },
        _ => AbruptOrNormal::Normal(v.clone()),
    }
}

// ===============================================================================================
// 7. Verified `StrWhiteSpace` Trimming, `StringToBigInt` (§7.1.14) & `StringToNumber` (§7.1.4.1.1)
// ===============================================================================================

/// Exact ECMA-262 §12.2 WhiteSpace + §12.3 LineTerminator UTF-16 code units.
pub open spec fn spec_is_str_whitespace(cu: u16) -> bool {
    cu == 0x0009u16 || cu == 0x000Au16 || cu == 0x000Bu16 || cu == 0x000Cu16
        || cu == 0x000Du16 || cu == 0x0020u16 || cu == 0x00A0u16 || cu == 0x1680u16
        || (0x2000u16 <= cu && cu <= 0x200Au16)
        || cu == 0x2028u16 || cu == 0x2029u16 || cu == 0x202Fu16
        || cu == 0x205Fu16 || cu == 0x3000u16 || cu == 0xFEFFu16
}

pub fn is_str_whitespace(cu: u16) -> (r: bool) ensures r == spec_is_str_whitespace(cu) {
    cu == 0x0009u16 || cu == 0x000Au16 || cu == 0x000Bu16 || cu == 0x000Cu16
        || cu == 0x000Du16 || cu == 0x0020u16 || cu == 0x00A0u16 || cu == 0x1680u16
        || (cu >= 0x2000u16 && cu <= 0x200Au16)
        || cu == 0x2028u16 || cu == 0x2029u16 || cu == 0x202Fu16
        || cu == 0x205Fu16 || cu == 0x3000u16 || cu == 0xFEFFu16
}

pub open spec fn spec_trim_start_idx(s: Seq<u16>, i: nat) -> nat
    decreases s.len() - i,
{
    if i < s.len() && spec_is_str_whitespace(s[i as int]) {
        spec_trim_start_idx(s, i + 1)
    } else {
        i
    }
}

pub open spec fn spec_trim_end_idx(s: Seq<u16>, start: nat, end: nat) -> nat
    decreases end - start,
{
    if end > start && end <= s.len() && spec_is_str_whitespace(s[end as int - 1]) {
        spec_trim_end_idx(s, start, (end - 1) as nat)
    } else {
        end
    }
}

pub open spec fn spec_trim_utf16(s: Seq<u16>) -> Seq<u16> {
    let a = spec_trim_start_idx(s, 0);
    let b = spec_trim_end_idx(s, a, s.len());
    if a <= b && b <= s.len() {
        s.subrange(a as int, b as int)
    } else {
        Seq::empty()
    }
}

fn trim_bounds_utf16(s: &Vec<u16>) -> (r: (usize, usize))
    ensures
        r.0 <= r.1,
        r.1 <= s.len(),
        s@.subrange(r.0 as int, r.1 as int) =~= spec_trim_utf16(s@),
{
    let n = s.len();
    let mut a: usize = 0;
    while a < n && is_str_whitespace(s[a])
        invariant
            0 <= a <= n,
            n == s@.len(),
            spec_trim_start_idx(s@, 0) == spec_trim_start_idx(s@, a as nat),
        decreases n - a,
    {
        a = a + 1;
    }
    let mut b: usize = n;
    while b > a && is_str_whitespace(s[b - 1])
        invariant
            a <= b <= n,
            n == s@.len(),
            spec_trim_end_idx(s@, a as nat, n as nat) == spec_trim_end_idx(s@, a as nat, b as nat),
        decreases b - a,
    {
        b = b - 1;
    }
    (a, b)
}

pub open spec fn spec_digit_val(cu: u16, radix: u32) -> Option<u32> {
    if radix == 2 {
        if cu == 0x30u16 || cu == 0x31u16 { Some((cu - 0x30u16) as u32) } else { None }
    } else if radix == 8 {
        if 0x30u16 <= cu && cu <= 0x37u16 { Some((cu - 0x30u16) as u32) } else { None }
    } else if radix == 10 {
        if 0x30u16 <= cu && cu <= 0x39u16 { Some((cu - 0x30u16) as u32) } else { None }
    } else {
        if 0x30u16 <= cu && cu <= 0x39u16 {
            Some((cu - 0x30u16) as u32)
        } else if 0x41u16 <= cu && cu <= 0x46u16 {
            Some((cu - 0x41u16 + 10u16) as u32)
        } else if 0x61u16 <= cu && cu <= 0x66u16 {
            Some((cu - 0x61u16 + 10u16) as u32)
        } else {
            None
        }
    }
}

fn digit_val(cu: u16, radix: u32) -> (r: Option<u32>)
    requires radix == 2 || radix == 8 || radix == 10 || radix == 16,
    ensures
        r == spec_digit_val(cu, radix),
        match r { Some(d) => d < radix, None => true },
{
    if radix == 2 {
        if cu == 0x30u16 || cu == 0x31u16 { Some((cu - 0x30u16) as u32) } else { None }
    } else if radix == 8 {
        if cu >= 0x30u16 && cu <= 0x37u16 { Some((cu - 0x30u16) as u32) } else { None }
    } else if radix == 10 {
        if cu >= 0x30u16 && cu <= 0x39u16 { Some((cu - 0x30u16) as u32) } else { None }
    } else {
        if cu >= 0x30u16 && cu <= 0x39u16 {
            Some((cu - 0x30u16) as u32)
        } else if cu >= 0x41u16 && cu <= 0x46u16 {
            Some((cu - 0x41u16 + 10u16) as u32)
        } else if cu >= 0x61u16 && cu <= 0x66u16 {
            Some((cu - 0x61u16 + 10u16) as u32)
        } else {
            None
        }
    }
}

/// Multiply a canonical limb sequence by `mul` (`<= 16`) and add `add` (`< 16`).
pub open spec fn spec_limbs_mul_add_step(limbs: Seq<u32>, idx: nat, mul: u32, carry: u64) -> Seq<u32>
    decreases limbs.len() - idx,
{
    if idx >= limbs.len() {
        if carry == 0 {
            Seq::empty()
        } else {
            seq![carry as u32]
        }
    } else {
        let cur: u64 = ((limbs[idx as int] as u64) * (mul as u64) + carry) as u64;
        let low: u32 = (cur % 0x1_0000_0000u64) as u32;
        let next_carry: u64 = cur / 0x1_0000_0000u64;
        seq![low] + spec_limbs_mul_add_step(limbs, idx + 1, mul, next_carry)
    }
}

fn limbs_mul_add_exec(limbs: &Vec<u32>, mul: u32, add: u32) -> (out: Vec<u32>)
    requires 2 <= mul <= 16, add < mul,
    ensures out@ =~= spec_limbs_mul_add_step(limbs@, 0, mul, add as u64),
{
    let n = limbs.len();
    let mut out: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    let mut carry: u64 = add as u64;
    while i < n
        invariant
            0 <= i <= n,
            n == limbs@.len(),
            2 <= mul <= 16,
            carry < 16,
            spec_limbs_mul_add_step(limbs@, 0, mul, add as u64)
                =~= out@ + spec_limbs_mul_add_step(limbs@, i as nat, mul, carry),
        decreases n - i,
    {
        let ghost old_out = out@;
        let limb = limbs[i] as u64;
        let m64 = mul as u64;
        proof {
            assert(limb <= 0xFFFF_FFFFu64);
            assert(m64 <= 16u64);
            assert(limb * m64 + carry <= 0xFFFF_FFFFu64 * 16u64 + 15u64) by (nonlinear_arith)
                requires limb <= 0xFFFF_FFFFu64, m64 <= 16u64, carry <= 15u64;
        }
        let cur: u64 = limb * m64 + carry;
        let low: u32 = (cur % 0x1_0000_0000u64) as u32;
        let next_carry: u64 = cur / 0x1_0000_0000u64;
        out.push(low);
        proof {
            assert(old_out + (seq![low] + spec_limbs_mul_add_step(limbs@, (i + 1) as nat, mul, next_carry))
                =~= out@ + spec_limbs_mul_add_step(limbs@, (i + 1) as nat, mul, next_carry));
        }
        carry = next_carry;
        i = i + 1;
    }
    if carry != 0 {
        let ghost old_out = out@;
        out.push(carry as u32);
        proof {
            assert(old_out + seq![carry as u32] =~= out@);
        }
    } else {
        proof {
            assert(out@ + Seq::<u32>::empty() =~= out@);
        }
    }
    out
}

pub open spec fn spec_parse_radix_limbs(s: Seq<u16>, idx: nat, radix: u32, acc: Seq<u32>) -> Option<Seq<u32>>
    decreases s.len() - idx,
{
    if idx >= s.len() {
        Some(acc)
    } else {
        match spec_digit_val(s[idx as int], radix) {
            None => None,
            Some(d) => {
                let next = if acc.len() == 0 && d == 0 {
                    acc
                } else {
                    spec_limbs_mul_add_step(acc, 0, radix, d as u64)
                };
                spec_parse_radix_limbs(s, idx + 1, radix, next)
            }
        }
    }
}

fn parse_radix_limbs_exec(s: &Vec<u16>, start: usize, end: usize, radix: u32) -> (r: Option<Vec<u32>>)
    requires
        start <= end,
        end <= s.len(),
        radix == 2 || radix == 8 || radix == 10 || radix == 16,
    ensures
        match r {
            Some(v) => spec_parse_radix_limbs(s@.subrange(start as int, end as int), 0, radix, Seq::empty()) == Some(v@),
            None => spec_parse_radix_limbs(s@.subrange(start as int, end as int), 0, radix, Seq::empty()) is None,
        },
{
    let ghost slice = s@.subrange(start as int, end as int);
    let mut acc: Vec<u32> = Vec::new();
    let mut k: usize = 0;
    let len = end - start;
    proof { assert(acc@ =~= Seq::<u32>::empty()); }
    while k < len
        invariant
            0 <= k <= len,
            start + len == end,
            end <= s.len(),
            radix == 2 || radix == 8 || radix == 10 || radix == 16,
            slice =~= s@.subrange(start as int, end as int),
            spec_parse_radix_limbs(slice, 0, radix, Seq::empty())
                == spec_parse_radix_limbs(slice, k as nat, radix, acc@),
        decreases len - k,
    {
        let cu = s[start + k];
        proof { assert(cu == slice[k as int]); }
        match digit_val(cu, radix) {
            None => { return None; }
            Some(d) => {
                if !(acc.len() == 0 && d == 0) {
                    acc = limbs_mul_add_exec(&acc, radix, d);
                }
                k = k + 1;
            }
        }
    }
    Some(acc)
}

/// ECMA-262 §7.1.14 `StringToBigInt ( string )`: returns `BigInt` or `Undefined` on syntax failure.
pub open spec fn spec_string_to_bigint_trimmed(t: Seq<u16>) -> SpecJsValue {
    if t.len() == 0 {
        SpecJsValue::BigInt(SpecBigInt { neg: false, limbs: Seq::empty() })
    } else if t.len() >= 2 && t[0] == 0x30u16 && (t[1] == 0x78u16 || t[1] == 0x58u16) {
        if t.len() == 2 {
            SpecJsValue::Undefined
        } else {
            match spec_parse_radix_limbs(t.subrange(2, t.len() as int), 0, 16, Seq::empty()) {
                Some(limbs) => SpecJsValue::BigInt(SpecBigInt { neg: false, limbs }),
                None => SpecJsValue::Undefined,
            }
        }
    } else if t.len() >= 2 && t[0] == 0x30u16 && (t[1] == 0x62u16 || t[1] == 0x42u16) {
        if t.len() == 2 {
            SpecJsValue::Undefined
        } else {
            match spec_parse_radix_limbs(t.subrange(2, t.len() as int), 0, 2, Seq::empty()) {
                Some(limbs) => SpecJsValue::BigInt(SpecBigInt { neg: false, limbs }),
                None => SpecJsValue::Undefined,
            }
        }
    } else if t.len() >= 2 && t[0] == 0x30u16 && (t[1] == 0x6Fu16 || t[1] == 0x4Fu16) {
        if t.len() == 2 {
            SpecJsValue::Undefined
        } else {
            match spec_parse_radix_limbs(t.subrange(2, t.len() as int), 0, 8, Seq::empty()) {
                Some(limbs) => SpecJsValue::BigInt(SpecBigInt { neg: false, limbs }),
                None => SpecJsValue::Undefined,
            }
        }
    } else {
        let neg = t[0] == 0x2Du16;
        let has_sign = t[0] == 0x2Du16 || t[0] == 0x2Bu16;
        let body = if has_sign { t.subrange(1, t.len() as int) } else { t };
        if body.len() == 0 {
            SpecJsValue::Undefined
        } else {
            match spec_parse_radix_limbs(body, 0, 10, Seq::empty()) {
                Some(limbs) => SpecJsValue::BigInt(SpecBigInt {
                    neg: neg && limbs.len() > 0,
                    limbs,
                }),
                None => SpecJsValue::Undefined,
            }
        }
    }
}

pub open spec fn spec_string_to_bigint_val(v: SpecJsValue) -> SpecJsValue {
    match v {
        SpecJsValue::Str(s) => spec_string_to_bigint_trimmed(spec_trim_utf16(s)),
        _ => SpecJsValue::Undefined,
    }
}

pub fn val_string_to_bigint(v: &JsValue) -> (r: JsValue)
    requires spec_is_string(v@),
    ensures
        r@ == spec_string_to_bigint_val(v@),
        spec_is_bigint(r@) || spec_is_undefined(r@),
{
    match v {
        JsValue::Str(s) => {
            let (a, b) = trim_bounds_utf16(s);
            let ghost t = s@.subrange(a as int, b as int);
            let len = b - a;
            if len == 0 {
                return JsValue::BigInt(JsBigInt { neg: false, limbs: Vec::new() });
            }
            if len >= 2 && s[a] == 0x30u16 && (s[a + 1] == 0x78u16 || s[a + 1] == 0x58u16) {
                if len == 2 { return JsValue::Undefined; }
                proof { assert(t.subrange(2, t.len() as int) =~= s@.subrange((a + 2) as int, b as int)); }
                return match parse_radix_limbs_exec(s, a + 2, b, 16) {
                    Some(limbs) => JsValue::BigInt(JsBigInt { neg: false, limbs }),
                    None => JsValue::Undefined,
                };
            }
            if len >= 2 && s[a] == 0x30u16 && (s[a + 1] == 0x62u16 || s[a + 1] == 0x42u16) {
                if len == 2 { return JsValue::Undefined; }
                proof { assert(t.subrange(2, t.len() as int) =~= s@.subrange((a + 2) as int, b as int)); }
                return match parse_radix_limbs_exec(s, a + 2, b, 2) {
                    Some(limbs) => JsValue::BigInt(JsBigInt { neg: false, limbs }),
                    None => JsValue::Undefined,
                };
            }
            if len >= 2 && s[a] == 0x30u16 && (s[a + 1] == 0x6Fu16 || s[a + 1] == 0x4Fu16) {
                if len == 2 { return JsValue::Undefined; }
                proof { assert(t.subrange(2, t.len() as int) =~= s@.subrange((a + 2) as int, b as int)); }
                return match parse_radix_limbs_exec(s, a + 2, b, 8) {
                    Some(limbs) => JsValue::BigInt(JsBigInt { neg: false, limbs }),
                    None => JsValue::Undefined,
                };
            }
            let c0 = s[a];
            let neg = c0 == 0x2Du16;
            let has_sign = c0 == 0x2Du16 || c0 == 0x2Bu16;
            let body_start = if has_sign { a + 1 } else { a };
            if body_start == b {
                proof {
                    assert(has_sign);
                    assert(t.subrange(1, t.len() as int) =~= s@.subrange((a + 1) as int, b as int));
                }
                return JsValue::Undefined;
            }
            proof {
                if has_sign {
                    assert(t.subrange(1, t.len() as int) =~= s@.subrange((a + 1) as int, b as int));
                } else {
                    assert(t =~= s@.subrange(a as int, b as int));
                }
            }
            match parse_radix_limbs_exec(s, body_start, b, 10) {
                Some(limbs) => {
                    let is_neg = neg && limbs.len() > 0;
                    JsValue::BigInt(JsBigInt { neg: is_neg, limbs })
                }
                None => JsValue::Undefined,
            }
        }
        _ => JsValue::Undefined,
    }
}

// -----------------------------------------------------------------------------------------------
// Verified `StringToNumber` (§7.1.4.1.1) with exact rational BigNat IEEE-754 round-to-nearest-even
// -----------------------------------------------------------------------------------------------

/// Compare two canonical `Seq<u32>` limb vectors: -1 (`<`), 0 (`==`), +1 (`>`).
pub open spec fn spec_cmp_limbs_from(a: Seq<u32>, b: Seq<u32>, k: nat) -> int
    decreases k,
{
    if k == 0 {
        0int
    } else {
        let idx = (k - 1) as int;
        if a[idx] < b[idx] {
            -1int
        } else if a[idx] > b[idx] {
            1int
        } else {
            spec_cmp_limbs_from(a, b, (k - 1) as nat)
        }
    }
}

pub open spec fn spec_cmp_limbs(a: Seq<u32>, b: Seq<u32>) -> int {
    if a.len() < b.len() {
        -1int
    } else if a.len() > b.len() {
        1int
    } else {
        spec_cmp_limbs_from(a, b, a.len())
    }
}

fn cmp_limbs_exec(a: &Vec<u32>, b: &Vec<u32>) -> (r: i8)
    ensures r as int == spec_cmp_limbs(a@, b@),
{
    if a.len() < b.len() {
        return -1i8;
    }
    if a.len() > b.len() {
        return 1i8;
    }
    let mut k = a.len();
    while k > 0
        invariant
            0 <= k <= a.len(),
            a.len() == b.len(),
            spec_cmp_limbs_from(a@, b@, a@.len()) == spec_cmp_limbs_from(a@, b@, k as nat),
        decreases k,
    {
        let av = a[k - 1];
        let bv = b[k - 1];
        if av < bv { return -1i8; }
        if av > bv { return 1i8; }
        k = k - 1;
    }
    0i8
}

/// Subtract `b` from `a` assuming `a >= b` in limb order (non-negative borrow-propagating sub),
/// then strip trailing zeros.
pub open spec fn spec_sub_limbs_raw(a: Seq<u32>, b: Seq<u32>, idx: nat, borrow: u64) -> Seq<u32>
    decreases a.len() - idx,
{
    if idx >= a.len() {
        Seq::empty()
    } else {
        let av: i64 = a[idx as int] as i64;
        let bv: i64 = if idx < b.len() { b[idx as int] as i64 } else { 0i64 };
        let diff: i64 = (av - bv - (borrow as i64)) as i64;
        let (low, next_borrow): (u32, u64) = if diff < 0 {
            ((diff + 0x1_0000_0000i64) as u32, 1u64)
        } else {
            (diff as u32, 0u64)
        };
        seq![low] + spec_sub_limbs_raw(a, b, idx + 1, next_borrow)
    }
}

pub open spec fn spec_strip_limbs(a: Seq<u32>) -> Seq<u32> {
    a.subrange(0, spec_canonical_len(a) as int)
}

fn strip_limbs_exec(a: Vec<u32>) -> (out: Vec<u32>)
    ensures out@ =~= spec_strip_limbs(a@),
{
    let cl = canonical_len_exec(&a);
    let mut out: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    while i < cl
        invariant
            0 <= i <= cl,
            cl <= a.len(),
            out@ =~= a@.subrange(0, i as int),
        decreases cl - i,
    {
        out.push(a[i]);
        proof { assert(out@ =~= a@.subrange(0, (i + 1) as int)); }
        i = i + 1;
    }
    out
}

pub open spec fn spec_sub_limbs(a: Seq<u32>, b: Seq<u32>) -> Seq<u32> {
    spec_strip_limbs(spec_sub_limbs_raw(a, b, 0, 0))
}

fn sub_limbs_exec(a: &Vec<u32>, b: &Vec<u32>) -> (out: Vec<u32>)
    ensures out@ =~= spec_sub_limbs(a@, b@),
{
    let n = a.len();
    let mut raw: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    let mut borrow: u64 = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == a@.len(),
            borrow <= 1,
            spec_sub_limbs_raw(a@, b@, 0, 0) =~= raw@ + spec_sub_limbs_raw(a@, b@, i as nat, borrow),
        decreases n - i,
    {
        let ghost old_raw = raw@;
        let av: i64 = a[i] as i64;
        let bv: i64 = if i < b.len() { b[i] as i64 } else { 0i64 };
        let diff: i64 = av - bv - (borrow as i64);
        let (low, next_borrow): (u32, u64) = if diff < 0 {
            ((diff + 0x1_0000_0000i64) as u32, 1u64)
        } else {
            (diff as u32, 0u64)
        };
        raw.push(low);
        proof {
            assert(old_raw + (seq![low] + spec_sub_limbs_raw(a@, b@, (i + 1) as nat, next_borrow))
                =~= raw@ + spec_sub_limbs_raw(a@, b@, (i + 1) as nat, next_borrow));
        }
        borrow = next_borrow;
        i = i + 1;
    }
    proof { assert(raw@ + Seq::<u32>::empty() =~= raw@); }
    strip_limbs_exec(raw)
}

/// Bit length of a non-empty canonical limb vector: `(len - 1) * 32 + bit_len_u32(last)`.
pub open spec fn spec_bit_len_u32_from(v: u32, b: nat) -> nat
    decreases b,
{
    if b == 0 {
        1nat
    } else if (v as nat) >= spec_pow2(b) {
        b + 1
    } else {
        spec_bit_len_u32_from(v, (b - 1) as nat)
    }
}

fn bit_len_u32_exec(v: u32) -> (r: u32)
    ensures r as nat == spec_bit_len_u32_from(v, 31), 1 <= r <= 32,
{
    let mut b: u32 = 31;
    while b > 0
        invariant
            0 <= b <= 31,
            spec_bit_len_u32_from(v, 31) == spec_bit_len_u32_from(v, b as nat),
        decreases b,
    {
        let p = pow2_u64(b);
        if (v as u64) >= p {
            return b + 1;
        }
        b = b - 1;
    }
    1
}

pub open spec fn spec_limbs_bit_len(a: Seq<u32>) -> nat {
    if a.len() == 0 {
        0nat
    } else {
        ((a.len() - 1) as nat) * 32nat + spec_bit_len_u32_from(a.last(), 31)
    }
}

fn limbs_bit_len_exec(a: &Vec<u32>) -> (r: usize)
    requires a.len() < 0x0100_0000usize,
    ensures
        r as nat == spec_limbs_bit_len(a@),
        r <= a.len() * 32,
{
    if a.len() == 0 {
        0
    } else {
        let top = bit_len_u32_exec(a[a.len() - 1]) as usize;
        (a.len() - 1) * 32 + top
    }
}

/// Multiply limb vector `a` by `2^shift` (`shift = q * 32 + r`).
pub open spec fn spec_shl_limbs(a: Seq<u32>, shift: nat) -> Seq<u32> {
    if a.len() == 0 || shift == 0 {
        a
    } else {
        let q = shift / 32nat;
        let r = shift % 32nat;
        let zeros = Seq::new(q, |_i: int| 0u32);
        if r == 0 {
            zeros + a
        } else {
            let mul = spec_pow2(r) as u32;
            // r in 1..31 -> mul in 2..2^31; do shift via spec_shl_small
            zeros + spec_shl_small_limbs(a, 0, r, 0)
        }
    }
}

pub open spec fn spec_shl_small_limbs(a: Seq<u32>, idx: nat, r: nat, carry: u64) -> Seq<u32>
    decreases a.len() - idx,
{
    if idx >= a.len() {
        if carry == 0 { Seq::empty() } else { seq![carry as u32] }
    } else {
        let p = spec_pow2(r);
        let cur: u64 = ((a[idx as int] as nat) * p + (carry as nat)) as u64;
        let low: u32 = (cur % 0x1_0000_0000u64) as u32;
        let next_carry: u64 = cur / 0x1_0000_0000u64;
        seq![low] + spec_shl_small_limbs(a, idx + 1, r, next_carry)
    }
}

fn shl_limbs_exec(a: &Vec<u32>, shift: usize) -> (out: Vec<u32>)
    requires shift <= 16384,
    ensures out@ =~= spec_shl_limbs(a@, shift as nat),
{
    if a.len() == 0 || shift == 0 {
        return a.clone();
    }
    let q = shift / 32;
    let r = (shift % 32) as u32;
    let mut out: Vec<u32> = Vec::new();
    let mut z: usize = 0;
    while z < q
        invariant
            0 <= z <= q,
            out@ =~= Seq::new(z as nat, |_i: int| 0u32),
        decreases q - z,
    {
        out.push(0u32);
        proof { assert(out@ =~= Seq::new((z + 1) as nat, |_i: int| 0u32)); }
        z = z + 1;
    }
    let ghost zeros = out@;
    if r == 0 {
        let mut i: usize = 0;
        while i < a.len()
            invariant
                0 <= i <= a.len(),
                out@ =~= zeros + a@.subrange(0, i as int),
            decreases a.len() - i,
        {
            out.push(a[i]);
            proof { assert(out@ =~= zeros + a@.subrange(0, (i + 1) as int)); }
            i = i + 1;
        }
        proof { assert(a@.subrange(0, a.len() as int) =~= a@); }
        return out;
    }
    let p_r = pow2_u64(r);
    proof {
        lemma_pow2_monotone(r as nat, 31nat);
        lemma_pow2_small_values();
    }
    let n = a.len();
    let mut tail: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    let mut carry: u64 = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == a@.len(),
            1 <= r <= 31,
            p_r as nat == spec_pow2(r as nat),
            p_r <= 2147483648u64,
            carry < 2147483648u64,
            spec_shl_small_limbs(a@, 0, r as nat, 0)
                =~= tail@ + spec_shl_small_limbs(a@, i as nat, r as nat, carry),
        decreases n - i,
    {
        let ghost old_tail = tail@;
        let av = a[i] as u64;
        proof {
            assert((av as nat) * (p_r as nat) + (carry as nat)
                <= 0xFFFF_FFFFnat * 2147483648nat + 2147483647nat) by (nonlinear_arith)
                requires av <= 0xFFFF_FFFFu64, p_r <= 2147483648u64, carry < 2147483648u64;
        }
        let cur: u64 = av * p_r + carry;
        let low: u32 = (cur % 0x1_0000_0000u64) as u32;
        let next_carry: u64 = cur / 0x1_0000_0000u64;
        tail.push(low);
        proof {
            assert(old_tail + (seq![low] + spec_shl_small_limbs(a@, (i + 1) as nat, r as nat, next_carry))
                =~= tail@ + spec_shl_small_limbs(a@, (i + 1) as nat, r as nat, next_carry));
        }
        carry = next_carry;
        i = i + 1;
    }
    if carry != 0 {
        let ghost old_tail = tail@;
        tail.push(carry as u32);
        proof { assert(old_tail + seq![carry as u32] =~= tail@); }
    } else {
        proof { assert(tail@ + Seq::<u32>::empty() =~= tail@); }
    }
    let mut j: usize = 0;
    while j < tail.len()
        invariant
            0 <= j <= tail.len(),
            out@ =~= zeros + tail@.subrange(0, j as int),
        decreases tail.len() - j,
    {
        out.push(tail[j]);
        proof { assert(out@ =~= zeros + tail@.subrange(0, (j + 1) as int)); }
        j = j + 1;
    }
    proof { assert(tail@.subrange(0, tail.len() as int) =~= tail@); }
    out
}

/// Extract a 54-bit quotient & remainder `(q, rem)` of `num / den` via 54-step binary long division
/// when `0 <= num < 2^54 * den`.
pub open spec fn spec_div_54_steps(rem: Seq<u32>, den: Seq<u32>, step: nat, q: u64) -> (u64, Seq<u32>)
    decreases step,
{
    if step == 0 {
        (q, rem)
    } else {
        let b = (step - 1) as nat;
        let scaled_den = spec_shl_limbs(den, b);
        if spec_cmp_limbs(rem, scaled_den) >= 0 {
            let next_rem = spec_sub_limbs(rem, scaled_den);
            let next_q: u64 = (q + spec_pow2(b)) as u64;
            spec_div_54_steps(next_rem, den, b, next_q)
        } else {
            spec_div_54_steps(rem, den, b, q)
        }
    }
}

fn div_54_steps_exec(num: &Vec<u32>, den: &Vec<u32>) -> (r: (u64, Vec<u32>))
    ensures
        r.0 == spec_div_54_steps(num@, den@, 54, 0).0,
        r.1@ =~= spec_div_54_steps(num@, den@, 54, 0).1,
        r.0 < 0x0040_0000_0000_0000u64,
{
    proof { lemma_pow2_small_values(); }
    let mut rem = num.clone();
    let mut step: u32 = 54;
    let mut q: u64 = 0;
    while step > 0
        invariant
            0 <= step <= 54,
            (q as nat) + spec_pow2(step as nat) <= spec_pow2(54),
            spec_pow2(54) == 0x0040_0000_0000_0000nat,
            spec_div_54_steps(num@, den@, 54, 0)
                == spec_div_54_steps(rem@, den@, step as nat, q),
        decreases step,
    {
        let b = step - 1;
        let scaled_den = shl_limbs_exec(den, b as usize);
        let p_b = pow2_u64(b);
        proof {
            assert(spec_pow2(step as nat) == 2nat * spec_pow2(b as nat));
        }
        if cmp_limbs_exec(&rem, &scaled_den) >= 0 {
            rem = sub_limbs_exec(&rem, &scaled_den);
            q = q + p_b;
        }
        step = b;
    }
    (q, rem)
}

pub open spec fn spec_mul_pow10_limbs(a: Seq<u32>, k: nat) -> Seq<u32>
    decreases k,
{
    if k == 0 {
        a
    } else {
        spec_mul_pow10_limbs(spec_limbs_mul_add_step(a, 0, 10, 0), (k - 1) as nat)
    }
}

fn mul_pow10_limbs_exec(mut a: Vec<u32>, k: u32) -> (out: Vec<u32>)
    ensures out@ =~= spec_mul_pow10_limbs(a@, k as nat),
{
    let mut rem_k: u32 = k;
    let ghost orig = a@;
    while rem_k > 0
        invariant
            0 <= rem_k <= k,
            spec_mul_pow10_limbs(orig, k as nat) == spec_mul_pow10_limbs(a@, rem_k as nat),
        decreases rem_k,
    {
        a = limbs_mul_add_exec(&a, 10, 0);
        rem_k = rem_k - 1;
    }
    a
}

/// Round exact positive rational `(neg, num / den)` (`num > 0`, `den > 0` canonical limbs)
/// to IEEE-754 binary64 using exact round-to-nearest-even (including subnormals & overflow).
pub open spec fn spec_pack_ieee754(neg: bool, raw_e: u64, raw_m: u64) -> JsNumber {
    let sign_part: u64 = if neg { 0x8000_0000_0000_0000u64 } else { 0u64 };
    JsNumber((sign_part + raw_e * 0x0010_0000_0000_0000u64 + raw_m) as u64)
}

fn pack_ieee754(neg: bool, raw_e: u64, raw_m: u64) -> (r: JsNumber)
    requires raw_e <= 0x7FFu64, raw_m < 0x0010_0000_0000_0000u64,
    ensures r == spec_pack_ieee754(neg, raw_e, raw_m),
{
    let sign_part: u64 = if neg { 0x8000_0000_0000_0000u64 } else { 0u64 };
    JsNumber(sign_part + raw_e * 0x0010_0000_0000_0000u64 + raw_m)
}

pub open spec fn spec_round_rational_to_f64(neg: bool, num: Seq<u32>, den: Seq<u32>) -> JsNumber {
    let bn = spec_limbs_bit_len(num) as int;
    let bd = spec_limbs_bit_len(den) as int;
    // Initial binary exponent estimate e0 for floor(log2(num / den)):
    let e_est: int = bn - bd;
    // Ensure scaled quotient sits in [2^52, 2^53) by adjusting e by -1 if num * 2^(52-e) < den * 2^52
    let e0: int = if e_est >= 0 {
        let lhs = num;
        let rhs = spec_shl_limbs(den, e_est as nat);
        if spec_cmp_limbs(lhs, rhs) >= 0 { e_est } else { e_est - 1 }
    } else {
        let lhs = spec_shl_limbs(num, (-e_est) as nat);
        let rhs = den;
        if spec_cmp_limbs(lhs, rhs) >= 0 { e_est } else { e_est - 1 }
    };
    if e0 > 1023 {
        if neg { spec_neg_inf() } else { spec_pos_inf() }
    } else if e0 < -1075 {
        if neg { spec_neg_zero() } else { spec_pos_zero() }
    } else {
        // Target significand shift `s`:
        // For normal numbers (e0 >= -1022), s = 52 - e0 (1-bit implicit + 52 mantissa bits).
        // For subnormals (-1075 <= e0 < -1022), s = 1074 (fixed ULP = 2^-1074).
        let is_sub = e0 < -1022;
        let s: int = if is_sub { 1074int } else { 52int - e0 };
        let (s_num, s_den) = if s >= 0 {
            (spec_shl_limbs(num, s as nat), den)
        } else {
            (num, spec_shl_limbs(den, (-s) as nat))
        };
        if s_num.len() >= 512 || s_den.len() >= 512 {
            // Unreachable under bounded exponent guard, kept total in spec
            if neg { spec_neg_zero() } else { spec_pos_zero() }
        } else {
            let (q, rem) = spec_div_54_steps(s_num, s_den, 54, 0);
            let twice_rem = spec_shl_limbs(rem, 1);
            let cmp = spec_cmp_limbs(twice_rem, s_den);
            let round_up = cmp > 0 || (cmp == 0 && (q % 2u64) == 1u64);
            let q_rounded: u64 = if round_up { (q + 1) as u64 } else { q };
            if is_sub {
                if q_rounded >= 0x0010_0000_0000_0000u64 {
                    // Rounded up from max subnormal to min normal (raw_e = 1, raw_m = 0)
                    spec_pack_ieee754(neg, 1u64, 0u64)
                } else {
                    spec_pack_ieee754(neg, 0u64, q_rounded)
                }
            } else {
                if q_rounded >= 0x0020_0000_0000_0000u64 {
                    let next_e = e0 + 1;
                    if next_e > 1023 {
                        if neg { spec_neg_inf() } else { spec_pos_inf() }
                    } else {
                        spec_pack_ieee754(neg, (next_e + 1023) as u64, 0u64)
                    }
                } else if q_rounded < 0x0010_0000_0000_0000u64 {
                    spec_pack_ieee754(neg, 0u64, q_rounded)
                } else {
                    let raw_e = (e0 + 1023) as u64;
                    let raw_m = (q_rounded - 0x0010_0000_0000_0000u64) as u64;
                    spec_pack_ieee754(neg, raw_e, raw_m)
                }
            }
        }
    }
}

#[verifier::spinoff_prover]
fn round_rational_to_f64_exec(neg: bool, num: &Vec<u32>, den: &Vec<u32>) -> (r: JsNumber)
    requires
        num.len() > 0,
        den.len() > 0,
        num.len() < 400,
        den.len() < 400,
    ensures r == spec_round_rational_to_f64(neg, num@, den@),
{
    let bn = limbs_bit_len_exec(num) as i64;
    let bd = limbs_bit_len_exec(den) as i64;
    let e_est: i64 = bn - bd;
    let e0: i64 = if e_est >= 0 {
        let rhs = shl_limbs_exec(den, e_est as usize);
        if cmp_limbs_exec(num, &rhs) >= 0 { e_est } else { e_est - 1 }
    } else {
        let lhs = shl_limbs_exec(num, (-e_est) as usize);
        if cmp_limbs_exec(&lhs, den) >= 0 { e_est } else { e_est - 1 }
    };
    if e0 > 1023 {
        return if neg { js_neg_inf() } else { js_pos_inf() };
    }
    if e0 < -1075 {
        return if neg { js_neg_zero() } else { js_pos_zero() };
    }
    let is_sub = e0 < -1022;
    let s: i64 = if is_sub { 1074i64 } else { 52i64 - e0 };
    let (s_num, s_den) = if s >= 0 {
        (shl_limbs_exec(num, s as usize), den.clone())
    } else {
        (num.clone(), shl_limbs_exec(den, (-s) as usize))
    };
    if s_num.len() >= 512 || s_den.len() >= 512 {
        return if neg { js_neg_zero() } else { js_pos_zero() };
    }
    let (q, rem) = div_54_steps_exec(&s_num, &s_den);
    let twice_rem = shl_limbs_exec(&rem, 1);
    let cmp = cmp_limbs_exec(&twice_rem, &s_den);
    let round_up = cmp > 0 || (cmp == 0 && (q % 2u64) == 1u64);
    let q_rounded: u64 = if round_up { q + 1 } else { q };
    if is_sub {
        if q_rounded >= 0x0010_0000_0000_0000u64 {
            pack_ieee754(neg, 1u64, 0u64)
        } else {
            pack_ieee754(neg, 0u64, q_rounded)
        }
    } else {
        if q_rounded >= 0x0020_0000_0000_0000u64 {
            let next_e = e0 + 1;
            if next_e > 1023 {
                if neg { js_neg_inf() } else { js_pos_inf() }
            } else {
                pack_ieee754(neg, (next_e + 1023) as u64, 0u64)
            }
        } else if q_rounded < 0x0010_0000_0000_0000u64 {
            pack_ieee754(neg, 0u64, q_rounded)
        } else {
            let raw_e = (e0 + 1023) as u64;
            let raw_m = q_rounded - 0x0010_0000_0000_0000u64;
            pack_ieee754(neg, raw_e, raw_m)
        }
    }
}

/// Check if slice matches ASCII `"Infinity"`.
pub open spec fn spec_is_infinity_word(s: Seq<u16>) -> bool {
    s.len() == 8
        && s[0] == 0x49u16 && s[1] == 0x6Eu16 && s[2] == 0x66u16 && s[3] == 0x69u16
        && s[4] == 0x6Eu16 && s[5] == 0x69u16 && s[6] == 0x74u16 && s[7] == 0x79u16
}

fn is_infinity_word_exec(s: &Vec<u16>, a: usize, b: usize) -> (r: bool)
    requires a <= b, b <= s.len(),
    ensures r == spec_is_infinity_word(s@.subrange(a as int, b as int)),
{
    if b - a != 8 { return false; }
    s[a] == 0x49u16 && s[a + 1] == 0x6Eu16 && s[a + 2] == 0x66u16 && s[a + 3] == 0x69u16
        && s[a + 4] == 0x6Eu16 && s[a + 5] == 0x69u16 && s[a + 6] == 0x74u16 && s[a + 7] == 0x79u16
}

/// Parse decimal exponent digits into an exact mathematical `int` (unclamped in spec).
pub open spec fn spec_parse_exp_digits(s: Seq<u16>, idx: nat, acc: int) -> Option<int>
    decreases s.len() - idx,
{
    if idx >= s.len() {
        Some(acc)
    } else {
        match spec_digit_val(s[idx as int], 10) {
            None => None,
            Some(d) => spec_parse_exp_digits(s, idx + 1, acc * 10 + (d as int)),
        }
    }
}

fn parse_exp_digits_exec(s: &Vec<u16>, start: usize, end: usize, cap: i128) -> (r: Option<i128>)
    requires
        start <= end,
        end <= s.len(),
        0 < cap,
        cap <= (u64::MAX as i128) + 10000i128,
    ensures
        (r is None) <==> (spec_parse_exp_digits(s@.subrange(start as int, end as int), 0, 0) is None),
        match r {
            None => true,
            Some(v) => {
                let sp = spec_parse_exp_digits(s@.subrange(start as int, end as int), 0, 0).unwrap();
                0 <= v
                    && v <= 10i128 * cap + 9i128
                    && (sp < (cap as int) ==> (v as int) == sp)
                    && (sp >= (cap as int) ==> v >= cap)
            }
        },
{
    let ghost slice = s@.subrange(start as int, end as int);
    let len = end - start;
    let mut k: usize = 0;
    let mut acc: i128 = 0;
    let ghost mut spec_acc: int = 0;
    while k < len
        invariant
            0 <= k <= len,
            start + len == end,
            end <= s.len(),
            0 < cap,
            cap <= (u64::MAX as i128) + 10000i128,
            0 <= spec_acc,
            0 <= acc <= 10i128 * cap + 9i128,
            spec_acc < (cap as int) ==> (acc as int) == spec_acc,
            spec_acc >= (cap as int) ==> acc >= cap,
            slice =~= s@.subrange(start as int, end as int),
            spec_parse_exp_digits(slice, 0, 0) == spec_parse_exp_digits(slice, k as nat, spec_acc),
        decreases len - k,
    {
        let cu = s[start + k];
        proof { assert(cu == slice[k as int]); }
        match digit_val(cu, 10) {
            None => { return None; }
            Some(d) => {
                acc = if acc >= cap { cap } else { acc * 10i128 + (d as i128) };
                proof {
                    spec_acc = spec_acc * 10 + (d as int);
                }
                k = k + 1;
            }
        }
    }
    Some(acc)
}

/// Parse decimal mantissa + fractional digits (capping significant digits at 780 with sticky
/// non-zero bit, with exact unclamped `frac_adjust`).
pub struct DecMantissa {
    pub limbs: Vec<u32>,
    pub frac_adjust: i128,
    pub saw_digit: bool,
    pub saw_dot: bool,
    pub end_rel: usize,
}

pub struct SpecDecMantissa {
    pub limbs: Seq<u32>,
    pub frac_adjust: int,
    pub saw_digit: bool,
    pub saw_dot: bool,
    pub end_rel: nat,
}

pub open spec fn spec_scan_dec_mantissa(
    s: Seq<u16>,
    idx: nat,
    limbs: Seq<u32>,
    sig_digits: nat,
    frac_adjust: int,
    saw_digit: bool,
    saw_dot: bool,
) -> Option<SpecDecMantissa>
    decreases s.len() - idx,
{
    if idx >= s.len() {
        Some(SpecDecMantissa { limbs, frac_adjust, saw_digit, saw_dot, end_rel: idx })
    } else {
        let cu = s[idx as int];
        if cu == 0x65u16 || cu == 0x45u16 {
            Some(SpecDecMantissa { limbs, frac_adjust, saw_digit, saw_dot, end_rel: idx })
        } else if cu == 0x2Eu16 {
            if saw_dot {
                None
            } else {
                spec_scan_dec_mantissa(s, idx + 1, limbs, sig_digits, frac_adjust, saw_digit, true)
            }
        } else {
            match spec_digit_val(cu, 10) {
                None => None,
                Some(d) => {
                    if limbs.len() == 0 && d == 0 {
                        let next_fa = if saw_dot { frac_adjust - 1 } else { frac_adjust };
                        spec_scan_dec_mantissa(s, idx + 1, limbs, 0, next_fa, true, saw_dot)
                    } else if sig_digits < 780 {
                        let next_limbs = spec_limbs_mul_add_step(limbs, 0, 10, d as u64);
                        let next_fa = if saw_dot { frac_adjust - 1 } else { frac_adjust };
                        spec_scan_dec_mantissa(s, idx + 1, next_limbs, sig_digits + 1, next_fa, true, saw_dot)
                    } else {
                        let next_limbs = if d != 0 && limbs.len() > 0 && (limbs[0] % 2u32) == 0u32 {
                            limbs.update(0, (limbs[0] + 1) as u32)
                        } else {
                            limbs
                        };
                        let next_fa = if saw_dot { frac_adjust } else { frac_adjust + 1 };
                        spec_scan_dec_mantissa(s, idx + 1, next_limbs, sig_digits, next_fa, true, saw_dot)
                    }
                }
            }
        }
    }
}

proof fn lemma_mul10_len_bound(limbs: Seq<u32>, idx: nat, carry: u64)
    requires idx <= limbs.len(), carry < 10u64,
    ensures
        spec_limbs_mul_add_step(limbs, idx, 10, carry).len() <= (limbs.len() - idx) + 1,
    decreases limbs.len() - idx,
{
    if idx < limbs.len() {
        let lv: u64 = limbs[idx as int] as u64;
        assert(lv * 10u64 + carry <= 0xFFFF_FFFFu64 * 10u64 + 9u64) by (nonlinear_arith)
            requires lv <= 0xFFFF_FFFFu64, carry < 10u64;
        let cur: u64 = (lv * 10u64 + carry) as u64;
        let next_carry: u64 = cur / 0x1_0000_0000u64;
        lemma_mul10_len_bound(limbs, idx + 1, next_carry);
    }
}

proof fn lemma_mul_pow10_len_bound(a: Seq<u32>, k: nat)
    ensures spec_mul_pow10_limbs(a, k).len() <= a.len() + k,
    decreases k,
{
    if k > 0 {
        lemma_mul10_len_bound(a, 0, 0);
        lemma_mul_pow10_len_bound(spec_limbs_mul_add_step(a, 0, 10, 0), (k - 1) as nat);
    }
}

proof fn lemma_mul10_preserves_nonempty(limbs: Seq<u32>, d: u32)
    requires limbs.len() > 0 || d > 0,
    ensures spec_limbs_mul_add_step(limbs, 0, 10, d as u64).len() > 0,
{
    if limbs.len() == 0 {
        assert(d > 0);
    }
}

proof fn lemma_mul_pow10_nonempty(a: Seq<u32>, k: nat)
    requires a.len() > 0,
    ensures spec_mul_pow10_limbs(a, k).len() > 0,
    decreases k,
{
    if k > 0 {
        lemma_mul10_preserves_nonempty(a, 0);
        lemma_mul_pow10_nonempty(spec_limbs_mul_add_step(a, 0, 10, 0), (k - 1) as nat);
    }
}

fn scan_dec_mantissa_exec(s: &Vec<u16>, start: usize, end: usize) -> (r: Option<DecMantissa>)
    requires start <= end, end <= s.len(),
    ensures
        match r {
            None => spec_scan_dec_mantissa(s@.subrange(start as int, end as int), 0, Seq::empty(), 0, 0, false, false) is None,
            Some(dm) => {
                let sp = spec_scan_dec_mantissa(s@.subrange(start as int, end as int), 0, Seq::empty(), 0, 0, false, false);
                sp is Some
                    && dm.limbs@ =~= sp.unwrap().limbs
                    && (dm.frac_adjust as int) == sp.unwrap().frac_adjust
                    && dm.saw_digit == sp.unwrap().saw_digit
                    && dm.saw_dot == sp.unwrap().saw_dot
                    && dm.end_rel as nat == sp.unwrap().end_rel
                    && dm.end_rel <= end - start
                    && dm.limbs.len() <= 780
                    && -((end - start) as i128) <= dm.frac_adjust
                    && dm.frac_adjust <= ((end - start) as i128)
            }
        },
{
    let ghost slice = s@.subrange(start as int, end as int);
    let len = end - start;
    let mut k: usize = 0;
    let mut limbs: Vec<u32> = Vec::new();
    let mut sig_digits: usize = 0;
    let mut frac_adjust: i128 = 0;
    let mut saw_digit = false;
    let mut saw_dot = false;
    while k < len
        invariant
            0 <= k <= len,
            start + len == end,
            end <= s.len(),
            sig_digits <= 780,
            limbs.len() <= sig_digits,
            limbs.len() == 0 ==> sig_digits == 0,
            -(k as i128) <= frac_adjust && frac_adjust <= (k as i128),
            slice =~= s@.subrange(start as int, end as int),
            spec_scan_dec_mantissa(slice, 0, Seq::empty(), 0, 0, false, false)
                == spec_scan_dec_mantissa(slice, k as nat, limbs@, sig_digits as nat, frac_adjust as int, saw_digit, saw_dot),
        decreases len - k,
    {
        let cu = s[start + k];
        proof { assert(cu == slice[k as int]); }
        if cu == 0x65u16 || cu == 0x45u16 {
            return Some(DecMantissa { limbs, frac_adjust, saw_digit, saw_dot, end_rel: k });
        } else if cu == 0x2Eu16 {
            if saw_dot {
                return None;
            }
            saw_dot = true;
            k = k + 1;
        } else {
            match digit_val(cu, 10) {
                None => { return None; }
                Some(d) => {
                    if limbs.len() == 0 && d == 0 {
                        if saw_dot {
                            frac_adjust = frac_adjust - 1;
                        }
                        saw_digit = true;
                        k = k + 1;
                    } else if sig_digits < 780 {
                        proof {
                            lemma_mul10_len_bound(limbs@, 0, d as u64);
                            lemma_mul10_preserves_nonempty(limbs@, d);
                        }
                        limbs = limbs_mul_add_exec(&limbs, 10, d);
                        sig_digits = sig_digits + 1;
                        if saw_dot {
                            frac_adjust = frac_adjust - 1;
                        }
                        saw_digit = true;
                        k = k + 1;
                    } else {
                        if d != 0 && limbs.len() > 0 && (limbs[0] % 2u32) == 0u32 {
                            let v0 = limbs[0];
                            proof {
                                // Since v0 is even, v0 <= 0xFFFF_FFFE, so v0 + 1 fits in u32!
                                assert((v0 % 2u32) == 0u32 ==> v0 < 0xFFFF_FFFFu32) by (bit_vector);
                            }
                            limbs.set(0, v0 + 1);
                        }
                        if !saw_dot {
                            frac_adjust = frac_adjust + 1;
                        }
                        saw_digit = true;
                        k = k + 1;
                    }
                }
            }
        }
    }
    Some(DecMantissa { limbs, frac_adjust, saw_digit, saw_dot, end_rel: k })
}

pub open spec fn spec_dec_body_to_number(body: Seq<u16>, neg: bool) -> JsNumber {
    if body.len() == 0 {
        spec_canon_nan()
    } else if spec_is_infinity_word(body) {
        if neg { spec_neg_inf() } else { spec_pos_inf() }
    } else {
        match spec_scan_dec_mantissa(body, 0, Seq::empty(), 0, 0, false, false) {
            None => spec_canon_nan(),
            Some(dm) => {
                if !dm.saw_digit {
                    spec_canon_nan()
                } else {
                    let exp_opt: Option<int> = if dm.end_rel < body.len() {
                        let after_e = body.subrange((dm.end_rel + 1) as int, body.len() as int);
                        if after_e.len() == 0 {
                            None
                        } else {
                            let exp_neg = after_e[0] == 0x2Du16;
                            let exp_sign = after_e[0] == 0x2Du16 || after_e[0] == 0x2Bu16;
                            let exp_digits = if exp_sign { after_e.subrange(1, after_e.len() as int) } else { after_e };
                            if exp_digits.len() == 0 {
                                None
                            } else {
                                match spec_parse_exp_digits(exp_digits, 0, 0) {
                                    None => None,
                                    Some(ev) => Some(if exp_neg { -ev + dm.frac_adjust } else { ev + dm.frac_adjust }),
                                }
                            }
                        }
                    } else {
                        Some(dm.frac_adjust)
                    };
                    match exp_opt {
                        None => spec_canon_nan(),
                        Some(exp10) => {
                            if dm.limbs.len() == 0 {
                                if neg { spec_neg_zero() } else { spec_pos_zero() }
                            } else if exp10 > 320int {
                                if neg { spec_neg_inf() } else { spec_pos_inf() }
                            } else if exp10 < -1120int {
                                if neg { spec_neg_zero() } else { spec_pos_zero() }
                            } else if exp10 >= 0int {
                                let num = spec_mul_pow10_limbs(dm.limbs, exp10 as nat);
                                let den = seq![1u32];
                                if num.len() >= 400 {
                                    if neg { spec_neg_inf() } else { spec_pos_inf() }
                                } else {
                                    spec_round_rational_to_f64(neg, num, den)
                                }
                            } else {
                                let num = dm.limbs;
                                let den = spec_mul_pow10_limbs(seq![1u32], (-exp10) as nat);
                                if num.len() >= 400 || den.len() >= 400 {
                                    if neg { spec_neg_zero() } else { spec_pos_zero() }
                                } else {
                                    spec_round_rational_to_f64(neg, num, den)
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

/// ECMA-262 §7.1.4.1.1 `StringToNumber ( string )`: exact verified implementation.
pub open spec fn spec_string_to_number_trimmed(t: Seq<u16>) -> JsNumber {
    if t.len() == 0 {
        spec_pos_zero()
    } else if t.len() >= 2 && t[0] == 0x30u16 && (t[1] == 0x78u16 || t[1] == 0x58u16) {
        if t.len() == 2 {
            spec_canon_nan()
        } else {
            match spec_parse_radix_limbs(t.subrange(2, t.len() as int), 0, 16, Seq::empty()) {
                None => spec_canon_nan(),
                Some(limbs) => {
                    if limbs.len() == 0 {
                        spec_pos_zero()
                    } else if limbs.len() >= 35 {
                        spec_pos_inf()
                    } else {
                        spec_round_rational_to_f64(false, limbs, seq![1u32])
                    }
                }
            }
        }
    } else if t.len() >= 2 && t[0] == 0x30u16 && (t[1] == 0x62u16 || t[1] == 0x42u16) {
        if t.len() == 2 {
            spec_canon_nan()
        } else {
            match spec_parse_radix_limbs(t.subrange(2, t.len() as int), 0, 2, Seq::empty()) {
                None => spec_canon_nan(),
                Some(limbs) => {
                    if limbs.len() == 0 {
                        spec_pos_zero()
                    } else if limbs.len() >= 35 {
                        spec_pos_inf()
                    } else {
                        spec_round_rational_to_f64(false, limbs, seq![1u32])
                    }
                }
            }
        }
    } else if t.len() >= 2 && t[0] == 0x30u16 && (t[1] == 0x6Fu16 || t[1] == 0x4Fu16) {
        if t.len() == 2 {
            spec_canon_nan()
        } else {
            match spec_parse_radix_limbs(t.subrange(2, t.len() as int), 0, 8, Seq::empty()) {
                None => spec_canon_nan(),
                Some(limbs) => {
                    if limbs.len() == 0 {
                        spec_pos_zero()
                    } else if limbs.len() >= 35 {
                        spec_pos_inf()
                    } else {
                        spec_round_rational_to_f64(false, limbs, seq![1u32])
                    }
                }
            }
        }
    } else {
        let neg = t[0] == 0x2Du16;
        let has_sign = t[0] == 0x2Du16 || t[0] == 0x2Bu16;
        let body = if has_sign { t.subrange(1, t.len() as int) } else { t };
        spec_dec_body_to_number(body, neg)
    }
}

pub open spec fn spec_string_to_number_val(v: SpecJsValue) -> JsNumber {
    match v {
        SpecJsValue::Str(s) => spec_string_to_number_trimmed(spec_trim_utf16(s)),
        _ => spec_canon_nan(),
    }
}

#[verifier::spinoff_prover]
fn dec_body_to_number_exec(s: &Vec<u16>, body_start: usize, b: usize, neg: bool) -> (r: JsNumber)
    requires
        body_start <= b,
        b <= s.len(),
    ensures
        r == spec_dec_body_to_number(s@.subrange(body_start as int, b as int), neg),
{
    let ghost body = s@.subrange(body_start as int, b as int);
    if body_start == b {
        return js_canon_nan();
    }
    if is_infinity_word_exec(s, body_start, b) {
        return if neg { js_neg_inf() } else { js_pos_inf() };
    }
    match scan_dec_mantissa_exec(s, body_start, b) {
        None => js_canon_nan(),
        Some(dm) => {
            if !dm.saw_digit {
                return js_canon_nan();
            }
            let body_len = b - body_start;
            let cap: i128 = (body_len as i128) + 5000i128;
            let exp_opt: Option<i128> = if dm.end_rel < body_len {
                let e_after_start = body_start + dm.end_rel + 1;
                proof {
                    assert(body.subrange((dm.end_rel + 1) as int, body.len() as int)
                        =~= s@.subrange(e_after_start as int, b as int));
                }
                if e_after_start == b {
                    None
                } else {
                    let ec0 = s[e_after_start];
                    let exp_neg = ec0 == 0x2Du16;
                    let exp_sign = ec0 == 0x2Du16 || ec0 == 0x2Bu16;
                    let ed_start = if exp_sign { e_after_start + 1 } else { e_after_start };
                    let ghost after_e = body.subrange((dm.end_rel + 1) as int, body.len() as int);
                    let ghost exp_digits = if exp_sign { after_e.subrange(1, after_e.len() as int) } else { after_e };
                    proof {
                        if exp_sign {
                            assert(exp_digits =~= s@.subrange(ed_start as int, b as int));
                        } else {
                            assert(exp_digits =~= s@.subrange(ed_start as int, b as int));
                        }
                    }
                    if ed_start == b {
                        None
                    } else {
                        match parse_exp_digits_exec(s, ed_start, b, cap) {
                            None => None,
                            Some(ev) => {
                                proof {
                                    let sp_ev = spec_parse_exp_digits(exp_digits, 0, 0).unwrap();
                                    if sp_ev >= (cap as int) {
                                        assert(ev >= cap);
                                        if exp_neg {
                                            assert(-sp_ev + (dm.frac_adjust as int) <= -5000int);
                                            assert(-ev + dm.frac_adjust <= -5000i128);
                                        } else {
                                            assert(sp_ev + (dm.frac_adjust as int) >= 5000int);
                                            assert(ev + dm.frac_adjust >= 5000i128);
                                        }
                                    }
                                }
                                if exp_neg {
                                    Some(-ev + dm.frac_adjust)
                                } else {
                                    Some(ev + dm.frac_adjust)
                                }
                            }
                        }
                    }
                }
            } else {
                Some(dm.frac_adjust)
            };
            match exp_opt {
                None => js_canon_nan(),
                Some(exp10) => {
                    if dm.limbs.len() == 0 {
                        if neg { js_neg_zero() } else { js_pos_zero() }
                    } else if exp10 > 320i128 {
                        if neg { js_neg_inf() } else { js_pos_inf() }
                    } else if exp10 < -1120i128 {
                        if neg { js_neg_zero() } else { js_pos_zero() }
                    } else if exp10 >= 0i128 {
                        let num = mul_pow10_limbs_exec(dm.limbs, exp10 as u32);
                        let mut den: Vec<u32> = Vec::new();
                        den.push(1u32);
                        proof {
                            assert(den@ =~= seq![1u32]);
                            lemma_mul_pow10_nonempty(dm.limbs@, exp10 as nat);
                        }
                        if num.len() >= 400 {
                            if neg { js_neg_inf() } else { js_pos_inf() }
                        } else {
                            round_rational_to_f64_exec(neg, &num, &den)
                        }
                    } else {
                        let num = dm.limbs;
                        let mut one_vec: Vec<u32> = Vec::new();
                        one_vec.push(1u32);
                        proof { assert(one_vec@ =~= seq![1u32]); }
                        let den = mul_pow10_limbs_exec(one_vec, (-exp10) as u32);
                        proof {
                            lemma_mul_pow10_nonempty(seq![1u32], (-exp10) as nat);
                        }
                        if num.len() >= 400 || den.len() >= 400 {
                            if neg { js_neg_zero() } else { js_pos_zero() }
                        } else {
                            round_rational_to_f64_exec(neg, &num, &den)
                        }
                    }
                }
            }
        }
    }
}

#[verifier::spinoff_prover]
pub fn val_string_to_number(v: &JsValue) -> (r: JsNumber)
    requires spec_is_string(v@),
    ensures r == spec_string_to_number_val(v@),
{
    match v {
        JsValue::Str(s) => {
            let (a, b) = trim_bounds_utf16(s);
            let ghost t = s@.subrange(a as int, b as int);
            let len = b - a;
            if len == 0 {
                return js_pos_zero();
            }
            if len >= 2 && s[a] == 0x30u16 && (s[a + 1] == 0x78u16 || s[a + 1] == 0x58u16) {
                if len == 2 { return js_canon_nan(); }
                proof { assert(t.subrange(2, t.len() as int) =~= s@.subrange((a + 2) as int, b as int)); }
                return match parse_radix_limbs_exec(s, a + 2, b, 16) {
                    None => js_canon_nan(),
                    Some(limbs) => {
                        if limbs.len() == 0 {
                            js_pos_zero()
                        } else if limbs.len() >= 35 {
                            js_pos_inf()
                        } else {
                            let mut den: Vec<u32> = Vec::new();
                            den.push(1u32);
                            proof { assert(den@ =~= seq![1u32]); }
                            round_rational_to_f64_exec(false, &limbs, &den)
                        }
                    }
                };
            }
            if len >= 2 && s[a] == 0x30u16 && (s[a + 1] == 0x62u16 || s[a + 1] == 0x42u16) {
                if len == 2 { return js_canon_nan(); }
                proof { assert(t.subrange(2, t.len() as int) =~= s@.subrange((a + 2) as int, b as int)); }
                return match parse_radix_limbs_exec(s, a + 2, b, 2) {
                    None => js_canon_nan(),
                    Some(limbs) => {
                        if limbs.len() == 0 {
                            js_pos_zero()
                        } else if limbs.len() >= 35 {
                            js_pos_inf()
                        } else {
                            let mut den: Vec<u32> = Vec::new();
                            den.push(1u32);
                            proof { assert(den@ =~= seq![1u32]); }
                            round_rational_to_f64_exec(false, &limbs, &den)
                        }
                    }
                };
            }
            if len >= 2 && s[a] == 0x30u16 && (s[a + 1] == 0x6Fu16 || s[a + 1] == 0x4Fu16) {
                if len == 2 { return js_canon_nan(); }
                proof { assert(t.subrange(2, t.len() as int) =~= s@.subrange((a + 2) as int, b as int)); }
                return match parse_radix_limbs_exec(s, a + 2, b, 8) {
                    None => js_canon_nan(),
                    Some(limbs) => {
                        if limbs.len() == 0 {
                            js_pos_zero()
                        } else if limbs.len() >= 35 {
                            js_pos_inf()
                        } else {
                            let mut den: Vec<u32> = Vec::new();
                            den.push(1u32);
                            proof { assert(den@ =~= seq![1u32]); }
                            round_rational_to_f64_exec(false, &limbs, &den)
                        }
                    }
                };
            }
            let c0 = s[a];
            let neg = c0 == 0x2Du16;
            let has_sign = c0 == 0x2Du16 || c0 == 0x2Bu16;
            let body_start = if has_sign { a + 1 } else { a };
            let ghost body = if has_sign { t.subrange(1, t.len() as int) } else { t };
            proof {
                if has_sign {
                    assert(body =~= s@.subrange((a + 1) as int, b as int));
                } else {
                    assert(body =~= s@.subrange(a as int, b as int));
                }
            }
            dec_body_to_number_exec(s, body_start, b, neg)
        }
        _ => js_canon_nan(),
    }
}

// ===============================================================================================
// 8. Termination Ranks for Recursive ECMA-262 Abstract Operations (`ToNumber`, `IsLooselyEqual`)
// ===============================================================================================

pub open spec fn spec_tonumber_rank(v: SpecJsValue) -> nat {
    if spec_is_object(v) { 1nat } else { 0nat }
}

pub open spec fn spec_loose_type_weight(v: SpecJsValue) -> nat {
    if spec_is_object(v) {
        4nat
    } else if spec_is_boolean(v) {
        2nat
    } else if spec_is_string(v) {
        1nat
    } else {
        0nat
    }
}

pub open spec fn spec_loosely_equal_rank(x: SpecJsValue, y: SpecJsValue) -> nat {
    2nat * (spec_loose_type_weight(x) + spec_loose_type_weight(y))
        + (if spec_is_string(x) { 1nat } else { 0nat })
}

} // verus!
