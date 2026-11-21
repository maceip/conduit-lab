//! ECMAScript language primitive values, IEEE-754 binary64 numbers, UTF-16 strings,
//! and abstract type-conversion / comparison operations (§6.1, §7.1, §7.2).
use vstd::prelude::*;

verus! {

/// Heap object identifier (§6.1.7).
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct ObjId(pub usize);

/// IEEE-754 binary64 number represented by its exact 64-bit pattern (§6.1.6.1).
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct JsNum(pub u64);

/// UTF-16 string value (§6.1.4): sequence of 16-bit code units.
#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub struct JsStr(pub Vec<u16>);

impl View for JsStr {
    type V = Seq<u16>;

    open spec fn view(&self) -> Seq<u16> {
        self.0@
    }
}

/// ECMAScript language value (§6.1).
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Val {
    Undefined,
    Null,
    Bool(bool),
    Number(JsNum),
    Str(JsStr),
    Object(ObjId),
}

/// Ghost view of an ECMAScript value.
pub enum SpecVal {
    Undefined,
    Null,
    Bool(bool),
    Number(JsNum),
    Str(Seq<u16>),
    Object(ObjId),
}

impl View for Val {
    type V = SpecVal;

    open spec fn view(&self) -> SpecVal {
        match self {
            Val::Undefined => SpecVal::Undefined,
            Val::Null => SpecVal::Null,
            Val::Bool(b) => SpecVal::Bool(*b),
            Val::Number(n) => SpecVal::Number(*n),
            Val::Str(s) => SpecVal::Str(s@),
            Val::Object(id) => SpecVal::Object(*id),
        }
    }
}

pub fn clone_js_str(s: &JsStr) -> (r: JsStr)
    ensures r@ == s@,
{
    let n = s.0.len();
    let mut out: Vec<u16> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n == s@.len(),
            out@ =~= s@.subrange(0, i as int),
        decreases n - i,
    {
        out.push(s.0[i]);
        i += 1;
    }
    proof { assert(s@.subrange(0, n as int) =~= s@); }
    JsStr(out)
}

pub fn clone_val(v: &Val) -> (r: Val)
    ensures r@ == v@,
{
    match v {
        Val::Undefined => Val::Undefined,
        Val::Null => Val::Null,
        Val::Bool(b) => Val::Bool(*b),
        Val::Number(n) => Val::Number(*n),
        Val::Str(s) => Val::Str(clone_js_str(s)),
        Val::Object(id) => Val::Object(*id),
    }
}

// ---------------------------------------------------------------------------
// IEEE-754 binary64 constants & bit-level helpers (pure integer math)
// ---------------------------------------------------------------------------

pub const POS_ZERO_BITS: u64 = 0x0000_0000_0000_0000;
pub const NEG_ZERO_BITS: u64 = 0x8000_0000_0000_0000;
pub const ONE_BITS: u64 = 0x3ff0_0000_0000_0000;
pub const NEG_ONE_BITS: u64 = 0xbff0_0000_0000_0000;
pub const POS_INF_BITS: u64 = 0x7ff0_0000_0000_0000;
pub const NEG_INF_BITS: u64 = 0xfff0_0000_0000_0000;
pub const NAN_BITS: u64 = 0x7ff8_0000_0000_0000;
pub const MANT_MOD: u64 = 0x0010_0000_0000_0000; // 2^52

impl JsNum {
    pub fn pos_zero() -> (r: Self)
        ensures r == JsNum(POS_ZERO_BITS),
    {
        JsNum(POS_ZERO_BITS)
    }

    pub fn neg_zero() -> (r: Self)
        ensures r == JsNum(NEG_ZERO_BITS),
    {
        JsNum(NEG_ZERO_BITS)
    }

    pub fn one() -> (r: Self)
        ensures r == JsNum(ONE_BITS),
    {
        JsNum(ONE_BITS)
    }

    pub fn nan() -> (r: Self)
        ensures r == JsNum(NAN_BITS),
    {
        JsNum(NAN_BITS)
    }

    pub fn pos_inf() -> (r: Self)
        ensures r == JsNum(POS_INF_BITS),
    {
        JsNum(POS_INF_BITS)
    }

    pub fn neg_inf() -> (r: Self)
        ensures r == JsNum(NEG_INF_BITS),
    {
        JsNum(NEG_INF_BITS)
    }
}

pub open spec fn spec_unpack_f64(n: JsNum) -> (bool, u16, u64) {
    let b = n.0;
    let neg = b >= NEG_ZERO_BITS;
    let abs_b: u64 = if neg { (b - NEG_ZERO_BITS) as u64 } else { b };
    let exp = (abs_b / MANT_MOD) as u16;
    let frac = abs_b % MANT_MOD;
    (neg, exp, frac)
}

pub fn unpack_f64(n: JsNum) -> (r: (bool, u16, u64))
    ensures
        r == spec_unpack_f64(n),
        r.1 <= 2047,
        r.2 < MANT_MOD,
{
    let b = n.0;
    let neg = b >= NEG_ZERO_BITS;
    let abs_b: u64 = if neg { b - NEG_ZERO_BITS } else { b };
    let exp = (abs_b / MANT_MOD) as u16;
    let frac = abs_b % MANT_MOD;
    (neg, exp, frac)
}

pub open spec fn spec_pack_f64(neg: bool, exp: u16, frac: u64) -> JsNum {
    let sign_part: u64 = if neg { NEG_ZERO_BITS } else { 0u64 };
    JsNum((sign_part + (exp as u64) * MANT_MOD + frac) as u64)
}

pub fn pack_f64(neg: bool, exp: u16, frac: u64) -> (r: JsNum)
    requires
        exp <= 2047,
        frac < MANT_MOD,
    ensures
        r == spec_pack_f64(neg, exp, frac),
{
    let sign_part: u64 = if neg { NEG_ZERO_BITS } else { 0u64 };
    JsNum(sign_part + (exp as u64) * MANT_MOD + frac)
}

pub open spec fn spec_is_nan(n: JsNum) -> bool {
    let (_, exp, frac) = spec_unpack_f64(n);
    exp == 2047 && frac != 0
}

pub fn num_is_nan(n: JsNum) -> (r: bool)
    ensures r == spec_is_nan(n),
{
    let (_, exp, frac) = unpack_f64(n);
    exp == 2047 && frac != 0
}

pub open spec fn spec_is_zero(n: JsNum) -> bool {
    let (_, exp, frac) = spec_unpack_f64(n);
    exp == 0 && frac == 0
}

pub fn num_is_zero(n: JsNum) -> (r: bool)
    ensures r == spec_is_zero(n),
{
    let (_, exp, frac) = unpack_f64(n);
    exp == 0 && frac == 0
}

pub open spec fn spec_is_infinite(n: JsNum) -> bool {
    let (_, exp, frac) = spec_unpack_f64(n);
    exp == 2047 && frac == 0
}

pub fn num_is_infinite(n: JsNum) -> (r: bool)
    ensures r == spec_is_infinite(n),
{
    let (_, exp, frac) = unpack_f64(n);
    exp == 2047 && frac == 0
}

pub open spec fn spec_is_finite(n: JsNum) -> bool {
    let (_, exp, _) = spec_unpack_f64(n);
    exp < 2047
}

pub fn num_is_finite(n: JsNum) -> (r: bool)
    ensures r == spec_is_finite(n),
{
    let (_, exp, _) = unpack_f64(n);
    exp < 2047
}

/// §6.1.6.1.1 Number::unaryMinus ( x )
pub open spec fn spec_num_neg(n: JsNum) -> JsNum {
    if spec_is_nan(n) {
        JsNum(NAN_BITS)
    } else {
        let (neg, exp, frac) = spec_unpack_f64(n);
        spec_pack_f64(!neg, exp, frac)
    }
}

pub fn num_neg(n: JsNum) -> (r: JsNum)
    ensures r == spec_num_neg(n),
{
    if num_is_nan(n) {
        JsNum(NAN_BITS)
    } else {
        let (neg, exp, frac) = unpack_f64(n);
        pack_f64(!neg, exp, frac)
    }
}

// ---------------------------------------------------------------------------
// Normalization & Round-to-Nearest-Even Packing
// ---------------------------------------------------------------------------

pub open spec fn spec_norm_subnormal_loop(sig: u64, e2: i32, steps: nat) -> (i32, u64)
    decreases steps,
{
    if steps == 0 || sig >= MANT_MOD {
        if sig < MANT_MOD { (e2, MANT_MOD) } else { (e2, sig) }
    } else {
        spec_norm_subnormal_loop((sig * 2) as u64, (e2 - 1) as i32, (steps - 1) as nat)
    }
}

fn norm_subnormal_loop(sig: u64, e2: i32, steps: usize) -> (r: (i32, u64))
    requires
        0 < sig < 2 * MANT_MOD,
        steps <= 52,
        -1074 <= e2 - (steps as int) && e2 <= -1022,
    ensures
        r == spec_norm_subnormal_loop(sig, e2, steps as nat),
        -1074 <= r.0 <= -1022,
        MANT_MOD <= r.1 < 2 * MANT_MOD,
{
    let mut cs = sig;
    let mut ce = e2;
    let mut rem = steps;
    while rem > 0 && cs < MANT_MOD
        invariant
            0 < cs < 2 * MANT_MOD,
            rem <= steps <= 52,
            -1074 <= ce - (rem as int) && ce <= -1022,
            spec_norm_subnormal_loop(sig, e2, steps as nat)
                == spec_norm_subnormal_loop(cs, ce, rem as nat),
        decreases rem,
    {
        cs = cs * 2;
        ce = ce - 1;
        rem = rem - 1;
    }
    if cs < MANT_MOD { (ce, MANT_MOD) } else { (ce, cs) }
}

pub open spec fn spec_normalize_finite(exp: u16, frac: u64) -> (i32, u64) {
    if exp > 0 {
        (((exp as i32) - 1023) as i32, (MANT_MOD + frac) as u64)
    } else {
        spec_norm_subnormal_loop(frac, -1022i32, 52nat)
    }
}

pub fn normalize_finite(exp: u16, frac: u64) -> (r: (i32, u64))
    requires
        exp < 2047,
        frac < MANT_MOD,
        exp > 0 || frac > 0,
    ensures
        r == spec_normalize_finite(exp, frac),
        -1074 <= r.0 <= 1023,
        MANT_MOD <= r.1 < 2 * MANT_MOD,
{
    if exp > 0 {
        ((exp as i32) - 1023, MANT_MOD + frac)
    } else {
        norm_subnormal_loop(frac, -1022, 52)
    }
}

pub const SIG_GRS_LOW: u128 = 0x0080_0000_0000_0000u128;  // 2^55
pub const SIG_GRS_HIGH: u128 = 0x0100_0000_0000_0000u128; // 2^56
pub const SIG_MAX_BOUND: u128 = 0x0004_0000_0000_0000_0000_0000_0000_0000u128; // 2^114

pub open spec fn spec_shr_sticky_one(sig: u128) -> u128 {
    let rem = sig % 2u128;
    let half = sig / 2u128;
    if rem == 1u128 && half % 2u128 == 0u128 {
        (half + 1u128) as u128
    } else {
        half
    }
}

fn shr_sticky_one(sig: u128) -> (r: u128)
    requires sig <= SIG_MAX_BOUND,
    ensures
        r == spec_shr_sticky_one(sig),
        r <= sig / 2u128 + 1u128,
        r <= SIG_MAX_BOUND,
        sig < SIG_GRS_HIGH ==> r < SIG_GRS_HIGH,
        sig > 0u128 ==> r > 0u128,
{
    let rem = sig % 2u128;
    let half = sig / 2u128;
    if rem == 1u128 && half % 2u128 == 0u128 {
        half + 1u128
    } else {
        half
    }
}

pub open spec fn spec_shr_until_56(e2: i32, sig: u128, steps: nat) -> (i32, u128)
    decreases steps,
{
    if steps == 0 || sig < SIG_GRS_HIGH {
        if sig >= SIG_GRS_HIGH { (e2, (SIG_GRS_HIGH - 1u128) as u128) } else { (e2, sig) }
    } else {
        spec_shr_until_56((e2 + 1) as i32, spec_shr_sticky_one(sig), (steps - 1) as nat)
    }
}

fn shr_until_56(e2: i32, sig: u128, steps: usize) -> (r: (i32, u128))
    requires
        0 < sig <= SIG_MAX_BOUND,
        steps <= 64,
        -5000 <= e2,
        e2 + (steps as int) <= 5064,
    ensures
        r == spec_shr_until_56(e2, sig, steps as nat),
        0 < r.1 < SIG_GRS_HIGH,
        -5000 <= r.0 <= 5064,
{
    let mut ce = e2;
    let mut cs = sig;
    let mut rem = steps;
    while rem > 0 && cs >= SIG_GRS_HIGH
        invariant
            0 < cs <= SIG_MAX_BOUND,
            rem <= steps <= 64,
            -5000 <= ce,
            ce + (rem as int) <= 5064,
            spec_shr_until_56(e2, sig, steps as nat) == spec_shr_until_56(ce, cs, rem as nat),
        decreases rem,
    {
        cs = shr_sticky_one(cs);
        ce = ce + 1;
        rem = rem - 1;
    }
    if cs >= SIG_GRS_HIGH { (ce, SIG_GRS_HIGH - 1u128) } else { (ce, cs) }
}

pub open spec fn spec_shl_until_55(e2: i32, sig: u128, steps: nat) -> (i32, u128)
    decreases steps,
{
    if steps == 0 || sig >= SIG_GRS_LOW || e2 <= -1022i32 {
        (e2, sig)
    } else {
        spec_shl_until_55((e2 - 1) as i32, (sig * 2u128) as u128, (steps - 1) as nat)
    }
}

fn shl_until_55(e2: i32, sig: u128, steps: usize) -> (r: (i32, u128))
    requires
        0 < sig < SIG_GRS_HIGH,
        steps <= 64,
        -5000 <= e2 <= 5100,
    ensures
        r == spec_shl_until_55(e2, sig, steps as nat),
        0 < r.1 < SIG_GRS_HIGH,
        -5064 <= r.0 <= 5100,
{
    let mut ce = e2;
    let mut cs = sig;
    let mut rem = steps;
    while rem > 0 && cs < SIG_GRS_LOW && ce > -1022
        invariant
            0 < cs < SIG_GRS_HIGH,
            rem <= steps <= 64,
            -5064 <= ce - (rem as int),
            ce <= 5100,
            spec_shl_until_55(e2, sig, steps as nat) == spec_shl_until_55(ce, cs, rem as nat),
        decreases rem,
    {
        cs = cs * 2u128;
        ce = ce - 1;
        rem = rem - 1;
    }
    (ce, cs)
}

pub open spec fn spec_subnormal_align(e2: i32, sig: u128, steps: nat) -> (i32, u128)
    decreases steps,
{
    if steps == 0 || e2 >= -1022i32 {
        if e2 < -1022i32 { (-1022i32, 1u128) } else { (e2, sig) }
    } else {
        spec_subnormal_align((e2 + 1) as i32, spec_shr_sticky_one(sig), (steps - 1) as nat)
    }
}

fn subnormal_align(e2: i32, sig: u128, steps: usize) -> (r: (i32, u128))
    requires
        0 < sig < SIG_GRS_HIGH,
        steps <= 64,
        -5100 <= e2 <= 5100,
    ensures
        r == spec_subnormal_align(e2, sig, steps as nat),
        0 < r.1 < SIG_GRS_HIGH,
        -1022 <= r.0 <= 5164,
{
    let mut ce = e2;
    let mut cs = sig;
    let mut rem = steps;
    while rem > 0 && ce < -1022
        invariant
            0 < cs < SIG_GRS_HIGH,
            rem <= steps <= 64,
            -5100 <= ce,
            ce + (rem as int) <= 5164,
            spec_subnormal_align(e2, sig, steps as nat) == spec_subnormal_align(ce, cs, rem as nat),
        decreases rem,
    {
        cs = shr_sticky_one(cs);
        ce = ce + 1;
        rem = rem - 1;
    }
    if ce < -1022 { (-1022, 1u128) } else { (ce, cs) }
}

pub open spec fn spec_round_pack_grs(neg: bool, e2_in: i32, sig_in: u128) -> JsNum {
    if sig_in == 0u128 || e2_in < -1100i32 {
        spec_pack_f64(neg, 0u16, 0u64)
    } else if e2_in > 1100i32 {
        spec_pack_f64(neg, 2047u16, 0u64)
    } else {
        let (e_shr, s_shr) = spec_shr_until_56(e2_in, sig_in, 64nat);
        let (e_shl, s_shl) = spec_shl_until_55(e_shr, s_shr, 64nat);
        let (e_sub, s_sub) = spec_subnormal_align(e_shl, s_shl, 64nat);
        let main_raw: u64 = (s_sub / 8u128) as u64;
        let grs: u8 = (s_sub % 8u128) as u8;
        let guard = grs / 4u8;
        let rs = grs % 4u8;
        let main_rounded: u64 = if guard == 1u8 && (rs > 0u8 || main_raw % 2u64 == 1u64) {
            (main_raw + 1u64) as u64
        } else {
            main_raw
        };
        let (e_fin, m_fin): (i32, u64) = if main_rounded >= 2u64 * MANT_MOD {
            ((e_sub + 1) as i32, main_rounded / 2u64)
        } else {
            (e_sub, main_rounded)
        };
        if m_fin == 0u64 {
            spec_pack_f64(neg, 0u16, 0u64)
        } else if e_fin > 1023i32 {
            spec_pack_f64(neg, 2047u16, 0u64)
        } else if m_fin < MANT_MOD {
            spec_pack_f64(neg, 0u16, m_fin)
        } else {
            spec_pack_f64(neg, (e_fin + 1023i32) as u16, (m_fin - MANT_MOD) as u64)
        }
    }
}

pub fn round_pack_grs(neg: bool, e2_in: i32, sig_in: u128) -> (r: JsNum)
    requires
        sig_in <= SIG_MAX_BOUND,
        -1_000_000 <= e2_in <= 1_000_000,
    ensures
        r == spec_round_pack_grs(neg, e2_in, sig_in),
{
    if sig_in == 0u128 || e2_in < -1100 {
        pack_f64(neg, 0, 0)
    } else if e2_in > 1100 {
        pack_f64(neg, 2047, 0)
    } else {
        let (e_shr, s_shr) = shr_until_56(e2_in, sig_in, 64);
        let (e_shl, s_shl) = shl_until_55(e_shr, s_shr, 64);
        let (e_sub, s_sub) = subnormal_align(e_shl, s_shl, 64);
        let main_raw: u64 = (s_sub / 8u128) as u64;
        let grs: u8 = (s_sub % 8u128) as u8;
        let guard = grs / 4u8;
        let rs = grs % 4u8;
        let main_rounded: u64 = if guard == 1u8 && (rs > 0u8 || main_raw % 2u64 == 1u64) {
            main_raw + 1u64
        } else {
            main_raw
        };
        let (e_fin, m_fin): (i32, u64) = if main_rounded >= 2u64 * MANT_MOD {
            (e_sub + 1, main_rounded / 2u64)
        } else {
            (e_sub, main_rounded)
        };
        if m_fin == 0u64 {
            pack_f64(neg, 0, 0)
        } else if e_fin > 1023 {
            pack_f64(neg, 2047, 0)
        } else if m_fin < MANT_MOD {
            pack_f64(neg, 0, m_fin)
        } else {
            pack_f64(neg, (e_fin + 1023) as u16, m_fin - MANT_MOD)
        }
    }
}

pub open spec fn spec_num_from_i64(v: i64) -> JsNum {
    if v == 0i64 {
        JsNum(POS_ZERO_BITS)
    } else {
        let neg = v < 0i64;
        let mag: u64 = if v == i64::MIN {
            0x8000_0000_0000_0000u64
        } else if v < 0i64 {
            (-v) as u64
        } else {
            v as u64
        };
        spec_round_pack_grs(neg, 52i32, ((mag as u128) * 8u128) as u128)
    }
}

pub fn num_from_i64(v: i64) -> (r: JsNum)
    ensures r == spec_num_from_i64(v),
{
    if v == 0i64 {
        JsNum(POS_ZERO_BITS)
    } else {
        let neg = v < 0i64;
        let mag: u64 = if v == i64::MIN {
            0x8000_0000_0000_0000u64
        } else if v < 0i64 {
            (-v) as u64
        } else {
            v as u64
        };
        round_pack_grs(neg, 52, (mag as u128) * 8u128)
    }
}

pub open spec fn spec_num_from_usize(v: usize) -> JsNum {
    if v == 0usize {
        JsNum(POS_ZERO_BITS)
    } else {
        spec_round_pack_grs(false, 52i32, (((v as u64) as u128) * 8u128) as u128)
    }
}

pub fn num_from_usize(v: usize) -> (r: JsNum)
    ensures r == spec_num_from_usize(v),
{
    if v == 0usize {
        JsNum(POS_ZERO_BITS)
    } else {
        round_pack_grs(false, 52, ((v as u64) as u128) * 8u128)
    }
}

// ---------------------------------------------------------------------------
// IEEE-754 binary64 Add, Sub, Mul, Div, Rem, Exp (§6.1.6.1)
// ---------------------------------------------------------------------------

pub open spec fn spec_align_rhs(sig: u128, diff: u32) -> u128
    decreases diff,
{
    if diff == 0u32 {
        sig
    } else if diff >= 60u32 {
        if sig > 0u128 { 1u128 } else { 0u128 }
    } else {
        spec_align_rhs(spec_shr_sticky_one(sig), (diff - 1u32) as u32)
    }
}

fn align_rhs(sig: u128, diff: u32) -> (r: u128)
    requires 0 < sig < SIG_GRS_HIGH,
    ensures
        r == spec_align_rhs(sig, diff),
        r < SIG_GRS_HIGH,
{
    if diff >= 60u32 {
        return 1u128;
    }
    let mut cs = sig;
    let mut cd = diff;
    while cd > 0u32
        invariant
            0 < cs < SIG_GRS_HIGH,
            cd < 60u32,
            spec_align_rhs(sig, diff) == spec_align_rhs(cs, cd),
        decreases cd,
    {
        cs = shr_sticky_one(cs);
        cd = cd - 1u32;
    }
    cs
}

/// §6.1.6.1.7 Number::add ( x, y )
pub open spec fn spec_num_add(x: JsNum, y: JsNum) -> JsNum {
    if spec_is_nan(x) || spec_is_nan(y) {
        JsNum(NAN_BITS)
    } else {
        let (nx, ex, fx) = spec_unpack_f64(x);
        let (ny, ey, fy) = spec_unpack_f64(y);
        if ex == 2047u16 && ey == 2047u16 {
            if nx == ny { x } else { JsNum(NAN_BITS) }
        } else if ex == 2047u16 {
            x
        } else if ey == 2047u16 {
            y
        } else if ex == 0u16 && fx == 0u64 && ey == 0u16 && fy == 0u64 {
            if nx && ny { JsNum(NEG_ZERO_BITS) } else { JsNum(POS_ZERO_BITS) }
        } else if ex == 0u16 && fx == 0u64 {
            y
        } else if ey == 0u16 && fy == 0u64 {
            x
        } else {
            let (e2x, sx) = spec_normalize_finite(ex, fx);
            let (e2y, sy) = spec_normalize_finite(ey, fy);
            let swap = e2y > e2x || (e2y == e2x && sy > sx);
            let (na, ea, sa, nb, eb, sb) = if swap {
                (ny, e2y, sy, nx, e2x, sx)
            } else {
                (nx, e2x, sx, ny, e2y, sy)
            };
            let diff = (ea - eb) as u32;
            let sa_grs = ((sa as u128) * 8u128) as u128;
            let sb_grs = spec_align_rhs(((sb as u128) * 8u128) as u128, diff);
            if na == nb {
                spec_round_pack_grs(na, ea, (sa_grs + sb_grs) as u128)
            } else if sa_grs == sb_grs {
                JsNum(POS_ZERO_BITS)
            } else if sa_grs > sb_grs {
                spec_round_pack_grs(na, ea, (sa_grs - sb_grs) as u128)
            } else {
                spec_round_pack_grs(nb, ea, (sb_grs - sa_grs) as u128)
            }
        }
    }
}

pub fn num_add(x: JsNum, y: JsNum) -> (r: JsNum)
    ensures r == spec_num_add(x, y),
{
    if num_is_nan(x) || num_is_nan(y) {
        JsNum(NAN_BITS)
    } else {
        let (nx, ex, fx) = unpack_f64(x);
        let (ny, ey, fy) = unpack_f64(y);
        if ex == 2047 && ey == 2047 {
            if nx == ny { x } else { JsNum(NAN_BITS) }
        } else if ex == 2047 {
            x
        } else if ey == 2047 {
            y
        } else if ex == 0 && fx == 0 && ey == 0 && fy == 0 {
            if nx && ny { JsNum(NEG_ZERO_BITS) } else { JsNum(POS_ZERO_BITS) }
        } else if ex == 0 && fx == 0 {
            y
        } else if ey == 0 && fy == 0 {
            x
        } else {
            let (e2x, sx) = normalize_finite(ex, fx);
            let (e2y, sy) = normalize_finite(ey, fy);
            let swap = e2y > e2x || (e2y == e2x && sy > sx);
            let (na, ea, sa, nb, eb, sb) = if swap {
                (ny, e2y, sy, nx, e2x, sx)
            } else {
                (nx, e2x, sx, ny, e2y, sy)
            };
            let diff = (ea - eb) as u32;
            let sa_grs = (sa as u128) * 8u128;
            let sb_grs = align_rhs((sb as u128) * 8u128, diff);
            if na == nb {
                round_pack_grs(na, ea, sa_grs + sb_grs)
            } else if sa_grs == sb_grs {
                JsNum(POS_ZERO_BITS)
            } else if sa_grs > sb_grs {
                round_pack_grs(na, ea, sa_grs - sb_grs)
            } else {
                round_pack_grs(nb, ea, sb_grs - sa_grs)
            }
        }
    }
}

/// §6.1.6.1.8 Number::subtract ( x, y )
pub open spec fn spec_num_sub(x: JsNum, y: JsNum) -> JsNum {
    spec_num_add(x, spec_num_neg(y))
}

pub fn num_sub(x: JsNum, y: JsNum) -> (r: JsNum)
    ensures r == spec_num_sub(x, y),
{
    num_add(x, num_neg(y))
}

/// §6.1.6.1.4 Number::multiply ( x, y )
pub open spec fn spec_num_mul(x: JsNum, y: JsNum) -> JsNum {
    if spec_is_nan(x) || spec_is_nan(y) {
        JsNum(NAN_BITS)
    } else {
        let (nx, ex, fx) = spec_unpack_f64(x);
        let (ny, ey, fy) = spec_unpack_f64(y);
        let neg = nx != ny;
        let zx = ex == 0u16 && fx == 0u64;
        let zy = ey == 0u16 && fy == 0u64;
        if (ex == 2047u16 && zy) || (ey == 2047u16 && zx) {
            JsNum(NAN_BITS)
        } else if ex == 2047u16 || ey == 2047u16 {
            spec_pack_f64(neg, 2047u16, 0u64)
        } else if zx || zy {
            spec_pack_f64(neg, 0u16, 0u64)
        } else {
            let (e2x, sx) = spec_normalize_finite(ex, fx);
            let (e2y, sy) = spec_normalize_finite(ey, fy);
            let prod: u128 = ((sx as u128) * (sy as u128)) as u128;
            spec_round_pack_grs(neg, (e2x + e2y - 49i32) as i32, prod)
        }
    }
}

pub fn num_mul(x: JsNum, y: JsNum) -> (r: JsNum)
    ensures r == spec_num_mul(x, y),
{
    if num_is_nan(x) || num_is_nan(y) {
        JsNum(NAN_BITS)
    } else {
        let (nx, ex, fx) = unpack_f64(x);
        let (ny, ey, fy) = unpack_f64(y);
        let neg = nx != ny;
        let zx = ex == 0 && fx == 0;
        let zy = ey == 0 && fy == 0;
        if (ex == 2047 && zy) || (ey == 2047 && zx) {
            JsNum(NAN_BITS)
        } else if ex == 2047 || ey == 2047 {
            pack_f64(neg, 2047, 0)
        } else if zx || zy {
            pack_f64(neg, 0, 0)
        } else {
            let (e2x, sx) = normalize_finite(ex, fx);
            let (e2y, sy) = normalize_finite(ey, fy);
            proof {
                assert((sx as u128) < 0x0020_0000_0000_0000u128);
                assert((sy as u128) < 0x0020_0000_0000_0000u128);
                assert((sx as u128) * (sy as u128) < SIG_MAX_BOUND) by (nonlinear_arith)
                    requires
                        (sx as u128) < 0x0020_0000_0000_0000u128,
                        (sy as u128) < 0x0020_0000_0000_0000u128;
            }
            let prod: u128 = (sx as u128) * (sy as u128);
            round_pack_grs(neg, e2x + e2y - 49, prod)
        }
    }
}

/// §6.1.6.1.5 Number::divide ( x, y )
pub open spec fn spec_num_div(x: JsNum, y: JsNum) -> JsNum {
    if spec_is_nan(x) || spec_is_nan(y) {
        JsNum(NAN_BITS)
    } else {
        let (nx, ex, fx) = spec_unpack_f64(x);
        let (ny, ey, fy) = spec_unpack_f64(y);
        let neg = nx != ny;
        let zx = ex == 0u16 && fx == 0u64;
        let zy = ey == 0u16 && fy == 0u64;
        if (ex == 2047u16 && ey == 2047u16) || (zx && zy) {
            JsNum(NAN_BITS)
        } else if ex == 2047u16 || zy {
            spec_pack_f64(neg, 2047u16, 0u64)
        } else if ey == 2047u16 || zx {
            spec_pack_f64(neg, 0u16, 0u64)
        } else {
            let (e2x, sx) = spec_normalize_finite(ex, fx);
            let (e2y, sy) = spec_normalize_finite(ey, fy);
            let num: u128 = ((sx as u128) * SIG_GRS_LOW) as u128;
            let q: u128 = num / (sy as u128);
            let rem: u128 = num % (sy as u128);
            let q_grs: u128 = (q * 2u128 + (if rem != 0u128 { 1u128 } else { 0u128 })) as u128;
            spec_round_pack_grs(neg, (e2x - e2y - 1i32) as i32, q_grs)
        }
    }
}

pub fn num_div(x: JsNum, y: JsNum) -> (r: JsNum)
    ensures r == spec_num_div(x, y),
{
    if num_is_nan(x) || num_is_nan(y) {
        JsNum(NAN_BITS)
    } else {
        let (nx, ex, fx) = unpack_f64(x);
        let (ny, ey, fy) = unpack_f64(y);
        let neg = nx != ny;
        let zx = ex == 0 && fx == 0;
        let zy = ey == 0 && fy == 0;
        if (ex == 2047 && ey == 2047) || (zx && zy) {
            JsNum(NAN_BITS)
        } else if ex == 2047 || zy {
            pack_f64(neg, 2047, 0)
        } else if ey == 2047 || zx {
            pack_f64(neg, 0, 0)
        } else {
            let (e2x, sx) = normalize_finite(ex, fx);
            let (e2y, sy) = normalize_finite(ey, fy);
            let num: u128 = (sx as u128) * SIG_GRS_LOW;
            proof {
                assert((sy as u128) >= (MANT_MOD as u128));
                assert(num / (sy as u128) <= num) by (nonlinear_arith)
                    requires num >= 0u128, (sy as u128) >= 1u128;
            }
            let q: u128 = num / (sy as u128);
            let rem: u128 = num % (sy as u128);
            let q_grs: u128 = q * 2u128 + (if rem != 0u128 { 1u128 } else { 0u128 });
            round_pack_grs(neg, e2x - e2y - 1, q_grs)
        }
    }
}

pub open spec fn spec_rem_steps(rem: u64, sd: u64, steps: nat) -> u64
    decreases steps,
{
    let r1: u64 = if rem >= sd { (rem - sd) as u64 } else { rem };
    if steps == 0 {
        r1
    } else {
        spec_rem_steps((r1 * 2u64) as u64, sd, (steps - 1) as nat)
    }
}

fn rem_steps(rem: u64, sd: u64, steps: usize) -> (r: u64)
    requires
        MANT_MOD <= sd < 2 * MANT_MOD,
        rem < 2 * sd,
        steps <= 2500,
    ensures
        r == spec_rem_steps(rem, sd, steps as nat),
        r < sd,
{
    let mut cr = rem;
    let mut cs = steps;
    while cs > 0
        invariant
            MANT_MOD <= sd < 2 * MANT_MOD,
            cr < 2 * sd,
            cs <= steps <= 2500,
            spec_rem_steps(rem, sd, steps as nat) == spec_rem_steps(cr, sd, cs as nat),
        decreases cs,
    {
        let r1: u64 = if cr >= sd { cr - sd } else { cr };
        cr = r1 * 2u64;
        cs = cs - 1;
    }
    if cr >= sd { cr - sd } else { cr }
}

/// §6.1.6.1.6 Number::remainder ( n, d )
pub open spec fn spec_num_rem(n: JsNum, d: JsNum) -> JsNum {
    if spec_is_nan(n) || spec_is_nan(d) {
        JsNum(NAN_BITS)
    } else {
        let (nn, en, fn_) = spec_unpack_f64(n);
        let (_, ed, fd) = spec_unpack_f64(d);
        let zn = en == 0u16 && fn_ == 0u64;
        let zd = ed == 0u16 && fd == 0u64;
        if en == 2047u16 || zd {
            JsNum(NAN_BITS)
        } else if ed == 2047u16 || zn {
            n
        } else {
            let (e2n, sn) = spec_normalize_finite(en, fn_);
            let (e2d, sd) = spec_normalize_finite(ed, fd);
            if e2n < e2d {
                n
            } else {
                let steps = (e2n - e2d) as usize;
                let rem = spec_rem_steps(sn, sd, steps as nat);
                if rem == 0u64 {
                    spec_pack_f64(nn, 0u16, 0u64)
                } else {
                    spec_round_pack_grs(nn, e2d, ((rem as u128) * 8u128) as u128)
                }
            }
        }
    }
}

pub fn num_rem(n: JsNum, d: JsNum) -> (r: JsNum)
    ensures r == spec_num_rem(n, d),
{
    if num_is_nan(n) || num_is_nan(d) {
        JsNum(NAN_BITS)
    } else {
        let (nn, en, fn_) = unpack_f64(n);
        let (_, ed, fd) = unpack_f64(d);
        let zn = en == 0 && fn_ == 0;
        let zd = ed == 0 && fd == 0;
        if en == 2047 || zd {
            JsNum(NAN_BITS)
        } else if ed == 2047 || zn {
            n
        } else {
            let (e2n, sn) = normalize_finite(en, fn_);
            let (e2d, sd) = normalize_finite(ed, fd);
            if e2n < e2d {
                n
            } else {
                let steps = (e2n - e2d) as usize;
                let rem = rem_steps(sn, sd, steps);
                if rem == 0 {
                    pack_f64(nn, 0, 0)
                } else {
                    round_pack_grs(nn, e2d, (rem as u128) * 8u128)
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// ToUint32, ToInt32, and Bitwise Operations (§7.1.6, §7.1.7, §6.1.6.1.9-15)
// ---------------------------------------------------------------------------

/// §7.1.7 ToUint32 ( argument ) on a Number
pub open spec fn spec_to_uint32(n: JsNum) -> u32 {
    if spec_is_nan(n) || spec_is_zero(n) || spec_is_infinite(n) {
        0u32
    } else {
        let (neg, exp, frac) = spec_unpack_f64(n);
        let (e2, sig) = spec_normalize_finite(exp, frac);
        if e2 < 0i32 || e2 >= 84i32 {
            0u32
        } else {
            let trunc_mod: u64 = if e2 >= 52i32 {
                let k = (e2 - 52i32) as u32;
                let shifted: u128 = (sig as u128) << k;
                (shifted % 0x1_0000_0000u128) as u64
            } else {
                let k = (52i32 - e2) as u32;
                let shifted: u64 = sig >> k;
                shifted % 0x1_0000_0000u64
            };
            if trunc_mod == 0u64 {
                0u32
            } else if neg {
                (0x1_0000_0000u64 - trunc_mod) as u32
            } else {
                trunc_mod as u32
            }
        }
    }
}

pub fn num_to_uint32(n: JsNum) -> (r: u32)
    ensures r == spec_to_uint32(n),
{
    if num_is_nan(n) || num_is_zero(n) || num_is_infinite(n) {
        0u32
    } else {
        let (neg, exp, frac) = unpack_f64(n);
        let (e2, sig) = normalize_finite(exp, frac);
        if e2 < 0 || e2 >= 84 {
            0u32
        } else {
            let trunc_mod: u64 = if e2 >= 52 {
                let k = (e2 - 52) as u32;
                let shifted: u128 = (sig as u128) << k;
                (shifted % 0x1_0000_0000u128) as u64
            } else {
                let k = (52 - e2) as u32;
                let shifted: u64 = sig >> k;
                shifted % 0x1_0000_0000u64
            };
            if trunc_mod == 0 {
                0u32
            } else if neg {
                (0x1_0000_0000u64 - trunc_mod) as u32
            } else {
                trunc_mod as u32
            }
        }
    }
}

/// §7.1.6 ToInt32 ( argument ) on a Number
pub open spec fn spec_to_int32(n: JsNum) -> i32 {
    let u = spec_to_uint32(n);
    if u >= 0x8000_0000u32 {
        ((u as i64) - 0x1_0000_0000i64) as i32
    } else {
        u as i32
    }
}

pub fn num_to_int32(n: JsNum) -> (r: i32)
    ensures r == spec_to_int32(n),
{
    let u = num_to_uint32(n);
    if u >= 0x8000_0000u32 {
        ((u as i64) - 0x1_0000_0000i64) as i32
    } else {
        u as i32
    }
}

pub open spec fn spec_num_bit_not(x: JsNum) -> JsNum {
    let a = spec_to_int32(x);
    spec_num_from_i64((!a) as i64)
}

pub fn num_bit_not(x: JsNum) -> (r: JsNum)
    ensures r == spec_num_bit_not(x),
{
    let a = num_to_int32(x);
    num_from_i64((!a) as i64)
}

pub open spec fn spec_num_bit_and(x: JsNum, y: JsNum) -> JsNum {
    let a = spec_to_int32(x);
    let b = spec_to_int32(y);
    spec_num_from_i64((a & b) as i64)
}

pub fn num_bit_and(x: JsNum, y: JsNum) -> (r: JsNum)
    ensures r == spec_num_bit_and(x, y),
{
    let a = num_to_int32(x);
    let b = num_to_int32(y);
    num_from_i64((a & b) as i64)
}

pub open spec fn spec_num_bit_or(x: JsNum, y: JsNum) -> JsNum {
    let a = spec_to_int32(x);
    let b = spec_to_int32(y);
    spec_num_from_i64((a | b) as i64)
}

pub fn num_bit_or(x: JsNum, y: JsNum) -> (r: JsNum)
    ensures r == spec_num_bit_or(x, y),
{
    let a = num_to_int32(x);
    let b = num_to_int32(y);
    num_from_i64((a | b) as i64)
}

pub open spec fn spec_num_bit_xor(x: JsNum, y: JsNum) -> JsNum {
    let a = spec_to_int32(x);
    let b = spec_to_int32(y);
    spec_num_from_i64((a ^ b) as i64)
}

pub fn num_bit_xor(x: JsNum, y: JsNum) -> (r: JsNum)
    ensures r == spec_num_bit_xor(x, y),
{
    let a = num_to_int32(x);
    let b = num_to_int32(y);
    num_from_i64((a ^ b) as i64)
}

pub open spec fn spec_num_shl(x: JsNum, y: JsNum) -> JsNum {
    let a = spec_to_int32(x) as u32;
    let shift = spec_to_uint32(y) % 32u32;
    let res_u = a << shift;
    let res_i: i32 = if res_u >= 0x8000_0000u32 {
        ((res_u as i64) - 0x1_0000_0000i64) as i32
    } else {
        res_u as i32
    };
    spec_num_from_i64(res_i as i64)
}

pub fn num_shl(x: JsNum, y: JsNum) -> (r: JsNum)
    ensures r == spec_num_shl(x, y),
{
    let a = num_to_int32(x) as u32;
    let shift = num_to_uint32(y) % 32u32;
    let res_u = a << shift;
    let res_i: i32 = if res_u >= 0x8000_0000u32 {
        ((res_u as i64) - 0x1_0000_0000i64) as i32
    } else {
        res_u as i32
    };
    num_from_i64(res_i as i64)
}

pub open spec fn spec_num_shr(x: JsNum, y: JsNum) -> JsNum {
    let a = spec_to_int32(x);
    let shift = spec_to_uint32(y) % 32u32;
    spec_num_from_i64((a >> shift) as i64)
}

pub fn num_shr(x: JsNum, y: JsNum) -> (r: JsNum)
    ensures r == spec_num_shr(x, y),
{
    let a = num_to_int32(x);
    let shift = num_to_uint32(y) % 32u32;
    num_from_i64((a >> shift) as i64)
}

pub open spec fn spec_num_ushr(x: JsNum, y: JsNum) -> JsNum {
    let a = spec_to_uint32(x);
    let shift = spec_to_uint32(y) % 32u32;
    spec_num_from_i64((a >> shift) as i64)
}

pub fn num_ushr(x: JsNum, y: JsNum) -> (r: JsNum)
    ensures r == spec_num_ushr(x, y),
{
    let a = num_to_uint32(x);
    let shift = num_to_uint32(y) % 32u32;
    num_from_i64((a >> shift) as i64)
}

// ---------------------------------------------------------------------------
// Number Comparisons & Equality (§6.1.6.1.12-19)
// ---------------------------------------------------------------------------

/// §6.1.6.1.13 Number::equal ( x, y )
pub open spec fn spec_num_equal(x: JsNum, y: JsNum) -> bool {
    if spec_is_nan(x) || spec_is_nan(y) {
        false
    } else if spec_is_zero(x) && spec_is_zero(y) {
        true
    } else {
        x.0 == y.0
    }
}

pub fn num_equal(x: JsNum, y: JsNum) -> (r: bool)
    ensures r == spec_num_equal(x, y),
{
    if num_is_nan(x) || num_is_nan(y) {
        false
    } else if num_is_zero(x) && num_is_zero(y) {
        true
    } else {
        x.0 == y.0
    }
}

/// §6.1.6.1.14 Number::sameValue ( x, y )
pub open spec fn spec_num_same_value(x: JsNum, y: JsNum) -> bool {
    if spec_is_nan(x) && spec_is_nan(y) {
        true
    } else {
        x.0 == y.0
    }
}

pub fn num_same_value(x: JsNum, y: JsNum) -> (r: bool)
    ensures r == spec_num_same_value(x, y),
{
    if num_is_nan(x) && num_is_nan(y) {
        true
    } else {
        x.0 == y.0
    }
}

/// §6.1.6.1.12 Number::lessThan ( x, y ): returns None when either operand is NaN.
pub open spec fn spec_num_less_than(x: JsNum, y: JsNum) -> Option<bool> {
    if spec_is_nan(x) || spec_is_nan(y) {
        None
    } else if spec_is_zero(x) && spec_is_zero(y) {
        Some(false)
    } else if x.0 == y.0 {
        Some(false)
    } else {
        let (nx, ex, fx) = spec_unpack_f64(x);
        let (ny, ey, fy) = spec_unpack_f64(y);
        if nx && !ny {
            Some(true)
        } else if !nx && ny {
            Some(false)
        } else if !nx {
            Some(ex < ey || (ex == ey && fx < fy))
        } else {
            Some(ex > ey || (ex == ey && fx > fy))
        }
    }
}

pub fn num_less_than(x: JsNum, y: JsNum) -> (r: Option<bool>)
    ensures r == spec_num_less_than(x, y),
{
    if num_is_nan(x) || num_is_nan(y) {
        None
    } else if num_is_zero(x) && num_is_zero(y) {
        Some(false)
    } else if x.0 == y.0 {
        Some(false)
    } else {
        let (nx, ex, fx) = unpack_f64(x);
        let (ny, ey, fy) = unpack_f64(y);
        if nx && !ny {
            Some(true)
        } else if !nx && ny {
            Some(false)
        } else if !nx {
            Some(ex < ey || (ex == ey && fx < fy))
        } else {
            Some(ex > ey || (ex == ey && fx > fy))
        }
    }
}

// ---------------------------------------------------------------------------
// Exact Safe Integer Extraction & Exponentiation (§6.1.6.1.3)
// ---------------------------------------------------------------------------

/// If `n` is an exact mathematical integer in `[-9007199254740991, 9007199254740991]`,
/// returns `Some((neg, abs_u64))`. Note `-0` and `+0` return `Some((false, 0))`.
pub open spec fn spec_num_exact_safe_int(n: JsNum) -> Option<(bool, u64)> {
    if spec_is_zero(n) {
        Some((false, 0u64))
    } else if !spec_is_finite(n) {
        None
    } else {
        let (neg, exp, frac) = spec_unpack_f64(n);
        let (e2, sig) = spec_normalize_finite(exp, frac);
        if e2 < 0i32 || e2 > 52i32 {
            None
        } else if e2 == 52i32 {
            Some((neg, sig))
        } else {
            let shift = (52i32 - e2) as u32;
            let q: u64 = sig >> shift;
            let reconstructed: u64 = q << shift;
            if reconstructed == sig {
                Some((neg, q))
            } else {
                None
            }
        }
    }
}

pub fn num_exact_safe_int(n: JsNum) -> (r: Option<(bool, u64)>)
    ensures r == spec_num_exact_safe_int(n),
{
    if num_is_zero(n) {
        Some((false, 0u64))
    } else if !num_is_finite(n) {
        None
    } else {
        let (neg, exp, frac) = unpack_f64(n);
        let (e2, sig) = normalize_finite(exp, frac);
        if e2 < 0 || e2 > 52 {
            None
        } else if e2 == 52 {
            Some((neg, sig))
        } else {
            let shift = (52 - e2) as u32;
            let q: u64 = sig >> shift;
            proof {
                assert((q << shift) <= sig) by (bit_vector)
                    requires shift <= 52u32, q == (sig >> shift);
            }
            let reconstructed: u64 = q << shift;
            if reconstructed == sig {
                Some((neg, q))
            } else {
                None
            }
        }
    }
}

pub open spec fn spec_pow_loop(acc: JsNum, base: JsNum, exp: u64) -> JsNum
    decreases exp,
{
    if exp == 0u64 {
        acc
    } else {
        let next_acc = if exp % 2u64 == 1u64 { spec_num_mul(acc, base) } else { acc };
        spec_pow_loop(next_acc, spec_num_mul(base, base), exp / 2u64)
    }
}

fn pow_loop(acc: JsNum, base: JsNum, exp: u64) -> (r: JsNum)
    ensures r == spec_pow_loop(acc, base, exp),
{
    let mut cacc = acc;
    let mut cbase = base;
    let mut cexp = exp;
    while cexp > 0u64
        invariant
            spec_pow_loop(acc, base, exp) == spec_pow_loop(cacc, cbase, cexp),
        decreases cexp,
    {
        if cexp % 2u64 == 1u64 {
            cacc = num_mul(cacc, cbase);
        }
        cbase = num_mul(cbase, cbase);
        cexp = cexp / 2u64;
    }
    cacc
}

/// Exact integer-exponent `Number::exponentiate(base, exponent)`; returns `None` only when
/// `exponent` is a finite non-integer (reported explicitly as `UnsupportedFeature::NonIntegerExponentiation`).
pub open spec fn spec_num_exp(base: JsNum, exponent: JsNum) -> Option<JsNum> {
    if spec_is_nan(exponent) {
        Some(JsNum(NAN_BITS))
    } else if spec_is_zero(exponent) {
        Some(JsNum(ONE_BITS))
    } else if spec_is_nan(base) {
        Some(JsNum(NAN_BITS))
    } else if spec_is_infinite(exponent) {
        let (neg_e, _, _) = spec_unpack_f64(exponent);
        let (_, eb, fb) = spec_unpack_f64(base);
        // |base| == 1 => NaN per ECMA-262 §6.1.6.1.3
        if eb == 1023u16 && fb == 0u64 {
            Some(JsNum(NAN_BITS))
        } else if eb > 1023u16 || (eb == 1023u16 && fb > 0u64) {
            Some(if neg_e { JsNum(POS_ZERO_BITS) } else { JsNum(POS_INF_BITS) })
        } else {
            Some(if neg_e { JsNum(POS_INF_BITS) } else { JsNum(POS_ZERO_BITS) })
        }
    } else {
        match spec_num_exact_safe_int(exponent) {
            Some((neg_e, mag_e)) => {
                let p = spec_pow_loop(JsNum(ONE_BITS), base, mag_e);
                if neg_e {
                    Some(spec_num_div(JsNum(ONE_BITS), p))
                } else {
                    Some(p)
                }
            }
            None => None,
        }
    }
}

pub fn num_exp(base: JsNum, exponent: JsNum) -> (r: Option<JsNum>)
    ensures r == spec_num_exp(base, exponent),
{
    if num_is_nan(exponent) {
        Some(JsNum(NAN_BITS))
    } else if num_is_zero(exponent) {
        Some(JsNum(ONE_BITS))
    } else if num_is_nan(base) {
        Some(JsNum(NAN_BITS))
    } else if num_is_infinite(exponent) {
        let (neg_e, _, _) = unpack_f64(exponent);
        let (_, eb, fb) = unpack_f64(base);
        if eb == 1023 && fb == 0 {
            Some(JsNum(NAN_BITS))
        } else if eb > 1023 || (eb == 1023 && fb > 0) {
            Some(if neg_e { JsNum(POS_ZERO_BITS) } else { JsNum(POS_INF_BITS) })
        } else {
            Some(if neg_e { JsNum(POS_INF_BITS) } else { JsNum(POS_ZERO_BITS) })
        }
    } else {
        match num_exact_safe_int(exponent) {
            Some((neg_e, mag_e)) => {
                let p = pow_loop(JsNum(ONE_BITS), base, mag_e);
                if neg_e {
                    Some(num_div(JsNum(ONE_BITS), p))
                } else {
                    Some(p)
                }
            }
            None => None,
        }
    }
}

// ---------------------------------------------------------------------------
// UTF-16 String Operations (§6.1.4, §7.2.13)
// ---------------------------------------------------------------------------

pub open spec fn spec_str_eq_from(a: Seq<u16>, b: Seq<u16>, idx: nat) -> bool
    decreases a.len() - idx,
{
    if a.len() != b.len() {
        false
    } else if idx >= a.len() {
        true
    } else if a[idx as int] != b[idx as int] {
        false
    } else {
        spec_str_eq_from(a, b, idx + 1)
    }
}

pub proof fn lemma_str_eq_from_equiv(a: Seq<u16>, b: Seq<u16>, idx: nat)
    requires
        a.len() == b.len(),
        idx <= a.len(),
    ensures
        spec_str_eq_from(a, b, idx) <==> (forall|k: int| idx as int <= k < a.len() ==> #[trigger] a[k] == b[k]),
    decreases a.len() - idx,
{
    if idx < a.len() {
        lemma_str_eq_from_equiv(a, b, idx + 1);
    }
}

pub fn js_str_eq(a: &JsStr, b: &JsStr) -> (r: bool)
    ensures r == (a@ == b@),
{
    if a.0.len() != b.0.len() {
        return false;
    }
    let n = a.0.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == a@.len(),
            n == b@.len(),
            forall|k: int| 0 <= k < i as int ==> a@[k] == b@[k],
        decreases n - i,
    {
        if a.0[i] != b.0[i] {
            return false;
        }
        i += 1;
    }
    proof {
        assert(a@ =~= b@);
    }
    true
}

/// §7.2.13 IsLessThan on two Strings (UTF-16 code unit lexicographic comparison).
pub open spec fn spec_str_lt_from(a: Seq<u16>, b: Seq<u16>, idx: nat) -> bool
    decreases a.len() - idx,
{
    if idx >= a.len() {
        idx < b.len()
    } else if idx >= b.len() {
        false
    } else if a[idx as int] < b[idx as int] {
        true
    } else if a[idx as int] > b[idx as int] {
        false
    } else {
        spec_str_lt_from(a, b, idx + 1)
    }
}

pub open spec fn spec_str_lt(a: Seq<u16>, b: Seq<u16>) -> bool {
    spec_str_lt_from(a, b, 0)
}

pub fn js_str_lt(a: &JsStr, b: &JsStr) -> (r: bool)
    ensures r == spec_str_lt(a@, b@),
{
    let na = a.0.len();
    let nb = b.0.len();
    let mut i: usize = 0;
    while i < na && i < nb
        invariant
            i <= na,
            i <= nb,
            na == a@.len(),
            nb == b@.len(),
            spec_str_lt_from(a@, b@, 0) == spec_str_lt_from(a@, b@, i as nat),
        decreases na - i,
    {
        if a.0[i] < b.0[i] {
            return true;
        }
        if a.0[i] > b.0[i] {
            return false;
        }
        i += 1;
    }
    i < nb
}

pub fn js_str_concat(a: &JsStr, b: &JsStr) -> (r: JsStr)
    ensures r@ == a@ + b@,
{
    let mut out: Vec<u16> = Vec::new();
    let na = a.0.len();
    let nb = b.0.len();
    let mut i: usize = 0;
    while i < na
        invariant
            i <= na,
            na == a@.len(),
            out@ =~= a@.subrange(0, i as int),
        decreases na - i,
    {
        out.push(a.0[i]);
        i += 1;
    }
    proof {
        assert(a@.subrange(0, na as int) =~= a@);
    }
    let mut j: usize = 0;
    while j < nb
        invariant
            j <= nb,
            nb == b@.len(),
            out@ =~= a@ + b@.subrange(0, j as int),
        decreases nb - j,
    {
        out.push(b.0[j]);
        j += 1;
    }
    proof {
        assert(b@.subrange(0, nb as int) =~= b@);
    }
    JsStr(out)
}

pub open spec fn spec_ascii_bytes_to_utf16(bs: Seq<u8>) -> Seq<u16> {
    Seq::new(bs.len(), |i: int| bs[i] as u16)
}

pub fn ascii_to_js_str(bs: &[u8]) -> (r: JsStr)
    ensures r@ == spec_ascii_bytes_to_utf16(bs@),
{
    let n = bs.len();
    let mut out: Vec<u16> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == bs@.len(),
            out@.len() == i,
            forall|k: int| 0 <= k < i as int ==> out@[k] == bs@[k] as u16,
        decreases n - i,
    {
        out.push(bs[i] as u16);
        i += 1;
    }
    proof {
        assert(out@ =~= spec_ascii_bytes_to_utf16(bs@));
    }
    JsStr(out)
}

/// Full UTF-8 byte sequence to UTF-16 code units (BMP + surrogate pairs for U+10000..=U+10FFFF).
pub open spec fn spec_utf8_to_utf16(bs: Seq<u8>) -> Seq<u16>
    decreases bs.len(),
{
    if bs.len() == 0 {
        seq![]
    } else {
        let b0 = bs[0];
        if b0 < 0x80u8 {
            seq![b0 as u16] + spec_utf8_to_utf16(bs.subrange(1, bs.len() as int))
        } else if b0 >= 0xC2u8 && b0 <= 0xDFu8 && bs.len() >= 2 && (bs[1] >= 0x80u8 && bs[1] <= 0xBFu8) {
            let cp: u16 = (((b0 - 0xC0u8) as u16) * 64u16 + ((bs[1] - 0x80u8) as u16)) as u16;
            seq![cp] + spec_utf8_to_utf16(bs.subrange(2, bs.len() as int))
        } else if b0 >= 0xE0u8 && b0 <= 0xEFu8 && bs.len() >= 3
            && (bs[1] >= 0x80u8 && bs[1] <= 0xBFu8)
            && (bs[2] >= 0x80u8 && bs[2] <= 0xBFu8)
        {
            let cp: u32 = (((b0 - 0xE0u8) as u32) * 4096u32
                + ((bs[1] - 0x80u8) as u32) * 64u32
                + ((bs[2] - 0x80u8) as u32)) as u32;
            seq![cp as u16] + spec_utf8_to_utf16(bs.subrange(3, bs.len() as int))
        } else if b0 >= 0xF0u8 && b0 <= 0xF4u8 && bs.len() >= 4
            && (bs[1] >= 0x80u8 && bs[1] <= 0xBFu8)
            && (bs[2] >= 0x80u8 && bs[2] <= 0xBFu8)
            && (bs[3] >= 0x80u8 && bs[3] <= 0xBFu8)
        {
            let cp_raw: u32 = (((b0 - 0xF0u8) as u32) * 262144u32
                + ((bs[1] - 0x80u8) as u32) * 4096u32
                + ((bs[2] - 0x80u8) as u32) * 64u32
                + ((bs[3] - 0x80u8) as u32)) as u32;
            if cp_raw >= 0x10000u32 && cp_raw <= 0x10FFFFu32 {
                let off: u32 = (cp_raw - 0x10000u32) as u32;
                let hi: u16 = (0xD800u32 + (off / 1024u32)) as u16;
                let lo: u16 = (0xDC00u32 + (off % 1024u32)) as u16;
                seq![hi, lo] + spec_utf8_to_utf16(bs.subrange(4, bs.len() as int))
            } else {
                seq![0xFFFDu16] + spec_utf8_to_utf16(bs.subrange(1, bs.len() as int))
            }
        } else {
            seq![0xFFFDu16] + spec_utf8_to_utf16(bs.subrange(1, bs.len() as int))
        }
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub fn utf8_to_js_str(bs: &[u8]) -> (out: JsStr)
    ensures out@ == spec_utf8_to_utf16(bs@),
{
    let n = bs.len();
    let mut v: Vec<u16> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(bs@.subrange(0, n as int) =~= bs@);
        assert(v@ =~= Seq::<u16>::empty());
    }
    while i < n
        invariant
            i <= n,
            n == bs@.len(),
            spec_utf8_to_utf16(bs@) == v@ + spec_utf8_to_utf16(bs@.subrange(i as int, n as int)),
        decreases n - i,
    {
        let b0 = bs[i];
        let ghost rest = bs@.subrange(i as int, n as int);
        let ghost old_v = v@;
        if b0 < 0x80 {
            proof { assert(rest.subrange(1, rest.len() as int) =~= bs@.subrange(i + 1, n as int)); }
            v.push(b0 as u16);
            i += 1;
            proof {
                assert(old_v + (seq![b0 as u16] + spec_utf8_to_utf16(bs@.subrange(i as int, n as int)))
                    =~= v@ + spec_utf8_to_utf16(bs@.subrange(i as int, n as int)));
            }
        } else if b0 >= 0xC2 && b0 <= 0xDF && n - i >= 2 && bs[i + 1] >= 0x80 && bs[i + 1] <= 0xBF {
            let cp: u16 = ((b0 - 0xC0) as u16) * 64 + ((bs[i + 1] - 0x80) as u16);
            proof { assert(rest.subrange(2, rest.len() as int) =~= bs@.subrange(i + 2, n as int)); }
            v.push(cp);
            i += 2;
            proof {
                assert(old_v + (seq![cp] + spec_utf8_to_utf16(bs@.subrange(i as int, n as int)))
                    =~= v@ + spec_utf8_to_utf16(bs@.subrange(i as int, n as int)));
            }
        } else if b0 >= 0xE0 && b0 <= 0xEF && n - i >= 3
            && bs[i + 1] >= 0x80 && bs[i + 1] <= 0xBF
            && bs[i + 2] >= 0x80 && bs[i + 2] <= 0xBF
        {
            let cp: u32 = ((b0 - 0xE0) as u32) * 4096
                + ((bs[i + 1] - 0x80) as u32) * 64
                + ((bs[i + 2] - 0x80) as u32);
            let cu = cp as u16;
            proof { assert(rest.subrange(3, rest.len() as int) =~= bs@.subrange(i + 3, n as int)); }
            v.push(cu);
            i += 3;
            proof {
                assert(old_v + (seq![cu] + spec_utf8_to_utf16(bs@.subrange(i as int, n as int)))
                    =~= v@ + spec_utf8_to_utf16(bs@.subrange(i as int, n as int)));
            }
        } else if b0 >= 0xF0 && b0 <= 0xF4 && n - i >= 4
            && bs[i + 1] >= 0x80 && bs[i + 1] <= 0xBF
            && bs[i + 2] >= 0x80 && bs[i + 2] <= 0xBF
            && bs[i + 3] >= 0x80 && bs[i + 3] <= 0xBF
        {
            let cp_raw: u32 = ((b0 - 0xF0) as u32) * 262144
                + ((bs[i + 1] - 0x80) as u32) * 4096
                + ((bs[i + 2] - 0x80) as u32) * 64
                + ((bs[i + 3] - 0x80) as u32);
            if cp_raw >= 0x10000 && cp_raw <= 0x10FFFF {
                let off: u32 = cp_raw - 0x10000;
                let hi: u16 = (0xD800 + (off / 1024)) as u16;
                let lo: u16 = (0xDC00 + (off % 1024)) as u16;
                proof { assert(rest.subrange(4, rest.len() as int) =~= bs@.subrange(i + 4, n as int)); }
                v.push(hi);
                v.push(lo);
                i += 4;
                proof {
                    assert(old_v + (seq![hi, lo] + spec_utf8_to_utf16(bs@.subrange(i as int, n as int)))
                        =~= v@ + spec_utf8_to_utf16(bs@.subrange(i as int, n as int)));
                }
            } else {
                proof { assert(rest.subrange(1, rest.len() as int) =~= bs@.subrange(i + 1, n as int)); }
                v.push(0xFFFD);
                i += 1;
                proof {
                    assert(old_v + (seq![0xFFFDu16] + spec_utf8_to_utf16(bs@.subrange(i as int, n as int)))
                        =~= v@ + spec_utf8_to_utf16(bs@.subrange(i as int, n as int)));
                }
            }
        } else {
            proof { assert(rest.subrange(1, rest.len() as int) =~= bs@.subrange(i + 1, n as int)); }
            v.push(0xFFFD);
            i += 1;
            proof {
                assert(old_v + (seq![0xFFFDu16] + spec_utf8_to_utf16(bs@.subrange(i as int, n as int)))
                    =~= v@ + spec_utf8_to_utf16(bs@.subrange(i as int, n as int)));
            }
        }
    }
    proof {
        assert(bs@.subrange(n as int, n as int) =~= Seq::<u8>::empty());
        assert(v@ + Seq::<u16>::empty() =~= v@);
    }
    JsStr(v)
}

// ---------------------------------------------------------------------------
// Number::toString & StringToNumber (§6.1.6.1.20, §7.1.4.1.1)
// Exact IEEE-754 Burger-Dybvig shortest round-trip & BigNat RNE conversion
// ---------------------------------------------------------------------------

/// §6.1.6.1.20 Number::toString ( x, 10 )
pub open spec fn spec_number_to_string(x: JsNum) -> Seq<u16> {
    crate::number::spec_number_to_string(crate::number::JsNumber(x.0))
}

pub fn number_to_js_str(x: JsNum) -> (r: JsStr)
    ensures r@ == spec_number_to_string(x),
{
    let out = crate::number::number_to_string(crate::number::JsNumber(x.0));
    JsStr(out.units)
}

/// §7.1.4.1.1 StringToNumber ( str )
pub open spec fn spec_string_to_number(s: Seq<u16>) -> JsNum {
    JsNum(crate::number::spec_string_to_number(s).0)
}

pub fn string_to_js_num(s: &JsStr) -> (r: JsNum)
    ensures r == spec_string_to_number(s@),
{
    let cloned = clone_js_str(s);
    let u = crate::utf16::Utf16Str { units: cloned.0 };
    let n = crate::number::string_to_number(&u);
    JsNum(n.0)
}

// ---------------------------------------------------------------------------
// Primitive Abstract Operations (§7.1.2 ToBoolean, §7.2.10 SameValue,
// §7.2.14 IsLooselyEqual, §7.2.15 IsStrictlyEqual)
// ---------------------------------------------------------------------------

/// §7.1.2 ToBoolean ( argument )
/// Objects always coerce to `true`; `0`, `-0`, `NaN`, `""`, `null`, `undefined`, `false` coerce to `false`.
pub open spec fn spec_to_boolean(v: SpecVal) -> bool {
    match v {
        SpecVal::Undefined => false,
        SpecVal::Null => false,
        SpecVal::Bool(b) => b,
        SpecVal::Number(n) => !spec_is_zero(n) && !spec_is_nan(n),
        SpecVal::Str(s) => s.len() > 0,
        SpecVal::Object(_) => true,
    }
}

pub fn val_to_boolean(v: &Val) -> (r: bool)
    ensures r == spec_to_boolean(v@),
{
    match v {
        Val::Undefined => false,
        Val::Null => false,
        Val::Bool(b) => *b,
        Val::Number(n) => !num_is_zero(*n) && !num_is_nan(*n),
        Val::Str(s) => s.0.len() > 0,
        Val::Object(_) => true,
    }
}

/// §7.1.4 ToNumber on primitive values (caller converts Objects via `ToPrimitive` first).
pub open spec fn spec_prim_to_number(v: SpecVal) -> JsNum {
    match v {
        SpecVal::Undefined => JsNum(NAN_BITS),
        SpecVal::Null => JsNum(POS_ZERO_BITS),
        SpecVal::Bool(b) => if b { JsNum(ONE_BITS) } else { JsNum(POS_ZERO_BITS) },
        SpecVal::Number(n) => n,
        SpecVal::Str(s) => spec_string_to_number(s),
        SpecVal::Object(_) => JsNum(NAN_BITS),
    }
}

pub fn prim_to_number(v: &Val) -> (r: JsNum)
    ensures r == spec_prim_to_number(v@),
{
    match v {
        Val::Undefined => JsNum(NAN_BITS),
        Val::Null => JsNum(POS_ZERO_BITS),
        Val::Bool(b) => if *b { JsNum(ONE_BITS) } else { JsNum(POS_ZERO_BITS) },
        Val::Number(n) => *n,
        Val::Str(s) => string_to_js_num(s),
        Val::Object(_) => JsNum(NAN_BITS),
    }
}

/// §7.1.17 ToString on primitive values.
pub open spec fn spec_prim_to_string(v: SpecVal) -> Seq<u16> {
    match v {
        SpecVal::Undefined => seq![0x75u16, 0x6Eu16, 0x64u16, 0x65u16, 0x66u16, 0x69u16, 0x6Eu16, 0x65u16, 0x64u16],
        SpecVal::Null => seq![0x6Eu16, 0x75u16, 0x6Cu16, 0x6Cu16],
        SpecVal::Bool(b) => if b {
            seq![0x74u16, 0x72u16, 0x75u16, 0x65u16]
        } else {
            seq![0x66u16, 0x61u16, 0x6Cu16, 0x73u16, 0x65u16]
        },
        SpecVal::Number(n) => spec_number_to_string(n),
        SpecVal::Str(s) => s,
        SpecVal::Object(_) => seq![
            0x5Bu16, 0x6Fu16, 0x62u16, 0x6Au16, 0x65u16, 0x63u16, 0x74u16, 0x20u16,
            0x4Fu16, 0x62u16, 0x6Au16, 0x65u16, 0x63u16, 0x74u16, 0x5Du16
        ],
    }
}

pub fn prim_to_js_str(v: &Val) -> (r: JsStr)
    ensures r@ == spec_prim_to_string(v@),
{
    match v {
        Val::Undefined => {
            let mut out: Vec<u16> = Vec::new();
            out.push(0x75); out.push(0x6E); out.push(0x64); out.push(0x65); out.push(0x66);
            out.push(0x69); out.push(0x6E); out.push(0x65); out.push(0x64);
            proof { assert(out@ =~= spec_prim_to_string(v@)); }
            JsStr(out)
        }
        Val::Null => {
            let mut out: Vec<u16> = Vec::new();
            out.push(0x6E); out.push(0x75); out.push(0x6C); out.push(0x6C);
            proof { assert(out@ =~= spec_prim_to_string(v@)); }
            JsStr(out)
        }
        Val::Bool(b) => {
            if *b {
                let mut out: Vec<u16> = Vec::new();
                out.push(0x74); out.push(0x72); out.push(0x75); out.push(0x65);
                proof { assert(out@ =~= spec_prim_to_string(v@)); }
                JsStr(out)
            } else {
                let mut out: Vec<u16> = Vec::new();
                out.push(0x66); out.push(0x61); out.push(0x6C); out.push(0x73); out.push(0x65);
                proof { assert(out@ =~= spec_prim_to_string(v@)); }
                JsStr(out)
            }
        }
        Val::Number(n) => number_to_js_str(*n),
        Val::Str(s) => clone_js_str(s),
        Val::Object(_) => {
            let mut out: Vec<u16> = Vec::new();
            out.push(0x5B); out.push(0x6F); out.push(0x62); out.push(0x6A); out.push(0x65);
            out.push(0x63); out.push(0x74); out.push(0x20); out.push(0x4F); out.push(0x62);
            out.push(0x6A); out.push(0x65); out.push(0x63); out.push(0x74); out.push(0x5D);
            proof { assert(out@ =~= spec_prim_to_string(v@)); }
            JsStr(out)
        }
    }
}

/// §7.2.15 IsStrictlyEqual ( x, y )
pub open spec fn spec_strict_eq(x: SpecVal, y: SpecVal) -> bool {
    match (x, y) {
        (SpecVal::Undefined, SpecVal::Undefined) => true,
        (SpecVal::Null, SpecVal::Null) => true,
        (SpecVal::Bool(a), SpecVal::Bool(b)) => a == b,
        (SpecVal::Number(a), SpecVal::Number(b)) => spec_num_equal(a, b),
        (SpecVal::Str(a), SpecVal::Str(b)) => a == b,
        (SpecVal::Object(a), SpecVal::Object(b)) => a == b,
        _ => false,
    }
}

pub fn val_strict_eq(x: &Val, y: &Val) -> (r: bool)
    ensures r == spec_strict_eq(x@, y@),
{
    match (x, y) {
        (Val::Undefined, Val::Undefined) => true,
        (Val::Null, Val::Null) => true,
        (Val::Bool(a), Val::Bool(b)) => *a == *b,
        (Val::Number(a), Val::Number(b)) => num_equal(*a, *b),
        (Val::Str(a), Val::Str(b)) => js_str_eq(a, b),
        (Val::Object(a), Val::Object(b)) => a.0 == b.0,
        _ => false,
    }
}

/// §7.2.10 SameValue ( x, y ) (`Object.is`)
pub open spec fn spec_same_value(x: SpecVal, y: SpecVal) -> bool {
    match (x, y) {
        (SpecVal::Undefined, SpecVal::Undefined) => true,
        (SpecVal::Null, SpecVal::Null) => true,
        (SpecVal::Bool(a), SpecVal::Bool(b)) => a == b,
        (SpecVal::Number(a), SpecVal::Number(b)) => spec_num_same_value(a, b),
        (SpecVal::Str(a), SpecVal::Str(b)) => a == b,
        (SpecVal::Object(a), SpecVal::Object(b)) => a == b,
        _ => false,
    }
}

pub fn val_same_value(x: &Val, y: &Val) -> (r: bool)
    ensures r == spec_same_value(x@, y@),
{
    match (x, y) {
        (Val::Undefined, Val::Undefined) => true,
        (Val::Null, Val::Null) => true,
        (Val::Bool(a), Val::Bool(b)) => *a == *b,
        (Val::Number(a), Val::Number(b)) => num_same_value(*a, *b),
        (Val::Str(a), Val::Str(b)) => js_str_eq(a, b),
        (Val::Object(a), Val::Object(b)) => a.0 == b.0,
        _ => false,
    }
}

/// §7.2.14 IsLooselyEqual on primitives (after any Object operand was already coerced via `ToPrimitive`
/// when compared against a primitive; two Objects compare by `ObjId` identity).
pub open spec fn spec_loose_eq_prim(x: SpecVal, y: SpecVal) -> bool {
    match (x, y) {
        (SpecVal::Undefined, SpecVal::Undefined) => true,
        (SpecVal::Null, SpecVal::Null) => true,
        (SpecVal::Undefined, SpecVal::Null) => true,
        (SpecVal::Null, SpecVal::Undefined) => true,
        (SpecVal::Bool(a), SpecVal::Bool(b)) => a == b,
        (SpecVal::Number(a), SpecVal::Number(b)) => spec_num_equal(a, b),
        (SpecVal::Str(a), SpecVal::Str(b)) => a == b,
        (SpecVal::Object(a), SpecVal::Object(b)) => a == b,
        (SpecVal::Number(a), SpecVal::Str(b)) => spec_num_equal(a, spec_string_to_number(b)),
        (SpecVal::Str(a), SpecVal::Number(b)) => spec_num_equal(spec_string_to_number(a), b),
        (SpecVal::Bool(a), _) => {
            let na = if a { JsNum(ONE_BITS) } else { JsNum(POS_ZERO_BITS) };
            match y {
                SpecVal::Number(b) => spec_num_equal(na, b),
                SpecVal::Str(b) => spec_num_equal(na, spec_string_to_number(b)),
                _ => false,
            }
        }
        (_, SpecVal::Bool(b)) => {
            let nb = if b { JsNum(ONE_BITS) } else { JsNum(POS_ZERO_BITS) };
            match x {
                SpecVal::Number(a) => spec_num_equal(a, nb),
                SpecVal::Str(a) => spec_num_equal(spec_string_to_number(a), nb),
                _ => false,
            }
        }
        _ => false,
    }
}

pub fn val_loose_eq_prim(x: &Val, y: &Val) -> (r: bool)
    ensures r == spec_loose_eq_prim(x@, y@),
{
    match (x, y) {
        (Val::Undefined, Val::Undefined) => true,
        (Val::Null, Val::Null) => true,
        (Val::Undefined, Val::Null) => true,
        (Val::Null, Val::Undefined) => true,
        (Val::Bool(a), Val::Bool(b)) => *a == *b,
        (Val::Number(a), Val::Number(b)) => num_equal(*a, *b),
        (Val::Str(a), Val::Str(b)) => js_str_eq(a, b),
        (Val::Object(a), Val::Object(b)) => a.0 == b.0,
        (Val::Number(a), Val::Str(b)) => num_equal(*a, string_to_js_num(b)),
        (Val::Str(a), Val::Number(b)) => num_equal(string_to_js_num(a), *b),
        (Val::Bool(a), _) => {
            let na = if *a { JsNum(ONE_BITS) } else { JsNum(POS_ZERO_BITS) };
            match y {
                Val::Number(b) => num_equal(na, *b),
                Val::Str(b) => num_equal(na, string_to_js_num(b)),
                _ => false,
            }
        }
        (_, Val::Bool(b)) => {
            let nb = if *b { JsNum(ONE_BITS) } else { JsNum(POS_ZERO_BITS) };
            match x {
                Val::Number(a) => num_equal(*a, nb),
                Val::Str(a) => num_equal(string_to_js_num(a), nb),
                _ => false,
            }
        }
        _ => false,
    }
}

} // verus!

