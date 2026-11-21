//! Formally verified ECMA-262 §7.1.4.1.1 `StringToNumber` -> IEEE-754 binary64 (`u64` bits)
//! round-to-nearest-ties-to-even (RNE) conversion, backed by canonical `BigNat` exact rational
//! arithmetic and unclamped mathematical exponent parsing (`spec_parse_exp_int`).
//!
//! Proves:
//! 1. `string_to_f64_bits(s) == spec_string_to_f64_bits(s@)` with zero truncation approximations;
//! 2. `BigNat` value soundness (`spec_bignat_val`) across `mul_add`, `pow10`, `shl_bits`, `bit_len`,
//!    `cmp`, `sub_ge`, and 53-step binary long division (`div53`);
//! 3. `theorem_rne_minimizes_distance_ties_to_even`: for any exact positive rational `N / D` in
//!    `[0, 2^53)`, `q_rne` minimizes `|q_rne * D - N|` over all integers `k: int` and breaks exact
//!    midpoint ties (`2 * rem == D`) uniquely to even (`q_rne % 2 == 0`).
use crate::value::{msb_u32, CANONICAL_NAN_BITS, NEG_ZERO_BITS, POS_ZERO_BITS};
#[cfg(verus_keep_ghost)]
use crate::value::{spec_msb_u32, spec_pow2};
use vstd::prelude::*;

verus! {

pub const POS_INF_BITS: u64 = 0x7ff0_0000_0000_0000u64;
pub const NEG_INF_BITS: u64 = 0xfff0_0000_0000_0000u64;

// ---------------------------------------------------------------------------------------
// 1. Powers of 2 / 2^32 and Canonical Little-Endian `BigNat` (`Vec<u32>`)
// ---------------------------------------------------------------------------------------

pub open spec fn spec_pow32(k: nat) -> nat
    decreases k,
{
    if k == 0 {
        1
    } else {
        0x1_0000_0000nat * spec_pow32((k - 1) as nat)
    }
}

pub open spec fn spec_bignat_wf(v: Seq<u32>) -> bool {
    v.len() == 0 || v.last() != 0u32
}

pub open spec fn spec_bignat_val(v: Seq<u32>) -> nat
    decreases v.len(),
{
    if v.len() == 0 {
        0
    } else {
        spec_bignat_val(v.drop_last()) + (v.last() as nat) * spec_pow32((v.len() - 1) as nat)
    }
}

pub proof fn lemma_pow2_pos(k: nat)
    ensures
        spec_pow2(k) >= 1,
    decreases k,
{
    if k > 0 {
        lemma_pow2_pos((k - 1) as nat);
    }
}

pub proof fn lemma_pow2_add(a: nat, b: nat)
    ensures
        spec_pow2(a + b) == spec_pow2(a) * spec_pow2(b),
    decreases a,
{
    if a == 0 {
        assert(0nat + b == b);
        assert(spec_pow2(0) == 1);
        assert(1nat * spec_pow2(b) == spec_pow2(b));
    } else {
        lemma_pow2_add((a - 1) as nat, b);
        assert(((a - 1) as nat) + b == (a + b - 1) as nat);
        let x = spec_pow2((a - 1) as nat);
        let y = spec_pow2(b);
        assert(spec_pow2(a) == 2 * x);
        assert(spec_pow2(a + b) == 2 * (x * y));
        assert(2 * (x * y) == (2 * x) * y) by (nonlinear_arith);
    }
}

pub proof fn lemma_pow2_mono(a: nat, b: nat)
    requires
        a <= b,
    ensures
        spec_pow2(a) <= spec_pow2(b),
    decreases b - a,
{
    if a < b {
        lemma_pow2_mono(a, (b - 1) as nat);
        lemma_pow2_pos((b - 1) as nat);
    }
}

pub proof fn lemma_pow32_eq_pow2(k: nat)
    ensures
        spec_pow32(k) == spec_pow2(32 * k),
        spec_pow32(k) >= 1,
    decreases k,
{
    if k == 0 {
        assert(32nat * 0nat == 0nat);
    } else {
        lemma_pow32_eq_pow2((k - 1) as nat);
        lemma_pow2_add(32nat, 32nat * ((k - 1) as nat));
        assert(32nat + 32nat * ((k - 1) as nat) == 32nat * k) by (nonlinear_arith)
            requires k >= 1;
        assert(spec_pow2(32) == 0x1_0000_0000nat) by {
            reveal_with_fuel(spec_pow2, 33);
        };
        let prev = spec_pow2(32nat * ((k - 1) as nat));
        assert(0x1_0000_0000nat * prev >= 1) by (nonlinear_arith)
            requires prev >= 1;
    }
}

pub proof fn lemma_bignat_upper_bound(v: Seq<u32>)
    ensures
        spec_bignat_val(v) < spec_pow32(v.len()),
    decreases v.len(),
{
    if v.len() == 0 {
        assert(spec_pow32(0) == 1);
    } else {
        let dl = v.drop_last();
        lemma_bignat_upper_bound(dl);
        let p = spec_pow32((v.len() - 1) as nat);
        lemma_pow32_eq_pow2((v.len() - 1) as nat);
        let top = v.last() as nat;
        assert(top <= 0xffff_ffffnat);
        assert(spec_pow32(v.len()) == 0x1_0000_0000nat * p);
        assert(spec_bignat_val(dl) + top * p < 0x1_0000_0000nat * p) by (nonlinear_arith)
            requires spec_bignat_val(dl) < p, top <= 0xffff_ffffnat, p >= 1;
    }
}

pub proof fn lemma_bignat_zero_iff_empty(v: Seq<u32>)
    requires
        spec_bignat_wf(v),
    ensures
        (spec_bignat_val(v) == 0) <==> (v.len() == 0),
{
    if v.len() > 0 {
        let p = spec_pow32((v.len() - 1) as nat);
        lemma_pow32_eq_pow2((v.len() - 1) as nat);
        let top = v.last() as nat;
        assert(top >= 1);
        assert(top * p >= 1) by (nonlinear_arith)
            requires top >= 1, p >= 1;
    }
}

pub open spec fn spec_normalize_limbs(v: Seq<u32>) -> Seq<u32>
    decreases v.len(),
{
    if v.len() == 0 {
        seq![]
    } else if v.last() == 0u32 {
        spec_normalize_limbs(v.drop_last())
    } else {
        v
    }
}

pub proof fn lemma_normalize_limbs_props(v: Seq<u32>)
    ensures
        spec_bignat_wf(spec_normalize_limbs(v)),
        spec_bignat_val(spec_normalize_limbs(v)) == spec_bignat_val(v),
    decreases v.len(),
{
    if v.len() > 0 && v.last() == 0u32 {
        let p = spec_pow32((v.len() - 1) as nat);
        assert(0nat * p == 0nat);
        lemma_normalize_limbs_props(v.drop_last());
    }
}

fn normalize_limbs(mut v: Vec<u32>) -> (out: Vec<u32>)
    ensures
        out@ == spec_normalize_limbs(v@),
        spec_bignat_wf(out@),
        spec_bignat_val(out@) == spec_bignat_val(v@),
{
    let ghost orig = v@;
    while v.len() > 0 && v[v.len() - 1] == 0u32
        invariant
            spec_normalize_limbs(orig) == spec_normalize_limbs(v@),
        decreases v@.len(),
    {
        let ghost before = v@;
        let _ = v.pop();
        proof {
            assert(before.last() == 0u32);
            assert(v@ =~= before.drop_last());
        }
    }
    proof {
        lemma_normalize_limbs_props(orig);
    }
    v
}

pub open spec fn spec_mul_add_loop(
    a: Seq<u32>,
    i: nat,
    m: u32,
    carry: u64,
    out: Seq<u32>,
) -> Seq<u32>
    decreases a.len() - i,
{
    if i >= a.len() {
        if carry > 0u64 {
            spec_normalize_limbs(out.push(carry as u32))
        } else {
            spec_normalize_limbs(out)
        }
    } else {
        let prod: nat = (a[i as int] as nat) * (m as nat) + (carry as nat);
        let lo: u32 = (prod % 0x1_0000_0000nat) as u32;
        let hi: u64 = (prod / 0x1_0000_0000nat) as u64;
        spec_mul_add_loop(a, i + 1, m, hi, out.push(lo))
    }
}

pub open spec fn spec_bignat_mul_add_u32(a: Seq<u32>, m: u32, addend: u32) -> Seq<u32> {
    spec_mul_add_loop(a, 0, m, addend as u64, seq![])
}

fn bignat_mul_add_u32(a: &Vec<u32>, m: u32, addend: u32) -> (out: Vec<u32>)
    ensures
        out@ == spec_bignat_mul_add_u32(a@, m, addend),
        spec_bignat_wf(out@),
        spec_bignat_val(out@) == spec_bignat_val(a@) * (m as nat) + (addend as nat),
{
    let n = a.len();
    let mut out: Vec<u32> = Vec::new();
    let mut carry: u64 = addend as u64;
    let mut i: usize = 0;
    proof {
        assert(a@.subrange(0, 0) =~= seq![]);
        assert(0nat * (m as nat) == 0nat) by (nonlinear_arith);
        assert(spec_pow32(0) == 1nat);
        assert((carry as nat) * 1nat == (addend as nat));
    }
    while i < n
        invariant
            i <= n,
            n == a@.len(),
            out@.len() == i as int,
            carry <= 0xffff_ffffu64,
            spec_bignat_mul_add_u32(a@, m, addend)
                == spec_mul_add_loop(a@, i as nat, m, carry, out@),
            spec_bignat_val(out@) + (carry as nat) * spec_pow32(i as nat)
                == spec_bignat_val(a@.subrange(0, i as int)) * (m as nat) + (addend as nat),
        decreases n - i,
    {
        let ai = a[i];
        proof {
            assert((ai as nat) * (m as nat) + (carry as nat) <= 0xffff_ffff_0000_0000nat) by (nonlinear_arith)
                requires ai <= 0xffff_ffffu32, m <= 0xffff_ffffu32, carry <= 0xffff_ffffu64;
        }
        let prod: u64 = (ai as u64) * (m as u64) + carry;
        let lo_u64: u64 = prod % 0x1_0000_0000u64;
        let hi: u64 = prod / 0x1_0000_0000u64;
        let lo: u32 = lo_u64 as u32;
        let ghost prev_out = out@;
        let ghost prev_carry = carry;
        out.push(lo);
        carry = hi;
        proof {
            assert(hi <= 0xffff_ffffu64);
            assert(out@.drop_last() =~= prev_out);
            assert(out@.last() == lo);
            let sub_next = a@.subrange(0, (i + 1) as int);
            let sub_cur = a@.subrange(0, i as int);
            assert(sub_next.drop_last() =~= sub_cur);
            assert(sub_next.last() == ai);

            let pi = spec_pow32(i as nat);
            let pi1 = spec_pow32((i + 1) as nat);
            assert(pi1 == 0x1_0000_0000nat * pi);
            let vo = spec_bignat_val(prev_out);
            let va = spec_bignat_val(sub_cur);
            assert((prod as nat) == (lo as nat) + 0x1_0000_0000nat * (hi as nat));
            assert((prod as nat) == (ai as nat) * (m as nat) + (prev_carry as nat));
            assert((vo + (lo as nat) * pi) + (hi as nat) * pi1
                == (va + (ai as nat) * pi) * (m as nat) + (addend as nat)) by (nonlinear_arith)
                requires
                    pi1 == 0x1_0000_0000nat * pi,
                    (lo as nat) + 0x1_0000_0000nat * (hi as nat) == (ai as nat) * (m as nat) + (prev_carry as nat),
                    vo + (prev_carry as nat) * pi == va * (m as nat) + (addend as nat);
        }
        i += 1;
    }
    proof {
        assert(a@.subrange(0, n as int) =~= a@);
    }
    if carry > 0u64 {
        let ghost prev_out = out@;
        out.push(carry as u32);
        proof {
            assert(out@.drop_last() =~= prev_out);
            assert(out@.last() == carry as u32);
        }
    } else {
        proof {
            let pn = spec_pow32(n as nat);
            assert(0nat * pn == 0nat) by (nonlinear_arith);
        }
    }
    normalize_limbs(out)
}

pub open spec fn spec_bignat_from_digits_loop(d: Seq<u8>, idx: nat, end: nat, acc: Seq<u32>) -> Seq<u32>
    decreases end - idx,
{
    if idx >= end || idx >= d.len() {
        acc
    } else {
        spec_bignat_from_digits_loop(
            d,
            idx + 1,
            end,
            spec_bignat_mul_add_u32(acc, 10u32, d[idx as int] as u32),
        )
    }
}

fn bignat_from_digits(d: &Vec<u8>, start: usize, end: usize) -> (out: Vec<u32>)
    requires
        start < end,
        end <= d@.len(),
        d@[start as int] != 0u8,
    ensures
        out@ == spec_bignat_from_digits_loop(d@, start as nat, end as nat, seq![]),
        spec_bignat_wf(out@),
        spec_bignat_val(out@) > 0,
        out@.len() > 0,
{
    let mut acc: Vec<u32> = Vec::new();
    let mut idx: usize = start;
    while idx < end
        invariant
            start <= idx <= end,
            end <= d@.len(),
            d@[start as int] != 0u8,
            spec_bignat_wf(acc@),
            idx > start ==> spec_bignat_val(acc@) > 0,
            spec_bignat_from_digits_loop(d@, start as nat, end as nat, seq![])
                == spec_bignat_from_digits_loop(d@, idx as nat, end as nat, acc@),
        decreases end - idx,
    {
        let dig = d[idx] as u32;
        let ghost prev_val = spec_bignat_val(acc@);
        acc = bignat_mul_add_u32(&acc, 10u32, dig);
        proof {
            if idx == start {
                assert(dig >= 1u32);
                assert(spec_bignat_val(acc@) >= 1);
            } else {
                assert(prev_val * 10nat + (dig as nat) >= 10) by (nonlinear_arith)
                    requires prev_val >= 1;
            }
        }
        idx += 1;
    }
    proof {
        lemma_bignat_zero_iff_empty(acc@);
    }
    acc
}

pub open spec fn spec_bignat_mul_pow10(acc: Seq<u32>, exp: nat) -> Seq<u32>
    decreases exp,
{
    if exp == 0 {
        acc
    } else {
        spec_bignat_mul_pow10(spec_bignat_mul_add_u32(acc, 10u32, 0u32), (exp - 1) as nat)
    }
}

fn bignat_mul_pow10(mut acc: Vec<u32>, mut exp: u128) -> (out: Vec<u32>)
    requires
        spec_bignat_wf(acc@),
        spec_bignat_val(acc@) > 0,
    ensures
        out@ == spec_bignat_mul_pow10(acc@, exp as nat),
        spec_bignat_wf(out@),
        spec_bignat_val(out@) > 0,
        out@.len() > 0,
{
    let ghost orig_acc = acc@;
    let ghost orig_exp = exp as nat;
    while exp > 0u128
        invariant
            spec_bignat_wf(acc@),
            spec_bignat_val(acc@) > 0,
            spec_bignat_mul_pow10(orig_acc, orig_exp)
                == spec_bignat_mul_pow10(acc@, exp as nat),
        decreases exp,
    {
        let ghost pv = spec_bignat_val(acc@);
        acc = bignat_mul_add_u32(&acc, 10u32, 0u32);
        proof {
            assert(pv * 10nat >= 10) by (nonlinear_arith)
                requires pv >= 1;
        }
        exp -= 1u128;
    }
    proof {
        lemma_bignat_zero_iff_empty(acc@);
    }
    acc
}

pub open spec fn spec_bignat_shl_bits(acc: Seq<u32>, bits: nat) -> Seq<u32>
    decreases bits,
{
    if bits == 0 {
        acc
    } else if bits >= 31 {
        spec_bignat_shl_bits(
            spec_bignat_mul_add_u32(acc, 0x8000_0000u32, 0u32),
            (bits - 31) as nat,
        )
    } else {
        spec_bignat_mul_add_u32(acc, (1u32 << (bits as u32)), 0u32)
    }
}

proof fn lemma_u32_shl_eq_pow2(k: u32)
    requires
        k <= 31u32,
    ensures
        ((1u32 << k) as nat) == spec_pow2(k as nat),
    decreases k,
{
    if k == 0u32 {
        assert((1u32 << 0u32) == 1u32) by (bit_vector);
    } else {
        let km1: u32 = (k - 1) as u32;
        lemma_u32_shl_eq_pow2(km1);
        assert(k > 0u32 && k <= 31u32 ==> (1u32 << k) == add(1u32 << sub(k, 1u32), 1u32 << sub(k, 1u32)) && (1u32 << sub(k, 1u32)) <= 0x4000_0000u32) by (bit_vector);
    }
}

proof fn lemma_msb_u32_pow2_bounds(top: u32)
    requires
        top > 0u32,
    ensures
        spec_msb_u32(top) <= 31u32,
        spec_pow2(spec_msb_u32(top) as nat) <= (top as nat),
        (top as nat) < spec_pow2((spec_msb_u32(top) + 1) as nat),
{
    let k = spec_msb_u32(top);
    assert( ({
        let a4: u32 = if top >= 0x0001_0000u32 { 16u32 } else { 0u32 };
        let m4: u32 = top >> a4;
        let a3: u32 = if m4 >= 0x0100u32 { 8u32 } else { 0u32 };
        let m3: u32 = m4 >> a3;
        let a2: u32 = if m3 >= 0x0010u32 { 4u32 } else { 0u32 };
        let m2: u32 = m3 >> a2;
        let a1: u32 = if m2 >= 0x0004u32 { 2u32 } else { 0u32 };
        let m1: u32 = m2 >> a1;
        let a0: u32 = if m1 >= 0x0002u32 { 1u32 } else { 0u32 };
        let kk: u64 = add(add(add(add(a4, a3), a2), a1), a0) as u64;
        top > 0u32 ==> (
            kk <= 31u64
            && (1u64 << kk) <= (top as u64)
            && (top as u64) < (1u64 << add(kk, 1u64))
        )
    }) ) by (bit_vector);
    lemma_u64_shl_eq_pow2(k as u64);
    lemma_u64_shl_eq_pow2((k + 1) as u64);
}

fn clone_limbs(a: &Vec<u32>) -> (out: Vec<u32>)
    ensures
        out@ == a@,
{
    let mut out: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a@.len(),
            out@ == a@.subrange(0, i as int),
        decreases a@.len() - i,
    {
        out.push(a[i]);
        proof {
            assert(a@.subrange(0, (i + 1) as int) =~= a@.subrange(0, i as int).push(a@[i as int]));
        }
        i += 1;
    }
    proof {
        assert(a@.subrange(0, a@.len() as int) =~= a@);
    }
    out
}

fn bignat_shl_bits(acc_ref: &Vec<u32>, mut bits: usize) -> (out: Vec<u32>)
    requires
        spec_bignat_wf(acc_ref@),
        spec_bignat_val(acc_ref@) > 0,
    ensures
        out@ == spec_bignat_shl_bits(acc_ref@, bits as nat),
        spec_bignat_wf(out@),
        spec_bignat_val(out@) == spec_bignat_val(acc_ref@) * spec_pow2(bits as nat),
        spec_bignat_val(out@) > 0,
        out@.len() > 0,
{
    let mut cur = clone_limbs(acc_ref);
    let ghost orig_bits: nat = bits as nat;
    let ghost mut done_bits: nat = 0;
    proof {
        assert(spec_pow2(0) == 1nat);
        assert(spec_bignat_val(acc_ref@) * 1nat == spec_bignat_val(acc_ref@));
        lemma_u32_shl_eq_pow2(31u32);
        assert((1u32 << 31u32) == 0x8000_0000u32) by (bit_vector);
    }
    while bits >= 31
        invariant
            done_bits + (bits as nat) == orig_bits,
            spec_bignat_wf(cur@),
            spec_pow2(31) == 0x8000_0000nat,
            spec_bignat_val(cur@) == spec_bignat_val(acc_ref@) * spec_pow2(done_bits),
            spec_bignat_shl_bits(acc_ref@, orig_bits)
                == spec_bignat_shl_bits(cur@, bits as nat),
        decreases bits,
    {
        cur = bignat_mul_add_u32(&cur, 0x8000_0000u32, 0u32);
        bits -= 31;
        proof {
            lemma_pow2_add(done_bits, 31nat);
            let base = spec_bignat_val(acc_ref@);
            let p_done = spec_pow2(done_bits);
            assert((base * p_done) * 0x8000_0000nat == base * (p_done * 0x8000_0000nat)) by (nonlinear_arith);
            done_bits = done_bits + 31nat;
        }
    }
    if bits > 0 {
        let b_u32: u32 = bits as u32;
        let factor: u32 = 1u32 << b_u32;
        cur = bignat_mul_add_u32(&cur, factor, 0u32);
        proof {
            lemma_u32_shl_eq_pow2(b_u32);
            lemma_pow2_add(done_bits, bits as nat);
            let base = spec_bignat_val(acc_ref@);
            let p_done = spec_pow2(done_bits);
            let p_rem = spec_pow2(bits as nat);
            assert((base * p_done) * p_rem == base * (p_done * p_rem)) by (nonlinear_arith);
        }
    }
    proof {
        lemma_pow2_pos(orig_bits);
        let base = spec_bignat_val(acc_ref@);
        let po = spec_pow2(orig_bits);
        assert(base * po >= 1) by (nonlinear_arith)
            requires base >= 1, po >= 1;
        lemma_bignat_zero_iff_empty(cur@);
    }
    cur
}

pub open spec fn spec_bignat_bit_len(a: Seq<u32>) -> nat {
    let hi = (a.len() - 1) as nat;
    let k = spec_msb_u32(a[hi as int]) as nat;
    hi * 32 + k + 1
}

fn bignat_bit_len(a: &Vec<u32>) -> (bl: u128)
    requires
        a@.len() > 0,
        spec_bignat_wf(a@),
    ensures
        bl as nat == spec_bignat_bit_len(a@),
        1u128 <= bl && bl <= 0x20_0000_0000_0000_0020u128,
        spec_pow2((bl - 1) as nat) <= spec_bignat_val(a@),
        spec_bignat_val(a@) < spec_pow2(bl as nat),
{
    let hi = a.len() - 1;
    let top = a[hi];
    let k = msb_u32(top);
    proof {
        assert(usize::BITS <= 64);
        assert(hi as u128 <= 0xffff_ffff_ffff_ffffu128);
    }
    let bl: u128 = (hi as u128) * 32u128 + (k as u128) + 1u128;
    proof {
        let dl = a@.drop_last();
        assert(a@.last() == top);
        lemma_bignat_upper_bound(dl);
        lemma_pow32_eq_pow2(hi as nat);
        lemma_msb_u32_pow2_bounds(top);
        let p_hi = spec_pow2(32 * (hi as nat));
        let pk = spec_pow2(k as nat);
        let pk1 = spec_pow2((k + 1) as nat);
        lemma_pow2_add(32 * (hi as nat), k as nat);
        lemma_pow2_add(32 * (hi as nat), (k + 1) as nat);
        let vdl = spec_bignat_val(dl);
        let tnat = top as nat;
        assert(p_hi * pk <= vdl + tnat * p_hi && vdl + tnat * p_hi < p_hi * pk1) by (nonlinear_arith)
            requires vdl < p_hi, pk <= tnat, tnat + 1 <= pk1, p_hi >= 1;
    }
    bl
}

pub open spec fn spec_cmp_same_len(a: Seq<u32>, b: Seq<u32>, k: nat) -> i8
    decreases k,
{
    if k == 0 {
        0i8
    } else {
        let idx = (k - 1) as int;
        if a[idx] < b[idx] {
            -1i8
        } else if a[idx] > b[idx] {
            1i8
        } else {
            spec_cmp_same_len(a, b, (k - 1) as nat)
        }
    }
}

pub open spec fn spec_bignat_cmp(a: Seq<u32>, b: Seq<u32>) -> i8 {
    if a.len() < b.len() {
        -1i8
    } else if a.len() > b.len() {
        1i8
    } else {
        spec_cmp_same_len(a, b, a.len())
    }
}

proof fn lemma_cmp_same_len_sound(a: Seq<u32>, b: Seq<u32>, k: nat)
    requires
        k <= a.len(),
        a.len() == b.len(),
    ensures
        spec_cmp_same_len(a, b, k) == 0i8
            ==> spec_bignat_val(a.subrange(0, k as int)) == spec_bignat_val(b.subrange(0, k as int)),
        spec_cmp_same_len(a, b, k) < 0i8
            ==> spec_bignat_val(a.subrange(0, k as int)) < spec_bignat_val(b.subrange(0, k as int)),
        spec_cmp_same_len(a, b, k) > 0i8
            ==> spec_bignat_val(a.subrange(0, k as int)) > spec_bignat_val(b.subrange(0, k as int)),
    decreases k,
{
    if k == 0 {
        assert(a.subrange(0, 0) =~= seq![]);
        assert(b.subrange(0, 0) =~= seq![]);
    } else {
        let idx = (k - 1) as int;
        let sa = a.subrange(0, k as int);
        let sb = b.subrange(0, k as int);
        let sa_prev = a.subrange(0, idx);
        let sb_prev = b.subrange(0, idx);
        assert(sa.drop_last() =~= sa_prev && sa.last() == a[idx]);
        assert(sb.drop_last() =~= sb_prev && sb.last() == b[idx]);
        let pk = spec_pow32((k - 1) as nat);
        lemma_pow32_eq_pow2((k - 1) as nat);
        if a[idx] < b[idx] {
            lemma_bignat_upper_bound(sa_prev);
            let va = spec_bignat_val(sa_prev);
            let vb = spec_bignat_val(sb_prev);
            let da = a[idx] as nat;
            let db = b[idx] as nat;
            assert(va + da * pk < vb + db * pk) by (nonlinear_arith)
                requires va < pk, da + 1 <= db, pk >= 1;
        } else if a[idx] > b[idx] {
            lemma_bignat_upper_bound(sb_prev);
            let va = spec_bignat_val(sa_prev);
            let vb = spec_bignat_val(sb_prev);
            let da = a[idx] as nat;
            let db = b[idx] as nat;
            assert(va + da * pk > vb + db * pk) by (nonlinear_arith)
                requires vb < pk, db + 1 <= da, pk >= 1;
        } else {
            lemma_cmp_same_len_sound(a, b, (k - 1) as nat);
        }
    }
}

proof fn lemma_pow32_mono(a: nat, b: nat)
    requires
        a <= b,
    ensures
        spec_pow32(a) <= spec_pow32(b),
{
    lemma_pow32_eq_pow2(a);
    lemma_pow32_eq_pow2(b);
    assert(32 * a <= 32 * b) by (nonlinear_arith)
        requires a <= b;
    lemma_pow2_mono(32 * a, 32 * b);
}

fn bignat_cmp(a: &Vec<u32>, b: &Vec<u32>) -> (res: i8)
    requires
        spec_bignat_wf(a@),
        spec_bignat_wf(b@),
    ensures
        res == spec_bignat_cmp(a@, b@),
        (res < 0i8) <==> (spec_bignat_val(a@) < spec_bignat_val(b@)),
        (res == 0i8) <==> (spec_bignat_val(a@) == spec_bignat_val(b@)),
        (res > 0i8) <==> (spec_bignat_val(a@) > spec_bignat_val(b@)),
{
    if a.len() < b.len() {
        proof {
            lemma_bignat_upper_bound(a@);
            lemma_pow32_mono(a@.len(), (b@.len() - 1) as nat);
            let pb = spec_pow32((b@.len() - 1) as nat);
            lemma_pow32_eq_pow2((b@.len() - 1) as nat);
            let top_b = b@.last() as nat;
            assert(top_b >= 1);
            assert(top_b * pb >= pb) by (nonlinear_arith)
                requires top_b >= 1, pb >= 1;
        }
        return -1i8;
    }
    if a.len() > b.len() {
        proof {
            lemma_bignat_upper_bound(b@);
            lemma_pow32_mono(b@.len(), (a@.len() - 1) as nat);
            let pa = spec_pow32((a@.len() - 1) as nat);
            lemma_pow32_eq_pow2((a@.len() - 1) as nat);
            let top_a = a@.last() as nat;
            assert(top_a >= 1);
            assert(top_a * pa >= pa) by (nonlinear_arith)
                requires top_a >= 1, pa >= 1;
        }
        return 1i8;
    }
    let mut k: usize = a.len();
    while k > 0
        invariant
            k <= a@.len(),
            a@.len() == b@.len(),
            spec_cmp_same_len(a@, b@, a@.len()) == spec_cmp_same_len(a@, b@, k as nat),
        decreases k,
    {
        let idx = k - 1;
        if a[idx] < b[idx] {
            proof {
                lemma_cmp_same_len_sound(a@, b@, a@.len());
                assert(a@.subrange(0, a@.len() as int) =~= a@);
                assert(b@.subrange(0, b@.len() as int) =~= b@);
            }
            return -1i8;
        } else if a[idx] > b[idx] {
            proof {
                lemma_cmp_same_len_sound(a@, b@, a@.len());
                assert(a@.subrange(0, a@.len() as int) =~= a@);
                assert(b@.subrange(0, b@.len() as int) =~= b@);
            }
            return 1i8;
        }
        k -= 1;
    }
    proof {
        lemma_cmp_same_len_sound(a@, b@, a@.len());
        assert(a@.subrange(0, a@.len() as int) =~= a@);
        assert(b@.subrange(0, b@.len() as int) =~= b@);
    }
    0i8
}

pub open spec fn spec_sub_loop(
    a: Seq<u32>,
    b: Seq<u32>,
    i: nat,
    borrow: i64,
    out: Seq<u32>,
) -> Seq<u32>
    decreases a.len() - i,
{
    if i >= a.len() {
        spec_normalize_limbs(out)
    } else {
        let bi: int = if i < b.len() { b[i as int] as int } else { 0 };
        let diff: int = (a[i as int] as int) - bi - (borrow as int);
        let (limb, next_borrow): (u32, i64) = if diff < 0 {
            ((diff + 0x1_0000_0000int) as u32, 1i64)
        } else {
            (diff as u32, 0i64)
        };
        spec_sub_loop(a, b, i + 1, next_borrow, out.push(limb))
    }
}

pub open spec fn spec_bignat_sub_ge(a: Seq<u32>, b: Seq<u32>) -> Seq<u32> {
    spec_sub_loop(a, b, 0, 0i64, seq![])
}

fn bignat_sub_ge(a: &Vec<u32>, b: &Vec<u32>) -> (out: Vec<u32>)
    requires
        spec_bignat_wf(a@),
        spec_bignat_wf(b@),
        spec_bignat_val(a@) >= spec_bignat_val(b@),
    ensures
        out@ == spec_bignat_sub_ge(a@, b@),
        spec_bignat_wf(out@),
        spec_bignat_val(out@) + spec_bignat_val(b@) == spec_bignat_val(a@),
{
    proof {
        if b@.len() > a@.len() {
            lemma_bignat_upper_bound(a@);
            lemma_pow32_mono(a@.len(), (b@.len() - 1) as nat);
            let pb = spec_pow32((b@.len() - 1) as nat);
            lemma_pow32_eq_pow2((b@.len() - 1) as nat);
            let top_b = b@.last() as nat;
            assert(top_b >= 1);
            assert(top_b * pb >= pb) by (nonlinear_arith)
                requires top_b >= 1, pb >= 1;
            assert(false);
        }
    }
    let n = a.len();
    let m = b.len();
    let mut out: Vec<u32> = Vec::new();
    let mut borrow: i64 = 0i64;
    let mut i: usize = 0;
    proof {
        assert(a@.subrange(0, 0) =~= seq![]);
        assert(b@.subrange(0, 0) =~= seq![]);
        assert(0nat * spec_pow32(0) == 0nat);
    }
    while i < n
        invariant
            i <= n,
            m <= n,
            n == a@.len(),
            m == b@.len(),
            out@.len() == i as int,
            borrow == 0i64 || borrow == 1i64,
            spec_bignat_sub_ge(a@, b@) == spec_sub_loop(a@, b@, i as nat, borrow, out@),
            spec_bignat_val(out@)
                + spec_bignat_val(b@.subrange(0, if i <= m { i as int } else { m as int }))
                == spec_bignat_val(a@.subrange(0, i as int)) + (borrow as nat) * spec_pow32(i as nat),
        decreases n - i,
    {
        let ai: i64 = a[i] as i64;
        let bi: i64 = if i < m { b[i] as i64 } else { 0i64 };
        let diff: i64 = ai - bi - borrow;
        let (limb, next_borrow): (u32, i64) = if diff < 0i64 {
            ((diff + 0x1_0000_0000i64) as u32, 1i64)
        } else {
            (diff as u32, 0i64)
        };
        let ghost prev_out = out@;
        let ghost prev_borrow = borrow;
        out.push(limb);
        borrow = next_borrow;
        proof {
            assert(out@.drop_last() =~= prev_out && out@.last() == limb);
            let sa_next = a@.subrange(0, (i + 1) as int);
            let sa_cur = a@.subrange(0, i as int);
            assert(sa_next.drop_last() =~= sa_cur && sa_next.last() == a[i as int]);
            let sb_cur = b@.subrange(0, if i <= m { i as int } else { m as int });
            let sb_next = b@.subrange(0, if i + 1 <= m { (i + 1) as int } else { m as int });
            if i < m {
                assert(sb_next.drop_last() =~= sb_cur && sb_next.last() == b[i as int]);
            } else {
                assert(sb_next =~= sb_cur);
                assert(bi == 0i64);
            }
            let pi = spec_pow32(i as nat);
            let pi1 = spec_pow32((i + 1) as nat);
            assert(pi1 == 0x1_0000_0000nat * pi);
            let vo = spec_bignat_val(prev_out);
            let va = spec_bignat_val(sa_cur);
            let vb = spec_bignat_val(sb_cur);
            let vb_next = spec_bignat_val(sb_next);
            let bi_nat: nat = bi as nat;
            if i < m {
                assert(vb_next == vb + bi_nat * pi);
            } else {
                assert(vb_next == vb);
                assert(bi_nat == 0nat);
                assert(0nat * pi == 0nat) by (nonlinear_arith);
                assert(vb_next == vb + bi_nat * pi);
            }
            let limb_nat: nat = limb as nat;
            let ai_nat: nat = a[i as int] as nat;
            let pb_nat: nat = prev_borrow as nat;
            let nb_nat: nat = next_borrow as nat;
            assert(limb_nat + bi_nat + pb_nat == ai_nat + nb_nat * 0x1_0000_0000nat);
            assert((vo + limb_nat * pi) + vb_next
                == (va + ai_nat * pi) + nb_nat * pi1) by (nonlinear_arith)
                requires
                    pi1 == 0x1_0000_0000nat * pi,
                    vb_next == vb + bi_nat * pi,
                    vo + vb == va + pb_nat * pi,
                    limb_nat + bi_nat + pb_nat == ai_nat + nb_nat * 0x1_0000_0000nat;
        }
        i += 1;
    }
    proof {
        assert(a@.subrange(0, n as int) =~= a@);
        assert(b@.subrange(0, m as int) =~= b@);
        let pn = spec_pow32(n as nat);
        if borrow == 1i64 {
            lemma_bignat_upper_bound(out@);
            let vo = spec_bignat_val(out@);
            let va = spec_bignat_val(a@);
            let vb = spec_bignat_val(b@);
            assert(out@.len() == n as int);
            assert(vo < pn);
            assert(1nat * pn == pn) by (nonlinear_arith);
            assert(vo + vb == va + pn);
            assert(va < vb);
            assert(false);
        }
        assert(borrow == 0i64);
        assert(0nat * pn == 0nat) by (nonlinear_arith);
    }
    normalize_limbs(out)
}

// ---------------------------------------------------------------------------------------
// 2. 53-Step Binary Long Division (`div53`) & RNE Distance-Minimization Theorem
// ---------------------------------------------------------------------------------------

/// Theorem: Round-to-nearest-ties-to-even (`q_rne`) minimizes `|q_rne * D - N|` over ALL integers
/// `k: int`, and when another integer `k != q_rne` ties (`|k * D - N| == |q_rne * D - N|`),
/// `q_rne` is uniquely even (`q_rne % 2 == 0`).
pub open spec fn spec_abs_int(x: int) -> nat {
    if x >= 0 { x as nat } else { (-x) as nat }
}

pub proof fn theorem_rne_minimizes_distance_ties_to_even(
    n_val: nat,
    d_val: nat,
    q: u64,
    rem: nat,
    k: int,
)
    requires
        d_val > 0,
        n_val == (q as nat) * d_val + rem,
        rem < d_val,
        q < 0x0020_0000_0000_0000u64,
    ensures
        ({
            let round_up = (2 * rem > d_val) || (2 * rem == d_val && (q & 1u64) == 1u64);
            let q_rne: int = if round_up { (q as int) + 1 } else { q as int };
            let err_rne = spec_abs_int(q_rne * (d_val as int) - (n_val as int));
            let err_k = spec_abs_int(k * (d_val as int) - (n_val as int));
            err_rne <= err_k
            && ((err_rne == err_k && k != q_rne) ==> (q_rne % 2 == 0))
        }),
{
    assert(((q & 1u64) == 1u64) <==> ((q as int) % 2 == 1)) by {
        assert(((q & 1u64) == 1u64) <==> (q % 2u64 == 1u64)) by (bit_vector);
    };
    let round_up = (2 * rem > d_val) || (2 * rem == d_val && (q & 1u64) == 1u64);
    let q_rne: int = if round_up { (q as int) + 1 } else { q as int };
    let qi = q as int;
    let di = d_val as int;
    let ni = n_val as int;
    let ri = rem as int;
    if k <= qi {
        assert(ni - k * di == (qi - k) * di + ri) by (nonlinear_arith)
            requires ni == qi * di + ri;
        assert((qi - k) * di >= 0) by (nonlinear_arith)
            requires k <= qi, di > 0;
        if k < qi {
            assert((qi - k) * di >= di) by (nonlinear_arith)
                requires qi - k >= 1, di > 0;
        }
    } else {
        assert(k * di - ni == (k - qi - 1) * di + (di - ri)) by (nonlinear_arith)
            requires ni == qi * di + ri;
        assert((k - qi - 1) * di >= 0) by (nonlinear_arith)
            requires k >= qi + 1, di > 0;
        if k > qi + 1 {
            assert((k - qi - 1) * di >= di) by (nonlinear_arith)
                requires k - qi - 1 >= 1, di > 0;
        }
    }
    if round_up {
        assert(q_rne * di - ni == di - ri) by (nonlinear_arith)
            requires q_rne == qi + 1, ni == qi * di + ri;
        if 2 * rem == d_val {
            assert(((qi + 1) % 2) == 0);
        }
    } else {
        assert(ni - q_rne * di == ri) by (nonlinear_arith)
            requires q_rne == qi, ni == qi * di + ri;
        if 2 * rem == d_val {
            assert((qi % 2) == 0);
        }
    }
}

pub open spec fn spec_div53_loop(
    rem: Seq<u32>,
    d: Seq<u32>,
    bit_plus_one: nat,
    q: u64,
) -> (u64, Seq<u32>)
    decreases bit_plus_one,
{
    if bit_plus_one == 0 {
        (q, rem)
    } else {
        let bit: nat = (bit_plus_one - 1) as nat;
        let trial = spec_bignat_shl_bits(d, bit);
        if spec_bignat_cmp(rem, trial) >= 0i8 {
            let next_rem = spec_bignat_sub_ge(rem, trial);
            let next_q: u64 = add(mul(q, 2u64), 1u64);
            spec_div53_loop(next_rem, d, bit, next_q)
        } else {
            let next_q: u64 = mul(q, 2u64);
            spec_div53_loop(rem, d, bit, next_q)
        }
    }
}

fn div53(n_big: Vec<u32>, d_big: &Vec<u32>) -> (res: (u64, Vec<u32>))
    requires
        spec_bignat_wf(n_big@),
        spec_bignat_wf(d_big@),
        spec_bignat_val(d_big@) > 0,
        spec_bignat_val(n_big@) < spec_bignat_val(d_big@) * spec_pow2(53),
    ensures
        res.0 == spec_div53_loop(n_big@, d_big@, 53, 0u64).0,
        res.1@ == spec_div53_loop(n_big@, d_big@, 53, 0u64).1,
        spec_bignat_wf(res.1@),
        res.0 < 0x0020_0000_0000_0000u64,
        spec_bignat_val(n_big@) == (res.0 as nat) * spec_bignat_val(d_big@) + spec_bignat_val(res.1@),
        spec_bignat_val(res.1@) < spec_bignat_val(d_big@),
{
    let ghost orig_n = n_big@;
    let ghost d_val = spec_bignat_val(d_big@);
    let mut rem: Vec<u32> = n_big;
    let mut q: u64 = 0u64;
    let mut bpo: usize = 53;
    proof {
        assert(spec_pow2(0) == 1nat);
        assert(0nat * (d_val * spec_pow2(53)) == 0nat) by (nonlinear_arith);
        lemma_u64_shl_eq_pow2(53u64);
        assert((1u64 << 53u64) == 0x0020_0000_0000_0000u64) by (bit_vector);
    }
    while bpo > 0
        invariant
            bpo <= 53,
            spec_bignat_wf(rem@),
            spec_bignat_wf(d_big@),
            d_val == spec_bignat_val(d_big@),
            d_val > 0,
            spec_pow2(53) == 0x0020_0000_0000_0000nat,
            (q as nat) < spec_pow2((53 - bpo) as nat),
            spec_bignat_val(orig_n)
                == (q as nat) * (d_val * spec_pow2(bpo as nat)) + spec_bignat_val(rem@),
            spec_bignat_val(rem@) < d_val * spec_pow2(bpo as nat),
            spec_div53_loop(orig_n, d_big@, 53, 0u64)
                == spec_div53_loop(rem@, d_big@, bpo as nat, q),
        decreases bpo,
    {
        let bit: usize = bpo - 1;
        let trial = bignat_shl_bits(d_big, bit);
        let ghost p_bit = spec_pow2(bit as nat);
        let ghost p_done = spec_pow2((53 - bpo) as nat);
        proof {
            assert(spec_pow2(bpo as nat) == 2 * p_bit);
            assert(spec_pow2((53 - bit) as nat) == 2 * p_done);
            lemma_pow2_mono((53 - bpo) as nat, 52nat);
            lemma_u64_shl_eq_pow2(52u64);
            assert((1u64 << 52u64) == 0x0010_0000_0000_0000u64) by (bit_vector);
            assert(q < 0x0010_0000_0000_0000u64);
        }
        if bignat_cmp(&rem, &trial) >= 0i8 {
            let ghost prev_rem_val = spec_bignat_val(rem@);
            let ghost prev_q = q;
            rem = bignat_sub_ge(&rem, &trial);
            q = q * 2u64 + 1u64;
            proof {
                assert(q == add(mul(prev_q, 2u64), 1u64)) by {
                    assert(prev_q < 0x0010_0000_0000_0000u64 ==> add(mul(prev_q, 2u64), 1u64) == prev_q * 2u64 + 1u64) by (bit_vector);
                };
                let new_rem_val = spec_bignat_val(rem@);
                assert(new_rem_val + d_val * p_bit == prev_rem_val);
                assert((q as nat) < 2 * p_done);
                assert(((prev_q as nat) * 2 + 1) * (d_val * p_bit) + new_rem_val
                    == (prev_q as nat) * (d_val * (2 * p_bit)) + prev_rem_val) by (nonlinear_arith)
                    requires new_rem_val + d_val * p_bit == prev_rem_val;
                assert(new_rem_val < d_val * p_bit) by (nonlinear_arith)
                    requires prev_rem_val < d_val * (2 * p_bit), new_rem_val + d_val * p_bit == prev_rem_val;
            }
        } else {
            let ghost prev_q = q;
            q = q * 2u64;
            proof {
                assert(q == mul(prev_q, 2u64)) by {
                    assert(prev_q < 0x0010_0000_0000_0000u64 ==> mul(prev_q, 2u64) == prev_q * 2u64) by (bit_vector);
                };
                assert((q as nat) < 2 * p_done);
                let rem_val = spec_bignat_val(rem@);
                assert(((prev_q as nat) * 2) * (d_val * p_bit) + rem_val
                    == (prev_q as nat) * (d_val * (2 * p_bit)) + rem_val) by (nonlinear_arith);
            }
        }
        bpo = bit;
    }
    proof {
        assert(spec_pow2(0) == 1nat);
        assert(d_val * 1nat == d_val);
    }
    (q, rem)
}

proof fn lemma_u64_shl_eq_pow2(k: u64)
    requires
        k <= 53u64,
    ensures
        ((1u64 << k) as nat) == spec_pow2(k as nat),
    decreases k,
{
    if k == 0u64 {
        assert((1u64 << 0u64) == 1u64) by (bit_vector);
    } else {
        let km1: u64 = (k - 1) as u64;
        lemma_u64_shl_eq_pow2(km1);
        assert(k > 0u64 && k <= 53u64 ==> (1u64 << k) == add(1u64 << sub(k, 1u64), 1u64 << sub(k, 1u64)) && (1u64 << sub(k, 1u64)) <= 0x0010_0000_0000_0000u64) by (bit_vector);
    }
}

pub open spec fn spec_ge_pow2(num: Seq<u32>, den: Seq<u32>, shift: int) -> bool {
    if shift >= 0 {
        spec_bignat_cmp(num, spec_bignat_shl_bits(den, shift as nat)) >= 0i8
    } else {
        spec_bignat_cmp(spec_bignat_shl_bits(num, (-shift) as nat), den) >= 0i8
    }
}

fn ge_pow2(num: &Vec<u32>, den: &Vec<u32>, shift: i32) -> (r: bool)
    requires
        spec_bignat_wf(num@),
        spec_bignat_wf(den@),
        spec_bignat_val(num@) > 0,
        spec_bignat_val(den@) > 0,
        -1100 <= shift <= 1100,
    ensures
        r == spec_ge_pow2(num@, den@, shift as int),
        shift >= 0 ==> (r <==> spec_bignat_val(num@) >= spec_bignat_val(den@) * spec_pow2(shift as nat)),
        shift < 0 ==> (r <==> spec_bignat_val(num@) * spec_pow2((-shift) as nat) >= spec_bignat_val(den@)),
{
    if shift >= 0 {
        let shifted = bignat_shl_bits(den, shift as usize);
        bignat_cmp(num, &shifted) >= 0i8
    } else {
        let shifted = bignat_shl_bits(num, (-shift) as usize);
        bignat_cmp(&shifted, den) >= 0i8
    }
}

pub open spec fn spec_pack_rational_f64_rne(
    neg: bool,
    num: Seq<u32>,
    den: Seq<u32>,
) -> u64 {
    let nb: int = spec_bignat_bit_len(num) as int;
    let db: int = spec_bignat_bit_len(den) as int;
    let cand: int = nb - db;
    let sign_mask: u64 = if neg { NEG_ZERO_BITS } else { POS_ZERO_BITS };
    if cand > 1024 {
        if neg { NEG_INF_BITS } else { POS_INF_BITS }
    } else if cand < -1075 {
        sign_mask
    } else {
        let e2: int = if spec_ge_pow2(num, den, cand) { cand } else { cand - 1 };
        if e2 > 1023 {
            if neg { NEG_INF_BITS } else { POS_INF_BITS }
        } else if e2 < -1075 {
            sign_mask
        } else {
            let ulp_exp: int = if e2 - 52 > -1074 { e2 - 52 } else { -1074 };
            let (n_big, d_big) = if ulp_exp >= 0 {
                (num, spec_bignat_shl_bits(den, ulp_exp as nat))
            } else {
                (spec_bignat_shl_bits(num, (-ulp_exp) as nat), den)
            };
            let (q, rem) = spec_div53_loop(n_big, d_big, 53, 0u64);
            let two_rem = if rem.len() == 0 {
                seq![]
            } else {
                spec_bignat_shl_bits(rem, 1)
            };
            let cmp = spec_bignat_cmp(two_rem, d_big);
            let q_rne: u64 = if cmp > 0i8 || (cmp == 0i8 && (q & 1u64) == 1u64) {
                add(q, 1u64)
            } else {
                q
            };
            let mag: u64 = if e2 < -1022 {
                q_rne
            } else {
                add((((e2 + 1022) as u64) << 52u64), q_rne)
            };
            mag | sign_mask
        }
    }
}

fn pack_rational_f64_rne(neg: bool, num: Vec<u32>, den: Vec<u32>) -> (bits: u64)
    requires
        num@.len() > 0,
        den@.len() > 0,
        spec_bignat_wf(num@),
        spec_bignat_wf(den@),
        spec_bignat_val(num@) > 0,
        spec_bignat_val(den@) > 0,
    ensures
        bits == spec_pack_rational_f64_rne(neg, num@, den@),
{
    let nb = bignat_bit_len(&num);
    let db = bignat_bit_len(&den);
    let cand_128: i128 = (nb as i128) - (db as i128);
    let sign_mask: u64 = if neg { NEG_ZERO_BITS } else { POS_ZERO_BITS };
    if cand_128 > 1024i128 {
        return if neg { NEG_INF_BITS } else { POS_INF_BITS };
    }
    if cand_128 < -1075i128 {
        return sign_mask;
    }
    let cand: i32 = cand_128 as i32;
    let ge = ge_pow2(&num, &den, cand);
    let e2: i32 = if ge { cand } else { cand - 1 };
    if e2 > 1023 {
        return if neg { NEG_INF_BITS } else { POS_INF_BITS };
    }
    if e2 < -1075 {
        return sign_mask;
    }
    proof {
        // Prove `num / den < 2^(e2 + 1)`:
        let nv = spec_bignat_val(num@);
        let dv = spec_bignat_val(den@);
        let n_hi = spec_pow2(nb as nat);
        let d_lo = spec_pow2((db - 1) as nat);
        assert(nv < n_hi && d_lo <= dv);
        if ge {
            // e2 == cand == nb - db, so e2 + 1 == nb - (db - 1) >= 0 since cand >= -1075?
            if e2 + 1 >= 0 {
                let s = (e2 + 1) as nat;
                lemma_pow2_add((db - 1) as nat, s);
                assert(((db - 1) as nat) + s == (nb as nat));
                let ps = spec_pow2(s);
                assert(nv < dv * ps) by (nonlinear_arith)
                    requires nv < d_lo * ps, d_lo <= dv, ps >= 0;
            } else {
                let s = (-(e2 + 1)) as nat;
                lemma_pow2_add(nb as nat, s);
                assert((nb as nat) + s == ((db - 1) as nat));
                let ps = spec_pow2(s);
                lemma_pow2_pos(s);
                assert(nv * ps < dv) by (nonlinear_arith)
                    requires nv < n_hi, n_hi * ps == d_lo, d_lo <= dv, ps >= 1;
            }
        } else {
            // !ge, so e2 + 1 == cand
            if cand >= 0 {
                assert(nv < dv * spec_pow2(cand as nat));
            } else {
                assert(nv * spec_pow2((-cand) as nat) < dv);
            }
        }
    }
    let ulp_exp: i32 = if e2 - 52 > -1074 { e2 - 52 } else { -1074 };
    let (n_big, d_big): (Vec<u32>, Vec<u32>) = if ulp_exp >= 0 {
        let ds = bignat_shl_bits(&den, ulp_exp as usize);
        (num, ds)
    } else {
        let ns = bignat_shl_bits(&num, (-ulp_exp) as usize);
        (ns, den)
    };
    proof {
        // Prove `spec_bignat_val(n_big@) < spec_bignat_val(d_big@) * spec_pow2(53)`!
        // Note: ulp_exp >= e2 - 52, so 53 + ulp_exp >= e2 + 1!
        let nv = spec_bignat_val(num@);
        let dv = spec_bignat_val(den@);
        let diff_exp: nat = ((53 + ulp_exp) - (e2 + 1)) as nat;
        lemma_pow2_pos(diff_exp);
        if ulp_exp >= 0 {
            // e2 >= -51, so e2 + 1 >= -50. Actually ulp_exp >= 0 ==> e2 >= 52 ==> e2 + 1 == ulp_exp + 53!
            assert(ulp_exp == e2 - 52);
            assert(e2 + 1 == ulp_exp + 53);
            lemma_pow2_add(ulp_exp as nat, 53nat);
            let pu = spec_pow2(ulp_exp as nat);
            let p53 = spec_pow2(53nat);
            assert(nv < (dv * pu) * p53) by (nonlinear_arith)
                requires nv < dv * (pu * p53);
        } else {
            // ulp_exp < 0, n_big == nv * 2^(-ulp_exp), d_big == dv.
            // Want: nv * 2^(-ulp_exp) < dv * 2^53.
            let nu: nat = (-ulp_exp) as nat;
            if e2 + 1 >= 0 {
                // nv < dv * 2^(e2 + 1), and (-ulp_exp) + (e2 + 1) <= 53!
                let e1 = (e2 + 1) as nat;
                lemma_pow2_add(e1, nu);
                lemma_pow2_mono(e1 + nu, 53nat);
                let pnu = spec_pow2(nu);
                let pe1 = spec_pow2(e1);
                let p53 = spec_pow2(53nat);
                lemma_pow2_pos(nu);
                assert(nv * pnu < dv * p53) by (nonlinear_arith)
                    requires nv < dv * pe1, pe1 * pnu <= p53, pnu >= 1, dv >= 1;
            } else {
                // e2 + 1 < 0: nv * 2^(-(e2 + 1)) < dv.
                // Since -ulp_exp <= 53 + (-(e2 + 1)), multiply both sides by 2^(53 - diff):
                let m1 = (-(e2 + 1)) as nat;
                // nu == -ulp_exp, and nu <= 53 + m1, specifically m1 + (53 - diff_exp)? Wait:
                // 53 - nu + m1 == 53 + ulp_exp - (e2 + 1) == diff_exp >= 0!
                // Wait: nu <= 1074, so 53 + m1 == nu + diff_exp!
                assert(53nat + m1 == nu + diff_exp);
                lemma_pow2_add(53nat, m1);
                lemma_pow2_add(nu, diff_exp);
                let pm1 = spec_pow2(m1);
                let pnu = spec_pow2(nu);
                let pdiff = spec_pow2(diff_exp);
                let p53 = spec_pow2(53nat);
                lemma_pow2_pos(m1);
                // (nv * pnu) * pm1 == (nv * pm1) * pnu < dv * pnu <= dv * (pnu * pdiff) == dv * (p53 * pm1)!
                assert((nv * pnu) * pm1 < (dv * p53) * pm1) by (nonlinear_arith)
                    requires
                        nv * pm1 < dv,
                        pnu >= 1,
                        pdiff >= 1,
                        dv >= 1,
                        pnu * pdiff == p53 * pm1;
                assert(nv * pnu < dv * p53) by (nonlinear_arith)
                    requires (nv * pnu) * pm1 < (dv * p53) * pm1, pm1 >= 1;
            }
        }
    }
    let (q, rem) = div53(n_big, &d_big);
    let two_rem: Vec<u32> = if rem.len() == 0 {
        Vec::new()
    } else {
        proof {
            lemma_bignat_zero_iff_empty(rem@);
        }
        bignat_shl_bits(&rem, 1)
    };
    let cmp = bignat_cmp(&two_rem, &d_big);
    let q_rne: u64 = if cmp > 0i8 || (cmp == 0i8 && (q & 1u64) == 1u64) {
        q + 1u64
    } else {
        q
    };
    let mag: u64 = if e2 < -1022 {
        q_rne
    } else {
        let bias_u64: u64 = (e2 + 1022) as u64;
        proof {
            assert(bias_u64 <= 2045u64 ==> (bias_u64 << 52u64) <= 0x7fd0_0000_0000_0000u64) by (bit_vector);
        }
        (bias_u64 << 52u64) + q_rne
    };
    mag | sign_mask
}

fn make_bignat_one() -> (one: Vec<u32>)
    ensures
        one@ == seq![1u32],
        one@.len() == 1,
        spec_bignat_wf(one@),
        spec_bignat_val(one@) == 1nat,
{
    let mut one: Vec<u32> = Vec::new();
    one.push(1u32);
    proof {
        reveal_with_fuel(spec_bignat_val, 3);
        assert(one@ =~= seq![1u32]);
        assert(one@.drop_last() =~= seq![]);
        assert(spec_pow32(0) == 1nat);
    }
    one
}

pub open spec fn spec_is_str_white_space(c: u16) -> bool {
    c == 0x0009u16
        || c == 0x000Au16
        || c == 0x000Bu16
        || c == 0x000Cu16
        || c == 0x000Du16
        || c == 0x0020u16
        || c == 0x00A0u16
        || c == 0x1680u16
        || (0x2000u16 <= c && c <= 0x200Au16)
        || c == 0x2028u16
        || c == 0x2029u16
        || c == 0x202Fu16
        || c == 0x205Fu16
        || c == 0x3000u16
        || c == 0xFEFFu16
}

fn is_str_white_space(c: u16) -> (r: bool)
    ensures
        r == spec_is_str_white_space(c),
{
    c == 0x0009u16
        || c == 0x000Au16
        || c == 0x000Bu16
        || c == 0x000Cu16
        || c == 0x000Du16
        || c == 0x0020u16
        || c == 0x00A0u16
        || c == 0x1680u16
        || (c >= 0x2000u16 && c <= 0x200Au16)
        || c == 0x2028u16
        || c == 0x2029u16
        || c == 0x202Fu16
        || c == 0x205Fu16
        || c == 0x3000u16
        || c == 0xFEFFu16
}

pub open spec fn spec_trim_start_idx(s: Seq<u16>, idx: nat) -> nat
    decreases s.len() - idx,
{
    if idx < s.len() && spec_is_str_white_space(s[idx as int]) {
        spec_trim_start_idx(s, idx + 1)
    } else {
        idx
    }
}

pub open spec fn spec_trim_end_idx(s: Seq<u16>, start: nat, end: nat) -> nat
    decreases end - start,
{
    if end > start && end <= s.len() && spec_is_str_white_space(s[(end - 1) as int]) {
        spec_trim_end_idx(s, start, (end - 1) as nat)
    } else {
        end
    }
}

pub open spec fn spec_matches_infinity(s: Seq<u16>, pos: nat, end: nat) -> bool {
    end - pos == 8
        && end <= s.len()
        && s[pos as int] == 0x0049u16
        && s[(pos + 1) as int] == 0x006Eu16
        && s[(pos + 2) as int] == 0x0066u16
        && s[(pos + 3) as int] == 0x0069u16
        && s[(pos + 4) as int] == 0x006Eu16
        && s[(pos + 5) as int] == 0x0069u16
        && s[(pos + 6) as int] == 0x0074u16
        && s[(pos + 7) as int] == 0x0079u16
}

fn matches_infinity(s: &Vec<u16>, pos: usize, end: usize) -> (r: bool)
    requires
        pos <= end,
        end <= s@.len(),
    ensures
        r == spec_matches_infinity(s@, pos as nat, end as nat),
{
    end - pos == 8
        && s[pos] == 0x0049u16
        && s[pos + 1] == 0x006Eu16
        && s[pos + 2] == 0x0066u16
        && s[pos + 3] == 0x0069u16
        && s[pos + 4] == 0x006Eu16
        && s[pos + 5] == 0x0069u16
        && s[pos + 6] == 0x0074u16
        && s[pos + 7] == 0x0079u16
}

pub open spec fn spec_radix_digit_u16(c: u16, radix: u32) -> Option<u32> {
    if radix == 2 {
        if c == 0x0030u16 || c == 0x0031u16 {
            Some((c - 0x0030u16) as u32)
        } else {
            None
        }
    } else if radix == 8 {
        if 0x0030u16 <= c && c <= 0x0037u16 {
            Some((c - 0x0030u16) as u32)
        } else {
            None
        }
    } else {
        if 0x0030u16 <= c && c <= 0x0039u16 {
            Some((c - 0x0030u16) as u32)
        } else if 0x0041u16 <= c && c <= 0x0046u16 {
            Some((c - 0x0041u16 + 10u16) as u32)
        } else if 0x0061u16 <= c && c <= 0x0066u16 {
            Some((c - 0x0061u16 + 10u16) as u32)
        } else {
            None
        }
    }
}

fn radix_digit_u16(c: u16, radix: u32) -> (res: Option<u32>)
    requires
        radix == 2 || radix == 8 || radix == 16,
    ensures
        res == spec_radix_digit_u16(c, radix),
{
    if radix == 2 {
        if c == 0x0030u16 || c == 0x0031u16 {
            Some((c - 0x0030u16) as u32)
        } else {
            None
        }
    } else if radix == 8 {
        if c >= 0x0030u16 && c <= 0x0037u16 {
            Some((c - 0x0030u16) as u32)
        } else {
            None
        }
    } else {
        if c >= 0x0030u16 && c <= 0x0039u16 {
            Some((c - 0x0030u16) as u32)
        } else if c >= 0x0041u16 && c <= 0x0046u16 {
            Some((c - 0x0041u16 + 10u16) as u32)
        } else if c >= 0x0061u16 && c <= 0x0066u16 {
            Some((c - 0x0061u16 + 10u16) as u32)
        } else {
            None
        }
    }
}

pub open spec fn spec_all_radix_digits(s: Seq<u16>, pos: nat, end: nat, radix: u32) -> bool
    decreases end - pos,
{
    if pos >= end {
        true
    } else if pos >= s.len() {
        false
    } else {
        spec_radix_digit_u16(s[pos as int], radix) is Some
            && spec_all_radix_digits(s, pos + 1, end, radix)
    }
}

pub open spec fn spec_skip_zero_u16(s: Seq<u16>, pos: nat, end: nat) -> nat
    decreases end - pos,
{
    if pos < end && pos < s.len() && s[pos as int] == 0x0030u16 {
        spec_skip_zero_u16(s, pos + 1, end)
    } else {
        pos
    }
}

pub open spec fn spec_radix_bignat_loop(
    s: Seq<u16>,
    pos: nat,
    end: nat,
    radix: u32,
    acc: Seq<u32>,
) -> Seq<u32>
    decreases end - pos,
{
    if pos >= end || pos >= s.len() {
        acc
    } else {
        let d = spec_radix_digit_u16(s[pos as int], radix).unwrap();
        spec_radix_bignat_loop(s, pos + 1, end, radix, spec_bignat_mul_add_u32(acc, radix, d))
    }
}

pub open spec fn spec_parse_radix_f64_bits(
    s: Seq<u16>,
    start: nat,
    end: nat,
    radix: u32,
) -> u64 {
    if start >= end || !spec_all_radix_digits(s, start, end, radix) {
        CANONICAL_NAN_BITS
    } else {
        let nz = spec_skip_zero_u16(s, start, end);
        if nz >= end {
            POS_ZERO_BITS
        } else if end - nz > 1030 {
            POS_INF_BITS
        } else {
            let num = spec_radix_bignat_loop(s, nz, end, radix, seq![]);
            spec_pack_rational_f64_rne(false, num, seq![1u32])
        }
    }
}

fn parse_radix_f64_bits(s: &Vec<u16>, start: usize, end: usize, radix: u32) -> (bits: u64)
    requires
        start <= end,
        end <= s@.len(),
        radix == 2 || radix == 8 || radix == 16,
    ensures
        bits == spec_parse_radix_f64_bits(s@, start as nat, end as nat, radix),
{
    if start >= end {
        return CANONICAL_NAN_BITS;
    }
    let mut p: usize = start;
    while p < end
        invariant
            start <= p <= end,
            end <= s@.len(),
            radix == 2 || radix == 8 || radix == 16,
            spec_all_radix_digits(s@, start as nat, end as nat, radix)
                == spec_all_radix_digits(s@, p as nat, end as nat, radix),
            forall|k: int| start as int <= k < p as int ==> spec_radix_digit_u16(#[trigger] s@[k], radix) is Some,
        decreases end - p,
    {
        if radix_digit_u16(s[p], radix).is_none() {
            return CANONICAL_NAN_BITS;
        }
        p += 1;
    }
    let mut nz: usize = start;
    while nz < end && s[nz] == 0x0030u16
        invariant
            start <= nz <= end,
            end <= s@.len(),
            spec_skip_zero_u16(s@, start as nat, end as nat)
                == spec_skip_zero_u16(s@, nz as nat, end as nat),
        decreases end - nz,
    {
        nz += 1;
    }
    if nz >= end {
        return POS_ZERO_BITS;
    }
    if end - nz > 1030 {
        return POS_INF_BITS;
    }
    let mut num: Vec<u32> = Vec::new();
    let mut idx: usize = nz;
    while idx < end
        invariant
            start <= nz <= idx <= end,
            end <= s@.len(),
            radix == 2 || radix == 8 || radix == 16,
            s@[nz as int] != 0x0030u16,
            forall|k: int| start as int <= k < end as int ==> spec_radix_digit_u16(#[trigger] s@[k], radix) is Some,
            spec_bignat_wf(num@),
            idx > nz ==> spec_bignat_val(num@) > 0,
            spec_radix_bignat_loop(s@, nz as nat, end as nat, radix, seq![])
                == spec_radix_bignat_loop(s@, idx as nat, end as nat, radix, num@),
        decreases end - idx,
    {
        let d = radix_digit_u16(s[idx], radix).unwrap();
        let ghost prev_val = spec_bignat_val(num@);
        num = bignat_mul_add_u32(&num, radix, d);
        proof {
            if idx == nz {
                assert(spec_radix_digit_u16(s@[nz as int], radix) == Some(d));
                assert(d >= 1u32);
                assert(spec_bignat_val(num@) >= 1);
            } else {
                assert(prev_val * (radix as nat) + (d as nat) >= 2) by (nonlinear_arith)
                    requires prev_val >= 1, radix >= 2;
            }
        }
        idx += 1;
    }
    let den = make_bignat_one();
    proof {
        lemma_bignat_zero_iff_empty(num@);
    }
    pack_rational_f64_rne(false, num, den)
}

pub open spec fn spec_scan_dec_digits_end(s: Seq<u16>, pos: nat, end: nat) -> nat
    decreases end - pos,
{
    if pos < end && pos < s.len() && 0x0030u16 <= s[pos as int] && s[pos as int] <= 0x0039u16 {
        spec_scan_dec_digits_end(s, pos + 1, end)
    } else {
        pos
    }
}

fn scan_dec_digits_end(s: &Vec<u16>, start: usize, end: usize) -> (pos: usize)
    requires
        start <= end,
        end <= s@.len(),
    ensures
        start <= pos <= end,
        pos as nat == spec_scan_dec_digits_end(s@, start as nat, end as nat),
        forall|k: int| start as int <= k < pos as int ==> 0x0030u16 <= (#[trigger] s@[k]) && s@[k] <= 0x0039u16,
{
    let mut pos: usize = start;
    while pos < end && s[pos] >= 0x0030u16 && s[pos] <= 0x0039u16
        invariant
            start <= pos <= end,
            end <= s@.len(),
            spec_scan_dec_digits_end(s@, start as nat, end as nat)
                == spec_scan_dec_digits_end(s@, pos as nat, end as nat),
            forall|k: int| start as int <= k < pos as int ==> 0x0030u16 <= (#[trigger] s@[k]) && s@[k] <= 0x0039u16,
        decreases end - pos,
    {
        pos += 1;
    }
    pos
}

/// Exact unclamped mathematical unsigned exponent parser over `s[pos..end]`.
pub open spec fn spec_parse_exp_int(
    s: Seq<u16>,
    pos: nat,
    end: nat,
    acc: int,
) -> Option<int>
    decreases end - pos,
{
    if pos >= end {
        Some(acc)
    } else if pos >= s.len() || !(0x0030u16 <= s[pos as int] && s[pos as int] <= 0x0039u16) {
        None
    } else {
        let d = (s[pos as int] - 0x0030u16) as int;
        spec_parse_exp_int(s, pos + 1, end, acc * 10 + d)
    }
}

/// Executive exponent parser saturating `acc: i128` only above `2 * (end as i128) + 2000`, proved
/// equivalent to unclamped `spec_parse_exp_int` across `sci_exp10 > 309` and `sci_exp10 < -325`.
fn parse_clamped_exp(s: &Vec<u16>, start: usize, end: usize) -> (res: Option<i128>)
    requires
        start < end,
        end <= s@.len(),
    ensures
        res is None <==> spec_parse_exp_int(s@, start as nat, end as nat, 0) is None,
        res is Some ==> ({
            let exact = spec_parse_exp_int(s@, start as nat, end as nat, 0).unwrap();
            let cl = res.unwrap() as int;
            let lim = 2 * (end as int) + 2000;
            0 <= cl && cl <= lim * 10 + 9
            && (cl < lim ==> cl == exact)
            && (cl >= lim ==> exact >= lim)
        }),
{
    let limit: i128 = 2i128 * (end as i128) + 2000i128;
    let mut pos: usize = start;
    let mut acc: i128 = 0;
    let ghost mut exact_acc: int = 0;
    while pos < end
        invariant
            start <= pos <= end,
            end <= s@.len(),
            limit as int == 2 * (end as int) + 2000,
            0 <= acc as int <= (limit as int) * 10 + 9,
            (acc as int) <= exact_acc,
            (acc < limit) ==> (acc as int == exact_acc),
            spec_parse_exp_int(s@, start as nat, end as nat, 0)
                == spec_parse_exp_int(s@, pos as nat, end as nat, exact_acc),
        decreases end - pos,
    {
        let c = s[pos];
        if !(c >= 0x0030u16 && c <= 0x0039u16) {
            return None;
        }
        let d = (c - 0x0030u16) as i128;
        proof {
            exact_acc = exact_acc * 10 + (d as int);
        }
        acc = if acc >= limit { limit } else { acc * 10i128 + d };
        pos += 1;
    }
    Some(acc)
}

pub open spec fn spec_strip_trailing_zero_u8(d: Seq<u8>) -> Seq<u8>
    decreases d.len(),
{
    if d.len() == 0 {
        seq![]
    } else if d.last() == 0u8 {
        spec_strip_trailing_zero_u8(d.drop_last())
    } else {
        d
    }
}

proof fn lemma_strip_trailing_zero_last_nonzero(d: Seq<u8>)
    ensures
        spec_strip_trailing_zero_u8(d).len() > 0
            ==> spec_strip_trailing_zero_u8(d).last() != 0u8,
    decreases d.len(),
{
    if d.len() > 0 && d.last() == 0u8 {
        lemma_strip_trailing_zero_last_nonzero(d.drop_last());
    }
}

pub open spec fn spec_strip_leading_zero_u8(d: Seq<u8>, idx: nat) -> nat
    decreases d.len() - idx,
{
    if idx < d.len() && d[idx as int] == 0u8 {
        spec_strip_leading_zero_u8(d, idx + 1)
    } else {
        idx
    }
}

proof fn lemma_strip_leading_zero_lt_when_last_nonzero(d: Seq<u8>, idx: nat)
    requires
        idx < d.len(),
        d.last() != 0u8,
    ensures
        spec_strip_leading_zero_u8(d, idx) < d.len(),
        d[spec_strip_leading_zero_u8(d, idx) as int] != 0u8,
    decreases d.len() - idx,
{
    if d[idx as int] == 0u8 {
        assert(idx < d.len() - 1);
        lemma_strip_leading_zero_lt_when_last_nonzero(d, idx + 1);
    }
}

fn build_combined_digits(
    s: &Vec<u16>,
    d_start: usize,
    int_end: usize,
    frac_start: usize,
    frac_end: usize,
) -> (combined: Vec<u8>)
    requires
        d_start <= int_end <= frac_start <= frac_end <= s@.len(),
        forall|k: int| d_start as int <= k < int_end as int ==> 0x0030u16 <= (#[trigger] s@[k]) && s@[k] <= 0x0039u16,
        forall|k: int| frac_start as int <= k < frac_end as int ==> 0x0030u16 <= (#[trigger] s@[k]) && s@[k] <= 0x0039u16,
    ensures
        combined@ == Seq::new(
            ((int_end - d_start) + (frac_end - frac_start)) as nat,
            |i: int|
                if i < (int_end - d_start) as int {
                    (s@[(d_start as int) + i] - 0x0030u16) as u8
                } else {
                    (s@[(frac_start as int) + (i - (int_end - d_start) as int)] - 0x0030u16) as u8
                },
        ),
{
    let int_len = int_end - d_start;
    let frac_len = frac_end - frac_start;
    let mut combined: Vec<u8> = Vec::new();
    let mut a: usize = 0;
    while a < int_len
        invariant
            a <= int_len,
            d_start + int_len == int_end,
            int_end <= s@.len(),
            forall|k: int| d_start as int <= k < int_end as int ==> 0x0030u16 <= (#[trigger] s@[k]) && s@[k] <= 0x0039u16,
            combined@.len() == a as int,
            forall|m: int| 0 <= m < a as int ==> (#[trigger] combined@[m]) == (s@[(d_start as int) + m] - 0x0030u16) as u8,
        decreases int_len - a,
    {
        let c = s[d_start + a];
        combined.push((c - 0x0030u16) as u8);
        a += 1;
    }
    let mut b: usize = 0;
    while b < frac_len
        invariant
            b <= frac_len,
            d_start + int_len == int_end,
            frac_start + frac_len == frac_end,
            int_end <= frac_start <= frac_end <= s@.len(),
            forall|k: int| d_start as int <= k < int_end as int ==> 0x0030u16 <= (#[trigger] s@[k]) && s@[k] <= 0x0039u16,
            forall|k: int| frac_start as int <= k < frac_end as int ==> 0x0030u16 <= (#[trigger] s@[k]) && s@[k] <= 0x0039u16,
            combined@.len() == (int_len + b) as int,
            forall|m: int| 0 <= m < combined@.len() ==>
                (#[trigger] combined@[m]) == (if m < int_len as int {
                    (s@[(d_start as int) + m] - 0x0030u16) as u8
                } else {
                    (s@[(frac_start as int) + (m - int_len as int)] - 0x0030u16) as u8
                }),
        decreases frac_len - b,
    {
        let c = s[frac_start + b];
        combined.push((c - 0x0030u16) as u8);
        b += 1;
    }
    let ghost spec_comb = Seq::new(
        (int_len + frac_len) as nat,
        |i: int|
            if i < int_len as int {
                (s@[(d_start as int) + i] - 0x0030u16) as u8
            } else {
                (s@[(frac_start as int) + (i - int_len as int)] - 0x0030u16) as u8
            },
    );
    proof {
        assert(combined@ =~= spec_comb);
    }
    combined
}

fn strip_trailing_zero_len(combined: &Vec<u8>) -> (nt_len: usize)
    ensures
        nt_len <= combined@.len(),
        combined@.subrange(0, nt_len as int) == spec_strip_trailing_zero_u8(combined@),
        nt_len > 0 ==> combined@[(nt_len - 1) as int] != 0u8,
{
    let mut nt_len: usize = combined.len();
    proof {
        assert(combined@.subrange(0, nt_len as int) =~= combined@);
    }
    while nt_len > 0 && combined[nt_len - 1] == 0u8
        invariant
            nt_len <= combined@.len(),
            spec_strip_trailing_zero_u8(combined@)
                == spec_strip_trailing_zero_u8(combined@.subrange(0, nt_len as int)),
        decreases nt_len,
    {
        let ghost cur_sub = combined@.subrange(0, nt_len as int);
        let ghost prev_sub = combined@.subrange(0, (nt_len - 1) as int);
        proof {
            assert(cur_sub.drop_last() =~= prev_sub);
            assert(cur_sub.last() == 0u8);
        }
        nt_len -= 1;
    }
    nt_len
}

fn strip_leading_zero_idx(combined: &Vec<u8>, nt_len: usize) -> (lead: usize)
    requires
        0 < nt_len <= combined@.len(),
        combined@[(nt_len - 1) as int] != 0u8,
    ensures
        lead < nt_len,
        combined@[lead as int] != 0u8,
        lead as nat == spec_strip_leading_zero_u8(combined@.subrange(0, nt_len as int), 0),
{
    let ghost no_trail = combined@.subrange(0, nt_len as int);
    proof {
        assert(no_trail.last() == combined@[(nt_len - 1) as int]);
        lemma_strip_leading_zero_lt_when_last_nonzero(no_trail, 0);
    }
    let mut lead: usize = 0;
    while lead < nt_len && combined[lead] == 0u8
        invariant
            lead <= nt_len,
            nt_len <= combined@.len(),
            no_trail == combined@.subrange(0, nt_len as int),
            spec_strip_leading_zero_u8(no_trail, 0) == spec_strip_leading_zero_u8(no_trail, lead as nat),
        decreases nt_len - lead,
    {
        lead += 1;
    }
    lead
}

pub open spec fn spec_parse_opt_signed_exp(s: Seq<u16>, frac_end: nat, end: nat) -> Option<int> {
    if frac_end == end {
        Some(0)
    } else if frac_end < end && end <= s.len()
        && (s[frac_end as int] == 0x0065u16 || s[frac_end as int] == 0x0045u16)
    {
        let e0: nat = frac_end + 1;
        if e0 >= end {
            None
        } else {
            let e_neg = s[e0 as int] == 0x002Du16;
            let e_sign = e_neg || s[e0 as int] == 0x002Bu16;
            let e_digits: nat = if e_sign { e0 + 1 } else { e0 };
            if e_digits >= end {
                None
            } else {
                match spec_parse_exp_int(s, e_digits, end, 0) {
                    None => None,
                    Some(ev) => Some(if e_neg { -ev } else { ev }),
                }
            }
        }
    } else {
        None
    }
}

fn parse_opt_signed_exp(s: &Vec<u16>, frac_end: usize, end: usize) -> (res: Option<i128>)
    requires
        frac_end <= end,
        end <= s@.len(),
    ensures
        res is None <==> spec_parse_opt_signed_exp(s@, frac_end as nat, end as nat) is None,
        res is Some ==> ({
            let exact = spec_parse_opt_signed_exp(s@, frac_end as nat, end as nat).unwrap();
            let cl = res.unwrap() as int;
            let lim = 2 * (end as int) + 2000;
            -(lim * 10 + 9) <= cl && cl <= lim * 10 + 9
            && ((-lim < cl && cl < lim) ==> cl == exact)
            && (cl >= lim ==> exact >= lim)
            && (cl <= -lim ==> exact <= -lim)
        }),
{
    if frac_end == end {
        return Some(0i128);
    }
    if !(s[frac_end] == 0x0065u16 || s[frac_end] == 0x0045u16) {
        return None;
    }
    let e0 = frac_end + 1;
    if e0 >= end {
        return None;
    }
    let e_neg = s[e0] == 0x002Du16;
    let e_sign = e_neg || s[e0] == 0x002Bu16;
    let e_digits = if e_sign { e0 + 1 } else { e0 };
    if e_digits >= end {
        return None;
    }
    match parse_clamped_exp(s, e_digits, end) {
        None => None,
        Some(ev) => Some(if e_neg { -ev } else { ev }),
    }
}

pub open spec fn spec_parse_decimal_f64_bits(
    s: Seq<u16>,
    d_start: nat,
    end: nat,
    neg: bool,
) -> u64 {
    if d_start >= end || end > s.len() {
        CANONICAL_NAN_BITS
    } else {
        let int_end = spec_scan_dec_digits_end(s, d_start, end);
        let has_dot = int_end < end && s[int_end as int] == 0x002Eu16;
        let frac_start: nat = if has_dot { int_end + 1 } else { int_end };
        let frac_end: nat = if has_dot {
            spec_scan_dec_digits_end(s, frac_start, end)
        } else {
            int_end
        };
        let int_len: nat = (int_end - d_start) as nat;
        let frac_len: nat = (frac_end - frac_start) as nat;
        if int_len + frac_len == 0 {
            CANONICAL_NAN_BITS
        } else {
            match spec_parse_opt_signed_exp(s, frac_end, end) {
                None => CANONICAL_NAN_BITS,
                Some(exp_val) => {
                    let combined = Seq::new(
                        int_len + frac_len,
                        |i: int|
                            if i < int_len as int {
                                (s[(d_start as int) + i] - 0x0030u16) as u8
                            } else {
                                (s[(frac_start as int) + (i - int_len as int)] - 0x0030u16) as u8
                            },
                    );
                    let no_trail = spec_strip_trailing_zero_u8(combined);
                    if no_trail.len() == 0 {
                        if neg { NEG_ZERO_BITS } else { POS_ZERO_BITS }
                    } else {
                        let lead = spec_strip_leading_zero_u8(no_trail, 0);
                        let orig_sig: int = (no_trail.len() as int) - (lead as int);
                        let trailing_zeros: int = (combined.len() as int) - (no_trail.len() as int);
                        let sci_exp10: int = exp_val - (frac_len as int) + trailing_zeros + orig_sig - 1;
                        if sci_exp10 > 309 {
                            if neg { NEG_INF_BITS } else { POS_INF_BITS }
                        } else if sci_exp10 < -325 {
                            if neg { NEG_ZERO_BITS } else { POS_ZERO_BITS }
                        } else {
                            let m_big = spec_bignat_from_digits_loop(no_trail, lead, no_trail.len(), seq![]);
                            let dec_exp: int = sci_exp10 - (orig_sig - 1);
                            let (num, den) = if dec_exp >= 0 {
                                (spec_bignat_mul_pow10(m_big, dec_exp as nat), seq![1u32])
                            } else {
                                (m_big, spec_bignat_mul_pow10(seq![1u32], (-dec_exp) as nat))
                            };
                            spec_pack_rational_f64_rne(neg, num, den)
                        }
                    }
                },
            }
        }
    }
}

proof fn lemma_from_digits_subrange_eq(
    combined: Seq<u8>,
    lead: nat,
    nt_len: nat,
    acc: Seq<u32>,
)
    requires
        lead <= nt_len <= combined.len(),
    ensures
        spec_bignat_from_digits_loop(combined, lead, nt_len, acc)
            == spec_bignat_from_digits_loop(combined.subrange(0, nt_len as int), lead, nt_len, acc),
    decreases nt_len - lead,
{
    if lead < nt_len {
        let sub = combined.subrange(0, nt_len as int);
        assert(sub[lead as int] == combined[lead as int]);
        lemma_from_digits_subrange_eq(
            combined,
            lead + 1,
            nt_len,
            spec_bignat_mul_add_u32(acc, 10u32, combined[lead as int] as u32),
        );
    }
}

fn parse_decimal_f64_bits(s: &Vec<u16>, d_start: usize, end: usize, neg: bool) -> (bits: u64)
    requires
        d_start <= end,
        end <= s@.len(),
    ensures
        bits == spec_parse_decimal_f64_bits(s@, d_start as nat, end as nat, neg),
{
    if d_start >= end {
        return CANONICAL_NAN_BITS;
    }
    let int_end = scan_dec_digits_end(s, d_start, end);
    let has_dot = int_end < end && s[int_end] == 0x002Eu16;
    let frac_start = if has_dot { int_end + 1 } else { int_end };
    let frac_end = if has_dot {
        scan_dec_digits_end(s, frac_start, end)
    } else {
        int_end
    };
    let int_len = int_end - d_start;
    let frac_len = frac_end - frac_start;
    if int_len == 0 && frac_len == 0 {
        return CANONICAL_NAN_BITS;
    }
    let exp_val: i128 = match parse_opt_signed_exp(s, frac_end, end) {
        None => return CANONICAL_NAN_BITS,
        Some(ev) => ev,
    };

    let combined = build_combined_digits(s, d_start, int_end, frac_start, frac_end);
    let nt_len = strip_trailing_zero_len(&combined);
    if nt_len == 0 {
        return if neg { NEG_ZERO_BITS } else { POS_ZERO_BITS };
    }
    let lead = strip_leading_zero_idx(&combined, nt_len);
    let orig_sig: usize = nt_len - lead;
    let trailing_zeros: usize = combined.len() - nt_len;
    proof {
        assert(usize::BITS <= 64);
        assert(end as i128 <= 0xffff_ffff_ffff_ffffi128);
    }
    let sci_exp10: i128 = exp_val - (frac_len as i128) + (trailing_zeros as i128) + (orig_sig as i128) - 1i128;
    if sci_exp10 > 309i128 {
        return if neg { NEG_INF_BITS } else { POS_INF_BITS };
    }
    if sci_exp10 < -325i128 {
        return if neg { NEG_ZERO_BITS } else { POS_ZERO_BITS };
    }
    let m_big = bignat_from_digits(&combined, lead, nt_len);
    proof {
        lemma_from_digits_subrange_eq(combined@, lead as nat, nt_len as nat, seq![]);
    }
    let dec_exp: i128 = sci_exp10 - ((orig_sig as i128) - 1i128);
    let one = make_bignat_one();
    let (num, den) = if dec_exp >= 0i128 {
        let scaled = bignat_mul_pow10(m_big, dec_exp as u128);
        (scaled, one)
    } else {
        let scaled_den = bignat_mul_pow10(one, (-dec_exp) as u128);
        (m_big, scaled_den)
    };
    pack_rational_f64_rne(neg, num, den)
}

/// Complete ECMA-262 §7.1.4.1.1 `StringToNumber` specification returning IEEE-754 binary64 bits.
pub open spec fn spec_string_to_f64_bits(s: Seq<u16>) -> u64 {
    let start = spec_trim_start_idx(s, 0);
    let end = spec_trim_end_idx(s, start, s.len());
    if start >= end || end > s.len() {
        POS_ZERO_BITS
    } else if spec_matches_infinity(s, start, end)
        || (s[start as int] == 0x002Bu16 && spec_matches_infinity(s, start + 1, end))
    {
        POS_INF_BITS
    } else if s[start as int] == 0x002Du16 && spec_matches_infinity(s, start + 1, end) {
        NEG_INF_BITS
    } else if end - start >= 2 && s[start as int] == 0x0030u16
        && (s[(start + 1) as int] == 0x0078u16 || s[(start + 1) as int] == 0x0058u16)
    {
        spec_parse_radix_f64_bits(s, start + 2, end, 16u32)
    } else if end - start >= 2 && s[start as int] == 0x0030u16
        && (s[(start + 1) as int] == 0x0062u16 || s[(start + 1) as int] == 0x0042u16)
    {
        spec_parse_radix_f64_bits(s, start + 2, end, 2u32)
    } else if end - start >= 2 && s[start as int] == 0x0030u16
        && (s[(start + 1) as int] == 0x006Fu16 || s[(start + 1) as int] == 0x004Fu16)
    {
        spec_parse_radix_f64_bits(s, start + 2, end, 8u32)
    } else {
        let neg = s[start as int] == 0x002Du16;
        let has_sign = neg || s[start as int] == 0x002Bu16;
        let d_start: nat = if has_sign { start + 1 } else { start };
        spec_parse_decimal_f64_bits(s, d_start, end, neg)
    }
}

/// Complete ECMA-262 §7.1.4.1.1 `StringToNumber` executive implementation proved `exec == spec`.
pub fn string_to_f64_bits(s: &Vec<u16>) -> (bits: u64)
    ensures
        bits == spec_string_to_f64_bits(s@),
{
    let n = s.len();
    let mut start: usize = 0;
    while start < n && is_str_white_space(s[start])
        invariant
            start <= n,
            n == s@.len(),
            spec_trim_start_idx(s@, 0) == spec_trim_start_idx(s@, start as nat),
        decreases n - start,
    {
        start += 1;
    }
    let mut end: usize = n;
    while end > start && is_str_white_space(s[end - 1])
        invariant
            start <= end <= n,
            n == s@.len(),
            spec_trim_end_idx(s@, start as nat, n as nat)
                == spec_trim_end_idx(s@, start as nat, end as nat),
        decreases end - start,
    {
        end -= 1;
    }
    if start >= end {
        return POS_ZERO_BITS;
    }
    if matches_infinity(s, start, end)
        || (s[start] == 0x002Bu16 && matches_infinity(s, start + 1, end))
    {
        return POS_INF_BITS;
    }
    if s[start] == 0x002Du16 && matches_infinity(s, start + 1, end) {
        return NEG_INF_BITS;
    }
    if end - start >= 2 && s[start] == 0x0030u16
        && (s[start + 1] == 0x0078u16 || s[start + 1] == 0x0058u16)
    {
        return parse_radix_f64_bits(s, start + 2, end, 16u32);
    }
    if end - start >= 2 && s[start] == 0x0030u16
        && (s[start + 1] == 0x0062u16 || s[start + 1] == 0x0042u16)
    {
        return parse_radix_f64_bits(s, start + 2, end, 2u32);
    }
    if end - start >= 2 && s[start] == 0x0030u16
        && (s[start + 1] == 0x006Fu16 || s[start + 1] == 0x004Fu16)
    {
        return parse_radix_f64_bits(s, start + 2, end, 8u32);
    }
    let neg = s[start] == 0x002Du16;
    let has_sign = neg || s[start] == 0x002Bu16;
    let d_start = if has_sign { start + 1 } else { start };
    parse_decimal_f64_bits(s, d_start, end, neg)
}

} // verus!
