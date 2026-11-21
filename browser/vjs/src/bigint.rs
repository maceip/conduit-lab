//! ECMA-262 §6.1.6.2 The BigInt Type & §7.1.14 StringToBigInt.
//!
//! Arbitrary-precision signed integers backed by canonical little-endian `Vec<u32>` limbs:
//! - Zero is uniquely represented as `neg == false` and `limbs.len() == 0`.
//! - Non-zero values have `limbs.last() != 0`.
//!
//! Includes machine-checked `exec == spec` proofs, `wf` preservation, canonical uniqueness,
//! algebraic ring identities (commutativity, associativity, additive/multiplicative identities,
//! additive inverse, distributivity), `StringToBigInt` (§7.1.14), `BigInt::toString`
//! (§6.1.6.2.21), and decimal serialize-parse roundtrip.

#[cfg(verus_keep_ghost)]
use crate::utf16::spec_trim;
use crate::utf16::Utf16Str;
use vstd::prelude::*;

verus! {

/// Ghost canonical model of `JsBigInt`.
pub struct SpecBigInt {
    pub neg: bool,
    pub limbs: Seq<u32>,
}

/// Arbitrary-precision signed integer (`ECMA-262 §6.1.6.2`).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct JsBigInt {
    pub neg: bool,
    pub limbs: Vec<u32>,
}

impl View for JsBigInt {
    type V = SpecBigInt;

    open spec fn view(&self) -> SpecBigInt {
        SpecBigInt {
            neg: self.neg,
            limbs: self.limbs@,
        }
    }
}

// -------------------------------------------------------------------------------------------
// Core Limb & BigInt Specifications
// -------------------------------------------------------------------------------------------

pub open spec fn pow32(k: nat) -> nat
    decreases k,
{
    if k == 0 {
        1
    } else {
        0x1_0000_0000nat * pow32((k - 1) as nat)
    }
}

/// Natural number value of little-endian base-$2^{32}$ limbs.
pub open spec fn spec_limbs_nat(limbs: Seq<u32>) -> nat
    decreases limbs.len(),
{
    if limbs.len() == 0 {
        0
    } else {
        spec_limbs_nat(limbs.drop_last()) + (limbs.last() as nat) * pow32((limbs.len() - 1) as nat)
    }
}

/// Canonical unsigned limb well-formedness: empty for zero, non-zero most-significant limb otherwise.
pub open spec fn spec_limbs_wf(limbs: Seq<u32>) -> bool {
    limbs.len() == 0 || limbs.last() != 0
}

pub open spec fn spec_limb_or_zero(limbs: Seq<u32>, i: nat) -> nat {
    if i < limbs.len() {
        limbs[i as int] as nat
    } else {
        0
    }
}

pub open spec fn spec_limbs_prefix_nat(limbs: Seq<u32>, i: nat) -> nat {
    if i <= limbs.len() {
        spec_limbs_nat(limbs.subrange(0, i as int))
    } else {
        spec_limbs_nat(limbs)
    }
}

/// Canonical decomposition of `n: nat` into little-endian base-$2^{32}$ limbs.
pub open spec fn spec_canonical_limbs_of_nat(n: nat) -> Seq<u32>
    decreases n,
{
    if n == 0 {
        Seq::<u32>::empty()
    } else {
        seq![(n % 0x1_0000_0000nat) as u32] + spec_canonical_limbs_of_nat(n / 0x1_0000_0000nat)
    }
}

impl SpecBigInt {
    pub open spec fn wf(self) -> bool {
        if self.limbs.len() == 0 {
            !self.neg
        } else {
            self.limbs.last() != 0
        }
    }

    pub open spec fn spec_val(self) -> int {
        if self.neg {
            -(spec_limbs_nat(self.limbs) as int)
        } else {
            spec_limbs_nat(self.limbs) as int
        }
    }
}

impl JsBigInt {
    pub open spec fn wf(&self) -> bool {
        self@.wf()
    }

    pub open spec fn spec_val(&self) -> int {
        self@.spec_val()
    }
}

pub open spec fn spec_bigint_zero() -> SpecBigInt {
    SpecBigInt { neg: false, limbs: Seq::<u32>::empty() }
}

pub open spec fn spec_bigint_from_int(z: int) -> SpecBigInt {
    if z == 0 {
        spec_bigint_zero()
    } else if z > 0 {
        SpecBigInt { neg: false, limbs: spec_canonical_limbs_of_nat(z as nat) }
    } else {
        SpecBigInt { neg: true, limbs: spec_canonical_limbs_of_nat((-z) as nat) }
    }
}

pub open spec fn spec_bigint_neg(a: SpecBigInt) -> SpecBigInt {
    spec_bigint_from_int(-a.spec_val())
}

pub open spec fn spec_bigint_add(a: SpecBigInt, b: SpecBigInt) -> SpecBigInt {
    spec_bigint_from_int(a.spec_val() + b.spec_val())
}

pub open spec fn spec_bigint_sub(a: SpecBigInt, b: SpecBigInt) -> SpecBigInt {
    spec_bigint_from_int(a.spec_val() - b.spec_val())
}

pub open spec fn spec_bigint_mul(a: SpecBigInt, b: SpecBigInt) -> SpecBigInt {
    spec_bigint_from_int(a.spec_val() * b.spec_val())
}

pub open spec fn spec_bigint_eq(a: SpecBigInt, b: SpecBigInt) -> bool {
    a.spec_val() == b.spec_val()
}

pub open spec fn spec_bigint_cmp(a: SpecBigInt, b: SpecBigInt) -> i8 {
    if a.spec_val() < b.spec_val() {
        -1i8
    } else if a.spec_val() > b.spec_val() {
        1i8
    } else {
        0i8
    }
}

// -------------------------------------------------------------------------------------------
// StringToBigInt (§7.1.14) & BigInt::toString (§6.1.6.2.21) Specifications
// -------------------------------------------------------------------------------------------

pub open spec fn spec_radix_digit_u16(u: u16, radix: nat) -> Option<nat> {
    let d: Option<nat> = if 0x30 <= u && u <= 0x39 {
        Some((u - 0x30) as nat)
    } else if 0x41 <= u && u <= 0x5A {
        Some((u - 0x41 + 10) as nat)
    } else if 0x61 <= u && u <= 0x7A {
        Some((u - 0x61 + 10) as nat)
    } else {
        None
    };
    match d {
        None => None,
        Some(v) => if v < radix { Some(v) } else { None },
    }
}

pub open spec fn spec_parse_radix_digits(digits: Seq<u16>, radix: nat) -> Option<nat>
    decreases digits.len(),
{
    if digits.len() == 0 {
        Some(0)
    } else {
        match (spec_parse_radix_digits(digits.drop_last(), radix), spec_radix_digit_u16(digits.last(), radix)) {
            (Some(acc), Some(d)) => Some(acc * radix + d),
            _ => None,
        }
    }
}

/// ECMA-262 §7.1.14 StringToBigInt(str).
pub open spec fn spec_string_to_bigint(s: Seq<u16>) -> Option<SpecBigInt> {
    let t = spec_trim(s);
    if t.len() == 0 {
        Some(spec_bigint_zero())
    } else if t.len() >= 2 && t[0] == 0x30 && (t[1] == 0x62 || t[1] == 0x42) {
        let digits = t.subrange(2, t.len() as int);
        if digits.len() == 0 {
            None
        } else {
            match spec_parse_radix_digits(digits, 2) {
                None => None,
                Some(v) => Some(spec_bigint_from_int(v as int)),
            }
        }
    } else if t.len() >= 2 && t[0] == 0x30 && (t[1] == 0x6F || t[1] == 0x4F) {
        let digits = t.subrange(2, t.len() as int);
        if digits.len() == 0 {
            None
        } else {
            match spec_parse_radix_digits(digits, 8) {
                None => None,
                Some(v) => Some(spec_bigint_from_int(v as int)),
            }
        }
    } else if t.len() >= 2 && t[0] == 0x30 && (t[1] == 0x78 || t[1] == 0x58) {
        let digits = t.subrange(2, t.len() as int);
        if digits.len() == 0 {
            None
        } else {
            match spec_parse_radix_digits(digits, 16) {
                None => None,
                Some(v) => Some(spec_bigint_from_int(v as int)),
            }
        }
    } else {
        let (neg, digits) = if t[0] == 0x2D {
            (true, t.subrange(1, t.len() as int))
        } else if t[0] == 0x2B {
            (false, t.subrange(1, t.len() as int))
        } else {
            (false, t)
        };
        if digits.len() == 0 {
            None
        } else {
            match spec_parse_radix_digits(digits, 10) {
                None => None,
                Some(v) => Some(spec_bigint_from_int(if neg { -(v as int) } else { v as int })),
            }
        }
    }
}

pub open spec fn spec_digit_to_u16(d: nat) -> u16 {
    if d < 10 {
        (0x30nat + d) as u16
    } else {
        (0x61nat + (d - 10)) as u16
    }
}

pub open spec fn spec_nat_to_radix_nonempty(n: nat, radix: nat) -> Seq<u16>
    decreases n,
{
    if radix < 2 || n < radix {
        seq![spec_digit_to_u16(n)]
    } else {
        proof {
            assert(n / radix < n) by (nonlinear_arith)
                requires radix >= 2, n >= radix;
        }
        spec_nat_to_radix_nonempty(n / radix, radix).push(spec_digit_to_u16(n % radix))
    }
}

/// ECMA-262 §6.1.6.2.21 BigInt::toString(x, radix).
pub open spec fn spec_bigint_to_string_radix(a: SpecBigInt, radix: nat) -> Seq<u16> {
    let mag = spec_limbs_nat(a.limbs);
    if mag == 0 {
        seq![0x30u16]
    } else {
        let digits = spec_nat_to_radix_nonempty(mag, radix);
        if a.neg {
            seq![0x2Du16] + digits
        } else {
            digits
        }
    }
}

// -------------------------------------------------------------------------------------------
// Canonical Representation & Algebraic Proofs
// -------------------------------------------------------------------------------------------

pub proof fn lemma_pow32_pos(k: nat)
    ensures
        pow32(k) >= 1,
    decreases k,
{
    if k > 0 {
        lemma_pow32_pos((k - 1) as nat);
    }
}

pub proof fn lemma_pow32_mono(a: nat, b: nat)
    requires
        a <= b,
    ensures
        pow32(a) <= pow32(b),
    decreases b - a,
{
    if a < b {
        lemma_pow32_mono(a, (b - 1) as nat);
        lemma_pow32_pos((b - 1) as nat);
    }
}

pub proof fn lemma_pow32_add(a: nat, b: nat)
    ensures
        pow32(a + b) == pow32(a) * pow32(b),
    decreases b,
{
    if b == 0 {
        assert(a + 0 == a);
        assert(pow32(0) == 1);
        let pa = pow32(a);
        assert(pa * 1 == pa) by (nonlinear_arith);
    } else {
        lemma_pow32_add(a, (b - 1) as nat);
        assert(a + b - 1 == a + (b - 1));
        assert(pow32(a + b) == 0x1_0000_0000nat * pow32((a + b - 1) as nat));
        let pa = pow32(a);
        let pb1 = pow32((b - 1) as nat);
        assert(0x1_0000_0000nat * (pa * pb1) == pa * (0x1_0000_0000nat * pb1)) by (nonlinear_arith);
    }
}

pub proof fn lemma_limbs_upper_bound(limbs: Seq<u32>)
    ensures
        spec_limbs_nat(limbs) < pow32(limbs.len()),
    decreases limbs.len(),
{
    if limbs.len() == 0 {
    } else {
        let pre = limbs.drop_last();
        let d = limbs.last() as nat;
        let k = (limbs.len() - 1) as nat;
        lemma_limbs_upper_bound(pre);
        lemma_pow32_pos(k);
        let p = pow32(k);
        let vp = spec_limbs_nat(pre);
        assert(d <= 0xFFFF_FFFFnat);
        assert(pow32(limbs.len()) == 0x1_0000_0000nat * p);
        assert(vp + d * p < 0x1_0000_0000nat * p) by (nonlinear_arith)
            requires vp < p, d <= 0xFFFF_FFFFnat, p >= 1;
    }
}

pub proof fn lemma_limbs_wf_lower_bound(limbs: Seq<u32>)
    requires
        spec_limbs_wf(limbs),
        limbs.len() > 0,
    ensures
        spec_limbs_nat(limbs) >= pow32((limbs.len() - 1) as nat),
{
    let k = (limbs.len() - 1) as nat;
    lemma_pow32_pos(k);
    let p = pow32(k);
    let d = limbs.last() as nat;
    assert(d >= 1);
    assert(d * p >= p) by (nonlinear_arith)
        requires d >= 1, p >= 1;
}

pub proof fn lemma_limbs_wf_zero_iff_empty(limbs: Seq<u32>)
    requires
        spec_limbs_wf(limbs),
    ensures
        (spec_limbs_nat(limbs) == 0) <==> (limbs.len() == 0),
{
    if limbs.len() > 0 {
        lemma_limbs_wf_lower_bound(limbs);
        lemma_pow32_pos((limbs.len() - 1) as nat);
    }
}

proof fn lemma_same_len_limbs_unique(a: Seq<u32>, b: Seq<u32>)
    requires
        a.len() == b.len(),
        spec_limbs_nat(a) == spec_limbs_nat(b),
    ensures
        a == b,
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a =~= b);
    } else {
        let k = (a.len() - 1) as nat;
        let p = pow32(k);
        let pa = a.drop_last();
        let pb = b.drop_last();
        let va = spec_limbs_nat(pa);
        let vb = spec_limbs_nat(pb);
        let da = a.last() as nat;
        let db = b.last() as nat;
        lemma_pow32_pos(k);
        lemma_limbs_upper_bound(pa);
        lemma_limbs_upper_bound(pb);
        assert(da == db && va == vb) by (nonlinear_arith)
            requires va < p, vb < p, p >= 1, va + da * p == vb + db * p;
        lemma_same_len_limbs_unique(pa, pb);
        assert(a =~= pa.push(a.last()));
        assert(b =~= pb.push(b.last()));
    }
}

/// Canonical unsigned limb representation is unique for every natural number.
pub proof fn lemma_limbs_canonical_unique(a: Seq<u32>, b: Seq<u32>)
    requires
        spec_limbs_wf(a),
        spec_limbs_wf(b),
        spec_limbs_nat(a) == spec_limbs_nat(b),
    ensures
        a == b,
{
    if a.len() < b.len() {
        lemma_limbs_upper_bound(a);
        lemma_pow32_mono(a.len(), (b.len() - 1) as nat);
        lemma_limbs_wf_lower_bound(b);
        assert(false);
    } else if b.len() < a.len() {
        lemma_limbs_upper_bound(b);
        lemma_pow32_mono(b.len(), (a.len() - 1) as nat);
        lemma_limbs_wf_lower_bound(a);
        assert(false);
    } else {
        lemma_same_len_limbs_unique(a, b);
    }
}

pub proof fn lemma_prepend_limb_val(d: u32, tail: Seq<u32>)
    ensures
        spec_limbs_nat(seq![d] + tail) == (d as nat) + 0x1_0000_0000nat * spec_limbs_nat(tail),
    decreases tail.len(),
{
    if tail.len() == 0 {
        reveal_with_fuel(spec_limbs_nat, 3);
        reveal_with_fuel(pow32, 3);
        assert(seq![d] + tail =~= seq![d]);
        assert((seq![d]).drop_last() =~= Seq::<u32>::empty());
        let dn = d as nat;
        assert(0 + dn * 1 == dn + 0x1_0000_0000nat * 0) by (nonlinear_arith);
    } else {
        let combined = seq![d] + tail;
        assert(combined.drop_last() =~= seq![d] + tail.drop_last());
        assert(combined.last() == tail.last());
        lemma_prepend_limb_val(d, tail.drop_last());
        let k = (tail.len() - 1) as nat;
        let pk = pow32(k);
        let tl = tail.last() as nat;
        let vt = spec_limbs_nat(tail.drop_last());
        assert(pow32(tail.len()) == 0x1_0000_0000nat * pk);
        assert((d as nat) + 0x1_0000_0000nat * vt + tl * (0x1_0000_0000nat * pk)
            == (d as nat) + 0x1_0000_0000nat * (vt + tl * pk)) by (nonlinear_arith);
    }
}

pub proof fn lemma_canonical_limbs_of_nat_props(n: nat)
    ensures
        spec_limbs_wf(spec_canonical_limbs_of_nat(n)),
        spec_limbs_nat(spec_canonical_limbs_of_nat(n)) == n,
        (n == 0) <==> (spec_canonical_limbs_of_nat(n).len() == 0),
    decreases n,
{
    if n == 0 {
    } else {
        let q = n / 0x1_0000_0000nat;
        let r = (n % 0x1_0000_0000nat) as u32;
        lemma_canonical_limbs_of_nat_props(q);
        let tail = spec_canonical_limbs_of_nat(q);
        let res = spec_canonical_limbs_of_nat(n);
        lemma_prepend_limb_val(r, tail);
        assert(r as nat == n % 0x1_0000_0000nat);
        if q == 0 {
            assert(tail =~= Seq::<u32>::empty());
            assert(res =~= seq![r]);
            assert(r != 0);
            assert(res.last() == r);
        } else {
            assert(tail.len() > 0);
            assert(res.last() == tail.last());
        }
    }
}

/// Every `SpecBigInt` produced by `spec_bigint_from_int(z)` is well-formed and has value `z`.
pub proof fn lemma_bigint_from_int_props(z: int)
    ensures
        spec_bigint_from_int(z).wf(),
        spec_bigint_from_int(z).spec_val() == z,
{
    if z == 0 {
    } else if z > 0 {
        lemma_canonical_limbs_of_nat_props(z as nat);
    } else {
        lemma_canonical_limbs_of_nat_props((-z) as nat);
    }
}

/// Canonical signed `SpecBigInt` uniqueness: equal mathematical values imply identical representation.
pub proof fn lemma_bigint_canonical_unique(a: SpecBigInt, b: SpecBigInt)
    requires
        a.wf(),
        b.wf(),
        a.spec_val() == b.spec_val(),
    ensures
        a == b,
{
    lemma_limbs_wf_zero_iff_empty(a.limbs);
    lemma_limbs_wf_zero_iff_empty(b.limbs);
    if a.limbs.len() == 0 {
        assert(a.spec_val() == 0);
        assert(b.limbs.len() == 0);
        assert(a.limbs =~= b.limbs);
    } else {
        assert(b.limbs.len() > 0);
        assert(a.neg == b.neg);
        assert(spec_limbs_nat(a.limbs) == spec_limbs_nat(b.limbs));
        lemma_limbs_canonical_unique(a.limbs, b.limbs);
    }
}

/// Algebraic ring laws for `SpecBigInt` (`add`, `sub`, `mul`, `neg`).
pub proof fn lemma_bigint_add_commutative(a: SpecBigInt, b: SpecBigInt)
    ensures
        spec_bigint_add(a, b) == spec_bigint_add(b, a),
{
    assert(a.spec_val() + b.spec_val() == b.spec_val() + a.spec_val());
}

pub proof fn lemma_bigint_add_associative(a: SpecBigInt, b: SpecBigInt, c: SpecBigInt)
    ensures
        spec_bigint_add(spec_bigint_add(a, b), c) == spec_bigint_add(a, spec_bigint_add(b, c)),
{
    lemma_bigint_from_int_props(a.spec_val() + b.spec_val());
    lemma_bigint_from_int_props(b.spec_val() + c.spec_val());
}

pub proof fn lemma_bigint_add_zero_identity(a: SpecBigInt)
    requires
        a.wf(),
    ensures
        spec_bigint_add(a, spec_bigint_zero()) == a,
        spec_bigint_add(spec_bigint_zero(), a) == a,
{
    lemma_bigint_from_int_props(a.spec_val());
    lemma_bigint_canonical_unique(spec_bigint_from_int(a.spec_val()), a);
}

pub proof fn lemma_bigint_add_neg_inverse(a: SpecBigInt)
    ensures
        spec_bigint_add(a, spec_bigint_neg(a)) == spec_bigint_zero(),
{
    lemma_bigint_from_int_props(-a.spec_val());
}

pub proof fn lemma_bigint_mul_commutative(a: SpecBigInt, b: SpecBigInt)
    ensures
        spec_bigint_mul(a, b) == spec_bigint_mul(b, a),
{
    let va = a.spec_val();
    let vb = b.spec_val();
    assert(va * vb == vb * va) by (nonlinear_arith);
}

pub proof fn lemma_bigint_mul_identities(a: SpecBigInt)
    requires
        a.wf(),
    ensures
        spec_bigint_mul(a, spec_bigint_zero()) == spec_bigint_zero(),
        spec_bigint_mul(a, spec_bigint_from_int(1)) == a,
{
    lemma_bigint_from_int_props(1);
    let va = a.spec_val();
    assert(va * 0 == 0) by (nonlinear_arith);
    assert(va * 1 == va) by (nonlinear_arith);
    lemma_bigint_from_int_props(va);
    lemma_bigint_canonical_unique(spec_bigint_from_int(va), a);
}

pub proof fn lemma_bigint_distributive(a: SpecBigInt, b: SpecBigInt, c: SpecBigInt)
    ensures
        spec_bigint_mul(a, spec_bigint_add(b, c))
            == spec_bigint_add(spec_bigint_mul(a, b), spec_bigint_mul(a, c)),
{
    let va = a.spec_val();
    let vb = b.spec_val();
    let vc = c.spec_val();
    lemma_bigint_from_int_props(vb + vc);
    lemma_bigint_from_int_props(va * vb);
    lemma_bigint_from_int_props(va * vc);
    assert(va * (vb + vc) == va * vb + va * vc) by (nonlinear_arith);
}

proof fn lemma_nat_to_radix10_roundtrip(n: nat)
    requires
        n >= 1,
    ensures
        ({
            let d = spec_nat_to_radix_nonempty(n, 10);
            &&& d.len() >= 1
            &&& 0x31u16 <= d[0] && d[0] <= 0x39u16
            &&& (forall|i: int| 0 <= i < d.len() ==> (0x30u16 <= #[trigger] d[i] && d[i] <= 0x39u16))
            &&& spec_parse_radix_digits(d, 10) == Some(n)
        }),
    decreases n,
{
    if n < 10 {
        let d = spec_nat_to_radix_nonempty(n, 10);
        assert(d =~= seq![(0x30nat + n) as u16]);
        assert(d.drop_last() =~= Seq::<u16>::empty());
        assert(d.last() == (0x30nat + n) as u16);
        reveal_with_fuel(spec_parse_radix_digits, 2);
        assert(0nat * 10 + n == n);
    } else {
        let q = n / 10;
        let r = n % 10;
        assert(q >= 1 && q < n && q * 10 + r == n && r < 10) by (nonlinear_arith)
            requires n >= 10, q == n / 10, r == n % 10;
        lemma_nat_to_radix10_roundtrip(q);
        let pre = spec_nat_to_radix_nonempty(q, 10);
        let ch = (0x30nat + r) as u16;
        let d = spec_nat_to_radix_nonempty(n, 10);
        assert(d =~= pre.push(ch));
        assert(d.drop_last() =~= pre);
        assert(d.last() == ch);
        assert(d[0] == pre[0]);
    }
}

/// Decimal serialize-then-parse roundtrip theorem: `StringToBigInt(BigInt::toString(a, 10)) == Some(a)`.
pub proof fn lemma_bigint_to_string_roundtrip(a: SpecBigInt)
    requires
        a.wf(),
    ensures
        spec_string_to_bigint(spec_bigint_to_string_radix(a, 10)) == Some(a),
{
    lemma_limbs_wf_zero_iff_empty(a.limbs);
    let mag = spec_limbs_nat(a.limbs);
    if mag == 0 {
        let s = spec_bigint_to_string_radix(a, 10);
        assert(s =~= seq![0x30u16]);
        assert(!crate::utf16::spec_is_str_white_space(0x30u16));
        assert(crate::utf16::spec_first_non_ws(s, 0) == 0);
        assert(crate::utf16::spec_last_non_ws_end(s, 0, 1) == 1);
        assert(spec_trim(s) =~= s);
        assert(s.drop_last() =~= Seq::<u16>::empty());
        reveal_with_fuel(spec_parse_radix_digits, 2);
        assert(a.limbs =~= Seq::<u32>::empty());
        assert(a == spec_bigint_zero());
    } else {
        lemma_nat_to_radix10_roundtrip(mag);
        let digits = spec_nat_to_radix_nonempty(mag, 10);
        if !a.neg {
            let s = spec_bigint_to_string_radix(a, 10);
            assert(s == digits);
            assert(!crate::utf16::spec_is_str_white_space(s[0]));
            assert(!crate::utf16::spec_is_str_white_space(s[s.len() - 1]));
            assert(crate::utf16::spec_first_non_ws(s, 0) == 0);
            assert(crate::utf16::spec_last_non_ws_end(s, 0, s.len()) == s.len());
            assert(spec_trim(s) =~= s);
            lemma_bigint_from_int_props(mag as int);
            lemma_bigint_canonical_unique(spec_bigint_from_int(mag as int), a);
        } else {
            let s = spec_bigint_to_string_radix(a, 10);
            assert(s =~= seq![0x2Du16] + digits);
            assert(s[0] == 0x2Du16);
            assert(s[s.len() - 1] == digits[digits.len() - 1]);
            assert(!crate::utf16::spec_is_str_white_space(s[0]));
            assert(!crate::utf16::spec_is_str_white_space(s[s.len() - 1]));
            assert(crate::utf16::spec_first_non_ws(s, 0) == 0);
            assert(crate::utf16::spec_last_non_ws_end(s, 0, s.len()) == s.len());
            assert(spec_trim(s) =~= s);
            assert(s.subrange(1, s.len() as int) =~= digits);
            lemma_bigint_from_int_props(-(mag as int));
            lemma_bigint_canonical_unique(spec_bigint_from_int(-(mag as int)), a);
        }
    }
}

proof fn lemma_prefix_step(limbs: Seq<u32>, i: nat)
    ensures
        spec_limbs_prefix_nat(limbs, i + 1)
            == spec_limbs_prefix_nat(limbs, i) + spec_limb_or_zero(limbs, i) * pow32(i),
{
    if i < limbs.len() {
        let sub_next = limbs.subrange(0, (i + 1) as int);
        assert(sub_next.drop_last() =~= limbs.subrange(0, i as int));
        assert(sub_next.last() == limbs[i as int]);
    } else {
        if i == limbs.len() {
            assert(limbs.subrange(0, i as int) =~= limbs);
        }
        assert(spec_limb_or_zero(limbs, i) == 0);
        assert(0nat * pow32(i) == 0) by (nonlinear_arith);
    }
}

proof fn lemma_prepend_zeros_val(zeros: Seq<u32>, v: Seq<u32>)
    requires
        forall|i: int| 0 <= i < zeros.len() ==> zeros[i] == 0,
    ensures
        spec_limbs_nat(zeros + v) == spec_limbs_nat(v) * pow32(zeros.len()),
    decreases zeros.len(),
{
    if zeros.len() == 0 {
        assert(zeros + v =~= v);
        assert(pow32(0) == 1);
        let vv = spec_limbs_nat(v);
        assert(vv * 1 == vv) by (nonlinear_arith);
    } else {
        let z_tail = zeros.subrange(1, zeros.len() as int);
        assert(zeros + v =~= seq![0u32] + (z_tail + v));
        lemma_prepend_limb_val(0u32, z_tail + v);
        lemma_prepend_zeros_val(z_tail, v);
        let vv = spec_limbs_nat(v);
        let pz = pow32(z_tail.len());
        assert(pow32(zeros.len()) == 0x1_0000_0000nat * pz);
        assert(0x1_0000_0000nat * (vv * pz) == vv * (0x1_0000_0000nat * pz)) by (nonlinear_arith);
    }
}

// -------------------------------------------------------------------------------------------
// Executable Unsigned Limb Helpers (Also Reused by `number.rs` Exact Decimal Conversions)
// -------------------------------------------------------------------------------------------

pub fn normalize_limbs(v: &mut Vec<u32>)
    ensures
        spec_limbs_wf(final(v)@),
        spec_limbs_nat(final(v)@) == spec_limbs_nat(old(v)@),
{
    while v.len() > 0 && v[v.len() - 1] == 0
        invariant
            spec_limbs_nat(v@) == spec_limbs_nat(old(v)@),
        decreases v@.len(),
    {
        let ghost pre = v@;
        let _ = v.pop();
        proof {
            assert(v@ =~= pre.drop_last());
            assert(pre.last() == 0);
            let p = pow32((pre.len() - 1) as nat);
            assert(0nat * p == 0) by (nonlinear_arith);
        }
    }
}

pub fn cmp_limbs(a: &[u32], b: &[u32]) -> (ord: i8)
    requires
        spec_limbs_wf(a@),
        spec_limbs_wf(b@),
    ensures
        (ord < 0) <==> (spec_limbs_nat(a@) < spec_limbs_nat(b@)),
        (ord == 0) <==> (spec_limbs_nat(a@) == spec_limbs_nat(b@)),
        (ord > 0) <==> (spec_limbs_nat(a@) > spec_limbs_nat(b@)),
{
    let na = a.len();
    let nb = b.len();
    if na < nb {
        proof {
            lemma_limbs_upper_bound(a@);
            lemma_pow32_mono(na as nat, (nb - 1) as nat);
            lemma_limbs_wf_lower_bound(b@);
        }
        return -1;
    }
    if na > nb {
        proof {
            lemma_limbs_upper_bound(b@);
            lemma_pow32_mono(nb as nat, (na - 1) as nat);
            lemma_limbs_wf_lower_bound(a@);
        }
        return 1;
    }
    let mut k: usize = na;
    while k > 0
        invariant
            k <= na,
            na == a@.len(),
            na == b@.len(),
            forall|j: int| k <= j < na ==> a@[j] == b@[j],
        decreases k,
    {
        let idx = k - 1;
        if a[idx] != b[idx] {
            let lt = a[idx] < b[idx];
            proof {
                // Prove suffix from idx+1..na cancels out, and prefix 0..idx is < pow32(idx).
                let pa = a@.subrange(0, idx as int);
                let pb = b@.subrange(0, idx as int);
                lemma_limbs_upper_bound(pa);
                lemma_limbs_upper_bound(pb);
                lemma_pow32_pos(idx as nat);
                // Relate full value to prefix at idx +1 via induction helper below.
                lemma_diff_at_top_mismatch(a@, b@, idx as nat);
            }
            return if lt { -1 } else { 1 };
        }
        k = idx;
    }
    proof {
        assert(a@ =~= b@);
    }
    0
}

proof fn lemma_diff_at_top_mismatch(a: Seq<u32>, b: Seq<u32>, idx: nat)
    requires
        a.len() == b.len(),
        idx < a.len(),
        a[idx as int] != b[idx as int],
        forall|j: int| idx < j < a.len() ==> a[j] == b[j],
    ensures
        (a[idx as int] < b[idx as int]) ==> (spec_limbs_nat(a) < spec_limbs_nat(b)),
        (a[idx as int] > b[idx as int]) ==> (spec_limbs_nat(a) > spec_limbs_nat(b)),
    decreases a.len() - idx,
{
    let n = a.len();
    if idx + 1 == n {
        let pa = a.drop_last();
        let pb = b.drop_last();
        let p = pow32(idx);
        let va = spec_limbs_nat(pa);
        let vb = spec_limbs_nat(pb);
        let da = a.last() as nat;
        let db = b.last() as nat;
        lemma_limbs_upper_bound(pa);
        lemma_limbs_upper_bound(pb);
        lemma_pow32_pos(idx);
        if da < db {
            assert(va + da * p < vb + db * p) by (nonlinear_arith)
                requires va < p, p >= 1, da + 1 <= db;
        } else {
            assert(va + da * p > vb + db * p) by (nonlinear_arith)
                requires vb < p, p >= 1, db + 1 <= da;
        }
    } else {
        let pa = a.drop_last();
        let pb = b.drop_last();
        assert(a.last() == b.last());
        lemma_diff_at_top_mismatch(pa, pb, idx);
    }
}

pub fn add_limbs(a: &[u32], b: &[u32]) -> (out: Vec<u32>)
    ensures
        spec_limbs_wf(out@),
        spec_limbs_nat(out@) == spec_limbs_nat(a@) + spec_limbs_nat(b@),
{
    let na = a.len();
    let nb = b.len();
    let n: usize = if na >= nb { na } else { nb };
    let mut out: Vec<u32> = Vec::new();
    let mut carry: u64 = 0;
    let mut i: usize = 0;
    proof {
        assert(a@.subrange(0, 0) =~= Seq::<u32>::empty());
        assert(b@.subrange(0, 0) =~= Seq::<u32>::empty());
    }
    while i < n
        invariant
            i <= n,
            na == a@.len(),
            nb == b@.len(),
            n >= na && n >= nb,
            out@.len() == i,
            carry <= 1,
            spec_limbs_nat(out@) + (carry as nat) * pow32(i as nat)
                == spec_limbs_prefix_nat(a@, i as nat) + spec_limbs_prefix_nat(b@, i as nat),
        decreases n - i,
    {
        let ai: u64 = if i < na { a[i] as u64 } else { 0 };
        let bi: u64 = if i < nb { b[i] as u64 } else { 0 };
        let sum: u64 = ai + bi + carry;
        let digit: u32 = (sum % 0x1_0000_0000u64) as u32;
        let next_carry: u64 = sum / 0x1_0000_0000u64;
        let ghost pre = out@;
        out.push(digit);
        proof {
            lemma_prefix_step(a@, i as nat);
            lemma_prefix_step(b@, i as nat);
            assert(out@.drop_last() =~= pre);
            assert(out@.last() == digit);
            let pi = pow32(i as nat);
            let pi1 = pow32((i + 1) as nat);
            assert(pi1 == 0x1_0000_0000nat * pi);
            let vp = spec_limbs_nat(pre);
            let pa = spec_limbs_prefix_nat(a@, i as nat);
            let pb = spec_limbs_prefix_nat(b@, i as nat);
            let nai = ai as nat;
            let nbi = bi as nat;
            let nc = carry as nat;
            let nd = digit as nat;
            let nnc = next_carry as nat;
            assert(nai == spec_limb_or_zero(a@, i as nat));
            assert(nbi == spec_limb_or_zero(b@, i as nat));
            assert((sum % 0x1_0000_0000u64) + (sum / 0x1_0000_0000u64) * 0x1_0000_0000u64 == sum)
                by (nonlinear_arith);
            assert(nai + nbi + nc == nd + nnc * 0x1_0000_0000nat);
            assert(vp + nd * pi + nnc * pi1 == (pa + nai * pi) + (pb + nbi * pi))
                by (nonlinear_arith)
                requires
                    vp + nc * pi == pa + pb,
                    nai + nbi + nc == nd + nnc * 0x1_0000_0000nat,
                    pi1 == 0x1_0000_0000nat * pi;
        }
        carry = next_carry;
        i = i + 1;
    }
    proof {
        if n == na {
            assert(a@.subrange(0, n as int) =~= a@);
        }
        if n == nb {
            assert(b@.subrange(0, n as int) =~= b@);
        }
    }
    if carry > 0 {
        let ghost pre = out@;
        out.push(carry as u32);
        proof {
            assert(out@.drop_last() =~= pre);
            assert(out@.last() == carry as u32);
        }
    } else {
        proof {
            let pn = pow32(n as nat);
            assert(0nat * pn == 0) by (nonlinear_arith);
        }
    }
    normalize_limbs(&mut out);
    out
}

pub fn sub_limbs(a: &[u32], b: &[u32]) -> (out: Vec<u32>)
    requires
        spec_limbs_nat(a@) >= spec_limbs_nat(b@),
    ensures
        spec_limbs_wf(out@),
        spec_limbs_nat(out@) == spec_limbs_nat(a@) - spec_limbs_nat(b@),
{
    let na = a.len();
    let nb = b.len();
    let n: usize = if na >= nb { na } else { nb };
    let mut out: Vec<u32> = Vec::new();
    let mut borrow: u64 = 0;
    let mut i: usize = 0;
    proof {
        assert(a@.subrange(0, 0) =~= Seq::<u32>::empty());
        assert(b@.subrange(0, 0) =~= Seq::<u32>::empty());
    }
    while i < n
        invariant
            i <= n,
            na == a@.len(),
            nb == b@.len(),
            n >= na && n >= nb,
            out@.len() == i,
            borrow <= 1,
            spec_limbs_nat(out@) + spec_limbs_prefix_nat(b@, i as nat)
                == spec_limbs_prefix_nat(a@, i as nat) + (borrow as nat) * pow32(i as nat),
        decreases n - i,
    {
        let ai: u64 = if i < na { a[i] as u64 } else { 0 };
        let bi: u64 = if i < nb { b[i] as u64 } else { 0 };
        let need: u64 = bi + borrow;
        let (digit, next_borrow): (u32, u64) = if ai >= need {
            ((ai - need) as u32, 0u64)
        } else {
            ((0x1_0000_0000u64 + ai - need) as u32, 1u64)
        };
        let ghost pre = out@;
        out.push(digit);
        proof {
            lemma_prefix_step(a@, i as nat);
            lemma_prefix_step(b@, i as nat);
            assert(out@.drop_last() =~= pre);
            assert(out@.last() == digit);
            let pi = pow32(i as nat);
            let pi1 = pow32((i + 1) as nat);
            assert(pi1 == 0x1_0000_0000nat * pi);
            let vp = spec_limbs_nat(pre);
            let pa = spec_limbs_prefix_nat(a@, i as nat);
            let pb = spec_limbs_prefix_nat(b@, i as nat);
            let nai = ai as nat;
            let nbi = bi as nat;
            let nbw = borrow as nat;
            let nd = digit as nat;
            let nnb = next_borrow as nat;
            assert(nai == spec_limb_or_zero(a@, i as nat));
            assert(nbi == spec_limb_or_zero(b@, i as nat));
            assert(nd + nbi + nbw == nai + nnb * 0x1_0000_0000nat);
            assert((vp + nd * pi) + (pb + nbi * pi) == (pa + nai * pi) + nnb * pi1)
                by (nonlinear_arith)
                requires
                    vp + pb == pa + nbw * pi,
                    nd + nbi + nbw == nai + nnb * 0x1_0000_0000nat,
                    pi1 == 0x1_0000_0000nat * pi;
        }
        borrow = next_borrow;
        i = i + 1;
    }
    proof {
        if n == na {
            assert(a@.subrange(0, n as int) =~= a@);
        }
        if n == nb {
            assert(b@.subrange(0, n as int) =~= b@);
        }
        lemma_limbs_upper_bound(out@);
        let pn = pow32(n as nat);
        let vo = spec_limbs_nat(out@);
        let va = spec_limbs_nat(a@);
        let vb = spec_limbs_nat(b@);
        let nbw = borrow as nat;
        assert(nbw == 0) by (nonlinear_arith)
            requires vo < pn, va >= vb, nbw <= 1, vo + vb == va + nbw * pn;
        assert(0nat * pn == 0) by (nonlinear_arith);
    }
    normalize_limbs(&mut out);
    out
}

pub fn mul_limb_add(a: &[u32], m: u32, addend: u32) -> (out: Vec<u32>)
    ensures
        spec_limbs_wf(out@),
        spec_limbs_nat(out@) == spec_limbs_nat(a@) * (m as nat) + (addend as nat),
{
    let n = a.len();
    let mut out: Vec<u32> = Vec::new();
    let mut carry: u64 = addend as u64;
    let mut i: usize = 0;
    proof {
        assert(a@.subrange(0, 0) =~= Seq::<u32>::empty());
        assert(pow32(0) == 1);
        let c0 = carry as nat;
        let m0 = m as nat;
        assert(0 + c0 * 1 == 0 * m0 + (addend as nat)) by (nonlinear_arith)
            requires c0 == addend as nat;
    }
    while i < n
        invariant
            i <= n,
            n == a@.len(),
            out@.len() == i,
            carry <= 0xFFFF_FFFFu64,
            spec_limbs_nat(out@) + (carry as nat) * pow32(i as nat)
                == spec_limbs_prefix_nat(a@, i as nat) * (m as nat) + (addend as nat),
        decreases n - i,
    {
        let ai: u64 = a[i] as u64;
        let mu: u64 = m as u64;
        proof {
            assert(ai * mu + carry <= 0xFFFF_FFFFu64 * 0xFFFF_FFFFu64 + 0xFFFF_FFFFu64)
                by (nonlinear_arith)
                requires ai <= 0xFFFF_FFFFu64, mu <= 0xFFFF_FFFFu64, carry <= 0xFFFF_FFFFu64;
        }
        let prod: u64 = ai * mu + carry;
        let digit: u32 = (prod % 0x1_0000_0000u64) as u32;
        let next_carry: u64 = prod / 0x1_0000_0000u64;
        let ghost pre = out@;
        out.push(digit);
        proof {
            lemma_prefix_step(a@, i as nat);
            assert(out@.drop_last() =~= pre);
            assert(out@.last() == digit);
            let pi = pow32(i as nat);
            let pi1 = pow32((i + 1) as nat);
            assert(pi1 == 0x1_0000_0000nat * pi);
            let pa = spec_limbs_prefix_nat(a@, i as nat);
            let nai = ai as nat;
            let nm = m as nat;
            let nc = carry as nat;
            let nd = digit as nat;
            let nnc = next_carry as nat;
            assert(nai * nm + nc == nd + nnc * 0x1_0000_0000nat);
            assert(next_carry <= 0xFFFF_FFFFu64);
            assert(spec_limbs_nat(pre) + nd * pi + nnc * pi1 == (pa + nai * pi) * nm + (addend as nat))
                by (nonlinear_arith)
                requires
                    spec_limbs_nat(pre) + nc * pi == pa * nm + (addend as nat),
                    nai * nm + nc == nd + nnc * 0x1_0000_0000nat,
                    pi1 == 0x1_0000_0000nat * pi;
        }
        carry = next_carry;
        i = i + 1;
    }
    proof {
        assert(a@.subrange(0, n as int) =~= a@);
    }
    if carry > 0 {
        let ghost pre = out@;
        out.push(carry as u32);
        proof {
            assert(out@.drop_last() =~= pre);
            assert(out@.last() == carry as u32);
        }
    } else {
        proof {
            let pn = pow32(n as nat);
            assert(0nat * pn == 0) by (nonlinear_arith);
        }
    }
    normalize_limbs(&mut out);
    out
}

fn prepend_zeros(v: &[u32], k: usize) -> (out: Vec<u32>)
    ensures
        spec_limbs_nat(out@) == spec_limbs_nat(v@) * pow32(k as nat),
{
    let nv = v.len();
    let mut out: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    while i < k
        invariant
            i <= k,
            out@.len() == i,
            forall|q: int| 0 <= q < i ==> out@[q] == 0,
        decreases k - i,
    {
        out.push(0);
        i = i + 1;
    }
    let ghost zeros = out@;
    let mut j: usize = 0;
    while j < nv
        invariant
            j <= nv,
            nv == v@.len(),
            out@ == zeros + v@.subrange(0, j as int),
        decreases nv - j,
    {
        out.push(v[j]);
        proof {
            assert(out@ =~= zeros + v@.subrange(0, (j + 1) as int));
        }
        j = j + 1;
    }
    proof {
        assert(v@.subrange(0, nv as int) =~= v@);
        lemma_prepend_zeros_val(zeros, v@);
    }
    out
}

pub fn mul_limbs(a: &[u32], b: &[u32]) -> (out: Vec<u32>)
    ensures
        spec_limbs_wf(out@),
        spec_limbs_nat(out@) == spec_limbs_nat(a@) * spec_limbs_nat(b@),
{
    let nb = b.len();
    let mut acc: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(b@.subrange(0, 0) =~= Seq::<u32>::empty());
        let va = spec_limbs_nat(a@);
        assert(va * 0 == 0) by (nonlinear_arith);
    }
    while i < nb
        invariant
            i <= nb,
            nb == b@.len(),
            spec_limbs_wf(acc@),
            spec_limbs_nat(acc@) == spec_limbs_nat(a@) * spec_limbs_prefix_nat(b@, i as nat),
        decreases nb - i,
    {
        let term = mul_limb_add(a, b[i], 0);
        let shifted = prepend_zeros(&term, i);
        let ghost prev_acc = acc@;
        acc = add_limbs(&acc, &shifted);
        proof {
            lemma_prefix_step(b@, i as nat);
            let va = spec_limbs_nat(a@);
            let pb = spec_limbs_prefix_nat(b@, i as nat);
            let bi = b@[i as int] as nat;
            let pi = pow32(i as nat);
            assert(va * pb + (va * bi) * pi == va * (pb + bi * pi)) by (nonlinear_arith);
        }
        i = i + 1;
    }
    proof {
        assert(b@.subrange(0, nb as int) =~= b@);
    }
    acc
}

/// Divide little-endian `a` by scalar `d > 0`, returning canonical `(quotient, remainder)`.
pub fn div_rem_limb(a: &[u32], d: u32) -> (qr: (Vec<u32>, u32))
    requires
        d > 0,
    ensures
        spec_limbs_wf(qr.0@),
        qr.1 < d,
        spec_limbs_nat(a@) == spec_limbs_nat(qr.0@) * (d as nat) + (qr.1 as nat),
{
    let n = a.len();
    let mut q_rev: Vec<u32> = Vec::new();
    let mut rem: u64 = 0;
    let mut k: usize = n;
    let ghost mut q_suffix: Seq<u32> = Seq::<u32>::empty();
    proof {
        assert(a@.subrange(n as int, n as int) =~= Seq::<u32>::empty());
        let dn = d as nat;
        assert(0nat * dn + 0 == 0) by (nonlinear_arith);
    }
    while k > 0
        invariant
            k <= n,
            n == a@.len(),
            d > 0,
            rem < d as u64,
            q_rev@.len() == n - k,
            q_suffix.len() == n - k,
            forall|j: int| 0 <= j < (n - k) ==> q_suffix[j] == q_rev@[(n - k - 1) - j],
            spec_limbs_nat(a@.subrange(k as int, n as int))
                == spec_limbs_nat(q_suffix) * (d as nat) + (rem as nat),
        decreases k,
    {
        let idx = k - 1;
        let ak: u64 = a[idx] as u64;
        let du: u64 = d as u64;
        proof {
            assert(rem * 0x1_0000_0000u64 + ak <= (du - 1) * 0x1_0000_0000u64 + 0xFFFF_FFFFu64)
                by (nonlinear_arith)
                requires rem < du, du >= 1, ak <= 0xFFFF_FFFFu64;
            assert((du - 1) * 0x1_0000_0000u64 + 0xFFFF_FFFFu64 == du * 0x1_0000_0000u64 - 1)
                by (nonlinear_arith)
                requires du >= 1;
            assert(du * 0x1_0000_0000u64 - 1 <= 0xFFFF_FFFFu64 * 0x1_0000_0000u64 + 0xFFFF_FFFFu64)
                by (nonlinear_arith)
                requires du <= 0xFFFF_FFFFu64;
        }
        let cur: u64 = rem * 0x1_0000_0000u64 + ak;
        let qk64: u64 = cur / du;
        let new_rem: u64 = cur % du;
        proof {
            assert(qk64 < 0x1_0000_0000u64) by (nonlinear_arith)
                requires cur < du * 0x1_0000_0000u64, du >= 1, qk64 == cur / du;
        }
        let qk: u32 = qk64 as u32;
        q_rev.push(qk);
        proof {
            let old_qs = q_suffix;
            q_suffix = seq![qk] + old_qs;
            assert(a@.subrange(idx as int, n as int) =~= seq![a@[idx as int]] + a@.subrange(k as int, n as int));
            lemma_prepend_limb_val(a@[idx as int], a@.subrange(k as int, n as int));
            lemma_prepend_limb_val(qk, old_qs);
            let vq = spec_limbs_nat(old_qs);
            let dn = d as nat;
            let nqk = qk as nat;
            let nr = new_rem as nat;
            let r_old = rem as nat;
            let nak = ak as nat;
            assert((cur / du) * du + (cur % du) == cur) by (nonlinear_arith)
                requires du >= 1;
            assert(nqk * dn + nr == r_old * 0x1_0000_0000nat + nak);
            assert((nqk + 0x1_0000_0000nat * vq) * dn + nr
                == nak + 0x1_0000_0000nat * (vq * dn + r_old))
                by (nonlinear_arith)
                requires nqk * dn + nr == r_old * 0x1_0000_0000nat + nak;
        }
        rem = new_rem;
        k = idx;
    }
    let mut q: Vec<u32> = Vec::with_capacity(n);
    let mut m: usize = 0;
    while m < n
        invariant
            m <= n,
            n == q_rev@.len(),
            q_suffix.len() == n,
            forall|j: int| 0 <= j < n ==> q_suffix[j] == q_rev@[(n - 1) - j],
            q@.len() == m,
            forall|j: int| 0 <= j < m ==> q@[j] == q_suffix[j],
        decreases n - m,
    {
        q.push(q_rev[(n - 1) - m]);
        m = m + 1;
    }
    proof {
        assert(q@ =~= q_suffix);
        assert(a@.subrange(0, n as int) =~= a@);
    }
    normalize_limbs(&mut q);
    (q, rem as u32)
}

pub fn clone_limbs(a: &[u32]) -> (out: Vec<u32>)
    ensures
        out@ == a@,
{
    let n = a.len();
    let mut out: Vec<u32> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == a@.len(),
            out@ == a@.subrange(0, i as int),
        decreases n - i,
    {
        out.push(a[i]);
        proof {
            assert(out@ =~= a@.subrange(0, (i + 1) as int));
        }
        i = i + 1;
    }
    proof {
        assert(a@.subrange(0, n as int) =~= a@);
    }
    out
}

pub open spec fn pow2_nat(k: nat) -> nat
    decreases k,
{
    if k == 0 {
        1
    } else {
        2nat * pow2_nat((k - 1) as nat)
    }
}

pub open spec fn pow_nat(base: nat, exp: nat) -> nat
    decreases exp,
{
    if exp == 0 {
        1
    } else {
        base * pow_nat(base, (exp - 1) as nat)
    }
}

pub proof fn lemma_pow2_pos(k: nat)
    ensures
        pow2_nat(k) >= 1,
    decreases k,
{
    if k > 0 {
        lemma_pow2_pos((k - 1) as nat);
    }
}

pub proof fn lemma_pow2_add(a: nat, b: nat)
    ensures
        pow2_nat(a + b) == pow2_nat(a) * pow2_nat(b),
    decreases b,
{
    if b == 0 {
        assert(a + 0 == a);
        let pa = pow2_nat(a);
        assert(pa * 1 == pa) by (nonlinear_arith);
    } else {
        lemma_pow2_add(a, (b - 1) as nat);
        assert(a + b - 1 == a + (b - 1));
        let pa = pow2_nat(a);
        let pb1 = pow2_nat((b - 1) as nat);
        assert(2nat * (pa * pb1) == pa * (2nat * pb1)) by (nonlinear_arith);
    }
}

pub proof fn lemma_pow2_32()
    ensures
        pow2_nat(16) == 0x1_0000nat,
        pow2_nat(32) == 0x1_0000_0000nat,
{
    reveal_with_fuel(pow2_nat, 17);
    assert(pow2_nat(16) == 0x1_0000nat);
    lemma_pow2_add(16, 16);
}

proof fn lemma_pow32_is_pow2(w: nat)
    ensures
        pow32(w) == pow2_nat(w * 32),
    decreases w,
{
    if w == 0 {
        assert(0nat * 32 == 0);
    } else {
        lemma_pow32_is_pow2((w - 1) as nat);
        assert(w * 32 == (w - 1) * 32 + 32) by (nonlinear_arith)
            requires w >= 1;
        lemma_pow2_add(((w - 1) * 32) as nat, 32);
        lemma_pow2_32();
        let p = pow2_nat(((w - 1) * 32) as nat);
        assert(p * 0x1_0000_0000nat == 0x1_0000_0000nat * p) by (nonlinear_arith);
    }
}

pub proof fn lemma_u32_shl_is_pow2_pub(b: u32)
    requires
        b < 32,
    ensures
        (1u32 << b) as nat == pow2_nat(b as nat),
{
    lemma_u32_shl_is_pow2(b);
}

proof fn lemma_u32_shl_is_pow2(b: u32)
    requires
        b < 32,
    ensures
        (1u32 << b) as nat == pow2_nat(b as nat),
{
    if b < 16 {
        reveal_with_fuel(pow2_nat, 17);
        if b == 0 { assert((1u32 << 0u32) == 1u32) by (bit_vector); }
        else if b == 1 { assert((1u32 << 1u32) == 2u32) by (bit_vector); }
        else if b == 2 { assert((1u32 << 2u32) == 4u32) by (bit_vector); }
        else if b == 3 { assert((1u32 << 3u32) == 8u32) by (bit_vector); }
        else if b == 4 { assert((1u32 << 4u32) == 16u32) by (bit_vector); }
        else if b == 5 { assert((1u32 << 5u32) == 32u32) by (bit_vector); }
        else if b == 6 { assert((1u32 << 6u32) == 64u32) by (bit_vector); }
        else if b == 7 { assert((1u32 << 7u32) == 128u32) by (bit_vector); }
        else if b == 8 { assert((1u32 << 8u32) == 256u32) by (bit_vector); }
        else if b == 9 { assert((1u32 << 9u32) == 512u32) by (bit_vector); }
        else if b == 10 { assert((1u32 << 10u32) == 1024u32) by (bit_vector); }
        else if b == 11 { assert((1u32 << 11u32) == 2048u32) by (bit_vector); }
        else if b == 12 { assert((1u32 << 12u32) == 4096u32) by (bit_vector); }
        else if b == 13 { assert((1u32 << 13u32) == 8192u32) by (bit_vector); }
        else if b == 14 { assert((1u32 << 14u32) == 16384u32) by (bit_vector); }
        else { assert((1u32 << 15u32) == 32768u32) by (bit_vector); }
    } else {
        lemma_pow2_32();
        let rem = (b - 16) as u32;
        lemma_u32_shl_is_pow2_low16(rem);
        lemma_pow2_add(16, rem as nat);
        assert((b as nat) == 16 + (rem as nat));
        assert((1u32 << b) == (0x1_0000u32 * (1u32 << rem))) by (bit_vector)
            requires 16u32 <= b, b < 32u32, rem == sub(b, 16u32);
    }
}

proof fn lemma_u32_shl_is_pow2_low16(b: u32)
    requires
        b < 16,
    ensures
        (1u32 << b) as nat == pow2_nat(b as nat),
{
    reveal_with_fuel(pow2_nat, 17);
    if b == 0 { assert((1u32 << 0u32) == 1u32) by (bit_vector); }
    else if b == 1 { assert((1u32 << 1u32) == 2u32) by (bit_vector); }
    else if b == 2 { assert((1u32 << 2u32) == 4u32) by (bit_vector); }
    else if b == 3 { assert((1u32 << 3u32) == 8u32) by (bit_vector); }
    else if b == 4 { assert((1u32 << 4u32) == 16u32) by (bit_vector); }
    else if b == 5 { assert((1u32 << 5u32) == 32u32) by (bit_vector); }
    else if b == 6 { assert((1u32 << 6u32) == 64u32) by (bit_vector); }
    else if b == 7 { assert((1u32 << 7u32) == 128u32) by (bit_vector); }
    else if b == 8 { assert((1u32 << 8u32) == 256u32) by (bit_vector); }
    else if b == 9 { assert((1u32 << 9u32) == 512u32) by (bit_vector); }
    else if b == 10 { assert((1u32 << 10u32) == 1024u32) by (bit_vector); }
    else if b == 11 { assert((1u32 << 11u32) == 2048u32) by (bit_vector); }
    else if b == 12 { assert((1u32 << 12u32) == 4096u32) by (bit_vector); }
    else if b == 13 { assert((1u32 << 13u32) == 8192u32) by (bit_vector); }
    else if b == 14 { assert((1u32 << 14u32) == 16384u32) by (bit_vector); }
    else { assert((1u32 << 15u32) == 32768u32) by (bit_vector); }
}

/// Shift canonical unsigned `a` left by `bits` (`a * 2^bits`).
pub fn shl_limbs(a: &[u32], bits: u32) -> (out: Vec<u32>)
    ensures
        spec_limbs_wf(out@),
        spec_limbs_nat(out@) == spec_limbs_nat(a@) * pow2_nat(bits as nat),
{
    let word_shift: usize = (bits / 32) as usize;
    let bit_shift: u32 = bits % 32;
    let factor: u32 = 1u32 << bit_shift;
    let sub = mul_limb_add(a, factor, 0);
    let mut out = prepend_zeros(&sub, word_shift);
    normalize_limbs(&mut out);
    proof {
        lemma_u32_shl_is_pow2(bit_shift);
        lemma_pow32_is_pow2(word_shift as nat);
        assert((bits as nat) == (word_shift as nat) * 32 + (bit_shift as nat))
            by (nonlinear_arith)
            requires word_shift == (bits / 32) as usize, bit_shift == bits % 32;
        lemma_pow2_add((word_shift as nat) * 32, bit_shift as nat);
        let va = spec_limbs_nat(a@);
        let pb = pow2_nat(bit_shift as nat);
        let pw = pow2_nat((word_shift as nat) * 32);
        assert((va * pb) * pw == va * (pw * pb)) by (nonlinear_arith);
    }
    out
}

/// Compute exact `base^exp` in canonical `Vec<u32>` limbs.
pub fn pow_u32_limbs(base: u32, exp: u32) -> (out: Vec<u32>)
    requires
        base > 0,
    ensures
        spec_limbs_wf(out@),
        out@.len() > 0,
        spec_limbs_nat(out@) == pow_nat(base as nat, exp as nat),
{
    let mut acc: Vec<u32> = Vec::with_capacity(1);
    acc.push(1u32);
    proof {
        reveal_with_fuel(spec_limbs_nat, 3);
        reveal_with_fuel(pow32, 2);
        assert(acc@ =~= seq![1u32]);
        assert((seq![1u32]).drop_last() =~= Seq::<u32>::empty());
        assert(spec_limbs_nat(acc@) == 1);
    }
    let mut k: u32 = 0;
    while k < exp
        invariant
            k <= exp,
            base > 0,
            spec_limbs_wf(acc@),
            acc@.len() > 0,
            spec_limbs_nat(acc@) == pow_nat(base as nat, k as nat),
        decreases exp - k,
    {
        proof {
            lemma_limbs_wf_lower_bound(acc@);
            lemma_pow32_pos((acc@.len() - 1) as nat);
        }
        let ghost prev = spec_limbs_nat(acc@);
        acc = mul_limb_add(&acc, base, 0);
        proof {
            let nb = base as nat;
            assert(nb * prev == prev * nb) by (nonlinear_arith);
            assert(prev * nb >= 1) by (nonlinear_arith)
                requires prev >= 1, nb >= 1;
            lemma_limbs_wf_zero_iff_empty(acc@);
        }
        k = k + 1;
    }
    acc
}

// -------------------------------------------------------------------------------------------
// Executable `JsBigInt` Operations
// -------------------------------------------------------------------------------------------

impl JsBigInt {
    pub fn zero() -> (z: Self)
        ensures
            z.wf(),
            z@ == spec_bigint_zero(),
            z.spec_val() == 0,
    {
        JsBigInt { neg: false, limbs: Vec::new() }
    }

    pub fn from_u64(v: u64) -> (out: Self)
        ensures
            out.wf(),
            out@ == spec_bigint_from_int(v as int),
            out.spec_val() == v as int,
    {
        if v == 0 {
            return Self::zero();
        }
        let lo: u32 = (v % 0x1_0000_0000u64) as u32;
        let hi: u32 = (v / 0x1_0000_0000u64) as u32;
        let mut limbs: Vec<u32> = Vec::new();
        limbs.push(lo);
        if hi != 0 {
            limbs.push(hi);
            proof {
                reveal_with_fuel(spec_limbs_nat, 4);
                reveal_with_fuel(pow32, 4);
                assert(limbs@.drop_last() =~= seq![lo]);
                assert((seq![lo]).drop_last() =~= Seq::<u32>::empty());
                assert((v % 0x1_0000_0000u64) + (v / 0x1_0000_0000u64) * 0x1_0000_0000u64 == v)
                    by (nonlinear_arith);
                let nlo = lo as nat;
                let nhi = hi as nat;
                assert(0 + nlo * 1 + nhi * 0x1_0000_0000nat == v as nat) by (nonlinear_arith)
                    requires nlo == (v % 0x1_0000_0000u64) as nat, nhi == (v / 0x1_0000_0000u64) as nat,
                    (v % 0x1_0000_0000u64) + (v / 0x1_0000_0000u64) * 0x1_0000_0000u64 == v;
                assert(spec_limbs_nat(limbs@) == v as nat);
            }
        } else {
            proof {
                reveal_with_fuel(spec_limbs_nat, 3);
                reveal_with_fuel(pow32, 3);
                assert(limbs@ =~= seq![lo]);
                assert((seq![lo]).drop_last() =~= Seq::<u32>::empty());
                assert((v % 0x1_0000_0000u64) + (v / 0x1_0000_0000u64) * 0x1_0000_0000u64 == v)
                    by (nonlinear_arith);
                assert(lo != 0);
                let nlo = lo as nat;
                assert(0 + nlo * 1 == v as nat) by (nonlinear_arith)
                    requires nlo == v as nat;
                assert(spec_limbs_nat(limbs@) == v as nat);
            }
        }
        let res = JsBigInt { neg: false, limbs };
        proof {
            lemma_bigint_from_int_props(v as int);
            lemma_bigint_canonical_unique(res@, spec_bigint_from_int(v as int));
        }
        res
    }

    pub fn from_i64(v: i64) -> (out: Self)
        ensures
            out.wf(),
            out@ == spec_bigint_from_int(v as int),
            out.spec_val() == v as int,
    {
        if v == 0 {
            Self::zero()
        } else if v > 0 {
            Self::from_u64(v as u64)
        } else {
            let mag: u64 = if v == i64::MIN {
                0x8000_0000_0000_0000u64
            } else {
                (-v) as u64
            };
            let pos = Self::from_u64(mag);
            let res = JsBigInt { neg: true, limbs: pos.limbs };
            proof {
                lemma_limbs_wf_zero_iff_empty(res.limbs@);
                lemma_bigint_from_int_props(v as int);
                lemma_bigint_canonical_unique(res@, spec_bigint_from_int(v as int));
            }
            res
        }
    }

    pub fn is_zero(&self) -> (z: bool)
        requires
            self.wf(),
        ensures
            z == (self.spec_val() == 0),
            z == (self.limbs@.len() == 0),
    {
        proof {
            lemma_limbs_wf_zero_iff_empty(self.limbs@);
        }
        self.limbs.len() == 0
    }

    pub fn clone_bigint(&self) -> (out: Self)
        ensures
            out@ == self@,
    {
        JsBigInt {
            neg: self.neg,
            limbs: clone_limbs(&self.limbs),
        }
    }

    /// ECMA-262 §6.1.6.2.1 BigInt::unaryMinus(x).
    pub fn neg(&self) -> (out: Self)
        requires
            self.wf(),
        ensures
            out.wf(),
            out@ == spec_bigint_neg(self@),
            out.spec_val() == -self.spec_val(),
    {
        if self.limbs.len() == 0 {
            Self::zero()
        } else {
            let out = JsBigInt {
                neg: !self.neg,
                limbs: clone_limbs(&self.limbs),
            };
            proof {
                lemma_bigint_from_int_props(-self.spec_val());
                lemma_bigint_canonical_unique(out@, spec_bigint_neg(self@));
            }
            out
        }
    }

    /// ECMA-262 §6.1.6.2.7 BigInt::add(x, y).
    pub fn add(&self, other: &Self) -> (out: Self)
        requires
            self.wf(),
            other.wf(),
        ensures
            out.wf(),
            out@ == spec_bigint_add(self@, other@),
            out.spec_val() == self.spec_val() + other.spec_val(),
    {
        if self.limbs.len() == 0 {
            let out = other.clone_bigint();
            proof {
                lemma_bigint_add_zero_identity(other@);
            }
            return out;
        }
        if other.limbs.len() == 0 {
            let out = self.clone_bigint();
            proof {
                lemma_bigint_add_zero_identity(self@);
            }
            return out;
        }
        let res = if self.neg == other.neg {
            let limbs = add_limbs(&self.limbs, &other.limbs);
            proof {
                lemma_limbs_wf_lower_bound(self.limbs@);
                lemma_pow32_pos((self.limbs@.len() - 1) as nat);
                lemma_limbs_wf_zero_iff_empty(limbs@);
            }
            JsBigInt { neg: self.neg, limbs }
        } else {
            let c = cmp_limbs(&self.limbs, &other.limbs);
            if c == 0 {
                Self::zero()
            } else if c > 0 {
                let limbs = sub_limbs(&self.limbs, &other.limbs);
                proof {
                    lemma_limbs_wf_zero_iff_empty(limbs@);
                }
                JsBigInt { neg: self.neg, limbs }
            } else {
                let limbs = sub_limbs(&other.limbs, &self.limbs);
                proof {
                    lemma_limbs_wf_zero_iff_empty(limbs@);
                }
                JsBigInt { neg: other.neg, limbs }
            }
        };
        proof {
            lemma_bigint_from_int_props(self.spec_val() + other.spec_val());
            lemma_bigint_canonical_unique(res@, spec_bigint_add(self@, other@));
        }
        res
    }

    /// ECMA-262 §6.1.6.2.8 BigInt::subtract(x, y).
    pub fn sub(&self, other: &Self) -> (out: Self)
        requires
            self.wf(),
            other.wf(),
        ensures
            out.wf(),
            out@ == spec_bigint_sub(self@, other@),
            out.spec_val() == self.spec_val() - other.spec_val(),
    {
        let neg_other = other.neg();
        let out = self.add(&neg_other);
        proof {
            lemma_bigint_from_int_props(self.spec_val() - other.spec_val());
            lemma_bigint_canonical_unique(out@, spec_bigint_sub(self@, other@));
        }
        out
    }

    /// ECMA-262 §6.1.6.2.4 BigInt::multiply(x, y).
    pub fn mul(&self, other: &Self) -> (out: Self)
        requires
            self.wf(),
            other.wf(),
        ensures
            out.wf(),
            out@ == spec_bigint_mul(self@, other@),
            out.spec_val() == self.spec_val() * other.spec_val(),
    {
        if self.limbs.len() == 0 || other.limbs.len() == 0 {
            let z = Self::zero();
            proof {
                let va = self.spec_val();
                let vb = other.spec_val();
                lemma_limbs_wf_zero_iff_empty(self.limbs@);
                lemma_limbs_wf_zero_iff_empty(other.limbs@);
                assert(va * vb == 0) by (nonlinear_arith)
                    requires va == 0 || vb == 0;
            }
            return z;
        }
        let limbs = mul_limbs(&self.limbs, &other.limbs);
        let neg = self.neg != other.neg;
        proof {
            lemma_limbs_wf_lower_bound(self.limbs@);
            lemma_limbs_wf_lower_bound(other.limbs@);
            lemma_pow32_pos((self.limbs@.len() - 1) as nat);
            lemma_pow32_pos((other.limbs@.len() - 1) as nat);
            let ma = spec_limbs_nat(self.limbs@);
            let mb = spec_limbs_nat(other.limbs@);
            assert(ma * mb >= 1) by (nonlinear_arith)
                requires ma >= 1, mb >= 1;
            lemma_limbs_wf_zero_iff_empty(limbs@);
        }
        let res = JsBigInt { neg, limbs };
        proof {
            let ma = spec_limbs_nat(self.limbs@) as int;
            let mb = spec_limbs_nat(other.limbs@) as int;
            let va = self.spec_val();
            let vb = other.spec_val();
            assert(res.spec_val() == va * vb) by (nonlinear_arith)
                requires
                    va == (if self.neg { -ma } else { ma }),
                    vb == (if other.neg { -mb } else { mb }),
                    res.spec_val() == (if self.neg != other.neg { -(ma * mb) } else { ma * mb });
            lemma_bigint_from_int_props(va * vb);
            lemma_bigint_canonical_unique(res@, spec_bigint_mul(self@, other@));
        }
        res
    }

    /// ECMA-262 §6.1.6.2.13 BigInt::equal(x, y).
    pub fn eq_bigint(&self, other: &Self) -> (eq: bool)
        requires
            self.wf(),
            other.wf(),
        ensures
            eq == spec_bigint_eq(self@, other@),
            eq == (self@ == other@),
    {
        if self.neg != other.neg {
            proof {
                if self.spec_val() == other.spec_val() {
                    lemma_bigint_canonical_unique(self@, other@);
                }
            }
            return false;
        }
        let c = cmp_limbs(&self.limbs, &other.limbs);
        proof {
            if c == 0 {
                lemma_limbs_canonical_unique(self.limbs@, other.limbs@);
            } else if self.spec_val() == other.spec_val() {
                lemma_bigint_canonical_unique(self@, other@);
            }
        }
        c == 0
    }

    /// ECMA-262 §6.1.6.2.12 BigInt::lessThan / three-way comparison.
    pub fn cmp_bigint(&self, other: &Self) -> (ord: i8)
        requires
            self.wf(),
            other.wf(),
        ensures
            ord == spec_bigint_cmp(self@, other@),
            (ord < 0) <==> (self.spec_val() < other.spec_val()),
            (ord == 0) <==> (self.spec_val() == other.spec_val()),
            (ord > 0) <==> (self.spec_val() > other.spec_val()),
    {
        if self.limbs.len() == 0 && other.limbs.len() == 0 {
            return 0;
        }
        if self.neg != other.neg {
            proof {
                lemma_limbs_wf_zero_iff_empty(self.limbs@);
                lemma_limbs_wf_zero_iff_empty(other.limbs@);
            }
            return if self.neg { -1 } else { 1 };
        }
        let c = cmp_limbs(&self.limbs, &other.limbs);
        if c == 0 {
            0
        } else if !self.neg {
            if c < 0 { -1 } else { 1 }
        } else {
            if c < 0 { 1 } else { -1 }
        }
    }

    /// ECMA-262 §6.1.6.2.21 BigInt::toString(x, radix) for `2 <= radix <= 36`.
    pub fn to_string_radix(&self, radix: u32) -> (out: Utf16Str)
        requires
            self.wf(),
            2 <= radix <= 36,
        ensures
            out@ == spec_bigint_to_string_radix(self@, radix as nat),
    {
        if self.limbs.len() == 0 {
            let mut u: Vec<u16> = Vec::with_capacity(1);
            u.push(0x30u16);
            proof {
                assert(u@ =~= seq![0x30u16]);
            }
            return Utf16Str { units: u };
        }
        let mut cur: Vec<u32> = clone_limbs(&self.limbs);
        let mut rev_digits: Vec<u16> = Vec::new();
        let ghost orig_mag: nat = spec_limbs_nat(self.limbs@);
        proof {
            lemma_limbs_wf_lower_bound(cur@);
            lemma_pow32_pos((cur@.len() - 1) as nat);
        }
        // Build digits from least-significant to most-significant via Euclidean division by `radix`.
        let mut out_units: Vec<u16> = Vec::new();
        while cur.len() > 0
            invariant
                2 <= radix <= 36,
                spec_limbs_wf(cur@),
                orig_mag >= 1,
                cur@.len() > 0 ==> (
                    spec_limbs_nat(cur@) >= 1
                    && spec_nat_to_radix_nonempty(orig_mag, radix as nat)
                        == spec_nat_to_radix_nonempty(spec_limbs_nat(cur@), radix as nat)
                            + rev_vec_view(rev_digits@)
                ),
                cur@.len() == 0 ==> (
                    rev_digits@.len() > 0
                    && spec_nat_to_radix_nonempty(orig_mag, radix as nat)
                        == rev_vec_view(rev_digits@)
                ),
            decreases spec_limbs_nat(cur@),
        {
            proof {
                lemma_limbs_wf_lower_bound(cur@);
                lemma_pow32_pos((cur@.len() - 1) as nat);
            }
            let ghost cur_val: nat = spec_limbs_nat(cur@);
            let (next_q, rem) = div_rem_limb(&cur, radix);
            let ch: u16 = if rem < 10 {
                (0x30u32 + rem) as u16
            } else {
                (0x61u32 + (rem - 10)) as u16
            };
            let ghost old_rev = rev_digits@;
            rev_digits.push(ch);
            proof {
                let r = radix as nat;
                let qv = spec_limbs_nat(next_q@);
                let rv = rem as nat;
                assert(cur_val / r == qv && cur_val % r == rv) by (nonlinear_arith)
                    requires cur_val == qv * r + rv, rv < r, r >= 2;
                lemma_rev_vec_push(old_rev, ch);
                lemma_limbs_wf_zero_iff_empty(next_q@);
                if next_q@.len() == 0 {
                    assert(qv == 0);
                    assert(cur_val < r) by (nonlinear_arith)
                        requires cur_val == 0 * r + rv, rv < r;
                    assert(spec_nat_to_radix_nonempty(cur_val, r) =~= seq![ch]);
                    assert(seq![ch] + rev_vec_view(old_rev) =~= rev_vec_view(rev_digits@));
                } else {
                    assert(qv >= 1);
                    assert(cur_val >= r) by (nonlinear_arith)
                        requires cur_val == qv * r + rv, qv >= 1, r >= 2;
                    assert(qv < cur_val) by (nonlinear_arith)
                        requires cur_val == qv * r + rv, qv >= 1, r >= 2;
                    assert(spec_nat_to_radix_nonempty(cur_val, r)
                        =~= spec_nat_to_radix_nonempty(qv, r).push(ch));
                    assert(spec_nat_to_radix_nonempty(qv, r).push(ch) + rev_vec_view(old_rev)
                        =~= spec_nat_to_radix_nonempty(qv, r) + (seq![ch] + rev_vec_view(old_rev)));
                }
            }
            cur = next_q;
        }
        if self.neg {
            out_units.push(0x2Du16);
        }
        let ghost prefix = out_units@;
        let m = rev_digits.len();
        let mut idx: usize = 0;
        while idx < m
            invariant
                idx <= m,
                m == rev_digits@.len(),
                out_units@ == prefix + rev_vec_view(rev_digits@).subrange(0, idx as int),
            decreases m - idx,
        {
            let ch = rev_digits[(m - 1) - idx];
            out_units.push(ch);
            proof {
                lemma_rev_vec_index(rev_digits@, idx as int);
                assert(out_units@ =~= prefix + rev_vec_view(rev_digits@).subrange(0, (idx + 1) as int));
            }
            idx = idx + 1;
        }
        proof {
            lemma_rev_vec_len(rev_digits@);
            assert(rev_vec_view(rev_digits@).subrange(0, m as int) =~= rev_vec_view(rev_digits@));
            if self.neg {
                assert(prefix =~= seq![0x2Du16]);
            } else {
                assert(prefix =~= Seq::<u16>::empty());
                assert(prefix + rev_vec_view(rev_digits@) =~= rev_vec_view(rev_digits@));
            }
        }
        Utf16Str { units: out_units }
    }

    pub fn to_string_radix10(&self) -> (out: Utf16Str)
        requires
            self.wf(),
        ensures
            out@ == spec_bigint_to_string_radix(self@, 10),
    {
        self.to_string_radix(10)
    }

    pub fn cmp(&self, other: &Self) -> (ord: i8)
        requires
            self.wf(),
            other.wf(),
        ensures
            ord == spec_bigint_cmp(self@, other@),
    {
        self.cmp_bigint(other)
    }
}

/// ECMA-262 §6.1.6.2.21 BigInt::toString(x, radix).
pub fn bigint_to_string(x: &JsBigInt, radix: u32) -> (out: Utf16Str)
    requires
        x.wf(),
        2 <= radix <= 36,
    ensures
        out@ == spec_bigint_to_string_radix(x@, radix as nat),
{
    x.to_string_radix(radix)
}

pub open spec fn rev_vec_view(s: Seq<u16>) -> Seq<u16>
    decreases s.len(),
{
    if s.len() == 0 {
        Seq::<u16>::empty()
    } else {
        seq![s.last()] + rev_vec_view(s.drop_last())
    }
}

proof fn lemma_rev_vec_len(s: Seq<u16>)
    ensures
        rev_vec_view(s).len() == s.len(),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_rev_vec_len(s.drop_last());
    }
}

proof fn lemma_rev_vec_push(s: Seq<u16>, x: u16)
    ensures
        rev_vec_view(s.push(x)) == seq![x] + rev_vec_view(s),
{
    assert(s.push(x).drop_last() =~= s);
    assert(s.push(x).last() == x);
}

proof fn lemma_rev_vec_index(s: Seq<u16>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        rev_vec_view(s).len() == s.len(),
        rev_vec_view(s)[i] == s[(s.len() - 1) - i],
    decreases s.len(),
{
    lemma_rev_vec_len(s);
    if i == 0 {
        assert(rev_vec_view(s)[0] == s.last());
    } else {
        lemma_rev_vec_index(s.drop_last(), i - 1);
        assert(rev_vec_view(s)[i] == rev_vec_view(s.drop_last())[i - 1]);
        assert(s.drop_last()[(s.drop_last().len() - 1) - (i - 1)] == s[(s.len() - 1) - i]);
    }
}

fn radix_digit_u16_exec(u: u16, radix: u32) -> (res: Option<u32>)
    requires
        2 <= radix <= 36,
    ensures
        match (res, spec_radix_digit_u16(u, radix as nat)) {
            (None, None) => true,
            (Some(v), Some(sv)) => v as nat == sv && v < radix,
            _ => false,
        },
{
    let d: Option<u32> = if u >= 0x30 && u <= 0x39 {
        Some((u - 0x30) as u32)
    } else if u >= 0x41 && u <= 0x5A {
        Some((u - 0x41 + 10) as u32)
    } else if u >= 0x61 && u <= 0x7A {
        Some((u - 0x61 + 10) as u32)
    } else {
        None
    };
    match d {
        None => None,
        Some(v) => if v < radix { Some(v) } else { None },
    }
}

fn parse_radix_limbs_exec(digits: &Utf16Str, radix: u32) -> (res: Option<Vec<u32>>)
    requires
        2 <= radix <= 36,
    ensures
        match (res, spec_parse_radix_digits(digits@, radix as nat)) {
            (None, None) => true,
            (Some(limbs), Some(val)) => spec_limbs_wf(limbs@) && spec_limbs_nat(limbs@) == val,
            _ => false,
        },
{
    let n = digits.len();
    let mut limbs: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(digits@.subrange(0, 0) =~= Seq::<u16>::empty());
    }
    while i < n
        invariant
            i <= n,
            n == digits@.len(),
            2 <= radix <= 36,
            spec_limbs_wf(limbs@),
            spec_parse_radix_digits(digits@.subrange(0, i as int), radix as nat)
                == Some(spec_limbs_nat(limbs@)),
        decreases n - i,
    {
        let u = digits.code_unit_at(i);
        proof {
            assert(digits@.subrange(0, (i + 1) as int).drop_last() =~= digits@.subrange(0, i as int));
            assert(digits@.subrange(0, (i + 1) as int).last() == u);
        }
        match radix_digit_u16_exec(u, radix) {
            None => {
                proof {
                    lemma_parse_radix_prefix_none(digits@, radix as nat, (i + 1) as nat);
                }
                return None;
            }
            Some(d) => {
                limbs = mul_limb_add(&limbs, radix, d);
            }
        }
        i = i + 1;
    }
    proof {
        assert(digits@.subrange(0, n as int) =~= digits@);
    }
    Some(limbs)
}

proof fn lemma_parse_radix_prefix_none(s: Seq<u16>, radix: nat, k: nat)
    requires
        k <= s.len(),
        spec_parse_radix_digits(s.subrange(0, k as int), radix) is None,
    ensures
        spec_parse_radix_digits(s, radix) is None,
    decreases s.len() - k,
{
    if k == s.len() {
        assert(s.subrange(0, k as int) =~= s);
    } else {
        let next = s.subrange(0, (k + 1) as int);
        assert(next.drop_last() =~= s.subrange(0, k as int));
        assert(spec_parse_radix_digits(next, radix) is None);
        lemma_parse_radix_prefix_none(s, radix, k + 1);
    }
}

/// ECMA-262 §7.1.14 StringToBigInt(str), proved equal to `spec_string_to_bigint`.
pub fn string_to_bigint(s: &Utf16Str) -> (res: Option<JsBigInt>)
    ensures
        match (res, spec_string_to_bigint(s@)) {
            (None, None) => true,
            (Some(b), Some(sb)) => b.wf() && b@ == sb,
            _ => false,
        },
{
    let t = s.trim();
    let n = t.len();
    if n == 0 {
        return Some(JsBigInt::zero());
    }
    let u0 = t.code_unit_at(0);
    if n >= 2 && u0 == 0x30 {
        let u1 = t.code_unit_at(1);
        if u1 == 0x62 || u1 == 0x42 {
            let digits = t.slice(2, n);
            if digits.len() == 0 {
                return None;
            }
            return match parse_radix_limbs_exec(&digits, 2) {
                None => None,
                Some(limbs) => {
                    let b = JsBigInt { neg: false, limbs };
                    proof {
                        let val = spec_limbs_nat(b.limbs@);
                        lemma_limbs_wf_zero_iff_empty(b.limbs@);
                        lemma_bigint_from_int_props(val as int);
                        lemma_bigint_canonical_unique(b@, spec_bigint_from_int(val as int));
                    }
                    Some(b)
                }
            };
        }
        if u1 == 0x6F || u1 == 0x4F {
            let digits = t.slice(2, n);
            if digits.len() == 0 {
                return None;
            }
            return match parse_radix_limbs_exec(&digits, 8) {
                None => None,
                Some(limbs) => {
                    let b = JsBigInt { neg: false, limbs };
                    proof {
                        let val = spec_limbs_nat(b.limbs@);
                        lemma_limbs_wf_zero_iff_empty(b.limbs@);
                        lemma_bigint_from_int_props(val as int);
                        lemma_bigint_canonical_unique(b@, spec_bigint_from_int(val as int));
                    }
                    Some(b)
                }
            };
        }
        if u1 == 0x78 || u1 == 0x58 {
            let digits = t.slice(2, n);
            if digits.len() == 0 {
                return None;
            }
            return match parse_radix_limbs_exec(&digits, 16) {
                None => None,
                Some(limbs) => {
                    let b = JsBigInt { neg: false, limbs };
                    proof {
                        let val = spec_limbs_nat(b.limbs@);
                        lemma_limbs_wf_zero_iff_empty(b.limbs@);
                        lemma_bigint_from_int_props(val as int);
                        lemma_bigint_canonical_unique(b@, spec_bigint_from_int(val as int));
                    }
                    Some(b)
                }
            };
        }
    }
    let (neg, digits) = if u0 == 0x2D {
        (true, t.slice(1, n))
    } else if u0 == 0x2B {
        (false, t.slice(1, n))
    } else {
        (false, t)
    };
    if digits.len() == 0 {
        return None;
    }
    match parse_radix_limbs_exec(&digits, 10) {
        None => None,
        Some(limbs) => {
            let final_neg = if limbs.len() == 0 { false } else { neg };
            let b = JsBigInt { neg: final_neg, limbs };
            proof {
                let val = spec_limbs_nat(b.limbs@);
                lemma_limbs_wf_zero_iff_empty(b.limbs@);
                let signed_val: int = if neg { -(val as int) } else { val as int };
                if b.limbs@.len() == 0 {
                    assert(val == 0);
                    assert(signed_val == 0);
                }
                lemma_bigint_from_int_props(signed_val);
                lemma_bigint_canonical_unique(b@, spec_bigint_from_int(signed_val));
            }
            Some(b)
        }
    }
}

} // verus!
