//! ECMA-262 §21.3 `Math`, §23.1 `Array`, and §22.1 `String` verified built-in operations.
use vstd::prelude::*;

verus! {

use crate::collections::*;

/// IEEE-754 binary64 `+1.0` bit pattern.
pub const POS_ONE_BITS: u64 = 0x3FF0_0000_0000_0000u64;
/// IEEE-754 binary64 `-1.0` bit pattern.
pub const NEG_ONE_BITS: u64 = 0xBFF0_0000_0000_0000u64;

// =======================================================================================
// 1. Verified `Math` (§21.3)
// =======================================================================================

/// Spec `2^k` on naturals.
pub open spec fn spec_pow2(k: nat) -> nat
    decreases k,
{
    if k == 0 {
        1
    } else {
        2 * spec_pow2((k - 1) as nat)
    }
}

/// Binary bit-length of `v` (`0` for `0`, `floor(log2(v)) + 1` for `v > 0`).
pub open spec fn spec_bit_length(v: nat) -> nat
    decreases v,
{
    if v == 0 {
        0
    } else {
        1 + spec_bit_length(v / 2)
    }
}

/// ECMA-262 §21.3.2.11 `Math.clz32 ( x )` on a `ToUint32`-converted 32-bit unsigned integer.
pub open spec fn spec_clz32(x: u32) -> nat {
    let bl = spec_bit_length(x as nat);
    if bl <= 32 {
        (32 - bl) as nat
    } else {
        0
    }
}

/// ECMA-262 §7.1.7 `ToUint32` modular reduction for exact integers.
pub open spec fn spec_to_uint32_int(x: int) -> u32 {
    (x % 4_294_967_296) as u32
}

/// ECMA-262 §21.3.2.19 `Math.imul ( x, y )` on `u32` operands:
/// `product = (a * b) modulo 2^32`; if `product >= 2^31`, `product - 2^32`, else `product`.
pub open spec fn spec_imul(a: u32, b: u32) -> int {
    let prod = ((a as int) * (b as int)) % 4_294_967_296;
    if prod >= 2_147_483_648 {
        prod - 4_294_967_296
    } else {
        prod
    }
}

/// ECMA-262 §21.3.2.1 `Math.abs ( x )` on IEEE-754 binary64 bit patterns.
pub open spec fn spec_math_abs_bits(bits: u64) -> u64 {
    if spec_is_nan_bits(bits) {
        CANONICAL_NAN_BITS
    } else if bits >= NEG_ZERO_BITS {
        (bits - NEG_ZERO_BITS) as u64
    } else {
        bits
    }
}

/// ECMA-262 §21.3.2.29 `Math.sign ( x )` on IEEE-754 binary64 bit patterns:
/// preserves `-0.0` and `+0.0`, propagates `NaN`, and maps negative/positive numbers to `-1.0`/`+1.0`.
pub open spec fn spec_math_sign_bits(bits: u64) -> u64 {
    if spec_is_nan_bits(bits) {
        CANONICAL_NAN_BITS
    } else if bits == NEG_ZERO_BITS {
        NEG_ZERO_BITS
    } else if bits == POS_ZERO_BITS {
        POS_ZERO_BITS
    } else if bits > NEG_ZERO_BITS {
        NEG_ONE_BITS
    } else {
        POS_ONE_BITS
    }
}

/// Total ordering predicate on non-NaN IEEE-754 binary64 bit patterns with `-0.0 < +0.0`
/// (matching ECMA-262 §21.3.2.24 `Math.max` and §21.3.2.25 `Math.min`).
pub open spec fn spec_ieee_le_non_nan(a: u64, b: u64) -> bool {
    if a >= NEG_ZERO_BITS && b >= NEG_ZERO_BITS {
        a >= b
    } else if a >= NEG_ZERO_BITS && b < NEG_ZERO_BITS {
        true
    } else if a < NEG_ZERO_BITS && b >= NEG_ZERO_BITS {
        false
    } else {
        a <= b
    }
}

/// ECMA-262 §21.3.2.25 `Math.min ( a, b )` on IEEE-754 binary64 bit patterns.
pub open spec fn spec_math_min_bits(a: u64, b: u64) -> u64 {
    if spec_is_nan_bits(a) || spec_is_nan_bits(b) {
        CANONICAL_NAN_BITS
    } else if spec_ieee_le_non_nan(a, b) {
        a
    } else {
        b
    }
}

/// ECMA-262 §21.3.2.24 `Math.max ( a, b )` on IEEE-754 binary64 bit patterns.
pub open spec fn spec_math_max_bits(a: u64, b: u64) -> u64 {
    if spec_is_nan_bits(a) || spec_is_nan_bits(b) {
        CANONICAL_NAN_BITS
    } else if spec_ieee_le_non_nan(a, b) {
        b
    } else {
        a
    }
}

/// Variadic `Math.min` over a sequence of IEEE-754 bit patterns (`+Infinity` on empty).
pub open spec fn spec_math_min_seq(xs: Seq<u64>) -> u64
    decreases xs.len(),
{
    if xs.len() == 0 {
        POS_INF_BITS
    } else {
        spec_math_min_bits(xs[0], spec_math_min_seq(xs.subrange(1, xs.len() as int)))
    }
}

/// Variadic `Math.max` over a sequence of IEEE-754 bit patterns (`-Infinity` on empty).
pub open spec fn spec_math_max_seq(xs: Seq<u64>) -> u64
    decreases xs.len(),
{
    if xs.len() == 0 {
        NEG_INF_BITS
    } else {
        spec_math_max_bits(xs[0], spec_math_max_seq(xs.subrange(1, xs.len() as int)))
    }
}

// ---------------------------------------------------------------------------------------
// Math Proofs: pow2 monotonicity, clz32 MSB bit-count theorem, imul algebra
// ---------------------------------------------------------------------------------------

proof fn lemma_pow2_pos(a: nat)
    ensures
        spec_pow2(a) >= 1,
    decreases a,
{
    if a > 0 {
        lemma_pow2_pos((a - 1) as nat);
    }
}

/// `spec_pow2` is strictly positive and strictly monotonic, with `2^32 == 4_294_967_296`.
pub proof fn lemma_pow2_properties(a: nat, b: nat)
    ensures
        spec_pow2(a) >= 1,
        a < b ==> spec_pow2(a) < spec_pow2(b),
        spec_pow2(32) == 4_294_967_296,
    decreases b,
{
    reveal_with_fuel(spec_pow2, 33);
    lemma_pow2_pos(a);
    if b > 0 {
        lemma_pow2_pos((b - 1) as nat);
        if a < (b - 1) as nat {
            lemma_pow2_properties(a, (b - 1) as nat);
        }
    }
}

/// Exact power-of-two bounds for `spec_bit_length(v)`.
pub proof fn lemma_bit_length_bounds(v: nat)
    ensures
        (v == 0) <==> (spec_bit_length(v) == 0),
        v > 0 ==> spec_pow2((spec_bit_length(v) - 1) as nat) <= v
            && v < spec_pow2(spec_bit_length(v)),
        v < 4_294_967_296 ==> spec_bit_length(v) <= 32,
    decreases v,
{
    if v > 0 {
        let half = v / 2;
        lemma_bit_length_bounds(half);
        if half > 0 {
            let bl_half = spec_bit_length(half);
            assert(spec_bit_length(v) == bl_half + 1);
            assert(spec_pow2(bl_half) == 2 * spec_pow2((bl_half - 1) as nat));
            assert(spec_pow2(bl_half + 1) == 2 * spec_pow2(bl_half));
        } else {
            assert(v == 1);
            assert(spec_bit_length(v) == 1);
            assert(spec_pow2(0) == 1);
            assert(spec_pow2(1) == 2);
        }
        if v < 4_294_967_296 {
            lemma_pow2_properties(32, spec_bit_length(v));
            if spec_bit_length(v) > 32 {
                lemma_pow2_properties(32, (spec_bit_length(v) - 1) as nat);
                assert(spec_pow2((spec_bit_length(v) - 1) as nat) >= 4_294_967_296);
            }
        }
    }
}

/// Leading-zero bit-count theorem for `Math.clz32`:
/// `clz32(0) == 32`, and for every `x > 0`, `c = clz32(x) <= 31` is the unique count of leading
/// zero bits in 32-bit binary representation (`2^(31 - c) <= x < 2^(32 - c)`).
pub proof fn lemma_clz32_bit_count(x: u32)
    ensures
        (x == 0) <==> (spec_clz32(x) == 32),
        x > 0 ==> spec_clz32(x) <= 31
            && spec_pow2((31 - spec_clz32(x)) as nat) <= x as nat
            && (x as nat) < spec_pow2((32 - spec_clz32(x)) as nat),
{
    lemma_bit_length_bounds(x as nat);
}

/// Uniqueness of `clz32` MSB position: if `2^(31 - k) <= x < 2^(32 - k)` for `k <= 31`, then `clz32(x) == k`.
pub proof fn lemma_clz32_unique(x: u32, k: nat)
    requires
        x > 0,
        k <= 31,
        spec_pow2((31 - k) as nat) <= x as nat,
        (x as nat) < spec_pow2((32 - k) as nat),
    ensures
        spec_clz32(x) == k,
{
    lemma_clz32_bit_count(x);
    let c = spec_clz32(x);
    if c < k {
        let e1: nat = (32 - k) as nat;
        let e2: nat = (31 - c) as nat;
        if e1 < e2 {
            lemma_pow2_properties(e1, e2);
        }
    } else if c > k {
        let e1: nat = (32 - c) as nat;
        let e2: nat = (31 - k) as nat;
        if e1 < e2 {
            lemma_pow2_properties(e1, e2);
        }
    }
}

/// `Math.imul` is commutative and stays within signed 32-bit bounds `[-2^31, 2^31 - 1]`.
pub proof fn lemma_imul_properties(a: u32, b: u32)
    ensures
        spec_imul(a, b) == spec_imul(b, a),
        -2_147_483_648 <= spec_imul(a, b) && spec_imul(a, b) <= 2_147_483_647,
{
    assert((a as int) * (b as int) == (b as int) * (a as int)) by (nonlinear_arith);
}

/// Signed-zero laws for `Math.abs`, `Math.sign`, `Math.min`, and `Math.max`.
pub proof fn lemma_math_signed_zero_laws()
    ensures
        spec_math_abs_bits(NEG_ZERO_BITS) == POS_ZERO_BITS,
        spec_math_sign_bits(NEG_ZERO_BITS) == NEG_ZERO_BITS,
        spec_math_sign_bits(POS_ZERO_BITS) == POS_ZERO_BITS,
        spec_math_min_bits(POS_ZERO_BITS, NEG_ZERO_BITS) == NEG_ZERO_BITS,
        spec_math_max_bits(NEG_ZERO_BITS, POS_ZERO_BITS) == POS_ZERO_BITS,
{
}

// ---------------------------------------------------------------------------------------
// Exec: Math operations
// ---------------------------------------------------------------------------------------

/// Exec `ToUint32` on `i64`.
pub fn to_uint32_i64(x: i64) -> (r: u32)
    ensures
        r == spec_to_uint32_int(x as int),
{
    let rem: i64 = x % 4_294_967_296i64;
    let m: i64 = if rem < 0 { rem + 4_294_967_296i64 } else { rem };
    m as u32
}

/// Exec `Math.clz32` (§21.3.2.11) proved equal to `spec_clz32` and satisfying the MSB bit-count bound.
pub fn math_clz32(x: u32) -> (c: u32)
    ensures
        c as nat == spec_clz32(x),
        (x == 0) <==> (c == 32),
        x > 0 ==> c <= 31
            && spec_pow2((31 - c) as nat) <= x as nat
            && (x as nat) < spec_pow2((32 - c) as nat),
{
    proof {
        lemma_bit_length_bounds(x as nat);
        lemma_clz32_bit_count(x);
    }
    let mut v: u32 = x;
    let mut bits: u32 = 0;
    while v > 0
        invariant
            bits as nat + spec_bit_length(v as nat) == spec_bit_length(x as nat),
            spec_bit_length(x as nat) <= 32,
            bits <= 32,
        decreases v,
    {
        proof {
            assert(spec_bit_length(v as nat) == 1 + spec_bit_length((v / 2) as nat));
        }
        v = v / 2;
        bits = bits + 1;
    }
    32 - bits
}

/// Exec `Math.imul` (§21.3.2.19) proved equal to `spec_imul`.
pub fn math_imul(a: u32, b: u32) -> (res: i32)
    ensures
        res as int == spec_imul(a, b),
{
    proof {
        assert((a as u64) * (b as u64) <= 0xFFFF_FFFFu64 * 0xFFFF_FFFFu64) by (nonlinear_arith);
        assert((a as u64) * (b as u64) == ((a as int) * (b as int)) as u64) by (nonlinear_arith);
    }
    let p: u64 = (a as u64) * (b as u64);
    let prod: u64 = p % 4_294_967_296u64;
    if prod >= 2_147_483_648u64 {
        ((prod as i64) - 4_294_967_296i64) as i32
    } else {
        prod as i32
    }
}

/// Exec `Math.abs` on IEEE-754 binary64 bit patterns (§21.3.2.1).
pub fn math_abs_bits(bits: u64) -> (res: u64)
    ensures
        res == spec_math_abs_bits(bits),
{
    if is_nan_bits(bits) {
        CANONICAL_NAN_BITS
    } else if bits >= NEG_ZERO_BITS {
        bits - NEG_ZERO_BITS
    } else {
        bits
    }
}

/// Exec `Math.abs` on `i64` (`None` only for `i64::MIN`).
pub fn math_abs_i64(x: i64) -> (res: Option<i64>)
    ensures
        x == i64::MIN ==> res.is_none(),
        x > i64::MIN ==> res == Some((if x < 0 { -(x as int) } else { x as int }) as i64),
{
    if x == i64::MIN {
        None
    } else if x < 0 {
        Some(-x)
    } else {
        Some(x)
    }
}

/// Exec `Math.sign` on IEEE-754 binary64 bit patterns (§21.3.2.29).
pub fn math_sign_bits(bits: u64) -> (res: u64)
    ensures
        res == spec_math_sign_bits(bits),
{
    if is_nan_bits(bits) {
        CANONICAL_NAN_BITS
    } else if bits == NEG_ZERO_BITS {
        NEG_ZERO_BITS
    } else if bits == POS_ZERO_BITS {
        POS_ZERO_BITS
    } else if bits > NEG_ZERO_BITS {
        NEG_ONE_BITS
    } else {
        POS_ONE_BITS
    }
}

/// Exec `Math.sign` on `i64`.
pub fn math_sign_i64(x: i64) -> (res: i64)
    ensures
        x < 0 ==> res == -1,
        x == 0 ==> res == 0,
        x > 0 ==> res == 1,
{
    if x < 0 {
        -1
    } else if x == 0 {
        0
    } else {
        1
    }
}

fn ieee_le_non_nan(a: u64, b: u64) -> (res: bool)
    ensures
        res == spec_ieee_le_non_nan(a, b),
{
    if a >= NEG_ZERO_BITS && b >= NEG_ZERO_BITS {
        a >= b
    } else if a >= NEG_ZERO_BITS && b < NEG_ZERO_BITS {
        true
    } else if a < NEG_ZERO_BITS && b >= NEG_ZERO_BITS {
        false
    } else {
        a <= b
    }
}

/// Exec `Math.min ( a, b )` on IEEE-754 binary64 bit patterns (§21.3.2.25).
pub fn math_min_bits(a: u64, b: u64) -> (res: u64)
    ensures
        res == spec_math_min_bits(a, b),
{
    if is_nan_bits(a) || is_nan_bits(b) {
        CANONICAL_NAN_BITS
    } else if ieee_le_non_nan(a, b) {
        a
    } else {
        b
    }
}

/// Exec `Math.max ( a, b )` on IEEE-754 binary64 bit patterns (§21.3.2.24).
pub fn math_max_bits(a: u64, b: u64) -> (res: u64)
    ensures
        res == spec_math_max_bits(a, b),
{
    if is_nan_bits(a) || is_nan_bits(b) {
        CANONICAL_NAN_BITS
    } else if ieee_le_non_nan(a, b) {
        b
    } else {
        a
    }
}

/// Exec variadic `Math.min` over a slice (`+Infinity` on empty slice).
pub fn math_min_slice(xs: &[u64]) -> (res: u64)
    ensures
        res == spec_math_min_seq(xs@),
{
    let mut acc: u64 = POS_INF_BITS;
    let mut k: usize = xs.len();
    proof {
        assert(xs@.subrange(k as int, xs@.len() as int) =~= Seq::<u64>::empty());
    }
    while k > 0
        invariant
            k <= xs@.len(),
            acc == spec_math_min_seq(xs@.subrange(k as int, xs@.len() as int)),
        decreases k,
    {
        k -= 1;
        let ghost sub = xs@.subrange(k as int, xs@.len() as int);
        proof {
            assert(sub[0] == xs@[k as int]);
            assert(sub.subrange(1, sub.len() as int) =~= xs@.subrange(k as int + 1, xs@.len() as int));
        }
        acc = math_min_bits(xs[k], acc);
    }
    proof {
        assert(xs@.subrange(0, xs@.len() as int) =~= xs@);
    }
    acc
}

/// Exec variadic `Math.max` over a slice (`-Infinity` on empty slice).
pub fn math_max_slice(xs: &[u64]) -> (res: u64)
    ensures
        res == spec_math_max_seq(xs@),
{
    let mut acc: u64 = NEG_INF_BITS;
    let mut k: usize = xs.len();
    proof {
        assert(xs@.subrange(k as int, xs@.len() as int) =~= Seq::<u64>::empty());
    }
    while k > 0
        invariant
            k <= xs@.len(),
            acc == spec_math_max_seq(xs@.subrange(k as int, xs@.len() as int)),
        decreases k,
    {
        k -= 1;
        let ghost sub = xs@.subrange(k as int, xs@.len() as int);
        proof {
            assert(sub[0] == xs@[k as int]);
            assert(sub.subrange(1, sub.len() as int) =~= xs@.subrange(k as int + 1, xs@.len() as int));
        }
        acc = math_max_bits(xs[k], acc);
    }
    proof {
        assert(xs@.subrange(0, xs@.len() as int) =~= xs@);
    }
    acc
}

/// Exec `Math.min` on `i64`.
pub fn math_min_i64(a: i64, b: i64) -> (res: i64)
    ensures
        res <= a && res <= b,
        res == a || res == b,
{
    if a <= b { a } else { b }
}

/// Exec `Math.max` on `i64`.
pub fn math_max_i64(a: i64, b: i64) -> (res: i64)
    ensures
        res >= a && res >= b,
        res == a || res == b,
{
    if a >= b { a } else { b }
}

// =======================================================================================
// 2. Verified `Array` (§23.1.3)
// =======================================================================================

/// ECMA-262 relative index resolution (`start` / `end` clamping in `Array.prototype.slice` & `String.prototype.slice`).
pub open spec fn spec_resolve_slice_bound(idx: int, len: nat) -> nat {
    if idx < 0 {
        if (len as int) + idx > 0 {
            ((len as int) + idx) as nat
        } else {
            0
        }
    } else if idx < len as int {
        idx as nat
    } else {
        len
    }
}

/// ECMA-262 §23.1.3.28 `Array.prototype.slice ( start, end )`.
pub open spec fn spec_array_slice(arr: Seq<SpecJsKey>, start: int, end: Option<int>) -> Seq<SpecJsKey> {
    let len = arr.len();
    let k = spec_resolve_slice_bound(start, len);
    let fin = match end {
        None => len,
        Some(e) => spec_resolve_slice_bound(e, len),
    };
    if k < fin {
        arr.subrange(k as int, fin as int)
    } else {
        Seq::empty()
    }
}

/// ECMA-262 §23.1.3.24 `Array.prototype.reverse ( )`.
pub open spec fn spec_array_reverse(arr: Seq<SpecJsKey>) -> Seq<SpecJsKey> {
    Seq::new(arr.len(), |i: int| arr[arr.len() - 1 - i])
}

/// Starting index `k` for `Array.prototype.indexOf` / `includes` (§23.1.3.13 / §23.1.3.14).
pub open spec fn spec_search_from_index(from_index: int, len: nat) -> nat {
    if from_index >= len as int {
        len
    } else if from_index >= 0 {
        from_index as nat
    } else if (len as int) + from_index > 0 {
        ((len as int) + from_index) as nat
    } else {
        0
    }
}

/// Helper: smallest index `>= k` strictly equal (`===`) to `search`, or `-1`.
pub open spec fn spec_array_index_of_from(arr: Seq<SpecJsKey>, search: SpecJsKey, k: nat) -> int
    decreases (if k <= arr.len() { arr.len() - k } else { 0 }),
{
    if k >= arr.len() {
        -1
    } else if spec_is_strictly_equal(arr[k as int], search) {
        k as int
    } else {
        spec_array_index_of_from(arr, search, k + 1)
    }
}

/// ECMA-262 §23.1.3.14 `Array.prototype.indexOf ( searchElement, fromIndex )`.
pub open spec fn spec_array_index_of(arr: Seq<SpecJsKey>, search: SpecJsKey, from_index: int) -> int {
    if arr.len() == 0 {
        -1
    } else {
        spec_array_index_of_from(arr, search, spec_search_from_index(from_index, arr.len()))
    }
}

/// Helper: whether any index `>= k` is `SameValueZero`-equal to `search`.
pub open spec fn spec_array_includes_from(arr: Seq<SpecJsKey>, search: SpecJsKey, k: nat) -> bool
    decreases (if k <= arr.len() { arr.len() - k } else { 0 }),
{
    if k >= arr.len() {
        false
    } else if spec_same_value_zero(arr[k as int], search) {
        true
    } else {
        spec_array_includes_from(arr, search, k + 1)
    }
}

/// ECMA-262 §23.1.3.13 `Array.prototype.includes ( searchElement, fromIndex )`.
pub open spec fn spec_array_includes(arr: Seq<SpecJsKey>, search: SpecJsKey, from_index: int) -> bool {
    if arr.len() == 0 {
        false
    } else {
        spec_array_includes_from(arr, search, spec_search_from_index(from_index, arr.len()))
    }
}

/// `spec_array_reverse` is an involution (`reverse(reverse(s)) == s`).
pub proof fn lemma_array_reverse_involution(arr: Seq<SpecJsKey>)
    ensures
        spec_array_reverse(spec_array_reverse(arr)) == arr,
{
    assert(spec_array_reverse(spec_array_reverse(arr)) =~= arr);
}

/// Classic ECMAScript distinction theorem: `[NaN].includes(NaN) == true` whereas `[NaN].indexOf(NaN) == -1`.
pub proof fn lemma_array_includes_vs_index_of_nan(nan1: u64, nan2: u64)
    requires
        spec_is_nan_bits(nan1),
        spec_is_nan_bits(nan2),
    ensures
        spec_array_includes(seq![SpecJsKey::NumberBits(nan1)], SpecJsKey::NumberBits(nan2), 0),
        spec_array_index_of(seq![SpecJsKey::NumberBits(nan1)], SpecJsKey::NumberBits(nan2), 0) == -1,
{
    reveal_with_fuel(spec_array_includes_from, 2);
    reveal_with_fuel(spec_array_index_of_from, 2);
}

fn resolve_slice_bound(idx: i64, len: usize) -> (res: usize)
    ensures
        res as nat == spec_resolve_slice_bound(idx as int, len as nat),
        res <= len,
{
    if idx < 0 {
        let neg_dist: u64 = if idx == i64::MIN {
            0x8000_0000_0000_0000u64
        } else {
            (-idx) as u64
        };
        if (len as u64) > neg_dist {
            ((len as u64) - neg_dist) as usize
        } else {
            0
        }
    } else if (idx as u64) < (len as u64) {
        idx as usize
    } else {
        len
    }
}

fn resolve_search_from(from_index: i64, len: usize) -> (res: usize)
    ensures
        res as nat == spec_search_from_index(from_index as int, len as nat),
        res <= len,
{
    if from_index >= 0 {
        if (from_index as u64) >= (len as u64) {
            len
        } else {
            from_index as usize
        }
    } else {
        let neg_dist: u64 = if from_index == i64::MIN {
            0x8000_0000_0000_0000u64
        } else {
            (-from_index) as u64
        };
        if (len as u64) > neg_dist {
            ((len as u64) - neg_dist) as usize
        } else {
            0
        }
    }
}

/// Exec `Array.prototype.push ( elem )` (§23.1.3.23).
pub fn array_push(arr: &mut Vec<JsKey>, elem: JsKey) -> (new_len: usize)
    ensures
        spec_keys_view(final(arr)@) == spec_keys_view(old(arr)@).push(elem@),
        new_len == final(arr)@.len(),
{
    arr.push(elem);
    proof {
        assert(spec_keys_view(arr@) =~= spec_keys_view(old(arr)@).push(elem@));
    }
    arr.len()
}

/// Exec `Array.prototype.pop ( )` (§23.1.3.22).
pub fn array_pop(arr: &mut Vec<JsKey>) -> (res: Option<JsKey>)
    ensures
        old(arr)@.len() == 0 ==> res.is_none() && final(arr)@.len() == 0,
        old(arr)@.len() > 0 ==> {
            &&& res.is_some()
            &&& res.unwrap()@ == spec_keys_view(old(arr)@)[old(arr)@.len() - 1]
            &&& spec_keys_view(final(arr)@)
                == spec_keys_view(old(arr)@).subrange(0, old(arr)@.len() - 1)
        },
{
    if arr.len() == 0 {
        None
    } else {
        let v = arr.pop();
        proof {
            assert(spec_keys_view(arr@) =~= spec_keys_view(old(arr)@).subrange(0, old(arr)@.len() - 1));
        }
        v
    }
}

/// Exec `Array.prototype.slice ( start, end )` (§23.1.3.28).
pub fn array_slice(arr: &[JsKey], start: i64, end: Option<i64>) -> (out: Vec<JsKey>)
    ensures
        spec_keys_view(out@)
            == spec_array_slice(
                spec_keys_view(arr@),
                start as int,
                match end {
                    Some(e) => Some(e as int),
                    None => None,
                },
            ),
{
    let len = arr.len();
    let k = resolve_slice_bound(start, len);
    let fin = match end {
        None => len,
        Some(e) => resolve_slice_bound(e, len),
    };
    let mut out: Vec<JsKey> = Vec::new();
    if k < fin {
        let mut i: usize = k;
        while i < fin
            invariant
                k <= i <= fin <= len,
                len == arr@.len(),
                out@.len() == (i - k) as int,
                forall|j: int| 0 <= j < out@.len() ==> out@[j]@ == arr@[k as int + j]@,
            decreases fin - i,
        {
            out.push(clone_js_key(&arr[i]));
            i += 1;
        }
    }
    proof {
        let ghost sv = spec_keys_view(arr@);
        let ghost se = match end {
            Some(e) => Some(e as int),
            None => None::<int>,
        };
        assert(spec_keys_view(out@) =~= spec_array_slice(sv, start as int, se));
    }
    out
}

/// Exec `Array.prototype.concat` (§23.1.3.1).
pub fn array_concat(a: &[JsKey], b: &[JsKey]) -> (out: Vec<JsKey>)
    ensures
        spec_keys_view(out@) == spec_keys_view(a@) + spec_keys_view(b@),
{
    let mut out: Vec<JsKey> = Vec::new();
    let na = a.len();
    let nb = b.len();
    let mut i: usize = 0;
    while i < na
        invariant
            i <= na,
            na == a@.len(),
            out@.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> out@[j]@ == a@[j]@,
        decreases na - i,
    {
        out.push(clone_js_key(&a[i]));
        i += 1;
    }
    let mut k: usize = 0;
    while k < nb
        invariant
            k <= nb,
            na == a@.len(),
            nb == b@.len(),
            out@.len() == (na + k) as int,
            forall|j: int| 0 <= j < na as int ==> out@[j]@ == a@[j]@,
            forall|j: int| 0 <= j < k as int ==> out@[na as int + j]@ == b@[j]@,
        decreases nb - k,
    {
        out.push(clone_js_key(&b[k]));
        k += 1;
    }
    proof {
        assert(spec_keys_view(out@) =~= spec_keys_view(a@) + spec_keys_view(b@));
    }
    out
}

/// Exec in-place `Array.prototype.reverse ( )` (§23.1.3.24).
pub fn array_reverse(arr: &mut Vec<JsKey>)
    ensures
        spec_keys_view(final(arr)@) == spec_array_reverse(spec_keys_view(old(arr)@)),
{
    let n = arr.len();
    let mut lo: usize = 0;
    while lo < n / 2
        invariant
            lo <= n / 2,
            arr@.len() == n,
            n == old(arr)@.len(),
            forall|i: int| 0 <= i < lo as int ==> arr@[i]@ == old(arr)@[n as int - 1 - i]@,
            forall|i: int|
                n as int - lo as int <= i < n as int ==> arr@[i]@ == old(arr)@[n as int - 1 - i]@,
            forall|i: int| lo as int <= i < n as int - lo as int ==> arr@[i]@ == old(arr)@[i]@,
        decreases n / 2 - lo,
    {
        let hi = n - 1 - lo;
        let left = clone_js_key(&arr[lo]);
        let right = clone_js_key(&arr[hi]);
        arr.set(lo, right);
        arr.set(hi, left);
        lo += 1;
    }
    proof {
        assert(spec_keys_view(arr@) =~= spec_array_reverse(spec_keys_view(old(arr)@)));
    }
}

/// Exec `Array.prototype.indexOf ( searchElement, fromIndex )` (§23.1.3.14, `===`).
pub fn array_index_of(arr: &[JsKey], search: &JsKey, from_index: i64) -> (res: i64)
    requires
        arr@.len() <= i64::MAX as int,
    ensures
        res as int == spec_array_index_of(spec_keys_view(arr@), search@, from_index as int),
{
    let len = arr.len();
    if len == 0 {
        return -1;
    }
    let start = resolve_search_from(from_index, len);
    let mut idx: usize = len;
    let mut found: Option<usize> = None;
    while idx > start
        invariant
            start <= idx <= len,
            len == arr@.len(),
            len <= i64::MAX as int,
            match found {
                Some(f) => f < len && f as int == spec_array_index_of_from(spec_keys_view(arr@), search@, idx as nat),
                None => spec_array_index_of_from(spec_keys_view(arr@), search@, idx as nat) == -1,
            },
        decreases idx - start,
    {
        idx -= 1;
        let ghost sv = spec_keys_view(arr@);
        proof {
            assert(sv[idx as int] == arr@[idx as int]@);
        }
        if is_strictly_equal(&arr[idx], search) {
            found = Some(idx);
        }
    }
    match found {
        Some(f) => f as i64,
        None => -1,
    }
}

/// Exec `Array.prototype.includes ( searchElement, fromIndex )` (§23.1.3.13, `SameValueZero`).
pub fn array_includes(arr: &[JsKey], search: &JsKey, from_index: i64) -> (res: bool)
    ensures
        res == spec_array_includes(spec_keys_view(arr@), search@, from_index as int),
{
    let len = arr.len();
    if len == 0 {
        return false;
    }
    let start = resolve_search_from(from_index, len);
    let mut idx: usize = len;
    let mut acc: bool = false;
    while idx > start
        invariant
            start <= idx <= len,
            len == arr@.len(),
            acc == spec_array_includes_from(spec_keys_view(arr@), search@, idx as nat),
        decreases idx - start,
    {
        idx -= 1;
        let ghost sv = spec_keys_view(arr@);
        proof {
            assert(sv[idx as int] == arr@[idx as int]@);
        }
        if same_value_zero(&arr[idx], search) {
            acc = true;
        }
    }
    acc
}

// =======================================================================================
// 3. Verified `String` (UTF-16 `&[u16]`, §22.1.3)
// =======================================================================================

/// ECMA-262 §22.1.3.22 `String.prototype.slice ( start, end )`.
pub open spec fn spec_string_slice(s: Seq<u16>, start: int, end: Option<int>) -> Seq<u16> {
    let len = s.len();
    let k = spec_resolve_slice_bound(start, len);
    let fin = match end {
        None => len,
        Some(e) => spec_resolve_slice_bound(e, len),
    };
    if k < fin {
        s.subrange(k as int, fin as int)
    } else {
        Seq::empty()
    }
}

/// Clamping helper `[0, len]` for `String.prototype.substring`, `indexOf`, `startsWith`, `endsWith`.
pub open spec fn spec_clamp_index(idx: int, len: nat) -> nat {
    if idx <= 0 {
        0
    } else if idx >= len as int {
        len
    } else {
        idx as nat
    }
}

/// ECMA-262 §22.1.3.25 `String.prototype.substring ( start, end )`:
/// clamps negative values to `0`, clamps `> len` to `len`, and swaps if `finalStart > finalEnd`.
pub open spec fn spec_string_substring(s: Seq<u16>, start: int, end: Option<int>) -> Seq<u16> {
    let len = s.len();
    let fs = spec_clamp_index(start, len);
    let fe = match end {
        None => len,
        Some(e) => spec_clamp_index(e, len),
    };
    let from = if fs <= fe { fs } else { fe };
    let to = if fs <= fe { fe } else { fs };
    s.subrange(from as int, to as int)
}

/// Smallest index `k` in `[pos, s.len() - search.len()]` where `s[k..k+search.len()] == search`, or `-1`.
pub open spec fn spec_string_index_of_from(s: Seq<u16>, search: Seq<u16>, k: nat) -> int
    decreases (if k + search.len() <= s.len() { (s.len() + 1) - (k + search.len()) } else { 0 }),
{
    if k + search.len() > s.len() {
        -1
    } else if s.subrange(k as int, (k + search.len()) as int) == search {
        k as int
    } else {
        spec_string_index_of_from(s, search, k + 1)
    }
}

/// ECMA-262 §22.1.3.9 `String.prototype.indexOf ( searchString, position )`.
pub open spec fn spec_string_index_of(s: Seq<u16>, search: Seq<u16>, position: int) -> int {
    let start = spec_clamp_index(position, s.len());
    spec_string_index_of_from(s, search, start)
}

/// ECMA-262 §22.1.3.24 `String.prototype.startsWith ( searchString, position )`.
pub open spec fn spec_string_starts_with(
    s: Seq<u16>,
    search: Seq<u16>,
    position: Option<int>,
) -> bool {
    let start = match position {
        None => 0nat,
        Some(p) => spec_clamp_index(p, s.len()),
    };
    start + search.len() <= s.len()
        && s.subrange(start as int, (start + search.len()) as int) == search
}

/// ECMA-262 §22.1.3.7 `String.prototype.endsWith ( searchString, endPosition )`.
pub open spec fn spec_string_ends_with(
    s: Seq<u16>,
    search: Seq<u16>,
    end_position: Option<int>,
) -> bool {
    let end = match end_position {
        None => s.len(),
        Some(p) => spec_clamp_index(p, s.len()),
    };
    search.len() <= end && s.subrange((end - search.len()) as int, end as int) == search
}

/// Code-unit case folding to lowercase (ASCII `A-Z` + Latin-1 `À-Ö`, `Ø-Þ`).
pub open spec fn spec_char_to_lower(c: u16) -> u16 {
    if (0x0041 <= c && c <= 0x005A)
        || (0x00C0 <= c && c <= 0x00D6)
        || (0x00D8 <= c && c <= 0x00DE)
    {
        (c + 32) as u16
    } else {
        c
    }
}

/// Code-unit case folding to uppercase (ASCII `a-z` + Latin-1 `à-ö`, `ø-þ`).
pub open spec fn spec_char_to_upper(c: u16) -> u16 {
    if (0x0061 <= c && c <= 0x007A)
        || (0x00E0 <= c && c <= 0x00F6)
        || (0x00F8 <= c && c <= 0x00FE)
    {
        (c - 32) as u16
    } else {
        c
    }
}

/// ECMA-262 §22.1.3.28 `String.prototype.toLowerCase ( )`.
pub open spec fn spec_string_to_lower(s: Seq<u16>) -> Seq<u16> {
    Seq::new(s.len(), |i: int| spec_char_to_lower(s[i]))
}

/// ECMA-262 §22.1.3.30 `String.prototype.toUpperCase ( )`.
pub open spec fn spec_string_to_upper(s: Seq<u16>) -> Seq<u16> {
    Seq::new(s.len(), |i: int| spec_char_to_upper(s[i]))
}

/// ECMA-262 §22.1.3.17 `String.prototype.repeat ( count )`.
pub open spec fn spec_string_repeat(s: Seq<u16>, count: nat) -> Seq<u16>
    decreases count,
{
    if count == 0 {
        Seq::empty()
    } else {
        spec_string_repeat(s, (count - 1) as nat) + s
    }
}

/// Soundness and minimality theorem for `String.prototype.indexOf`.
pub proof fn lemma_string_index_of_sound_and_minimal(s: Seq<u16>, search: Seq<u16>, k: nat)
    ensures
        ({
            let r = spec_string_index_of_from(s, search, k);
            if r >= 0 {
                &&& r >= k as int
                &&& r + (search.len() as int) <= s.len() as int
                &&& s.subrange(r, r + (search.len() as int)) == search
                &&& forall|j: int|
                    k as int <= j < r ==> #[trigger] s.subrange(j, j + (search.len() as int)) != search
            } else {
                &&& r == -1
                &&& forall|j: int|
                    k as int <= j && j + (search.len() as int) <= s.len() as int
                        ==> #[trigger] s.subrange(j, j + (search.len() as int)) != search
            }
        }),
    decreases (if k + search.len() <= s.len() { (s.len() + 1) - (k + search.len()) } else { 0 }),
{
    if k + search.len() <= s.len() && s.subrange(k as int, (k + search.len()) as int) != search {
        lemma_string_index_of_sound_and_minimal(s, search, k + 1);
    }
}

/// Idempotence of `toLowerCase` and `toUpperCase`.
pub proof fn lemma_string_case_idempotent(s: Seq<u16>)
    ensures
        spec_string_to_lower(spec_string_to_lower(s)) == spec_string_to_lower(s),
        spec_string_to_upper(spec_string_to_upper(s)) == spec_string_to_upper(s),
{
    assert(spec_string_to_lower(spec_string_to_lower(s)) =~= spec_string_to_lower(s));
    assert(spec_string_to_upper(spec_string_to_upper(s)) =~= spec_string_to_upper(s));
}

/// Length theorem for `String.prototype.repeat`: `repeat(s, count).len() == s.len() * count`.
pub proof fn lemma_string_repeat_len(s: Seq<u16>, count: nat)
    ensures
        spec_string_repeat(s, count).len() == s.len() * count,
    decreases count,
{
    let n = s.len();
    if count > 0 {
        let c1 = (count - 1) as nat;
        lemma_string_repeat_len(s, c1);
        assert(n * count == n * c1 + n) by (nonlinear_arith)
            requires
                count == c1 + 1,
        ;
    } else {
        assert(n * 0 == 0) by (nonlinear_arith);
    }
}

fn clamp_index(idx: i64, len: usize) -> (res: usize)
    ensures
        res as nat == spec_clamp_index(idx as int, len as nat),
        res <= len,
{
    if idx <= 0 {
        0
    } else if (idx as u64) >= (len as u64) {
        len
    } else {
        idx as usize
    }
}

fn copy_subslice(s: &[u16], from: usize, to: usize) -> (out: Vec<u16>)
    requires
        from <= to <= s@.len(),
    ensures
        out@ == s@.subrange(from as int, to as int),
{
    let mut out: Vec<u16> = Vec::new();
    let mut i: usize = from;
    while i < to
        invariant
            from <= i <= to <= s@.len(),
            out@.len() == (i - from) as int,
            forall|j: int| 0 <= j < out@.len() ==> out@[j] == s@[from as int + j],
        decreases to - i,
    {
        out.push(s[i]);
        i += 1;
    }
    proof {
        assert(out@ =~= s@.subrange(from as int, to as int));
    }
    out
}

/// Exec `String.prototype.slice ( start, end )` (§22.1.3.22).
pub fn string_slice(s: &[u16], start: i64, end: Option<i64>) -> (out: Vec<u16>)
    ensures
        out@
            == spec_string_slice(
                s@,
                start as int,
                match end {
                    Some(e) => Some(e as int),
                    None => None,
                },
            ),
{
    let len = s.len();
    let k = resolve_slice_bound(start, len);
    let fin = match end {
        None => len,
        Some(e) => resolve_slice_bound(e, len),
    };
    if k < fin {
        copy_subslice(s, k, fin)
    } else {
        let empty: Vec<u16> = Vec::new();
        proof {
            assert(empty@ =~= Seq::<u16>::empty());
        }
        empty
    }
}

/// Exec `String.prototype.substring ( start, end )` (§22.1.3.25).
pub fn string_substring(s: &[u16], start: i64, end: Option<i64>) -> (out: Vec<u16>)
    ensures
        out@
            == spec_string_substring(
                s@,
                start as int,
                match end {
                    Some(e) => Some(e as int),
                    None => None,
                },
            ),
{
    let len = s.len();
    let fs = clamp_index(start, len);
    let fe = match end {
        None => len,
        Some(e) => clamp_index(e, len),
    };
    let (from, to) = if fs <= fe { (fs, fe) } else { (fe, fs) };
    copy_subslice(s, from, to)
}

fn matches_at(s: &[u16], search: &[u16], pos: usize) -> (res: bool)
    requires
        pos <= s@.len(),
        search@.len() <= s@.len() - pos,
    ensures
        res == (s@.subrange(pos as int, (pos + search.len()) as int) == search@),
{
    let m = search.len();
    let mut i: usize = 0;
    while i < m
        invariant
            i <= m,
            m == search@.len(),
            pos <= s.len(),
            m <= s.len() - pos,
            forall|j: int| 0 <= j < i as int ==> s@[pos as int + j] == search@[j],
        decreases m - i,
    {
        if s[pos + i] != search[i] {
            proof {
                assert(s@.subrange(pos as int, (pos + m) as int)[i as int] != search@[i as int]);
            }
            return false;
        }
        i += 1;
    }
    proof {
        assert(s@.subrange(pos as int, (pos + m) as int) =~= search@);
    }
    true
}

/// Exec `String.prototype.indexOf ( searchString, position )` (§22.1.3.9).
pub fn string_index_of(s: &[u16], search: &[u16], position: i64) -> (res: i64)
    requires
        s@.len() <= i64::MAX as int,
    ensures
        res as int == spec_string_index_of(s@, search@, position as int),
{
    let len = s.len();
    let m = search.len();
    let start = clamp_index(position, len);
    if m > len || start > len - m {
        return -1;
    }
    let last = len - m;
    let mut best: Option<usize> = if matches_at(s, search, last) {
        Some(last)
    } else {
        None
    };
    proof {
        assert(spec_string_index_of_from(s@, search@, (last + 1) as nat) == -1);
    }
    let mut idx: usize = last;
    while idx > start
        invariant
            start <= idx <= last,
            last + m == len,
            len == s@.len(),
            m == search@.len(),
            len <= i64::MAX as int,
            match best {
                Some(b) => b <= last && b as int == spec_string_index_of_from(s@, search@, idx as nat),
                None => spec_string_index_of_from(s@, search@, idx as nat) == -1,
            },
        decreases idx - start,
    {
        idx -= 1;
        if matches_at(s, search, idx) {
            best = Some(idx);
        }
    }
    match best {
        Some(b) => b as i64,
        None => -1,
    }
}

/// Exec `String.prototype.startsWith ( searchString, position )` (§22.1.3.24).
pub fn string_starts_with(s: &[u16], search: &[u16], position: Option<i64>) -> (res: bool)
    ensures
        res
            == spec_string_starts_with(
                s@,
                search@,
                match position {
                    Some(p) => Some(p as int),
                    None => None,
                },
            ),
{
    let len = s.len();
    let start = match position {
        None => 0usize,
        Some(p) => clamp_index(p, len),
    };
    if search.len() > len - start {
        false
    } else {
        matches_at(s, search, start)
    }
}

/// Exec `String.prototype.endsWith ( searchString, endPosition )` (§22.1.3.7).
pub fn string_ends_with(s: &[u16], search: &[u16], end_position: Option<i64>) -> (res: bool)
    ensures
        res
            == spec_string_ends_with(
                s@,
                search@,
                match end_position {
                    Some(p) => Some(p as int),
                    None => None,
                },
            ),
{
    let len = s.len();
    let end = match end_position {
        None => len,
        Some(p) => clamp_index(p, len),
    };
    if search.len() > end {
        false
    } else {
        matches_at(s, search, end - search.len())
    }
}

/// Exec `String.prototype.toLowerCase ( )` (§22.1.3.28).
pub fn string_to_lower_case(s: &[u16]) -> (out: Vec<u16>)
    ensures
        out@ == spec_string_to_lower(s@),
{
    let n = s.len();
    let mut out: Vec<u16> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == s@.len(),
            out@.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> out@[j] == spec_char_to_lower(s@[j]),
        decreases n - i,
    {
        let c = s[i];
        let lc = if (c >= 0x0041 && c <= 0x005A)
            || (c >= 0x00C0 && c <= 0x00D6)
            || (c >= 0x00D8 && c <= 0x00DE)
        {
            c + 32
        } else {
            c
        };
        out.push(lc);
        i += 1;
    }
    proof {
        assert(out@ =~= spec_string_to_lower(s@));
    }
    out
}

/// Exec `String.prototype.toUpperCase ( )` (§22.1.3.30).
pub fn string_to_upper_case(s: &[u16]) -> (out: Vec<u16>)
    ensures
        out@ == spec_string_to_upper(s@),
{
    let n = s.len();
    let mut out: Vec<u16> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == s@.len(),
            out@.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> out@[j] == spec_char_to_upper(s@[j]),
        decreases n - i,
    {
        let c = s[i];
        let uc = if (c >= 0x0061 && c <= 0x007A)
            || (c >= 0x00E0 && c <= 0x00F6)
            || (c >= 0x00F8 && c <= 0x00FE)
        {
            c - 32
        } else {
            c
        };
        out.push(uc);
        i += 1;
    }
    proof {
        assert(out@ =~= spec_string_to_upper(s@));
    }
    out
}

/// Exec `String.prototype.repeat ( count )` (§22.1.3.17) with verified `max_len` quota check.
pub fn string_repeat(s: &[u16], count: usize, max_len: usize) -> (res: Option<Vec<u16>>)
    ensures
        (s@.len() * (count as nat) > max_len as nat) ==> res.is_none(),
        (s@.len() * (count as nat) <= max_len as nat) ==> {
            &&& res.is_some()
            &&& res.unwrap()@ == spec_string_repeat(s@, count as nat)
            &&& res.unwrap()@.len() == s@.len() * (count as nat)
        },
{
    let slen = s.len();
    if slen == 0 || count == 0 {
        let empty: Vec<u16> = Vec::new();
        proof {
            lemma_string_repeat_len(s@, count as nat);
            assert(empty@ =~= spec_string_repeat(s@, count as nat));
        }
        return Some(empty);
    }
    if count > max_len / slen {
        proof {
            let q = max_len / slen;
            let r = max_len % slen;
            assert((slen as nat) * (count as nat) > max_len as nat) by (nonlinear_arith)
                requires
                    slen > 0,
                    q == max_len / slen,
                    r == max_len % slen,
                    count > q,
            ;
        }
        return None;
    }
    proof {
        let q = max_len / slen;
        let r = max_len % slen;
        assert((slen as nat) * (count as nat) <= max_len as nat) by (nonlinear_arith)
            requires
                slen > 0,
                q == max_len / slen,
                r == max_len % slen,
                count <= q,
        ;
        lemma_string_repeat_len(s@, count as nat);
    }
    let mut out: Vec<u16> = Vec::new();
    let mut rep: usize = 0;
    proof {
        assert(out@ =~= spec_string_repeat(s@, 0));
    }
    while rep < count
        invariant
            rep <= count,
            slen == s@.len(),
            out@ == spec_string_repeat(s@, rep as nat),
        decreases count - rep,
    {
        let ghost prev = out@;
        let mut i: usize = 0;
        while i < slen
            invariant
                i <= slen,
                slen == s@.len(),
                out@ == prev + s@.subrange(0, i as int),
            decreases slen - i,
        {
            out.push(s[i]);
            i += 1;
            proof {
                assert(out@ =~= prev + s@.subrange(0, i as int));
            }
        }
        rep += 1;
        proof {
            assert(s@.subrange(0, slen as int) =~= s@);
            assert(out@ =~= spec_string_repeat(s@, rep as nat));
        }
    }
    Some(out)
}

} // verus!
