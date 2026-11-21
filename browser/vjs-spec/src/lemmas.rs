//! Machine-checked algebraic metatheorems over the generated ECMA-262 specification
//! functions in `crate::generated` (§6.1.6.1, §7.1, §7.2).
//!
//! Proves:
//! - `SameType`, `SameValue`, and `SameValueZero` are equivalence relations (reflexive,
//!   symmetric, transitive), with `SameValueZero` strictly coarsening `SameValue` solely
//!   on `(+0_𝔽, -0_𝔽)` and `(-0_𝔽, +0_𝔽)` (§7.2.10 note).
//! - `IsStrictlyEqual` (`===`) is symmetric and transitive, reflexive iff not `NaN`, and
//!   agrees with `SameValueZero` on all non-`NaN` language values.
//! - `IsLooselyEqual` (`==`) is unconditionally symmetric across ALL ECMAScript language
//!   values (including `null`/`undefined`, `Boolean`, `String`, `Number`, `BigInt`,
//!   `Symbol`, `[[IsHTMLDDA]]` exotic objects, and throwing `ToPrimitive` objects), while
//!   provably non-transitive (`"0" == 0` and `0 == ""` hold, yet `"0" == ""` is false).
//! - `ToFixedSizeInteger` satisfies ECMA-262 §7.1.7's `<emu-note>`: idempotence AND
//!   invariance under inversion of `~signed~` / `~unsigned~` for every bit-width `1..=32`.
//! - `ToInt32`, `ToUint32`, and `ToUint16` are idempotent, cross-idempotent
//!   (`ToUint32(ToInt32(x)) == ToUint32(x)`, `ToInt32(ToUint32(x)) == ToInt32(x)`), and
//!   never return `*-0*_𝔽`.
//! - `Number::bitwiseNOT`, `NumberBitwiseOp`, `Number::bitwiseAND`, `Number::bitwiseXOR`,
//!   and `Number::bitwiseOR` satisfy double-complement involution (`~~x == ToInt32(x)`),
//!   commutativity, self-XOR annihilation (`x ^ x == +0_𝔽`), and De Morgan's law
//!   (`~(x & y) == (~x) | (~y)`).
use vstd::prelude::*;
#[allow(unused_imports)]
use crate::runtime::*;
#[allow(unused_imports)]
use crate::generated::*;

verus! {

// ===============================================================================================
// 1. `SameType` (§7.2.8) Equivalence Relation
// ===============================================================================================

pub proof fn lemma_same_type_reflexive(x: SpecJsValue)
    ensures spec_same_type(x, x),
{
}

pub proof fn lemma_same_type_symmetric(x: SpecJsValue, y: SpecJsValue)
    ensures spec_same_type(x, y) == spec_same_type(y, x),
{
}

pub proof fn lemma_same_type_transitive(x: SpecJsValue, y: SpecJsValue, z: SpecJsValue)
    requires spec_same_type(x, y), spec_same_type(y, z),
    ensures spec_same_type(x, z),
{
}

// ===============================================================================================
// 2. `SameValueNonNumber` (§7.2.11), `SameValue` (§7.2.9) & `SameValueZero` (§7.2.10)
// ===============================================================================================

pub proof fn lemma_same_value_non_number_equivalence(x: SpecJsValue, y: SpecJsValue, z: SpecJsValue)
    requires !spec_is_number(x), !spec_is_number(y), !spec_is_number(z),
    ensures
        spec_same_value_non_number(x, x),
        spec_same_type(x, y) ==> (spec_same_value_non_number(x, y) == spec_same_value_non_number(y, x)),
        (spec_same_type(x, y) && spec_same_type(y, z)
            && spec_same_value_non_number(x, y) && spec_same_value_non_number(y, z))
            ==> spec_same_value_non_number(x, z),
{
}

pub proof fn lemma_same_value_reflexive(x: SpecJsValue)
    ensures spec_same_value(x, x),
{
}

pub proof fn lemma_same_value_symmetric(x: SpecJsValue, y: SpecJsValue)
    ensures spec_same_value(x, y) == spec_same_value(y, x),
{
}

pub proof fn lemma_same_value_transitive(x: SpecJsValue, y: SpecJsValue, z: SpecJsValue)
    requires spec_same_value(x, y), spec_same_value(y, z),
    ensures spec_same_value(x, z),
{
}

pub proof fn lemma_same_value_zero_reflexive(x: SpecJsValue)
    ensures spec_same_value_zero(x, x),
{
}

pub proof fn lemma_same_value_zero_symmetric(x: SpecJsValue, y: SpecJsValue)
    ensures spec_same_value_zero(x, y) == spec_same_value_zero(y, x),
{
}

pub proof fn lemma_same_value_zero_transitive(x: SpecJsValue, y: SpecJsValue, z: SpecJsValue)
    requires spec_same_value_zero(x, y), spec_same_value_zero(y, z),
    ensures spec_same_value_zero(x, z),
{
}

/// ECMA-262 §7.2.10 Note: `SameValueZero` coarsens `SameValue`, differing exclusively on
/// `(+0_𝔽, -0_𝔽)` and `(-0_𝔽, +0_𝔽)`.
pub proof fn lemma_same_value_vs_same_value_zero_note(x: SpecJsValue, y: SpecJsValue)
    ensures
        spec_same_value(x, y) ==> spec_same_value_zero(x, y),
        (spec_same_value_zero(x, y) && !spec_same_value(x, y)) <==> (
            (spec_val_is_pos_zero(x) && spec_val_is_neg_zero(y))
                || (spec_val_is_neg_zero(x) && spec_val_is_pos_zero(y))
        ),
{
}

// ===============================================================================================
// 3. `IsStrictlyEqual` (§7.2.14) & `Number::equal` (§6.1.6.1.13)
// ===============================================================================================

/// `IsStrictlyEqual` is reflexive if and only if the value is not `NaN` (irreflexive on all NaNs).
pub proof fn lemma_is_strictly_equal_reflexive_iff_not_nan(x: SpecJsValue)
    ensures spec_is_strictly_equal(x, x) <==> !spec_val_is_nan(x),
{
}

pub proof fn lemma_is_strictly_equal_symmetric(x: SpecJsValue, y: SpecJsValue)
    ensures spec_is_strictly_equal(x, y) == spec_is_strictly_equal(y, x),
{
}

pub proof fn lemma_is_strictly_equal_transitive(x: SpecJsValue, y: SpecJsValue, z: SpecJsValue)
    requires spec_is_strictly_equal(x, y), spec_is_strictly_equal(y, z),
    ensures spec_is_strictly_equal(x, z),
{
}

pub proof fn lemma_is_strictly_equal_agrees_with_same_value_zero_off_nan(x: SpecJsValue, y: SpecJsValue)
    requires !spec_val_is_nan(x), !spec_val_is_nan(y),
    ensures spec_is_strictly_equal(x, y) == spec_same_value_zero(x, y),
{
}

// ===============================================================================================
// 4. `IsLooselyEqual` (§7.2.13) Symmetry & Non-Transitivity
// ===============================================================================================

#[verifier::spinoff_prover]
pub proof fn lemma_is_loosely_equal_symmetric(x: SpecJsValue, y: SpecJsValue)
    ensures spec_is_loosely_equal(x, y) == spec_is_loosely_equal(y, x),
    decreases spec_loosely_equal_rank(x, y) + spec_loosely_equal_rank(y, x),
{
    reveal_with_fuel(spec_is_loosely_equal, 2);
    if spec_same_type(x, y) {
        lemma_same_type_symmetric(x, y);
        lemma_is_strictly_equal_symmetric(x, y);
    } else if (spec_is_null(x) && spec_is_undefined(y)) || (spec_is_undefined(x) && spec_is_null(y)) {
    } else if spec_is_boolean(x) && spec_is_boolean(y) {
        // Covered by same_type above
    } else if spec_is_boolean(x) {
        let nx = match spec_to_number(x) {
            AbruptOrNormal::Normal(n) => SpecJsValue::Number(n),
            AbruptOrNormal::ThrowTypeError => SpecJsValue::Undefined,
        };
        assert(spec_to_number(x) is Normal);
        lemma_is_loosely_equal_symmetric(nx, y);
    } else if spec_is_boolean(y) {
        let ny = match spec_to_number(y) {
            AbruptOrNormal::Normal(n) => SpecJsValue::Number(n),
            AbruptOrNormal::ThrowTypeError => SpecJsValue::Undefined,
        };
        assert(spec_to_number(y) is Normal);
        lemma_is_loosely_equal_symmetric(x, ny);
    } else if spec_is_number(x) && spec_is_string(y) {
        let ny = match spec_to_number(y) {
            AbruptOrNormal::Normal(n) => SpecJsValue::Number(n),
            AbruptOrNormal::ThrowTypeError => SpecJsValue::Undefined,
        };
        assert(spec_to_number(y) is Normal);
        lemma_is_loosely_equal_symmetric(x, ny);
    } else if spec_is_string(x) && spec_is_number(y) {
        let nx = match spec_to_number(x) {
            AbruptOrNormal::Normal(n) => SpecJsValue::Number(n),
            AbruptOrNormal::ThrowTypeError => SpecJsValue::Undefined,
        };
        assert(spec_to_number(x) is Normal);
        lemma_is_loosely_equal_symmetric(nx, y);
    } else if spec_is_bigint(x) && spec_is_string(y) {
        let n = spec_string_to_bigint_val(y);
        if !spec_is_undefined(n) {
            // spec_is_loosely_equal(y, x) steps directly to spec_is_loosely_equal(x, y)
        }
    } else if spec_is_string(x) && spec_is_bigint(y) {
        // Step 8 directly delegates `(String, BigInt)` to `(BigInt, String)`:
        let n = spec_string_to_bigint_val(x);
        if !spec_is_undefined(n) {
            assert(spec_is_bigint(n)) by {
                lemma_string_to_bigint_type(x);
            };
            assert(spec_same_type(y, n));
        }
    } else if (spec_is_string(x) || spec_is_number(x) || spec_is_bigint(x) || spec_is_symbol(x))
        && spec_is_object(y)
    {
        match spec_to_primitive_default(y) {
            AbruptOrNormal::ThrowTypeError => {}
            AbruptOrNormal::Normal(py) => {
                assert(!spec_is_object(py)) by { lemma_to_primitive_default_not_object(y); };
                lemma_is_loosely_equal_symmetric(x, py);
                lemma_loosely_equal_non_objects_normal(x, py);
                lemma_loosely_equal_non_objects_normal(py, x);
            }
        }
    } else if spec_is_object(x)
        && (spec_is_string(y) || spec_is_number(y) || spec_is_bigint(y) || spec_is_symbol(y))
    {
        match spec_to_primitive_default(x) {
            AbruptOrNormal::ThrowTypeError => {}
            AbruptOrNormal::Normal(px) => {
                assert(!spec_is_object(px)) by { lemma_to_primitive_default_not_object(x); };
                lemma_is_loosely_equal_symmetric(px, y);
                lemma_loosely_equal_non_objects_normal(px, y);
                lemma_loosely_equal_non_objects_normal(y, px);
            }
        }
    } else {
        // Remaining cases: HTMLDDA with null/undefined, BigInt vs Number, or incomparable primitives
    }
}

proof fn lemma_string_to_bigint_type(v: SpecJsValue)
    requires spec_is_string(v),
    ensures spec_is_bigint(spec_string_to_bigint_val(v)) || spec_is_undefined(spec_string_to_bigint_val(v)),
{
}

proof fn lemma_to_primitive_default_not_object(v: SpecJsValue)
    ensures
        match spec_to_primitive_default(v) {
            AbruptOrNormal::Normal(p) => !spec_is_object(p),
            AbruptOrNormal::ThrowTypeError => true,
        },
{
    if let SpecJsValue::Object(o) = v {
        if let SpecObjectCoercion::Primitive(p) = o.prim_default {
            assert(!spec_is_object(spec_prim_to_val(p)));
        }
    }
}

proof fn lemma_loosely_equal_non_objects_normal(x: SpecJsValue, y: SpecJsValue)
    requires !spec_is_object(x), !spec_is_object(y),
    ensures spec_is_loosely_equal(x, y) is Normal,
    decreases spec_loosely_equal_rank(x, y),
{
    if !spec_same_type(x, y) {
        if spec_is_boolean(x) {
            let nx = match spec_to_number(x) {
                AbruptOrNormal::Normal(n) => SpecJsValue::Number(n),
                AbruptOrNormal::ThrowTypeError => SpecJsValue::Undefined,
            };
            lemma_loosely_equal_non_objects_normal(nx, y);
        } else if spec_is_boolean(y) {
            let ny = match spec_to_number(y) {
                AbruptOrNormal::Normal(n) => SpecJsValue::Number(n),
                AbruptOrNormal::ThrowTypeError => SpecJsValue::Undefined,
            };
            lemma_loosely_equal_non_objects_normal(x, ny);
        }
    }
}

/// Classic counterexample proving `IsLooselyEqual` (`==`) is NOT transitive:
/// `"" == +0_𝔽` and `+0_𝔽 == "0"` (or `"0" == 0` via `false == 0` and `0 == ""` while `false == ""` —
/// even simpler: `"" == +0_𝔽` and `+0_𝔽 == "-0"`! Wait: `""` (empty) and `"   "` (space) both equal `+0_𝔽`,
/// yet `"" == "   "` is `false`!).
pub proof fn lemma_is_loosely_equal_not_transitive_witness()
    ensures ({
        let empty_s = SpecJsValue::Str(Seq::empty());
        let space_s = SpecJsValue::Str(seq![0x0020u16]);
        let zero_n = SpecJsValue::Number(spec_pos_zero());
        spec_is_loosely_equal(empty_s, zero_n) == AbruptOrNormal::Normal(true)
            && spec_is_loosely_equal(zero_n, space_s) == AbruptOrNormal::Normal(true)
            && spec_is_loosely_equal(empty_s, space_s) == AbruptOrNormal::Normal(false)
    }),
{
    let empty_s = SpecJsValue::Str(Seq::empty());
    let space_s = SpecJsValue::Str(seq![0x0020u16]);
    let zero_n = SpecJsValue::Number(spec_pos_zero());
    reveal_with_fuel(spec_trim_start_idx, 3);
    reveal_with_fuel(spec_trim_end_idx, 3);
    assert(spec_trim_utf16(Seq::empty()) =~= Seq::<u16>::empty());
    assert(spec_trim_utf16(seq![0x0020u16]) =~= Seq::<u16>::empty());
    assert(spec_string_to_number_val(empty_s) == spec_pos_zero());
    assert(spec_string_to_number_val(space_s) == spec_pos_zero());
    reveal_with_fuel(spec_is_loosely_equal, 3);
    assert(empty_s != space_s);
    assert(Seq::<u16>::empty().len() != seq![0x0020u16].len());
}

// ===============================================================================================
// 5. `ToFixedSizeInteger` (§7.1.7), `ToInt32` (§7.1.8), `ToUint32` (§7.1.9) & `ToUint16` (§7.1.11)
// ===============================================================================================

/// ECMA-262 §7.1.7 `<emu-note>` Theorem:
/// `ToFixedSizeInteger` is idempotent AND survives inversion of `_signed_` (`~signed~` <-> `~unsigned~`)
/// for EVERY positive bit-width `1 <= bw <= 32`!
#[verifier::spinoff_prover]
pub proof fn lemma_to_fixed_size_integer_idempotent_and_sign_invariant(
    int_val: MathIntOrInf,
    s1: Signedness,
    s2: Signedness,
    bw: nat,
)
    requires 1 <= bw && bw <= 32,
    ensures ({
        let k1 = spec_to_fixed_size_integer(int_val, s1, bw);
        let k1_as_int_or_inf = MathIntOrInf::Finite(spec_truncate_finite_number(spec_number_from_int(k1)));
        spec_to_fixed_size_integer(k1_as_int_or_inf, s2, bw) == spec_to_fixed_size_integer(int_val, s2, bw)
    }),
{
    lemma_pow2_bitwidth_bounds(bw as u32);
    lemma_pow2_small_values();
    let m: int = spec_pow2(bw) as int;
    let half: int = spec_pow2((bw - 1) as nat) as int;
    let base_mod: int = match int_val {
        MathIntOrInf::PosInf => 0int,
        MathIntOrInf::NegInf => 0int,
        MathIntOrInf::Finite(ex) => {
            vstd::arithmetic::div_mod::lemma_mod_bound(spec_exact_int_val(ex), m);
            spec_exact_int_modulo_pow2(ex, bw)
        }
    };
    assert(0 <= base_mod < m);

    let k1 = spec_to_fixed_size_integer(int_val, s1, bw);
    if int_val == MathIntOrInf::PosInf || int_val == MathIntOrInf::NegInf {
        assert(k1 == 0);
        vstd::arithmetic::div_mod::lemma_small_mod(0nat, m as nat);
    } else if s1 == Signedness::Signed && base_mod >= half {
        assert(k1 == base_mod - m);
        assert(base_mod - m == (-1int) * m + base_mod) by (nonlinear_arith);
        vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(-1int, base_mod, m);
        vstd::arithmetic::div_mod::lemma_small_mod(base_mod as nat, m as nat);
        assert(k1 % m == base_mod);
    } else {
        assert(k1 == base_mod);
        vstd::arithmetic::div_mod::lemma_small_mod(base_mod as nat, m as nat);
        assert(k1 % m == base_mod);
    }

    assert(-2147483648int <= k1 && k1 < 4294967296int);
    lemma_number_from_int_roundtrip(k1);
    let ex1 = spec_truncate_finite_number(spec_number_from_int(k1));
    assert(spec_exact_int_val(ex1) == k1);
    assert(spec_exact_int_modulo_pow2(ex1, bw) == k1 % m);
    assert(spec_exact_int_modulo_pow2(ex1, bw) == base_mod);

    if int_val == MathIntOrInf::PosInf || int_val == MathIntOrInf::NegInf {
        assert(base_mod == 0);
        assert(0 < half);
    }
}

/// `ToInt32` is idempotent and never produces `*-0*_𝔽`, and `ToUint32(ToInt32(x)) == ToUint32(x)`.
pub proof fn lemma_to_int32_idempotent_and_cross_invariant(x: SpecJsValue)
    ensures
        match spec_to_int32(x) {
            AbruptOrNormal::ThrowTypeError => true,
            AbruptOrNormal::Normal(n) =>
                !spec_is_neg_zero(n)
                    && spec_to_int32(SpecJsValue::Number(n)) == AbruptOrNormal::Normal(n)
                    && spec_to_uint32(SpecJsValue::Number(n)) == spec_to_uint32(x),
        },
{
    if let AbruptOrNormal::Normal(iv) = spec_to_integer_or_infinity(x) {
        lemma_pow2_bitwidth_bounds(32);
        lemma_pow2_small_values();
        if let MathIntOrInf::Finite(ex) = iv {
            vstd::arithmetic::div_mod::lemma_mod_bound(spec_exact_int_val(ex), 4294967296int);
        }
        let k = spec_to_fixed_size_integer(iv, Signedness::Signed, 32);
        lemma_number_from_int_roundtrip(k);
        let n = spec_number_from_int(k);
        lemma_to_fixed_size_integer_idempotent_and_sign_invariant(iv, Signedness::Signed, Signedness::Signed, 32);
        lemma_to_fixed_size_integer_idempotent_and_sign_invariant(iv, Signedness::Signed, Signedness::Unsigned, 32);
        if k == 0 {
            assert(spec_is_pos_zero(n));
            vstd::arithmetic::div_mod::lemma_small_mod(0nat, 4294967296nat);
        } else {
            assert(!spec_is_pos_zero(n) && !spec_is_neg_zero(n) && !spec_is_nan(n));
            assert(!spec_is_pos_inf(n) && !spec_is_neg_inf(n)) by {
                assert(spec_is_finite_num(n));
                assert(spec_raw_exp(spec_pos_inf()) == 0x7FFu64);
                assert(spec_raw_exp(spec_neg_inf()) == 0x7FFu64);
            };
        }
    }
}

/// `ToUint32` is idempotent and never produces `*-0*_𝔽`, and `ToInt32(ToUint32(x)) == ToInt32(x)`.
pub proof fn lemma_to_uint32_idempotent_and_cross_invariant(x: SpecJsValue)
    ensures
        match spec_to_uint32(x) {
            AbruptOrNormal::ThrowTypeError => true,
            AbruptOrNormal::Normal(n) =>
                !spec_is_neg_zero(n)
                    && spec_to_uint32(SpecJsValue::Number(n)) == AbruptOrNormal::Normal(n)
                    && spec_to_int32(SpecJsValue::Number(n)) == spec_to_int32(x),
        },
{
    if let AbruptOrNormal::Normal(iv) = spec_to_integer_or_infinity(x) {
        lemma_pow2_bitwidth_bounds(32);
        lemma_pow2_small_values();
        if let MathIntOrInf::Finite(ex) = iv {
            vstd::arithmetic::div_mod::lemma_mod_bound(spec_exact_int_val(ex), 4294967296int);
        }
        let k = spec_to_fixed_size_integer(iv, Signedness::Unsigned, 32);
        lemma_number_from_int_roundtrip(k);
        let n = spec_number_from_int(k);
        lemma_to_fixed_size_integer_idempotent_and_sign_invariant(iv, Signedness::Unsigned, Signedness::Unsigned, 32);
        lemma_to_fixed_size_integer_idempotent_and_sign_invariant(iv, Signedness::Unsigned, Signedness::Signed, 32);
        if k == 0 {
            assert(spec_is_pos_zero(n));
            vstd::arithmetic::div_mod::lemma_small_mod(0nat, 4294967296nat);
        } else {
            assert(!spec_is_pos_zero(n) && !spec_is_neg_zero(n) && !spec_is_nan(n));
            assert(!spec_is_pos_inf(n) && !spec_is_neg_inf(n)) by {
                assert(spec_is_finite_num(n));
                assert(spec_raw_exp(spec_pos_inf()) == 0x7FFu64);
                assert(spec_raw_exp(spec_neg_inf()) == 0x7FFu64);
            };
        }
    }
}

/// `ToUint16` is idempotent and never produces `*-0*_𝔽`.
pub proof fn lemma_to_uint16_idempotent(x: SpecJsValue)
    ensures
        match spec_to_uint16(x) {
            AbruptOrNormal::ThrowTypeError => true,
            AbruptOrNormal::Normal(n) =>
                !spec_is_neg_zero(n)
                    && spec_to_uint16(SpecJsValue::Number(n)) == AbruptOrNormal::Normal(n),
        },
{
    if let AbruptOrNormal::Normal(iv) = spec_to_integer_or_infinity(x) {
        lemma_pow2_bitwidth_bounds(16);
        lemma_pow2_small_values();
        if let MathIntOrInf::Finite(ex) = iv {
            vstd::arithmetic::div_mod::lemma_mod_bound(spec_exact_int_val(ex), 65536int);
        }
        let k = spec_to_fixed_size_integer(iv, Signedness::Unsigned, 16);
        lemma_number_from_int_roundtrip(k);
        let n = spec_number_from_int(k);
        lemma_to_fixed_size_integer_idempotent_and_sign_invariant(iv, Signedness::Unsigned, Signedness::Unsigned, 16);
        if k == 0 {
            assert(spec_is_pos_zero(n));
            vstd::arithmetic::div_mod::lemma_small_mod(0nat, 65536nat);
        } else {
            assert(!spec_is_pos_zero(n) && !spec_is_neg_zero(n) && !spec_is_nan(n));
            assert(!spec_is_pos_inf(n) && !spec_is_neg_inf(n)) by {
                assert(spec_is_finite_num(n));
                assert(spec_raw_exp(spec_pos_inf()) == 0x7FFu64);
                assert(spec_raw_exp(spec_neg_inf()) == 0x7FFu64);
            };
        }
    }
}

// ===============================================================================================
// 6. Bitwise, `ToBoolean` & `RequireObjectCoercible` Algebraic Laws
// ===============================================================================================

proof fn lemma_u32_bits_i32_roundtrip(b: u32)
    ensures spec_i32_to_u32_bits(spec_u32_bits_to_i32_int(b)) == b,
{
    if b >= 0x8000_0000u32 {
        let v = (b as int) - 4294967296int;
        assert(v == (-1int) * 4294967296int + (b as int));
        vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(-1int, b as int, 4294967296int);
        vstd::arithmetic::div_mod::lemma_small_mod(b as nat, 4294967296nat);
    } else {
        vstd::arithmetic::div_mod::lemma_small_mod(b as nat, 4294967296nat);
    }
}

proof fn lemma_i32_int_u32_roundtrip(v: int)
    requires -2147483648int <= v && v <= 2147483647int,
    ensures spec_u32_bits_to_i32_int(spec_i32_to_u32_bits(v)) == v,
{
    if v >= 0 {
        vstd::arithmetic::div_mod::lemma_small_mod(v as nat, 4294967296nat);
    } else {
        let u = (v + 4294967296int) as nat;
        assert(v == (-1int) * 4294967296int + (u as int));
        vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(-1int, u as int, 4294967296int);
        vstd::arithmetic::div_mod::lemma_small_mod(u, 4294967296nat);
    }
}

/// `~~x == !ToInt32(x)` for ALL IEEE-754 binary64 `JsNumber`s `x` (`NaN`, `±0`, `±∞`, finite).
pub proof fn lemma_number_bitwise_not_involution(x: JsNumber)
    ensures
        spec_number_bitwise_not(spec_number_bitwise_not(x)) == (match spec_to_int32(SpecJsValue::Number(x)) {
            AbruptOrNormal::Normal(n) => n,
            AbruptOrNormal::ThrowTypeError => spec_pos_zero(),
        }),
{
    lemma_pow2_bitwidth_bounds(32);
    lemma_pow2_small_values();
    let xv = SpecJsValue::Number(x);
    assert(spec_to_int32(xv) is Normal);
    if let AbruptOrNormal::Normal(iv) = spec_to_integer_or_infinity(xv) {
        if let MathIntOrInf::Finite(ex) = iv {
            vstd::arithmetic::div_mod::lemma_mod_bound(spec_exact_int_val(ex), 4294967296int);
        }
        let k = spec_to_fixed_size_integer(iv, Signedness::Signed, 32);
        lemma_number_from_int_roundtrip(k);
        let old_val = spec_number_from_int(k);
        assert(spec_integral_number_to_i64(old_val) == k);
        let b0 = spec_i32_to_u32_bits(k);
        let b1 = spec_bitnot_u32(b0);
        let k1 = spec_u32_bits_to_i32_int(b1);
        lemma_number_from_int_roundtrip(k1);
        let n1 = spec_number_from_int(k1);
        lemma_to_int32_idempotent_and_cross_invariant(xv);
        // Show `spec_to_int32(Number(n1)) == Normal(n1)` because `n1 = 𝔽(k1)` with `-2^31 <= k1 < 2^31`!
        if k1 == 0 {
            vstd::arithmetic::div_mod::lemma_small_mod(0nat, 4294967296nat);
        } else {
            assert(!spec_is_pos_zero(n1) && !spec_is_neg_zero(n1) && !spec_is_nan(n1));
            assert(!spec_is_pos_inf(n1) && !spec_is_neg_inf(n1)) by {
                assert(spec_is_finite_num(n1));
                assert(spec_raw_exp(spec_pos_inf()) == 0x7FFu64);
                assert(spec_raw_exp(spec_neg_inf()) == 0x7FFu64);
            };
            if k1 >= 0 {
                vstd::arithmetic::div_mod::lemma_small_mod(k1 as nat, 4294967296nat);
            } else {
                let u1 = (k1 + 4294967296int) as nat;
                assert(k1 == (-1int) * 4294967296int + (u1 as int));
                vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(-1int, u1 as int, 4294967296int);
                vstd::arithmetic::div_mod::lemma_small_mod(u1, 4294967296nat);
            }
        }
        assert(spec_to_int32(SpecJsValue::Number(n1)) == AbruptOrNormal::Normal(n1));
        assert(spec_integral_number_to_i64(n1) == k1);
        lemma_u32_bits_i32_roundtrip(b1);
        assert(!(!b0) == b0) by (bit_vector);
        assert(spec_bitnot_u32(b1) == b0);
        lemma_i32_int_u32_roundtrip(k);
    }
}

pub proof fn lemma_number_bitwise_op_commutative(op: BitwiseOp, x: JsNumber, y: JsNumber)
    ensures spec_number_bitwise_op(op, x, y) == spec_number_bitwise_op(op, y, x),
{
    let lx = match spec_to_int32(SpecJsValue::Number(x)) {
        AbruptOrNormal::Normal(n) => spec_i32_to_u32_bits(spec_integral_number_to_i64(n)),
        AbruptOrNormal::ThrowTypeError => spec_i32_to_u32_bits(spec_integral_number_to_i64(spec_pos_zero())),
    };
    let ly = match spec_to_int32(SpecJsValue::Number(y)) {
        AbruptOrNormal::Normal(n) => spec_i32_to_u32_bits(spec_integral_number_to_i64(n)),
        AbruptOrNormal::ThrowTypeError => spec_i32_to_u32_bits(spec_integral_number_to_i64(spec_pos_zero())),
    };
    assert((lx & ly) == (ly & lx)) by (bit_vector);
    assert((lx ^ ly) == (ly ^ lx)) by (bit_vector);
    assert((lx | ly) == (ly | lx)) by (bit_vector);
}

pub proof fn lemma_number_bitwise_xor_self_zero(x: JsNumber)
    ensures spec_number_bitwise_xor(x, x) == spec_pos_zero(),
{
    let lx = match spec_to_int32(SpecJsValue::Number(x)) {
        AbruptOrNormal::Normal(n) => spec_i32_to_u32_bits(spec_integral_number_to_i64(n)),
        AbruptOrNormal::ThrowTypeError => spec_i32_to_u32_bits(spec_integral_number_to_i64(spec_pos_zero())),
    };
    assert((lx ^ lx) == 0u32) by (bit_vector);
    assert(spec_u32_bits_to_i32_int(0u32) == 0int);
    assert(spec_number_from_int(0int) == spec_pos_zero());
}

/// De Morgan's Law over full IEEE-754 `JsNumber`: `~(x & y) == (~x) | (~y)`.
#[verifier::spinoff_prover]
pub proof fn lemma_number_bitwise_demorgan(x: JsNumber, y: JsNumber)
    ensures
        spec_number_bitwise_not(spec_number_bitwise_and(x, y))
            == spec_number_bitwise_or(spec_number_bitwise_not(x), spec_number_bitwise_not(y)),
{
    lemma_pow2_bitwidth_bounds(32);
    lemma_pow2_small_values();
    let nx = match spec_to_int32(SpecJsValue::Number(x)) {
        AbruptOrNormal::Normal(n) => n,
        AbruptOrNormal::ThrowTypeError => spec_pos_zero(),
    };
    let ny = match spec_to_int32(SpecJsValue::Number(y)) {
        AbruptOrNormal::Normal(n) => n,
        AbruptOrNormal::ThrowTypeError => spec_pos_zero(),
    };
    let bx = spec_i32_to_u32_bits(spec_integral_number_to_i64(nx));
    let by_ = spec_i32_to_u32_bits(spec_integral_number_to_i64(ny));

    // Helper: for any `b: u32`, `ToInt32(Number(𝔽(u32_bits_to_i32_int(b))))` roundtrips to `b`!
    lemma_int32_bits_number_roundtrip(bx & by_);
    lemma_int32_bits_number_roundtrip(!bx);
    lemma_int32_bits_number_roundtrip(!by_);
    assert(!(bx & by_) == ((!bx) | (!by_))) by (bit_vector);
}

proof fn lemma_int32_bits_number_roundtrip(b: u32)
    ensures ({
        let k = spec_u32_bits_to_i32_int(b);
        let num = spec_number_from_int(k);
        spec_to_int32(SpecJsValue::Number(num)) == AbruptOrNormal::Normal(num)
            && spec_i32_to_u32_bits(spec_integral_number_to_i64(num)) == b
    }),
{
    lemma_pow2_bitwidth_bounds(32);
    lemma_pow2_small_values();
    let k = spec_u32_bits_to_i32_int(b);
    lemma_number_from_int_roundtrip(k);
    let num = spec_number_from_int(k);
    if k == 0 {
        vstd::arithmetic::div_mod::lemma_small_mod(0nat, 4294967296nat);
    } else {
        assert(!spec_is_pos_zero(num) && !spec_is_neg_zero(num) && !spec_is_nan(num));
        assert(!spec_is_pos_inf(num) && !spec_is_neg_inf(num)) by {
            assert(spec_is_finite_num(num));
            assert(spec_raw_exp(spec_pos_inf()) == 0x7FFu64);
            assert(spec_raw_exp(spec_neg_inf()) == 0x7FFu64);
        };
        if k >= 0 {
            vstd::arithmetic::div_mod::lemma_small_mod(k as nat, 4294967296nat);
        } else {
            let u1 = (k + 4294967296int) as nat;
            assert(k == (-1int) * 4294967296int + (u1 as int));
            vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(-1int, u1 as int, 4294967296int);
            vstd::arithmetic::div_mod::lemma_small_mod(u1, 4294967296nat);
        }
    }
    lemma_u32_bits_i32_roundtrip(b);
}

pub proof fn lemma_to_boolean_idempotent(x: SpecJsValue)
    ensures spec_to_boolean(SpecJsValue::Boolean(spec_to_boolean(x))) == spec_to_boolean(x),
{
}

pub proof fn lemma_require_object_coercible_iff_not_nullish(x: SpecJsValue)
    ensures (spec_require_object_coercible(x) is ThrowTypeError) <==> (spec_is_undefined(x) || spec_is_null(x)),
{
}

} // verus!
