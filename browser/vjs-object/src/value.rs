//! ECMAScript value, identifier, property-key canonicalization, SameValue (§7.2.10),
//! SameValueZero (§7.2.11), and exact IEEE-754 binary64 <-> `u32` array-length bit conversions.
use vstd::prelude::*;

verus! {

/// Arena object identifier (`ECMA-262 §6.1.7`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct ObjId(pub usize);

/// Explicit ECMAScript / `vjs` error and unsupported-feature completion tags.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum UnsupportedFeature {
    /// `ToNumber` / `ToUint32` on an Object value requires invoking `ToPrimitive` (`valueOf`/`toString`)
    /// through the J4 interpreter call stack.
    ObjectToPrimitiveCoercion,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum JsError {
    TypeError,
    RangeError,
    Unsupported(UnsupportedFeature),
}

// ---------------------------------------------------------------------------------------
// Helper sequence / vector utilities (verified without any external_body)
// ---------------------------------------------------------------------------------------

pub fn clone_vec_u16(v: &Vec<u16>) -> (out: Vec<u16>)
    ensures
        out@ == v@,
{
    let n = v.len();
    let mut out: Vec<u16> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == v@.len(),
            out@ == v@.subrange(0, i as int),
        decreases n - i,
    {
        out.push(v[i]);
        proof {
            assert(v@.subrange(0, (i + 1) as int) =~= v@.subrange(0, i as int).push(v@[i as int]));
        }
        i += 1;
    }
    proof {
        assert(v@.subrange(0, n as int) =~= v@);
    }
    out
}

pub fn clone_vec_u32(v: &Vec<u32>) -> (out: Vec<u32>)
    ensures
        out@ == v@,
{
    let n = v.len();
    let mut out: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == v@.len(),
            out@ == v@.subrange(0, i as int),
        decreases n - i,
    {
        out.push(v[i]);
        proof {
            assert(v@.subrange(0, (i + 1) as int) =~= v@.subrange(0, i as int).push(v@[i as int]));
        }
        i += 1;
    }
    proof {
        assert(v@.subrange(0, n as int) =~= v@);
    }
    out
}

pub fn eq_vec_u16(a: &Vec<u16>, b: &Vec<u16>) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let n = a.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == a@.len(),
            n == b@.len(),
            forall|k: int| 0 <= k < i as int ==> a@[k] == b@[k],
        decreases n - i,
    {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    proof {
        assert(a@ =~= b@);
    }
    true
}

pub fn eq_vec_u32(a: &Vec<u32>, b: &Vec<u32>) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let n = a.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == a@.len(),
            n == b@.len(),
            forall|k: int| 0 <= k < i as int ==> a@[k] == b@[k],
        decreases n - i,
    {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    proof {
        assert(a@ =~= b@);
    }
    true
}

// ---------------------------------------------------------------------------------------
// Property Keys (§6.1.7): Canonical Array Index vs UTF-16 String vs Symbol
// ---------------------------------------------------------------------------------------

/// Mathematical ghost view of `PropKey`, using `Seq<u16>` so Z3 `==` is structural equality.
pub enum PropKeyView {
    ArrayIndex(u32),
    Str(Seq<u16>),
    Symbol(u64),
}

/// ECMAScript property key (`§6.1.7`):
/// - `ArrayIndex(u32)` for canonical array index strings `"0"` .. `"4294967294"` (`idx < u32::MAX`);
/// - `Str(Vec<u16>)` for all other UTF-16 string keys (incl. `"length"`, `"01"`, `"-0"`, `"4294967295"`);
/// - `Symbol(u64)` for unique Symbol keys.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum PropKey {
    ArrayIndex(u32),
    Str(Vec<u16>),
    Symbol(u64),
}

impl View for PropKey {
    type V = PropKeyView;

    open spec fn view(&self) -> PropKeyView {
        match self {
            PropKey::ArrayIndex(idx) => PropKeyView::ArrayIndex(*idx),
            PropKey::Str(s) => PropKeyView::Str(s@),
            PropKey::Symbol(id) => PropKeyView::Symbol(*id),
        }
    }
}

pub open spec fn spec_is_ascii_digit_u16(c: u16) -> bool {
    0x0030u16 <= c && c <= 0x0039u16
}

pub open spec fn spec_pow10(k: nat) -> nat
    decreases k,
{
    if k == 0 {
        1
    } else {
        spec_pow10((k - 1) as nat) * 10
    }
}

proof fn lemma_pow10_le_9(k: nat)
    requires
        k <= 9,
    ensures
        spec_pow10(k) <= 1_000_000_000,
{
    reveal_with_fuel(spec_pow10, 10);
}

/// Decimal value of UTF-16 digits `s`, or `None` if any code unit is not `'0'..'9'`.
pub open spec fn spec_decimal_digits_value(s: Seq<u16>) -> Option<nat>
    decreases s.len(),
{
    if s.len() == 0 {
        Some(0)
    } else {
        match spec_decimal_digits_value(s.drop_last()) {
            None => None,
            Some(acc) =>
                if spec_is_ascii_digit_u16(s.last()) {
                    Some(acc * 10 + (s.last() - 0x0030u16) as nat)
                } else {
                    None
                },
        }
    }
}

proof fn lemma_digits_none_propagates(s: Seq<u16>, k: int)
    requires
        0 <= k <= s.len(),
        spec_decimal_digits_value(s.subrange(0, k)) is None,
    ensures
        spec_decimal_digits_value(s) is None,
    decreases s.len() - k,
{
    if k == s.len() {
        assert(s.subrange(0, k) =~= s);
    } else {
        let next = s.subrange(0, k + 1);
        assert(next.drop_last() =~= s.subrange(0, k));
        lemma_digits_none_propagates(s, k + 1);
    }
}

/// ECMA-262 §6.1.7 array index parser:
/// A String key is an array index iff it is a canonical base-10 integer in `[0, 2^32 - 1)`,
/// i.e. `"0"` or non-zero-leading digits with value `< 4_294_967_295` (`u32::MAX`).
pub open spec fn spec_parse_array_index_utf16(s: Seq<u16>) -> Option<u32> {
    if s.len() == 0 || s.len() > 10 {
        None
    } else if s.len() == 1 {
        if spec_is_ascii_digit_u16(s[0]) {
            Some((s[0] - 0x0030u16) as u32)
        } else {
            None
        }
    } else if s[0] == 0x0030u16 {
        None
    } else {
        match spec_decimal_digits_value(s) {
            Some(v) =>
                if v < (u32::MAX as nat) {
                    Some(v as u32)
                } else {
                    None
                },
            None => None,
        }
    }
}

pub open spec fn prop_key_wf(k: PropKeyView) -> bool {
    match k {
        PropKeyView::ArrayIndex(idx) => idx < u32::MAX,
        PropKeyView::Str(s) => spec_parse_array_index_utf16(s) is None,
        PropKeyView::Symbol(_) => true,
    }
}

pub open spec fn spec_prop_key_from_utf16(s: Seq<u16>) -> PropKeyView {
    match spec_parse_array_index_utf16(s) {
        Some(idx) => PropKeyView::ArrayIndex(idx),
        None => PropKeyView::Str(s),
    }
}

pub open spec fn spec_length_utf16() -> Seq<u16> {
    seq![0x006Cu16, 0x0065u16, 0x006Eu16, 0x0067u16, 0x0074u16, 0x0068u16]
}

pub open spec fn spec_length_key() -> PropKeyView {
    PropKeyView::Str(spec_length_utf16())
}

pub proof fn lemma_length_key_wf()
    ensures
        prop_key_wf(spec_length_key()),
{
    let s = spec_length_utf16();
    assert(s.len() == 6);
    assert(!spec_is_ascii_digit_u16(s.last()));
    reveal_with_fuel(spec_decimal_digits_value, 2);
}

pub fn parse_array_index_utf16(s: &Vec<u16>) -> (res: Option<u32>)
    ensures
        res == spec_parse_array_index_utf16(s@),
        res is Some ==> res.unwrap() < u32::MAX,
{
    let n = s.len();
    if n == 0 || n > 10 {
        return None;
    }
    if n == 1 {
        let c = s[0];
        if c >= 0x0030 && c <= 0x0039 {
            return Some((c - 0x0030) as u32);
        } else {
            return None;
        }
    }
    if s[0] == 0x0030 {
        return None;
    }
    let mut acc: u64 = 0;
    let mut i: usize = 0;
    proof {
        assert(s@.subrange(0, 0) =~= Seq::<u16>::empty());
    }
    while i < n
        invariant
            i <= n,
            n == s@.len(),
            n <= 10,
            (acc as nat) < spec_pow10(i as nat),
            spec_decimal_digits_value(s@.subrange(0, i as int)) == Some(acc as nat),
        decreases n - i,
    {
        let c = s[i];
        let ghost prev = s@.subrange(0, i as int);
        let ghost next_sub = s@.subrange(0, (i + 1) as int);
        proof {
            assert(next_sub.drop_last() =~= prev);
            assert(next_sub.last() == c);
        }
        if !(c >= 0x0030 && c <= 0x0039) {
            proof {
                lemma_digits_none_propagates(s@, (i + 1) as int);
            }
            return None;
        }
        let d = (c - 0x0030) as u64;
        proof {
            lemma_pow10_le_9(i as nat);
            assert(acc <= 999_999_999u64);
        }
        acc = acc * 10 + d;
        i += 1;
    }
    proof {
        assert(s@.subrange(0, n as int) =~= s@);
    }
    if acc < (u32::MAX as u64) {
        Some(acc as u32)
    } else {
        None
    }
}

pub fn prop_key_from_utf16(s: Vec<u16>) -> (k: PropKey)
    ensures
        k@ == spec_prop_key_from_utf16(s@),
        prop_key_wf(k@),
{
    match parse_array_index_utf16(&s) {
        Some(idx) => PropKey::ArrayIndex(idx),
        None => PropKey::Str(s),
    }
}

pub open spec fn spec_ascii_to_utf16(bytes: Seq<u8>) -> Seq<u16>
    decreases bytes.len(),
{
    if bytes.len() == 0 {
        seq![]
    } else {
        spec_ascii_to_utf16(bytes.drop_last()).push(bytes.last() as u16)
    }
}

pub fn prop_key_from_ascii(bytes: &[u8]) -> (k: PropKey)
    ensures
        k@ == spec_prop_key_from_utf16(spec_ascii_to_utf16(bytes@)),
        prop_key_wf(k@),
{
    let n = bytes.len();
    let mut s: Vec<u16> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(bytes@.subrange(0, 0) =~= Seq::<u8>::empty());
    }
    while i < n
        invariant
            i <= n,
            n == bytes@.len(),
            s@ == spec_ascii_to_utf16(bytes@.subrange(0, i as int)),
        decreases n - i,
    {
        s.push(bytes[i] as u16);
        proof {
            let sub_next = bytes@.subrange(0, (i + 1) as int);
            assert(sub_next.drop_last() =~= bytes@.subrange(0, i as int));
            assert(sub_next.last() == bytes@[i as int]);
        }
        i += 1;
    }
    proof {
        assert(bytes@.subrange(0, n as int) =~= bytes@);
    }
    prop_key_from_utf16(s)
}

pub fn length_prop_key() -> (k: PropKey)
    ensures
        k@ == spec_length_key(),
        prop_key_wf(k@),
{
    let mut s: Vec<u16> = Vec::new();
    s.push(0x006Cu16);
    s.push(0x0065u16);
    s.push(0x006Eu16);
    s.push(0x0067u16);
    s.push(0x0074u16);
    s.push(0x0068u16);
    proof {
        assert(s@ =~= spec_length_utf16());
        lemma_length_key_wf();
    }
    PropKey::Str(s)
}

pub fn is_length_key(k: &PropKey) -> (r: bool)
    ensures
        r == (k@ == spec_length_key()),
{
    match k {
        PropKey::Str(s) => {
            if s.len() != 6 {
                false
            } else {
                let ok = s[0] == 0x006Cu16
                    && s[1] == 0x0065u16
                    && s[2] == 0x006Eu16
                    && s[3] == 0x0067u16
                    && s[4] == 0x0074u16
                    && s[5] == 0x0068u16;
                proof {
                    if ok {
                        assert(s@ =~= spec_length_utf16());
                    }
                }
                ok
            }
        },
        _ => false,
    }
}

pub fn check_prop_key_wf(k: &PropKey) -> (r: bool)
    ensures
        r == prop_key_wf(k@),
{
    match k {
        PropKey::ArrayIndex(idx) => *idx < u32::MAX,
        PropKey::Str(s) => parse_array_index_utf16(s).is_none(),
        PropKey::Symbol(_) => true,
    }
}

pub fn prop_key_eq(a: &PropKey, b: &PropKey) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    match (a, b) {
        (PropKey::ArrayIndex(x), PropKey::ArrayIndex(y)) => *x == *y,
        (PropKey::Str(x), PropKey::Str(y)) => eq_vec_u16(x, y),
        (PropKey::Symbol(x), PropKey::Symbol(y)) => *x == *y,
        _ => false,
    }
}

pub fn clone_prop_key(k: &PropKey) -> (out: PropKey)
    ensures
        out@ == k@,
{
    match k {
        PropKey::ArrayIndex(idx) => PropKey::ArrayIndex(*idx),
        PropKey::Str(s) => PropKey::Str(clone_vec_u16(s)),
        PropKey::Symbol(id) => PropKey::Symbol(*id),
    }
}

// ---------------------------------------------------------------------------------------
// ECMAScript Values (`JsVal`, §6.1) and SameValue / SameValueZero (§7.2.10–§7.2.11)
// ---------------------------------------------------------------------------------------

pub struct JsBigIntView {
    pub neg: bool,
    pub limbs: Seq<u32>,
}

/// Arbitrary-precision ECMAScript BigInt value (`§6.1.6.2`).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct JsBigInt {
    pub neg: bool,
    pub limbs: Vec<u32>,
}

impl View for JsBigInt {
    type V = JsBigIntView;

    open spec fn view(&self) -> JsBigIntView {
        JsBigIntView { neg: self.neg, limbs: self.limbs@ }
    }
}

pub enum JsValView {
    Undefined,
    Null,
    Bool(bool),
    NumberBits(u64),
    BigInt(JsBigIntView),
    Str(Seq<u16>),
    Symbol(u64),
    Object(ObjId),
}

/// ECMAScript language value (`§6.1`), storing IEEE-754 binary64 numbers at the exact bit level.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum JsVal {
    Undefined,
    Null,
    Bool(bool),
    NumberBits(u64),
    BigInt(JsBigInt),
    Str(Vec<u16>),
    Symbol(u64),
    Object(ObjId),
}

impl View for JsVal {
    type V = JsValView;

    open spec fn view(&self) -> JsValView {
        match self {
            JsVal::Undefined => JsValView::Undefined,
            JsVal::Null => JsValView::Null,
            JsVal::Bool(b) => JsValView::Bool(*b),
            JsVal::NumberBits(bits) => JsValView::NumberBits(*bits),
            JsVal::BigInt(bi) => JsValView::BigInt(bi@),
            JsVal::Str(s) => JsValView::Str(s@),
            JsVal::Symbol(id) => JsValView::Symbol(*id),
            JsVal::Object(oid) => JsValView::Object(*oid),
        }
    }
}

pub fn clone_js_val(v: &JsVal) -> (out: JsVal)
    ensures
        out@ == v@,
{
    match v {
        JsVal::Undefined => JsVal::Undefined,
        JsVal::Null => JsVal::Null,
        JsVal::Bool(b) => JsVal::Bool(*b),
        JsVal::NumberBits(bits) => JsVal::NumberBits(*bits),
        JsVal::BigInt(bi) => JsVal::BigInt(JsBigInt { neg: bi.neg, limbs: clone_vec_u32(&bi.limbs) }),
        JsVal::Str(s) => JsVal::Str(clone_vec_u16(s)),
        JsVal::Symbol(id) => JsVal::Symbol(*id),
        JsVal::Object(oid) => JsVal::Object(*oid),
    }
}

pub const POS_ZERO_BITS: u64 = 0x0000_0000_0000_0000u64;
pub const NEG_ZERO_BITS: u64 = 0x8000_0000_0000_0000u64;
pub const CANONICAL_NAN_BITS: u64 = 0x7ff8_0000_0000_0000u64;

pub open spec fn spec_is_nan_bits(bits: u64) -> bool {
    ((bits >> 52u64) & 0x7ffu64) == 0x7ffu64 && (bits & 0x000f_ffff_ffff_ffffu64) != 0u64
}

pub open spec fn spec_is_zero_bits(bits: u64) -> bool {
    bits == 0x0000_0000_0000_0000u64 || bits == 0x8000_0000_0000_0000u64
}

pub fn is_nan_bits(bits: u64) -> (r: bool)
    ensures
        r == spec_is_nan_bits(bits),
{
    ((bits >> 52) & 0x7ff) == 0x7ff && (bits & 0x000f_ffff_ffff_ffff) != 0
}

pub fn is_zero_bits(bits: u64) -> (r: bool)
    ensures
        r == spec_is_zero_bits(bits),
{
    bits == POS_ZERO_BITS || bits == NEG_ZERO_BITS
}

/// Strip trailing zero limbs from a BigInt limb sequence so BigInt value equality is canonical
/// over arbitrary `JsBigIntView` representations.
pub open spec fn spec_strip_trailing_zero_limbs(limbs: Seq<u32>) -> Seq<u32>
    decreases limbs.len(),
{
    if limbs.len() == 0 {
        seq![]
    } else if limbs.last() == 0u32 {
        spec_strip_trailing_zero_limbs(limbs.drop_last())
    } else {
        limbs
    }
}

pub open spec fn spec_bigint_same_value(a: JsBigIntView, b: JsBigIntView) -> bool {
    let la = spec_strip_trailing_zero_limbs(a.limbs);
    let lb = spec_strip_trailing_zero_limbs(b.limbs);
    if la.len() == 0 && lb.len() == 0 {
        true
    } else {
        a.neg == b.neg && la == lb
    }
}

fn effective_bigint_len(limbs: &Vec<u32>) -> (k: usize)
    ensures
        k <= limbs@.len(),
        limbs@.subrange(0, k as int) == spec_strip_trailing_zero_limbs(limbs@),
{
    let mut k: usize = limbs.len();
    proof {
        assert(limbs@.subrange(0, k as int) =~= limbs@);
    }
    while k > 0 && limbs[k - 1] == 0
        invariant
            k <= limbs@.len(),
            spec_strip_trailing_zero_limbs(limbs@) == spec_strip_trailing_zero_limbs(
                limbs@.subrange(0, k as int),
            ),
        decreases k,
    {
        let ghost cur = limbs@.subrange(0, k as int);
        let ghost prev = limbs@.subrange(0, (k - 1) as int);
        proof {
            assert(cur.drop_last() =~= prev);
            assert(cur.last() == 0u32);
        }
        k -= 1;
    }
    k
}

pub fn bigint_same_value(a: &JsBigInt, b: &JsBigInt) -> (r: bool)
    ensures
        r == spec_bigint_same_value(a@, b@),
{
    let ka = effective_bigint_len(&a.limbs);
    let kb = effective_bigint_len(&b.limbs);
    if ka == 0 && kb == 0 {
        return true;
    }
    if ka != kb || a.neg != b.neg {
        return false;
    }
    let mut i: usize = 0;
    while i < ka
        invariant
            i <= ka,
            ka == kb,
            ka <= a.limbs@.len(),
            kb <= b.limbs@.len(),
            a.limbs@.subrange(0, ka as int) == spec_strip_trailing_zero_limbs(a.limbs@),
            b.limbs@.subrange(0, kb as int) == spec_strip_trailing_zero_limbs(b.limbs@),
            forall|j: int| 0 <= j < i as int ==> a.limbs@[j] == b.limbs@[j],
        decreases ka - i,
    {
        if a.limbs[i] != b.limbs[i] {
            proof {
                let la = spec_strip_trailing_zero_limbs(a.limbs@);
                let lb = spec_strip_trailing_zero_limbs(b.limbs@);
                assert(la[i as int] == a.limbs@[i as int]);
                assert(lb[i as int] == b.limbs@[i as int]);
            }
            return false;
        }
        i += 1;
    }
    proof {
        assert(a.limbs@.subrange(0, ka as int) =~= b.limbs@.subrange(0, kb as int));
    }
    true
}

/// ECMA-262 §7.2.10 `SameValue(x, y)`:
/// Distinguishes `+0.0` from `-0.0`, while equating all IEEE-754 `NaN` bit patterns.
pub open spec fn spec_same_value(x: JsValView, y: JsValView) -> bool {
    match (x, y) {
        (JsValView::Undefined, JsValView::Undefined) => true,
        (JsValView::Null, JsValView::Null) => true,
        (JsValView::Bool(a), JsValView::Bool(b)) => a == b,
        (JsValView::NumberBits(a), JsValView::NumberBits(b)) =>
            (spec_is_nan_bits(a) && spec_is_nan_bits(b)) || a == b,
        (JsValView::BigInt(a), JsValView::BigInt(b)) => spec_bigint_same_value(a, b),
        (JsValView::Str(a), JsValView::Str(b)) => a == b,
        (JsValView::Symbol(a), JsValView::Symbol(b)) => a == b,
        (JsValView::Object(a), JsValView::Object(b)) => a == b,
        _ => false,
    }
}

/// ECMA-262 §7.2.11 `SameValueZero(x, y)`:
/// Like `SameValue`, except `+0.0` and `-0.0` are also equal.
pub open spec fn spec_same_value_zero(x: JsValView, y: JsValView) -> bool {
    match (x, y) {
        (JsValView::NumberBits(a), JsValView::NumberBits(b)) =>
            (spec_is_zero_bits(a) && spec_is_zero_bits(b))
                || (spec_is_nan_bits(a) && spec_is_nan_bits(b))
                || a == b,
        _ => spec_same_value(x, y),
    }
}

pub fn same_value(x: &JsVal, y: &JsVal) -> (r: bool)
    ensures
        r == spec_same_value(x@, y@),
{
    match (x, y) {
        (JsVal::Undefined, JsVal::Undefined) => true,
        (JsVal::Null, JsVal::Null) => true,
        (JsVal::Bool(a), JsVal::Bool(b)) => *a == *b,
        (JsVal::NumberBits(a), JsVal::NumberBits(b)) =>
            (is_nan_bits(*a) && is_nan_bits(*b)) || *a == *b,
        (JsVal::BigInt(a), JsVal::BigInt(b)) => bigint_same_value(a, b),
        (JsVal::Str(a), JsVal::Str(b)) => eq_vec_u16(a, b),
        (JsVal::Symbol(a), JsVal::Symbol(b)) => *a == *b,
        (JsVal::Object(a), JsVal::Object(b)) => a.0 == b.0,
        _ => false,
    }
}

pub fn same_value_zero(x: &JsVal, y: &JsVal) -> (r: bool)
    ensures
        r == spec_same_value_zero(x@, y@),
{
    match (x, y) {
        (JsVal::NumberBits(a), JsVal::NumberBits(b)) =>
            (is_zero_bits(*a) && is_zero_bits(*b))
                || (is_nan_bits(*a) && is_nan_bits(*b))
                || *a == *b,
        _ => same_value(x, y),
    }
}

pub proof fn lemma_same_value_refl(x: JsValView)
    ensures
        spec_same_value(x, x),
{
}

pub proof fn lemma_same_value_sym(x: JsValView, y: JsValView)
    ensures
        spec_same_value(x, y) == spec_same_value(y, x),
{
}

pub proof fn lemma_same_value_trans(x: JsValView, y: JsValView, z: JsValView)
    requires
        spec_same_value(x, y),
        spec_same_value(y, z),
    ensures
        spec_same_value(x, z),
{
}

pub proof fn lemma_pos_neg_zero_distinct_in_same_value()
    ensures
        !spec_same_value(
            JsValView::NumberBits(POS_ZERO_BITS),
            JsValView::NumberBits(NEG_ZERO_BITS),
        ),
        spec_same_value_zero(
            JsValView::NumberBits(POS_ZERO_BITS),
            JsValView::NumberBits(NEG_ZERO_BITS),
        ),
{
    assert(!spec_is_nan_bits(POS_ZERO_BITS)) by (bit_vector);
    assert(!spec_is_nan_bits(NEG_ZERO_BITS)) by (bit_vector);
}

pub proof fn lemma_nan_payloads_equal_in_same_value()
    ensures
        spec_same_value(
            JsValView::NumberBits(0x7ff8_0000_0000_0000u64),
            JsValView::NumberBits(0xfff8_0000_0000_0001u64),
        ),
{
    assert(spec_is_nan_bits(0x7ff8_0000_0000_0000u64)) by (bit_vector);
    assert(spec_is_nan_bits(0xfff8_0000_0000_0001u64)) by (bit_vector);
}

// ---------------------------------------------------------------------------------------
// Exact IEEE-754 binary64 <-> `u32` Bit Encoding for Array `length` (§10.4.2)
// ---------------------------------------------------------------------------------------

pub open spec fn spec_msb_u32(n: u32) -> u32 {
    let k4: u32 = if n >= 0x0001_0000u32 { 16u32 } else { 0u32 };
    let n4: u32 = n >> k4;
    let k3: u32 = if n4 >= 0x0100u32 { 8u32 } else { 0u32 };
    let n3: u32 = n4 >> k3;
    let k2: u32 = if n3 >= 0x0010u32 { 4u32 } else { 0u32 };
    let n2: u32 = n3 >> k2;
    let k1: u32 = if n2 >= 0x0004u32 { 2u32 } else { 0u32 };
    let n1: u32 = n2 >> k1;
    let k0: u32 = if n1 >= 0x0002u32 { 1u32 } else { 0u32 };
    add(add(add(add(k4, k3), k2), k1), k0)
}

/// Exact IEEE-754 binary64 encoding of `n: u32` (`+0.0` for `0`).
pub open spec fn spec_u32_to_f64_bits(n: u32) -> u64 {
    if n == 0u32 {
        0u64
    } else {
        let k: u64 = spec_msb_u32(n) as u64;
        let exp: u64 = add(1023u64, k);
        let shift: u64 = sub(52u64, k);
        let mant: u64 = sub(n as u64, 1u64 << k) << shift;
        (exp << 52u64) | mant
    }
}

/// Exact IEEE-754 binary64 decoding to `u32` iff the number is integral and in `[0, 2^32 - 1]`
/// (accepting both `+0.0` and `-0.0` as `Some(0u32)` per `SameValueZero(𝔽(newLen), numberLen)`).
pub open spec fn spec_f64_bits_to_exact_u32(bits: u64) -> Option<u32> {
    if bits == 0u64 || bits == 0x8000_0000_0000_0000u64 {
        Some(0u32)
    } else if (bits >> 63u64) != 0u64 {
        None
    } else {
        let exp: u64 = (bits >> 52u64) & 0x7ffu64;
        if exp < 1023u64 || exp > 1054u64 {
            None
        } else {
            let k: u64 = sub(exp, 1023u64);
            let shift: u64 = sub(52u64, k);
            let frac: u64 = bits & 0x000f_ffff_ffff_ffffu64;
            let low_mask: u64 = sub(1u64 << shift, 1u64);
            if (frac & low_mask) != 0u64 {
                None
            } else {
                Some(((1u64 << k) | (frac >> shift)) as u32)
            }
        }
    }
}

pub proof fn lemma_u32_f64_bits_roundtrip(n: u32)
    ensures
        spec_f64_bits_to_exact_u32(spec_u32_to_f64_bits(n)) == Some(n),
        !spec_is_nan_bits(spec_u32_to_f64_bits(n)),
        spec_u32_to_f64_bits(n) != NEG_ZERO_BITS,
{
    let bits = spec_u32_to_f64_bits(n);
    if n == 0u32 {
        assert(!spec_is_nan_bits(0u64)) by (bit_vector);
    } else {
        assert( ({
            let k4: u32 = if n >= 0x0001_0000u32 { 16u32 } else { 0u32 };
            let n4: u32 = n >> k4;
            let k3: u32 = if n4 >= 0x0100u32 { 8u32 } else { 0u32 };
            let n3: u32 = n4 >> k3;
            let k2: u32 = if n3 >= 0x0010u32 { 4u32 } else { 0u32 };
            let n2: u32 = n3 >> k2;
            let k1: u32 = if n2 >= 0x0004u32 { 2u32 } else { 0u32 };
            let n1: u32 = n2 >> k1;
            let k0: u32 = if n1 >= 0x0002u32 { 1u32 } else { 0u32 };
            let k: u64 = add(add(add(add(k4, k3), k2), k1), k0) as u64;
            let exp: u64 = add(1023u64, k);
            let shift: u64 = sub(52u64, k);
            let mant: u64 = sub(n as u64, 1u64 << k) << shift;
            let b: u64 = (exp << 52u64) | mant;
            let b_exp: u64 = (b >> 52u64) & 0x7ffu64;
            let b_frac: u64 = b & 0x000f_ffff_ffff_ffffu64;
            let low_mask: u64 = sub(1u64 << shift, 1u64);
            n != 0u32 ==> (
                b != 0u64
                && b != 0x8000_0000_0000_0000u64
                && (b >> 63u64) == 0u64
                && 1023u64 <= b_exp && b_exp <= 1054u64
                && sub(b_exp, 1023u64) == k
                && (b_frac & low_mask) == 0u64
                && (((1u64 << k) | (b_frac >> shift)) as u32) == n
                && !(b_exp == 0x7ffu64 && b_frac != 0u64)
            )
        }) ) by (bit_vector);
        assert(spec_f64_bits_to_exact_u32(bits) == Some(n));
        assert(!spec_is_nan_bits(bits));
        assert(bits != NEG_ZERO_BITS);
    }
}

pub proof fn lemma_u32_f64_bits_injective(a: u32, b: u32)
    ensures
        spec_same_value(
            JsValView::NumberBits(spec_u32_to_f64_bits(a)),
            JsValView::NumberBits(spec_u32_to_f64_bits(b)),
        ) <==> (a == b),
{
    lemma_u32_f64_bits_roundtrip(a);
    lemma_u32_f64_bits_roundtrip(b);
}

pub proof fn lemma_f64_bits_to_exact_u32_canonical(bits: u64, n: u32)
    requires
        spec_f64_bits_to_exact_u32(bits) == Some(n),
    ensures
        spec_same_value_zero(
            JsValView::NumberBits(bits),
            JsValView::NumberBits(spec_u32_to_f64_bits(n)),
        ),
        bits != NEG_ZERO_BITS ==> bits == spec_u32_to_f64_bits(n),
{
    if bits == 0u64 || bits == 0x8000_0000_0000_0000u64 {
        assert(n == 0u32);
    } else {
        assert( ({
            let exp: u64 = (bits >> 52u64) & 0x7ffu64;
            let k: u64 = sub(exp, 1023u64);
            let shift: u64 = sub(52u64, k);
            let frac: u64 = bits & 0x000f_ffff_ffff_ffffu64;
            let low_mask: u64 = sub(1u64 << shift, 1u64);
            let val: u32 = ((1u64 << k) | (frac >> shift)) as u32;
            let k4: u32 = if val >= 0x0001_0000u32 { 16u32 } else { 0u32 };
            let n4: u32 = val >> k4;
            let k3: u32 = if n4 >= 0x0100u32 { 8u32 } else { 0u32 };
            let n3: u32 = n4 >> k3;
            let k2: u32 = if n3 >= 0x0010u32 { 4u32 } else { 0u32 };
            let n2: u32 = n3 >> k2;
            let k1: u32 = if n2 >= 0x0004u32 { 2u32 } else { 0u32 };
            let n1: u32 = n2 >> k1;
            let k0: u32 = if n1 >= 0x0002u32 { 1u32 } else { 0u32 };
            let m_k: u64 = add(add(add(add(k4, k3), k2), k1), k0) as u64;
            let m_exp: u64 = add(1023u64, m_k);
            let m_shift: u64 = sub(52u64, m_k);
            let m_mant: u64 = sub(val as u64, 1u64 << m_k) << m_shift;
            let encoded: u64 = (m_exp << 52u64) | m_mant;
            (bits != 0u64 && bits != 0x8000_0000_0000_0000u64 && (bits >> 63u64) == 0u64
                && 1023u64 <= exp && exp <= 1054u64 && (frac & low_mask) == 0u64)
            ==> (val != 0u32 && m_k == k && encoded == bits)
        }) ) by (bit_vector);
        lemma_u32_f64_bits_roundtrip(n);
    }
}

pub fn msb_u32(n: u32) -> (k: u32)
    requires
        n > 0,
    ensures
        k == spec_msb_u32(n),
        k < 32,
        (1u64 << (k as u64)) <= (n as u64),
{
    let k4: u32 = if n >= 0x0001_0000u32 { 16u32 } else { 0u32 };
    let n4: u32 = n >> k4;
    let k3: u32 = if n4 >= 0x0100u32 { 8u32 } else { 0u32 };
    let n3: u32 = n4 >> k3;
    let k2: u32 = if n3 >= 0x0010u32 { 4u32 } else { 0u32 };
    let n2: u32 = n3 >> k2;
    let k1: u32 = if n2 >= 0x0004u32 { 2u32 } else { 0u32 };
    let n1: u32 = n2 >> k1;
    let k0: u32 = if n1 >= 0x0002u32 { 1u32 } else { 0u32 };
    proof {
        assert( ({
            let a4: u32 = if n >= 0x0001_0000u32 { 16u32 } else { 0u32 };
            let m4: u32 = n >> a4;
            let a3: u32 = if m4 >= 0x0100u32 { 8u32 } else { 0u32 };
            let m3: u32 = m4 >> a3;
            let a2: u32 = if m3 >= 0x0010u32 { 4u32 } else { 0u32 };
            let m2: u32 = m3 >> a2;
            let a1: u32 = if m2 >= 0x0004u32 { 2u32 } else { 0u32 };
            let m1: u32 = m2 >> a1;
            let a0: u32 = if m1 >= 0x0002u32 { 1u32 } else { 0u32 };
            let kk: u32 = add(add(add(add(a4, a3), a2), a1), a0);
            n > 0u32 ==> (
                a4 + a3 + a2 + a1 + a0 < 32
                && (1u64 << (kk as u64)) <= (n as u64)
            )
        }) ) by (bit_vector);
    }
    k4 + k3 + k2 + k1 + k0
}

pub fn u32_to_f64_bits(n: u32) -> (bits: u64)
    ensures
        bits == spec_u32_to_f64_bits(n),
{
    if n == 0 {
        0u64
    } else {
        let k = msb_u32(n) as u64;
        let exp: u64 = 1023u64 + k;
        let shift: u64 = 52u64 - k;
        let mant: u64 = ((n as u64) - (1u64 << k)) << shift;
        proof {
            assert( ({
                let a4: u32 = if n >= 0x0001_0000u32 { 16u32 } else { 0u32 };
                let m4: u32 = n >> a4;
                let a3: u32 = if m4 >= 0x0100u32 { 8u32 } else { 0u32 };
                let m3: u32 = m4 >> a3;
                let a2: u32 = if m3 >= 0x0010u32 { 4u32 } else { 0u32 };
                let m2: u32 = m3 >> a2;
                let a1: u32 = if m2 >= 0x0004u32 { 2u32 } else { 0u32 };
                let m1: u32 = m2 >> a1;
                let a0: u32 = if m1 >= 0x0002u32 { 1u32 } else { 0u32 };
                let kk: u64 = add(add(add(add(a4, a3), a2), a1), a0) as u64;
                n > 0u32 ==> sub(n as u64, 1u64 << kk) < (1u64 << kk)
            }) ) by (bit_vector);
        }
        (exp << 52u64) | mant
    }
}

pub fn f64_bits_to_exact_u32(bits: u64) -> (res: Option<u32>)
    ensures
        res == spec_f64_bits_to_exact_u32(bits),
{
    if bits == 0u64 || bits == 0x8000_0000_0000_0000u64 {
        Some(0u32)
    } else if (bits >> 63u64) != 0u64 {
        None
    } else {
        let exp: u64 = (bits >> 52u64) & 0x7ffu64;
        if exp < 1023u64 || exp > 1054u64 {
            None
        } else {
            let k: u64 = exp - 1023u64;
            let shift: u64 = 52u64 - k;
            let frac: u64 = bits & 0x000f_ffff_ffff_ffffu64;
            proof {
                assert(21u64 <= shift && shift <= 52u64 ==> (1u64 << shift) >= 1u64) by (bit_vector);
            }
            let low_mask: u64 = (1u64 << shift) - 1u64;
            if (frac & low_mask) != 0u64 {
                None
            } else {
                proof {
                    assert( ({
                        let e: u64 = (bits >> 52u64) & 0x7ffu64;
                        let kk: u64 = sub(e, 1023u64);
                        let sh: u64 = sub(52u64, kk);
                        let fr: u64 = bits & 0x000f_ffff_ffff_ffffu64;
                        (1023u64 <= e && e <= 1054u64) ==> ((1u64 << kk) | (fr >> sh)) <= 0xffff_ffffu64
                    }) ) by (bit_vector);
                }
                Some(((1u64 << k) | (frac >> shift)) as u32)
            }
        }
    }
}

pub open spec fn spec_pow2(k: nat) -> nat
    decreases k,
{
    if k == 0 {
        1
    } else {
        2 * spec_pow2((k - 1) as nat)
    }
}

proof fn lemma_pow2_shl(k: u64)
    requires
        k <= 62u64,
    ensures
        ((1u64 << k) as nat) == spec_pow2(k as nat),
    decreases k,
{
    if k == 0u64 {
        assert((1u64 << 0u64) == 1u64) by (bit_vector);
    } else {
        let km1: u64 = (k - 1) as u64;
        lemma_pow2_shl(km1);
        let p: u64 = 1u64 << km1;
        assert(k > 0u64 && k <= 62u64 ==> (1u64 << k) == add(1u64 << sub(k, 1u64), 1u64 << sub(k, 1u64)) && (1u64 << sub(k, 1u64)) <= 0x4000_0000_0000_0000u64) by (bit_vector);
        assert(((1u64 << k) as nat) == (p as nat) + (p as nat));
    }
}

proof fn lemma_shl_mul_pow2(v: u64, k: u64)
    requires
        k <= 52u64,
        (v << k) < 0x0020_0000_0000_0000u64,
        forall|j: u64| j <= k ==> (#[trigger] (v << j)) >> j == v,
    ensures
        ((v << k) as nat) == (v as nat) * spec_pow2(k as nat),
    decreases k,
{
    if k == 0u64 {
        assert((v << 0u64) == v) by (bit_vector);
        assert(spec_pow2(0) == 1);
        assert((v as nat) * 1 == (v as nat));
    } else {
        let km1: u64 = (k - 1) as u64;
        assert(k > 0u64 && k <= 52u64 && (v << k) < 0x0020_0000_0000_0000u64 && ((v << k) >> k) == v
            ==> (v << sub(k, 1u64)) < 0x0010_0000_0000_0000u64
                && (v << k) == add(v << sub(k, 1u64), v << sub(k, 1u64))) by (bit_vector);
        lemma_shl_mul_pow2(v, km1);
        let prev: nat = (v << km1) as nat;
        assert(((v << k) as nat) == prev + prev);
        let p2: nat = spec_pow2(km1 as nat);
        assert(spec_pow2(k as nat) == 2 * p2);
        assert((v as nat) * (2 * p2) == prev + prev) by (nonlinear_arith)
            requires prev == (v as nat) * p2;
    }
}

/// Bridges `spec_u32_to_f64_bits` directly to IEEE-754 binary64's mathematical real-value
/// equation `(2^52 + frac) == n * 2^(1075 - exp)` (i.e. `(1 + frac / 2^52) * 2^(exp - 1023) == n`).
pub proof fn lemma_u32_f64_bits_ieee754_value(n: u32)
    ensures
        n == 0u32 ==> spec_u32_to_f64_bits(n) == 0u64,
        n > 0u32 ==> ({
            let bits = spec_u32_to_f64_bits(n);
            let sign = bits >> 63u64;
            let exp = (bits >> 52u64) & 0x7ffu64;
            let frac = bits & 0x000f_ffff_ffff_ffffu64;
            sign == 0u64
            && 1023u64 <= exp && exp <= 1054u64
            && (spec_pow2(52) + (frac as nat))
                == (n as nat) * spec_pow2((1075 - (exp as int)) as nat)
        }),
{
    if n > 0u32 {
        let bits = spec_u32_to_f64_bits(n);
        let exp: u64 = (bits >> 52u64) & 0x7ffu64;
        let frac: u64 = bits & 0x000f_ffff_ffff_ffffu64;
        assert( ({
            let k4: u32 = if n >= 0x0001_0000u32 { 16u32 } else { 0u32 };
            let n4: u32 = n >> k4;
            let k3: u32 = if n4 >= 0x0100u32 { 8u32 } else { 0u32 };
            let n3: u32 = n4 >> k3;
            let k2: u32 = if n3 >= 0x0010u32 { 4u32 } else { 0u32 };
            let n2: u32 = n3 >> k2;
            let k1: u32 = if n2 >= 0x0004u32 { 2u32 } else { 0u32 };
            let n1: u32 = n2 >> k1;
            let k0: u32 = if n1 >= 0x0002u32 { 1u32 } else { 0u32 };
            let k: u64 = add(add(add(add(k4, k3), k2), k1), k0) as u64;
            let e: u64 = add(1023u64, k);
            let sh: u64 = sub(52u64, k);
            let mant: u64 = sub(n as u64, 1u64 << k) << sh;
            let b: u64 = (e << 52u64) | mant;
            let b_sign: u64 = b >> 63u64;
            let b_exp: u64 = (b >> 52u64) & 0x7ffu64;
            let b_frac: u64 = b & 0x000f_ffff_ffff_ffffu64;
            let b_sh: u64 = sub(1075u64, b_exp);
            n > 0u32 ==> (
                b_sign == 0u64
                && 1023u64 <= b_exp && b_exp <= 1054u64
                && b_frac < 0x0010_0000_0000_0000u64
                && ((n as u64) << b_sh) < 0x0020_0000_0000_0000u64
                && add(0x0010_0000_0000_0000u64, b_frac) == ((n as u64) << b_sh)
            )
        }) ) by (bit_vector);
        let sh: u64 = (1075 - (exp as int)) as u64;
        assert forall|j: u64| j <= sh implies (#[trigger] ((n as u64) << j)) >> j == (n as u64) by {
            assert( ({
                let k4: u32 = if n >= 0x0001_0000u32 { 16u32 } else { 0u32 };
                let n4: u32 = n >> k4;
                let k3: u32 = if n4 >= 0x0100u32 { 8u32 } else { 0u32 };
                let n3: u32 = n4 >> k3;
                let k2: u32 = if n3 >= 0x0010u32 { 4u32 } else { 0u32 };
                let n2: u32 = n3 >> k2;
                let k1: u32 = if n2 >= 0x0004u32 { 2u32 } else { 0u32 };
                let n1: u32 = n2 >> k1;
                let k0: u32 = if n1 >= 0x0002u32 { 1u32 } else { 0u32 };
                let k: u64 = add(add(add(add(k4, k3), k2), k1), k0) as u64;
                let e: u64 = add(1023u64, k);
                let sh0: u64 = sub(52u64, k);
                let mant: u64 = sub(n as u64, 1u64 << k) << sh0;
                let b: u64 = (e << 52u64) | mant;
                let b_exp: u64 = (b >> 52u64) & 0x7ffu64;
                let b_sh: u64 = sub(1075u64, b_exp);
                (n > 0u32 && j <= b_sh) ==> (((n as u64) << j) >> j) == (n as u64)
            }) ) by (bit_vector);
        };
        lemma_pow2_shl(52u64);
        assert((1u64 << 52u64) == 0x0010_0000_0000_0000u64) by (bit_vector);
        lemma_shl_mul_pow2(n as u64, sh);
    }
}

pub fn js_val_from_u32(n: u32) -> (v: JsVal)
    ensures
        v@ == JsValView::NumberBits(spec_u32_to_f64_bits(n)),
{
    JsVal::NumberBits(u32_to_f64_bits(n))
}

} // verus!
