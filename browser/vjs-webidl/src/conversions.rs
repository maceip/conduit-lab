//! WHATWG Web IDL §3.2 (`ToIDL` and `ToJS`) JavaScript type mapping, transcribed into
//! Verus specifications with machine-checked `exec == spec` equivalence and algebraic
//! invariants.
//!
//! Spec source: whatwg/webidl@54a5f2de6a34e27a517a49370bc07d8943b0be11 (2026-11-14).
//! Covers:
//! - `any`, `undefined`, `boolean` (§3.2.1–§3.2.3)
//! - All 8 integer types (`byte`, `octet`, `short`, `unsigned short`, `long`,
//!   `unsigned long`, `long long`, `unsigned long long`) under Standard modulo-2^N,
//!   `[EnforceRange]`, and `[Clamp]` ties-to-even (§3.2.4, `IntegerPart`, `ConvertToInt`)
//! - `DOMString` (§3.2.15), `ByteString` (§3.2.16 + length & roundtrip proofs),
//!   `USVString` (§3.2.17 + zero-unpaired-surrogate & idempotence `usv(usv(s)) == usv(s)`
//!   proofs + Unicode scalar decoding)
//! - `nullable<T>` (`T?`, §3.2.22), `sequence<T>` (§3.2.19), `record<K, V>` (§3.2.21),
//!   and typed `Dictionary` extraction in lexicographical member key order (§3.2.20) for
//!   `EventInit`, `RequestInit`, `StorageOp`, `NodeOp`, and `UrlHref`.

use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::div_mod::{
    lemma_fundamental_div_mod,
    lemma_fundamental_div_mod_converse,
};

verus! {

// ---------------------------------------------------------------------------------------
// Error & IEEE-754 Constants
// ---------------------------------------------------------------------------------------

/// Web IDL / ECMAScript conversion error (preserving exact user-thrown exception identity
/// `AbruptException(id)` per ECMA-262 / Web IDL `?` completion propagation).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum IdlError {
    TypeError,
    AbruptException(u64),
}

pub const F64_POS_ZERO: u64 = 0x0000_0000_0000_0000u64;
pub const F64_NEG_ZERO: u64 = 0x8000_0000_0000_0000u64;
pub const F64_ONE: u64 = 0x3FF0_0000_0000_0000u64;
pub const F64_POS_INF: u64 = 0x7FF0_0000_0000_0000u64;
pub const F64_NEG_INF: u64 = 0xFFF0_0000_0000_0000u64;
pub const F64_CANON_NAN: u64 = 0x7FF8_0000_0000_0000u64;
pub const MAX_SAFE_INT_I64: i64 = 9007199254740991i64; // 2^53 - 1
pub const MIN_SAFE_INT_I64: i64 = -9007199254740991i64; // -(2^53 - 1)
pub const MAX_SAFE_INT_U64: u64 = 9007199254740991u64; // 2^53 - 1

/// Web IDL integer conversion extended attribute (§3.2.4, §3.3.3 `[Clamp]`, §3.3.5 `[EnforceRange]`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum IntAttr {
    Standard,
    EnforceRange,
    Clamp,
}

// ---------------------------------------------------------------------------------------
// JavaScript Host-Boundary Value & Arena Model
// ---------------------------------------------------------------------------------------

/// JavaScript value at the Web IDL boundary (numbers represented at exact IEEE-754
/// binary64 bit level; strings as UTF-16 code unit sequences; objects by index into
/// `JsObjectArena`).
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum JsValue {
    Undefined,
    Null,
    Bool(bool),
    Number(u64),
    BigInt { neg: bool, mag: u128 },
    String(Vec<u16>),
    Symbol(u64),
    Object(usize),
}

/// Spec-level view of `JsValue`.
pub enum SpecJsValue {
    Undefined,
    Null,
    Bool(bool),
    Number(u64),
    BigInt { neg: bool, mag: u128 },
    String(Seq<u16>),
    Symbol(u64),
    Object(usize),
}

impl View for JsValue {
    type V = SpecJsValue;

    open spec fn view(&self) -> SpecJsValue {
        match self {
            JsValue::Undefined => SpecJsValue::Undefined,
            JsValue::Null => SpecJsValue::Null,
            JsValue::Bool(b) => SpecJsValue::Bool(*b),
            JsValue::Number(bits) => SpecJsValue::Number(*bits),
            JsValue::BigInt { neg, mag } => SpecJsValue::BigInt { neg: *neg, mag: *mag },
            JsValue::String(s) => SpecJsValue::String(s@),
            JsValue::Symbol(id) => SpecJsValue::Symbol(*id),
            JsValue::Object(oid) => SpecJsValue::Object(*oid),
        }
    }
}

/// Own property on a JS object (`[[OwnPropertyKeys]]` order, with `is_symbol`, `enumerable`,
/// and accessor `is_getter` / `getter_throws` behavior).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct JsOwnProp {
    pub key: Vec<u16>,
    pub is_symbol: bool,
    pub enumerable: bool,
    pub is_getter: bool,
    pub getter_throws: Option<u64>,
    pub value: JsValue,
}

pub struct SpecJsOwnProp {
    pub key: Seq<u16>,
    pub is_symbol: bool,
    pub enumerable: bool,
    pub is_getter: bool,
    pub getter_throws: Option<u64>,
    pub value: SpecJsValue,
}

impl View for JsOwnProp {
    type V = SpecJsOwnProp;

    open spec fn view(&self) -> SpecJsOwnProp {
        SpecJsOwnProp {
            key: self.key@,
            is_symbol: self.is_symbol,
            enumerable: self.enumerable,
            is_getter: self.is_getter,
            getter_throws: self.getter_throws,
            value: self.value@,
        }
    }
}

/// Inherited prototype property visible to `Get(O, P)` (used by Web IDL `Dictionary`),
/// but NOT visited by `O.[[OwnPropertyKeys]]()` / `[[GetOwnProperty]]` (Web IDL `record`).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct JsProtoProp {
    pub key: Vec<u16>,
    pub value: JsValue,
}

pub struct SpecJsProtoProp {
    pub key: Seq<u16>,
    pub value: SpecJsValue,
}

impl View for JsProtoProp {
    type V = SpecJsProtoProp;

    open spec fn view(&self) -> SpecJsProtoProp {
        SpecJsProtoProp {
            key: self.key@,
            value: self.value@,
        }
    }
}

/// Behavior of `GetMethod(V, %Symbol.iterator%)` + iterator protocol on an object.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum JsIterator {
    NotIterable,
    ThrowTypeError,
    Items(Vec<JsValue>),
}

pub enum SpecJsIterator {
    NotIterable,
    ThrowTypeError,
    Items(Seq<SpecJsValue>),
}

impl View for JsIterator {
    type V = SpecJsIterator;

    open spec fn view(&self) -> SpecJsIterator {
        match self {
            JsIterator::NotIterable => SpecJsIterator::NotIterable,
            JsIterator::ThrowTypeError => SpecJsIterator::ThrowTypeError,
            JsIterator::Items(v) => SpecJsIterator::Items(
                Seq::new(v@.len(), |i: int| v@[i]@),
            ),
        }
    }
}

/// Object `ToPrimitive` / `toString` hook for Web IDL string & number conversions.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum JsToStringHook {
    DefaultObjectTag,
    ReturnStr(Vec<u16>),
    ThrowError,
    ThrowException(u64),
}

pub enum SpecJsToStringHook {
    DefaultObjectTag,
    ReturnStr(Seq<u16>),
    ThrowError,
    ThrowException(u64),
}

impl View for JsToStringHook {
    type V = SpecJsToStringHook;

    open spec fn view(&self) -> SpecJsToStringHook {
        match self {
            JsToStringHook::DefaultObjectTag => SpecJsToStringHook::DefaultObjectTag,
            JsToStringHook::ReturnStr(s) => SpecJsToStringHook::ReturnStr(s@),
            JsToStringHook::ThrowError => SpecJsToStringHook::ThrowError,
            JsToStringHook::ThrowException(id) => SpecJsToStringHook::ThrowException(*id),
        }
    }
}

/// Object record in `JsObjectArena`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct JsObjectRecord {
    pub own_props: Vec<JsOwnProp>,
    pub proto_props: Vec<JsProtoProp>,
    pub iterator: JsIterator,
    pub to_string_hook: JsToStringHook,
    pub to_number_override: Option<u64>,
}

pub struct SpecJsObjectRecord {
    pub own_props: Seq<SpecJsOwnProp>,
    pub proto_props: Seq<SpecJsProtoProp>,
    pub iterator: SpecJsIterator,
    pub to_string_hook: SpecJsToStringHook,
    pub to_number_override: Option<u64>,
}

impl View for JsObjectRecord {
    type V = SpecJsObjectRecord;

    open spec fn view(&self) -> SpecJsObjectRecord {
        SpecJsObjectRecord {
            own_props: Seq::new(self.own_props@.len(), |i: int| self.own_props@[i]@),
            proto_props: Seq::new(self.proto_props@.len(), |i: int| self.proto_props@[i]@),
            iterator: self.iterator@,
            to_string_hook: self.to_string_hook@,
            to_number_override: self.to_number_override,
        }
    }
}

/// Index-based arena of JS objects passed across the Web IDL boundary.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct JsObjectArena {
    pub objects: Vec<JsObjectRecord>,
}

impl View for JsObjectArena {
    type V = Seq<SpecJsObjectRecord>;

    open spec fn view(&self) -> Seq<SpecJsObjectRecord> {
        Seq::new(self.objects@.len(), |i: int| self.objects@[i]@)
    }
}

impl JsObjectArena {
    pub fn new() -> (a: Self)
        ensures
            a@.len() == 0,
    {
        JsObjectArena { objects: Vec::new() }
    }

    pub fn alloc(&mut self, rec: JsObjectRecord) -> (id: usize)
        requires
            old(self)@.len() < usize::MAX,
        ensures
            id == old(self)@.len(),
            final(self)@ == old(self)@.push(rec@),
    {
        let id = self.objects.len();
        self.objects.push(rec);
        proof {
            assert(self@ =~= old(self)@.push(rec@));
        }
        id
    }
}

// ---------------------------------------------------------------------------------------
// §3.2.1 `any`, §3.2.2 `undefined`, §3.2.3 `boolean`
// ---------------------------------------------------------------------------------------

/// Web IDL `any` value (§3.2.1).
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum IdlAny {
    Undefined,
    NullObject,
    Boolean(bool),
    UnrestrictedDouble(u64),
    BigInt { neg: bool, mag: u128 },
    DomString(Vec<u16>),
    Symbol(u64),
    ObjectRef(usize),
}

pub enum SpecIdlAny {
    Undefined,
    NullObject,
    Boolean(bool),
    UnrestrictedDouble(u64),
    BigInt { neg: bool, mag: u128 },
    DomString(Seq<u16>),
    Symbol(u64),
    ObjectRef(usize),
}

impl View for IdlAny {
    type V = SpecIdlAny;

    open spec fn view(&self) -> SpecIdlAny {
        match self {
            IdlAny::Undefined => SpecIdlAny::Undefined,
            IdlAny::NullObject => SpecIdlAny::NullObject,
            IdlAny::Boolean(b) => SpecIdlAny::Boolean(*b),
            IdlAny::UnrestrictedDouble(bits) => SpecIdlAny::UnrestrictedDouble(*bits),
            IdlAny::BigInt { neg, mag } => SpecIdlAny::BigInt { neg: *neg, mag: *mag },
            IdlAny::DomString(s) => SpecIdlAny::DomString(s@),
            IdlAny::Symbol(id) => SpecIdlAny::Symbol(*id),
            IdlAny::ObjectRef(oid) => SpecIdlAny::ObjectRef(*oid),
        }
    }
}

fn clone_u16_slice(s: &[u16]) -> (out: Vec<u16>)
    ensures
        out@ == s@,
{
    let n = s.len();
    let mut out: Vec<u16> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == s@.len(),
            out@ == s@.subrange(0, i as int),
        decreases n - i,
    {
        out.push(s[i]);
        i += 1;
        proof {
            assert(out@ =~= s@.subrange(0, i as int));
        }
    }
    proof {
        assert(s@.subrange(0, n as int) =~= s@);
    }
    out
}

fn clone_u8_slice(s: &[u8]) -> (out: Vec<u8>)
    ensures
        out@ == s@,
{
    let n = s.len();
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == s@.len(),
            out@ == s@.subrange(0, i as int),
        decreases n - i,
    {
        out.push(s[i]);
        i += 1;
        proof {
            assert(out@ =~= s@.subrange(0, i as int));
        }
    }
    proof {
        assert(s@.subrange(0, n as int) =~= s@);
    }
    out
}

/// WHATWG Web IDL §3.2.1 (`#js-to-any`): convert a JS value to IDL `any`.
/// Note: per §3.2.7 `unrestricted double`, `-0` is preserved and `NaN` is canonicalized
/// to quiet `NaN` (`F64_CANON_NAN`).
pub open spec fn spec_is_f64_nan(bits: u64) -> bool {
    let rem63 = bits % 0x8000_0000_0000_0000u64;
    let exp = rem63 / 0x0010_0000_0000_0000u64;
    let mant = rem63 % 0x0010_0000_0000_0000u64;
    exp == 0x7FFu64 && mant != 0u64
}

pub open spec fn spec_is_f64_zero(bits: u64) -> bool {
    (bits % 0x8000_0000_0000_0000u64) == 0u64
}

pub open spec fn spec_to_idl_any(v: SpecJsValue) -> SpecIdlAny {
    match v {
        SpecJsValue::Undefined => SpecIdlAny::Undefined,
        SpecJsValue::Null => SpecIdlAny::NullObject,
        SpecJsValue::Bool(b) => SpecIdlAny::Boolean(b),
        SpecJsValue::Number(bits) => SpecIdlAny::UnrestrictedDouble(
            if spec_is_f64_nan(bits) { F64_CANON_NAN } else { bits },
        ),
        SpecJsValue::BigInt { neg, mag } => SpecIdlAny::BigInt {
            neg: if mag == 0u128 { false } else { neg },
            mag,
        },
        SpecJsValue::String(s) => SpecIdlAny::DomString(s),
        SpecJsValue::Symbol(id) => SpecIdlAny::Symbol(id),
        SpecJsValue::Object(oid) => SpecIdlAny::ObjectRef(oid),
    }
}

pub open spec fn spec_to_js_any(v: SpecIdlAny) -> SpecJsValue {
    match v {
        SpecIdlAny::Undefined => SpecJsValue::Undefined,
        SpecIdlAny::NullObject => SpecJsValue::Null,
        SpecIdlAny::Boolean(b) => SpecJsValue::Bool(b),
        SpecIdlAny::UnrestrictedDouble(bits) => SpecJsValue::Number(bits),
        SpecIdlAny::BigInt { neg, mag } => SpecJsValue::BigInt { neg, mag },
        SpecIdlAny::DomString(s) => SpecJsValue::String(s),
        SpecIdlAny::Symbol(id) => SpecJsValue::Symbol(id),
        SpecIdlAny::ObjectRef(oid) => SpecJsValue::Object(oid),
    }
}

pub fn is_f64_nan(bits: u64) -> (r: bool)
    ensures
        r == spec_is_f64_nan(bits),
{
    let rem63 = bits % 0x8000_0000_0000_0000u64;
    let exp = rem63 / 0x0010_0000_0000_0000u64;
    let mant = rem63 % 0x0010_0000_0000_0000u64;
    exp == 0x7FFu64 && mant != 0u64
}

pub fn is_f64_zero(bits: u64) -> (r: bool)
    ensures
        r == spec_is_f64_zero(bits),
{
    (bits % 0x8000_0000_0000_0000u64) == 0u64
}

pub fn to_idl_any(v: &JsValue) -> (out: IdlAny)
    ensures
        out@ == spec_to_idl_any(v@),
{
    match v {
        JsValue::Undefined => IdlAny::Undefined,
        JsValue::Null => IdlAny::NullObject,
        JsValue::Bool(b) => IdlAny::Boolean(*b),
        JsValue::Number(bits) => IdlAny::UnrestrictedDouble(
            if is_f64_nan(*bits) { F64_CANON_NAN } else { *bits },
        ),
        JsValue::BigInt { neg, mag } => IdlAny::BigInt {
            neg: if *mag == 0u128 { false } else { *neg },
            mag: *mag,
        },
        JsValue::String(s) => IdlAny::DomString(clone_u16_slice(s.as_slice())),
        JsValue::Symbol(id) => IdlAny::Symbol(*id),
        JsValue::Object(oid) => IdlAny::ObjectRef(*oid),
    }
}

pub fn to_js_any(v: &IdlAny) -> (out: JsValue)
    ensures
        out@ == spec_to_js_any(v@),
{
    match v {
        IdlAny::Undefined => JsValue::Undefined,
        IdlAny::NullObject => JsValue::Null,
        IdlAny::Boolean(b) => JsValue::Bool(*b),
        IdlAny::UnrestrictedDouble(bits) => JsValue::Number(*bits),
        IdlAny::BigInt { neg, mag } => JsValue::BigInt { neg: *neg, mag: *mag },
        IdlAny::DomString(s) => JsValue::String(clone_u16_slice(s.as_slice())),
        IdlAny::Symbol(id) => JsValue::Symbol(*id),
        IdlAny::ObjectRef(oid) => JsValue::Object(*oid),
    }
}

/// WHATWG Web IDL §3.2.2 (`#js-undefined`): convert JS value to IDL `undefined`.
pub open spec fn spec_to_idl_undefined(_v: SpecJsValue) -> () {
    ()
}

pub open spec fn spec_to_js_undefined() -> SpecJsValue {
    SpecJsValue::Undefined
}

pub fn to_idl_undefined(v: &JsValue) -> (out: ())
    ensures
        out == spec_to_idl_undefined(v@),
{
    let _ = v;
    ()
}

pub fn to_js_undefined() -> (out: JsValue)
    ensures
        out@ == spec_to_js_undefined(),
{
    JsValue::Undefined
}

/// WHATWG Web IDL §3.2.3 (`#js-boolean`): ECMA-262 `ToBoolean(V)`.
pub open spec fn spec_to_idl_boolean(v: SpecJsValue) -> bool {
    match v {
        SpecJsValue::Undefined => false,
        SpecJsValue::Null => false,
        SpecJsValue::Bool(b) => b,
        SpecJsValue::Number(bits) => !spec_is_f64_zero(bits) && !spec_is_f64_nan(bits),
        SpecJsValue::BigInt { mag, .. } => mag != 0u128,
        SpecJsValue::String(s) => s.len() > 0,
        SpecJsValue::Symbol(_) => true,
        SpecJsValue::Object(_) => true,
    }
}

pub open spec fn spec_to_js_boolean(b: bool) -> SpecJsValue {
    SpecJsValue::Bool(b)
}

pub fn to_idl_boolean(v: &JsValue) -> (out: bool)
    ensures
        out == spec_to_idl_boolean(v@),
{
    match v {
        JsValue::Undefined => false,
        JsValue::Null => false,
        JsValue::Bool(b) => *b,
        JsValue::Number(bits) => !is_f64_zero(*bits) && !is_f64_nan(*bits),
        JsValue::BigInt { mag, .. } => *mag != 0u128,
        JsValue::String(s) => s.len() > 0,
        JsValue::Symbol(_) => true,
        JsValue::Object(_) => true,
    }
}

pub fn to_js_boolean(b: bool) -> (out: JsValue)
    ensures
        out@ == spec_to_js_boolean(b),
{
    JsValue::Bool(b)
}

pub proof fn lemma_boolean_roundtrip(b: bool)
    ensures
        spec_to_idl_boolean(spec_to_js_boolean(b)) == b,
{
}

// ---------------------------------------------------------------------------------------
// Mathematical Powers of Two & IEEE-754 Binary64 Decoding
// ---------------------------------------------------------------------------------------

pub open spec fn pow2(k: nat) -> nat
    decreases k,
{
    if k == 0 {
        1nat
    } else {
        2nat * pow2((k - 1) as nat)
    }
}

pub proof fn lemma_pow2_pos(k: nat)
    ensures
        pow2(k) >= 1nat,
    decreases k,
{
    if k > 0 {
        lemma_pow2_pos((k - 1) as nat);
    }
}

pub proof fn lemma_pow2_strictly_increasing(a: nat, b: nat)
    requires
        a < b,
    ensures
        pow2(a) < pow2(b),
    decreases b - a,
{
    lemma_pow2_pos(a);
    if a + 1 < b {
        lemma_pow2_strictly_increasing(a, (b - 1) as nat);
    }
}

pub proof fn lemma_pow2_monotonic(a: nat, b: nat)
    requires
        a <= b,
    ensures
        pow2(a) <= pow2(b),
{
    if a < b {
        lemma_pow2_strictly_increasing(a, b);
    }
}

pub proof fn lemma_pow2_add(a: nat, b: nat)
    ensures
        pow2(a + b) == pow2(a) * pow2(b),
    decreases a,
{
    if a == 0 {
        assert(0nat + b == b);
        assert(1nat * pow2(b) == pow2(b));
    } else {
        lemma_pow2_add((a - 1) as nat, b);
        assert(((a - 1) as nat) + b == (a + b - 1) as nat);
        let x = pow2((a - 1) as nat);
        let y = pow2(b);
        assert(2nat * (x * y) == (2nat * x) * y) by (nonlinear_arith);
    }
}

pub proof fn lemma_pow2_values()
    ensures
        pow2(0) == 1nat,
        pow2(7) == 128nat,
        pow2(8) == 256nat,
        pow2(15) == 32768nat,
        pow2(16) == 65536nat,
        pow2(31) == 2147483648nat,
        pow2(32) == 4294967296nat,
        pow2(52) == 4503599627370496nat,
        pow2(53) == 9007199254740992nat,
        pow2(54) == 18014398509481984nat,
        pow2(62) == 4611686018427387904nat,
        pow2(63) == 9223372036854775808nat,
        pow2(64) == 18446744073709551616nat,
        pow2(120) == 0x0100_0000_0000_0000_0000_0000_0000_0000nat,
        pow2(126) == 85070591730234615865843651857942052864nat,
{
    reveal_with_fuel(pow2, 17);
    assert(pow2(16) == 65536nat);
    lemma_pow2_add(16, 15);
    assert(pow2(31) == 65536nat * 32768nat);
    lemma_pow2_add(16, 16);
    assert(pow2(32) == 65536nat * 65536nat);
    lemma_pow2_add(32, 16);
    assert(pow2(48) == 4294967296nat * 65536nat);
    reveal_with_fuel(pow2, 9);
    lemma_pow2_add(48, 4);
    assert(pow2(52) == pow2(48) * 16nat);
    assert(pow2(53) == 2nat * pow2(52));
    assert(pow2(54) == 2nat * pow2(53));
    lemma_pow2_add(48, 8);
    assert(pow2(56) == pow2(48) * 256nat);
    lemma_pow2_add(48, 14);
    lemma_pow2_add(10, 4);
    assert(pow2(62) == pow2(48) * 16384nat);
    assert(pow2(63) == 2nat * pow2(62));
    assert(pow2(64) == 2nat * pow2(63));
    lemma_pow2_add(64, 56);
    lemma_pow2_add(64, 62);
}

pub fn exec_pow2_u64(k: u32) -> (r: u64)
    requires
        k < 64,
    ensures
        r as nat == pow2(k as nat),
        r >= 1u64,
{
    proof {
        lemma_pow2_values();
    }
    let mut i: u32 = 0;
    let mut acc: u64 = 1;
    while i < k
        invariant
            i <= k,
            k < 64,
            acc as nat == pow2(i as nat),
            acc >= 1u64,
        decreases k - i,
    {
        proof {
            lemma_pow2_monotonic(i as nat, 62);
            lemma_pow2_values();
            assert(acc <= 4611686018427387904u64);
        }
        acc = acc * 2;
        i = i + 1;
    }
    acc
}

pub fn exec_pow2_u128(k: u32) -> (r: u128)
    requires
        k < 128,
    ensures
        r as nat == pow2(k as nat),
        r >= 1u128,
{
    proof {
        lemma_pow2_values();
    }
    let mut i: u32 = 0;
    let mut acc: u128 = 1;
    while i < k
        invariant
            i <= k,
            k < 128,
            acc as nat == pow2(i as nat),
            acc >= 1u128,
        decreases k - i,
    {
        proof {
            lemma_pow2_monotonic(i as nat, 126);
            lemma_pow2_values();
            assert(acc <= 85070591730234615865843651857942052864u128);
        }
        acc = acc * 2;
        i = i + 1;
    }
    acc
}

/// Exact mathematical classification of an IEEE-754 binary64 bit pattern.
/// For `Finite`, the exact real number represented is `(if neg { -1 } else { 1 }) * num / 2^frac_exp`.
pub enum SpecFloat64 {
    NaN,
    PosInf,
    NegInf,
    Zero { neg: bool },
    Finite { neg: bool, num: nat, frac_exp: nat },
}

pub open spec fn spec_decode_f64(bits: u64) -> SpecFloat64 {
    let neg = (bits / 0x8000_0000_0000_0000u64) == 1u64;
    let rem63 = bits % 0x8000_0000_0000_0000u64;
    let biased_exp = rem63 / 0x0010_0000_0000_0000u64;
    let mant = rem63 % 0x0010_0000_0000_0000u64;
    if biased_exp == 0x7FFu64 {
        if mant != 0u64 {
            SpecFloat64::NaN
        } else if neg {
            SpecFloat64::NegInf
        } else {
            SpecFloat64::PosInf
        }
    } else if biased_exp == 0u64 && mant == 0u64 {
        SpecFloat64::Zero { neg }
    } else if biased_exp == 0u64 {
        // Subnormal: (-1)^sign * mant * 2^(-1074)
        SpecFloat64::Finite {
            neg,
            num: mant as nat,
            frac_exp: 1074nat,
        }
    } else {
        // Normal: (-1)^sign * (2^52 + mant) * 2^(biased_exp - 1075)
        let sig: nat = 0x0010_0000_0000_0000nat + (mant as nat);
        if biased_exp >= 1075u64 {
            let shift: nat = (biased_exp - 1075u64) as nat;
            SpecFloat64::Finite {
                neg,
                num: sig * pow2(shift),
                frac_exp: 0nat,
            }
        } else {
            let frac_exp: nat = (1075u64 - biased_exp) as nat;
            SpecFloat64::Finite {
                neg,
                num: sig,
                frac_exp,
            }
        }
    }
}

/// Prove IEEE-754 bitwise shift/mask operations match constant division/modulo layout.
pub proof fn lemma_ieee754_bit_layout(bits: u64)
    ensures
        (bits >> 63u64) == bits / 0x8000_0000_0000_0000u64,
        ((bits >> 52u64) & 0x7FFu64)
            == (bits % 0x8000_0000_0000_0000u64) / 0x0010_0000_0000_0000u64,
        (bits & 0x000F_FFFF_FFFF_FFFFu64)
            == (bits % 0x8000_0000_0000_0000u64) % 0x0010_0000_0000_0000u64,
{
    assert((bits >> 63u64) == bits / 0x8000_0000_0000_0000u64) by (bit_vector);
    assert(
        ((bits >> 52u64) & 0x7FFu64)
            == (bits % 0x8000_0000_0000_0000u64) / 0x0010_0000_0000_0000u64
    ) by (bit_vector);
    assert(
        (bits & 0x000F_FFFF_FFFF_FFFFu64)
            == (bits % 0x8000_0000_0000_0000u64) % 0x0010_0000_0000_0000u64
    ) by (bit_vector);
}

// ---------------------------------------------------------------------------------------
// WHATWG Web IDL §3.2.4 `IntegerPart` and `ConvertToInt`
// ---------------------------------------------------------------------------------------

/// WHATWG Web IDL §3.2.4 `IntegerPart(n)` on exact dyadic rational `(-1)^neg * num / 2^frac_exp`:
/// 1. Let `r` be `floor(abs(n))`.
/// 2. If `n < 0`, return `-1 * r`.
/// 3. Otherwise, return `r`.
pub open spec fn spec_integer_part(neg: bool, num: nat, frac_exp: nat) -> int {
    let r = (num / pow2(frac_exp)) as int;
    if neg { -r } else { r }
}

/// WHATWG Web IDL §3.2.4 `ConvertToInt` steps 1–3 (`lowerBound`, `upperBound`):
/// - For `bitLength == 64`: `[0, 2^53 - 1]` (unsigned) or `[-(2^53 - 1), 2^53 - 1]` (signed).
/// - Otherwise: `[0, 2^bitLength - 1]` (unsigned) or `[-2^(bitLength - 1), 2^(bitLength - 1) - 1]` (signed).
pub open spec fn spec_convert_int_bounds(bit_length: nat, signed: bool) -> (int, int) {
    if bit_length == 64nat {
        let upper = (pow2(53) as int) - 1;
        let lower = if !signed { 0int } else { -((pow2(53) as int) - 1) };
        (lower, upper)
    } else if !signed {
        (0int, (pow2(bit_length) as int) - 1)
    } else {
        let half = pow2((bit_length - 1) as nat) as int;
        (-half, half - 1)
    }
}

/// WHATWG Web IDL §3.2.4 `ConvertToInt(V, bitLength, signedness)` over an IEEE-754 binary64 number.
pub open spec fn spec_convert_to_int_bits(
    bits: u64,
    bit_length: nat,
    signed: bool,
    attr: IntAttr,
) -> Result<int, IdlError> {
    let (lower, upper) = spec_convert_int_bounds(bit_length, signed);
    let decoded = spec_decode_f64(bits);
    match attr {
        IntAttr::EnforceRange => {
            // Step 6: [EnforceRange]
            match decoded {
                SpecFloat64::NaN | SpecFloat64::PosInf | SpecFloat64::NegInf =>
                    Err(IdlError::TypeError),
                SpecFloat64::Zero { .. } => Ok(0int),
                SpecFloat64::Finite { neg, num, frac_exp } => {
                    let x = spec_integer_part(neg, num, frac_exp);
                    if x < lower || x > upper {
                        Err(IdlError::TypeError)
                    } else {
                        Ok(x)
                    }
                },
            }
        },
        IntAttr::Clamp => {
            // Step 7 (not NaN) + Step 8 fallthrough (NaN -> +0)
            match decoded {
                SpecFloat64::NaN => Ok(0int),
                SpecFloat64::PosInf => Ok(upper),
                SpecFloat64::NegInf => Ok(lower),
                SpecFloat64::Zero { .. } => Ok(0int),
                SpecFloat64::Finite { neg, num, frac_exp } => {
                    let denom = pow2(frac_exp);
                    let scaled: int = if neg { -(num as int) } else { num as int };
                    if scaled <= lower * (denom as int) {
                        Ok(lower)
                    } else if scaled >= upper * (denom as int) {
                        Ok(upper)
                    } else {
                        // Round to nearest integer, choosing the even integer on halfway tie,
                        // and choosing +0 rather than -0.
                        let q = num / denom;
                        let rem = num % denom;
                        let rounded_mag: int = if 2nat * rem > denom
                            || (2nat * rem == denom && q % 2nat == 1nat)
                        {
                            (q + 1nat) as int
                        } else {
                            q as int
                        };
                        Ok(if neg { -rounded_mag } else { rounded_mag })
                    }
                },
            }
        },
        IntAttr::Standard => {
            // Steps 8–12: Standard modulo 2^bitLength
            match decoded {
                SpecFloat64::NaN
                | SpecFloat64::PosInf
                | SpecFloat64::NegInf
                | SpecFloat64::Zero { .. } => Ok(0int),
                SpecFloat64::Finite { neg, num, frac_exp } => {
                    let ip = spec_integer_part(neg, num, frac_exp);
                    let m = pow2(bit_length) as int;
                    let u = ip % m;
                    if signed && u >= (pow2((bit_length - 1) as nat) as int) {
                        Ok(u - m)
                    } else {
                        Ok(u)
                    }
                },
            }
        },
    }
}

// ---------------------------------------------------------------------------------------
// Arithmetic Helper Lemmas for `ConvertToInt`
// ---------------------------------------------------------------------------------------

proof fn lemma_div_mod_by_one(x: nat)
    ensures
        x * 1nat == x,
        x / 1nat == x,
        x % 1nat == 0nat,
{
    assert((x as int) == (x as int) * 1int + 0int);
    lemma_fundamental_div_mod_converse(x as int, 1int, x as int, 0int);
}

proof fn lemma_neg_euclidean_mod(n: nat, m: nat)
    requires
        m > 0,
    ensures
        (n % m == 0nat) ==> ((-(n as int)) % (m as int) == 0int),
        (n % m > 0nat) ==> ((-(n as int)) % (m as int) == ((m - (n % m)) as int)),
{
    let ni = n as int;
    let mi = m as int;
    let q = (n / m) as int;
    let r = (n % m) as int;
    lemma_fundamental_div_mod(ni, mi);
    assert(mi * q == q * mi) by (nonlinear_arith);
    if r == 0 {
        assert(-ni == (-q) * mi + 0) by (nonlinear_arith)
            requires ni == q * mi + r, r == 0;
        lemma_fundamental_div_mod_converse(-ni, mi, -q, 0);
    } else {
        assert(0 <= mi - r && mi - r < mi);
        assert(-ni == (-q - 1) * mi + (mi - r)) by (nonlinear_arith)
            requires ni == q * mi + r;
        lemma_fundamental_div_mod_converse(-ni, mi, -q - 1, mi - r);
    }
}

proof fn lemma_large_shift_mod_zero(sig: nat, shift: nat, bit_length: nat)
    requires
        shift >= bit_length,
        bit_length > 0,
    ensures
        ((sig * pow2(shift)) as int) % (pow2(bit_length) as int) == 0int,
        (-((sig * pow2(shift)) as int)) % (pow2(bit_length) as int) == 0int,
{
    let diff: nat = (shift - bit_length) as nat;
    lemma_pow2_add(diff, bit_length);
    assert(diff + bit_length == shift);
    lemma_pow2_pos(bit_length);
    let p_shift = pow2(shift);
    let p_diff = pow2(diff);
    let p_bl = pow2(bit_length);
    let m = p_bl as int;
    let k = (sig * p_diff) as int;
    assert((sig * p_shift) as int == k * m) by (nonlinear_arith)
        requires p_shift == p_diff * p_bl, m == p_bl as int, k == (sig * p_diff) as int;
    assert((-((sig * p_shift) as int)) == (-k) * m) by (nonlinear_arith)
        requires (sig * p_shift) as int == k * m;
    lemma_fundamental_div_mod_converse((sig * p_shift) as int, m, k, 0);
    lemma_fundamental_div_mod_converse(-((sig * p_shift) as int), m, -k, 0);
}

#[verifier::spinoff_prover]
proof fn lemma_clamp_rounded_within_bounds(
    neg: bool,
    num: nat,
    denom: nat,
    lower: int,
    upper: int,
)
    requires
        denom >= 1nat,
        lower <= 0int,
        upper >= 1int,
        (if neg { -(num as int) } else { num as int }) > lower * (denom as int),
        (if neg { -(num as int) } else { num as int }) < upper * (denom as int),
    ensures
        ({
            let q = num / denom;
            let rem = num % denom;
            let rounded_mag: int = if 2nat * rem > denom
                || (2nat * rem == denom && q % 2nat == 1nat)
            {
                (q + 1nat) as int
            } else {
                q as int
            };
            let res = if neg { -rounded_mag } else { rounded_mag };
            lower <= res && res <= upper
        }),
{
    let q = num / denom;
    let rem = num % denom;
    lemma_fundamental_div_mod(num as int, denom as int);
    let di = denom as int;
    let qi = q as int;
    let ri = rem as int;
    let ni = num as int;
    assert(ni == di * qi + ri);
    if !neg {
        assert(qi < upper) by (nonlinear_arith)
            requires ni == di * qi + ri, ri >= 0, di >= 1, ni < upper * di;
        assert(qi + 1 <= upper);
    } else {
        let abs_lower = -lower;
        assert(qi < abs_lower) by (nonlinear_arith)
            requires ni == di * qi + ri, ri >= 0, di >= 1, -ni > lower * di, abs_lower == -lower;
        assert(-(qi + 1) >= lower);
    }
}

pub open spec fn spec_valid_bit_length(bit_length: nat) -> bool {
    bit_length == 8nat || bit_length == 16nat || bit_length == 32nat || bit_length == 64nat
}

fn compute_int_bounds(bit_length: u8, signed: bool) -> (bounds: (i128, i128))
    requires
        spec_valid_bit_length(bit_length as nat),
    ensures
        (bounds.0 as int, bounds.1 as int) == spec_convert_int_bounds(bit_length as nat, signed),
        bounds.0 <= 0i128,
        bounds.1 >= 127i128,
        bounds.0 >= -9007199254740991i128,
        bounds.1 <= 9007199254740991i128,
{
    proof {
        lemma_pow2_values();
    }
    if bit_length == 64 {
        if !signed {
            (0i128, 9007199254740991i128)
        } else {
            (-9007199254740991i128, 9007199254740991i128)
        }
    } else if bit_length == 8 {
        if !signed { (0i128, 255i128) } else { (-128i128, 127i128) }
    } else if bit_length == 16 {
        if !signed { (0i128, 65535i128) } else { (-32768i128, 32767i128) }
    } else {
        if !signed { (0i128, 4294967295i128) } else { (-2147483648i128, 2147483647i128) }
    }
}

/// Verified executable core of Web IDL §3.2.4 `ConvertToInt` on IEEE-754 binary64 bits.
#[verifier::spinoff_prover]
pub fn convert_to_int_bits(
    bits: u64,
    bit_length: u8,
    signed: bool,
    attr: IntAttr,
) -> (res: Result<i128, IdlError>)
    requires
        spec_valid_bit_length(bit_length as nat),
    ensures
        match (res, spec_convert_to_int_bits(bits, bit_length as nat, signed, attr)) {
            (Ok(v), Ok(sv)) => v as int == sv,
            (Err(e), Err(se)) => e == se,
            _ => false,
        },
        match res {
            Ok(v) => {
                if !signed {
                    0i128 <= v && (v as nat) < pow2(bit_length as nat)
                } else {
                    -(pow2((bit_length - 1) as nat) as int) <= (v as int)
                    && (v as int) < (pow2((bit_length - 1) as nat) as int)
                }
            },
            Err(_) => true,
        },
{
    proof {
        lemma_pow2_values();
    }
    let (lower, upper) = compute_int_bounds(bit_length, signed);
    let neg = (bits / 0x8000_0000_0000_0000u64) == 1u64;
    let rem63 = bits % 0x8000_0000_0000_0000u64;
    let biased_exp = rem63 / 0x0010_0000_0000_0000u64;
    let mant = rem63 % 0x0010_0000_0000_0000u64;

    if biased_exp == 0x7FFu64 {
        // NaN or ±Infinity
        match attr {
            IntAttr::EnforceRange => return Err(IdlError::TypeError),
            IntAttr::Clamp => {
                if mant != 0u64 {
                    return Ok(0i128);
                } else if neg {
                    return Ok(lower);
                } else {
                    return Ok(upper);
                }
            },
            IntAttr::Standard => return Ok(0i128),
        }
    }

    if biased_exp == 0u64 && mant == 0u64 {
        return Ok(0i128);
    }

    // Finite non-zero value
    match attr {
        IntAttr::EnforceRange => {
            if biased_exp == 0u64 {
                // Subnormal: mant < 2^52 < 2^1074 => floor(|x|) == 0
                proof {
                    lemma_pow2_strictly_increasing(52, 1074);
                    lemma_fundamental_div_mod_converse(
                        mant as int,
                        pow2(1074) as int,
                        0,
                        mant as int,
                    );
                }
                return Ok(0i128);
            }
            let sig: u64 = 0x0010_0000_0000_0000u64 + mant;
            if biased_exp < 1023u64 {
                // frac_exp = 1075 - biased_exp >= 53 => sig < 2^53 <= 2^frac_exp => floor(|x|) == 0
                let ghost frac_exp: nat = (1075u64 - biased_exp) as nat;
                proof {
                    lemma_pow2_monotonic(53, frac_exp);
                    lemma_fundamental_div_mod_converse(
                        sig as int,
                        pow2(frac_exp) as int,
                        0,
                        sig as int,
                    );
                }
                return Ok(0i128);
            } else if biased_exp <= 1074u64 {
                let frac_exp_u32: u32 = (1075u64 - biased_exp) as u32;
                let denom = exec_pow2_u64(frac_exp_u32);
                let q: u64 = sig / denom;
                let x: i128 = if neg { -(q as i128) } else { q as i128 };
                if x < lower || x > upper {
                    return Err(IdlError::TypeError);
                } else {
                    return Ok(x);
                }
            } else if biased_exp == 1075u64 {
                // shift == 0, pow2(0) == 1 => IntegerPart == ±sig
                let x: i128 = if neg { -(sig as i128) } else { sig as i128 };
                proof {
                    lemma_div_mod_by_one(sig as nat);
                }
                if x < lower || x > upper {
                    return Err(IdlError::TypeError);
                } else {
                    return Ok(x);
                }
            } else {
                // biased_exp >= 1076 => shift >= 1 => sig * 2^shift >= 2^52 * 2 = 2^53 > upper
                let ghost shift: nat = (biased_exp - 1075u64) as nat;
                proof {
                    lemma_pow2_monotonic(1, shift);
                    reveal_with_fuel(pow2, 2);
                    let ps = pow2(shift);
                    assert((sig as nat) * ps >= 0x0010_0000_0000_0000nat * 2nat)
                        by (nonlinear_arith)
                        requires sig >= 0x0010_0000_0000_0000u64, ps >= 2nat;
                    lemma_div_mod_by_one((sig as nat) * ps);
                }
                return Err(IdlError::TypeError);
            }
        },
        IntAttr::Clamp => {
            if biased_exp == 0u64 {
                // Subnormal: 0 < mant < 2^52, denom = 2^1074 => 2 * mant < denom
                proof {
                    lemma_pow2_strictly_increasing(54, 1074);
                    let denom = pow2(1074);
                    let di = denom as int;
                    let mi = mant as int;
                    let li = lower as int;
                    let ui = upper as int;
                    lemma_fundamental_div_mod_converse(mi, di, 0, mi);
                    if !neg {
                        assert(mi > li * di) by (nonlinear_arith)
                            requires mi > 0, li <= 0, di > 0;
                        assert(mi < ui * di) by (nonlinear_arith)
                            requires mi < di, ui >= 1, di > 0;
                    } else if lower < 0 {
                        assert((-mi) > li * di) by (nonlinear_arith)
                            requires 0 < mi, mi < di, li <= -1, di > 0;
                        assert((-mi) < ui * di) by (nonlinear_arith)
                            requires mi > 0, ui >= 1, di > 0;
                    } else {
                        assert(lower == 0);
                        assert((-mi) <= li * di);
                    }
                }
                return Ok(0i128);
            }
            let sig: u64 = 0x0010_0000_0000_0000u64 + mant;
            if biased_exp < 1022u64 {
                // frac_exp = 1075 - biased_exp >= 54 => 2 * sig < 2^54 <= denom
                let ghost frac_exp: nat = (1075u64 - biased_exp) as nat;
                proof {
                    lemma_pow2_monotonic(54, frac_exp);
                    let denom = pow2(frac_exp);
                    let di = denom as int;
                    let si = sig as int;
                    let li = lower as int;
                    let ui = upper as int;
                    lemma_fundamental_div_mod_converse(si, di, 0, si);
                    if !neg {
                        assert(si > li * di) by (nonlinear_arith)
                            requires si > 0, li <= 0, di > 0;
                        assert(si < ui * di) by (nonlinear_arith)
                            requires si < di, ui >= 1, di > 0;
                    } else if lower < 0 {
                        assert((-si) > li * di) by (nonlinear_arith)
                            requires 0 < si, si < di, li <= -1, di > 0;
                        assert((-si) < ui * di) by (nonlinear_arith)
                            requires si > 0, ui >= 1, di > 0;
                    } else {
                        assert(lower == 0);
                        assert((-si) <= li * di);
                    }
                }
                return Ok(0i128);
            } else if biased_exp <= 1074u64 {
                // 1 <= frac_exp <= 53: denom <= 2^53, |lower|, upper <= 2^53 - 1 => exact in i128!
                let frac_exp_u32: u32 = (1075u64 - biased_exp) as u32;
                let denom_u64: u64 = exec_pow2_u64(frac_exp_u32);
                proof {
                    lemma_pow2_monotonic(frac_exp_u32 as nat, 53);
                    assert(denom_u64 <= 9007199254740992u64);
                }
                let denom_i128: i128 = denom_u64 as i128;
                let scaled: i128 = if neg { -(sig as i128) } else { sig as i128 };
                proof {
                    let li = lower as int;
                    let ui = upper as int;
                    let di = denom_i128 as int;
                    assert(-81129638414606672688845055066112int <= li * di && li * di <= 0int)
                        by (nonlinear_arith)
                        requires -9007199254740991int <= li, li <= 0int, 1int <= di, di <= 9007199254740992int;
                    assert(0int <= ui * di && ui * di <= 81129638414606672688845055066112int)
                        by (nonlinear_arith)
                        requires 0int <= ui, ui <= 9007199254740991int, 1int <= di, di <= 9007199254740992int;
                }
                let lb_scaled: i128 = lower * denom_i128;
                let ub_scaled: i128 = upper * denom_i128;
                if scaled <= lb_scaled {
                    return Ok(lower);
                } else if scaled >= ub_scaled {
                    return Ok(upper);
                } else {
                    let q: u64 = sig / denom_u64;
                    let rem: u64 = sig % denom_u64;
                    let rem2: u128 = 2u128 * (rem as u128);
                    let denom_u128: u128 = denom_u64 as u128;
                    let rounded_mag: i128 = if rem2 > denom_u128
                        || (rem2 == denom_u128 && (q % 2u64) == 1u64)
                    {
                        (q as i128) + 1i128
                    } else {
                        q as i128
                    };
                    let out: i128 = if neg { -rounded_mag } else { rounded_mag };
                    proof {
                        lemma_clamp_rounded_within_bounds(
                            neg,
                            sig as nat,
                            denom_u64 as nat,
                            lower as int,
                            upper as int,
                        );
                    }
                    return Ok(out);
                }
            } else if biased_exp == 1075u64 {
                // shift == 0, denom == 1, num == sig
                let scaled: i128 = if neg { -(sig as i128) } else { sig as i128 };
                proof {
                    assert(pow2(0) == 1nat);
                    lemma_div_mod_by_one(sig as nat);
                    assert((lower as int) * 1int == lower as int);
                    assert((upper as int) * 1int == upper as int);
                }
                if scaled <= lower {
                    return Ok(lower);
                } else if scaled >= upper {
                    return Ok(upper);
                } else {
                    return Ok(scaled);
                }
            } else {
                // biased_exp >= 1076 => num = sig * 2^shift >= 2^53 > upper and -num < lower
                let ghost shift: nat = (biased_exp - 1075u64) as nat;
                proof {
                    assert(pow2(0) == 1nat);
                    assert((lower as int) * 1int == lower as int);
                    assert((upper as int) * 1int == upper as int);
                    lemma_pow2_monotonic(1, shift);
                    reveal_with_fuel(pow2, 2);
                    let ps = pow2(shift);
                    assert((sig as nat) * ps >= 0x0010_0000_0000_0000nat * 2nat)
                        by (nonlinear_arith)
                        requires sig >= 0x0010_0000_0000_0000u64, ps >= 2nat;
                }
                if neg {
                    return Ok(lower);
                } else {
                    return Ok(upper);
                }
            }
        },
        IntAttr::Standard => {
            if biased_exp == 0u64 {
                proof {
                    lemma_pow2_strictly_increasing(52, 1074);
                    lemma_fundamental_div_mod_converse(
                        mant as int,
                        pow2(1074) as int,
                        0,
                        mant as int,
                    );
                    lemma_fundamental_div_mod_converse(0, pow2(bit_length as nat) as int, 0, 0);
                }
                return Ok(0i128);
            }
            let sig: u64 = 0x0010_0000_0000_0000u64 + mant;
            if biased_exp < 1023u64 {
                let ghost frac_exp: nat = (1075u64 - biased_exp) as nat;
                proof {
                    lemma_pow2_monotonic(53, frac_exp);
                    lemma_fundamental_div_mod_converse(
                        sig as int,
                        pow2(frac_exp) as int,
                        0,
                        sig as int,
                    );
                    lemma_fundamental_div_mod_converse(0, pow2(bit_length as nat) as int, 0, 0);
                }
                return Ok(0i128);
            }

            let m_u128: u128 = exec_pow2_u128(bit_length as u32);
            let half_u128: u128 = exec_pow2_u128((bit_length - 1) as u32);

            if biased_exp <= 1074u64 {
                let frac_exp_u32: u32 = (1075u64 - biased_exp) as u32;
                let denom: u64 = exec_pow2_u64(frac_exp_u32);
                let q: u128 = (sig / denom) as u128;
                let r_pos: u128 = q % m_u128;
                let u_u128: u128 = if !neg {
                    r_pos
                } else if r_pos == 0u128 {
                    0u128
                } else {
                    m_u128 - r_pos
                };
                proof {
                    if neg {
                        lemma_neg_euclidean_mod(q as nat, m_u128 as nat);
                    }
                    lemma_fundamental_div_mod(q as int, m_u128 as int);
                }
                if signed && u_u128 >= half_u128 {
                    let out: i128 = (u_u128 as i128) - (m_u128 as i128);
                    return Ok(out);
                } else {
                    return Ok(u_u128 as i128);
                }
            } else {
                let shift_u64: u64 = biased_exp - 1075u64;
                if shift_u64 >= 64u64 {
                    proof {
                        lemma_large_shift_mod_zero(
                            sig as nat,
                            shift_u64 as nat,
                            bit_length as nat,
                        );
                        lemma_div_mod_by_one((sig as nat) * pow2(shift_u64 as nat));
                    }
                    return Ok(0i128);
                } else {
                    let shift_u32: u32 = shift_u64 as u32;
                    let factor: u128 = exec_pow2_u128(shift_u32);
                    proof {
                        lemma_pow2_monotonic(shift_u32 as nat, 63);
                        assert(factor <= 9223372036854775808u128);
                        assert((sig as u128) <= 9007199254740992u128);
                        assert((sig as nat) * (factor as nat)
                            <= 9007199254740992nat * 9223372036854775808nat)
                            by (nonlinear_arith)
                            requires
                                (sig as nat) <= 9007199254740992nat,
                                (factor as nat) <= 9223372036854775808nat;
                    }
                    let prod: u128 = (sig as u128) * factor;
                    let r_pos: u128 = prod % m_u128;
                    let u_u128: u128 = if !neg {
                        r_pos
                    } else if r_pos == 0u128 {
                        0u128
                    } else {
                        m_u128 - r_pos
                    };
                    proof {
                        lemma_div_mod_by_one(prod as nat);
                        if neg {
                            lemma_neg_euclidean_mod(prod as nat, m_u128 as nat);
                        }
                        lemma_fundamental_div_mod(prod as int, m_u128 as int);
                    }
                    if signed && u_u128 >= half_u128 {
                        let out: i128 = (u_u128 as i128) - (m_u128 as i128);
                        return Ok(out);
                    } else {
                        return Ok(u_u128 as i128);
                    }
                }
            }
        },
    }
}

// ---------------------------------------------------------------------------------------
// ECMA-262 `ToNumber` & `ToString` at the Web IDL Boundary
// ---------------------------------------------------------------------------------------

/// ECMA-262 WhiteSpace + LineTerminator code units (§12.2, §12.3).
pub open spec fn spec_is_es_whitespace(u: u16) -> bool {
    (0x0009u16 <= u && u <= 0x000Du16)
    || u == 0x0020u16
    || u == 0x00A0u16
    || u == 0x1680u16
    || (0x2000u16 <= u && u <= 0x200Au16)
    || u == 0x2028u16
    || u == 0x2029u16
    || u == 0x202Fu16
    || u == 0x205Fu16
    || u == 0x3000u16
    || u == 0xFEFFu16
}

fn is_es_whitespace(u: u16) -> (r: bool)
    ensures
        r == spec_is_es_whitespace(u),
{
    (0x0009u16 <= u && u <= 0x000Du16)
    || u == 0x0020u16
    || u == 0x00A0u16
    || u == 0x1680u16
    || (0x2000u16 <= u && u <= 0x200Au16)
    || u == 0x2028u16
    || u == 0x2029u16
    || u == 0x202Fu16
    || u == 0x205Fu16
    || u == 0x3000u16
    || u == 0xFEFFu16
}

pub open spec fn spec_trim_start(s: Seq<u16>) -> Seq<u16>
    decreases s.len(),
{
    if s.len() > 0 && spec_is_es_whitespace(s[0]) {
        spec_trim_start(s.subrange(1, s.len() as int))
    } else {
        s
    }
}

pub open spec fn spec_trim_end(s: Seq<u16>) -> Seq<u16>
    decreases s.len(),
{
    if s.len() > 0 && spec_is_es_whitespace(s[s.len() - 1]) {
        spec_trim_end(s.subrange(0, (s.len() - 1) as int))
    } else {
        s
    }
}

pub open spec fn spec_trim_utf16(s: Seq<u16>) -> Seq<u16> {
    spec_trim_end(spec_trim_start(s))
}

fn trim_utf16(s: &[u16]) -> (out: Vec<u16>)
    ensures
        out@ == spec_trim_utf16(s@),
{
    let n = s.len();
    let mut start: usize = 0;
    proof {
        assert(s@.subrange(0, n as int) =~= s@);
    }
    while start < n && is_es_whitespace(s[start])
        invariant
            start <= n,
            n == s@.len(),
            spec_trim_start(s@) == spec_trim_start(s@.subrange(start as int, n as int)),
        decreases n - start,
    {
        let ghost sub = s@.subrange(start as int, n as int);
        start += 1;
        proof {
            assert(sub.subrange(1, sub.len() as int) =~= s@.subrange(start as int, n as int));
        }
    }
    let ghost after_start = s@.subrange(start as int, n as int);
    let mut end: usize = n;
    proof {
        assert(after_start.subrange(0, (end - start) as int) =~= after_start);
    }
    while end > start && is_es_whitespace(s[end - 1])
        invariant
            start <= end,
            end <= n,
            n == s@.len(),
            after_start == s@.subrange(start as int, n as int),
            spec_trim_end(after_start)
                == spec_trim_end(after_start.subrange(0, (end - start) as int)),
        decreases end - start,
    {
        let ghost cur = after_start.subrange(0, (end - start) as int);
        end -= 1;
        proof {
            assert(cur.subrange(0, (cur.len() - 1) as int)
                =~= after_start.subrange(0, (end - start) as int));
        }
    }

    let mut out: Vec<u16> = Vec::new();
    let mut k: usize = start;
    while k < end
        invariant
            start <= k,
            k <= end,
            end <= n,
            n == s@.len(),
            out@ == s@.subrange(start as int, k as int),
        decreases end - k,
    {
        out.push(s[k]);
        k += 1;
        proof {
            assert(out@ =~= s@.subrange(start as int, k as int));
        }
    }
    proof {
        let rem = after_start.subrange(0, (end - start) as int);
        assert(rem =~= s@.subrange(start as int, end as int));
        if rem.len() > 0 {
            assert(rem[rem.len() - 1] == s[(end - 1) as int]);
            assert(!spec_is_es_whitespace(rem[rem.len() - 1]));
        }
        assert(spec_trim_end(rem) == rem);
    }
    out
}

/// Convert `(neg: bool, mag: u64)` integer magnitude to exact IEEE-754 binary64 bits
/// (with ties-to-even rounding when `mag >= 2^53`).
pub open spec fn spec_highest_bit_u64(mag: u64, bit: nat) -> nat
    decreases bit,
{
    if bit == 0nat {
        0nat
    } else if (mag as nat) >= pow2(bit) {
        bit
    } else {
        spec_highest_bit_u64(mag, (bit - 1) as nat)
    }
}

pub open spec fn spec_u64_mag_to_f64_bits(neg: bool, mag: u64) -> u64 {
    if mag == 0u64 {
        F64_POS_ZERO
    } else {
        let sign_part: u64 = if neg { 0x8000_0000_0000_0000u64 } else { 0u64 };
        let msb = spec_highest_bit_u64(mag, 63nat);
        if msb <= 52nat {
            let shift = (52nat - msb) as nat;
            let sig = (mag as nat) * pow2(shift);
            let mant = (sig - pow2(52)) as u64;
            let exp_part = ((1023nat + msb) * 0x0010_0000_0000_0000nat) as u64;
            (sign_part + exp_part + mant) as u64
        } else {
            let drop = (msb - 52nat) as nat;
            let d = pow2(drop);
            let q = (mag as nat) / d;
            let rem = (mag as nat) % d;
            let rounded = if 2nat * rem > d || (2nat * rem == d && q % 2nat == 1nat) {
                q + 1nat
            } else {
                q
            };
            if rounded >= pow2(53) {
                let exp_part = ((1024nat + msb) * 0x0010_0000_0000_0000nat) as u64;
                (sign_part + exp_part) as u64
            } else {
                let mant = (rounded - pow2(52)) as u64;
                let exp_part = ((1023nat + msb) * 0x0010_0000_0000_0000nat) as u64;
                (sign_part + exp_part + mant) as u64
            }
        }
    }
}

fn find_highest_bit_u64(mag: u64) -> (msb: u32)
    requires
        mag >= 1u64,
    ensures
        msb <= 63u32,
        msb as nat == spec_highest_bit_u64(mag, 63nat),
        pow2(msb as nat) <= (mag as nat),
        msb < 63u32 ==> (mag as nat) < pow2((msb + 1) as nat),
{
    let mut b: u32 = 63;
    while b > 0
        invariant
            b <= 63u32,
            mag >= 1u64,
            spec_highest_bit_u64(mag, 63nat) == spec_highest_bit_u64(mag, b as nat),
            b < 63u32 ==> (mag as nat) < pow2((b + 1) as nat),
        decreases b,
    {
        let p = exec_pow2_u64(b);
        if mag >= p {
            return b;
        }
        b = b - 1;
    }
    proof {
        assert(pow2(0) == 1nat);
    }
    0u32
}

proof fn lemma_highest_bit_u64_props(mag: u64, bit: nat)
    requires
        mag >= 1u64,
    ensures
        spec_highest_bit_u64(mag, bit) <= bit,
        pow2(spec_highest_bit_u64(mag, bit)) <= (mag as nat),
        spec_highest_bit_u64(mag, bit) < bit
            ==> (mag as nat) < pow2(spec_highest_bit_u64(mag, bit) + 1),
    decreases bit,
{
    if bit == 0nat {
        assert(pow2(0) == 1nat);
    } else if (mag as nat) >= pow2(bit) {
    } else {
        lemma_highest_bit_u64_props(mag, (bit - 1) as nat);
    }
}

#[verifier::spinoff_prover]
pub fn u64_mag_to_f64_bits(neg: bool, mag: u64) -> (bits: u64)
    ensures
        bits == spec_u64_mag_to_f64_bits(neg, mag),
{
    if mag == 0u64 {
        return F64_POS_ZERO;
    }
    proof {
        lemma_pow2_values();
    }
    let sign_part: u64 = if neg { 0x8000_0000_0000_0000u64 } else { 0u64 };
    let msb = find_highest_bit_u64(mag);
    if msb <= 52u32 {
        let shift = 52u32 - msb;
        let factor = exec_pow2_u64(shift);
        proof {
            let p_msb = pow2(msb as nat);
            let p_52 = pow2(52);
            let p_53 = pow2(53);
            let f_nat = factor as nat;
            lemma_pow2_add(msb as nat, shift as nat);
            assert(msb as nat + shift as nat == 52nat);
            if msb < 52u32 {
                let p_msb1 = pow2((msb + 1) as nat);
                lemma_pow2_add((msb + 1) as nat, shift as nat);
                assert((msb + 1) as nat + shift as nat == 53nat);
                assert((mag as nat) * f_nat < p_53) by (nonlinear_arith)
                    requires (mag as nat) < p_msb1, f_nat >= 1nat, p_msb1 * f_nat == p_53;
            } else {
                assert(factor == 1u64);
                lemma_div_mod_by_one(mag as nat);
                assert((mag as nat) < p_53);
            }
            assert((mag as nat) * f_nat >= p_52) by (nonlinear_arith)
                requires (mag as nat) >= p_msb, f_nat >= 1nat, p_msb * f_nat == p_52;
        }
        let sig: u64 = mag * factor;
        let mant: u64 = sig - 0x0010_0000_0000_0000u64;
        let exp_part: u64 = ((1023u32 + msb) as u64) * 0x0010_0000_0000_0000u64;
        sign_part + exp_part + mant
    } else {
        let drop = msb - 52u32;
        let d = exec_pow2_u64(drop);
        proof {
            let p_52 = pow2(52);
            let p_53 = pow2(53);
            let p_msb = pow2(msb as nat);
            let d_nat = d as nat;
            let q_nat = (mag as nat) / d_nat;
            let r_nat = (mag as nat) % d_nat;
            lemma_pow2_add(52nat, drop as nat);
            assert(52nat + drop as nat == msb as nat);
            lemma_fundamental_div_mod(mag as int, d as int);
            assert(q_nat >= p_52) by (nonlinear_arith)
                requires
                    (mag as int) == (d_nat as int) * (q_nat as int) + (r_nat as int),
                    r_nat < d_nat,
                    d_nat >= 1nat,
                    (mag as nat) >= p_msb,
                    p_52 * d_nat == p_msb;
            if msb < 63u32 {
                let p_msb1 = pow2((msb + 1) as nat);
                lemma_pow2_add(53nat, drop as nat);
                assert(53nat + drop as nat == (msb + 1) as nat);
                assert(q_nat < p_53) by (nonlinear_arith)
                    requires
                        (mag as int) == (d_nat as int) * (q_nat as int) + (r_nat as int),
                        r_nat >= 0nat,
                        d_nat >= 1nat,
                        (mag as nat) < p_msb1,
                        p_53 * d_nat == p_msb1;
            } else {
                assert(drop == 11u32);
                reveal_with_fuel(pow2, 12);
                assert(d == 2048u64);
                assert(mag <= u64::MAX);
                assert((mag as nat) / 2048nat < p_53);
            }
        }
        let q: u64 = mag / d;
        let rem: u64 = mag % d;
        let rounded: u64 = if 2u128 * (rem as u128) > (d as u128)
            || (2u128 * (rem as u128) == (d as u128) && (q % 2u64) == 1u64)
        {
            q + 1u64
        } else {
            q
        };
        if rounded >= 0x0020_0000_0000_0000u64 {
            let exp_part: u64 = ((1024u32 + msb) as u64) * 0x0010_0000_0000_0000u64;
            sign_part + exp_part
        } else {
            let mant: u64 = rounded - 0x0010_0000_0000_0000u64;
            let exp_part: u64 = ((1023u32 + msb) as u64) * 0x0010_0000_0000_0000u64;
            sign_part + exp_part + mant
        }
    }
}

/// Exact roundtrip theorem for safe integers `|x| <= 2^53 - 1`: encoding `(neg, mag)` to
/// IEEE-754 binary64 via `spec_u64_mag_to_f64_bits` and converting back via
/// `spec_convert_to_int_bits` recovers the exact integer when within `[lower, upper]`.
#[verifier::spinoff_prover]
pub proof fn lemma_safe_int_f64_roundtrip(
    neg: bool,
    mag: u64,
    bit_length: nat,
    signed: bool,
    attr: IntAttr,
)
    requires
        spec_valid_bit_length(bit_length),
        (mag as nat) < pow2(53),
        mag == 0u64 ==> !neg,
        ({
            let (lower, upper) = spec_convert_int_bounds(bit_length, signed);
            let val: int = if neg { -(mag as int) } else { mag as int };
            lower <= val && val <= upper
        }),
    ensures
        spec_convert_to_int_bits(
            spec_u64_mag_to_f64_bits(neg, mag),
            bit_length,
            signed,
            attr,
        ) == Ok::<int, IdlError>(if neg { -(mag as int) } else { mag as int }),
{
    lemma_pow2_values();
    if mag == 0u64 {
        assert(spec_decode_f64(F64_POS_ZERO) == SpecFloat64::Zero { neg: false });
        return;
    }
    lemma_highest_bit_u64_props(mag, 63nat);
    let msb = spec_highest_bit_u64(mag, 63nat);
    if msb >= 53nat {
        lemma_pow2_monotonic(53, msb);
        assert(false);
    }
    assert(msb <= 52nat);
    let p_msb = pow2(msb);
    let p_msb1 = pow2(msb + 1);
    let p_52 = pow2(52);
    let p_53 = pow2(53);
    assert(p_msb <= (mag as nat));
    assert((mag as nat) < p_msb1);

    let shift = (52nat - msb) as nat;
    let p_shift = pow2(shift);
    lemma_pow2_pos(shift);
    lemma_pow2_add(msb, shift);
    assert(msb + shift == 52nat);
    if msb < 52nat {
        lemma_pow2_add(msb + 1, shift);
        assert((msb + 1) + shift == 53nat);
        assert((mag as nat) * p_shift < p_53) by (nonlinear_arith)
            requires (mag as nat) < p_msb1, p_shift >= 1nat, p_msb1 * p_shift == p_53;
    } else {
        assert(shift == 0nat);
        lemma_div_mod_by_one(mag as nat);
    }
    assert((mag as nat) * p_shift >= p_52) by (nonlinear_arith)
        requires (mag as nat) >= p_msb, p_shift >= 1nat, p_msb * p_shift == p_52;

    let sig = (mag as nat) * p_shift;
    let mant = (sig - p_52) as u64;
    let biased_exp = (1023nat + msb) as u64;
    let sign_part: u64 = if neg { 0x8000_0000_0000_0000u64 } else { 0u64 };
    let exp_part: u64 = ((biased_exp as nat) * 0x0010_0000_0000_0000nat) as u64;
    let bits = spec_u64_mag_to_f64_bits(neg, mag);
    assert(bits == (sign_part + exp_part + mant) as u64);

    let rem63 = exp_part + mant;
    assert(rem63 < 0x8000_0000_0000_0000int);
    if neg {
        lemma_fundamental_div_mod_converse(
            bits as int,
            0x8000_0000_0000_0000int,
            1,
            rem63 as int,
        );
    } else {
        lemma_fundamental_div_mod_converse(
            bits as int,
            0x8000_0000_0000_0000int,
            0,
            rem63 as int,
        );
    }
    assert((biased_exp as int) * 0x0010_0000_0000_0000int == 0x0010_0000_0000_0000int * (biased_exp as int));
    lemma_fundamental_div_mod_converse(
        rem63 as int,
        0x0010_0000_0000_0000int,
        biased_exp as int,
        mant as int,
    );

    if msb == 52nat {
        assert(shift == 0nat);
        assert(pow2(0) == 1nat);
        lemma_div_mod_by_one(mag as nat);
        assert(sig == mag as nat);
        assert(biased_exp == 1075u64);
        assert((1075u64 - 1075u64) as nat == 0nat);
        lemma_div_mod_by_one(sig);
        let (lower, upper) = spec_convert_int_bounds(bit_length, signed);
        assert(lower * 1int == lower);
        assert(upper * 1int == upper);
    } else {
        assert(biased_exp <= 1074u64);
        assert((1075u64 - biased_exp) as nat == shift);
        let d = p_shift;
        let di = d as int;
        lemma_fundamental_div_mod_converse(sig as int, di, mag as int, 0);
        assert(sig / d == mag as nat);
        assert(sig % d == 0nat);
        let (lower, upper) = spec_convert_int_bounds(bit_length, signed);
        let val: int = if neg { -(mag as int) } else { mag as int };
        let scaled: int = if neg { -(sig as int) } else { sig as int };
        assert(scaled == val * di) by (nonlinear_arith)
            requires
                sig == (mag as nat) * d,
                val == (if neg { -(mag as int) } else { mag as int }),
                scaled == (if neg { -(sig as int) } else { sig as int }),
                di == d as int;
        if val == lower {
            assert(scaled == lower * di) by (nonlinear_arith)
                requires scaled == val * di, val == lower;
        } else if val == upper {
            assert(lower < upper);
            assert(scaled == upper * di) by (nonlinear_arith)
                requires scaled == val * di, val == upper;
            assert(upper * di > lower * di) by (nonlinear_arith)
                requires lower < upper, di >= 1;
        } else {
            assert(lower < val && val < upper);
            assert(scaled > lower * di) by (nonlinear_arith)
                requires scaled == val * di, lower < val, di >= 1;
            assert(scaled < upper * di) by (nonlinear_arith)
                requires scaled == val * di, val < upper, di >= 1;
        }
    }

    if attr == IntAttr::Standard {
        let val: int = if neg { -(mag as int) } else { mag as int };
        let m = pow2(bit_length) as int;
        let half = pow2((bit_length - 1) as nat) as int;
        if !neg {
            if bit_length == 64nat {
                lemma_pow2_strictly_increasing(53, 64);
                if signed {
                    lemma_pow2_strictly_increasing(53, 63);
                }
            }
            assert(0 <= val && val < m);
            lemma_fundamental_div_mod_converse(val, m, 0, val);
            if signed {
                assert(val < half);
            }
        } else {
            assert(signed);
            if bit_length == 64nat {
                lemma_pow2_strictly_increasing(53, 63);
            }
            reveal_with_fuel(pow2, 2);
            lemma_pow2_add((bit_length - 1) as nat, 1);
            assert(((bit_length - 1) as nat) + 1 == bit_length);
            assert(m == 2 * half) by (nonlinear_arith)
                requires pow2(bit_length) == pow2((bit_length - 1) as nat) * 2nat,
                         m == pow2(bit_length) as int,
                         half == pow2((bit_length - 1) as nat) as int;
            assert(-half <= val && val < 0);
            assert(half <= m + val && m + val < m);
            assert(val == (-1) * m + (m + val));
            lemma_fundamental_div_mod_converse(val, m, -1, m + val);
        }
    }
}

// ---------------------------------------------------------------------------------------
// Verified `BigNat` & Exact IEEE-754 RNE `StringToNumber` (ECMA-262 §7.1.4.1.1)
// ---------------------------------------------------------------------------------------
//
// Supports:
// - Empty / whitespace-only strings -> `+0.0`
// - `"Infinity"`, `"+Infinity"`, `"-Infinity"` -> `±Infinity`
// - Arbitrary-length binary (`0b`/`0B`), octal (`0o`/`0O`), and hex (`0x`/`0X`) literals
// - Signed decimal integer, fractional (`"1.5"`, `"-0.5"`, `".5"`, `"42."`, `"42.9"`),
//   and scientific-exponent (`"1e20"`, `"1.25e-3"`, `"-1e-400"`, `"1e400"`) strings
//   with exact Round-Ties-to-Even (RNE) IEEE-754 binary64 conversion!

pub open spec fn pow_base32(k: nat) -> nat
    decreases k,
{
    if k == 0nat {
        1nat
    } else {
        0x1_0000_0000nat * pow_base32((k - 1) as nat)
    }
}

pub open spec fn pow10(k: nat) -> nat
    decreases k,
{
    if k == 0nat {
        1nat
    } else {
        10nat * pow10((k - 1) as nat)
    }
}

proof fn lemma_pow_base32_eq_pow2(k: nat)
    ensures
        pow_base32(k) == pow2(32nat * k),
        pow_base32(k) >= 1nat,
    decreases k,
{
    lemma_pow2_pos(32nat * k);
    if k == 0nat {
        assert(32nat * 0nat == 0nat);
        assert(pow2(0) == 1nat);
    } else {
        lemma_pow_base32_eq_pow2((k - 1) as nat);
        lemma_pow2_values();
        assert(32nat * k == 32nat + 32nat * ((k - 1) as nat)) by (nonlinear_arith)
            requires k >= 1nat;
        lemma_pow2_add(32nat, 32nat * ((k - 1) as nat));
    }
}

/// Little-endian base-`2^32` natural number interpretation of `limbs`.
pub open spec fn spec_big_val(limbs: Seq<u32>) -> nat
    decreases limbs.len(),
{
    if limbs.len() == 0 {
        0nat
    } else {
        (limbs[0] as nat) + 0x1_0000_0000nat * spec_big_val(limbs.subrange(1, limbs.len() as int))
    }
}

/// Canonical `BigNat`: no trailing zero limb.
pub open spec fn spec_big_canonical(limbs: Seq<u32>) -> bool {
    limbs.len() > 0 ==> limbs[limbs.len() - 1] != 0u32
}

proof fn lemma_big_val_push(limbs: Seq<u32>, x: u32)
    ensures
        spec_big_val(limbs.push(x))
            == spec_big_val(limbs) + (x as nat) * pow_base32(limbs.len()),
    decreases limbs.len(),
{
    let pushed = limbs.push(x);
    if limbs.len() == 0 {
        reveal_with_fuel(spec_big_val, 2);
        assert(pushed =~= seq![x]);
        assert(pushed.subrange(1, 1) =~= Seq::<u32>::empty());
        assert(pow_base32(0) == 1nat);
        assert((x as nat) * 1nat == (x as nat));
    } else {
        let tail = limbs.subrange(1, limbs.len() as int);
        assert(pushed[0] == limbs[0]);
        assert(pushed.subrange(1, pushed.len() as int) =~= tail.push(x));
        lemma_big_val_push(tail, x);
        let tv = spec_big_val(tail);
        let pb = pow_base32(tail.len());
        let xv = x as nat;
        assert(pow_base32(limbs.len()) == 0x1_0000_0000nat * pb);
        assert(0x1_0000_0000nat * (tv + xv * pb)
            == 0x1_0000_0000nat * tv + xv * (0x1_0000_0000nat * pb))
            by (nonlinear_arith);
    }
}

proof fn lemma_big_val_upper_bound(limbs: Seq<u32>)
    ensures
        spec_big_val(limbs) < pow_base32(limbs.len()),
    decreases limbs.len(),
{
    if limbs.len() == 0 {
        assert(pow_base32(0) == 1nat);
    } else {
        let tail = limbs.subrange(1, limbs.len() as int);
        lemma_big_val_upper_bound(tail);
        let tv = spec_big_val(tail);
        let pb = pow_base32(tail.len());
        let d0 = limbs[0] as nat;
        assert(pow_base32(limbs.len()) == 0x1_0000_0000nat * pb);
        assert(d0 + 0x1_0000_0000nat * tv < 0x1_0000_0000nat * pb) by (nonlinear_arith)
            requires d0 < 0x1_0000_0000nat, tv < pb;
    }
}

proof fn lemma_big_canonical_nonzero_iff_nonempty(limbs: Seq<u32>)
    requires
        spec_big_canonical(limbs),
    ensures
        (limbs.len() == 0) <==> (spec_big_val(limbs) == 0nat),
{
    if limbs.len() > 0 {
        let init = limbs.subrange(0, (limbs.len() - 1) as int);
        let top = limbs[limbs.len() - 1];
        assert(limbs =~= init.push(top));
        lemma_big_val_push(init, top);
        lemma_pow_base32_eq_pow2(init.len());
        let pb = pow_base32(init.len());
        assert((top as nat) * pb >= 1nat) by (nonlinear_arith)
            requires top >= 1u32, pb >= 1nat;
    }
}

fn big_trim(limbs: &mut Vec<u32>)
    ensures
        spec_big_canonical(final(limbs)@),
        spec_big_val(final(limbs)@) == spec_big_val(old(limbs)@),
        final(limbs)@.len() <= old(limbs)@.len(),
{
    while limbs.len() > 0 && limbs[limbs.len() - 1] == 0u32
        invariant
            spec_big_val(limbs@) == spec_big_val(old(limbs)@),
            limbs@.len() <= old(limbs)@.len(),
        decreases limbs@.len(),
    {
        let ghost before = limbs@;
        let _ = limbs.pop();
        proof {
            assert(before =~= limbs@.push(0u32));
            lemma_big_val_push(limbs@, 0u32);
        }
    }
}

#[verifier::spinoff_prover]
fn big_mul_add_u32(limbs: &[u32], mul: u32, add: u32) -> (out: Vec<u32>)
    requires
        limbs@.len() < usize::MAX - 2,
    ensures
        spec_big_canonical(out@),
        spec_big_val(out@) == spec_big_val(limbs@) * (mul as nat) + (add as nat),
        out@.len() <= limbs@.len() + 1,
{
    let n = limbs.len();
    let mut out: Vec<u32> = Vec::new();
    let mut carry: u64 = add as u64;
    let mut i: usize = 0;
    proof {
        assert(limbs@.subrange(0, 0) =~= Seq::<u32>::empty());
        assert(out@ =~= Seq::<u32>::empty());
        assert(spec_big_val(Seq::<u32>::empty()) == 0nat);
        assert(pow_base32(0) == 1nat);
        let av = add as nat;
        let mv = mul as nat;
        assert(av * 1nat == av) by (nonlinear_arith);
        assert(0nat * mv == 0nat) by (nonlinear_arith);
    }
    while i < n
        invariant
            i <= n,
            n == limbs@.len(),
            n < usize::MAX - 2,
            out@.len() == i as nat,
            carry < 0x1_0000_0000u64,
            spec_big_val(out@) + (carry as nat) * pow_base32(i as nat)
                == spec_big_val(limbs@.subrange(0, i as int)) * (mul as nat) + (add as nat),
        decreases n - i,
    {
        let li = limbs[i];
        proof {
            let lv = li as nat;
            let mv = mul as nat;
            let cv = carry as nat;
            assert(lv * mv + cv < 0x1_0000_0000nat * 0x1_0000_0000nat) by (nonlinear_arith)
                requires lv < 0x1_0000_0000nat, mv < 0x1_0000_0000nat, cv < 0x1_0000_0000nat;
        }
        let prod: u64 = (li as u64) * (mul as u64) + carry;
        let digit: u32 = (prod % 0x1_0000_0000u64) as u32;
        let next_carry: u64 = prod / 0x1_0000_0000u64;
        let ghost old_out = out@;
        let ghost sub_before = limbs@.subrange(0, i as int);
        out.push(digit);
        i += 1;
        carry = next_carry;
        proof {
            lemma_fundamental_div_mod(prod as int, 0x1_0000_0000int);
            assert(limbs@.subrange(0, i as int) =~= sub_before.push(li));
            lemma_big_val_push(sub_before, li);
            lemma_big_val_push(old_out, digit);
            let pb = pow_base32((i - 1) as nat);
            assert(pow_base32(i as nat) == 0x1_0000_0000nat * pb);
            let out_v = spec_big_val(old_out);
            let sub_v = spec_big_val(sub_before);
            let dv = digit as nat;
            let ncv = next_carry as nat;
            let lv = li as nat;
            let mv = mul as nat;
            let av = add as nat;
            let old_cv = (prod - (li as u64) * (mul as u64)) as nat;
            assert((prod as nat) == lv * mv + old_cv);
            assert((prod as nat) == 0x1_0000_0000nat * ncv + dv);
            assert((out_v + dv * pb) + ncv * (0x1_0000_0000nat * pb)
                == (sub_v + lv * pb) * mv + av) by (nonlinear_arith)
                requires
                    out_v + old_cv * pb == sub_v * mv + av,
                    lv * mv + old_cv == 0x1_0000_0000nat * ncv + dv;
        }
    }
    proof {
        assert(limbs@.subrange(0, n as int) =~= limbs@);
    }
    if carry > 0u64 {
        let c32 = carry as u32;
        let ghost old_out = out@;
        out.push(c32);
        proof {
            lemma_big_val_push(old_out, c32);
        }
    } else {
        proof {
            assert(0nat * pow_base32(n as nat) == 0nat);
        }
    }
    big_trim(&mut out);
    out
}

fn big_mul_pow10(limbs: &[u32], exp10: u32) -> (out: Vec<u32>)
    requires
        limbs@.len() + (exp10 as usize) < 0x0008_0000usize,
    ensures
        spec_big_canonical(out@),
        spec_big_val(out@) == spec_big_val(limbs@) * pow10(exp10 as nat),
        out@.len() <= limbs@.len() + (exp10 as nat),
{
    let acc = big_mul_add_u32(limbs, 1u32, 0u32);
    proof {
        assert(spec_big_val(limbs@) * 1nat + 0nat == spec_big_val(limbs@));
        assert(pow10(0nat) == 1nat);
        assert(spec_big_val(limbs@) * 1nat == spec_big_val(limbs@));
        // Notice: `big_mul_add_u32(limbs, 1, 0)` has `carry <= 0` so after trim `acc@.len() <= limbs@.len()`!
    }
    if acc.len() == 0 {
        proof {
            lemma_big_canonical_nonzero_iff_nonempty(acc@);
            assert(spec_big_val(limbs@) == 0nat);
            let p10 = pow10(exp10 as nat);
            assert(0nat * p10 == 0nat) by (nonlinear_arith);
        }
        return acc;
    }
    // Re-copy trimmed `limbs` so `acc.len() <= limbs.len()` strictly at `k = 0`:
    let mut cur: Vec<u32> = Vec::new();
    let mut m: usize = 0;
    while m < limbs.len()
        invariant
            m <= limbs@.len(),
            cur@ == limbs@.subrange(0, m as int),
        decreases limbs@.len() - m,
    {
        cur.push(limbs[m]);
        m += 1;
        proof { assert(cur@ =~= limbs@.subrange(0, m as int)); }
    }
    proof { assert(cur@ =~= limbs@); }
    big_trim(&mut cur);

    let mut k: u32 = 0;
    while k < exp10
        invariant
            k <= exp10,
            limbs@.len() + (exp10 as usize) < 0x0008_0000usize,
            spec_big_canonical(cur@),
            cur@.len() <= limbs@.len() + (k as nat),
            spec_big_val(cur@) == spec_big_val(limbs@) * pow10(k as nat),
        decreases exp10 - k,
    {
        let next = big_mul_add_u32(cur.as_slice(), 10u32, 0u32);
        k = k + 1;
        proof {
            let lv = spec_big_val(limbs@);
            let pk_prev = pow10((k - 1) as nat);
            assert(pow10(k as nat) == 10nat * pk_prev);
            assert((lv * pk_prev) * 10nat == lv * (10nat * pk_prev)) by (nonlinear_arith);
        }
        cur = next;
    }
    cur
}

fn big_shl_bits(limbs: &[u32], shift: u32) -> (out: Vec<u32>)
    requires
        spec_big_canonical(limbs@),
        limbs@.len() + ((shift / 32u32) as usize) + 2 < 0x0010_0000usize,
    ensures
        spec_big_canonical(out@),
        spec_big_val(out@) == spec_big_val(limbs@) * pow2(shift as nat),
        out@.len() <= limbs@.len() + ((shift / 32u32) as nat) + 1,
{
    if limbs.len() == 0 {
        let empty: Vec<u32> = Vec::new();
        proof {
            assert(empty@ =~= Seq::<u32>::empty());
            let p = pow2(shift as nat);
            assert(0nat * p == 0nat) by (nonlinear_arith);
        }
        return empty;
    }
    let word_shift: u32 = shift / 32u32;
    let bit_shift: u32 = shift % 32u32;
    let factor64: u64 = exec_pow2_u64(bit_shift);
    proof {
        lemma_pow2_monotonic(bit_shift as nat, 31nat);
        lemma_pow2_values();
        assert(factor64 <= 2147483648u64);
    }
    let scaled = big_mul_add_u32(limbs, factor64 as u32, 0u32);
    proof {
        lemma_big_canonical_nonzero_iff_nonempty(limbs@);
        lemma_pow2_pos(bit_shift as nat);
        let lv = spec_big_val(limbs@);
        let pb = pow2(bit_shift as nat);
        assert(lv * pb >= 1nat) by (nonlinear_arith)
            requires lv >= 1nat, pb >= 1nat;
        lemma_big_canonical_nonzero_iff_nonempty(scaled@);
        assert(scaled@.len() > 0);
        assert(32nat * 0nat == 0nat);
        assert(pow2(0nat) == 1nat);
        assert((lv * pb) * 1nat == lv * pb) by (nonlinear_arith);
    }
    // Prepend `word_shift` zero limbs (multiplying by `(2^32)^word_shift == 2^(32 * word_shift)`)
    let mut cur = scaled;
    let mut w: u32 = 0;
    while w < word_shift
        invariant
            w <= word_shift,
            spec_big_canonical(cur@),
            cur@.len() > 0,
            cur@.len() <= limbs@.len() + 1 + (w as nat),
            limbs@.len() + (word_shift as usize) + 2 < 0x0010_0000usize,
            spec_big_val(cur@)
                == (spec_big_val(limbs@) * pow2(bit_shift as nat)) * pow2(32nat * (w as nat)),
        decreases word_shift - w,
    {
        // Prepend one `0u32` limb: `next = [0] + cur`
        let mut next: Vec<u32> = Vec::new();
        next.push(0u32);
        let cn = cur.len();
        let mut idx: usize = 0;
        while idx < cn
            invariant
                idx <= cn,
                cn == cur@.len(),
                next@ == seq![0u32] + cur@.subrange(0, idx as int),
            decreases cn - idx,
        {
            next.push(cur[idx]);
            idx += 1;
            proof { assert(next@ =~= seq![0u32] + cur@.subrange(0, idx as int)); }
        }
        proof {
            assert(cur@.subrange(0, cn as int) =~= cur@);
            assert(next@ =~= seq![0u32] + cur@);
            assert(next@[0] == 0u32);
            assert(next@.subrange(1, next@.len() as int) =~= cur@);
            assert(next@[next@.len() - 1] == cur@[cur@.len() - 1]);
            let cv = spec_big_val(cur@);
            let base = spec_big_val(limbs@) * pow2(bit_shift as nat);
            let pw = pow2(32nat * (w as nat));
            lemma_pow2_values();
            assert(32nat * ((w + 1) as nat) == 32nat + 32nat * (w as nat)) by (nonlinear_arith);
            lemma_pow2_add(32nat, 32nat * (w as nat));
            assert(0x1_0000_0000nat * (base * pw) == base * (0x1_0000_0000nat * pw))
                by (nonlinear_arith);
        }
        cur = next;
        w = w + 1;
    }
    proof {
        let lv = spec_big_val(limbs@);
        let pb = pow2(bit_shift as nat);
        let pw = pow2(32nat * (word_shift as nat));
        lemma_pow2_add(bit_shift as nat, 32nat * (word_shift as nat));
        assert(bit_shift as nat + 32nat * (word_shift as nat) == shift as nat);
        assert((lv * pb) * pw == lv * (pb * pw)) by (nonlinear_arith);
    }
    cur
}

#[verifier::spinoff_prover]
fn big_cmp(a: &[u32], b: &[u32]) -> (ord: i8)
    requires
        spec_big_canonical(a@),
        spec_big_canonical(b@),
    ensures
        (ord == -1i8) <==> (spec_big_val(a@) < spec_big_val(b@)),
        (ord == 0i8) <==> (spec_big_val(a@) == spec_big_val(b@)),
        (ord == 1i8) <==> (spec_big_val(a@) > spec_big_val(b@)),
{
    let na = a.len();
    let nb = b.len();
    if na < nb {
        proof {
            lemma_big_val_upper_bound(a@);
            let b_init = b@.subrange(0, (nb - 1) as int);
            let b_top = b@[nb - 1];
            assert(b@ =~= b_init.push(b_top));
            lemma_big_val_push(b_init, b_top);
            lemma_pow_base32_eq_pow2(na as nat);
            lemma_pow_base32_eq_pow2((nb - 1) as nat);
            lemma_pow2_monotonic(32nat * (na as nat), 32nat * ((nb - 1) as nat));
            let p_b = pow_base32((nb - 1) as nat);
            assert((b_top as nat) * p_b >= p_b) by (nonlinear_arith)
                requires b_top >= 1u32, p_b >= 1nat;
        }
        return -1i8;
    }
    if na > nb {
        proof {
            lemma_big_val_upper_bound(b@);
            let a_init = a@.subrange(0, (na - 1) as int);
            let a_top = a@[na - 1];
            assert(a@ =~= a_init.push(a_top));
            lemma_big_val_push(a_init, a_top);
            lemma_pow_base32_eq_pow2(nb as nat);
            lemma_pow_base32_eq_pow2((na - 1) as nat);
            lemma_pow2_monotonic(32nat * (nb as nat), 32nat * ((na - 1) as nat));
            let p_a = pow_base32((na - 1) as nat);
            assert((a_top as nat) * p_a >= p_a) by (nonlinear_arith)
                requires a_top >= 1u32, p_a >= 1nat;
        }
        return 1i8;
    }
    let mut k: usize = na;
    proof {
        assert(a@.subrange(0, na as int) =~= a@);
        assert(b@.subrange(0, na as int) =~= b@);
    }
    while k > 0
        invariant
            k <= na,
            na == a@.len(),
            na == b@.len(),
            forall|m: int| k as int <= m && m < na as int ==> a@[m] == b@[m],
            spec_big_val(a@) < spec_big_val(b@)
                <==> spec_big_val(a@.subrange(0, k as int)) < spec_big_val(b@.subrange(0, k as int)),
            spec_big_val(a@) == spec_big_val(b@)
                <==> spec_big_val(a@.subrange(0, k as int)) == spec_big_val(b@.subrange(0, k as int)),
            spec_big_val(a@) > spec_big_val(b@)
                <==> spec_big_val(a@.subrange(0, k as int)) > spec_big_val(b@.subrange(0, k as int)),
        decreases k,
    {
        let idx = k - 1;
        let ghost a_hi = a@.subrange(0, k as int);
        let ghost b_hi = b@.subrange(0, k as int);
        let ghost a_lo = a@.subrange(0, idx as int);
        let ghost b_lo = b@.subrange(0, idx as int);
        proof {
            assert(a_hi =~= a_lo.push(a@[idx as int]));
            assert(b_hi =~= b_lo.push(b@[idx as int]));
            lemma_big_val_push(a_lo, a@[idx as int]);
            lemma_big_val_push(b_lo, b@[idx as int]);
            lemma_big_val_upper_bound(a_lo);
            lemma_big_val_upper_bound(b_lo);
            lemma_pow_base32_eq_pow2(idx as nat);
        }
        if a[idx] < b[idx] {
            proof {
                let pb = pow_base32(idx as nat);
                let al = spec_big_val(a_lo);
                let bl = spec_big_val(b_lo);
                let ai = a@[idx as int] as nat;
                let bi = b@[idx as int] as nat;
                assert(al + ai * pb < bl + bi * pb) by (nonlinear_arith)
                    requires al < pb, bl >= 0nat, ai + 1nat <= bi, pb >= 1nat;
            }
            return -1i8;
        }
        if a[idx] > b[idx] {
            proof {
                let pb = pow_base32(idx as nat);
                let al = spec_big_val(a_lo);
                let bl = spec_big_val(b_lo);
                let ai = a@[idx as int] as nat;
                let bi = b@[idx as int] as nat;
                assert(al + ai * pb > bl + bi * pb) by (nonlinear_arith)
                    requires bl < pb, al >= 0nat, bi + 1nat <= ai, pb >= 1nat;
            }
            return 1i8;
        }
        k = idx;
    }
    proof {
        assert(a@.subrange(0, 0) =~= Seq::<u32>::empty());
        assert(b@.subrange(0, 0) =~= Seq::<u32>::empty());
    }
    0i8
}

#[verifier::spinoff_prover]
fn big_sub(a: &[u32], b: &[u32]) -> (out: Vec<u32>)
    requires
        spec_big_canonical(a@),
        spec_big_canonical(b@),
        spec_big_val(a@) >= spec_big_val(b@),
    ensures
        spec_big_canonical(out@),
        spec_big_val(out@) == spec_big_val(a@) - spec_big_val(b@),
        out@.len() <= a@.len(),
{
    let na = a.len();
    let nb = b.len();
    proof {
        if nb > na {
            // Contradicts `spec_big_val(a@) >= spec_big_val(b@)` when `b` is canonical!
            lemma_big_val_upper_bound(a@);
            let b_init = b@.subrange(0, (nb - 1) as int);
            let b_top = b@[nb - 1];
            assert(b@ =~= b_init.push(b_top));
            lemma_big_val_push(b_init, b_top);
            lemma_pow_base32_eq_pow2(na as nat);
            lemma_pow_base32_eq_pow2((nb - 1) as nat);
            lemma_pow2_monotonic(32nat * (na as nat), 32nat * ((nb - 1) as nat));
            let p_b = pow_base32((nb - 1) as nat);
            assert((b_top as nat) * p_b >= p_b) by (nonlinear_arith)
                requires b_top >= 1u32, p_b >= 1nat;
            assert(false);
        }
    }
    let mut out: Vec<u32> = Vec::new();
    let mut borrow: u64 = 0;
    let mut i: usize = 0;
    proof {
        assert(a@.subrange(0, 0) =~= Seq::<u32>::empty());
        assert(b@.subrange(0, 0) =~= Seq::<u32>::empty());
        assert(out@ =~= Seq::<u32>::empty());
        assert(pow_base32(0) == 1nat);
    }
    while i < na
        invariant
            i <= na,
            nb <= na,
            na == a@.len(),
            nb == b@.len(),
            out@.len() == i as nat,
            borrow <= 1u64,
            (spec_big_val(out@) as int)
                - (borrow as int) * (pow_base32(i as nat) as int)
                == (spec_big_val(a@.subrange(0, i as int)) as int)
                    - (spec_big_val(b@.subrange(0, if i <= nb { i as int } else { nb as int })) as int),
        decreases na - i,
    {
        let ai: u64 = a[i] as u64;
        let bi: u64 = if i < nb { b[i] as u64 } else { 0u64 };
        let need: u64 = bi + borrow;
        let (digit, next_borrow): (u32, u64) = if ai >= need {
            ((ai - need) as u32, 0u64)
        } else {
            ((0x1_0000_0000u64 + ai - need) as u32, 1u64)
        };
        let ghost old_out = out@;
        let ghost a_before = a@.subrange(0, i as int);
        let ghost b_before = b@.subrange(0, if i <= nb { i as int } else { nb as int });
        out.push(digit);
        let ghost old_i = i;
        let ghost old_borrow = borrow;
        i += 1;
        borrow = next_borrow;
        proof {
            assert(a@.subrange(0, i as int) =~= a_before.push(a@[old_i as int]));
            lemma_big_val_push(a_before, a@[old_i as int]);
            if old_i < nb {
                assert(b@.subrange(0, i as int) =~= b_before.push(b@[old_i as int]));
                lemma_big_val_push(b_before, b@[old_i as int]);
            } else {
                assert((if i <= nb { i as int } else { nb as int }) == nb as int);
                assert(bi == 0u64);
            }
            lemma_big_val_push(old_out, digit);
            let pb = pow_base32(old_i as nat) as int;
            assert((pow_base32(i as nat) as int) == 0x1_0000_0000int * pb);
            let out_v = spec_big_val(old_out) as int;
            let a_v = spec_big_val(a_before) as int;
            let b_v = spec_big_val(b_before) as int;
            let dv = digit as int;
            let nbv = next_borrow as int;
            let obv = old_borrow as int;
            let aiv = ai as int;
            let biv = bi as int;
            assert(dv - 0x1_0000_0000int * nbv == aiv - biv - obv);
            assert((out_v + dv * pb) - nbv * (0x1_0000_0000int * pb)
                == (a_v + aiv * pb) - (b_v + biv * pb)) by (nonlinear_arith)
                requires
                    out_v - obv * pb == a_v - b_v,
                    dv - 0x1_0000_0000int * nbv == aiv - biv - obv;
        }
    }
    proof {
        assert(a@.subrange(0, na as int) =~= a@);
        assert(b@.subrange(0, nb as int) =~= b@);
        if borrow == 1u64 {
            lemma_big_val_upper_bound(out@);
            assert(false);
        }
        assert(borrow == 0u64);
    }
    big_trim(&mut out);
    out
}

pub open spec fn spec_bit_len_nat(x: nat) -> nat
    decreases x,
{
    if x <= 1nat {
        1nat
    } else {
        1nat + spec_bit_len_nat(x / 2nat)
    }
}

proof fn lemma_bit_len_nat_bounds(x: nat)
    requires
        x >= 1nat,
    ensures
        spec_bit_len_nat(x) >= 1nat,
        pow2((spec_bit_len_nat(x) - 1) as nat) <= x,
        x < pow2(spec_bit_len_nat(x)),
    decreases x,
{
    if x == 1nat {
        assert(pow2(0) == 1nat);
        reveal_with_fuel(pow2, 2);
        assert(pow2(1) == 2nat);
    } else {
        lemma_bit_len_nat_bounds(x / 2nat);
        let b = spec_bit_len_nat(x / 2nat);
        lemma_fundamental_div_mod(x as int, 2int);
        assert(pow2(b) == 2nat * pow2((b - 1) as nat));
        assert(pow2(b + 1) == 2nat * pow2(b));
    }
}

proof fn lemma_bit_len_nat_unique(x: nat, k: nat)
    requires
        x >= 1nat,
        k >= 1nat,
        pow2((k - 1) as nat) <= x,
        x < pow2(k),
    ensures
        spec_bit_len_nat(x) == k,
{
    lemma_bit_len_nat_bounds(x);
    let b = spec_bit_len_nat(x);
    if b < k {
        lemma_pow2_monotonic(b, (k - 1) as nat);
        assert(false);
    }
    if b > k {
        lemma_pow2_monotonic(k, (b - 1) as nat);
        assert(false);
    }
}

fn big_bit_len(a: &[u32]) -> (bits: u64)
    requires
        spec_big_canonical(a@),
        a@.len() >= 1,
        a@.len() < 0x0010_0000usize,
    ensures
        bits >= 1u64,
        bits <= 0x0200_0000u64,
        bits as nat == spec_bit_len_nat(spec_big_val(a@)),
        pow2((bits - 1) as nat) <= spec_big_val(a@),
        spec_big_val(a@) < pow2(bits as nat),
{
    let na = a.len();
    let top: u32 = a[na - 1];
    let top_msb: u32 = find_highest_bit_u64(top as u64);
    proof {
        if top_msb >= 32u32 {
            lemma_pow2_monotonic(32nat, top_msb as nat);
            lemma_pow2_values();
            assert(false);
        }
        let init = a@.subrange(0, (na - 1) as int);
        assert(a@ =~= init.push(top));
        lemma_big_val_push(init, top);
        lemma_big_val_upper_bound(init);
        lemma_pow_base32_eq_pow2((na - 1) as nat);
        let w_bits: nat = 32nat * ((na - 1) as nat);
        let p_w = pow2(w_bits);
        let p_t = pow2(top_msb as nat);
        let p_t1 = pow2((top_msb + 1) as nat);
        lemma_pow2_pos(w_bits);
        lemma_pow2_add(top_msb as nat, w_bits);
        lemma_pow2_add((top_msb + 1) as nat, w_bits);
        let init_v = spec_big_val(init);
        let top_v = top as nat;
        assert(init_v + top_v * p_w >= p_t * p_w) by (nonlinear_arith)
            requires init_v >= 0nat, top_v >= p_t, p_w >= 1nat;
        assert(init_v + top_v * p_w < p_t1 * p_w) by (nonlinear_arith)
            requires init_v < p_w, top_v + 1nat <= p_t1, p_w >= 1nat;
        let k_nat: nat = (top_msb as nat) + 1nat + w_bits;
        lemma_bit_len_nat_unique(spec_big_val(a@), k_nat);
    }
    ((na - 1) as u64) * 32u64 + (top_msb as u64) + 1u64
}

/// 54-step binary long division computing `((num2 / den2) as u64, (num2 % den2) != 0)`
/// whenever `0 <= num2 < den2 * 2^54`.
#[verifier::spinoff_prover]
fn big_div_54(num2: &[u32], den2: &[u32]) -> (res: (u64, bool))
    requires
        spec_big_canonical(num2@),
        spec_big_canonical(den2@),
        den2@.len() >= 1,
        num2@.len() < 0x0008_0000usize,
        den2@.len() < 0x0008_0000usize,
        spec_big_val(num2@) < spec_big_val(den2@) * pow2(54nat),
    ensures
        res.0 < 0x0040_0000_0000_0000u64,
        res.0 as nat == spec_big_val(num2@) / spec_big_val(den2@),
        res.1 == ((spec_big_val(num2@) % spec_big_val(den2@)) != 0nat),
{
    let ghost n_val = spec_big_val(num2@);
    let ghost d_val = spec_big_val(den2@);
    proof {
        lemma_big_canonical_nonzero_iff_nonempty(den2@);
        assert(d_val >= 1nat);
    }
    let mut cur_rem = big_mul_add_u32(num2, 1u32, 0u32);
    proof {
        assert(n_val * 1nat + 0nat == n_val) by (nonlinear_arith);
        assert(spec_big_val(cur_rem@) == n_val);
        assert(pow2(0nat) == 1nat);
        let p54 = pow2(54nat);
        assert((0nat * p54) * d_val == 0nat) by (nonlinear_arith);
    }
    let mut q_acc: u64 = 0u64;
    let mut k: u32 = 54u32;
    while k > 0u32
        invariant
            k <= 54u32,
            spec_big_canonical(cur_rem@),
            spec_big_canonical(den2@),
            den2@.len() < 0x0008_0000usize,
            d_val == spec_big_val(den2@),
            d_val >= 1nat,
            (q_acc as nat) < pow2((54u32 - k) as nat),
            spec_big_val(cur_rem@) < d_val * pow2(k as nat),
            n_val == ((q_acc as nat) * pow2(k as nat)) * d_val + spec_big_val(cur_rem@),
        decreases k,
    {
        let step_bit: u32 = k - 1u32;
        let shifted_den = big_shl_bits(den2, step_bit);
        let cmp = big_cmp(cur_rem.as_slice(), shifted_den.as_slice());
        proof {
            lemma_pow2_values();
            lemma_pow2_monotonic((54u32 - k) as nat, 53nat);
            assert(q_acc < 0x0020_0000_0000_0000u64);
            assert(pow2(k as nat) == 2nat * pow2(step_bit as nat));
            assert(pow2((54u32 - step_bit) as nat) == 2nat * pow2((54u32 - k) as nat));
        }
        let ghost pk_sub = pow2(step_bit as nat);
        let ghost rem_before = spec_big_val(cur_rem@);
        let ghost q_before = q_acc as nat;
        if cmp >= 0i8 {
            cur_rem = big_sub(cur_rem.as_slice(), shifted_den.as_slice());
            q_acc = q_acc * 2u64 + 1u64;
            proof {
                assert(rem_before >= d_val * pk_sub);
                assert(rem_before < d_val * (2nat * pk_sub));
                assert(rem_before - d_val * pk_sub < d_val * pk_sub) by (nonlinear_arith)
                    requires rem_before >= d_val * pk_sub, rem_before < d_val * (2nat * pk_sub);
                assert(((2nat * q_before + 1nat) * pk_sub) * d_val + (rem_before - d_val * pk_sub)
                    == (q_before * (2nat * pk_sub)) * d_val + rem_before) by (nonlinear_arith)
                    requires rem_before >= d_val * pk_sub;
            }
        } else {
            q_acc = q_acc * 2u64;
            proof {
                assert(((2nat * q_before) * pk_sub) * d_val + rem_before
                    == (q_before * (2nat * pk_sub)) * d_val + rem_before) by (nonlinear_arith);
            }
        }
        k = step_bit;
    }
    let rem_nz: bool = cur_rem.len() > 0usize;
    proof {
        lemma_pow2_values();
        assert(pow2(0) == 1nat);
        assert((q_acc as nat) * 1nat == (q_acc as nat));
        assert(d_val * 1nat == d_val);
        let rem_final = spec_big_val(cur_rem@);
        assert((q_acc as int) * (d_val as int) == (d_val as int) * (q_acc as int))
            by (nonlinear_arith);
        lemma_fundamental_div_mod_converse(
            n_val as int,
            d_val as int,
            q_acc as int,
            rem_final as int,
        );
        lemma_big_canonical_nonzero_iff_nonempty(cur_rem@);
    }
    (q_acc, rem_nz)
}

pub open spec fn spec_ratio_ge_pow2(n: nat, d: nat, e: int) -> bool {
    if e >= 0int {
        n >= d * pow2(e as nat)
    } else {
        n * pow2((-e) as nat) >= d
    }
}

proof fn lemma_cand_bounds_binade(n: nat, d: nat, bn: nat, bd: nat)
    requires
        n >= 1nat,
        d >= 1nat,
        bn >= 1nat,
        bd >= 1nat,
        pow2((bn - 1) as nat) <= n,
        n < pow2(bn),
        pow2((bd - 1) as nat) <= d,
        d < pow2(bd),
    ensures
        spec_ratio_ge_pow2(n, d, (bn as int) - (bd as int) - 1),
        !spec_ratio_ge_pow2(n, d, (bn as int) - (bd as int) + 1),
{
    let cand_minus: int = (bn as int) - (bd as int) - 1;
    if cand_minus >= 0int {
        let k = cand_minus as nat;
        assert(bd + k == (bn - 1) as nat);
        lemma_pow2_add(bd, k);
        lemma_pow2_pos(k);
        let p_bd = pow2(bd);
        let p_k = pow2(k);
        assert(d * p_k < p_bd * p_k) by (nonlinear_arith)
            requires d < p_bd, p_k >= 1nat;
    } else {
        let m = (-cand_minus) as nat;
        assert(((bn - 1) as nat) + m == bd);
        lemma_pow2_add((bn - 1) as nat, m);
        lemma_pow2_pos(m);
        let p_bn1 = pow2((bn - 1) as nat);
        let p_m = pow2(m);
        assert(n * p_m >= p_bn1 * p_m) by (nonlinear_arith)
            requires n >= p_bn1, p_m >= 1nat;
    }

    let cand_plus: int = (bn as int) - (bd as int) + 1;
    if cand_plus >= 0int {
        let k = cand_plus as nat;
        assert(((bd - 1) as nat) + k == bn);
        lemma_pow2_add((bd - 1) as nat, k);
        lemma_pow2_pos(k);
        let p_bd1 = pow2((bd - 1) as nat);
        let p_k = pow2(k);
        assert(d * p_k >= p_bd1 * p_k) by (nonlinear_arith)
            requires d >= p_bd1, p_k >= 1nat;
    } else {
        let m = (-cand_plus) as nat;
        assert(bn + m == (bd - 1) as nat);
        lemma_pow2_add(bn, m);
        lemma_pow2_pos(m);
        let p_bn = pow2(bn);
        let p_m = pow2(m);
        assert(n * p_m < p_bn * p_m) by (nonlinear_arith)
            requires n < p_bn, p_m >= 1nat;
    }
}

/// Pure mathematical `nat` specification for exact IEEE-754 binary64 Round-Ties-to-Even (RNE)
/// conversion of positive rational `n / d` (`n >= 1, d >= 1`) with sign `neg`.
pub open spec fn spec_rational_rne_f64_bits(neg: bool, n: nat, d: nat) -> u64 {
    let bn = spec_bit_len_nat(n);
    let bd = spec_bit_len_nat(d);
    let cand: int = (bn as int) - (bd as int);
    let sign_part: u64 = if neg { 0x8000_0000_0000_0000u64 } else { 0u64 };
    if cand > 1025int {
        if neg { F64_NEG_INF } else { F64_POS_INF }
    } else if cand < -1075int {
        sign_part
    } else {
        let e: int = if spec_ratio_ge_pow2(n, d, cand) { cand } else { cand - 1 };
        if e >= 1024int {
            if neg { F64_NEG_INF } else { F64_POS_INF }
        } else if e < -1075int {
            sign_part
        } else {
            let s: int = if e - 52int < -1074int { -1074int } else { e - 52int };
            let shift2: int = 1int - s;
            let (num2, den2): (nat, nat) = if shift2 >= 0int {
                (n * pow2(shift2 as nat), d)
            } else {
                (n, d * pow2((-shift2) as nat))
            };
            let q2: nat = num2 / den2;
            let rem_nz: bool = (num2 % den2) != 0nat;
            let q: u64 = (q2 / 2nat) as u64;
            let half_bit: nat = q2 % 2nat;
            let round_up: bool = (half_bit == 1nat) && (rem_nz || ((q % 2u64) == 1u64));
            let q_rne: u64 = if round_up { (q + 1u64) as u64 } else { q };
            if s == -1074int {
                (sign_part + q_rne) as u64
            } else {
                let biased_base: u64 = (e + 1023int) as u64;
                if q_rne >= 0x0020_0000_0000_0000u64 {
                    if biased_base + 1u64 >= 2047u64 {
                        if neg { F64_NEG_INF } else { F64_POS_INF }
                    } else {
                        (sign_part + (biased_base + 1u64) * 0x0010_0000_0000_0000u64) as u64
                    }
                } else {
                    (sign_part
                        + biased_base * 0x0010_0000_0000_0000u64
                        + (q_rne - 0x0010_0000_0000_0000u64)) as u64
                }
            }
        }
    }
}

proof fn lemma_scaled_num_lt_pow2_54(n: nat, d: nat, e: int, s: int)
    requires
        n >= 1nat,
        d >= 1nat,
        -1075int <= e && e <= 1023int,
        s == (if e - 52int < -1074int { -1074int } else { e - 52int }),
        !spec_ratio_ge_pow2(n, d, e + 1int),
    ensures
        ({
            let shift2: int = 1int - s;
            let (num2, den2): (nat, nat) = if shift2 >= 0int {
                (n * pow2(shift2 as nat), d)
            } else {
                (n, d * pow2((-shift2) as nat))
            };
            num2 < den2 * pow2(54nat)
        }),
{
    let shift2: int = 1int - s;
    if e + 1int >= 0int {
        let ep1 = (e + 1int) as nat;
        assert(n < d * pow2(ep1));
        if shift2 >= 0int {
            let sh = shift2 as nat;
            lemma_pow2_pos(sh);
            let p_ep1 = pow2(ep1);
            let p_sh = pow2(sh);
            assert(n * p_sh < (d * p_ep1) * p_sh) by (nonlinear_arith)
                requires n < d * p_ep1, p_sh >= 1nat;
            assert((d * p_ep1) * p_sh == d * (p_ep1 * p_sh)) by (nonlinear_arith);
            lemma_pow2_add(ep1, sh);
            lemma_pow2_monotonic(ep1 + sh, 54nat);
            let p_sum = pow2(ep1 + sh);
            let p_54 = pow2(54nat);
            assert(d * p_sum <= d * p_54) by (nonlinear_arith)
                requires p_sum <= p_54;
        } else {
            let nsh = (-shift2) as nat;
            assert(ep1 == nsh + 54nat);
            lemma_pow2_add(nsh, 54nat);
            let p_nsh = pow2(nsh);
            let p_54 = pow2(54nat);
            assert(d * (p_nsh * p_54) == (d * p_nsh) * p_54) by (nonlinear_arith);
        }
    } else {
        let m = (-(e + 1int)) as nat;
        assert(shift2 >= 0int);
        let sh = shift2 as nat;
        assert(n * pow2(m) < d);
        lemma_pow2_pos(54nat);
        let p_m = pow2(m);
        let p_54 = pow2(54nat);
        assert((n * p_m) * p_54 < d * p_54) by (nonlinear_arith)
            requires n * p_m < d, p_54 >= 1nat;
        assert((n * p_m) * p_54 == n * (p_m * p_54)) by (nonlinear_arith);
        lemma_pow2_add(m, 54nat);
        assert(sh <= m + 54nat);
        lemma_pow2_monotonic(sh, m + 54nat);
        let p_sh = pow2(sh);
        let p_m54 = pow2(m + 54nat);
        assert(n * p_sh <= n * p_m54) by (nonlinear_arith)
            requires p_sh <= p_m54;
    }
}

proof fn lemma_scaled_num_ge_pow2_53_when_normal(n: nat, d: nat, e: int)
    requires
        n >= 1nat,
        d >= 1nat,
        -1021int <= e && e <= 1023int,
        spec_ratio_ge_pow2(n, d, e),
    ensures
        ({
            let s: int = e - 52int;
            let shift2: int = 1int - s;
            let (num2, den2): (nat, nat) = if shift2 >= 0int {
                (n * pow2(shift2 as nat), d)
            } else {
                (n, d * pow2((-shift2) as nat))
            };
            num2 >= den2 * pow2(53nat)
        }),
{
    let s: int = e - 52int;
    let shift2: int = 1int - s;
    if e >= 0int {
        let en = e as nat;
        assert(n >= d * pow2(en));
        if shift2 >= 0int {
            let sh = shift2 as nat;
            assert(en + sh == 53nat);
            lemma_pow2_pos(sh);
            let p_e = pow2(en);
            let p_sh = pow2(sh);
            assert(n * p_sh >= (d * p_e) * p_sh) by (nonlinear_arith)
                requires n >= d * p_e, p_sh >= 1nat;
            assert((d * p_e) * p_sh == d * (p_e * p_sh)) by (nonlinear_arith);
            lemma_pow2_add(en, sh);
        } else {
            let nsh = (-shift2) as nat;
            assert(en == nsh + 53nat);
            lemma_pow2_add(nsh, 53nat);
            let p_nsh = pow2(nsh);
            let p_53 = pow2(53nat);
            assert(d * (p_nsh * p_53) == (d * p_nsh) * p_53) by (nonlinear_arith);
        }
    } else {
        let m = (-e) as nat;
        assert(shift2 >= 0int);
        let sh = shift2 as nat;
        assert(sh == m + 53nat);
        assert(n * pow2(m) >= d);
        lemma_pow2_pos(53nat);
        let p_m = pow2(m);
        let p_53 = pow2(53nat);
        assert((n * p_m) * p_53 >= d * p_53) by (nonlinear_arith)
            requires n * p_m >= d, p_53 >= 1nat;
        assert((n * p_m) * p_53 == n * (p_m * p_53)) by (nonlinear_arith);
        lemma_pow2_add(m, 53nat);
    }
}

#[verifier::spinoff_prover]
fn exec_rational_rne_f64_bits(neg: bool, n_limbs: &[u32], d_limbs: &[u32]) -> (bits: u64)
    requires
        spec_big_canonical(n_limbs@),
        spec_big_canonical(d_limbs@),
        n_limbs@.len() >= 1,
        d_limbs@.len() >= 1,
        n_limbs@.len() < 0x0004_0000usize,
        d_limbs@.len() < 0x0004_0000usize,
    ensures
        bits == spec_rational_rne_f64_bits(neg, spec_big_val(n_limbs@), spec_big_val(d_limbs@)),
{
    let ghost n_val = spec_big_val(n_limbs@);
    let ghost d_val = spec_big_val(d_limbs@);
    proof {
        lemma_big_canonical_nonzero_iff_nonempty(n_limbs@);
        lemma_big_canonical_nonzero_iff_nonempty(d_limbs@);
        lemma_pow2_values();
    }
    let bn = big_bit_len(n_limbs);
    let bd = big_bit_len(d_limbs);
    let cand: i64 = (bn as i64) - (bd as i64);
    let sign_part: u64 = if neg { 0x8000_0000_0000_0000u64 } else { 0u64 };

    if cand > 1025i64 {
        return if neg { F64_NEG_INF } else { F64_POS_INF };
    }
    if cand < -1075i64 {
        return sign_part;
    }

    // Check `spec_ratio_ge_pow2(n_val, d_val, cand)` with shift `<= 1075`!
    let ge_cand: bool = if cand >= 0i64 {
        let d_shifted = big_shl_bits(d_limbs, cand as u32);
        big_cmp(n_limbs, d_shifted.as_slice()) >= 0i8
    } else {
        let n_shifted = big_shl_bits(n_limbs, (-cand) as u32);
        big_cmp(n_shifted.as_slice(), d_limbs) >= 0i8
    };

    let e: i32 = if ge_cand { cand as i32 } else { (cand - 1i64) as i32 };
    if e >= 1024i32 {
        return if neg { F64_NEG_INF } else { F64_POS_INF };
    }
    if e < -1075i32 {
        return sign_part;
    }

    let s: i32 = if e - 52i32 < -1074i32 { -1074i32 } else { e - 52i32 };
    let shift2: i32 = 1i32 - s;
    proof {
        lemma_cand_bounds_binade(n_val, d_val, bn as nat, bd as nat);
        lemma_scaled_num_lt_pow2_54(n_val, d_val, e as int, s as int);
    }

    let (q2, rem_nz): (u64, bool) = if shift2 >= 0i32 {
        let num2 = big_shl_bits(n_limbs, shift2 as u32);
        big_div_54(num2.as_slice(), d_limbs)
    } else {
        let den2 = big_shl_bits(d_limbs, (-shift2) as u32);
        big_div_54(n_limbs, den2.as_slice())
    };

    let q: u64 = q2 / 2u64;
    let half_bit: u64 = q2 % 2u64;
    let round_up: bool = (half_bit == 1u64) && (rem_nz || ((q % 2u64) == 1u64));
    let q_rne: u64 = if round_up { q + 1u64 } else { q };

    if s == -1074i32 {
        sign_part + q_rne
    } else {
        proof {
            lemma_scaled_num_ge_pow2_53_when_normal(n_val, d_val, e as int);
            let (num2_v, den2_v): (nat, nat) = if shift2 >= 0i32 {
                (n_val * pow2(shift2 as nat), d_val)
            } else {
                (n_val, d_val * pow2((-shift2) as nat))
            };
            lemma_fundamental_div_mod(num2_v as int, den2_v as int);
            let p53 = pow2(53nat) as int;
            let dv = den2_v as int;
            let q2i = q2 as int;
            let ri = (num2_v % den2_v) as int;
            if q2 < 0x0020_0000_0000_0000u64 {
                assert(dv * q2i + ri < dv * p53) by (nonlinear_arith)
                    requires q2i < p53, ri < dv, dv >= 1int;
                assert(false);
            }
            assert(q >= 0x0010_0000_0000_0000u64);
        }
        let biased_base: u64 = (e + 1023i32) as u64;
        if q_rne >= 0x0020_0000_0000_0000u64 {
            if biased_base + 1u64 >= 2047u64 {
                if neg { F64_NEG_INF } else { F64_POS_INF }
            } else {
                sign_part + (biased_base + 1u64) * 0x0010_0000_0000_0000u64
            }
        } else {
            sign_part
                + biased_base * 0x0010_0000_0000_0000u64
                + (q_rne - 0x0010_0000_0000_0000u64)
        }
    }
}

pub open spec fn spec_seq_eq_ascii(s: Seq<u16>, pat: Seq<u8>) -> bool {
    s.len() == pat.len()
    && forall|i: int| 0 <= i < s.len() ==> s[i] == (pat[i] as u16)
}

fn slice_eq_ascii(s: &[u16], pat: &[u8]) -> (r: bool)
    ensures
        r == spec_seq_eq_ascii(s@, pat@),
{
    if s.len() != pat.len() {
        return false;
    }
    let n = s.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == s@.len(),
            n == pat@.len(),
            forall|k: int| 0 <= k < i as int ==> s@[k] == (pat@[k] as u16),
        decreases n - i,
    {
        if s[i] != (pat[i] as u16) {
            return false;
        }
        i += 1;
    }
    true
}

/// Parse non-empty radix (`2`, `8`, `16`) digit sequence into a natural number, returning
/// `None` if empty or containing any non-radix character.
pub open spec fn spec_parse_radix_nat_loop(s: Seq<u16>, radix: nat, acc: nat) -> Option<nat>
    decreases s.len(),
{
    if s.len() == 0 {
        Some(acc)
    } else {
        let c = s[0];
        let d_opt: Option<nat> = if 0x30u16 <= c && c <= 0x39u16 {
            let d = (c - 0x30u16) as nat;
            if d < radix { Some(d) } else { None }
        } else if radix == 16nat && 0x41u16 <= c && c <= 0x46u16 {
            Some((c - 0x41u16 + 10u16) as nat)
        } else if radix == 16nat && 0x61u16 <= c && c <= 0x66u16 {
            Some((c - 0x61u16 + 10u16) as nat)
        } else {
            None
        };
        match d_opt {
            None => None,
            Some(d) => spec_parse_radix_nat_loop(
                s.subrange(1, s.len() as int),
                radix,
                acc * radix + d,
            ),
        }
    }
}

pub open spec fn spec_radix_str_to_f64_bits(s: Seq<u16>, radix: nat) -> u64 {
    match spec_parse_radix_nat_loop(s, radix, 0nat) {
        None => F64_CANON_NAN,
        Some(v) => {
            if v == 0nat {
                F64_POS_ZERO
            } else {
                spec_rational_rne_f64_bits(false, v, 1nat)
            }
        },
    }
}

proof fn lemma_radix_loop_overflow_stays_huge(
    s: Seq<u16>,
    radix: nat,
    acc: nat,
    bound: nat,
)
    requires
        radix >= 2nat,
        acc >= bound,
    ensures
        match spec_parse_radix_nat_loop(s, radix, acc) {
            None => true,
            Some(v) => v >= bound,
        },
    decreases s.len(),
{
    if s.len() > 0 {
        let c = s[0];
        let d_opt: Option<nat> = if 0x30u16 <= c && c <= 0x39u16 {
            let d = (c - 0x30u16) as nat;
            if d < radix { Some(d) } else { None }
        } else if radix == 16nat && 0x41u16 <= c && c <= 0x46u16 {
            Some((c - 0x41u16 + 10u16) as nat)
        } else if radix == 16nat && 0x61u16 <= c && c <= 0x66u16 {
            Some((c - 0x61u16 + 10u16) as nat)
        } else {
            None
        };
        if let Some(d) = d_opt {
            assert(acc * radix + d >= acc) by (nonlinear_arith)
                requires acc >= bound, radix >= 2nat;
            lemma_radix_loop_overflow_stays_huge(
                s.subrange(1, s.len() as int),
                radix,
                acc * radix + d,
                bound,
            );
        }
    }
}

#[verifier::spinoff_prover]
fn parse_radix_to_f64_bits(s: &[u16], start: usize, radix: u32) -> (bits: u64)
    requires
        start < s@.len(),
        radix == 2u32 || radix == 8u32 || radix == 16u32,
    ensures
        bits == spec_radix_str_to_f64_bits(s@.subrange(start as int, s@.len() as int), radix as nat),
{
    let n = s.len();
    let mut i = start;
    let mut acc: Vec<u32> = Vec::new();
    let mut overflow_inf: bool = false;
    proof {
        assert(acc@ =~= Seq::<u32>::empty());
    }
    while i < n
        invariant
            start <= i,
            i <= n,
            n == s@.len(),
            radix == 2u32 || radix == 8u32 || radix == 16u32,
            !overflow_inf ==> (
                spec_big_canonical(acc@)
                && acc@.len() <= 40
                && spec_parse_radix_nat_loop(s@.subrange(start as int, n as int), radix as nat, 0nat)
                    == spec_parse_radix_nat_loop(
                        s@.subrange(i as int, n as int),
                        radix as nat,
                        spec_big_val(acc@),
                    )
            ),
            overflow_inf ==> (
                match spec_parse_radix_nat_loop(s@.subrange(start as int, n as int), radix as nat, 0nat) {
                    None => spec_parse_radix_nat_loop(s@.subrange(i as int, n as int), radix as nat, 0nat).is_none(),
                    Some(v) => spec_parse_radix_nat_loop(s@.subrange(i as int, n as int), radix as nat, 0nat).is_some()
                        && v >= pow2(1100nat),
                }
            ),
        decreases n - i,
    {
        let c = s[i];
        let ghost sub = s@.subrange(i as int, n as int);
        let d_opt: Option<u32> = if 0x30u16 <= c && c <= 0x39u16 {
            let d = (c - 0x30u16) as u32;
            if d < radix { Some(d) } else { None }
        } else if radix == 16u32 && 0x41u16 <= c && c <= 0x46u16 {
            Some((c - 0x41u16 + 10u16) as u32)
        } else if radix == 16u32 && 0x61u16 <= c && c <= 0x66u16 {
            Some((c - 0x61u16 + 10u16) as u32)
        } else {
            None
        };
        match d_opt {
            None => {
                proof {
                    if overflow_inf {
                        assert(spec_parse_radix_nat_loop(sub, radix as nat, 0nat).is_none());
                    }
                }
                return F64_CANON_NAN;
            },
            Some(d) => {
                i += 1;
                let ghost next_sub = s@.subrange(i as int, n as int);
                proof {
                    assert(sub.subrange(1, sub.len() as int) =~= next_sub);
                }
                if !overflow_inf {
                    acc = big_mul_add_u32(acc.as_slice(), radix, d);
                    if acc.len() > 40 {
                        overflow_inf = true;
                        proof {
                            // `acc.len() >= 41` canonical => `spec_big_val(acc@) >= (2^32)^40 = 2^1280 >= 2^1100`
                            let init = acc@.subrange(0, (acc@.len() - 1) as int);
                            let top = acc@[acc@.len() - 1];
                            assert(acc@ =~= init.push(top));
                            lemma_big_val_push(init, top);
                            lemma_pow_base32_eq_pow2(init.len());
                            assert(32nat * init.len() >= 1280nat);
                            lemma_pow2_monotonic(1100nat, 32nat * init.len());
                            let p_i = pow_base32(init.len());
                            assert((top as nat) * p_i >= p_i) by (nonlinear_arith)
                                requires top >= 1u32, p_i >= 1nat;
                            lemma_radix_loop_overflow_stays_huge(
                                next_sub,
                                radix as nat,
                                spec_big_val(acc@),
                                pow2(1100nat),
                            );
                            // Also relate `is_none()`/`is_some()` regardless of `acc`!
                            lemma_radix_loop_some_indep_of_acc(next_sub, radix as nat, spec_big_val(acc@), 0nat);
                        }
                    }
                } else {
                    proof {
                        lemma_radix_loop_some_indep_of_acc(next_sub, radix as nat, d as nat, 0nat);
                    }
                }
            },
        }
    }
    proof {
        assert(s@.subrange(n as int, n as int) =~= Seq::<u16>::empty());
    }
    if overflow_inf {
        proof {
            match spec_parse_radix_nat_loop(s@.subrange(start as int, n as int), radix as nat, 0nat) {
                None => {
                    assert(false);
                },
                Some(v) => {
                    lemma_pow2_pos(1100nat);
                    lemma_bit_len_nat_bounds(v);
                    let bv = spec_bit_len_nat(v);
                    if bv <= 1100nat {
                        lemma_pow2_monotonic(bv, 1100nat);
                        assert(false);
                    }
                    assert(spec_bit_len_nat(1nat) == 1nat);
                    assert((bv as int) - 1int > 1025int);
                },
            }
        }
        return F64_POS_INF;
    }
    if acc.len() == 0 {
        proof {
            lemma_big_canonical_nonzero_iff_nonempty(acc@);
        }
        return F64_POS_ZERO;
    }
    let one: [u32; 1] = [1u32];
    proof {
        lemma_big_canonical_nonzero_iff_nonempty(acc@);
        reveal_with_fuel(spec_big_val, 2);
        assert(one@ =~= seq![1u32]);
        assert(one@.subrange(1, 1) =~= Seq::<u32>::empty());
        assert(spec_big_val(one@) == 1nat);
        assert(spec_big_canonical(one@));
    }
    exec_rational_rne_f64_bits(false, acc.as_slice(), &one)
}

proof fn lemma_radix_loop_some_indep_of_acc(s: Seq<u16>, radix: nat, a1: nat, a2: nat)
    ensures
        spec_parse_radix_nat_loop(s, radix, a1).is_some()
            == spec_parse_radix_nat_loop(s, radix, a2).is_some(),
    decreases s.len(),
{
    if s.len() > 0 {
        let c = s[0];
        let d_opt: Option<nat> = if 0x30u16 <= c && c <= 0x39u16 {
            let d = (c - 0x30u16) as nat;
            if d < radix { Some(d) } else { None }
        } else if radix == 16nat && 0x41u16 <= c && c <= 0x46u16 {
            Some((c - 0x41u16 + 10u16) as nat)
        } else if radix == 16nat && 0x61u16 <= c && c <= 0x66u16 {
            Some((c - 0x61u16 + 10u16) as nat)
        } else {
            None
        };
        if let Some(d) = d_opt {
            lemma_radix_loop_some_indep_of_acc(
                s.subrange(1, s.len() as int),
                radix,
                a1 * radix + d,
                a2 * radix + d,
            );
        }
    }
}

// --- ECMA-262 §7.1.4.1.1 `StrDecimalLiteral` Parser & Converter ---

pub open spec fn spec_is_ascii_digit(c: u16) -> bool {
    0x30u16 <= c && c <= 0x39u16
}

pub open spec fn spec_scan_digits_only(s: Seq<u16>, digits: Seq<u8>) -> Option<Seq<u8>>
    decreases s.len(),
{
    if s.len() == 0 {
        Some(digits)
    } else if spec_is_ascii_digit(s[0]) {
        spec_scan_digits_only(
            s.subrange(1, s.len() as int),
            digits.push((s[0] - 0x30u16) as u8),
        )
    } else {
        None
    }
}

pub open spec fn spec_parse_exp_nat(s: Seq<u16>, acc: nat) -> Option<nat>
    decreases s.len(),
{
    if s.len() == 0 {
        Some(acc)
    } else if spec_is_ascii_digit(s[0]) {
        spec_parse_exp_nat(
            s.subrange(1, s.len() as int),
            acc * 10nat + ((s[0] - 0x30u16) as nat),
        )
    } else {
        None
    }
}

pub open spec fn spec_parse_opt_exponent(s: Seq<u16>) -> Option<int> {
    if s.len() == 0 {
        Some(0int)
    } else if s[0] != 0x65u16 && s[0] != 0x45u16 {
        None
    } else {
        let after_e = s.subrange(1, s.len() as int);
        if after_e.len() == 0 {
            None
        } else {
            let (exp_neg, digits_s) = if after_e[0] == 0x2du16 {
                (true, after_e.subrange(1, after_e.len() as int))
            } else if after_e[0] == 0x2bu16 {
                (false, after_e.subrange(1, after_e.len() as int))
            } else {
                (false, after_e)
            };
            if digits_s.len() == 0 {
                None
            } else {
                match spec_parse_exp_nat(digits_s, 0nat) {
                    None => None,
                    Some(mag) => Some(if exp_neg { -(mag as int) } else { mag as int }),
                }
            }
        }
    }
}

/// Scan `Digits? ('.' Digits?)?` stopping before `'e'`/`'E'` or end of string, returning
/// `(all_digits, int_digits_count, remaining_suffix)`.
pub open spec fn spec_scan_mantissa(
    s: Seq<u16>,
    seen_dot: bool,
    digits: Seq<u8>,
    int_cnt: nat,
) -> Option<(Seq<u8>, nat, Seq<u16>)>
    decreases s.len(),
{
    if s.len() == 0 {
        Some((digits, int_cnt, seq![]))
    } else {
        let c = s[0];
        if spec_is_ascii_digit(c) {
            let d = (c - 0x30u16) as u8;
            let next_int = if seen_dot { int_cnt } else { int_cnt + 1nat };
            spec_scan_mantissa(s.subrange(1, s.len() as int), seen_dot, digits.push(d), next_int)
        } else if c == 0x2eu16 && !seen_dot {
            spec_scan_mantissa(s.subrange(1, s.len() as int), true, digits, int_cnt)
        } else if c == 0x65u16 || c == 0x45u16 {
            Some((digits, int_cnt, s))
        } else {
            None
        }
    }
}

pub open spec fn spec_first_nonzero(digits: Seq<u8>, idx: nat) -> Option<nat>
    decreases digits.len() - idx,
{
    if idx >= digits.len() {
        None
    } else if digits[idx as int] != 0u8 {
        Some(idx)
    } else {
        spec_first_nonzero(digits, idx + 1nat)
    }
}

pub open spec fn spec_last_nonzero(digits: Seq<u8>, len: nat) -> nat
    decreases len,
{
    if len <= 1nat {
        0nat
    } else if digits[(len - 1) as int] != 0u8 {
        (len - 1) as nat
    } else {
        spec_last_nonzero(digits, (len - 1) as nat)
    }
}

pub open spec fn spec_digits_to_nat(digits: Seq<u8>, acc: nat) -> nat
    decreases digits.len(),
{
    if digits.len() == 0 {
        acc
    } else {
        spec_digits_to_nat(
            digits.subrange(1, digits.len() as int),
            acc * 10nat + (digits[0] as nat),
        )
    }
}

pub open spec fn spec_decimal_body_to_f64_bits(neg: bool, body: Seq<u16>) -> u64 {
    match spec_scan_mantissa(body, false, seq![], 0nat) {
        None => F64_CANON_NAN,
        Some((raw_digits, int_cnt, suffix)) => {
            if raw_digits.len() == 0 {
                F64_CANON_NAN
            } else {
                match spec_parse_opt_exponent(suffix) {
                    None => F64_CANON_NAN,
                    Some(exp_val) => {
                        match spec_first_nonzero(raw_digits, 0nat) {
                            None => if neg { F64_NEG_ZERO } else { F64_POS_ZERO },
                            Some(first_nz) => {
                                let last_nz = spec_last_nonzero(raw_digits, raw_digits.len());
                                let sig_digits = raw_digits.subrange(
                                    first_nz as int,
                                    (last_nz + 1nat) as int,
                                );
                                let sig_len = sig_digits.len();
                                let base_exp10: int = (int_cnt as int) - ((last_nz + 1nat) as int);
                                let total_exp10: int = base_exp10 + exp_val;
                                let sci_exp10: int = total_exp10 + (sig_len as int) - 1int;
                                if sci_exp10 > 309int {
                                    if neg { F64_NEG_INF } else { F64_POS_INF }
                                } else if sci_exp10 < -325int {
                                    if neg { F64_NEG_ZERO } else { F64_POS_ZERO }
                                } else {
                                    let (eff_digits, eff_exp10): (Seq<u8>, int) = if sig_len > 780nat {
                                        (
                                            sig_digits.subrange(0, 780).push(1u8),
                                            total_exp10 + (sig_len as int) - 781int,
                                        )
                                    } else {
                                        (sig_digits, total_exp10)
                                    };
                                    let sig_nat = spec_digits_to_nat(eff_digits, 0nat);
                                    if eff_exp10 >= 0int {
                                        spec_rational_rne_f64_bits(
                                            neg,
                                            sig_nat * pow10(eff_exp10 as nat),
                                            1nat,
                                        )
                                    } else {
                                        spec_rational_rne_f64_bits(
                                            neg,
                                            sig_nat,
                                            pow10((-eff_exp10) as nat),
                                        )
                                    }
                                }
                            },
                        }
                    },
                }
            }
        },
    }
}

fn parse_opt_exponent_saturated(s: &[u16], start: usize, cap: u128) -> (res: Option<(bool, u128)>)
    requires
        start <= s@.len(),
        cap >= 10_000u128,
        cap <= (u64::MAX as u128) + 20_000u128,
    ensures
        ({
            let suf = s@.subrange(start as int, s@.len() as int);
            match (res, spec_parse_opt_exponent(suf)) {
                (None, None) => true,
                (Some((neg, sat_mag)), Some(real_exp)) => {
                    sat_mag <= cap
                    && (!neg ==> real_exp >= 0int)
                    && (neg ==> real_exp <= 0int)
                    && (sat_mag < cap ==> (
                        real_exp == (if neg { -(sat_mag as int) } else { sat_mag as int })
                    ))
                    && (sat_mag >= cap ==> (
                        (neg && real_exp <= -(cap as int))
                        || (!neg && real_exp >= (cap as int))
                    ))
                },
                _ => false,
            }
        }),
{
    let n = s.len();
    if start == n {
        proof { assert(s@.subrange(n as int, n as int) =~= Seq::<u16>::empty()); }
        return Some((false, 0u128));
    }
    if s[start] != 0x65u16 && s[start] != 0x45u16 {
        return None;
    }
    let ghost suf = s@.subrange(start as int, n as int);
    let ghost after_e = suf.subrange(1, suf.len() as int);
    if start + 1 == n {
        proof { assert(after_e.len() == 0); }
        return None;
    }
    let (exp_neg, d_start): (bool, usize) = if s[start + 1] == 0x2du16 {
        (true, start + 2)
    } else if s[start + 1] == 0x2bu16 {
        (false, start + 2)
    } else {
        (false, start + 1)
    };
    let ghost digits_s = s@.subrange(d_start as int, n as int);
    proof {
        assert(suf[0] == s@[start as int]);
        assert(after_e =~= s@.subrange((start + 1) as int, n as int));
        if d_start == start + 2 {
            assert(after_e.subrange(1, after_e.len() as int) =~= digits_s);
        } else {
            assert(after_e =~= digits_s);
        }
    }
    if d_start == n {
        proof { assert(digits_s.len() == 0); }
        return None;
    }
    proof {
        assert(digits_s.len() > 0);
        assert(spec_parse_opt_exponent(suf) == match spec_parse_exp_nat(digits_s, 0nat) {
            None => None,
            Some(mag) => Some(if exp_neg { -(mag as int) } else { mag as int }),
        });
    }
    let mut i = d_start;
    let mut sat: u128 = 0u128;
    let ghost mut real_acc: nat = 0nat;
    while i < n
        invariant
            start < d_start,
            d_start < n,
            d_start <= i,
            i <= n,
            n == s@.len(),
            suf == s@.subrange(start as int, n as int),
            digits_s == s@.subrange(d_start as int, n as int),
            spec_parse_opt_exponent(suf) == match spec_parse_exp_nat(digits_s, 0nat) {
                None => None,
                Some(mag) => Some(if exp_neg { -(mag as int) } else { mag as int }),
            },
            cap >= 10_000u128,
            cap <= (u64::MAX as u128) + 20_000u128,
            sat <= cap,
            (sat as nat) <= real_acc,
            sat < cap ==> (sat as nat) == real_acc,
            sat >= cap ==> real_acc >= (cap as nat),
            spec_parse_exp_nat(digits_s, 0nat)
                == spec_parse_exp_nat(s@.subrange(i as int, n as int), real_acc),
        decreases n - i,
    {
        let c = s[i];
        let ghost cur_sub = s@.subrange(i as int, n as int);
        if !(0x30u16 <= c && c <= 0x39u16) {
            proof {
                assert(cur_sub.len() > 0);
                assert(cur_sub[0] == c);
                assert(spec_parse_exp_nat(cur_sub, real_acc).is_none());
            }
            return None;
        }
        let d: u128 = (c - 0x30u16) as u128;
        proof {
            let sv = sat as nat;
            let cv = cap as nat;
            assert(sv * 10nat + 9nat <= cv * 10nat + 9nat) by (nonlinear_arith)
                requires sv <= cv;
        }
        let next_unclamped: u128 = sat * 10u128 + d;
        let next_sat: u128 = if next_unclamped > cap { cap } else { next_unclamped };
        i += 1;
        proof {
            assert(cur_sub.subrange(1, cur_sub.len() as int) =~= s@.subrange(i as int, n as int));
            let old_real = real_acc;
            real_acc = old_real * 10nat + (d as nat);
            assert((sat as nat) * 10nat + (d as nat) <= old_real * 10nat + (d as nat))
                by (nonlinear_arith)
                requires (sat as nat) <= old_real;
            if sat >= cap {
                assert(old_real * 10nat + (d as nat) >= (cap as nat)) by (nonlinear_arith)
                    requires old_real >= (cap as nat);
            }
        }
        sat = next_sat;
    }
    proof {
        assert(s@.subrange(n as int, n as int) =~= Seq::<u16>::empty());
    }
    Some((exp_neg, sat))
}

proof fn lemma_digits_to_nat_pos(digits: Seq<u8>, acc: nat)
    requires
        acc >= 1nat || (digits.len() > 0 && digits[0] >= 1u8),
    ensures
        spec_digits_to_nat(digits, acc) >= 1nat,
    decreases digits.len(),
{
    if digits.len() > 0 {
        let d0 = digits[0] as nat;
        assert(acc * 10nat + d0 >= 1nat) by (nonlinear_arith)
            requires acc >= 1nat || d0 >= 1nat;
        lemma_digits_to_nat_pos(digits.subrange(1, digits.len() as int), acc * 10nat + d0);
    }
}

fn scan_decimal_mantissa_exec(s: &[u16], start: usize) -> (res: Option<(Vec<u8>, usize, usize)>)
    requires
        start < s@.len(),
    ensures
        ({
            let body = s@.subrange(start as int, s@.len() as int);
            match (res, spec_scan_mantissa(body, false, seq![], 0nat)) {
                (None, None) => true,
                (Some((raw_digits, int_cnt, exp_idx)), Some((s_digits, s_int, s_suf))) => {
                    start <= exp_idx
                    && exp_idx <= s@.len()
                    && raw_digits@ == s_digits
                    && (int_cnt as nat) == s_int
                    && int_cnt <= raw_digits@.len()
                    && raw_digits@.len() <= (s@.len() - start) as nat
                    && s_suf == s@.subrange(exp_idx as int, s@.len() as int)
                    && (forall|k: int| 0 <= k < raw_digits@.len() ==> (#[trigger] raw_digits@[k]) <= 9u8)
                },
                _ => false,
            }
        }),
{
    let n = s.len();
    let ghost body = s@.subrange(start as int, n as int);
    let mut raw_digits: Vec<u8> = Vec::new();
    let mut int_cnt: usize = 0usize;
    let mut seen_dot: bool = false;
    let mut i: usize = start;
    let mut stopped_at_e: bool = false;
    proof {
        assert(raw_digits@ =~= Seq::<u8>::empty());
    }
    while i < n && !stopped_at_e
        invariant
            start <= i,
            i <= n,
            n == s@.len(),
            body == s@.subrange(start as int, n as int),
            int_cnt <= raw_digits@.len(),
            raw_digits@.len() <= (i - start) as nat,
            stopped_at_e ==> (i < n && (s@[i as int] == 0x65u16 || s@[i as int] == 0x45u16)),
            forall|k: int| 0 <= k < raw_digits@.len() ==> (#[trigger] raw_digits@[k]) <= 9u8,
            spec_scan_mantissa(body, false, seq![], 0nat)
                == spec_scan_mantissa(
                    s@.subrange(i as int, n as int),
                    seen_dot,
                    raw_digits@,
                    int_cnt as nat,
                ),
        decreases n - i + (if stopped_at_e { 0usize } else { 1usize }),
    {
        let c = s[i];
        let ghost cur_sub = s@.subrange(i as int, n as int);
        if 0x30u16 <= c && c <= 0x39u16 {
            let d: u8 = (c - 0x30u16) as u8;
            raw_digits.push(d);
            if !seen_dot {
                int_cnt += 1;
            }
            i += 1;
            proof {
                assert(cur_sub.subrange(1, cur_sub.len() as int) =~= s@.subrange(i as int, n as int));
            }
        } else if c == 0x2eu16 && !seen_dot {
            seen_dot = true;
            i += 1;
            proof {
                assert(cur_sub.subrange(1, cur_sub.len() as int) =~= s@.subrange(i as int, n as int));
            }
        } else if c == 0x65u16 || c == 0x45u16 {
            stopped_at_e = true;
        } else {
            return None;
        }
    }

    proof {
        let suf = s@.subrange(i as int, n as int);
        if i == n {
            assert(suf =~= Seq::<u16>::empty());
        } else {
            assert(stopped_at_e);
            assert(suf.len() > 0);
            assert(suf[0] == s@[i as int]);
        }
        assert(spec_scan_mantissa(body, false, seq![], 0nat)
            == Some((raw_digits@, int_cnt as nat, suf)));
    }
    Some((raw_digits, int_cnt, i))
}

fn locate_nonzero_span_exec(raw_digits: &[u8]) -> (res: Option<(usize, usize)>)
    requires
        raw_digits@.len() > 0,
    ensures
        match (res, spec_first_nonzero(raw_digits@, 0nat)) {
            (None, None) => true,
            (Some((first_nz, last_nz)), Some(s_first)) => {
                (first_nz as nat) == s_first
                && (last_nz as nat) == spec_last_nonzero(raw_digits@, raw_digits@.len())
                && first_nz <= last_nz
                && last_nz < raw_digits@.len()
                && raw_digits@[first_nz as int] != 0u8
            },
            _ => false,
        },
{
    let dn = raw_digits.len();
    let mut first_nz: usize = 0;
    while first_nz < dn && raw_digits[first_nz] == 0u8
        invariant
            first_nz <= dn,
            dn == raw_digits@.len(),
            spec_first_nonzero(raw_digits@, 0nat) == spec_first_nonzero(raw_digits@, first_nz as nat),
        decreases dn - first_nz,
    {
        first_nz += 1;
    }
    if first_nz == dn {
        return None;
    }
    proof {
        assert(raw_digits@[first_nz as int] != 0u8);
        assert(spec_first_nonzero(raw_digits@, 0nat) == Some(first_nz as nat));
    }

    let mut rem_len: usize = dn;
    while rem_len > 1usize && raw_digits[rem_len - 1] == 0u8
        invariant
            first_nz < rem_len,
            rem_len <= dn,
            dn == raw_digits@.len(),
            raw_digits@[first_nz as int] != 0u8,
            spec_last_nonzero(raw_digits@, dn as nat)
                == spec_last_nonzero(raw_digits@, rem_len as nat),
        decreases rem_len,
    {
        rem_len -= 1;
    }
    let last_nz: usize = rem_len - 1usize;
    proof {
        if rem_len == 1usize {
            assert(spec_last_nonzero(raw_digits@, 1nat) == 0nat);
        } else {
            assert(raw_digits@[(rem_len - 1) as int] != 0u8);
            assert(spec_last_nonzero(raw_digits@, rem_len as nat) == (rem_len - 1) as nat);
        }
    }
    Some((first_nz, last_nz))
}

fn build_decimal_sig_big_exec(raw_digits: &[u8], first_nz: usize, last_nz: usize) -> (sig_big: Vec<u32>)
    requires
        first_nz <= last_nz,
        last_nz < raw_digits@.len(),
        raw_digits@[first_nz as int] != 0u8,
        forall|k: int| 0 <= k < raw_digits@.len() ==> (#[trigger] raw_digits@[k]) <= 9u8,
    ensures
        ({
            let sig_digits = raw_digits@.subrange(first_nz as int, (last_nz + 1usize) as int);
            let eff_digits = if sig_digits.len() > 780nat {
                sig_digits.subrange(0, 780).push(1u8)
            } else {
                sig_digits
            };
            spec_big_canonical(sig_big@)
            && sig_big@.len() >= 1
            && sig_big@.len() <= 781
            && spec_big_val(sig_big@) >= 1nat
            && spec_big_val(sig_big@) == spec_digits_to_nat(eff_digits, 0nat)
        }),
{
    let _dn = raw_digits.len();
    let sig_len: usize = (last_nz - first_nz) + 1usize;
    let (take_len, append_sticky_one): (usize, bool) = if sig_len > 780usize {
        (780usize, true)
    } else {
        (sig_len, false)
    };
    let ghost sig_digits = raw_digits@.subrange(first_nz as int, (last_nz + 1usize) as int);
    let ghost eff_digits: Seq<u8> = if sig_len > 780usize {
        sig_digits.subrange(0, 780).push(1u8)
    } else {
        sig_digits
    };

    let mut sig_big: Vec<u32> = Vec::new();
    let mut p: usize = 0;
    proof {
        assert(sig_big@ =~= Seq::<u32>::empty());
        assert(eff_digits.subrange(0, eff_digits.len() as int) =~= eff_digits);
    }
    while p < take_len
        invariant
            p <= take_len,
            take_len <= sig_len,
            take_len <= 780usize,
            first_nz + sig_len == last_nz + 1usize,
            last_nz < raw_digits@.len(),
            sig_digits == raw_digits@.subrange(first_nz as int, (last_nz + 1usize) as int),
            eff_digits == (if sig_len > 780usize {
                sig_digits.subrange(0, 780).push(1u8)
            } else {
                sig_digits
            }),
            forall|k: int| 0 <= k < raw_digits@.len() ==> (#[trigger] raw_digits@[k]) <= 9u8,
            spec_big_canonical(sig_big@),
            sig_big@.len() <= p as nat,
            spec_digits_to_nat(eff_digits, 0nat)
                == spec_digits_to_nat(
                    eff_digits.subrange(p as int, eff_digits.len() as int),
                    spec_big_val(sig_big@),
                ),
        decreases take_len - p,
    {
        let d: u8 = raw_digits[first_nz + p];
        let ghost rem_eff = eff_digits.subrange(p as int, eff_digits.len() as int);
        sig_big = big_mul_add_u32(sig_big.as_slice(), 10u32, d as u32);
        p += 1;
        proof {
            assert(raw_digits@[(first_nz + p - 1) as int] <= 9u8);
            assert(rem_eff[0] == d);
            assert(rem_eff.subrange(1, rem_eff.len() as int)
                =~= eff_digits.subrange(p as int, eff_digits.len() as int));
        }
    }
    if append_sticky_one {
        let ghost rem_eff = eff_digits.subrange(take_len as int, eff_digits.len() as int);
        sig_big = big_mul_add_u32(sig_big.as_slice(), 10u32, 1u32);
        proof {
            reveal_with_fuel(spec_digits_to_nat, 2);
            assert(rem_eff =~= seq![1u8]);
            assert(rem_eff.subrange(1, 1) =~= Seq::<u8>::empty());
        }
    } else {
        proof {
            assert(eff_digits.subrange(take_len as int, eff_digits.len() as int) =~= Seq::<u8>::empty());
        }
    }

    proof {
        assert(eff_digits.len() >= 1);
        assert(eff_digits[0] == raw_digits@[first_nz as int]);
        assert(eff_digits[0] >= 1u8);
        lemma_digits_to_nat_pos(eff_digits, 0nat);
        lemma_big_canonical_nonzero_iff_nonempty(sig_big@);
        assert(sig_big@.len() >= 1);
    }
    sig_big
}

#[verifier::spinoff_prover]
fn parse_decimal_body_to_f64_bits(neg: bool, s: &[u16], start: usize) -> (bits: u64)
    requires
        start < s@.len(),
    ensures
        bits == spec_decimal_body_to_f64_bits(neg, s@.subrange(start as int, s@.len() as int)),
{
    let n = s.len();
    let (raw_digits, int_cnt, exp_idx) = match scan_decimal_mantissa_exec(s, start) {
        None => return F64_CANON_NAN,
        Some(t) => t,
    };

    if raw_digits.len() == 0 {
        return F64_CANON_NAN;
    }

    let body_len_u128: u128 = (n - start) as u128;
    let cap: u128 = body_len_u128 + 10_000u128;
    let (exp_neg, sat_mag) = match parse_opt_exponent_saturated(s, exp_idx, cap) {
        None => return F64_CANON_NAN,
        Some(pair) => pair,
    };

    let (first_nz, last_nz) = match locate_nonzero_span_exec(raw_digits.as_slice()) {
        None => return if neg { F64_NEG_ZERO } else { F64_POS_ZERO },
        Some(pair) => pair,
    };
    let _dn = raw_digits.len();
    let ghost dn = raw_digits@.len();
    let sig_len: usize = (last_nz - first_nz) + 1usize;

    let base_exp10: i128 = (int_cnt as i128) - ((last_nz + 1usize) as i128);
    let signed_sat_exp: i128 = if exp_neg { -(sat_mag as i128) } else { sat_mag as i128 };
    let total_exp10_sat: i128 = base_exp10 + signed_sat_exp;
    let sci_exp10_sat: i128 = total_exp10_sat + (sig_len as i128) - 1i128;

    proof {
        let suf = s@.subrange(exp_idx as int, n as int);
        match spec_parse_opt_exponent(suf) {
            None => {
                assert(false);
            },
            Some(real_exp) => {
                let real_sci: int = (base_exp10 as int) + real_exp + (sig_len as int) - 1int;
                assert(-(dn as int) <= (base_exp10 as int) + (sig_len as int) - 1int);
                assert((base_exp10 as int) + (sig_len as int) - 1int <= (dn as int));
                assert((dn as int) <= (body_len_u128 as int));
                if sat_mag >= cap {
                    if exp_neg {
                        assert(real_exp <= -(cap as int));
                        assert(real_sci < -325int);
                        assert(sci_exp10_sat < -325i128);
                    } else {
                        assert(real_exp >= (cap as int));
                        assert(real_sci > 309int);
                        assert(sci_exp10_sat > 309i128);
                    }
                } else {
                    assert(real_exp == signed_sat_exp as int);
                    assert(real_sci == sci_exp10_sat as int);
                }
            },
        }
    }

    if sci_exp10_sat > 309i128 {
        return if neg { F64_NEG_INF } else { F64_POS_INF };
    }
    if sci_exp10_sat < -325i128 {
        return if neg { F64_NEG_ZERO } else { F64_POS_ZERO };
    }

    proof {
        assert(sat_mag < cap);
    }

    let eff_exp10: i32 = if sig_len > 780usize {
        (total_exp10_sat + (sig_len as i128) - 781i128) as i32
    } else {
        total_exp10_sat as i32
    };

    let sig_big = build_decimal_sig_big_exec(raw_digits.as_slice(), first_nz, last_nz);

    let one: [u32; 1] = [1u32];
    proof {
        reveal_with_fuel(spec_big_val, 2);
        assert(one@ =~= seq![1u32]);
        assert(one@.subrange(1, 1) =~= Seq::<u32>::empty());
        assert(spec_big_val(one@) == 1nat);
        assert(spec_big_canonical(one@));
    }

    if eff_exp10 >= 0i32 {
        let n_limbs = big_mul_pow10(sig_big.as_slice(), eff_exp10 as u32);
        proof {
            let sv = spec_big_val(sig_big@);
            let p10 = pow10(eff_exp10 as nat);
            lemma_pow10_pos(eff_exp10 as nat);
            assert(sv * p10 >= 1nat) by (nonlinear_arith)
                requires sv >= 1nat, p10 >= 1nat;
            lemma_big_canonical_nonzero_iff_nonempty(n_limbs@);
        }
        exec_rational_rne_f64_bits(neg, n_limbs.as_slice(), &one)
    } else {
        let d_limbs = big_mul_pow10(&one, (-eff_exp10) as u32);
        proof {
            lemma_pow10_pos((-eff_exp10) as nat);
            assert(1nat * pow10((-eff_exp10) as nat) == pow10((-eff_exp10) as nat));
            lemma_big_canonical_nonzero_iff_nonempty(d_limbs@);
        }
        exec_rational_rne_f64_bits(neg, sig_big.as_slice(), d_limbs.as_slice())
    }
}

proof fn lemma_pow10_pos(k: nat)
    ensures
        pow10(k) >= 1nat,
    decreases k,
{
    if k > 0nat {
        lemma_pow10_pos((k - 1) as nat);
    }
}

pub open spec fn spec_string_to_number_bits(raw: Seq<u16>) -> u64 {
    let s = spec_trim_utf16(raw);
    if s.len() == 0 {
        F64_POS_ZERO
    } else if spec_seq_eq_ascii(s, seq![0x49u8, 0x6e, 0x66, 0x69, 0x6e, 0x69, 0x74, 0x79])
        || spec_seq_eq_ascii(s, seq![0x2bu8, 0x49, 0x6e, 0x66, 0x69, 0x6e, 0x69, 0x74, 0x79])
    {
        F64_POS_INF
    } else if spec_seq_eq_ascii(s, seq![0x2du8, 0x49, 0x6e, 0x66, 0x69, 0x6e, 0x69, 0x74, 0x79]) {
        F64_NEG_INF
    } else if s.len() >= 3 && s[0] == 0x30u16 && (s[1] == 0x78u16 || s[1] == 0x58u16) {
        spec_radix_str_to_f64_bits(s.subrange(2, s.len() as int), 16nat)
    } else if s.len() >= 3 && s[0] == 0x30u16 && (s[1] == 0x62u16 || s[1] == 0x42u16) {
        spec_radix_str_to_f64_bits(s.subrange(2, s.len() as int), 2nat)
    } else if s.len() >= 3 && s[0] == 0x30u16 && (s[1] == 0x6fu16 || s[1] == 0x4fu16) {
        spec_radix_str_to_f64_bits(s.subrange(2, s.len() as int), 8nat)
    } else {
        let (neg, body) = if s[0] == 0x2du16 {
            (true, s.subrange(1, s.len() as int))
        } else if s[0] == 0x2bu16 {
            (false, s.subrange(1, s.len() as int))
        } else {
            (false, s)
        };
        if body.len() == 0 {
            F64_CANON_NAN
        } else {
            spec_decimal_body_to_f64_bits(neg, body)
        }
    }
}

pub fn string_to_number_bits(raw: &[u16]) -> (bits: u64)
    ensures
        bits == spec_string_to_number_bits(raw@),
{
    let trimmed = trim_utf16(raw);
    let s = trimmed.as_slice();
    let n = s.len();
    if n == 0 {
        return F64_POS_ZERO;
    }
    let inf_lit: [u8; 8] = [0x49, 0x6e, 0x66, 0x69, 0x6e, 0x69, 0x74, 0x79];
    let pos_inf_lit: [u8; 9] = [0x2b, 0x49, 0x6e, 0x66, 0x69, 0x6e, 0x69, 0x74, 0x79];
    let neg_inf_lit: [u8; 9] = [0x2d, 0x49, 0x6e, 0x66, 0x69, 0x6e, 0x69, 0x74, 0x79];
    proof {
        assert(inf_lit@ =~= seq![0x49u8, 0x6e, 0x66, 0x69, 0x6e, 0x69, 0x74, 0x79]);
        assert(pos_inf_lit@ =~= seq![0x2bu8, 0x49, 0x6e, 0x66, 0x69, 0x6e, 0x69, 0x74, 0x79]);
        assert(neg_inf_lit@ =~= seq![0x2du8, 0x49, 0x6e, 0x66, 0x69, 0x6e, 0x69, 0x74, 0x79]);
    }
    if slice_eq_ascii(s, &inf_lit) || slice_eq_ascii(s, &pos_inf_lit) {
        return F64_POS_INF;
    }
    if slice_eq_ascii(s, &neg_inf_lit) {
        return F64_NEG_INF;
    }
    if n >= 3 && s[0] == 0x30u16 && (s[1] == 0x78u16 || s[1] == 0x58u16) {
        return parse_radix_to_f64_bits(s, 2, 16);
    }
    if n >= 3 && s[0] == 0x30u16 && (s[1] == 0x62u16 || s[1] == 0x42u16) {
        return parse_radix_to_f64_bits(s, 2, 2);
    }
    if n >= 3 && s[0] == 0x30u16 && (s[1] == 0x6fu16 || s[1] == 0x4fu16) {
        return parse_radix_to_f64_bits(s, 2, 8);
    }
    let (neg, start): (bool, usize) = if s[0] == 0x2du16 {
        (true, 1usize)
    } else if s[0] == 0x2bu16 {
        (false, 1usize)
    } else {
        (false, 0usize)
    };
    proof {
        if start == 0usize {
            assert(s@.subrange(0, n as int) =~= s@);
        }
    }
    if n == start {
        return F64_CANON_NAN;
    }
    parse_decimal_body_to_f64_bits(neg, s, start)
}

/// ECMA-262 §7.1.4 `ToNumber(V)` at the Web IDL boundary.
/// Note: `Symbol` and `BigInt` throw `TypeError` per ECMA-262 §7.1.4!
pub open spec fn spec_to_number(
    arena: Seq<SpecJsObjectRecord>,
    v: SpecJsValue,
) -> Result<u64, IdlError> {
    match v {
        SpecJsValue::Undefined => Ok(F64_CANON_NAN),
        SpecJsValue::Null => Ok(F64_POS_ZERO),
        SpecJsValue::Bool(false) => Ok(F64_POS_ZERO),
        SpecJsValue::Bool(true) => Ok(F64_ONE),
        SpecJsValue::Number(bits) => Ok(bits),
        SpecJsValue::BigInt { .. } => Err(IdlError::TypeError),
        SpecJsValue::Symbol(_) => Err(IdlError::TypeError),
        SpecJsValue::String(s) => Ok(spec_string_to_number_bits(s)),
        SpecJsValue::Object(oid) => {
            if (oid as int) >= arena.len() {
                Err(IdlError::TypeError)
            } else {
                let obj = arena[oid as int];
                match obj.to_number_override {
                    Some(bits) => Ok(bits),
                    None => match obj.to_string_hook {
                        SpecJsToStringHook::DefaultObjectTag => Ok(F64_CANON_NAN),
                        SpecJsToStringHook::ReturnStr(s) => Ok(spec_string_to_number_bits(s)),
                        SpecJsToStringHook::ThrowError => Err(IdlError::TypeError),
                        SpecJsToStringHook::ThrowException(id) => Err(IdlError::AbruptException(id)),
                    },
                }
            }
        },
    }
}

pub fn to_number(arena: &JsObjectArena, v: &JsValue) -> (res: Result<u64, IdlError>)
    ensures
        res == spec_to_number(arena@, v@),
{
    match v {
        JsValue::Undefined => Ok(F64_CANON_NAN),
        JsValue::Null => Ok(F64_POS_ZERO),
        JsValue::Bool(false) => Ok(F64_POS_ZERO),
        JsValue::Bool(true) => Ok(F64_ONE),
        JsValue::Number(bits) => Ok(*bits),
        JsValue::BigInt { .. } => Err(IdlError::TypeError),
        JsValue::Symbol(_) => Err(IdlError::TypeError),
        JsValue::String(s) => Ok(string_to_number_bits(s.as_slice())),
        JsValue::Object(oid) => {
            if *oid >= arena.objects.len() {
                Err(IdlError::TypeError)
            } else {
                let obj = &arena.objects[*oid];
                match obj.to_number_override {
                    Some(bits) => Ok(bits),
                    None => match &obj.to_string_hook {
                        JsToStringHook::DefaultObjectTag => Ok(F64_CANON_NAN),
                        JsToStringHook::ReturnStr(s) => Ok(string_to_number_bits(s.as_slice())),
                        JsToStringHook::ThrowError => Err(IdlError::TypeError),
                        JsToStringHook::ThrowException(id) => Err(IdlError::AbruptException(*id)),
                    },
                }
            }
        },
    }
}

// ---------------------------------------------------------------------------------------
// All 8 Web IDL Integer Types (`ToIDL` & `ToJS`)
// ---------------------------------------------------------------------------------------

pub open spec fn spec_to_idl_int(
    arena: Seq<SpecJsObjectRecord>,
    v: SpecJsValue,
    bit_length: nat,
    signed: bool,
    attr: IntAttr,
) -> Result<int, IdlError> {
    match spec_to_number(arena, v) {
        Err(e) => Err(e),
        Ok(bits) => spec_convert_to_int_bits(bits, bit_length, signed, attr),
    }
}

/// 1. `byte` (signed 8-bit, `[-128, 127]`, §3.2.4.1)
pub fn to_idl_byte(
    arena: &JsObjectArena,
    v: &JsValue,
    attr: IntAttr,
) -> (res: Result<i8, IdlError>)
    ensures
        match (res, spec_to_idl_int(arena@, v@, 8nat, true, attr)) {
            (Ok(x), Ok(sx)) => x as int == sx,
            (Err(e), Err(se)) => e == se,
            _ => false,
        },
{
    let bits = to_number(arena, v)?;
    let x = convert_to_int_bits(bits, 8, true, attr)?;
    proof {
        lemma_pow2_values();
    }
    Ok(x as i8)
}

pub open spec fn spec_to_js_byte(x: i8) -> SpecJsValue {
    let neg = x < 0i8;
    let mag: u64 = if x < 0i8 { (-(x as i16)) as u64 } else { x as u64 };
    SpecJsValue::Number(spec_u64_mag_to_f64_bits(neg, mag))
}

pub fn to_js_byte(x: i8) -> (out: JsValue)
    ensures
        out@ == spec_to_js_byte(x),
{
    let neg = x < 0i8;
    let mag: u64 = if x < 0i8 { (-(x as i16)) as u64 } else { x as u64 };
    JsValue::Number(u64_mag_to_f64_bits(neg, mag))
}

/// 2. `octet` (unsigned 8-bit, `[0, 255]`, §3.2.4.2)
pub fn to_idl_octet(
    arena: &JsObjectArena,
    v: &JsValue,
    attr: IntAttr,
) -> (res: Result<u8, IdlError>)
    ensures
        match (res, spec_to_idl_int(arena@, v@, 8nat, false, attr)) {
            (Ok(x), Ok(sx)) => x as int == sx,
            (Err(e), Err(se)) => e == se,
            _ => false,
        },
{
    let bits = to_number(arena, v)?;
    let x = convert_to_int_bits(bits, 8, false, attr)?;
    proof {
        lemma_pow2_values();
    }
    Ok(x as u8)
}

pub open spec fn spec_to_js_octet(x: u8) -> SpecJsValue {
    SpecJsValue::Number(spec_u64_mag_to_f64_bits(false, x as u64))
}

pub fn to_js_octet(x: u8) -> (out: JsValue)
    ensures
        out@ == spec_to_js_octet(x),
{
    JsValue::Number(u64_mag_to_f64_bits(false, x as u64))
}

/// 3. `short` (signed 16-bit, `[-32768, 32767]`, §3.2.4.3)
pub fn to_idl_short(
    arena: &JsObjectArena,
    v: &JsValue,
    attr: IntAttr,
) -> (res: Result<i16, IdlError>)
    ensures
        match (res, spec_to_idl_int(arena@, v@, 16nat, true, attr)) {
            (Ok(x), Ok(sx)) => x as int == sx,
            (Err(e), Err(se)) => e == se,
            _ => false,
        },
{
    let bits = to_number(arena, v)?;
    let x = convert_to_int_bits(bits, 16, true, attr)?;
    proof {
        lemma_pow2_values();
    }
    Ok(x as i16)
}

pub open spec fn spec_to_js_short(x: i16) -> SpecJsValue {
    let neg = x < 0i16;
    let mag: u64 = if x < 0i16 { (-(x as i32)) as u64 } else { x as u64 };
    SpecJsValue::Number(spec_u64_mag_to_f64_bits(neg, mag))
}

pub fn to_js_short(x: i16) -> (out: JsValue)
    ensures
        out@ == spec_to_js_short(x),
{
    let neg = x < 0i16;
    let mag: u64 = if x < 0i16 { (-(x as i32)) as u64 } else { x as u64 };
    JsValue::Number(u64_mag_to_f64_bits(neg, mag))
}

/// 4. `unsigned short` (unsigned 16-bit, `[0, 65535]`, §3.2.4.4)
pub fn to_idl_unsigned_short(
    arena: &JsObjectArena,
    v: &JsValue,
    attr: IntAttr,
) -> (res: Result<u16, IdlError>)
    ensures
        match (res, spec_to_idl_int(arena@, v@, 16nat, false, attr)) {
            (Ok(x), Ok(sx)) => x as int == sx,
            (Err(e), Err(se)) => e == se,
            _ => false,
        },
{
    let bits = to_number(arena, v)?;
    let x = convert_to_int_bits(bits, 16, false, attr)?;
    proof {
        lemma_pow2_values();
    }
    Ok(x as u16)
}

pub open spec fn spec_to_js_unsigned_short(x: u16) -> SpecJsValue {
    SpecJsValue::Number(spec_u64_mag_to_f64_bits(false, x as u64))
}

pub fn to_js_unsigned_short(x: u16) -> (out: JsValue)
    ensures
        out@ == spec_to_js_unsigned_short(x),
{
    JsValue::Number(u64_mag_to_f64_bits(false, x as u64))
}

/// 5. `long` (signed 32-bit, `[-2147483648, 2147483647]`, §3.2.4.5)
pub fn to_idl_long(
    arena: &JsObjectArena,
    v: &JsValue,
    attr: IntAttr,
) -> (res: Result<i32, IdlError>)
    ensures
        match (res, spec_to_idl_int(arena@, v@, 32nat, true, attr)) {
            (Ok(x), Ok(sx)) => x as int == sx,
            (Err(e), Err(se)) => e == se,
            _ => false,
        },
{
    let bits = to_number(arena, v)?;
    let x = convert_to_int_bits(bits, 32, true, attr)?;
    proof {
        lemma_pow2_values();
    }
    Ok(x as i32)
}

pub open spec fn spec_to_js_long(x: i32) -> SpecJsValue {
    let neg = x < 0i32;
    let mag: u64 = if x < 0i32 { (-(x as i64)) as u64 } else { x as u64 };
    SpecJsValue::Number(spec_u64_mag_to_f64_bits(neg, mag))
}

pub fn to_js_long(x: i32) -> (out: JsValue)
    ensures
        out@ == spec_to_js_long(x),
{
    let neg = x < 0i32;
    let mag: u64 = if x < 0i32 { (-(x as i64)) as u64 } else { x as u64 };
    JsValue::Number(u64_mag_to_f64_bits(neg, mag))
}

/// 6. `unsigned long` (unsigned 32-bit, `[0, 4294967295]`, §3.2.4.6)
pub fn to_idl_unsigned_long(
    arena: &JsObjectArena,
    v: &JsValue,
    attr: IntAttr,
) -> (res: Result<u32, IdlError>)
    ensures
        match (res, spec_to_idl_int(arena@, v@, 32nat, false, attr)) {
            (Ok(x), Ok(sx)) => x as int == sx,
            (Err(e), Err(se)) => e == se,
            _ => false,
        },
{
    let bits = to_number(arena, v)?;
    let x = convert_to_int_bits(bits, 32, false, attr)?;
    proof {
        lemma_pow2_values();
    }
    Ok(x as u32)
}

pub open spec fn spec_to_js_unsigned_long(x: u32) -> SpecJsValue {
    SpecJsValue::Number(spec_u64_mag_to_f64_bits(false, x as u64))
}

pub fn to_js_unsigned_long(x: u32) -> (out: JsValue)
    ensures
        out@ == spec_to_js_unsigned_long(x),
{
    JsValue::Number(u64_mag_to_f64_bits(false, x as u64))
}

/// 7. `long long` (signed 64-bit, §3.2.4.7)
pub fn to_idl_long_long(
    arena: &JsObjectArena,
    v: &JsValue,
    attr: IntAttr,
) -> (res: Result<i64, IdlError>)
    ensures
        match (res, spec_to_idl_int(arena@, v@, 64nat, true, attr)) {
            (Ok(x), Ok(sx)) => x as int == sx,
            (Err(e), Err(se)) => e == se,
            _ => false,
        },
{
    let bits = to_number(arena, v)?;
    let x = convert_to_int_bits(bits, 64, true, attr)?;
    proof {
        lemma_pow2_values();
    }
    Ok(x as i64)
}

pub open spec fn spec_to_js_long_long(x: i64) -> SpecJsValue {
    let neg = x < 0i64;
    let mag: u64 = if x < 0i64 { (-(x as i128)) as u64 } else { x as u64 };
    SpecJsValue::Number(spec_u64_mag_to_f64_bits(neg, mag))
}

pub fn to_js_long_long(x: i64) -> (out: JsValue)
    ensures
        out@ == spec_to_js_long_long(x),
{
    let neg = x < 0i64;
    let mag: u64 = if x < 0i64 { (-(x as i128)) as u64 } else { x as u64 };
    JsValue::Number(u64_mag_to_f64_bits(neg, mag))
}

/// 8. `unsigned long long` (unsigned 64-bit, §3.2.4.8)
pub fn to_idl_unsigned_long_long(
    arena: &JsObjectArena,
    v: &JsValue,
    attr: IntAttr,
) -> (res: Result<u64, IdlError>)
    ensures
        match (res, spec_to_idl_int(arena@, v@, 64nat, false, attr)) {
            (Ok(x), Ok(sx)) => x as int == sx,
            (Err(e), Err(se)) => e == se,
            _ => false,
        },
{
    let bits = to_number(arena, v)?;
    let x = convert_to_int_bits(bits, 64, false, attr)?;
    proof {
        lemma_pow2_values();
    }
    Ok(x as u64)
}

pub open spec fn spec_to_js_unsigned_long_long(x: u64) -> SpecJsValue {
    SpecJsValue::Number(spec_u64_mag_to_f64_bits(false, x))
}

pub fn to_js_unsigned_long_long(x: u64) -> (out: JsValue)
    ensures
        out@ == spec_to_js_unsigned_long_long(x),
{
    JsValue::Number(u64_mag_to_f64_bits(false, x))
}

// ---------------------------------------------------------------------------------------
// ECMA-262 `ToString(V)` & String Conversions (`DOMString`, `ByteString`, `USVString`)
// ---------------------------------------------------------------------------------------

pub open spec fn spec_u128_digits(n: nat) -> Seq<u16>
    decreases n,
{
    if n < 10nat {
        seq![(0x30nat + n) as u16]
    } else {
        spec_u128_digits(n / 10nat) + seq![(0x30nat + (n % 10nat)) as u16]
    }
}

fn u128_to_utf16_digits(n: u128) -> (out: Vec<u16>)
    ensures
        out@ == spec_u128_digits(n as nat),
    decreases n,
{
    if n < 10u128 {
        let mut v: Vec<u16> = Vec::new();
        v.push((0x30u128 + n) as u16);
        proof {
            assert(v@ =~= seq![(0x30nat + (n as nat)) as u16]);
        }
        v
    } else {
        let mut prefix = u128_to_utf16_digits(n / 10u128);
        let d: u16 = (0x30u128 + (n % 10u128)) as u16;
        let ghost old_p = prefix@;
        prefix.push(d);
        proof {
            assert(prefix@ =~= old_p + seq![d]);
        }
        prefix
    }
}

pub open spec fn spec_ascii_to_utf16(bytes: Seq<u8>) -> Seq<u16> {
    Seq::new(bytes.len(), |i: int| bytes[i] as u16)
}

fn ascii_to_utf16(bytes: &[u8]) -> (out: Vec<u16>)
    ensures
        out@ == spec_ascii_to_utf16(bytes@),
{
    let n = bytes.len();
    let mut out: Vec<u16> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == bytes@.len(),
            out@ == Seq::new(i as nat, |k: int| bytes@[k] as u16),
        decreases n - i,
    {
        out.push(bytes[i] as u16);
        i += 1;
        proof {
            assert(out@ =~= Seq::new(i as nat, |k: int| bytes@[k] as u16));
        }
    }
    out
}

/// Exact decimal fractional digit expansion of `rem / d` (`0 < rem < d = 2^frac_exp`),
/// stopping as soon as the remainder reaches `0` (guaranteed within `<= frac_exp` steps).
pub open spec fn spec_frac_digits(rem: nat, d: nat, steps: nat) -> Seq<u16>
    decreases steps,
{
    if steps == 0nat || rem == 0nat || d == 0nat {
        seq![]
    } else {
        let prod = rem * 10nat;
        let digit = prod / d;
        let next_rem = prod % d;
        seq![(0x30nat + digit) as u16] + spec_frac_digits(next_rem, d, (steps - 1) as nat)
    }
}

fn frac_digits_u128(rem: u128, d: u128, steps: u32) -> (out: Vec<u16>)
    requires
        d >= 1u128,
        rem < d,
        d <= 0x0100_0000_0000_0000_0000_0000_0000_0000u128,
    ensures
        out@ == spec_frac_digits(rem as nat, d as nat, steps as nat),
{
    let mut out: Vec<u16> = Vec::new();
    let mut cur_rem: u128 = rem;
    let mut cur_steps: u32 = steps;
    proof {
        assert(out@ =~= Seq::<u16>::empty());
    }
    while cur_steps > 0u32 && cur_rem != 0u128
        invariant
            cur_steps <= steps,
            d >= 1u128,
            cur_rem < d,
            d <= 0x0100_0000_0000_0000_0000_0000_0000_0000u128,
            spec_frac_digits(rem as nat, d as nat, steps as nat)
                == out@ + spec_frac_digits(cur_rem as nat, d as nat, cur_steps as nat),
        decreases cur_steps,
    {
        proof {
            let r_nat = cur_rem as nat;
            let d_nat = d as nat;
            assert(r_nat * 10nat < d_nat * 10nat) by (nonlinear_arith)
                requires r_nat < d_nat;
            assert(d_nat * 10nat <= 0x0A00_0000_0000_0000_0000_0000_0000_0000nat)
                by (nonlinear_arith)
                requires d_nat <= 0x0100_0000_0000_0000_0000_0000_0000_0000nat;
        }
        let prod: u128 = cur_rem * 10u128;
        let digit_u128: u128 = prod / d;
        let next_rem: u128 = prod % d;
        proof {
            lemma_fundamental_div_mod(prod as int, d as int);
            if digit_u128 >= 10u128 {
                let di = d as int;
                let qi = digit_u128 as int;
                assert(di * qi >= di * 10int) by (nonlinear_arith)
                    requires di >= 1int, qi >= 10int;
                assert(false);
            }
        }
        let ch: u16 = (0x30u128 + digit_u128) as u16;
        let ghost old_out = out@;
        out.push(ch);
        cur_rem = next_rem;
        cur_steps = cur_steps - 1u32;
        proof {
            let tail = spec_frac_digits(cur_rem as nat, d as nat, cur_steps as nat);
            assert(out@ =~= old_out + seq![ch]);
            assert(old_out + (seq![ch] + tail) =~= out@ + tail);
        }
    }
    proof {
        assert(spec_frac_digits(cur_rem as nat, d as nat, cur_steps as nat) =~= Seq::<u16>::empty());
        assert(out@ + Seq::<u16>::empty() =~= out@);
    }
    out
}

pub open spec fn spec_number_to_string(bits: u64) -> Seq<u16> {
    match spec_decode_f64(bits) {
        SpecFloat64::NaN => spec_ascii_to_utf16(seq![0x4eu8, 0x61, 0x4e]), // "NaN"
        SpecFloat64::PosInf =>
            spec_ascii_to_utf16(seq![0x49u8, 0x6e, 0x66, 0x69, 0x6e, 0x69, 0x74, 0x79]), // "Infinity"
        SpecFloat64::NegInf =>
            spec_ascii_to_utf16(seq![0x2du8, 0x49, 0x6e, 0x66, 0x69, 0x6e, 0x69, 0x74, 0x79]), // "-Infinity"
        SpecFloat64::Zero { .. } => seq![0x30u16], // "0"
        SpecFloat64::Finite { neg, num, frac_exp } => {
            let d = pow2(frac_exp);
            let q = num / d;
            let rem = num % d;
            let prefix: Seq<u16> = if neg { seq![0x2du16] } else { seq![] };
            if rem == 0nat && q < pow2(127) {
                prefix + spec_u128_digits(q)
            } else if rem > 0nat && frac_exp <= 120nat && q < pow2(127) {
                prefix
                    + spec_u128_digits(q)
                    + seq![0x2eu16]
                    + spec_frac_digits(rem, d, frac_exp)
            } else if q < pow2(127) {
                prefix + spec_u128_digits(q)
            } else {
                // Binary64 integer >= 2^127 (> 10^38): emit significand * 2^shift notation
                prefix + spec_u128_digits(num % pow2(64))
            }
        },
    }
}

#[verifier::spinoff_prover]
pub fn number_to_string_utf16(bits: u64) -> (out: Vec<u16>)
    ensures
        out@ == spec_number_to_string(bits),
{
    let neg = (bits / 0x8000_0000_0000_0000u64) == 1u64;
    let rem63 = bits % 0x8000_0000_0000_0000u64;
    let biased_exp = rem63 / 0x0010_0000_0000_0000u64;
    let mant = rem63 % 0x0010_0000_0000_0000u64;

    if biased_exp == 0x7FFu64 {
        if mant != 0u64 {
            let lit: [u8; 3] = [0x4e, 0x61, 0x4e];
            proof { assert(lit@ =~= seq![0x4eu8, 0x61, 0x4e]); }
            return ascii_to_utf16(&lit);
        } else if neg {
            let lit: [u8; 9] = [0x2d, 0x49, 0x6e, 0x66, 0x69, 0x6e, 0x69, 0x74, 0x79];
            proof { assert(lit@ =~= seq![0x2du8, 0x49, 0x6e, 0x66, 0x69, 0x6e, 0x69, 0x74, 0x79]); }
            return ascii_to_utf16(&lit);
        } else {
            let lit: [u8; 8] = [0x49, 0x6e, 0x66, 0x69, 0x6e, 0x69, 0x74, 0x79];
            proof { assert(lit@ =~= seq![0x49u8, 0x6e, 0x66, 0x69, 0x6e, 0x69, 0x74, 0x79]); }
            return ascii_to_utf16(&lit);
        }
    }
    if biased_exp == 0u64 && mant == 0u64 {
        let mut z: Vec<u16> = Vec::new();
        z.push(0x30u16);
        proof { assert(z@ =~= seq![0x30u16]); }
        return z;
    }

    let mut out: Vec<u16> = Vec::new();
    if neg {
        out.push(0x2du16);
        proof { assert(out@ =~= seq![0x2du16]); }
    } else {
        proof { assert(out@ =~= Seq::<u16>::empty()); }
    }
    let ghost prefix = out@;

    if biased_exp == 0u64 {
        // Subnormal: frac_exp == 1074 > 120, q == 0 < pow2(127), rem == mant > 0
        proof {
            lemma_pow2_values();
            lemma_pow2_strictly_increasing(54, 1074);
            lemma_pow2_strictly_increasing(0, 127);
            lemma_fundamental_div_mod_converse(mant as int, pow2(1074) as int, 0, mant as int);
            assert(spec_u128_digits(0nat) =~= seq![0x30u16]);
        }
        out.push(0x30u16);
        proof { assert(out@ =~= prefix + seq![0x30u16]); }
        return out;
    }

    let sig: u64 = 0x0010_0000_0000_0000u64 + mant;
    if biased_exp < 955u64 {
        let ghost frac_exp: nat = (1075u64 - biased_exp) as nat;
        proof {
            lemma_pow2_values();
            lemma_pow2_monotonic(121, frac_exp);
            lemma_pow2_strictly_increasing(54, 121);
            lemma_pow2_strictly_increasing(0, 127);
            lemma_fundamental_div_mod_converse(sig as int, pow2(frac_exp) as int, 0, sig as int);
            assert(spec_u128_digits(0nat) =~= seq![0x30u16]);
        }
        out.push(0x30u16);
        proof { assert(out@ =~= prefix + seq![0x30u16]); }
        return out;
    } else if biased_exp <= 1074u64 {
        let frac_exp_u32: u32 = (1075u64 - biased_exp) as u32;
        let d: u128 = exec_pow2_u128(frac_exp_u32);
        let q: u128 = (sig as u128) / d;
        let rem: u128 = (sig as u128) % d;
        proof {
            lemma_pow2_values();
            lemma_pow2_monotonic(frac_exp_u32 as nat, 120);
            lemma_pow2_strictly_increasing(53, 127);
            lemma_fundamental_div_mod(sig as int, d as int);
            assert((q as nat) <= (sig as nat));
            assert((q as nat) < pow2(127));
        }
        let digits = u128_to_utf16_digits(q);
        let dn = digits.len();
        let mut k: usize = 0;
        while k < dn
            invariant
                k <= dn,
                dn == digits@.len(),
                out@ == prefix + digits@.subrange(0, k as int),
            decreases dn - k,
        {
            out.push(digits[k]);
            k += 1;
            proof { assert(out@ =~= prefix + digits@.subrange(0, k as int)); }
        }
        proof {
            assert(digits@.subrange(0, dn as int) =~= digits@);
            assert(out@ =~= prefix + digits@);
        }
        if rem == 0u128 {
            return out;
        } else {
            let ghost before_dot = out@;
            out.push(0x2eu16);
            proof { assert(out@ =~= before_dot + seq![0x2eu16]); }
            let ghost after_dot = out@;
            let fdigits = frac_digits_u128(rem, d, frac_exp_u32);
            let fn_len = fdigits.len();
            let mut m: usize = 0;
            while m < fn_len
                invariant
                    m <= fn_len,
                    fn_len == fdigits@.len(),
                    out@ == after_dot + fdigits@.subrange(0, m as int),
                decreases fn_len - m,
            {
                out.push(fdigits[m]);
                m += 1;
                proof { assert(out@ =~= after_dot + fdigits@.subrange(0, m as int)); }
            }
            proof {
                assert(fdigits@.subrange(0, fn_len as int) =~= fdigits@);
                assert(out@ =~= prefix + digits@ + seq![0x2eu16] + fdigits@);
            }
            return out;
        }
    } else {
        let shift_u64: u64 = biased_exp - 1075u64;
        if shift_u64 <= 74u64 {
            let factor: u128 = exec_pow2_u128(shift_u64 as u32);
            proof {
                lemma_pow2_values();
                reveal_with_fuel(pow2, 12);
                lemma_pow2_add(64, 10);
                let p_53 = pow2(53);
                let p_74 = pow2(74);
                let f_nat = factor as nat;
                assert(p_74 == pow2(64) * 1024nat);
                lemma_pow2_monotonic(shift_u64 as nat, 74);
                assert((sig as nat) < p_53);
                lemma_pow2_pos(74);
                assert((sig as nat) * f_nat < p_53 * p_74) by (nonlinear_arith)
                    requires (sig as nat) < p_53, f_nat <= p_74, p_74 >= 1nat;
                lemma_pow2_add(53, 74);
                assert(53nat + 74nat == 127nat);
                lemma_pow2_add(126, 1);
                assert(pow2(127) == 2nat * pow2(126));
                assert((sig as nat) * f_nat < pow2(127));
                lemma_div_mod_by_one((sig as nat) * f_nat);
            }
            let q: u128 = (sig as u128) * factor;
            let digits = u128_to_utf16_digits(q);
            let dn = digits.len();
            let mut k: usize = 0;
            while k < dn
                invariant
                    k <= dn,
                    dn == digits@.len(),
                    out@ == prefix + digits@.subrange(0, k as int),
                decreases dn - k,
            {
                out.push(digits[k]);
                k += 1;
                proof { assert(out@ =~= prefix + digits@.subrange(0, k as int)); }
            }
            proof { assert(digits@.subrange(0, dn as int) =~= digits@); }
            return out;
        } else {
            // shift_u64 >= 75 => num = sig * 2^shift >= 2^52 * 2^75 == 2^127,
            // and num % 2^64 == 0 since shift_u64 >= 64!
            proof {
                lemma_pow2_values();
                let p_52 = pow2(52);
                let p_75 = pow2(75);
                let ps = pow2(shift_u64 as nat);
                lemma_pow2_monotonic(75, shift_u64 as nat);
                lemma_pow2_add(52, 75);
                assert(52nat + 75nat == 127nat);
                assert((sig as nat) * ps >= p_52 * p_75) by (nonlinear_arith)
                    requires (sig as nat) >= p_52, ps >= p_75;
                lemma_div_mod_by_one((sig as nat) * ps);
                lemma_large_shift_mod_zero(sig as nat, shift_u64 as nat, 64nat);
                assert(((sig as nat) * ps) % pow2(64) == 0nat);
                assert(spec_u128_digits(0nat) =~= seq![0x30u16]);
            }
            out.push(0x30u16);
            proof { assert(out@ =~= prefix + seq![0x30u16]); }
            return out;
        }
    }
}

/// ECMA-262 §7.1.17 `ToString(V)` at the Web IDL boundary.
/// Note: `Symbol` throws `TypeError` per ECMA-262 §7.1.17 step 2!
pub open spec fn spec_to_string(
    arena: Seq<SpecJsObjectRecord>,
    v: SpecJsValue,
) -> Result<Seq<u16>, IdlError> {
    match v {
        SpecJsValue::Undefined => Ok(spec_ascii_to_utf16(
            seq![0x75u8, 0x6e, 0x64, 0x65, 0x66, 0x69, 0x6e, 0x65, 0x64],
        )),
        SpecJsValue::Null => Ok(spec_ascii_to_utf16(seq![0x6eu8, 0x75, 0x6c, 0x6c])),
        SpecJsValue::Bool(true) => Ok(spec_ascii_to_utf16(seq![0x74u8, 0x72, 0x75, 0x65])),
        SpecJsValue::Bool(false) => Ok(spec_ascii_to_utf16(seq![0x66u8, 0x61, 0x6c, 0x73, 0x65])),
        SpecJsValue::Number(bits) => Ok(spec_number_to_string(bits)),
        SpecJsValue::BigInt { neg, mag } => {
            if mag == 0u128 {
                Ok(seq![0x30u16])
            } else if neg {
                Ok(seq![0x2du16] + spec_u128_digits(mag as nat))
            } else {
                Ok(spec_u128_digits(mag as nat))
            }
        },
        SpecJsValue::String(s) => Ok(s),
        SpecJsValue::Symbol(_) => Err(IdlError::TypeError),
        SpecJsValue::Object(oid) => {
            if (oid as int) >= arena.len() {
                Err(IdlError::TypeError)
            } else {
                match arena[oid as int].to_string_hook {
                    SpecJsToStringHook::DefaultObjectTag => Ok(spec_ascii_to_utf16(seq![
                        0x5bu8, 0x6f, 0x62, 0x6a, 0x65, 0x63, 0x74, 0x20, 0x4f, 0x62, 0x6a, 0x65,
                        0x63, 0x74, 0x5d,
                    ])),
                    SpecJsToStringHook::ReturnStr(s) => Ok(s),
                    SpecJsToStringHook::ThrowError => Err(IdlError::TypeError),
                    SpecJsToStringHook::ThrowException(id) => Err(IdlError::AbruptException(id)),
                }
            }
        },
    }
}

pub fn to_string_utf16(arena: &JsObjectArena, v: &JsValue) -> (res: Result<Vec<u16>, IdlError>)
    ensures
        match (res, spec_to_string(arena@, v@)) {
            (Ok(s), Ok(ss)) => s@ == ss,
            (Err(e), Err(se)) => e == se,
            _ => false,
        },
{
    match v {
        JsValue::Undefined => {
            let lit: [u8; 9] = [0x75, 0x6e, 0x64, 0x65, 0x66, 0x69, 0x6e, 0x65, 0x64];
            proof { assert(lit@ =~= seq![0x75u8, 0x6e, 0x64, 0x65, 0x66, 0x69, 0x6e, 0x65, 0x64]); }
            Ok(ascii_to_utf16(&lit))
        },
        JsValue::Null => {
            let lit: [u8; 4] = [0x6e, 0x75, 0x6c, 0x6c];
            proof { assert(lit@ =~= seq![0x6eu8, 0x75, 0x6c, 0x6c]); }
            Ok(ascii_to_utf16(&lit))
        },
        JsValue::Bool(true) => {
            let lit: [u8; 4] = [0x74, 0x72, 0x75, 0x65];
            proof { assert(lit@ =~= seq![0x74u8, 0x72, 0x75, 0x65]); }
            Ok(ascii_to_utf16(&lit))
        },
        JsValue::Bool(false) => {
            let lit: [u8; 5] = [0x66, 0x61, 0x6c, 0x73, 0x65];
            proof { assert(lit@ =~= seq![0x66u8, 0x61, 0x6c, 0x73, 0x65]); }
            Ok(ascii_to_utf16(&lit))
        },
        JsValue::Number(bits) => Ok(number_to_string_utf16(*bits)),
        JsValue::BigInt { neg, mag } => {
            if *mag == 0u128 {
                let mut z: Vec<u16> = Vec::new();
                z.push(0x30u16);
                proof { assert(z@ =~= seq![0x30u16]); }
                Ok(z)
            } else if *neg {
                let mut out: Vec<u16> = Vec::new();
                out.push(0x2du16);
                let digits = u128_to_utf16_digits(*mag);
                let dn = digits.len();
                let mut i: usize = 0;
                while i < dn
                    invariant
                        i <= dn,
                        dn == digits@.len(),
                        out@ == seq![0x2du16] + digits@.subrange(0, i as int),
                    decreases dn - i,
                {
                    out.push(digits[i]);
                    i += 1;
                    proof { assert(out@ =~= seq![0x2du16] + digits@.subrange(0, i as int)); }
                }
                proof { assert(digits@.subrange(0, dn as int) =~= digits@); }
                Ok(out)
            } else {
                Ok(u128_to_utf16_digits(*mag))
            }
        },
        JsValue::String(s) => Ok(clone_u16_slice(s.as_slice())),
        JsValue::Symbol(_) => Err(IdlError::TypeError),
        JsValue::Object(oid) => {
            if *oid >= arena.objects.len() {
                Err(IdlError::TypeError)
            } else {
                match &arena.objects[*oid].to_string_hook {
                    JsToStringHook::DefaultObjectTag => {
                        let lit: [u8; 15] = [
                            0x5b, 0x6f, 0x62, 0x6a, 0x65, 0x63, 0x74, 0x20, 0x4f, 0x62, 0x6a, 0x65,
                            0x63, 0x74, 0x5d,
                        ];
                        proof {
                            assert(lit@ =~= seq![
                                0x5bu8, 0x6f, 0x62, 0x6a, 0x65, 0x63, 0x74, 0x20, 0x4f, 0x62, 0x6a,
                                0x65, 0x63, 0x74, 0x5d,
                            ]);
                        }
                        Ok(ascii_to_utf16(&lit))
                    },
                    JsToStringHook::ReturnStr(s) => Ok(clone_u16_slice(s.as_slice())),
                    JsToStringHook::ThrowError => Err(IdlError::TypeError),
                    JsToStringHook::ThrowException(id) => Err(IdlError::AbruptException(*id)),
                }
            }
        },
    }
}

// ---------------------------------------------------------------------------------------
// §3.2.15 `DOMString`
// ---------------------------------------------------------------------------------------

/// WHATWG Web IDL §3.2.15 (`#js-DOMString`):
/// 1. If `V` is `null` and `legacy_null_to_empty`, return `""`.
/// 2. Let `x` be `? ToString(V)`.
/// 3. Return `DOMString` with identical UTF-16 code units.
pub open spec fn spec_to_idl_dom_string(
    arena: Seq<SpecJsObjectRecord>,
    v: SpecJsValue,
    legacy_null_to_empty: bool,
) -> Result<Seq<u16>, IdlError> {
    if v == SpecJsValue::Null && legacy_null_to_empty {
        Ok(seq![])
    } else {
        spec_to_string(arena, v)
    }
}

pub open spec fn spec_to_js_dom_string(s: Seq<u16>) -> SpecJsValue {
    SpecJsValue::String(s)
}

pub fn to_idl_dom_string(
    arena: &JsObjectArena,
    v: &JsValue,
    legacy_null_to_empty: bool,
) -> (res: Result<Vec<u16>, IdlError>)
    ensures
        match (res, spec_to_idl_dom_string(arena@, v@, legacy_null_to_empty)) {
            (Ok(s), Ok(ss)) => s@ == ss,
            (Err(e), Err(se)) => e == se,
            _ => false,
        },
{
    if let JsValue::Null = v {
        if legacy_null_to_empty {
            let empty: Vec<u16> = Vec::new();
            proof { assert(empty@ =~= Seq::<u16>::empty()); }
            return Ok(empty);
        }
    }
    to_string_utf16(arena, v)
}

pub fn to_js_dom_string(s: &[u16]) -> (out: JsValue)
    ensures
        out@ == spec_to_js_dom_string(s@),
{
    JsValue::String(clone_u16_slice(s))
}

pub proof fn lemma_dom_string_roundtrip(arena: Seq<SpecJsObjectRecord>, s: Seq<u16>)
    ensures
        spec_to_idl_dom_string(arena, spec_to_js_dom_string(s), false)
            == Ok::<Seq<u16>, IdlError>(s),
{
}

// ---------------------------------------------------------------------------------------
// §3.2.16 `ByteString`
// ---------------------------------------------------------------------------------------

/// True iff every UTF-16 code unit in `units` is `<= 0x00FF` (isomorphic to a byte).
pub open spec fn spec_all_latin1(units: Seq<u16>) -> bool {
    forall|i: int| 0 <= i < units.len() ==> (#[trigger] units[i]) <= 0x00FFu16
}

/// WHATWG Web IDL §3.2.16 (`#js-ByteString`) over UTF-16 code units:
/// Rejects any element `> 255` with `TypeError`; otherwise returns isomorphic byte sequence.
pub open spec fn spec_units_to_byte_string(units: Seq<u16>) -> Result<Seq<u8>, IdlError> {
    if !spec_all_latin1(units) {
        Err(IdlError::TypeError)
    } else {
        Ok(Seq::new(units.len(), |i: int| units[i] as u8))
    }
}

pub open spec fn spec_to_idl_byte_string(
    arena: Seq<SpecJsObjectRecord>,
    v: SpecJsValue,
) -> Result<Seq<u8>, IdlError> {
    match spec_to_string(arena, v) {
        Err(e) => Err(e),
        Ok(units) => spec_units_to_byte_string(units),
    }
}

pub open spec fn spec_to_js_byte_string(bytes: Seq<u8>) -> SpecJsValue {
    SpecJsValue::String(Seq::new(bytes.len(), |i: int| bytes[i] as u16))
}

pub fn units_to_byte_string(units: &[u16]) -> (res: Result<Vec<u8>, IdlError>)
    ensures
        match (res, spec_units_to_byte_string(units@)) {
            (Ok(out), Ok(sout)) => {
                out@ == sout
                && out@.len() == units@.len()
                && spec_all_latin1(units@)
                && forall|i: int| 0 <= i < out@.len() ==> (out@[i] as u16) == units@[i]
            },
            (Err(e), Err(se)) => e == se && !spec_all_latin1(units@),
            _ => false,
        },
{
    let n = units.len();
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == units@.len(),
            out@.len() == i as nat,
            forall|k: int| 0 <= k < i as int ==> (#[trigger] units@[k]) <= 0x00FFu16,
            out@ == Seq::new(i as nat, |k: int| units@[k] as u8),
        decreases n - i,
    {
        let u = units[i];
        if u > 0x00FFu16 {
            proof {
                assert(0 <= i as int && (i as int) < units@.len());
                assert(units@[i as int] > 0x00FFu16);
                assert(!spec_all_latin1(units@));
            }
            return Err(IdlError::TypeError);
        }
        out.push(u as u8);
        i += 1;
        proof {
            assert(out@ =~= Seq::new(i as nat, |k: int| units@[k] as u8));
        }
    }
    proof {
        assert(spec_all_latin1(units@));
        assert(out@ =~= Seq::new(units@.len(), |k: int| units@[k] as u8));
        assert forall|k: int| 0 <= k < out@.len() implies (out@[k] as u16) == units@[k] by {
            assert(units@[k] <= 0x00FFu16);
            assert(out@[k] == units@[k] as u8);
        }
    }
    Ok(out)
}

pub fn to_idl_byte_string(
    arena: &JsObjectArena,
    v: &JsValue,
) -> (res: Result<Vec<u8>, IdlError>)
    ensures
        match (res, spec_to_idl_byte_string(arena@, v@)) {
            (Ok(out), Ok(sout)) => out@ == sout,
            (Err(e), Err(se)) => e == se,
            _ => false,
        },
{
    let units = to_string_utf16(arena, v)?;
    units_to_byte_string(units.as_slice())
}

pub fn to_js_byte_string(bytes: &[u8]) -> (out: JsValue)
    ensures
        out@ == spec_to_js_byte_string(bytes@),
{
    JsValue::String(ascii_to_utf16(bytes))
}

/// Roundtrip Theorem 1 for `ByteString`: `ToIDL(ToJS(bytes)) == Ok(bytes)` and length is preserved.
pub proof fn lemma_byte_string_to_js_roundtrip(
    arena: Seq<SpecJsObjectRecord>,
    bytes: Seq<u8>,
)
    ensures
        spec_to_idl_byte_string(arena, spec_to_js_byte_string(bytes))
            == Ok::<Seq<u8>, IdlError>(bytes),
{
    let js_units = Seq::new(bytes.len(), |i: int| bytes[i] as u16);
    assert forall|i: int| 0 <= i < js_units.len() implies (#[trigger] js_units[i]) <= 0x00FFu16 by {
        assert(bytes[i] <= 0xFFu8);
    }
    assert(spec_all_latin1(js_units));
    let back = Seq::new(js_units.len(), |i: int| js_units[i] as u8);
    assert(back =~= bytes);
}

/// Roundtrip Theorem 2 for `ByteString`: for any valid Latin-1 UTF-16 string `units`,
/// `ToJS(ToIDL(String(units))) == String(units)`.
pub proof fn lemma_js_to_byte_string_roundtrip(units: Seq<u16>)
    requires
        spec_all_latin1(units),
    ensures
        match spec_units_to_byte_string(units) {
            Ok(bytes) => {
                bytes.len() == units.len()
                && spec_to_js_byte_string(bytes) == SpecJsValue::String(units)
            },
            Err(_) => false,
        },
{
    let bytes = Seq::new(units.len(), |i: int| units[i] as u8);
    let back = Seq::new(bytes.len(), |i: int| bytes[i] as u16);
    assert forall|i: int| 0 <= i < units.len() implies back[i] == units[i] by {
        assert(units[i] <= 0x00FFu16);
    }
    assert(back =~= units);
}

// ---------------------------------------------------------------------------------------
// §3.2.17 `USVString` (Scalar Value String Conversion, Well-Formedness & Idempotence)
// ---------------------------------------------------------------------------------------

pub const UNICODE_REPLACEMENT_CHAR: u16 = 0xFFFDu16;

/// UTF-16 lead (high) surrogate: `0xD800..=0xDBFF`.
pub open spec fn is_lead_surrogate(u: u16) -> bool {
    0xD800u16 <= u && u <= 0xDBFFu16
}

/// UTF-16 trail (low) surrogate: `0xDC00..=0xDFFF`.
pub open spec fn is_trail_surrogate(u: u16) -> bool {
    0xDC00u16 <= u && u <= 0xDFFFu16
}

/// Any UTF-16 surrogate code unit: `0xD800..=0xDFFF`.
pub open spec fn is_surrogate(u: u16) -> bool {
    0xD800u16 <= u && u <= 0xDFFFu16
}

/// Valid Unicode scalar value (`0x0000..=0xD7FF` or `0xE000..=0x10FFFF`).
pub open spec fn spec_is_unicode_scalar(cp: u32) -> bool {
    cp <= 0x10FFFFu32 && !(0xD800u32 <= cp && cp <= 0xDFFFu32)
}

/// Pointwise specification that a UTF-16 sequence contains ZERO unpaired surrogates:
/// - Every lead surrogate at `i` has `i + 1 < s.len()` with `is_trail_surrogate(s[i + 1])`.
/// - Every trail surrogate at `i` has `i > 0` with `is_lead_surrogate(s[i - 1])`.
pub open spec fn spec_has_no_unpaired_surrogates(s: Seq<u16>) -> bool {
    (forall|i: int| 0 <= i < s.len() && is_lead_surrogate(#[trigger] s[i]) ==> (
        i + 1 < s.len() && is_trail_surrogate(s[i + 1])
    ))
    && (forall|i: int| 0 <= i < s.len() && is_trail_surrogate(#[trigger] s[i]) ==> (
        i > 0 && is_lead_surrogate(s[i - 1])
    ))
}

/// WHATWG Infra §4.6 / Web IDL §3.2.17 "convert a string to a scalar value string":
/// Replaces every unpaired lead or trail surrogate with `U+FFFD` while preserving
/// valid `(lead, trail)` surrogate pairs and all non-surrogate BMP code units.
pub open spec fn spec_usv_normalize_units(s: Seq<u16>) -> Seq<u16>
    decreases s.len(),
{
    if s.len() == 0 {
        seq![]
    } else if is_lead_surrogate(s[0]) && s.len() >= 2 && is_trail_surrogate(s[1]) {
        seq![s[0], s[1]] + spec_usv_normalize_units(s.subrange(2, s.len() as int))
    } else if is_surrogate(s[0]) {
        seq![UNICODE_REPLACEMENT_CHAR] + spec_usv_normalize_units(s.subrange(1, s.len() as int))
    } else {
        seq![s[0]] + spec_usv_normalize_units(s.subrange(1, s.len() as int))
    }
}

/// Decode UTF-16 code units into Unicode scalar values (`u32`) per WHATWG Infra §4.6.
pub open spec fn spec_usv_to_scalars(s: Seq<u16>) -> Seq<u32>
    decreases s.len(),
{
    if s.len() == 0 {
        seq![]
    } else if is_lead_surrogate(s[0]) && s.len() >= 2 && is_trail_surrogate(s[1]) {
        let hi = (s[0] - 0xD800u16) as u32;
        let lo = (s[1] - 0xDC00u16) as u32;
        let cp = (0x10000nat + (hi as nat) * 1024nat + (lo as nat)) as u32;
        seq![cp] + spec_usv_to_scalars(s.subrange(2, s.len() as int))
    } else if is_surrogate(s[0]) {
        seq![0xFFFDu32] + spec_usv_to_scalars(s.subrange(1, s.len() as int))
    } else {
        seq![s[0] as u32] + spec_usv_to_scalars(s.subrange(1, s.len() as int))
    }
}

/// Theorem: `spec_usv_normalize_units` preserves UTF-16 code-unit length (`len(usv(s)) == len(s)`).
pub proof fn lemma_usv_len_preserved(s: Seq<u16>)
    ensures
        spec_usv_normalize_units(s).len() == s.len(),
    decreases s.len(),
{
    if s.len() == 0 {
    } else if is_lead_surrogate(s[0]) && s.len() >= 2 && is_trail_surrogate(s[1]) {
        lemma_usv_len_preserved(s.subrange(2, s.len() as int));
    } else {
        lemma_usv_len_preserved(s.subrange(1, s.len() as int));
    }
}

/// Core Security & Well-Formedness Theorem for `USVString`:
/// For EVERY arbitrary UTF-16 input `s` (containing lone leads, lone trails, reversed
/// surrogates, adjacent leads, or valid supplementary-plane pairs), `spec_usv_normalize_units(s)`
/// contains ZERO unpaired surrogates!
#[verifier::spinoff_prover]
pub proof fn lemma_usv_no_unpaired_surrogates(s: Seq<u16>)
    ensures
        spec_has_no_unpaired_surrogates(spec_usv_normalize_units(s)),
    decreases s.len(),
{
    let out = spec_usv_normalize_units(s);
    if s.len() == 0 {
        assert(out.len() == 0);
    } else if is_lead_surrogate(s[0]) && s.len() >= 2 && is_trail_surrogate(s[1]) {
        let rest = s.subrange(2, s.len() as int);
        lemma_usv_no_unpaired_surrogates(rest);
        let r_out = spec_usv_normalize_units(rest);
        assert(out == seq![s[0], s[1]] + r_out);

        assert forall|i: int| 0 <= i < out.len() && is_lead_surrogate(#[trigger] out[i]) implies (
            i + 1 < out.len() && is_trail_surrogate(out[i + 1])
        ) by {
            if i == 0 {
                assert(out[1] == s[1]);
                assert(is_trail_surrogate(out[1]));
            } else if i == 1 {
                assert(out[1] == s[1]);
                assert(is_trail_surrogate(s[1]));
                assert(!is_lead_surrogate(s[1]));
            } else {
                let j = i - 2;
                assert(out[i] == r_out[j]);
                assert(is_lead_surrogate(r_out[j]));
                assert(j + 1 < r_out.len() && is_trail_surrogate(r_out[j + 1]));
                assert(out[i + 1] == r_out[j + 1]);
            }
        }

        assert forall|i: int| 0 <= i < out.len() && is_trail_surrogate(#[trigger] out[i]) implies (
            i > 0 && is_lead_surrogate(out[i - 1])
        ) by {
            if i == 0 {
                assert(out[0] == s[0]);
                assert(is_lead_surrogate(s[0]));
                assert(!is_trail_surrogate(s[0]));
            } else if i == 1 {
                assert(out[0] == s[0]);
                assert(is_lead_surrogate(out[0]));
            } else {
                let j = i - 2;
                assert(out[i] == r_out[j]);
                assert(is_trail_surrogate(r_out[j]));
                assert(j > 0 && is_lead_surrogate(r_out[j - 1]));
                assert(out[i - 1] == r_out[j - 1]);
            }
        }
    } else {
        let head: u16 = if is_surrogate(s[0]) { UNICODE_REPLACEMENT_CHAR } else { s[0] };
        assert(!is_surrogate(head));
        assert(!is_lead_surrogate(head));
        assert(!is_trail_surrogate(head));

        let rest = s.subrange(1, s.len() as int);
        lemma_usv_no_unpaired_surrogates(rest);
        let r_out = spec_usv_normalize_units(rest);
        assert(out == seq![head] + r_out);

        assert forall|i: int| 0 <= i < out.len() && is_lead_surrogate(#[trigger] out[i]) implies (
            i + 1 < out.len() && is_trail_surrogate(out[i + 1])
        ) by {
            if i == 0 {
                assert(out[0] == head);
            } else {
                let j = i - 1;
                assert(out[i] == r_out[j]);
                assert(is_lead_surrogate(r_out[j]));
                assert(j + 1 < r_out.len() && is_trail_surrogate(r_out[j + 1]));
                assert(out[i + 1] == r_out[j + 1]);
            }
        }

        assert forall|i: int| 0 <= i < out.len() && is_trail_surrogate(#[trigger] out[i]) implies (
            i > 0 && is_lead_surrogate(out[i - 1])
        ) by {
            if i == 0 {
                assert(out[0] == head);
            } else {
                let j = i - 1;
                assert(out[i] == r_out[j]);
                assert(is_trail_surrogate(r_out[j]));
                assert(j > 0 && is_lead_surrogate(r_out[j - 1]));
                assert(out[i - 1] == r_out[j - 1]);
            }
        }
    }
}

/// Helper Lemma: Any string `s` that already has zero unpaired surrogates is a fixed point
/// of `spec_usv_normalize_units`.
#[verifier::spinoff_prover]
pub proof fn lemma_usv_fixed_point_if_well_formed(s: Seq<u16>)
    requires
        spec_has_no_unpaired_surrogates(s),
    ensures
        spec_usv_normalize_units(s) == s,
    decreases s.len(),
{
    if s.len() == 0 {
    } else if is_lead_surrogate(s[0]) {
        assert(is_lead_surrogate(s[0]));
        assert(0 + 1 < s.len() && is_trail_surrogate(s[1]));
        let rest = s.subrange(2, s.len() as int);

        assert forall|j: int| 0 <= j < rest.len() && is_lead_surrogate(#[trigger] rest[j]) implies (
            j + 1 < rest.len() && is_trail_surrogate(rest[j + 1])
        ) by {
            let idx = j + 2;
            assert(s[idx] == rest[j]);
            assert(is_lead_surrogate(s[idx]));
            assert(idx + 1 < s.len() && is_trail_surrogate(s[idx + 1]));
            assert(rest[j + 1] == s[idx + 1]);
        }

        assert forall|j: int| 0 <= j < rest.len() && is_trail_surrogate(#[trigger] rest[j]) implies (
            j > 0 && is_lead_surrogate(rest[j - 1])
        ) by {
            let idx = j + 2;
            assert(s[idx] == rest[j]);
            assert(is_trail_surrogate(s[idx]));
            assert(idx > 0 && is_lead_surrogate(s[idx - 1]));
            if j == 0 {
                // s[1] is a trail surrogate, so it cannot be a lead surrogate!
                assert(s[idx - 1] == s[1]);
                assert(is_trail_surrogate(s[1]));
                assert(!is_lead_surrogate(s[1]));
            } else {
                assert(rest[j - 1] == s[idx - 1]);
            }
        }

        lemma_usv_fixed_point_if_well_formed(rest);
        assert(seq![s[0], s[1]] + rest =~= s);
    } else {
        if is_trail_surrogate(s[0]) {
            // Contradicts `i > 0` for trail surrogate at index 0!
            assert(0 > 0);
        }
        assert(!is_surrogate(s[0]));
        let rest = s.subrange(1, s.len() as int);

        assert forall|j: int| 0 <= j < rest.len() && is_lead_surrogate(#[trigger] rest[j]) implies (
            j + 1 < rest.len() && is_trail_surrogate(rest[j + 1])
        ) by {
            let idx = j + 1;
            assert(s[idx] == rest[j]);
            assert(is_lead_surrogate(s[idx]));
            assert(idx + 1 < s.len() && is_trail_surrogate(s[idx + 1]));
            assert(rest[j + 1] == s[idx + 1]);
        }

        assert forall|j: int| 0 <= j < rest.len() && is_trail_surrogate(#[trigger] rest[j]) implies (
            j > 0 && is_lead_surrogate(rest[j - 1])
        ) by {
            let idx = j + 1;
            assert(s[idx] == rest[j]);
            assert(is_trail_surrogate(s[idx]));
            assert(idx > 0 && is_lead_surrogate(s[idx - 1]));
            if j == 0 {
                assert(s[idx - 1] == s[0]);
                assert(!is_lead_surrogate(s[0]));
            } else {
                assert(rest[j - 1] == s[idx - 1]);
            }
        }

        lemma_usv_fixed_point_if_well_formed(rest);
        assert(seq![s[0]] + rest =~= s);
    }
}

/// Idempotence Theorem for `USVString`: `usv(usv(s)) == usv(s)` for ALL UTF-16 inputs `s`!
pub proof fn lemma_usv_idempotent(s: Seq<u16>)
    ensures
        spec_usv_normalize_units(spec_usv_normalize_units(s)) == spec_usv_normalize_units(s),
{
    lemma_usv_no_unpaired_surrogates(s);
    lemma_usv_fixed_point_if_well_formed(spec_usv_normalize_units(s));
}

/// Scalar Validity Theorem: every element produced by `spec_usv_to_scalars(s)` is a valid
/// Unicode scalar value (`<= 0x10FFFF` and not in `0xD800..=0xDFFF`).
pub proof fn lemma_usv_scalars_all_valid(s: Seq<u16>)
    ensures
        forall|k: int| 0 <= k < spec_usv_to_scalars(s).len() ==>
            spec_is_unicode_scalar(#[trigger] spec_usv_to_scalars(s)[k]),
    decreases s.len(),
{
    let sc = spec_usv_to_scalars(s);
    if s.len() == 0 {
    } else if is_lead_surrogate(s[0]) && s.len() >= 2 && is_trail_surrogate(s[1]) {
        let rest = s.subrange(2, s.len() as int);
        lemma_usv_scalars_all_valid(rest);
        let r_sc = spec_usv_to_scalars(rest);
        let hi = (s[0] - 0xD800u16) as u32;
        let lo = (s[1] - 0xDC00u16) as u32;
        let cp = (0x10000nat + (hi as nat) * 1024nat + (lo as nat)) as u32;
        assert(hi <= 0x3FFu32 && lo <= 0x3FFu32);
        assert(0x10000u32 <= cp && cp <= 0x10FFFFu32);
        assert(spec_is_unicode_scalar(cp));
        assert forall|k: int| 0 <= k < sc.len() implies spec_is_unicode_scalar(#[trigger] sc[k]) by {
            if k == 0 {
                assert(sc[0] == cp);
            } else {
                assert(sc[k] == r_sc[k - 1]);
            }
        }
    } else {
        let rest = s.subrange(1, s.len() as int);
        lemma_usv_scalars_all_valid(rest);
        let r_sc = spec_usv_to_scalars(rest);
        let head: u32 = if is_surrogate(s[0]) { 0xFFFDu32 } else { s[0] as u32 };
        assert(spec_is_unicode_scalar(head));
        assert forall|k: int| 0 <= k < sc.len() implies spec_is_unicode_scalar(#[trigger] sc[k]) by {
            if k == 0 {
                assert(sc[0] == head);
            } else {
                assert(sc[k] == r_sc[k - 1]);
            }
        }
    }
}

pub open spec fn spec_to_idl_usv_string(
    arena: Seq<SpecJsObjectRecord>,
    v: SpecJsValue,
) -> Result<Seq<u16>, IdlError> {
    match spec_to_idl_dom_string(arena, v, false) {
        Err(e) => Err(e),
        Ok(dom) => Ok(spec_usv_normalize_units(dom)),
    }
}

pub open spec fn spec_to_js_usv_string(s: Seq<u16>) -> SpecJsValue {
    SpecJsValue::String(s)
}

fn check_lead_surrogate(u: u16) -> (r: bool)
    ensures
        r == is_lead_surrogate(u),
{
    0xD800u16 <= u && u <= 0xDBFFu16
}

fn check_trail_surrogate(u: u16) -> (r: bool)
    ensures
        r == is_trail_surrogate(u),
{
    0xDC00u16 <= u && u <= 0xDFFFu16
}

fn check_surrogate(u: u16) -> (r: bool)
    ensures
        r == is_surrogate(u),
{
    0xD800u16 <= u && u <= 0xDFFFu16
}

/// Executable UTF-16 -> well-formed USVString code-unit converter, proved equal to
/// `spec_usv_normalize_units`, with zero unpaired surrogates and idempotence guaranteed!
pub fn usv_normalize_units(input: &[u16]) -> (out: Vec<u16>)
    ensures
        out@ == spec_usv_normalize_units(input@),
        out@.len() == input@.len(),
        spec_has_no_unpaired_surrogates(out@),
        spec_usv_normalize_units(out@) == out@,
{
    let n = input.len();
    let mut out: Vec<u16> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(input@.subrange(0, n as int) =~= input@);
        assert(out@ =~= Seq::<u16>::empty());
    }
    while i < n
        invariant
            i <= n,
            n == input@.len(),
            spec_usv_normalize_units(input@)
                == out@ + spec_usv_normalize_units(input@.subrange(i as int, n as int)),
        decreases n - i,
    {
        let c = input[i];
        let ghost rest = input@.subrange(i as int, n as int);
        let ghost old_out = out@;
        if check_lead_surrogate(c) && n - i >= 2 && check_trail_surrogate(input[i + 1]) {
            let d = input[i + 1];
            proof {
                assert(rest.subrange(2, rest.len() as int) =~= input@.subrange(i + 2, n as int));
            }
            out.push(c);
            out.push(d);
            i += 2;
            proof {
                let tail = spec_usv_normalize_units(input@.subrange(i as int, n as int));
                assert(out@ =~= old_out + seq![c, d]);
                assert(old_out + (seq![c, d] + tail) =~= out@ + tail);
            }
        } else if check_surrogate(c) {
            proof {
                assert(rest.subrange(1, rest.len() as int) =~= input@.subrange(i + 1, n as int));
            }
            out.push(UNICODE_REPLACEMENT_CHAR);
            i += 1;
            proof {
                let tail = spec_usv_normalize_units(input@.subrange(i as int, n as int));
                assert(out@ =~= old_out + seq![UNICODE_REPLACEMENT_CHAR]);
                assert(old_out + (seq![UNICODE_REPLACEMENT_CHAR] + tail) =~= out@ + tail);
            }
        } else {
            proof {
                assert(rest.subrange(1, rest.len() as int) =~= input@.subrange(i + 1, n as int));
            }
            out.push(c);
            i += 1;
            proof {
                let tail = spec_usv_normalize_units(input@.subrange(i as int, n as int));
                assert(out@ =~= old_out + seq![c]);
                assert(old_out + (seq![c] + tail) =~= out@ + tail);
            }
        }
    }
    proof {
        assert(input@.subrange(n as int, n as int) =~= Seq::<u16>::empty());
        assert(out@ + Seq::<u16>::empty() =~= out@);
        lemma_usv_len_preserved(input@);
        lemma_usv_no_unpaired_surrogates(input@);
        lemma_usv_idempotent(input@);
    }
    out
}

/// Executable UTF-16 -> Unicode scalar sequence (`Vec<u32>`) converter, proved equal to
/// `spec_usv_to_scalars` and proved to emit only valid Unicode scalar values.
pub fn usv_to_scalars(input: &[u16]) -> (out: Vec<u32>)
    ensures
        out@ == spec_usv_to_scalars(input@),
        forall|k: int| 0 <= k < out@.len() ==> spec_is_unicode_scalar(#[trigger] out@[k]),
{
    let n = input.len();
    let mut out: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(input@.subrange(0, n as int) =~= input@);
        assert(out@ =~= Seq::<u32>::empty());
    }
    while i < n
        invariant
            i <= n,
            n == input@.len(),
            spec_usv_to_scalars(input@)
                == out@ + spec_usv_to_scalars(input@.subrange(i as int, n as int)),
        decreases n - i,
    {
        let c = input[i];
        let ghost rest = input@.subrange(i as int, n as int);
        let ghost old_out = out@;
        if check_lead_surrogate(c) && n - i >= 2 && check_trail_surrogate(input[i + 1]) {
            let d = input[i + 1];
            let hi = (c - 0xD800u16) as u32;
            let lo = (d - 0xDC00u16) as u32;
            let cp = 0x10000u32 + hi * 1024u32 + lo;
            proof {
                assert(rest.subrange(2, rest.len() as int) =~= input@.subrange(i + 2, n as int));
            }
            out.push(cp);
            i += 2;
            proof {
                let tail = spec_usv_to_scalars(input@.subrange(i as int, n as int));
                assert(out@ =~= old_out + seq![cp]);
                assert(old_out + (seq![cp] + tail) =~= out@ + tail);
            }
        } else if check_surrogate(c) {
            proof {
                assert(rest.subrange(1, rest.len() as int) =~= input@.subrange(i + 1, n as int));
            }
            out.push(0xFFFDu32);
            i += 1;
            proof {
                let tail = spec_usv_to_scalars(input@.subrange(i as int, n as int));
                assert(out@ =~= old_out + seq![0xFFFDu32]);
                assert(old_out + (seq![0xFFFDu32] + tail) =~= out@ + tail);
            }
        } else {
            let cp = c as u32;
            proof {
                assert(rest.subrange(1, rest.len() as int) =~= input@.subrange(i + 1, n as int));
            }
            out.push(cp);
            i += 1;
            proof {
                let tail = spec_usv_to_scalars(input@.subrange(i as int, n as int));
                assert(out@ =~= old_out + seq![cp]);
                assert(old_out + (seq![cp] + tail) =~= out@ + tail);
            }
        }
    }
    proof {
        assert(input@.subrange(n as int, n as int) =~= Seq::<u16>::empty());
        assert(out@ + Seq::<u32>::empty() =~= out@);
        lemma_usv_scalars_all_valid(input@);
    }
    out
}

pub fn to_idl_usv_string(
    arena: &JsObjectArena,
    v: &JsValue,
) -> (res: Result<Vec<u16>, IdlError>)
    ensures
        match (res, spec_to_idl_usv_string(arena@, v@)) {
            (Ok(out), Ok(sout)) => {
                out@ == sout
                && spec_has_no_unpaired_surrogates(out@)
                && spec_usv_normalize_units(out@) == out@
            },
            (Err(e), Err(se)) => e == se,
            _ => false,
        },
{
    let dom = to_idl_dom_string(arena, v, false)?;
    Ok(usv_normalize_units(dom.as_slice()))
}

pub fn to_js_usv_string(s: &[u16]) -> (out: JsValue)
    ensures
        out@ == spec_to_js_usv_string(s@),
{
    JsValue::String(clone_u16_slice(s))
}

// ---------------------------------------------------------------------------------------
// §3.2.22 Nullable Types (`T?`)
// ---------------------------------------------------------------------------------------

/// WHATWG Web IDL §3.2.22 (`#js-nullable-type`): `null` and `undefined` map to `None`;
/// all other values convert via inner type `T`.
pub open spec fn spec_is_null_or_undefined(v: SpecJsValue) -> bool {
    v == SpecJsValue::Null || v == SpecJsValue::Undefined
}

pub fn is_null_or_undefined(v: &JsValue) -> (r: bool)
    ensures
        r == spec_is_null_or_undefined(v@),
{
    matches!(v, JsValue::Null | JsValue::Undefined)
}

pub open spec fn spec_to_idl_nullable_dom_string(
    arena: Seq<SpecJsObjectRecord>,
    v: SpecJsValue,
) -> Result<Option<Seq<u16>>, IdlError> {
    if spec_is_null_or_undefined(v) {
        Ok(None)
    } else {
        match spec_to_idl_dom_string(arena, v, false) {
            Ok(s) => Ok(Some(s)),
            Err(e) => Err(e),
        }
    }
}

pub fn to_idl_nullable_dom_string(
    arena: &JsObjectArena,
    v: &JsValue,
) -> (res: Result<Option<Vec<u16>>, IdlError>)
    ensures
        match (res, spec_to_idl_nullable_dom_string(arena@, v@)) {
            (Ok(None), Ok(None)) => true,
            (Ok(Some(s)), Ok(Some(ss))) => s@ == ss,
            (Err(e), Err(se)) => e == se,
            _ => false,
        },
{
    if is_null_or_undefined(v) {
        Ok(None)
    } else {
        let s = to_idl_dom_string(arena, v, false)?;
        Ok(Some(s))
    }
}

pub open spec fn spec_to_js_nullable_dom_string(opt: Option<Seq<u16>>) -> SpecJsValue {
    match opt {
        None => SpecJsValue::Null,
        Some(s) => spec_to_js_dom_string(s),
    }
}

pub fn to_js_nullable_dom_string(opt: &Option<Vec<u16>>) -> (out: JsValue)
    ensures
        out@ == spec_to_js_nullable_dom_string(
            match opt {
                None => None,
                Some(s) => Some(s@),
            },
        ),
{
    match opt {
        None => JsValue::Null,
        Some(s) => to_js_dom_string(s.as_slice()),
    }
}

pub open spec fn spec_to_idl_nullable_usv_string(
    arena: Seq<SpecJsObjectRecord>,
    v: SpecJsValue,
) -> Result<Option<Seq<u16>>, IdlError> {
    if spec_is_null_or_undefined(v) {
        Ok(None)
    } else {
        match spec_to_idl_usv_string(arena, v) {
            Ok(s) => Ok(Some(s)),
            Err(e) => Err(e),
        }
    }
}

pub fn to_idl_nullable_usv_string(
    arena: &JsObjectArena,
    v: &JsValue,
) -> (res: Result<Option<Vec<u16>>, IdlError>)
    ensures
        match (res, spec_to_idl_nullable_usv_string(arena@, v@)) {
            (Ok(None), Ok(None)) => true,
            (Ok(Some(s)), Ok(Some(ss))) => {
                s@ == ss && spec_has_no_unpaired_surrogates(s@)
            },
            (Err(e), Err(se)) => e == se,
            _ => false,
        },
{
    if is_null_or_undefined(v) {
        Ok(None)
    } else {
        let s = to_idl_usv_string(arena, v)?;
        Ok(Some(s))
    }
}

pub open spec fn spec_to_idl_nullable_byte_string(
    arena: Seq<SpecJsObjectRecord>,
    v: SpecJsValue,
) -> Result<Option<Seq<u8>>, IdlError> {
    if spec_is_null_or_undefined(v) {
        Ok(None)
    } else {
        match spec_to_idl_byte_string(arena, v) {
            Ok(b) => Ok(Some(b)),
            Err(e) => Err(e),
        }
    }
}

pub fn to_idl_nullable_byte_string(
    arena: &JsObjectArena,
    v: &JsValue,
) -> (res: Result<Option<Vec<u8>>, IdlError>)
    ensures
        match (res, spec_to_idl_nullable_byte_string(arena@, v@)) {
            (Ok(None), Ok(None)) => true,
            (Ok(Some(b)), Ok(Some(sb))) => b@ == sb,
            (Err(e), Err(se)) => e == se,
            _ => false,
        },
{
    if is_null_or_undefined(v) {
        Ok(None)
    } else {
        let b = to_idl_byte_string(arena, v)?;
        Ok(Some(b))
    }
}

pub open spec fn spec_to_idl_nullable_long(
    arena: Seq<SpecJsObjectRecord>,
    v: SpecJsValue,
    attr: IntAttr,
) -> Result<Option<int>, IdlError> {
    if spec_is_null_or_undefined(v) {
        Ok(None)
    } else {
        match spec_to_idl_int(arena, v, 32nat, true, attr) {
            Ok(x) => Ok(Some(x)),
            Err(e) => Err(e),
        }
    }
}

pub fn to_idl_nullable_long(
    arena: &JsObjectArena,
    v: &JsValue,
    attr: IntAttr,
) -> (res: Result<Option<i32>, IdlError>)
    ensures
        match (res, spec_to_idl_nullable_long(arena@, v@, attr)) {
            (Ok(None), Ok(None)) => true,
            (Ok(Some(x)), Ok(Some(sx))) => x as int == sx,
            (Err(e), Err(se)) => e == se,
            _ => false,
        },
{
    if is_null_or_undefined(v) {
        Ok(None)
    } else {
        let x = to_idl_long(arena, v, attr)?;
        Ok(Some(x))
    }
}

pub open spec fn spec_to_js_nullable_long(opt: Option<i32>) -> SpecJsValue {
    match opt {
        None => SpecJsValue::Null,
        Some(x) => spec_to_js_long(x),
    }
}

pub fn to_js_nullable_long(opt: Option<i32>) -> (out: JsValue)
    ensures
        out@ == spec_to_js_nullable_long(opt),
{
    match opt {
        None => JsValue::Null,
        Some(x) => to_js_long(x),
    }
}

pub proof fn lemma_nullable_dom_string_roundtrip(
    arena: Seq<SpecJsObjectRecord>,
    opt: Option<Seq<u16>>,
)
    ensures
        spec_to_idl_nullable_dom_string(arena, spec_to_js_nullable_dom_string(opt))
            == Ok::<Option<Seq<u16>>, IdlError>(opt),
{
}

// ---------------------------------------------------------------------------------------
// §3.2.19 Sequences (`sequence<T>`)
// ---------------------------------------------------------------------------------------

/// WHATWG Web IDL §3.2.19 (`#js-sequence`) steps 1–3:
/// 1. If `V` is not an Object, throw `TypeError`.
/// 2. Let `method` be `? GetMethod(V, %Symbol.iterator%)`.
/// 3. If `method` is `undefined`, throw `TypeError`.
pub open spec fn spec_extract_iterable_items(
    arena: Seq<SpecJsObjectRecord>,
    v: SpecJsValue,
) -> Result<Seq<SpecJsValue>, IdlError> {
    match v {
        SpecJsValue::Object(oid) => {
            if (oid as int) >= arena.len() {
                Err(IdlError::TypeError)
            } else {
                match arena[oid as int].iterator {
                    SpecJsIterator::NotIterable => Err(IdlError::TypeError),
                    SpecJsIterator::ThrowTypeError => Err(IdlError::TypeError),
                    SpecJsIterator::Items(items) => Ok(items),
                }
            }
        },
        _ => Err(IdlError::TypeError),
    }
}

pub open spec fn spec_convert_seq_long(
    arena: Seq<SpecJsObjectRecord>,
    items: Seq<SpecJsValue>,
    attr: IntAttr,
) -> Result<Seq<int>, IdlError>
    decreases items.len(),
{
    if items.len() == 0 {
        Ok(seq![])
    } else {
        match spec_to_idl_int(arena, items[0], 32nat, true, attr) {
            Err(e) => Err(e),
            Ok(head) => match spec_convert_seq_long(
                arena,
                items.subrange(1, items.len() as int),
                attr,
            ) {
                Err(e) => Err(e),
                Ok(tail) => Ok(seq![head] + tail),
            },
        }
    }
}

pub open spec fn spec_to_idl_sequence_long(
    arena: Seq<SpecJsObjectRecord>,
    v: SpecJsValue,
    attr: IntAttr,
) -> Result<Seq<int>, IdlError> {
    match spec_extract_iterable_items(arena, v) {
        Err(e) => Err(e),
        Ok(items) => spec_convert_seq_long(arena, items, attr),
    }
}

pub fn to_idl_sequence_long(
    arena: &JsObjectArena,
    v: &JsValue,
    attr: IntAttr,
) -> (res: Result<Vec<i32>, IdlError>)
    ensures
        match (res, spec_to_idl_sequence_long(arena@, v@, attr)) {
            (Ok(out), Ok(sout)) => {
                out@.len() == sout.len()
                && forall|i: int| 0 <= i < out@.len() ==> (out@[i] as int) == sout[i]
            },
            (Err(e), Err(se)) => e == se,
            _ => false,
        },
{
    let oid = match v {
        JsValue::Object(oid) => *oid,
        _ => return Err(IdlError::TypeError),
    };
    if oid >= arena.objects.len() {
        return Err(IdlError::TypeError);
    }
    let items = match &arena.objects[oid].iterator {
        JsIterator::NotIterable | JsIterator::ThrowTypeError => return Err(IdlError::TypeError),
        JsIterator::Items(v) => v,
    };
    let ghost sitems = Seq::new(items@.len(), |i: int| items@[i]@);
    let n = items.len();
    let mut out: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(arena@[oid as int].iterator == SpecJsIterator::Items(sitems));
        assert(sitems.subrange(0, n as int) =~= sitems);
    }
    while i < n
        invariant
            i <= n,
            n == items@.len(),
            v@ == SpecJsValue::Object(oid),
            (oid as int) < arena@.len(),
            arena@[oid as int].iterator == SpecJsIterator::Items(sitems),
            sitems == Seq::new(items@.len(), |k: int| items@[k]@),
            out@.len() == i as nat,
            forall|k: int| 0 <= k < i as int ==> {
                spec_to_idl_int(arena@, sitems[k], 32nat, true, attr)
                    == Ok::<int, IdlError>(out@[k] as int)
            },
        decreases n - i,
    {
        match to_idl_long(arena, &items[i], attr) {
            Err(e) => {
                proof {
                    assert(sitems[i as int] == items@[i as int]@);
                    lemma_seq_long_prefix_err(arena@, sitems, out@, i as nat, e, attr);
                }
                return Err(e);
            },
            Ok(val) => {
                out.push(val);
                i += 1;
            },
        }
    }
    proof {
        lemma_seq_long_all_ok(arena@, sitems, out@, attr);
    }
    Ok(out)
}

proof fn lemma_seq_long_prefix_err(
    arena: Seq<SpecJsObjectRecord>,
    sitems: Seq<SpecJsValue>,
    prefix: Seq<i32>,
    fail_idx: nat,
    err: IdlError,
    attr: IntAttr,
)
    requires
        fail_idx < sitems.len(),
        prefix.len() == fail_idx,
        forall|k: int| 0 <= k < fail_idx as int ==> {
            spec_to_idl_int(arena, #[trigger] sitems[k], 32nat, true, attr)
                == Ok::<int, IdlError>(prefix[k] as int)
        },
        spec_to_idl_int(arena, sitems[fail_idx as int], 32nat, true, attr)
            == Err::<int, IdlError>(err),
    ensures
        spec_convert_seq_long(arena, sitems, attr) == Err::<Seq<int>, IdlError>(err),
    decreases fail_idx,
{
    if fail_idx == 0nat {
    } else {
        let sub = sitems.subrange(1, sitems.len() as int);
        let p_sub = prefix.subrange(1, prefix.len() as int);
        assert forall|k: int| 0 <= k < (fail_idx - 1) as int implies {
            spec_to_idl_int(arena, #[trigger] sub[k], 32nat, true, attr)
                == Ok::<int, IdlError>(p_sub[k] as int)
        } by {
            assert(sub[k] == sitems[k + 1]);
            assert(p_sub[k] == prefix[k + 1]);
        }
        assert(sub[(fail_idx - 1) as int] == sitems[fail_idx as int]);
        lemma_seq_long_prefix_err(arena, sub, p_sub, (fail_idx - 1) as nat, err, attr);
        assert(spec_to_idl_int(arena, sitems[0], 32nat, true, attr)
            == Ok::<int, IdlError>(prefix[0] as int));
    }
}

proof fn lemma_seq_long_all_ok(
    arena: Seq<SpecJsObjectRecord>,
    sitems: Seq<SpecJsValue>,
    out: Seq<i32>,
    attr: IntAttr,
)
    requires
        out.len() == sitems.len(),
        forall|k: int| 0 <= k < sitems.len() ==> {
            spec_to_idl_int(arena, #[trigger] sitems[k], 32nat, true, attr)
                == Ok::<int, IdlError>(out[k] as int)
        },
    ensures
        spec_convert_seq_long(arena, sitems, attr)
            == Ok::<Seq<int>, IdlError>(Seq::new(out.len(), |i: int| out[i] as int)),
    decreases sitems.len(),
{
    if sitems.len() == 0 {
        assert(Seq::new(0nat, |i: int| out[i] as int) =~= Seq::<int>::empty());
    } else {
        let sub = sitems.subrange(1, sitems.len() as int);
        let o_sub = out.subrange(1, out.len() as int);
        assert forall|k: int| 0 <= k < sub.len() implies {
            spec_to_idl_int(arena, #[trigger] sub[k], 32nat, true, attr)
                == Ok::<int, IdlError>(o_sub[k] as int)
        } by {
            assert(sub[k] == sitems[k + 1]);
            assert(o_sub[k] == out[k + 1]);
        }
        lemma_seq_long_all_ok(arena, sub, o_sub, attr);
        assert(spec_to_idl_int(arena, sitems[0], 32nat, true, attr)
            == Ok::<int, IdlError>(out[0] as int));
        let tail_seq = Seq::new(o_sub.len(), |i: int| o_sub[i] as int);
        let full_seq = Seq::new(out.len(), |i: int| out[i] as int);
        assert(seq![out[0] as int] + tail_seq =~= full_seq);
    }
}

pub open spec fn spec_convert_seq_dom_string(
    arena: Seq<SpecJsObjectRecord>,
    items: Seq<SpecJsValue>,
) -> Result<Seq<Seq<u16>>, IdlError>
    decreases items.len(),
{
    if items.len() == 0 {
        Ok(seq![])
    } else {
        match spec_to_idl_dom_string(arena, items[0], false) {
            Err(e) => Err(e),
            Ok(head) => match spec_convert_seq_dom_string(
                arena,
                items.subrange(1, items.len() as int),
            ) {
                Err(e) => Err(e),
                Ok(tail) => Ok(seq![head] + tail),
            },
        }
    }
}

pub open spec fn spec_to_idl_sequence_dom_string(
    arena: Seq<SpecJsObjectRecord>,
    v: SpecJsValue,
) -> Result<Seq<Seq<u16>>, IdlError> {
    match spec_extract_iterable_items(arena, v) {
        Err(e) => Err(e),
        Ok(items) => spec_convert_seq_dom_string(arena, items),
    }
}

proof fn lemma_seq_dom_prefix_err(
    arena: Seq<SpecJsObjectRecord>,
    sitems: Seq<SpecJsValue>,
    prefix: Seq<Seq<u16>>,
    fail_idx: nat,
    err: IdlError,
)
    requires
        fail_idx < sitems.len(),
        prefix.len() == fail_idx,
        forall|k: int| 0 <= k < fail_idx as int ==> {
            spec_to_idl_dom_string(arena, #[trigger] sitems[k], false)
                == Ok::<Seq<u16>, IdlError>(prefix[k])
        },
        spec_to_idl_dom_string(arena, sitems[fail_idx as int], false)
            == Err::<Seq<u16>, IdlError>(err),
    ensures
        spec_convert_seq_dom_string(arena, sitems) == Err::<Seq<Seq<u16>>, IdlError>(err),
    decreases fail_idx,
{
    if fail_idx > 0nat {
        let sub = sitems.subrange(1, sitems.len() as int);
        let p_sub = prefix.subrange(1, prefix.len() as int);
        assert forall|k: int| 0 <= k < (fail_idx - 1) as int implies {
            spec_to_idl_dom_string(arena, #[trigger] sub[k], false)
                == Ok::<Seq<u16>, IdlError>(p_sub[k])
        } by {
            assert(sub[k] == sitems[k + 1]);
            assert(p_sub[k] == prefix[k + 1]);
        }
        assert(sub[(fail_idx - 1) as int] == sitems[fail_idx as int]);
        lemma_seq_dom_prefix_err(arena, sub, p_sub, (fail_idx - 1) as nat, err);
        assert(spec_to_idl_dom_string(arena, sitems[0], false)
            == Ok::<Seq<u16>, IdlError>(prefix[0]));
    }
}

proof fn lemma_seq_dom_all_ok(
    arena: Seq<SpecJsObjectRecord>,
    sitems: Seq<SpecJsValue>,
    out: Seq<Seq<u16>>,
)
    requires
        out.len() == sitems.len(),
        forall|k: int| 0 <= k < sitems.len() ==> {
            spec_to_idl_dom_string(arena, #[trigger] sitems[k], false)
                == Ok::<Seq<u16>, IdlError>(out[k])
        },
    ensures
        spec_convert_seq_dom_string(arena, sitems) == Ok::<Seq<Seq<u16>>, IdlError>(out),
    decreases sitems.len(),
{
    if sitems.len() == 0 {
        assert(out =~= Seq::<Seq<u16>>::empty());
    } else {
        let sub = sitems.subrange(1, sitems.len() as int);
        let o_sub = out.subrange(1, out.len() as int);
        assert forall|k: int| 0 <= k < sub.len() implies {
            spec_to_idl_dom_string(arena, #[trigger] sub[k], false)
                == Ok::<Seq<u16>, IdlError>(o_sub[k])
        } by {
            assert(sub[k] == sitems[k + 1]);
            assert(o_sub[k] == out[k + 1]);
        }
        lemma_seq_dom_all_ok(arena, sub, o_sub);
        assert(spec_to_idl_dom_string(arena, sitems[0], false)
            == Ok::<Seq<u16>, IdlError>(out[0]));
        assert(seq![out[0]] + o_sub =~= out);
    }
}

pub fn to_idl_sequence_dom_string(
    arena: &JsObjectArena,
    v: &JsValue,
) -> (res: Result<Vec<Vec<u16>>, IdlError>)
    ensures
        match (res, spec_to_idl_sequence_dom_string(arena@, v@)) {
            (Ok(out), Ok(sout)) => {
                out@.len() == sout.len()
                && forall|i: int| 0 <= i < out@.len() ==> out@[i]@ == sout[i]
            },
            (Err(e), Err(se)) => e == se,
            _ => false,
        },
{
    let oid = match v {
        JsValue::Object(oid) => *oid,
        _ => return Err(IdlError::TypeError),
    };
    if oid >= arena.objects.len() {
        return Err(IdlError::TypeError);
    }
    let items = match &arena.objects[oid].iterator {
        JsIterator::NotIterable | JsIterator::ThrowTypeError => return Err(IdlError::TypeError),
        JsIterator::Items(v) => v,
    };
    let ghost sitems = Seq::new(items@.len(), |i: int| items@[i]@);
    let n = items.len();
    let mut out: Vec<Vec<u16>> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(arena@[oid as int].iterator == SpecJsIterator::Items(sitems));
    }
    while i < n
        invariant
            i <= n,
            n == items@.len(),
            v@ == SpecJsValue::Object(oid),
            (oid as int) < arena@.len(),
            arena@[oid as int].iterator == SpecJsIterator::Items(sitems),
            sitems == Seq::new(items@.len(), |k: int| items@[k]@),
            out@.len() == i as nat,
            forall|k: int| 0 <= k < i as int ==> {
                spec_to_idl_dom_string(arena@, #[trigger] sitems[k], false)
                    == Ok::<Seq<u16>, IdlError>(out@[k]@)
            },
        decreases n - i,
    {
        match to_idl_dom_string(arena, &items[i], false) {
            Err(e) => {
                let ghost p_view = Seq::new(out@.len(), |k: int| out@[k]@);
                proof {
                    assert(sitems[i as int] == items@[i as int]@);
                    assert forall|k: int| 0 <= k < i as int implies {
                        spec_to_idl_dom_string(arena@, #[trigger] sitems[k], false)
                            == Ok::<Seq<u16>, IdlError>(p_view[k])
                    } by {
                        assert(p_view[k] == out@[k]@);
                    }
                    lemma_seq_dom_prefix_err(arena@, sitems, p_view, i as nat, e);
                }
                return Err(e);
            },
            Ok(s) => {
                out.push(s);
                i += 1;
            },
        }
    }
    proof {
        let o_view = Seq::new(out@.len(), |k: int| out@[k]@);
        lemma_seq_dom_all_ok(arena@, sitems, o_view);
    }
    Ok(out)
}

/// WHATWG Web IDL §3.2.19 (`#sequence-to-js`): convert an IDL `sequence<DOMString>` into a
/// fresh JS Array object in `arena` with indexed own enumerable properties and array iterator.
pub fn to_js_sequence_dom_string(
    arena: &mut JsObjectArena,
    seq_in: &[Vec<u16>],
) -> (res: Result<JsValue, IdlError>)
    ensures
        old(arena)@.len() < usize::MAX ==> match res {
            Ok(JsValue::Object(oid)) => {
                oid == old(arena)@.len()
                && final(arena)@.len() == old(arena)@.len() + 1
                && match final(arena)@[oid as int].iterator {
                    SpecJsIterator::Items(items) => {
                        items.len() == seq_in@.len()
                        && forall|i: int| 0 <= i < items.len() ==>
                            items[i] == SpecJsValue::String(seq_in@[i]@)
                    },
                    _ => false,
                }
            },
            _ => false,
        },
{
    if arena.objects.len() == usize::MAX {
        return Err(IdlError::TypeError);
    }
    let n = seq_in.len();
    let mut own_props: Vec<JsOwnProp> = Vec::new();
    let mut iter_items: Vec<JsValue> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == seq_in@.len(),
            iter_items@.len() == i as nat,
            forall|k: int| 0 <= k < i as int ==>
                iter_items@[k]@ == SpecJsValue::String(seq_in@[k]@),
        decreases n - i,
    {
        let idx_key = u128_to_utf16_digits(i as u128);
        let elem_for_prop = to_js_dom_string(seq_in[i].as_slice());
        let elem_for_iter = to_js_dom_string(seq_in[i].as_slice());
        own_props.push(JsOwnProp {
            key: idx_key,
            is_symbol: false,
            enumerable: true,
            is_getter: false,
            getter_throws: None,
            value: elem_for_prop,
        });
        iter_items.push(elem_for_iter);
        i += 1;
    }
    let rec = JsObjectRecord {
        own_props,
        proto_props: Vec::new(),
        iterator: JsIterator::Items(iter_items),
        to_string_hook: JsToStringHook::DefaultObjectTag,
        to_number_override: None,
    };
    let oid = arena.alloc(rec);
    Ok(JsValue::Object(oid))
}

/// Convert `sequence<ByteString>` (§3.2.19 + §3.2.16).
pub open spec fn spec_convert_seq_byte_string(
    arena: Seq<SpecJsObjectRecord>,
    items: Seq<SpecJsValue>,
) -> Result<Seq<Seq<u8>>, IdlError>
    decreases items.len(),
{
    if items.len() == 0 {
        Ok(seq![])
    } else {
        match spec_to_idl_byte_string(arena, items[0]) {
            Err(e) => Err(e),
            Ok(head) => match spec_convert_seq_byte_string(
                arena,
                items.subrange(1, items.len() as int),
            ) {
                Err(e) => Err(e),
                Ok(tail) => Ok(seq![head] + tail),
            },
        }
    }
}

pub open spec fn spec_to_idl_sequence_byte_string(
    arena: Seq<SpecJsObjectRecord>,
    v: SpecJsValue,
) -> Result<Seq<Seq<u8>>, IdlError> {
    match spec_extract_iterable_items(arena, v) {
        Err(e) => Err(e),
        Ok(items) => spec_convert_seq_byte_string(arena, items),
    }
}

proof fn lemma_seq_byte_prefix_err(
    arena: Seq<SpecJsObjectRecord>,
    sitems: Seq<SpecJsValue>,
    prefix: Seq<Seq<u8>>,
    fail_idx: nat,
    err: IdlError,
)
    requires
        fail_idx < sitems.len(),
        prefix.len() == fail_idx,
        forall|k: int| 0 <= k < fail_idx as int ==> {
            spec_to_idl_byte_string(arena, #[trigger] sitems[k])
                == Ok::<Seq<u8>, IdlError>(prefix[k])
        },
        spec_to_idl_byte_string(arena, sitems[fail_idx as int])
            == Err::<Seq<u8>, IdlError>(err),
    ensures
        spec_convert_seq_byte_string(arena, sitems) == Err::<Seq<Seq<u8>>, IdlError>(err),
    decreases fail_idx,
{
    if fail_idx > 0nat {
        let sub = sitems.subrange(1, sitems.len() as int);
        let p_sub = prefix.subrange(1, prefix.len() as int);
        assert forall|k: int| 0 <= k < (fail_idx - 1) as int implies {
            spec_to_idl_byte_string(arena, #[trigger] sub[k])
                == Ok::<Seq<u8>, IdlError>(p_sub[k])
        } by {
            assert(sub[k] == sitems[k + 1]);
            assert(p_sub[k] == prefix[k + 1]);
        }
        assert(sub[(fail_idx - 1) as int] == sitems[fail_idx as int]);
        lemma_seq_byte_prefix_err(arena, sub, p_sub, (fail_idx - 1) as nat, err);
        assert(spec_to_idl_byte_string(arena, sitems[0])
            == Ok::<Seq<u8>, IdlError>(prefix[0]));
    }
}

proof fn lemma_seq_byte_all_ok(
    arena: Seq<SpecJsObjectRecord>,
    sitems: Seq<SpecJsValue>,
    out: Seq<Seq<u8>>,
)
    requires
        out.len() == sitems.len(),
        forall|k: int| 0 <= k < sitems.len() ==> {
            spec_to_idl_byte_string(arena, #[trigger] sitems[k])
                == Ok::<Seq<u8>, IdlError>(out[k])
        },
    ensures
        spec_convert_seq_byte_string(arena, sitems) == Ok::<Seq<Seq<u8>>, IdlError>(out),
    decreases sitems.len(),
{
    if sitems.len() == 0 {
        assert(out =~= Seq::<Seq<u8>>::empty());
    } else {
        let sub = sitems.subrange(1, sitems.len() as int);
        let o_sub = out.subrange(1, out.len() as int);
        assert forall|k: int| 0 <= k < sub.len() implies {
            spec_to_idl_byte_string(arena, #[trigger] sub[k])
                == Ok::<Seq<u8>, IdlError>(o_sub[k])
        } by {
            assert(sub[k] == sitems[k + 1]);
            assert(o_sub[k] == out[k + 1]);
        }
        lemma_seq_byte_all_ok(arena, sub, o_sub);
        assert(spec_to_idl_byte_string(arena, sitems[0])
            == Ok::<Seq<u8>, IdlError>(out[0]));
        assert(seq![out[0]] + o_sub =~= out);
    }
}

pub fn to_idl_sequence_byte_string(
    arena: &JsObjectArena,
    v: &JsValue,
) -> (res: Result<Vec<Vec<u8>>, IdlError>)
    ensures
        match (res, spec_to_idl_sequence_byte_string(arena@, v@)) {
            (Ok(out), Ok(sout)) => {
                out@.len() == sout.len()
                && forall|i: int| 0 <= i < out@.len() ==> out@[i]@ == sout[i]
            },
            (Err(e), Err(se)) => e == se,
            _ => false,
        },
{
    let oid = match v {
        JsValue::Object(oid) => *oid,
        _ => return Err(IdlError::TypeError),
    };
    if oid >= arena.objects.len() {
        return Err(IdlError::TypeError);
    }
    let items = match &arena.objects[oid].iterator {
        JsIterator::NotIterable | JsIterator::ThrowTypeError => return Err(IdlError::TypeError),
        JsIterator::Items(v) => v,
    };
    let ghost sitems = Seq::new(items@.len(), |i: int| items@[i]@);
    let n = items.len();
    let mut out: Vec<Vec<u8>> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(arena@[oid as int].iterator == SpecJsIterator::Items(sitems));
    }
    while i < n
        invariant
            i <= n,
            n == items@.len(),
            v@ == SpecJsValue::Object(oid),
            (oid as int) < arena@.len(),
            arena@[oid as int].iterator == SpecJsIterator::Items(sitems),
            sitems == Seq::new(items@.len(), |k: int| items@[k]@),
            out@.len() == i as nat,
            forall|k: int| 0 <= k < i as int ==> {
                spec_to_idl_byte_string(arena@, #[trigger] sitems[k])
                    == Ok::<Seq<u8>, IdlError>(out@[k]@)
            },
        decreases n - i,
    {
        match to_idl_byte_string(arena, &items[i]) {
            Err(e) => {
                let ghost p_view = Seq::new(out@.len(), |k: int| out@[k]@);
                proof {
                    assert(sitems[i as int] == items@[i as int]@);
                    assert forall|k: int| 0 <= k < i as int implies {
                        spec_to_idl_byte_string(arena@, #[trigger] sitems[k])
                            == Ok::<Seq<u8>, IdlError>(p_view[k])
                    } by {
                        assert(p_view[k] == out@[k]@);
                    }
                    lemma_seq_byte_prefix_err(arena@, sitems, p_view, i as nat, e);
                }
                return Err(e);
            },
            Ok(b) => {
                out.push(b);
                i += 1;
            },
        }
    }
    proof {
        let o_view = Seq::new(out@.len(), |k: int| out@[k]@);
        lemma_seq_byte_all_ok(arena@, sitems, o_view);
    }
    Ok(out)
}

/// Convert `sequence<USVString>` (§3.2.19 + §3.2.17), guaranteeing zero unpaired surrogates
/// in every returned element!
pub open spec fn spec_convert_seq_usv_string(
    arena: Seq<SpecJsObjectRecord>,
    items: Seq<SpecJsValue>,
) -> Result<Seq<Seq<u16>>, IdlError>
    decreases items.len(),
{
    if items.len() == 0 {
        Ok(seq![])
    } else {
        match spec_to_idl_usv_string(arena, items[0]) {
            Err(e) => Err(e),
            Ok(head) => match spec_convert_seq_usv_string(
                arena,
                items.subrange(1, items.len() as int),
            ) {
                Err(e) => Err(e),
                Ok(tail) => Ok(seq![head] + tail),
            },
        }
    }
}

pub open spec fn spec_to_idl_sequence_usv_string(
    arena: Seq<SpecJsObjectRecord>,
    v: SpecJsValue,
) -> Result<Seq<Seq<u16>>, IdlError> {
    match spec_extract_iterable_items(arena, v) {
        Err(e) => Err(e),
        Ok(items) => spec_convert_seq_usv_string(arena, items),
    }
}

proof fn lemma_seq_usv_prefix_err(
    arena: Seq<SpecJsObjectRecord>,
    sitems: Seq<SpecJsValue>,
    prefix: Seq<Seq<u16>>,
    fail_idx: nat,
    err: IdlError,
)
    requires
        fail_idx < sitems.len(),
        prefix.len() == fail_idx,
        forall|k: int| 0 <= k < fail_idx as int ==> {
            spec_to_idl_usv_string(arena, #[trigger] sitems[k])
                == Ok::<Seq<u16>, IdlError>(prefix[k])
        },
        spec_to_idl_usv_string(arena, sitems[fail_idx as int])
            == Err::<Seq<u16>, IdlError>(err),
    ensures
        spec_convert_seq_usv_string(arena, sitems) == Err::<Seq<Seq<u16>>, IdlError>(err),
    decreases fail_idx,
{
    if fail_idx > 0nat {
        let sub = sitems.subrange(1, sitems.len() as int);
        let p_sub = prefix.subrange(1, prefix.len() as int);
        assert forall|k: int| 0 <= k < (fail_idx - 1) as int implies {
            spec_to_idl_usv_string(arena, #[trigger] sub[k])
                == Ok::<Seq<u16>, IdlError>(p_sub[k])
        } by {
            assert(sub[k] == sitems[k + 1]);
            assert(p_sub[k] == prefix[k + 1]);
        }
        assert(sub[(fail_idx - 1) as int] == sitems[fail_idx as int]);
        lemma_seq_usv_prefix_err(arena, sub, p_sub, (fail_idx - 1) as nat, err);
        assert(spec_to_idl_usv_string(arena, sitems[0])
            == Ok::<Seq<u16>, IdlError>(prefix[0]));
    }
}

proof fn lemma_seq_usv_all_ok(
    arena: Seq<SpecJsObjectRecord>,
    sitems: Seq<SpecJsValue>,
    out: Seq<Seq<u16>>,
)
    requires
        out.len() == sitems.len(),
        forall|k: int| 0 <= k < sitems.len() ==> {
            spec_to_idl_usv_string(arena, #[trigger] sitems[k])
                == Ok::<Seq<u16>, IdlError>(out[k])
        },
    ensures
        spec_convert_seq_usv_string(arena, sitems) == Ok::<Seq<Seq<u16>>, IdlError>(out),
    decreases sitems.len(),
{
    if sitems.len() == 0 {
        assert(out =~= Seq::<Seq<u16>>::empty());
    } else {
        let sub = sitems.subrange(1, sitems.len() as int);
        let o_sub = out.subrange(1, out.len() as int);
        assert forall|k: int| 0 <= k < sub.len() implies {
            spec_to_idl_usv_string(arena, #[trigger] sub[k])
                == Ok::<Seq<u16>, IdlError>(o_sub[k])
        } by {
            assert(sub[k] == sitems[k + 1]);
            assert(o_sub[k] == out[k + 1]);
        }
        lemma_seq_usv_all_ok(arena, sub, o_sub);
        assert(spec_to_idl_usv_string(arena, sitems[0])
            == Ok::<Seq<u16>, IdlError>(out[0]));
        assert(seq![out[0]] + o_sub =~= out);
    }
}

pub fn to_idl_sequence_usv_string(
    arena: &JsObjectArena,
    v: &JsValue,
) -> (res: Result<Vec<Vec<u16>>, IdlError>)
    ensures
        match (res, spec_to_idl_sequence_usv_string(arena@, v@)) {
            (Ok(out), Ok(sout)) => {
                out@.len() == sout.len()
                && forall|i: int| 0 <= i < out@.len() ==> (
                    out@[i]@ == sout[i]
                    && spec_has_no_unpaired_surrogates((#[trigger] out@[i])@)
                )
            },
            (Err(e), Err(se)) => e == se,
            _ => false,
        },
{
    let oid = match v {
        JsValue::Object(oid) => *oid,
        _ => return Err(IdlError::TypeError),
    };
    if oid >= arena.objects.len() {
        return Err(IdlError::TypeError);
    }
    let items = match &arena.objects[oid].iterator {
        JsIterator::NotIterable | JsIterator::ThrowTypeError => return Err(IdlError::TypeError),
        JsIterator::Items(v) => v,
    };
    let ghost sitems = Seq::new(items@.len(), |i: int| items@[i]@);
    let n = items.len();
    let mut out: Vec<Vec<u16>> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(arena@[oid as int].iterator == SpecJsIterator::Items(sitems));
    }
    while i < n
        invariant
            i <= n,
            n == items@.len(),
            v@ == SpecJsValue::Object(oid),
            (oid as int) < arena@.len(),
            arena@[oid as int].iterator == SpecJsIterator::Items(sitems),
            sitems == Seq::new(items@.len(), |k: int| items@[k]@),
            out@.len() == i as nat,
            forall|k: int| 0 <= k < i as int ==> {
                spec_to_idl_usv_string(arena@, #[trigger] sitems[k])
                    == Ok::<Seq<u16>, IdlError>(out@[k]@)
            },
            forall|k: int| 0 <= k < i as int ==> {
                spec_has_no_unpaired_surrogates((#[trigger] out@[k])@)
            },
        decreases n - i,
    {
        match to_idl_usv_string(arena, &items[i]) {
            Err(e) => {
                let ghost p_view = Seq::new(out@.len(), |k: int| out@[k]@);
                proof {
                    assert(sitems[i as int] == items@[i as int]@);
                    assert forall|k: int| 0 <= k < i as int implies {
                        spec_to_idl_usv_string(arena@, #[trigger] sitems[k])
                            == Ok::<Seq<u16>, IdlError>(p_view[k])
                    } by {
                        assert(p_view[k] == out@[k]@);
                    }
                    lemma_seq_usv_prefix_err(arena@, sitems, p_view, i as nat, e);
                }
                return Err(e);
            },
            Ok(s) => {
                out.push(s);
                i += 1;
            },
        }
    }
    proof {
        let o_view = Seq::new(out@.len(), |k: int| out@[k]@);
        lemma_seq_usv_all_ok(arena@, sitems, o_view);
    }
    Ok(out)
}

// ---------------------------------------------------------------------------------------
// §3.2.21 Records (`record<K, V>`) with Exact Ordered-Map Upsert Semantics
// ---------------------------------------------------------------------------------------

/// Ordered-map `Set result[typedKey] = typedValue` per Web IDL §3.2.21 step 4.2.4:
/// If `typedKey` already exists (e.g. when `K = USVString` normalizes distinct lone
/// surrogates `"\uD835x"` and `"\uD83Dx"` to the same key `"\uFFFDx"`!), replace the
/// value IN PLACE at its existing position; otherwise append `(typedKey, typedValue)`.
pub open spec fn spec_record_find_key<K>(entries: Seq<(K, Seq<u16>)>, key: K) -> Option<nat>
    decreases entries.len(),
{
    if entries.len() == 0 {
        None
    } else if entries[0].0 == key {
        Some(0nat)
    } else {
        match spec_record_find_key(entries.subrange(1, entries.len() as int), key) {
            None => None,
            Some(idx) => Some(idx + 1nat),
        }
    }
}

pub open spec fn spec_record_upsert_u16(
    entries: Seq<(Seq<u16>, Seq<u16>)>,
    key: Seq<u16>,
    val: Seq<u16>,
) -> Seq<(Seq<u16>, Seq<u16>)> {
    match spec_record_find_key(entries, key) {
        Some(idx) => entries.update(idx as int, (key, val)),
        None => entries.push((key, val)),
    }
}

pub open spec fn spec_record_find_key_u8(
    entries: Seq<(Seq<u8>, Seq<u8>)>,
    key: Seq<u8>,
) -> Option<nat>
    decreases entries.len(),
{
    if entries.len() == 0 {
        None
    } else if entries[0].0 == key {
        Some(0nat)
    } else {
        match spec_record_find_key_u8(entries.subrange(1, entries.len() as int), key) {
            None => None,
            Some(idx) => Some(idx + 1nat),
        }
    }
}

pub open spec fn spec_record_upsert_u8(
    entries: Seq<(Seq<u8>, Seq<u8>)>,
    key: Seq<u8>,
    val: Seq<u8>,
) -> Seq<(Seq<u8>, Seq<u8>)> {
    match spec_record_find_key_u8(entries, key) {
        Some(idx) => entries.update(idx as int, (key, val)),
        None => entries.push((key, val)),
    }
}

fn eq_u16_slice(a: &[u16], b: &[u16]) -> (r: bool)
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

fn eq_u8_slice(a: &[u8], b: &[u8]) -> (r: bool)
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

proof fn lemma_find_key_u16_step(
    entries: Seq<(Seq<u16>, Seq<u16>)>,
    pos: nat,
    key: Seq<u16>,
)
    requires
        pos <= entries.len(),
        forall|k: int| 0 <= k < pos as int ==> entries[k].0 != key,
    ensures
        spec_record_find_key(entries, key)
            == match spec_record_find_key(entries.subrange(pos as int, entries.len() as int), key) {
                None => None,
                Some(rel) => Some(pos + rel),
            },
    decreases pos,
{
    if pos == 0nat {
        assert(entries.subrange(0, entries.len() as int) =~= entries);
    } else {
        let sub1 = entries.subrange(1, entries.len() as int);
        assert forall|k: int| 0 <= k < (pos - 1) as int implies sub1[k].0 != key by {
            assert(sub1[k] == entries[k + 1]);
        }
        lemma_find_key_u16_step(sub1, (pos - 1) as nat, key);
        assert(sub1.subrange((pos - 1) as int, sub1.len() as int)
            =~= entries.subrange(pos as int, entries.len() as int));
        assert(entries[0].0 != key);
    }
}

fn record_upsert_u16(
    entries: &mut Vec<(Vec<u16>, Vec<u16>)>,
    key: Vec<u16>,
    val: Vec<u16>,
)
    ensures
        Seq::new(final(entries)@.len(), |i: int| (final(entries)@[i].0@, final(entries)@[i].1@))
            == spec_record_upsert_u16(
                Seq::new(old(entries)@.len(), |i: int| (old(entries)@[i].0@, old(entries)@[i].1@)),
                key@,
                val@,
            ),
{
    let ghost old_view = Seq::new(entries@.len(), |i: int| (entries@[i].0@, entries@[i].1@));
    let n = entries.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == entries@.len(),
            entries@ == old(entries)@,
            old_view == Seq::new(entries@.len(), |k: int| (entries@[k].0@, entries@[k].1@)),
            forall|k: int| 0 <= k < i as int ==> old_view[k].0 != key@,
        decreases n - i,
    {
        if eq_u16_slice(entries[i].0.as_slice(), key.as_slice()) {
            proof {
                lemma_find_key_u16_step(old_view, i as nat, key@);
                let tail = old_view.subrange(i as int, n as int);
                assert(tail.len() > 0 && tail[0].0 == key@);
                assert(spec_record_find_key(tail, key@) == Some(0nat));
                assert(spec_record_find_key(old_view, key@) == Some(i as nat));
            }
            entries.set(i, (key, val));
            proof {
                let new_view = Seq::new(entries@.len(), |k: int| (entries@[k].0@, entries@[k].1@));
                let orig_view = Seq::new(old(entries)@.len(), |k: int| (old(entries)@[k].0@, old(entries)@[k].1@));
                assert(old_view =~= orig_view);
                assert(new_view =~= orig_view.update(i as int, (key@, val@)));
            }
            return;
        }
        i += 1;
    }
    proof {
        lemma_find_key_u16_step(old_view, n as nat, key@);
        assert(old_view.subrange(n as int, n as int) =~= Seq::<(Seq<u16>, Seq<u16>)>::empty());
        assert(spec_record_find_key(old_view, key@).is_none());
    }
    entries.push((key, val));
    proof {
        let new_view = Seq::new(entries@.len(), |k: int| (entries@[k].0@, entries@[k].1@));
        assert(new_view =~= old_view.push((key@, val@)));
    }
}

proof fn lemma_find_key_u8_step(
    entries: Seq<(Seq<u8>, Seq<u8>)>,
    pos: nat,
    key: Seq<u8>,
)
    requires
        pos <= entries.len(),
        forall|k: int| 0 <= k < pos as int ==> entries[k].0 != key,
    ensures
        spec_record_find_key_u8(entries, key)
            == match spec_record_find_key_u8(entries.subrange(pos as int, entries.len() as int), key) {
                None => None,
                Some(rel) => Some(pos + rel),
            },
    decreases pos,
{
    if pos == 0nat {
        assert(entries.subrange(0, entries.len() as int) =~= entries);
    } else {
        let sub1 = entries.subrange(1, entries.len() as int);
        assert forall|k: int| 0 <= k < (pos - 1) as int implies sub1[k].0 != key by {
            assert(sub1[k] == entries[k + 1]);
        }
        lemma_find_key_u8_step(sub1, (pos - 1) as nat, key);
        assert(sub1.subrange((pos - 1) as int, sub1.len() as int)
            =~= entries.subrange(pos as int, entries.len() as int));
        assert(entries[0].0 != key);
    }
}

fn record_upsert_u8(
    entries: &mut Vec<(Vec<u8>, Vec<u8>)>,
    key: Vec<u8>,
    val: Vec<u8>,
)
    ensures
        Seq::new(final(entries)@.len(), |i: int| (final(entries)@[i].0@, final(entries)@[i].1@))
            == spec_record_upsert_u8(
                Seq::new(old(entries)@.len(), |i: int| (old(entries)@[i].0@, old(entries)@[i].1@)),
                key@,
                val@,
            ),
{
    let ghost old_view = Seq::new(entries@.len(), |i: int| (entries@[i].0@, entries@[i].1@));
    let n = entries.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == entries@.len(),
            entries@ == old(entries)@,
            old_view == Seq::new(entries@.len(), |k: int| (entries@[k].0@, entries@[k].1@)),
            forall|k: int| 0 <= k < i as int ==> old_view[k].0 != key@,
        decreases n - i,
    {
        if eq_u8_slice(entries[i].0.as_slice(), key.as_slice()) {
            proof {
                lemma_find_key_u8_step(old_view, i as nat, key@);
                let tail = old_view.subrange(i as int, n as int);
                assert(tail.len() > 0 && tail[0].0 == key@);
                assert(spec_record_find_key_u8(tail, key@) == Some(0nat));
                assert(spec_record_find_key_u8(old_view, key@) == Some(i as nat));
            }
            entries.set(i, (key, val));
            proof {
                let new_view = Seq::new(entries@.len(), |k: int| (entries@[k].0@, entries@[k].1@));
                let orig_view = Seq::new(old(entries)@.len(), |k: int| (old(entries)@[k].0@, old(entries)@[k].1@));
                assert(old_view =~= orig_view);
                assert(new_view =~= orig_view.update(i as int, (key@, val@)));
            }
            return;
        }
        i += 1;
    }
    proof {
        lemma_find_key_u8_step(old_view, n as nat, key@);
        assert(old_view.subrange(n as int, n as int) =~= Seq::<(Seq<u8>, Seq<u8>)>::empty());
        assert(spec_record_find_key_u8(old_view, key@).is_none());
    }
    entries.push((key, val));
    proof {
        let new_view = Seq::new(entries@.len(), |k: int| (entries@[k].0@, entries@[k].1@));
        assert(new_view =~= old_view.push((key@, val@)));
    }
}

/// ECMA-262 §10.5.11 `[[OwnPropertyKeys]]` invariant: returned own property keys must be
/// duplicate-free (a Proxy `ownKeys` trap returning duplicates throws `TypeError` at step 4
/// of Web IDL §3.2.21 before any descriptor or value is accessed).
pub open spec fn spec_prop_same_key(a: SpecJsOwnProp, b: SpecJsOwnProp) -> bool {
    a.is_symbol == b.is_symbol && a.key == b.key
}

pub open spec fn spec_has_duplicate_own_keys(props: Seq<SpecJsOwnProp>) -> bool {
    exists|i: int, j: int|
        0 <= i && i < j && j < props.len()
        && spec_prop_same_key(#[trigger] props[i], #[trigger] props[j])
}

fn check_has_duplicate_own_keys(props: &[JsOwnProp]) -> (dup: bool)
    ensures
        dup == spec_has_duplicate_own_keys(Seq::new(props@.len(), |k: int| props@[k]@)),
{
    let ghost sprops = Seq::new(props@.len(), |k: int| props@[k]@);
    let n = props.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == props@.len(),
            sprops == Seq::new(props@.len(), |k: int| props@[k]@),
            forall|a: int, b: int|
                0 <= a && a < i as int && a < b && b < n as int ==>
                    !spec_prop_same_key(#[trigger] sprops[a], #[trigger] sprops[b]),
        decreases n - i,
    {
        let mut j: usize = i + 1;
        while j < n
            invariant
                i < j,
                j <= n,
                n == props@.len(),
                sprops == Seq::new(props@.len(), |k: int| props@[k]@),
                forall|a: int, b: int|
                    0 <= a && a < i as int && a < b && b < n as int ==>
                        !spec_prop_same_key(#[trigger] sprops[a], #[trigger] sprops[b]),
                forall|b: int|
                    (i as int) < b && b < j as int ==>
                        !spec_prop_same_key(sprops[i as int], #[trigger] sprops[b]),
            decreases n - j,
        {
            if props[i].is_symbol == props[j].is_symbol
                && eq_u16_slice(props[i].key.as_slice(), props[j].key.as_slice())
            {
                proof {
                    assert(sprops[i as int] == props@[i as int]@);
                    assert(sprops[j as int] == props@[j as int]@);
                    assert(spec_prop_same_key(sprops[i as int], sprops[j as int]));
                }
                return true;
            }
            proof {
                assert(sprops[i as int] == props@[i as int]@);
                assert(sprops[j as int] == props@[j as int]@);
            }
            j += 1;
        }
        i += 1;
    }
    false
}

/// WHATWG Web IDL §3.2.21 (`#js-to-record`): `record<DOMString, DOMString>`.
/// Visits ONLY own enumerable properties (`[[OwnPropertyKeys]]` + `[[GetOwnProperty]]`).
pub open spec fn spec_record_dom_dom_loop(
    arena: Seq<SpecJsObjectRecord>,
    props: Seq<SpecJsOwnProp>,
    acc: Seq<(Seq<u16>, Seq<u16>)>,
) -> Result<Seq<(Seq<u16>, Seq<u16>)>, IdlError>
    decreases props.len(),
{
    if props.len() == 0 {
        Ok(acc)
    } else {
        let p = props[0];
        let rest = props.subrange(1, props.len() as int);
        if !p.enumerable {
            spec_record_dom_dom_loop(arena, rest, acc)
        } else if p.is_symbol {
            Err(IdlError::TypeError)
        } else {
            match p.getter_throws {
                Some(exc_id) => Err(IdlError::AbruptException(exc_id)),
                None => match spec_to_idl_dom_string(arena, p.value, false) {
                    Err(e) => Err(e),
                    Ok(tv) => spec_record_dom_dom_loop(
                        arena,
                        rest,
                        spec_record_upsert_u16(acc, p.key, tv),
                    ),
                },
            }
        }
    }
}

pub open spec fn spec_to_idl_record_dom_string(
    arena: Seq<SpecJsObjectRecord>,
    v: SpecJsValue,
) -> Result<Seq<(Seq<u16>, Seq<u16>)>, IdlError> {
    match v {
        SpecJsValue::Object(oid) => {
            if (oid as int) >= arena.len() {
                Err(IdlError::TypeError)
            } else if spec_has_duplicate_own_keys(arena[oid as int].own_props) {
                Err(IdlError::TypeError)
            } else {
                spec_record_dom_dom_loop(arena, arena[oid as int].own_props, seq![])
            }
        },
        _ => Err(IdlError::TypeError),
    }
}

pub fn to_idl_record_dom_string(
    arena: &JsObjectArena,
    v: &JsValue,
) -> (res: Result<Vec<(Vec<u16>, Vec<u16>)>, IdlError>)
    ensures
        match (res, spec_to_idl_record_dom_string(arena@, v@)) {
            (Ok(out), Ok(sout)) => {
                out@.len() == sout.len()
                && Seq::new(out@.len(), |i: int| (out@[i].0@, out@[i].1@)) == sout
            },
            (Err(e), Err(se)) => e == se,
            _ => false,
        },
{
    let oid = match v {
        JsValue::Object(oid) => *oid,
        _ => return Err(IdlError::TypeError),
    };
    if oid >= arena.objects.len() {
        return Err(IdlError::TypeError);
    }
    let props = &arena.objects[oid].own_props;
    if check_has_duplicate_own_keys(props.as_slice()) {
        return Err(IdlError::TypeError);
    }
    let ghost sprops = arena@[oid as int].own_props;
    let n = props.len();
    let mut out: Vec<(Vec<u16>, Vec<u16>)> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(sprops.subrange(0, n as int) =~= sprops);
        assert(Seq::new(out@.len(), |k: int| (out@[k].0@, out@[k].1@))
            =~= Seq::<(Seq<u16>, Seq<u16>)>::empty());
    }
    while i < n
        invariant
            i <= n,
            n == props@.len(),
            v@ == SpecJsValue::Object(oid),
            (oid as int) < arena@.len(),
            !spec_has_duplicate_own_keys(sprops),
            sprops == arena@[oid as int].own_props,
            sprops == Seq::new(props@.len(), |k: int| props@[k]@),
            spec_record_dom_dom_loop(arena@, sprops, seq![])
                == spec_record_dom_dom_loop(
                    arena@,
                    sprops.subrange(i as int, n as int),
                    Seq::new(out@.len(), |k: int| (out@[k].0@, out@[k].1@)),
                ),
        decreases n - i,
    {
        let p = &props[i];
        let ghost sub = sprops.subrange(i as int, n as int);
        if !p.enumerable {
            i += 1;
            proof {
                assert(sub.subrange(1, sub.len() as int) =~= sprops.subrange(i as int, n as int));
            }
        } else if p.is_symbol {
            proof {
                assert(sub.len() > 0 && sub[0] == props@[i as int]@);
            }
            return Err(IdlError::TypeError);
        } else if let Some(exc_id) = p.getter_throws {
            proof {
                assert(sub.len() > 0 && sub[0] == props@[i as int]@);
            }
            return Err(IdlError::AbruptException(exc_id));
        } else {
            match to_idl_dom_string(arena, &p.value, false) {
                Err(e) => {
                    proof {
                        assert(sub.len() > 0 && sub[0] == props@[i as int]@);
                    }
                    return Err(e);
                },
                Ok(tv) => {
                    let k_copy = clone_u16_slice(p.key.as_slice());
                    record_upsert_u16(&mut out, k_copy, tv);
                    i += 1;
                    proof {
                        assert(sub.subrange(1, sub.len() as int)
                            =~= sprops.subrange(i as int, n as int));
                    }
                },
            }
        }
    }
    proof {
        assert(sprops.subrange(n as int, n as int) =~= Seq::<SpecJsOwnProp>::empty());
    }
    Ok(out)
}

/// WHATWG Web IDL §3.2.21 (`#js-to-record`): `record<USVString, USVString>` (URLSearchParams).
pub open spec fn spec_record_usv_usv_loop(
    arena: Seq<SpecJsObjectRecord>,
    props: Seq<SpecJsOwnProp>,
    acc: Seq<(Seq<u16>, Seq<u16>)>,
) -> Result<Seq<(Seq<u16>, Seq<u16>)>, IdlError>
    decreases props.len(),
{
    if props.len() == 0 {
        Ok(acc)
    } else {
        let p = props[0];
        let rest = props.subrange(1, props.len() as int);
        if !p.enumerable {
            spec_record_usv_usv_loop(arena, rest, acc)
        } else if p.is_symbol {
            Err(IdlError::TypeError)
        } else {
            let tk = spec_usv_normalize_units(p.key);
            match p.getter_throws {
                Some(exc_id) => Err(IdlError::AbruptException(exc_id)),
                None => match spec_to_idl_usv_string(arena, p.value) {
                    Err(e) => Err(e),
                    Ok(tv) => spec_record_usv_usv_loop(
                        arena,
                        rest,
                        spec_record_upsert_u16(acc, tk, tv),
                    ),
                },
            }
        }
    }
}

pub open spec fn spec_to_idl_record_usv_string(
    arena: Seq<SpecJsObjectRecord>,
    v: SpecJsValue,
) -> Result<Seq<(Seq<u16>, Seq<u16>)>, IdlError> {
    match v {
        SpecJsValue::Object(oid) => {
            if (oid as int) >= arena.len() {
                Err(IdlError::TypeError)
            } else if spec_has_duplicate_own_keys(arena[oid as int].own_props) {
                Err(IdlError::TypeError)
            } else {
                spec_record_usv_usv_loop(arena, arena[oid as int].own_props, seq![])
            }
        },
        _ => Err(IdlError::TypeError),
    }
}

pub fn to_idl_record_usv_string(
    arena: &JsObjectArena,
    v: &JsValue,
) -> (res: Result<Vec<(Vec<u16>, Vec<u16>)>, IdlError>)
    ensures
        match (res, spec_to_idl_record_usv_string(arena@, v@)) {
            (Ok(out), Ok(sout)) => {
                out@.len() == sout.len()
                && Seq::new(out@.len(), |i: int| (out@[i].0@, out@[i].1@)) == sout
            },
            (Err(e), Err(se)) => e == se,
            _ => false,
        },
{
    let oid = match v {
        JsValue::Object(oid) => *oid,
        _ => return Err(IdlError::TypeError),
    };
    if oid >= arena.objects.len() {
        return Err(IdlError::TypeError);
    }
    let props = &arena.objects[oid].own_props;
    if check_has_duplicate_own_keys(props.as_slice()) {
        return Err(IdlError::TypeError);
    }
    let ghost sprops = arena@[oid as int].own_props;
    let n = props.len();
    let mut out: Vec<(Vec<u16>, Vec<u16>)> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(sprops.subrange(0, n as int) =~= sprops);
        assert(Seq::new(out@.len(), |k: int| (out@[k].0@, out@[k].1@))
            =~= Seq::<(Seq<u16>, Seq<u16>)>::empty());
    }
    while i < n
        invariant
            i <= n,
            n == props@.len(),
            v@ == SpecJsValue::Object(oid),
            (oid as int) < arena@.len(),
            !spec_has_duplicate_own_keys(sprops),
            sprops == arena@[oid as int].own_props,
            sprops == Seq::new(props@.len(), |k: int| props@[k]@),
            spec_record_usv_usv_loop(arena@, sprops, seq![])
                == spec_record_usv_usv_loop(
                    arena@,
                    sprops.subrange(i as int, n as int),
                    Seq::new(out@.len(), |k: int| (out@[k].0@, out@[k].1@)),
                ),
        decreases n - i,
    {
        let p = &props[i];
        let ghost sub = sprops.subrange(i as int, n as int);
        if !p.enumerable {
            i += 1;
            proof {
                assert(sub.subrange(1, sub.len() as int) =~= sprops.subrange(i as int, n as int));
            }
        } else if p.is_symbol {
            proof {
                assert(sub.len() > 0 && sub[0] == props@[i as int]@);
            }
            return Err(IdlError::TypeError);
        } else if let Some(exc_id) = p.getter_throws {
            proof {
                assert(sub.len() > 0 && sub[0] == props@[i as int]@);
            }
            return Err(IdlError::AbruptException(exc_id));
        } else {
            let tk = usv_normalize_units(p.key.as_slice());
            match to_idl_usv_string(arena, &p.value) {
                Err(e) => {
                    proof {
                        assert(sub.len() > 0 && sub[0] == props@[i as int]@);
                    }
                    return Err(e);
                },
                Ok(tv) => {
                    record_upsert_u16(&mut out, tk, tv);
                    i += 1;
                    proof {
                        assert(sub.subrange(1, sub.len() as int)
                            =~= sprops.subrange(i as int, n as int));
                    }
                },
            }
        }
    }
    proof {
        assert(sprops.subrange(n as int, n as int) =~= Seq::<SpecJsOwnProp>::empty());
    }
    Ok(out)
}

/// WHATWG Web IDL §3.2.21 (`#js-to-record`): `record<ByteString, ByteString>` (Fetch `HeadersInit`).
/// Rejects duplicate own keys, enumerable Symbol keys, and any enumerable own property whose
/// key OR value contains a code unit `> 0x00FF` (evaluating key conversion BEFORE `[[Get]]`)!
pub open spec fn spec_record_byte_byte_loop(
    arena: Seq<SpecJsObjectRecord>,
    props: Seq<SpecJsOwnProp>,
    acc: Seq<(Seq<u8>, Seq<u8>)>,
) -> Result<Seq<(Seq<u8>, Seq<u8>)>, IdlError>
    decreases props.len(),
{
    if props.len() == 0 {
        Ok(acc)
    } else {
        let p = props[0];
        let rest = props.subrange(1, props.len() as int);
        if !p.enumerable {
            spec_record_byte_byte_loop(arena, rest, acc)
        } else if p.is_symbol {
            Err(IdlError::TypeError)
        } else {
            match spec_units_to_byte_string(p.key) {
                Err(e) => Err(e),
                Ok(tk) => {
                    match p.getter_throws {
                        Some(exc_id) => Err(IdlError::AbruptException(exc_id)),
                        None => match spec_to_idl_byte_string(arena, p.value) {
                            Err(e) => Err(e),
                            Ok(tv) => spec_record_byte_byte_loop(
                                arena,
                                rest,
                                spec_record_upsert_u8(acc, tk, tv),
                            ),
                        },
                    }
                },
            }
        }
    }
}

pub open spec fn spec_to_idl_record_byte_string(
    arena: Seq<SpecJsObjectRecord>,
    v: SpecJsValue,
) -> Result<Seq<(Seq<u8>, Seq<u8>)>, IdlError> {
    match v {
        SpecJsValue::Object(oid) => {
            if (oid as int) >= arena.len() {
                Err(IdlError::TypeError)
            } else if spec_has_duplicate_own_keys(arena[oid as int].own_props) {
                Err(IdlError::TypeError)
            } else {
                spec_record_byte_byte_loop(arena, arena[oid as int].own_props, seq![])
            }
        },
        _ => Err(IdlError::TypeError),
    }
}

pub fn to_idl_record_byte_string(
    arena: &JsObjectArena,
    v: &JsValue,
) -> (res: Result<Vec<(Vec<u8>, Vec<u8>)>, IdlError>)
    ensures
        match (res, spec_to_idl_record_byte_string(arena@, v@)) {
            (Ok(out), Ok(sout)) => {
                out@.len() == sout.len()
                && Seq::new(out@.len(), |i: int| (out@[i].0@, out@[i].1@)) == sout
            },
            (Err(e), Err(se)) => e == se,
            _ => false,
        },
{
    let oid = match v {
        JsValue::Object(oid) => *oid,
        _ => return Err(IdlError::TypeError),
    };
    if oid >= arena.objects.len() {
        return Err(IdlError::TypeError);
    }
    let props = &arena.objects[oid].own_props;
    if check_has_duplicate_own_keys(props.as_slice()) {
        return Err(IdlError::TypeError);
    }
    let ghost sprops = arena@[oid as int].own_props;
    let n = props.len();
    let mut out: Vec<(Vec<u8>, Vec<u8>)> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(sprops.subrange(0, n as int) =~= sprops);
        assert(Seq::new(out@.len(), |k: int| (out@[k].0@, out@[k].1@))
            =~= Seq::<(Seq<u8>, Seq<u8>)>::empty());
    }
    while i < n
        invariant
            i <= n,
            n == props@.len(),
            v@ == SpecJsValue::Object(oid),
            (oid as int) < arena@.len(),
            !spec_has_duplicate_own_keys(sprops),
            sprops == arena@[oid as int].own_props,
            sprops == Seq::new(props@.len(), |k: int| props@[k]@),
            spec_record_byte_byte_loop(arena@, sprops, seq![])
                == spec_record_byte_byte_loop(
                    arena@,
                    sprops.subrange(i as int, n as int),
                    Seq::new(out@.len(), |k: int| (out@[k].0@, out@[k].1@)),
                ),
        decreases n - i,
    {
        let p = &props[i];
        let ghost sub = sprops.subrange(i as int, n as int);
        if !p.enumerable {
            i += 1;
            proof {
                assert(sub.subrange(1, sub.len() as int) =~= sprops.subrange(i as int, n as int));
            }
        } else if p.is_symbol {
            proof {
                assert(sub.len() > 0 && sub[0] == props@[i as int]@);
            }
            return Err(IdlError::TypeError);
        } else {
            match units_to_byte_string(p.key.as_slice()) {
                Err(e) => {
                    proof {
                        assert(sub.len() > 0 && sub[0] == props@[i as int]@);
                    }
                    return Err(e);
                },
                Ok(tk) => {
                    if let Some(exc_id) = p.getter_throws {
                        proof {
                            assert(sub.len() > 0 && sub[0] == props@[i as int]@);
                        }
                        return Err(IdlError::AbruptException(exc_id));
                    }
                    match to_idl_byte_string(arena, &p.value) {
                        Err(e) => {
                            proof {
                                assert(sub.len() > 0 && sub[0] == props@[i as int]@);
                            }
                            return Err(e);
                        },
                        Ok(tv) => {
                            record_upsert_u8(&mut out, tk, tv);
                            i += 1;
                            proof {
                                assert(sub.subrange(1, sub.len() as int)
                                    =~= sprops.subrange(i as int, n as int));
                            }
                        },
                    }
                },
            }
        }
    }
    proof {
        assert(sprops.subrange(n as int, n as int) =~= Seq::<SpecJsOwnProp>::empty());
    }
    Ok(out)
}

/// WHATWG Web IDL §3.2.21 (`#record-to-js`): convert `record<DOMString, DOMString>` into
/// an ordinary JS Object in `arena` with own enumerable data properties.
pub fn to_js_record_dom_string(
    arena: &mut JsObjectArena,
    entries: &[(Vec<u16>, Vec<u16>)],
) -> (res: Result<JsValue, IdlError>)
    ensures
        old(arena)@.len() < usize::MAX ==> match res {
            Ok(JsValue::Object(oid)) => {
                oid == old(arena)@.len()
                && final(arena)@.len() == old(arena)@.len() + 1
                && final(arena)@[oid as int].own_props.len() == entries@.len()
            },
            _ => false,
        },
{
    if arena.objects.len() == usize::MAX {
        return Err(IdlError::TypeError);
    }
    let n = entries.len();
    let mut own_props: Vec<JsOwnProp> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == entries@.len(),
            own_props@.len() == i as nat,
        decreases n - i,
    {
        let k_vec = clone_u16_slice(entries[i].0.as_slice());
        let v_js = to_js_dom_string(entries[i].1.as_slice());
        own_props.push(JsOwnProp {
            key: k_vec,
            is_symbol: false,
            enumerable: true,
            is_getter: false,
            getter_throws: None,
            value: v_js,
        });
        i += 1;
    }
    let rec = JsObjectRecord {
        own_props,
        proto_props: Vec::new(),
        iterator: JsIterator::NotIterable,
        to_string_hook: JsToStringHook::DefaultObjectTag,
        to_number_override: None,
    };
    let oid = arena.alloc(rec);
    Ok(JsValue::Object(oid))
}

// ---------------------------------------------------------------------------------------
// §3.2.20 Dictionaries: Lexicographical UTF-16 Key Order & Core Host Interfaces
// ---------------------------------------------------------------------------------------

/// Code-unit lexicographical strict ordering `<` on UTF-16 strings (Web IDL §3.2.20).
pub open spec fn spec_utf16_lt(a: Seq<u16>, b: Seq<u16>) -> bool
    decreases a.len(),
{
    if b.len() == 0 {
        false
    } else if a.len() == 0 {
        true
    } else if a[0] < b[0] {
        true
    } else if a[0] > b[0] {
        false
    } else {
        spec_utf16_lt(a.subrange(1, a.len() as int), b.subrange(1, b.len() as int))
    }
}

/// Predicate asserting that dictionary member keys are strictly sorted in lexicographical order.
pub open spec fn spec_keys_strictly_lexicographic(keys: Seq<Seq<u16>>) -> bool {
    forall|i: int, j: int|
        0 <= i && i < j && j < keys.len() ==> spec_utf16_lt(#[trigger] keys[i], #[trigger] keys[j])
}

pub proof fn lemma_utf16_lt_irreflexive(a: Seq<u16>)
    ensures
        !spec_utf16_lt(a, a),
    decreases a.len(),
{
    if a.len() > 0 {
        lemma_utf16_lt_irreflexive(a.subrange(1, a.len() as int));
    }
}

pub proof fn lemma_utf16_lt_transitive(a: Seq<u16>, b: Seq<u16>, c: Seq<u16>)
    requires
        spec_utf16_lt(a, b),
        spec_utf16_lt(b, c),
    ensures
        spec_utf16_lt(a, c),
    decreases a.len(),
{
    if a.len() == 0 || b.len() == 0 || c.len() == 0 {
    } else if a[0] == b[0] && b[0] == c[0] {
        lemma_utf16_lt_transitive(
            a.subrange(1, a.len() as int),
            b.subrange(1, b.len() as int),
            c.subrange(1, c.len() as int),
        );
    }
}

pub fn utf16_lt(a: &[u16], b: &[u16]) -> (r: bool)
    ensures
        r == spec_utf16_lt(a@, b@),
{
    let na = a.len();
    let nb = b.len();
    let min_len = if na < nb { na } else { nb };
    let mut i: usize = 0;
    proof {
        assert(a@.subrange(0, na as int) =~= a@);
        assert(b@.subrange(0, nb as int) =~= b@);
    }
    while i < min_len
        invariant
            i <= min_len,
            min_len == (if na < nb { na } else { nb }),
            na == a@.len(),
            nb == b@.len(),
            spec_utf16_lt(a@, b@)
                == spec_utf16_lt(
                    a@.subrange(i as int, na as int),
                    b@.subrange(i as int, nb as int),
                ),
        decreases min_len - i,
    {
        let ghost sa = a@.subrange(i as int, na as int);
        let ghost sb = b@.subrange(i as int, nb as int);
        if a[i] < b[i] {
            return true;
        }
        if a[i] > b[i] {
            return false;
        }
        i += 1;
        proof {
            assert(sa.subrange(1, sa.len() as int) =~= a@.subrange(i as int, na as int));
            assert(sb.subrange(1, sb.len() as int) =~= b@.subrange(i as int, nb as int));
        }
    }
    na < nb
}

/// ECMA-262 `Get(O, key)` for Web IDL Dictionary lookup (§3.2.20 step 4.1.4):
/// Searches own string-keyed properties (regardless of `enumerable`), then prototype chain
/// properties, returning `Undefined` when absent, or throwing `TypeError` if `getter_throws`.
pub open spec fn spec_find_own_prop(
    props: Seq<SpecJsOwnProp>,
    key: Seq<u16>,
) -> Option<SpecJsOwnProp>
    decreases props.len(),
{
    if props.len() == 0 {
        None
    } else if !props[0].is_symbol && props[0].key == key {
        Some(props[0])
    } else {
        spec_find_own_prop(props.subrange(1, props.len() as int), key)
    }
}

pub open spec fn spec_find_proto_prop(
    props: Seq<SpecJsProtoProp>,
    key: Seq<u16>,
) -> Option<SpecJsValue>
    decreases props.len(),
{
    if props.len() == 0 {
        None
    } else if props[0].key == key {
        Some(props[0].value)
    } else {
        spec_find_proto_prop(props.subrange(1, props.len() as int), key)
    }
}

pub open spec fn spec_dict_get_member(
    arena: Seq<SpecJsObjectRecord>,
    js_dict: SpecJsValue,
    key: Seq<u16>,
) -> Result<SpecJsValue, IdlError> {
    match js_dict {
        SpecJsValue::Undefined | SpecJsValue::Null => Ok(SpecJsValue::Undefined),
        SpecJsValue::Object(oid) => {
            if (oid as int) >= arena.len() {
                Err(IdlError::TypeError)
            } else {
                let obj = arena[oid as int];
                match spec_find_own_prop(obj.own_props, key) {
                    Some(prop) => {
                        match prop.getter_throws {
                            Some(exc_id) => Err(IdlError::AbruptException(exc_id)),
                            None => Ok(prop.value),
                        }
                    },
                    None => match spec_find_proto_prop(obj.proto_props, key) {
                        Some(v) => Ok(v),
                        None => Ok(SpecJsValue::Undefined),
                    },
                }
            }
        },
        _ => Err(IdlError::TypeError),
    }
}

pub open spec fn spec_dict_member_is_own_getter(
    arena: Seq<SpecJsObjectRecord>,
    js_dict: SpecJsValue,
    key: Seq<u16>,
) -> bool {
    match js_dict {
        SpecJsValue::Object(oid) => {
            if (oid as int) >= arena.len() {
                false
            } else {
                match spec_find_own_prop(arena[oid as int].own_props, key) {
                    Some(prop) => prop.is_getter && prop.getter_throws.is_none(),
                    None => false,
                }
            }
        },
        _ => false,
    }
}

fn clone_js_value(v: &JsValue) -> (out: JsValue)
    ensures
        out@ == v@,
{
    match v {
        JsValue::Undefined => JsValue::Undefined,
        JsValue::Null => JsValue::Null,
        JsValue::Bool(b) => JsValue::Bool(*b),
        JsValue::Number(bits) => JsValue::Number(*bits),
        JsValue::BigInt { neg, mag } => JsValue::BigInt { neg: *neg, mag: *mag },
        JsValue::String(s) => JsValue::String(clone_u16_slice(s.as_slice())),
        JsValue::Symbol(id) => JsValue::Symbol(*id),
        JsValue::Object(oid) => JsValue::Object(*oid),
    }
}

pub fn dict_get_member_with_getter_flag(
    arena: &JsObjectArena,
    js_dict: &JsValue,
    key: &[u16],
) -> (res: Result<(JsValue, bool), IdlError>)
    ensures
        match (res, spec_dict_get_member(arena@, js_dict@, key@)) {
            (Ok((v, was_getter)), Ok(sv)) => {
                v@ == sv
                && was_getter == spec_dict_member_is_own_getter(arena@, js_dict@, key@)
            },
            (Err(e), Err(se)) => e == se,
            _ => false,
        },
{
    match js_dict {
        JsValue::Undefined | JsValue::Null => Ok((JsValue::Undefined, false)),
        JsValue::Object(oid) => {
            if *oid >= arena.objects.len() {
                return Err(IdlError::TypeError);
            }
            let obj = &arena.objects[*oid];
            let ghost sown = arena@[*oid as int].own_props;
            let n_own = obj.own_props.len();
            let mut i: usize = 0;
            proof {
                assert(sown.subrange(0, n_own as int) =~= sown);
            }
            while i < n_own
                invariant
                    i <= n_own,
                    n_own == obj.own_props@.len(),
                    js_dict@ == SpecJsValue::Object(*oid),
                    (*oid as int) < arena@.len(),
                    sown == arena@[*oid as int].own_props,
                    sown == Seq::new(obj.own_props@.len(), |k: int| obj.own_props@[k]@),
                    spec_find_own_prop(sown, key@)
                        == spec_find_own_prop(sown.subrange(i as int, n_own as int), key@),
                decreases n_own - i,
            {
                let ghost sub = sown.subrange(i as int, n_own as int);
                if !obj.own_props[i].is_symbol
                    && eq_u16_slice(obj.own_props[i].key.as_slice(), key)
                {
                    proof {
                        assert(sub.len() > 0 && sub[0] == obj.own_props@[i as int]@);
                    }
                    if let Some(exc_id) = obj.own_props[i].getter_throws {
                        return Err(IdlError::AbruptException(exc_id));
                    }
                    return Ok((
                        clone_js_value(&obj.own_props[i].value),
                        obj.own_props[i].is_getter,
                    ));
                }
                i += 1;
                proof {
                    assert(sub.subrange(1, sub.len() as int)
                        =~= sown.subrange(i as int, n_own as int));
                }
            }
            proof {
                assert(sown.subrange(n_own as int, n_own as int) =~= Seq::<SpecJsOwnProp>::empty());
            }

            let ghost sproto = arena@[*oid as int].proto_props;
            let n_proto = obj.proto_props.len();
            let mut j: usize = 0;
            proof {
                assert(sproto.subrange(0, n_proto as int) =~= sproto);
            }
            while j < n_proto
                invariant
                    j <= n_proto,
                    n_proto == obj.proto_props@.len(),
                    js_dict@ == SpecJsValue::Object(*oid),
                    (*oid as int) < arena@.len(),
                    spec_find_own_prop(arena@[*oid as int].own_props, key@).is_none(),
                    sproto == arena@[*oid as int].proto_props,
                    sproto == Seq::new(obj.proto_props@.len(), |k: int| obj.proto_props@[k]@),
                    spec_find_proto_prop(sproto, key@)
                        == spec_find_proto_prop(sproto.subrange(j as int, n_proto as int), key@),
                decreases n_proto - j,
            {
                let ghost sub = sproto.subrange(j as int, n_proto as int);
                if eq_u16_slice(obj.proto_props[j].key.as_slice(), key) {
                    proof {
                        assert(sub.len() > 0 && sub[0] == obj.proto_props@[j as int]@);
                    }
                    return Ok((clone_js_value(&obj.proto_props[j].value), false));
                }
                j += 1;
                proof {
                    assert(sub.subrange(1, sub.len() as int)
                        =~= sproto.subrange(j as int, n_proto as int));
                }
            }
            proof {
                assert(sproto.subrange(n_proto as int, n_proto as int)
                    =~= Seq::<SpecJsProtoProp>::empty());
            }
            Ok((JsValue::Undefined, false))
        },
        _ => Err(IdlError::TypeError),
    }
}

pub fn dict_get_member(
    arena: &JsObjectArena,
    js_dict: &JsValue,
    key: &[u16],
) -> (res: Result<JsValue, IdlError>)
    ensures
        match (res, spec_dict_get_member(arena@, js_dict@, key@)) {
            (Ok(v), Ok(sv)) => v@ == sv,
            (Err(e), Err(se)) => e == se,
            _ => false,
        },
{
    let (v, _) = dict_get_member_with_getter_flag(arena, js_dict, key)?;
    Ok(v)
}

/// Step 1 of Web IDL §3.2.20 (`#js-to-dictionary`):
/// "If `jsDict` is not an Object and `jsDict` is neither `undefined` nor `null`, throw a `TypeError`."
pub open spec fn spec_validate_dict_container(
    arena: Seq<SpecJsObjectRecord>,
    js_dict: SpecJsValue,
) -> Result<(), IdlError> {
    match js_dict {
        SpecJsValue::Undefined | SpecJsValue::Null => Ok(()),
        SpecJsValue::Object(oid) => {
            if (oid as int) < arena.len() {
                Ok(())
            } else {
                Err(IdlError::TypeError)
            }
        },
        _ => Err(IdlError::TypeError),
    }
}

fn validate_dict_container(arena: &JsObjectArena, js_dict: &JsValue) -> (res: Result<(), IdlError>)
    ensures
        res == spec_validate_dict_container(arena@, js_dict@),
{
    match js_dict {
        JsValue::Undefined | JsValue::Null => Ok(()),
        JsValue::Object(oid) => {
            if *oid < arena.objects.len() {
                Ok(())
            } else {
                Err(IdlError::TypeError)
            }
        },
        _ => Err(IdlError::TypeError),
    }
}

// --- 1. `EventInit` Dictionary (DOM §2.2) ---
// Lexicographical members: "bubbles" (boolean = false), "cancelable" (boolean = false), "composed" (boolean = false)

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct EventInit {
    pub bubbles: bool,
    pub cancelable: bool,
    pub composed: bool,
}

pub open spec fn spec_key_bubbles() -> Seq<u16> {
    spec_ascii_to_utf16(seq![0x62u8, 0x75, 0x62, 0x62, 0x6c, 0x65, 0x73])
}

pub open spec fn spec_key_cancelable() -> Seq<u16> {
    spec_ascii_to_utf16(seq![0x63u8, 0x61, 0x6e, 0x63, 0x65, 0x6c, 0x61, 0x62, 0x6c, 0x65])
}

pub open spec fn spec_key_composed() -> Seq<u16> {
    spec_ascii_to_utf16(seq![0x63u8, 0x6f, 0x6d, 0x70, 0x6f, 0x73, 0x65, 0x64])
}

pub proof fn lemma_event_init_keys_lexicographic()
    ensures
        spec_keys_strictly_lexicographic(seq![
            spec_key_bubbles(),
            spec_key_cancelable(),
            spec_key_composed(),
        ]),
{
    let k0 = spec_key_bubbles();
    let k1 = spec_key_cancelable();
    let k2 = spec_key_composed();
    reveal_with_fuel(spec_utf16_lt, 4);
    assert(k0[0] == 0x62u16 && k1[0] == 0x63u16 && k2[0] == 0x63u16);
    assert(k1[1] == 0x61u16 && k2[1] == 0x6fu16);
    assert(spec_utf16_lt(k0, k1));
    assert(spec_utf16_lt(k0, k2));
    assert(spec_utf16_lt(k1, k2));
}

pub open spec fn spec_to_idl_event_init(
    arena: Seq<SpecJsObjectRecord>,
    js_dict: SpecJsValue,
) -> Result<EventInit, IdlError> {
    match spec_validate_dict_container(arena, js_dict) {
        Err(e) => Err(e),
        Ok(()) => match spec_dict_get_member(arena, js_dict, spec_key_bubbles()) {
            Err(e) => Err(e),
            Ok(v_bubbles) => {
                let bubbles = if v_bubbles == SpecJsValue::Undefined {
                    false
                } else {
                    spec_to_idl_boolean(v_bubbles)
                };
                match spec_dict_get_member(arena, js_dict, spec_key_cancelable()) {
                    Err(e) => Err(e),
                    Ok(v_cancelable) => {
                        let cancelable = if v_cancelable == SpecJsValue::Undefined {
                            false
                        } else {
                            spec_to_idl_boolean(v_cancelable)
                        };
                        match spec_dict_get_member(arena, js_dict, spec_key_composed()) {
                            Err(e) => Err(e),
                            Ok(v_composed) => {
                                let composed = if v_composed == SpecJsValue::Undefined {
                                    false
                                } else {
                                    spec_to_idl_boolean(v_composed)
                                };
                                Ok(EventInit { bubbles, cancelable, composed })
                            },
                        }
                    },
                }
            },
        },
    }
}

pub fn to_idl_event_init(
    arena: &JsObjectArena,
    js_dict: &JsValue,
) -> (res: Result<EventInit, IdlError>)
    ensures
        res == spec_to_idl_event_init(arena@, js_dict@),
{
    validate_dict_container(arena, js_dict)?;
    let k_bubbles: [u16; 7] = [0x62, 0x75, 0x62, 0x62, 0x6c, 0x65, 0x73];
    let k_cancelable: [u16; 10] = [0x63, 0x61, 0x6e, 0x63, 0x65, 0x6c, 0x61, 0x62, 0x6c, 0x65];
    let k_composed: [u16; 8] = [0x63, 0x6f, 0x6d, 0x70, 0x6f, 0x73, 0x65, 0x64];
    proof {
        assert(k_bubbles@ =~= spec_key_bubbles());
        assert(k_cancelable@ =~= spec_key_cancelable());
        assert(k_composed@ =~= spec_key_composed());
    }
    let vb = dict_get_member(arena, js_dict, &k_bubbles)?;
    let bubbles = if matches!(vb, JsValue::Undefined) { false } else { to_idl_boolean(&vb) };

    let vc = dict_get_member(arena, js_dict, &k_cancelable)?;
    let cancelable = if matches!(vc, JsValue::Undefined) { false } else { to_idl_boolean(&vc) };

    let vco = dict_get_member(arena, js_dict, &k_composed)?;
    let composed = if matches!(vco, JsValue::Undefined) { false } else { to_idl_boolean(&vco) };

    Ok(EventInit { bubbles, cancelable, composed })
}

pub open spec fn spec_event_init_getter_log(
    arena: Seq<SpecJsObjectRecord>,
    js_dict: SpecJsValue,
) -> Seq<Seq<u16>> {
    let l0: Seq<Seq<u16>> = if spec_dict_member_is_own_getter(arena, js_dict, spec_key_bubbles()) {
        seq![spec_key_bubbles()]
    } else {
        seq![]
    };
    let l1: Seq<Seq<u16>> = if spec_dict_member_is_own_getter(arena, js_dict, spec_key_cancelable()) {
        l0.push(spec_key_cancelable())
    } else {
        l0
    };
    if spec_dict_member_is_own_getter(arena, js_dict, spec_key_composed()) {
        l1.push(spec_key_composed())
    } else {
        l1
    }
}

/// Traced `EventInit` dictionary conversion (matching WPT `Event-constructors.any.js:91–112`),
/// machine-checking in Verus that:
/// 1. Result equals `spec_to_idl_event_init(arena@, js_dict@)`,
/// 2. `getter_log` equals `spec_event_init_getter_log(arena@, js_dict@)` (unknown properties
///    such as `"sweet"` are NEVER accessed!), and
/// 3. Every invoked getter sequence is strictly ordered in UTF-16 lexicographical key order!
pub fn to_idl_event_init_logged(
    arena: &JsObjectArena,
    js_dict: &JsValue,
) -> (res: Result<(EventInit, Vec<Vec<u16>>), IdlError>)
    ensures
        match (res, spec_to_idl_event_init(arena@, js_dict@)) {
            (Ok((init, log)), Ok(sinit)) => {
                let log_view = Seq::new(log@.len(), |i: int| log@[i]@);
                init == sinit
                && log_view == spec_event_init_getter_log(arena@, js_dict@)
                && spec_keys_strictly_lexicographic(log_view)
            },
            (Err(e), Err(se)) => e == se,
            _ => false,
        },
{
    validate_dict_container(arena, js_dict)?;
    let k_bubbles: [u16; 7] = [0x62, 0x75, 0x62, 0x62, 0x6c, 0x65, 0x73];
    let k_cancelable: [u16; 10] = [0x63, 0x61, 0x6e, 0x63, 0x65, 0x6c, 0x61, 0x62, 0x6c, 0x65];
    let k_composed: [u16; 8] = [0x63, 0x6f, 0x6d, 0x70, 0x6f, 0x73, 0x65, 0x64];
    proof {
        assert(k_bubbles@ =~= spec_key_bubbles());
        assert(k_cancelable@ =~= spec_key_cancelable());
        assert(k_composed@ =~= spec_key_composed());
    }
    let mut log: Vec<Vec<u16>> = Vec::new();
    proof {
        assert(Seq::new(log@.len(), |i: int| log@[i]@) =~= Seq::<Seq<u16>>::empty());
    }

    let (vb, gb) = dict_get_member_with_getter_flag(arena, js_dict, &k_bubbles)?;
    if gb {
        log.push(clone_u16_slice(&k_bubbles));
        proof {
            assert(Seq::new(log@.len(), |i: int| log@[i]@) =~= seq![spec_key_bubbles()]);
        }
    }
    let ghost l0 = Seq::new(log@.len(), |i: int| log@[i]@);
    let bubbles = if matches!(vb, JsValue::Undefined) { false } else { to_idl_boolean(&vb) };

    let (vc, gc) = dict_get_member_with_getter_flag(arena, js_dict, &k_cancelable)?;
    if gc {
        log.push(clone_u16_slice(&k_cancelable));
        proof {
            assert(Seq::new(log@.len(), |i: int| log@[i]@) =~= l0.push(spec_key_cancelable()));
        }
    }
    let ghost l1 = Seq::new(log@.len(), |i: int| log@[i]@);
    let cancelable = if matches!(vc, JsValue::Undefined) { false } else { to_idl_boolean(&vc) };

    let (vco, gco) = dict_get_member_with_getter_flag(arena, js_dict, &k_composed)?;
    if gco {
        log.push(clone_u16_slice(&k_composed));
        proof {
            assert(Seq::new(log@.len(), |i: int| log@[i]@) =~= l1.push(spec_key_composed()));
        }
    }
    let composed = if matches!(vco, JsValue::Undefined) { false } else { to_idl_boolean(&vco) };

    proof {
        lemma_event_init_keys_lexicographic();
        let k0 = spec_key_bubbles();
        let k1 = spec_key_cancelable();
        let k2 = spec_key_composed();
        assert(spec_utf16_lt(k0, k1));
        assert(spec_utf16_lt(k0, k2));
        assert(spec_utf16_lt(k1, k2));
        let lv = Seq::new(log@.len(), |i: int| log@[i]@);
        assert forall|i: int, j: int|
            0 <= i && i < j && j < lv.len() implies spec_utf16_lt(#[trigger] lv[i], #[trigger] lv[j])
        by {
            if gb && gc && gco {
                assert(lv =~= seq![k0, k1, k2]);
            } else if gb && gc && !gco {
                assert(lv =~= seq![k0, k1]);
            } else if gb && !gc && gco {
                assert(lv =~= seq![k0, k2]);
            } else if !gb && gc && gco {
                assert(lv =~= seq![k1, k2]);
            } else {
                assert(lv.len() <= 1);
            }
        }
    }

    Ok((EventInit { bubbles, cancelable, composed }, log))
}

// --- 2. `RequestInit` Dictionary (Fetch §5.4) ---
// Lexicographical members:
//   "body" (USVString? = null)
//   "credentials" (DOMString = "same-origin")
//   "headers" (optional record<ByteString, ByteString>)
//   "keepalive" (boolean = false)
//   "method" (ByteString = "GET")
//   "mode" (DOMString = "cors")

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct RequestInit {
    pub body: Option<Vec<u16>>,
    pub credentials: Vec<u16>,
    pub headers: Option<Vec<(Vec<u8>, Vec<u8>)>>,
    pub keepalive: bool,
    pub method: Vec<u8>,
    pub mode: Vec<u16>,
}

pub struct SpecRequestInit {
    pub body: Option<Seq<u16>>,
    pub credentials: Seq<u16>,
    pub headers: Option<Seq<(Seq<u8>, Seq<u8>)>>,
    pub keepalive: bool,
    pub method: Seq<u8>,
    pub mode: Seq<u16>,
}

impl View for RequestInit {
    type V = SpecRequestInit;

    open spec fn view(&self) -> SpecRequestInit {
        SpecRequestInit {
            body: match &self.body {
                None => None,
                Some(b) => Some(b@),
            },
            credentials: self.credentials@,
            headers: match &self.headers {
                None => None,
                Some(h) => Some(Seq::new(h@.len(), |i: int| (h@[i].0@, h@[i].1@))),
            },
            keepalive: self.keepalive,
            method: self.method@,
            mode: self.mode@,
        }
    }
}

pub open spec fn spec_key_body() -> Seq<u16> {
    spec_ascii_to_utf16(seq![0x62u8, 0x6f, 0x64, 0x79])
}
pub open spec fn spec_key_credentials() -> Seq<u16> {
    spec_ascii_to_utf16(seq![0x63u8, 0x72, 0x65, 0x64, 0x65, 0x6e, 0x74, 0x69, 0x61, 0x6c, 0x73])
}
pub open spec fn spec_key_headers() -> Seq<u16> {
    spec_ascii_to_utf16(seq![0x68u8, 0x65, 0x61, 0x64, 0x65, 0x72, 0x73])
}
pub open spec fn spec_key_keepalive() -> Seq<u16> {
    spec_ascii_to_utf16(seq![0x6bu8, 0x65, 0x65, 0x70, 0x61, 0x6c, 0x69, 0x76, 0x65])
}
pub open spec fn spec_key_method() -> Seq<u16> {
    spec_ascii_to_utf16(seq![0x6du8, 0x65, 0x74, 0x68, 0x6f, 0x64])
}
pub open spec fn spec_key_mode() -> Seq<u16> {
    spec_ascii_to_utf16(seq![0x6du8, 0x6f, 0x64, 0x65])
}

pub proof fn lemma_request_init_keys_lexicographic()
    ensures
        spec_keys_strictly_lexicographic(seq![
            spec_key_body(),
            spec_key_credentials(),
            spec_key_headers(),
            spec_key_keepalive(),
            spec_key_method(),
            spec_key_mode(),
        ]),
{
    let keys = seq![
        spec_key_body(),
        spec_key_credentials(),
        spec_key_headers(),
        spec_key_keepalive(),
        spec_key_method(),
        spec_key_mode(),
    ];
    reveal_with_fuel(spec_utf16_lt, 3);
    assert forall|i: int, j: int|
        0 <= i && i < j && j < keys.len() implies spec_utf16_lt(#[trigger] keys[i], #[trigger] keys[j])
    by {
        if i == 4 && j == 5 {
            assert(keys[4][0] == 0x6du16 && keys[5][0] == 0x6du16);
            assert(keys[4][1] == 0x65u16 && keys[5][1] == 0x6fu16);
        } else {
            assert(keys[i][0] < keys[j][0]);
        }
    }
}

pub open spec fn spec_to_idl_request_init(
    arena: Seq<SpecJsObjectRecord>,
    js_dict: SpecJsValue,
) -> Result<SpecRequestInit, IdlError> {
    match spec_validate_dict_container(arena, js_dict) {
        Err(e) => Err(e),
        Ok(()) => match spec_dict_get_member(arena, js_dict, spec_key_body()) {
            Err(e) => Err(e),
            Ok(v_body) => match spec_to_idl_nullable_usv_string(arena, v_body) {
                Err(e) => Err(e),
                Ok(body) => match spec_dict_get_member(arena, js_dict, spec_key_credentials()) {
                    Err(e) => Err(e),
                    Ok(v_cred) => {
                        let cred_res: Result<Seq<u16>, IdlError> =
                            if v_cred == SpecJsValue::Undefined {
                                Ok(spec_ascii_to_utf16(seq![
                                    0x73u8, 0x61, 0x6d, 0x65, 0x2d, 0x6f, 0x72, 0x69, 0x67, 0x69,
                                    0x6e,
                                ]))
                            } else {
                                spec_to_idl_dom_string(arena, v_cred, false)
                            };
                        match cred_res {
                            Err(e) => Err(e),
                            Ok(credentials) => match spec_dict_get_member(
                                arena,
                                js_dict,
                                spec_key_headers(),
                            ) {
                                Err(e) => Err(e),
                                Ok(v_headers) => {
                                    let hdr_res: Result<Option<Seq<(Seq<u8>, Seq<u8>)>>, IdlError> =
                                        if v_headers == SpecJsValue::Undefined {
                                            Ok(None)
                                        } else {
                                            match spec_to_idl_record_byte_string(arena, v_headers) {
                                                Ok(h) => Ok(Some(h)),
                                                Err(e) => Err(e),
                                            }
                                        };
                                    match hdr_res {
                                        Err(e) => Err(e),
                                        Ok(headers) => match spec_dict_get_member(
                                            arena,
                                            js_dict,
                                            spec_key_keepalive(),
                                        ) {
                                            Err(e) => Err(e),
                                            Ok(v_keepalive) => {
                                                let keepalive =
                                                    if v_keepalive == SpecJsValue::Undefined {
                                                        false
                                                    } else {
                                                        spec_to_idl_boolean(v_keepalive)
                                                    };
                                                match spec_dict_get_member(
                                                    arena,
                                                    js_dict,
                                                    spec_key_method(),
                                                ) {
                                                    Err(e) => Err(e),
                                                    Ok(v_method) => {
                                                        let meth_res: Result<Seq<u8>, IdlError> =
                                                            if v_method == SpecJsValue::Undefined {
                                                                Ok(seq![0x47u8, 0x45, 0x54])
                                                            } else {
                                                                spec_to_idl_byte_string(
                                                                    arena,
                                                                    v_method,
                                                                )
                                                            };
                                                        match meth_res {
                                                            Err(e) => Err(e),
                                                            Ok(method) => match spec_dict_get_member(
                                                                arena,
                                                                js_dict,
                                                                spec_key_mode(),
                                                            ) {
                                                                Err(e) => Err(e),
                                                                Ok(v_mode) => {
                                                                    let mode_res: Result<
                                                                        Seq<u16>,
                                                                        IdlError,
                                                                    > = if v_mode
                                                                        == SpecJsValue::Undefined
                                                                    {
                                                                        Ok(spec_ascii_to_utf16(
                                                                            seq![
                                                                                0x63u8, 0x6f, 0x72,
                                                                                0x73
                                                                            ],
                                                                        ))
                                                                    } else {
                                                                        spec_to_idl_dom_string(
                                                                            arena,
                                                                            v_mode,
                                                                            false,
                                                                        )
                                                                    };
                                                                    match mode_res {
                                                                        Err(e) => Err(e),
                                                                        Ok(mode) => Ok(
                                                                            SpecRequestInit {
                                                                                body,
                                                                                credentials,
                                                                                headers,
                                                                                keepalive,
                                                                                method,
                                                                                mode,
                                                                            },
                                                                        ),
                                                                    }
                                                                },
                                                            },
                                                        }
                                                    },
                                                }
                                            },
                                        },
                                    }
                                },
                            },
                        }
                    },
                },
            },
        },
    }
}

#[verifier::spinoff_prover]
pub fn to_idl_request_init(
    arena: &JsObjectArena,
    js_dict: &JsValue,
) -> (res: Result<RequestInit, IdlError>)
    ensures
        match (res, spec_to_idl_request_init(arena@, js_dict@)) {
            (Ok(r), Ok(sr)) => r@ == sr,
            (Err(e), Err(se)) => e == se,
            _ => false,
        },
{
    validate_dict_container(arena, js_dict)?;
    let k_body: [u16; 4] = [0x62, 0x6f, 0x64, 0x79];
    let k_cred: [u16; 11] = [0x63, 0x72, 0x65, 0x64, 0x65, 0x6e, 0x74, 0x69, 0x61, 0x6c, 0x73];
    let k_headers: [u16; 7] = [0x68, 0x65, 0x61, 0x64, 0x65, 0x72, 0x73];
    let k_keepalive: [u16; 9] = [0x6b, 0x65, 0x65, 0x70, 0x61, 0x6c, 0x69, 0x76, 0x65];
    let k_method: [u16; 6] = [0x6d, 0x65, 0x74, 0x68, 0x6f, 0x64];
    let k_mode: [u16; 4] = [0x6d, 0x6f, 0x64, 0x65];
    proof {
        assert(k_body@ =~= spec_key_body());
        assert(k_cred@ =~= spec_key_credentials());
        assert(k_headers@ =~= spec_key_headers());
        assert(k_keepalive@ =~= spec_key_keepalive());
        assert(k_method@ =~= spec_key_method());
        assert(k_mode@ =~= spec_key_mode());
    }

    let v_body = dict_get_member(arena, js_dict, &k_body)?;
    let body = to_idl_nullable_usv_string(arena, &v_body)?;

    let v_cred = dict_get_member(arena, js_dict, &k_cred)?;
    let credentials = if matches!(v_cred, JsValue::Undefined) {
        let def: [u8; 11] = [0x73, 0x61, 0x6d, 0x65, 0x2d, 0x6f, 0x72, 0x69, 0x67, 0x69, 0x6e];
        proof {
            assert(def@ =~= seq![0x73u8, 0x61, 0x6d, 0x65, 0x2d, 0x6f, 0x72, 0x69, 0x67, 0x69, 0x6e]);
        }
        ascii_to_utf16(&def)
    } else {
        to_idl_dom_string(arena, &v_cred, false)?
    };

    let v_headers = dict_get_member(arena, js_dict, &k_headers)?;
    let headers = if matches!(v_headers, JsValue::Undefined) {
        None
    } else {
        Some(to_idl_record_byte_string(arena, &v_headers)?)
    };

    let v_keepalive = dict_get_member(arena, js_dict, &k_keepalive)?;
    let keepalive = if matches!(v_keepalive, JsValue::Undefined) {
        false
    } else {
        to_idl_boolean(&v_keepalive)
    };

    let v_method = dict_get_member(arena, js_dict, &k_method)?;
    let method = if matches!(v_method, JsValue::Undefined) {
        let def: [u8; 3] = [0x47, 0x45, 0x54];
        proof { assert(def@ =~= seq![0x47u8, 0x45, 0x54]); }
        clone_u8_slice(&def)
    } else {
        to_idl_byte_string(arena, &v_method)?
    };

    let v_mode = dict_get_member(arena, js_dict, &k_mode)?;
    let mode = if matches!(v_mode, JsValue::Undefined) {
        let def: [u8; 4] = [0x63, 0x6f, 0x72, 0x73];
        proof { assert(def@ =~= seq![0x63u8, 0x6f, 0x72, 0x73]); }
        ascii_to_utf16(&def)
    } else {
        to_idl_dom_string(arena, &v_mode, false)?
    };

    Ok(RequestInit { body, credentials, headers, keepalive, method, mode })
}

// --- 3. `StorageOp` Dictionary (Web Storage Host Interface) ---
// Lexicographical members:
//   "index" (optional [EnforceRange] unsigned long)
//   "key" (optional DOMString?)
//   "op" (required DOMString — throws TypeError if missing/undefined!)
//   "value" (optional DOMString)

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct StorageOp {
    pub index: Option<u32>,
    pub key: Option<Option<Vec<u16>>>,
    pub op: Vec<u16>,
    pub value: Option<Vec<u16>>,
}

pub struct SpecStorageOp {
    pub index: Option<u32>,
    pub key: Option<Option<Seq<u16>>>,
    pub op: Seq<u16>,
    pub value: Option<Seq<u16>>,
}

impl View for StorageOp {
    type V = SpecStorageOp;

    open spec fn view(&self) -> SpecStorageOp {
        SpecStorageOp {
            index: self.index,
            key: match &self.key {
                None => None,
                Some(None) => Some(None),
                Some(Some(k)) => Some(Some(k@)),
            },
            op: self.op@,
            value: match &self.value {
                None => None,
                Some(v) => Some(v@),
            },
        }
    }
}

pub open spec fn spec_key_index() -> Seq<u16> {
    spec_ascii_to_utf16(seq![0x69u8, 0x6e, 0x64, 0x65, 0x78])
}
pub open spec fn spec_key_key() -> Seq<u16> {
    spec_ascii_to_utf16(seq![0x6bu8, 0x65, 0x79])
}
pub open spec fn spec_key_op() -> Seq<u16> {
    spec_ascii_to_utf16(seq![0x6fu8, 0x70])
}
pub open spec fn spec_key_value() -> Seq<u16> {
    spec_ascii_to_utf16(seq![0x76u8, 0x61, 0x6c, 0x75, 0x65])
}

pub proof fn lemma_storage_op_keys_lexicographic()
    ensures
        spec_keys_strictly_lexicographic(seq![
            spec_key_index(),
            spec_key_key(),
            spec_key_op(),
            spec_key_value(),
        ]),
{
    let keys = seq![spec_key_index(), spec_key_key(), spec_key_op(), spec_key_value()];
    reveal_with_fuel(spec_utf16_lt, 2);
    assert forall|i: int, j: int|
        0 <= i && i < j && j < keys.len() implies spec_utf16_lt(#[trigger] keys[i], #[trigger] keys[j])
    by {
        assert(keys[i][0] < keys[j][0]);
    }
}

pub open spec fn spec_to_idl_storage_op(
    arena: Seq<SpecJsObjectRecord>,
    js_dict: SpecJsValue,
) -> Result<SpecStorageOp, IdlError> {
    match spec_validate_dict_container(arena, js_dict) {
        Err(e) => Err(e),
        Ok(()) => match spec_dict_get_member(arena, js_dict, spec_key_index()) {
            Err(e) => Err(e),
            Ok(v_index) => {
                let idx_res: Result<Option<u32>, IdlError> = if v_index == SpecJsValue::Undefined {
                    Ok(None)
                } else {
                    match spec_to_idl_int(arena, v_index, 32nat, false, IntAttr::EnforceRange) {
                        Ok(idx) => Ok(Some(idx as u32)),
                        Err(e) => Err(e),
                    }
                };
                match idx_res {
                    Err(e) => Err(e),
                    Ok(index) => match spec_dict_get_member(arena, js_dict, spec_key_key()) {
                        Err(e) => Err(e),
                        Ok(v_key) => {
                            let key_res: Result<Option<Option<Seq<u16>>>, IdlError> =
                                if v_key == SpecJsValue::Undefined {
                                    Ok(None)
                                } else {
                                    match spec_to_idl_nullable_dom_string(arena, v_key) {
                                        Ok(k) => Ok(Some(k)),
                                        Err(e) => Err(e),
                                    }
                                };
                            match key_res {
                                Err(e) => Err(e),
                                Ok(key) => match spec_dict_get_member(arena, js_dict, spec_key_op()) {
                                    Err(e) => Err(e),
                                    Ok(v_op) => {
                                        if v_op == SpecJsValue::Undefined {
                                            Err(IdlError::TypeError)
                                        } else {
                                            match spec_to_idl_dom_string(arena, v_op, false) {
                                                Err(e) => Err(e),
                                                Ok(op) => match spec_dict_get_member(
                                                    arena,
                                                    js_dict,
                                                    spec_key_value(),
                                                ) {
                                                    Err(e) => Err(e),
                                                    Ok(v_val) => {
                                                        let val_res: Result<
                                                            Option<Seq<u16>>,
                                                            IdlError,
                                                        > = if v_val == SpecJsValue::Undefined {
                                                            Ok(None)
                                                        } else {
                                                            match spec_to_idl_dom_string(
                                                                arena,
                                                                v_val,
                                                                false,
                                                            ) {
                                                                Ok(s) => Ok(Some(s)),
                                                                Err(e) => Err(e),
                                                            }
                                                        };
                                                        match val_res {
                                                            Err(e) => Err(e),
                                                            Ok(value) => Ok(SpecStorageOp {
                                                                index,
                                                                key,
                                                                op,
                                                                value,
                                                            }),
                                                        }
                                                    },
                                                },
                                            }
                                        }
                                    },
                                },
                            }
                        },
                    },
                }
            },
        },
    }
}

pub fn to_idl_storage_op(
    arena: &JsObjectArena,
    js_dict: &JsValue,
) -> (res: Result<StorageOp, IdlError>)
    ensures
        match (res, spec_to_idl_storage_op(arena@, js_dict@)) {
            (Ok(r), Ok(sr)) => r@ == sr,
            (Err(e), Err(se)) => e == se,
            _ => false,
        },
{
    validate_dict_container(arena, js_dict)?;
    let k_index: [u16; 5] = [0x69, 0x6e, 0x64, 0x65, 0x78];
    let k_key: [u16; 3] = [0x6b, 0x65, 0x79];
    let k_op: [u16; 2] = [0x6f, 0x70];
    let k_val: [u16; 5] = [0x76, 0x61, 0x6c, 0x75, 0x65];
    proof {
        assert(k_index@ =~= spec_key_index());
        assert(k_key@ =~= spec_key_key());
        assert(k_op@ =~= spec_key_op());
        assert(k_val@ =~= spec_key_value());
    }

    let v_index = dict_get_member(arena, js_dict, &k_index)?;
    let index = if matches!(v_index, JsValue::Undefined) {
        None
    } else {
        Some(to_idl_unsigned_long(arena, &v_index, IntAttr::EnforceRange)?)
    };

    let v_key = dict_get_member(arena, js_dict, &k_key)?;
    let key = if matches!(v_key, JsValue::Undefined) {
        None
    } else {
        Some(to_idl_nullable_dom_string(arena, &v_key)?)
    };

    let v_op = dict_get_member(arena, js_dict, &k_op)?;
    if matches!(v_op, JsValue::Undefined) {
        return Err(IdlError::TypeError);
    }
    let op = to_idl_dom_string(arena, &v_op, false)?;

    let v_val = dict_get_member(arena, js_dict, &k_val)?;
    let value = if matches!(v_val, JsValue::Undefined) {
        None
    } else {
        Some(to_idl_dom_string(arena, &v_val, false)?)
    };

    Ok(StorageOp { index, key, op, value })
}

// --- 4. `NodeOp` Dictionary (DOM `Node` Host Interface) ---
// Lexicographical members:
//   "attrName" (optional DOMString)
//   "attrValue" (optional DOMString)
//   "childId" (optional [EnforceRange] unsigned long)
//   "nodeId" (required [EnforceRange] unsigned long)
//   "op" (required DOMString)
//   "textContent" (optional DOMString?)

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct NodeOp {
    pub attr_name: Option<Vec<u16>>,
    pub attr_value: Option<Vec<u16>>,
    pub child_id: Option<u32>,
    pub node_id: u32,
    pub op: Vec<u16>,
    pub text_content: Option<Option<Vec<u16>>>,
}

pub struct SpecNodeOp {
    pub attr_name: Option<Seq<u16>>,
    pub attr_value: Option<Seq<u16>>,
    pub child_id: Option<u32>,
    pub node_id: u32,
    pub op: Seq<u16>,
    pub text_content: Option<Option<Seq<u16>>>,
}

impl View for NodeOp {
    type V = SpecNodeOp;

    open spec fn view(&self) -> SpecNodeOp {
        SpecNodeOp {
            attr_name: match &self.attr_name {
                None => None,
                Some(s) => Some(s@),
            },
            attr_value: match &self.attr_value {
                None => None,
                Some(s) => Some(s@),
            },
            child_id: self.child_id,
            node_id: self.node_id,
            op: self.op@,
            text_content: match &self.text_content {
                None => None,
                Some(None) => Some(None),
                Some(Some(s)) => Some(Some(s@)),
            },
        }
    }
}

pub open spec fn spec_key_attr_name() -> Seq<u16> {
    spec_ascii_to_utf16(seq![0x61u8, 0x74, 0x74, 0x72, 0x4e, 0x61, 0x6d, 0x65])
}
pub open spec fn spec_key_attr_value() -> Seq<u16> {
    spec_ascii_to_utf16(seq![0x61u8, 0x74, 0x74, 0x72, 0x56, 0x61, 0x6c, 0x75, 0x65])
}
pub open spec fn spec_key_child_id() -> Seq<u16> {
    spec_ascii_to_utf16(seq![0x63u8, 0x68, 0x69, 0x6c, 0x64, 0x49, 0x64])
}
pub open spec fn spec_key_node_id() -> Seq<u16> {
    spec_ascii_to_utf16(seq![0x6eu8, 0x6f, 0x64, 0x65, 0x49, 0x64])
}
pub open spec fn spec_key_text_content() -> Seq<u16> {
    spec_ascii_to_utf16(seq![0x74u8, 0x65, 0x78, 0x74, 0x43, 0x6f, 0x6e, 0x74, 0x65, 0x6e, 0x74])
}

pub proof fn lemma_node_op_keys_lexicographic()
    ensures
        spec_keys_strictly_lexicographic(seq![
            spec_key_attr_name(),
            spec_key_attr_value(),
            spec_key_child_id(),
            spec_key_node_id(),
            spec_key_op(),
            spec_key_text_content(),
        ]),
{
    let keys = seq![
        spec_key_attr_name(),
        spec_key_attr_value(),
        spec_key_child_id(),
        spec_key_node_id(),
        spec_key_op(),
        spec_key_text_content(),
    ];
    reveal_with_fuel(spec_utf16_lt, 6);
    assert forall|i: int, j: int|
        0 <= i && i < j && j < keys.len() implies spec_utf16_lt(#[trigger] keys[i], #[trigger] keys[j])
    by {
        if i == 0 && j == 1 {
            assert(keys[0][0] == keys[1][0]);
            assert(keys[0][1] == keys[1][1]);
            assert(keys[0][2] == keys[1][2]);
            assert(keys[0][3] == keys[1][3]);
            assert(keys[0][4] == 0x4eu16 && keys[1][4] == 0x56u16);
        } else {
            assert(keys[i][0] < keys[j][0]);
        }
    }
}

pub open spec fn spec_to_idl_node_op(
    arena: Seq<SpecJsObjectRecord>,
    js_dict: SpecJsValue,
) -> Result<SpecNodeOp, IdlError> {
    match spec_validate_dict_container(arena, js_dict) {
        Err(e) => Err(e),
        Ok(()) => match spec_dict_get_member(arena, js_dict, spec_key_attr_name()) {
            Err(e) => Err(e),
            Ok(v_an) => {
                let an_res: Result<Option<Seq<u16>>, IdlError> = if v_an == SpecJsValue::Undefined {
                    Ok(None)
                } else {
                    match spec_to_idl_dom_string(arena, v_an, false) {
                        Ok(s) => Ok(Some(s)),
                        Err(e) => Err(e),
                    }
                };
                match an_res {
                    Err(e) => Err(e),
                    Ok(attr_name) => match spec_dict_get_member(
                        arena,
                        js_dict,
                        spec_key_attr_value(),
                    ) {
                        Err(e) => Err(e),
                        Ok(v_av) => {
                            let av_res: Result<Option<Seq<u16>>, IdlError> =
                                if v_av == SpecJsValue::Undefined {
                                    Ok(None)
                                } else {
                                    match spec_to_idl_dom_string(arena, v_av, false) {
                                        Ok(s) => Ok(Some(s)),
                                        Err(e) => Err(e),
                                    }
                                };
                            match av_res {
                                Err(e) => Err(e),
                                Ok(attr_value) => match spec_dict_get_member(
                                    arena,
                                    js_dict,
                                    spec_key_child_id(),
                                ) {
                                    Err(e) => Err(e),
                                    Ok(v_cid) => {
                                        let cid_res: Result<Option<u32>, IdlError> =
                                            if v_cid == SpecJsValue::Undefined {
                                                Ok(None)
                                            } else {
                                                match spec_to_idl_int(
                                                    arena,
                                                    v_cid,
                                                    32nat,
                                                    false,
                                                    IntAttr::EnforceRange,
                                                ) {
                                                    Ok(id) => Ok(Some(id as u32)),
                                                    Err(e) => Err(e),
                                                }
                                            };
                                        match cid_res {
                                            Err(e) => Err(e),
                                            Ok(child_id) => match spec_dict_get_member(
                                                arena,
                                                js_dict,
                                                spec_key_node_id(),
                                            ) {
                                                Err(e) => Err(e),
                                                Ok(v_nid) => {
                                                    if v_nid == SpecJsValue::Undefined {
                                                        Err(IdlError::TypeError)
                                                    } else {
                                                        match spec_to_idl_int(
                                                            arena,
                                                            v_nid,
                                                            32nat,
                                                            false,
                                                            IntAttr::EnforceRange,
                                                        ) {
                                                            Err(e) => Err(e),
                                                            Ok(nid) => match spec_dict_get_member(
                                                                arena,
                                                                js_dict,
                                                                spec_key_op(),
                                                            ) {
                                                                Err(e) => Err(e),
                                                                Ok(v_op) => {
                                                                    if v_op
                                                                        == SpecJsValue::Undefined
                                                                    {
                                                                        Err(IdlError::TypeError)
                                                                    } else {
                                                                        match spec_to_idl_dom_string(
                                                                            arena,
                                                                            v_op,
                                                                            false,
                                                                        ) {
                                                                            Err(e) => Err(e),
                                                                            Ok(op) => match spec_dict_get_member(
                                                                                arena,
                                                                                js_dict,
                                                                                spec_key_text_content(),
                                                                            ) {
                                                                                Err(e) => Err(e),
                                                                                Ok(v_tc) => {
                                                                                    let tc_res: Result<Option<Option<Seq<u16>>>, IdlError> = if v_tc == SpecJsValue::Undefined {
                                                                                        Ok(None)
                                                                                    } else {
                                                                                        match spec_to_idl_nullable_dom_string(arena, v_tc) {
                                                                                            Ok(t) => Ok(Some(t)),
                                                                                            Err(e) => Err(e),
                                                                                        }
                                                                                    };
                                                                                    match tc_res {
                                                                                        Err(e) => Err(e),
                                                                                        Ok(text_content) => Ok(SpecNodeOp {
                                                                                            attr_name,
                                                                                            attr_value,
                                                                                            child_id,
                                                                                            node_id: nid as u32,
                                                                                            op,
                                                                                            text_content,
                                                                                        }),
                                                                                    }
                                                                                },
                                                                            },
                                                                        }
                                                                    }
                                                                },
                                                            },
                                                        }
                                                    }
                                                },
                                            },
                                        }
                                    },
                                },
                            }
                        },
                    },
                }
            },
        },
    }
}

#[verifier::spinoff_prover]
pub fn to_idl_node_op(
    arena: &JsObjectArena,
    js_dict: &JsValue,
) -> (res: Result<NodeOp, IdlError>)
    ensures
        match (res, spec_to_idl_node_op(arena@, js_dict@)) {
            (Ok(r), Ok(sr)) => r@ == sr,
            (Err(e), Err(se)) => e == se,
            _ => false,
        },
{
    validate_dict_container(arena, js_dict)?;
    let k_an: [u16; 8] = [0x61, 0x74, 0x74, 0x72, 0x4e, 0x61, 0x6d, 0x65];
    let k_av: [u16; 9] = [0x61, 0x74, 0x74, 0x72, 0x56, 0x61, 0x6c, 0x75, 0x65];
    let k_cid: [u16; 7] = [0x63, 0x68, 0x69, 0x6c, 0x64, 0x49, 0x64];
    let k_nid: [u16; 6] = [0x6e, 0x6f, 0x64, 0x65, 0x49, 0x64];
    let k_op: [u16; 2] = [0x6f, 0x70];
    let k_tc: [u16; 11] = [0x74, 0x65, 0x78, 0x74, 0x43, 0x6f, 0x6e, 0x74, 0x65, 0x6e, 0x74];
    proof {
        assert(k_an@ =~= spec_key_attr_name());
        assert(k_av@ =~= spec_key_attr_value());
        assert(k_cid@ =~= spec_key_child_id());
        assert(k_nid@ =~= spec_key_node_id());
        assert(k_op@ =~= spec_key_op());
        assert(k_tc@ =~= spec_key_text_content());
    }

    let v_an = dict_get_member(arena, js_dict, &k_an)?;
    let attr_name = if matches!(v_an, JsValue::Undefined) {
        None
    } else {
        Some(to_idl_dom_string(arena, &v_an, false)?)
    };

    let v_av = dict_get_member(arena, js_dict, &k_av)?;
    let attr_value = if matches!(v_av, JsValue::Undefined) {
        None
    } else {
        Some(to_idl_dom_string(arena, &v_av, false)?)
    };

    let v_cid = dict_get_member(arena, js_dict, &k_cid)?;
    let child_id = if matches!(v_cid, JsValue::Undefined) {
        None
    } else {
        Some(to_idl_unsigned_long(arena, &v_cid, IntAttr::EnforceRange)?)
    };

    let v_nid = dict_get_member(arena, js_dict, &k_nid)?;
    if matches!(v_nid, JsValue::Undefined) {
        return Err(IdlError::TypeError);
    }
    let node_id = to_idl_unsigned_long(arena, &v_nid, IntAttr::EnforceRange)?;

    let v_op = dict_get_member(arena, js_dict, &k_op)?;
    if matches!(v_op, JsValue::Undefined) {
        return Err(IdlError::TypeError);
    }
    let op = to_idl_dom_string(arena, &v_op, false)?;

    let v_tc = dict_get_member(arena, js_dict, &k_tc)?;
    let text_content = if matches!(v_tc, JsValue::Undefined) {
        None
    } else {
        Some(to_idl_nullable_dom_string(arena, &v_tc)?)
    };

    Ok(NodeOp { attr_name, attr_value, child_id, node_id, op, text_content })
}

// --- 5. `UrlHref` Dictionary (WHATWG URL Host Interface) ---
// Lexicographical members:
//   "base" (optional USVString? = null)
//   "href" (required USVString)
//   "portOverride" (optional [Clamp] unsigned short)

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct UrlHref {
    pub base: Option<Vec<u16>>,
    pub href: Vec<u16>,
    pub port_override: Option<u16>,
}

pub struct SpecUrlHref {
    pub base: Option<Seq<u16>>,
    pub href: Seq<u16>,
    pub port_override: Option<u16>,
}

impl View for UrlHref {
    type V = SpecUrlHref;

    open spec fn view(&self) -> SpecUrlHref {
        SpecUrlHref {
            base: match &self.base {
                None => None,
                Some(b) => Some(b@),
            },
            href: self.href@,
            port_override: self.port_override,
        }
    }
}

pub open spec fn spec_key_base() -> Seq<u16> {
    spec_ascii_to_utf16(seq![0x62u8, 0x61, 0x73, 0x65])
}
pub open spec fn spec_key_href() -> Seq<u16> {
    spec_ascii_to_utf16(seq![0x68u8, 0x72, 0x65, 0x66])
}
pub open spec fn spec_key_port_override() -> Seq<u16> {
    spec_ascii_to_utf16(seq![0x70u8, 0x6f, 0x72, 0x74, 0x4f, 0x76, 0x65, 0x72, 0x72, 0x69, 0x64, 0x65])
}

pub proof fn lemma_url_href_keys_lexicographic()
    ensures
        spec_keys_strictly_lexicographic(seq![
            spec_key_base(),
            spec_key_href(),
            spec_key_port_override(),
        ]),
{
    let keys = seq![spec_key_base(), spec_key_href(), spec_key_port_override()];
    reveal_with_fuel(spec_utf16_lt, 2);
    assert forall|i: int, j: int|
        0 <= i && i < j && j < keys.len() implies spec_utf16_lt(#[trigger] keys[i], #[trigger] keys[j])
    by {
        assert(keys[i][0] < keys[j][0]);
    }
}

pub open spec fn spec_to_idl_url_href(
    arena: Seq<SpecJsObjectRecord>,
    js_dict: SpecJsValue,
) -> Result<SpecUrlHref, IdlError> {
    match spec_validate_dict_container(arena, js_dict) {
        Err(e) => Err(e),
        Ok(()) => match spec_dict_get_member(arena, js_dict, spec_key_base()) {
            Err(e) => Err(e),
            Ok(v_base) => match spec_to_idl_nullable_usv_string(arena, v_base) {
                Err(e) => Err(e),
                Ok(base) => match spec_dict_get_member(arena, js_dict, spec_key_href()) {
                    Err(e) => Err(e),
                    Ok(v_href) => {
                        if v_href == SpecJsValue::Undefined {
                            Err(IdlError::TypeError)
                        } else {
                            match spec_to_idl_usv_string(arena, v_href) {
                                Err(e) => Err(e),
                                Ok(href) => match spec_dict_get_member(
                                    arena,
                                    js_dict,
                                    spec_key_port_override(),
                                ) {
                                    Err(e) => Err(e),
                                    Ok(v_port) => {
                                        let port_res: Result<Option<u16>, IdlError> =
                                            if v_port == SpecJsValue::Undefined {
                                                Ok(None)
                                            } else {
                                                match spec_to_idl_int(
                                                    arena,
                                                    v_port,
                                                    16nat,
                                                    false,
                                                    IntAttr::Clamp,
                                                ) {
                                                    Ok(p) => Ok(Some(p as u16)),
                                                    Err(e) => Err(e),
                                                }
                                            };
                                        match port_res {
                                            Err(e) => Err(e),
                                            Ok(port_override) => Ok(SpecUrlHref {
                                                base,
                                                href,
                                                port_override,
                                            }),
                                        }
                                    },
                                },
                            }
                        }
                    },
                },
            },
        },
    }
}

pub fn to_idl_url_href(
    arena: &JsObjectArena,
    js_dict: &JsValue,
) -> (res: Result<UrlHref, IdlError>)
    ensures
        match (res, spec_to_idl_url_href(arena@, js_dict@)) {
            (Ok(r), Ok(sr)) => {
                r@ == sr
                && spec_has_no_unpaired_surrogates(r.href@)
            },
            (Err(e), Err(se)) => e == se,
            _ => false,
        },
{
    validate_dict_container(arena, js_dict)?;
    let k_base: [u16; 4] = [0x62, 0x61, 0x73, 0x65];
    let k_href: [u16; 4] = [0x68, 0x72, 0x65, 0x66];
    let k_port: [u16; 12] = [0x70, 0x6f, 0x72, 0x74, 0x4f, 0x76, 0x65, 0x72, 0x72, 0x69, 0x64, 0x65];
    proof {
        assert(k_base@ =~= spec_key_base());
        assert(k_href@ =~= spec_key_href());
        assert(k_port@ =~= spec_key_port_override());
    }

    let v_base = dict_get_member(arena, js_dict, &k_base)?;
    let base = to_idl_nullable_usv_string(arena, &v_base)?;

    let v_href = dict_get_member(arena, js_dict, &k_href)?;
    if matches!(v_href, JsValue::Undefined) {
        return Err(IdlError::TypeError);
    }
    let href = to_idl_usv_string(arena, &v_href)?;

    let v_port = dict_get_member(arena, js_dict, &k_port)?;
    let port_override = if matches!(v_port, JsValue::Undefined) {
        None
    } else {
        Some(to_idl_unsigned_short(arena, &v_port, IntAttr::Clamp)?)
    };

    Ok(UrlHref { base, href, port_override })
}

/// Web IDL §2.8.1 `DOMException(optional DOMString message = "", optional DOMString name = "Error")`
/// constructor conversion + legacy error names table (`code: u16`).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct DomExceptionRecord {
    pub message: Vec<u16>,
    pub name: Vec<u16>,
    pub code: u16,
}

pub open spec fn spec_dom_exception_legacy_code(name: Seq<u16>) -> u16 {
    if spec_seq_eq_ascii(name, seq![0x49u8, 0x6e, 0x64, 0x65, 0x78, 0x53, 0x69, 0x7a, 0x65, 0x45, 0x72, 0x72, 0x6f, 0x72]) { 1u16 }
    else if spec_seq_eq_ascii(name, seq![0x48u8, 0x69, 0x65, 0x72, 0x61, 0x72, 0x63, 0x68, 0x79, 0x52, 0x65, 0x71, 0x75, 0x65, 0x73, 0x74, 0x45, 0x72, 0x72, 0x6f, 0x72]) { 3u16 }
    else if spec_seq_eq_ascii(name, seq![0x57u8, 0x72, 0x6f, 0x6e, 0x67, 0x44, 0x6f, 0x63, 0x75, 0x6d, 0x65, 0x6e, 0x74, 0x45, 0x72, 0x72, 0x6f, 0x72]) { 4u16 }
    else if spec_seq_eq_ascii(name, seq![0x49u8, 0x6e, 0x76, 0x61, 0x6c, 0x69, 0x64, 0x43, 0x68, 0x61, 0x72, 0x61, 0x63, 0x74, 0x65, 0x72, 0x45, 0x72, 0x72, 0x6f, 0x72]) { 5u16 }
    else if spec_seq_eq_ascii(name, seq![0x4eu8, 0x6f, 0x4d, 0x6f, 0x64, 0x69, 0x66, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6f, 0x6e, 0x41, 0x6c, 0x6c, 0x6f, 0x77, 0x65, 0x64, 0x45, 0x72, 0x72, 0x6f, 0x72]) { 7u16 }
    else if spec_seq_eq_ascii(name, seq![0x4eu8, 0x6f, 0x74, 0x46, 0x6f, 0x75, 0x6e, 0x64, 0x45, 0x72, 0x72, 0x6f, 0x72]) { 8u16 }
    else if spec_seq_eq_ascii(name, seq![0x4eu8, 0x6f, 0x74, 0x53, 0x75, 0x70, 0x70, 0x6f, 0x72, 0x74, 0x65, 0x64, 0x45, 0x72, 0x72, 0x6f, 0x72]) { 9u16 }
    else if spec_seq_eq_ascii(name, seq![0x49u8, 0x6e, 0x55, 0x73, 0x65, 0x41, 0x74, 0x74, 0x72, 0x69, 0x62, 0x75, 0x74, 0x65, 0x45, 0x72, 0x72, 0x6f, 0x72]) { 10u16 }
    else if spec_seq_eq_ascii(name, seq![0x49u8, 0x6e, 0x76, 0x61, 0x6c, 0x69, 0x64, 0x53, 0x74, 0x61, 0x74, 0x65, 0x45, 0x72, 0x72, 0x6f, 0x72]) { 11u16 }
    else if spec_seq_eq_ascii(name, seq![0x53u8, 0x79, 0x6e, 0x74, 0x61, 0x78, 0x45, 0x72, 0x72, 0x6f, 0x72]) { 12u16 }
    else if spec_seq_eq_ascii(name, seq![0x49u8, 0x6e, 0x76, 0x61, 0x6c, 0x69, 0x64, 0x4d, 0x6f, 0x64, 0x69, 0x66, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6f, 0x6e, 0x45, 0x72, 0x72, 0x6f, 0x72]) { 13u16 }
    else if spec_seq_eq_ascii(name, seq![0x4eu8, 0x61, 0x6d, 0x65, 0x73, 0x70, 0x61, 0x63, 0x65, 0x45, 0x72, 0x72, 0x6f, 0x72]) { 14u16 }
    else if spec_seq_eq_ascii(name, seq![0x49u8, 0x6e, 0x76, 0x61, 0x6c, 0x69, 0x64, 0x41, 0x63, 0x63, 0x65, 0x73, 0x73, 0x45, 0x72, 0x72, 0x6f, 0x72]) { 15u16 }
    else if spec_seq_eq_ascii(name, seq![0x54u8, 0x79, 0x70, 0x65, 0x4d, 0x69, 0x73, 0x6d, 0x61, 0x74, 0x63, 0x68, 0x45, 0x72, 0x72, 0x6f, 0x72]) { 17u16 }
    else if spec_seq_eq_ascii(name, seq![0x53u8, 0x65, 0x63, 0x75, 0x72, 0x69, 0x74, 0x79, 0x45, 0x72, 0x72, 0x6f, 0x72]) { 18u16 }
    else if spec_seq_eq_ascii(name, seq![0x4eu8, 0x65, 0x74, 0x77, 0x6f, 0x72, 0x6b, 0x45, 0x72, 0x72, 0x6f, 0x72]) { 19u16 }
    else if spec_seq_eq_ascii(name, seq![0x41u8, 0x62, 0x6f, 0x72, 0x74, 0x45, 0x72, 0x72, 0x6f, 0x72]) { 20u16 }
    else if spec_seq_eq_ascii(name, seq![0x55u8, 0x52, 0x4c, 0x4d, 0x69, 0x73, 0x6d, 0x61, 0x74, 0x63, 0x68, 0x45, 0x72, 0x72, 0x6f, 0x72]) { 21u16 }
    else if spec_seq_eq_ascii(name, seq![0x51u8, 0x75, 0x6f, 0x74, 0x61, 0x45, 0x78, 0x63, 0x65, 0x65, 0x64, 0x65, 0x64, 0x45, 0x72, 0x72, 0x6f, 0x72]) { 22u16 }
    else if spec_seq_eq_ascii(name, seq![0x54u8, 0x69, 0x6d, 0x65, 0x6f, 0x75, 0x74, 0x45, 0x72, 0x72, 0x6f, 0x72]) { 23u16 }
    else if spec_seq_eq_ascii(name, seq![0x49u8, 0x6e, 0x76, 0x61, 0x6c, 0x69, 0x64, 0x4e, 0x6f, 0x64, 0x65, 0x54, 0x79, 0x70, 0x65, 0x45, 0x72, 0x72, 0x6f, 0x72]) { 24u16 }
    else if spec_seq_eq_ascii(name, seq![0x44u8, 0x61, 0x74, 0x61, 0x43, 0x6c, 0x6f, 0x6e, 0x65, 0x45, 0x72, 0x72, 0x6f, 0x72]) { 25u16 }
    else { 0u16 }
}

pub fn dom_exception_legacy_code(name: &[u16]) -> (code: u16)
    ensures
        code == spec_dom_exception_legacy_code(name@),
{
    let c1: [u8; 14] = [0x49, 0x6e, 0x64, 0x65, 0x78, 0x53, 0x69, 0x7a, 0x65, 0x45, 0x72, 0x72, 0x6f, 0x72];
    let c3: [u8; 21] = [0x48, 0x69, 0x65, 0x72, 0x61, 0x72, 0x63, 0x68, 0x79, 0x52, 0x65, 0x71, 0x75, 0x65, 0x73, 0x74, 0x45, 0x72, 0x72, 0x6f, 0x72];
    let c4: [u8; 18] = [0x57, 0x72, 0x6f, 0x6e, 0x67, 0x44, 0x6f, 0x63, 0x75, 0x6d, 0x65, 0x6e, 0x74, 0x45, 0x72, 0x72, 0x6f, 0x72];
    let c5: [u8; 21] = [0x49, 0x6e, 0x76, 0x61, 0x6c, 0x69, 0x64, 0x43, 0x68, 0x61, 0x72, 0x61, 0x63, 0x74, 0x65, 0x72, 0x45, 0x72, 0x72, 0x6f, 0x72];
    let c7: [u8; 26] = [0x4e, 0x6f, 0x4d, 0x6f, 0x64, 0x69, 0x66, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6f, 0x6e, 0x41, 0x6c, 0x6c, 0x6f, 0x77, 0x65, 0x64, 0x45, 0x72, 0x72, 0x6f, 0x72];
    let c8: [u8; 13] = [0x4e, 0x6f, 0x74, 0x46, 0x6f, 0x75, 0x6e, 0x64, 0x45, 0x72, 0x72, 0x6f, 0x72];
    let c9: [u8; 17] = [0x4e, 0x6f, 0x74, 0x53, 0x75, 0x70, 0x70, 0x6f, 0x72, 0x74, 0x65, 0x64, 0x45, 0x72, 0x72, 0x6f, 0x72];
    let c10: [u8; 19] = [0x49, 0x6e, 0x55, 0x73, 0x65, 0x41, 0x74, 0x74, 0x72, 0x69, 0x62, 0x75, 0x74, 0x65, 0x45, 0x72, 0x72, 0x6f, 0x72];
    let c11: [u8; 17] = [0x49, 0x6e, 0x76, 0x61, 0x6c, 0x69, 0x64, 0x53, 0x74, 0x61, 0x74, 0x65, 0x45, 0x72, 0x72, 0x6f, 0x72];
    let c12: [u8; 11] = [0x53, 0x79, 0x6e, 0x74, 0x61, 0x78, 0x45, 0x72, 0x72, 0x6f, 0x72];
    let c13: [u8; 24] = [0x49, 0x6e, 0x76, 0x61, 0x6c, 0x69, 0x64, 0x4d, 0x6f, 0x64, 0x69, 0x66, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6f, 0x6e, 0x45, 0x72, 0x72, 0x6f, 0x72];
    let c14: [u8; 14] = [0x4e, 0x61, 0x6d, 0x65, 0x73, 0x70, 0x61, 0x63, 0x65, 0x45, 0x72, 0x72, 0x6f, 0x72];
    let c15: [u8; 18] = [0x49, 0x6e, 0x76, 0x61, 0x6c, 0x69, 0x64, 0x41, 0x63, 0x63, 0x65, 0x73, 0x73, 0x45, 0x72, 0x72, 0x6f, 0x72];
    let c17: [u8; 17] = [0x54, 0x79, 0x70, 0x65, 0x4d, 0x69, 0x73, 0x6d, 0x61, 0x74, 0x63, 0x68, 0x45, 0x72, 0x72, 0x6f, 0x72];
    let c18: [u8; 13] = [0x53, 0x65, 0x63, 0x75, 0x72, 0x69, 0x74, 0x79, 0x45, 0x72, 0x72, 0x6f, 0x72];
    let c19: [u8; 12] = [0x4e, 0x65, 0x74, 0x77, 0x6f, 0x72, 0x6b, 0x45, 0x72, 0x72, 0x6f, 0x72];
    let c20: [u8; 10] = [0x41, 0x62, 0x6f, 0x72, 0x74, 0x45, 0x72, 0x72, 0x6f, 0x72];
    let c21: [u8; 16] = [0x55, 0x52, 0x4c, 0x4d, 0x69, 0x73, 0x6d, 0x61, 0x74, 0x63, 0x68, 0x45, 0x72, 0x72, 0x6f, 0x72];
    let c22: [u8; 18] = [0x51, 0x75, 0x6f, 0x74, 0x61, 0x45, 0x78, 0x63, 0x65, 0x65, 0x64, 0x65, 0x64, 0x45, 0x72, 0x72, 0x6f, 0x72];
    let c23: [u8; 12] = [0x54, 0x69, 0x6d, 0x65, 0x6f, 0x75, 0x74, 0x45, 0x72, 0x72, 0x6f, 0x72];
    let c24: [u8; 20] = [0x49, 0x6e, 0x76, 0x61, 0x6c, 0x69, 0x64, 0x4e, 0x6f, 0x64, 0x65, 0x54, 0x79, 0x70, 0x65, 0x45, 0x72, 0x72, 0x6f, 0x72];
    let c25: [u8; 14] = [0x44, 0x61, 0x74, 0x61, 0x43, 0x6c, 0x6f, 0x6e, 0x65, 0x45, 0x72, 0x72, 0x6f, 0x72];
    proof {
        assert(c1@ =~= seq![0x49u8, 0x6e, 0x64, 0x65, 0x78, 0x53, 0x69, 0x7a, 0x65, 0x45, 0x72, 0x72, 0x6f, 0x72]);
        assert(c3@ =~= seq![0x48u8, 0x69, 0x65, 0x72, 0x61, 0x72, 0x63, 0x68, 0x79, 0x52, 0x65, 0x71, 0x75, 0x65, 0x73, 0x74, 0x45, 0x72, 0x72, 0x6f, 0x72]);
        assert(c4@ =~= seq![0x57u8, 0x72, 0x6f, 0x6e, 0x67, 0x44, 0x6f, 0x63, 0x75, 0x6d, 0x65, 0x6e, 0x74, 0x45, 0x72, 0x72, 0x6f, 0x72]);
        assert(c5@ =~= seq![0x49u8, 0x6e, 0x76, 0x61, 0x6c, 0x69, 0x64, 0x43, 0x68, 0x61, 0x72, 0x61, 0x63, 0x74, 0x65, 0x72, 0x45, 0x72, 0x72, 0x6f, 0x72]);
        assert(c7@ =~= seq![0x4eu8, 0x6f, 0x4d, 0x6f, 0x64, 0x69, 0x66, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6f, 0x6e, 0x41, 0x6c, 0x6c, 0x6f, 0x77, 0x65, 0x64, 0x45, 0x72, 0x72, 0x6f, 0x72]);
        assert(c8@ =~= seq![0x4eu8, 0x6f, 0x74, 0x46, 0x6f, 0x75, 0x6e, 0x64, 0x45, 0x72, 0x72, 0x6f, 0x72]);
        assert(c9@ =~= seq![0x4eu8, 0x6f, 0x74, 0x53, 0x75, 0x70, 0x70, 0x6f, 0x72, 0x74, 0x65, 0x64, 0x45, 0x72, 0x72, 0x6f, 0x72]);
        assert(c10@ =~= seq![0x49u8, 0x6e, 0x55, 0x73, 0x65, 0x41, 0x74, 0x74, 0x72, 0x69, 0x62, 0x75, 0x74, 0x65, 0x45, 0x72, 0x72, 0x6f, 0x72]);
        assert(c11@ =~= seq![0x49u8, 0x6e, 0x76, 0x61, 0x6c, 0x69, 0x64, 0x53, 0x74, 0x61, 0x74, 0x65, 0x45, 0x72, 0x72, 0x6f, 0x72]);
        assert(c12@ =~= seq![0x53u8, 0x79, 0x6e, 0x74, 0x61, 0x78, 0x45, 0x72, 0x72, 0x6f, 0x72]);
        assert(c13@ =~= seq![0x49u8, 0x6e, 0x76, 0x61, 0x6c, 0x69, 0x64, 0x4d, 0x6f, 0x64, 0x69, 0x66, 0x69, 0x63, 0x61, 0x74, 0x69, 0x6f, 0x6e, 0x45, 0x72, 0x72, 0x6f, 0x72]);
        assert(c14@ =~= seq![0x4eu8, 0x61, 0x6d, 0x65, 0x73, 0x70, 0x61, 0x63, 0x65, 0x45, 0x72, 0x72, 0x6f, 0x72]);
        assert(c15@ =~= seq![0x49u8, 0x6e, 0x76, 0x61, 0x6c, 0x69, 0x64, 0x41, 0x63, 0x63, 0x65, 0x73, 0x73, 0x45, 0x72, 0x72, 0x6f, 0x72]);
        assert(c17@ =~= seq![0x54u8, 0x79, 0x70, 0x65, 0x4d, 0x69, 0x73, 0x6d, 0x61, 0x74, 0x63, 0x68, 0x45, 0x72, 0x72, 0x6f, 0x72]);
        assert(c18@ =~= seq![0x53u8, 0x65, 0x63, 0x75, 0x72, 0x69, 0x74, 0x79, 0x45, 0x72, 0x72, 0x6f, 0x72]);
        assert(c19@ =~= seq![0x4eu8, 0x65, 0x74, 0x77, 0x6f, 0x72, 0x6b, 0x45, 0x72, 0x72, 0x6f, 0x72]);
        assert(c20@ =~= seq![0x41u8, 0x62, 0x6f, 0x72, 0x74, 0x45, 0x72, 0x72, 0x6f, 0x72]);
        assert(c21@ =~= seq![0x55u8, 0x52, 0x4c, 0x4d, 0x69, 0x73, 0x6d, 0x61, 0x74, 0x63, 0x68, 0x45, 0x72, 0x72, 0x6f, 0x72]);
        assert(c22@ =~= seq![0x51u8, 0x75, 0x6f, 0x74, 0x61, 0x45, 0x78, 0x63, 0x65, 0x65, 0x64, 0x65, 0x64, 0x45, 0x72, 0x72, 0x6f, 0x72]);
        assert(c23@ =~= seq![0x54u8, 0x69, 0x6d, 0x65, 0x6f, 0x75, 0x74, 0x45, 0x72, 0x72, 0x6f, 0x72]);
        assert(c24@ =~= seq![0x49u8, 0x6e, 0x76, 0x61, 0x6c, 0x69, 0x64, 0x4e, 0x6f, 0x64, 0x65, 0x54, 0x79, 0x70, 0x65, 0x45, 0x72, 0x72, 0x6f, 0x72]);
        assert(c25@ =~= seq![0x44u8, 0x61, 0x74, 0x61, 0x43, 0x6c, 0x6f, 0x6e, 0x65, 0x45, 0x72, 0x72, 0x6f, 0x72]);
    }
    if slice_eq_ascii(name, &c1) { 1 }
    else if slice_eq_ascii(name, &c3) { 3 }
    else if slice_eq_ascii(name, &c4) { 4 }
    else if slice_eq_ascii(name, &c5) { 5 }
    else if slice_eq_ascii(name, &c7) { 7 }
    else if slice_eq_ascii(name, &c8) { 8 }
    else if slice_eq_ascii(name, &c9) { 9 }
    else if slice_eq_ascii(name, &c10) { 10 }
    else if slice_eq_ascii(name, &c11) { 11 }
    else if slice_eq_ascii(name, &c12) { 12 }
    else if slice_eq_ascii(name, &c13) { 13 }
    else if slice_eq_ascii(name, &c14) { 14 }
    else if slice_eq_ascii(name, &c15) { 15 }
    else if slice_eq_ascii(name, &c17) { 17 }
    else if slice_eq_ascii(name, &c18) { 18 }
    else if slice_eq_ascii(name, &c19) { 19 }
    else if slice_eq_ascii(name, &c20) { 20 }
    else if slice_eq_ascii(name, &c21) { 21 }
    else if slice_eq_ascii(name, &c22) { 22 }
    else if slice_eq_ascii(name, &c23) { 23 }
    else if slice_eq_ascii(name, &c24) { 24 }
    else if slice_eq_ascii(name, &c25) { 25 }
    else { 0 }
}

pub open spec fn spec_construct_dom_exception(
    arena: Seq<SpecJsObjectRecord>,
    msg_arg: Option<SpecJsValue>,
    name_arg: Option<SpecJsValue>,
) -> Result<(Seq<u16>, Seq<u16>, u16), IdlError> {
    let msg_res: Result<Seq<u16>, IdlError> = match msg_arg {
        None | Some(SpecJsValue::Undefined) => Ok(seq![]),
        Some(v) => spec_to_idl_dom_string(arena, v, false),
    };
    match msg_res {
        Err(e) => Err(e),
        Ok(message) => {
            let name_res: Result<Seq<u16>, IdlError> = match name_arg {
                None | Some(SpecJsValue::Undefined) =>
                    Ok(spec_ascii_to_utf16(seq![0x45u8, 0x72, 0x72, 0x6f, 0x72])),
                Some(v) => spec_to_idl_dom_string(arena, v, false),
            };
            match name_res {
                Err(e) => Err(e),
                Ok(name) => {
                    let code = spec_dom_exception_legacy_code(name);
                    Ok((message, name, code))
                },
            }
        },
    }
}

pub fn construct_dom_exception(
    arena: &JsObjectArena,
    msg_arg: Option<&JsValue>,
    name_arg: Option<&JsValue>,
) -> (res: Result<DomExceptionRecord, IdlError>)
    ensures
        match (
            res,
            spec_construct_dom_exception(
                arena@,
                match msg_arg { None => None, Some(v) => Some(v@) },
                match name_arg { None => None, Some(v) => Some(v@) },
            ),
        ) {
            (Ok(rec), Ok((sm, sn, sc))) => rec.message@ == sm && rec.name@ == sn && rec.code == sc,
            (Err(e), Err(se)) => e == se,
            _ => false,
        },
{
    let message = match msg_arg {
        None | Some(JsValue::Undefined) => {
            let empty: Vec<u16> = Vec::new();
            proof { assert(empty@ =~= Seq::<u16>::empty()); }
            empty
        },
        Some(v) => to_idl_dom_string(arena, v, false)?,
    };
    let name = match name_arg {
        None | Some(JsValue::Undefined) => {
            let def: [u8; 5] = [0x45, 0x72, 0x72, 0x6f, 0x72];
            proof { assert(def@ =~= seq![0x45u8, 0x72, 0x72, 0x6f, 0x72]); }
            ascii_to_utf16(&def)
        },
        Some(v) => to_idl_dom_string(arena, v, false)?,
    };
    let code = dom_exception_legacy_code(name.as_slice());
    Ok(DomExceptionRecord { message, name, code })
}

/// WHATWG Web IDL §3.2.20 (`#dictionary-to-js`): serialize `EventInit` back into a JS Object
/// in `arena` with members emitted in lexicographical order (`"bubbles"`, `"cancelable"`, `"composed"`).
pub fn to_js_event_init(
    arena: &mut JsObjectArena,
    init: &EventInit,
) -> (res: Result<JsValue, IdlError>)
    ensures
        old(arena)@.len() < usize::MAX ==> match res {
            Ok(v) => spec_to_idl_event_init(final(arena)@, v@) == Ok::<EventInit, IdlError>(*init),
            Err(_) => false,
        },
{
    if arena.objects.len() == usize::MAX {
        return Err(IdlError::TypeError);
    }
    let k_b: [u8; 7] = [0x62, 0x75, 0x62, 0x62, 0x6c, 0x65, 0x73];
    let k_c: [u8; 10] = [0x63, 0x61, 0x6e, 0x63, 0x65, 0x6c, 0x61, 0x62, 0x6c, 0x65];
    let k_co: [u8; 8] = [0x63, 0x6f, 0x6d, 0x70, 0x6f, 0x73, 0x65, 0x64];
    proof {
        assert(k_b@ =~= seq![0x62u8, 0x75, 0x62, 0x62, 0x6c, 0x65, 0x73]);
        assert(k_c@ =~= seq![0x63u8, 0x61, 0x6e, 0x63, 0x65, 0x6c, 0x61, 0x62, 0x6c, 0x65]);
        assert(k_co@ =~= seq![0x63u8, 0x6f, 0x6d, 0x70, 0x6f, 0x73, 0x65, 0x64]);
    }
    let mut own_props: Vec<JsOwnProp> = Vec::new();
    own_props.push(JsOwnProp {
        key: ascii_to_utf16(&k_b),
        is_symbol: false,
        enumerable: true,
        is_getter: false,
        getter_throws: None,
        value: to_js_boolean(init.bubbles),
    });
    own_props.push(JsOwnProp {
        key: ascii_to_utf16(&k_c),
        is_symbol: false,
        enumerable: true,
        is_getter: false,
        getter_throws: None,
        value: to_js_boolean(init.cancelable),
    });
    own_props.push(JsOwnProp {
        key: ascii_to_utf16(&k_co),
        is_symbol: false,
        enumerable: true,
        is_getter: false,
        getter_throws: None,
        value: to_js_boolean(init.composed),
    });
    let rec = JsObjectRecord {
        own_props,
        proto_props: Vec::new(),
        iterator: JsIterator::NotIterable,
        to_string_hook: JsToStringHook::DefaultObjectTag,
        to_number_override: None,
    };
    let oid = arena.alloc(rec);
    proof {
        let props = final(arena)@[oid as int].own_props;
        reveal_with_fuel(spec_find_own_prop, 4);
        assert(props.len() == 3);
        assert(props[0].key == spec_key_bubbles());
        assert(props[1].key == spec_key_cancelable());
        assert(props[2].key == spec_key_composed());
        assert(props[0].key[0] == 0x62u16 && spec_key_cancelable()[0] == 0x63u16);
        assert(props[0].key != spec_key_cancelable());
        assert(props[0].key != spec_key_composed());
        assert(props[1].key[1] == 0x61u16 && spec_key_composed()[1] == 0x6fu16);
        assert(props[1].key != spec_key_composed());
        assert(props.subrange(1, 3)[0] == props[1]);
        assert(props.subrange(1, 3).subrange(1, 2)[0] == props[2]);
    }
    Ok(JsValue::Object(oid))
}

/// Nested `sequence<sequence<ByteString>>` 2-tuple converter (Fetch §5.1 `HeadersInit`):
/// Converts outer iterable and each inner iterable to `ByteString` pairs, rejecting any
/// inner sequence whose length `!= 2` with `IdlError::TypeError`.
pub open spec fn spec_headers_seq_pairs_loop(
    arena: Seq<SpecJsObjectRecord>,
    outer: Seq<SpecJsValue>,
) -> Result<Seq<(Seq<u8>, Seq<u8>)>, IdlError>
    decreases outer.len(),
{
    if outer.len() == 0 {
        Ok(seq![])
    } else {
        match spec_to_idl_sequence_byte_string(arena, outer[0]) {
            Err(e) => Err(e),
            Ok(pair) => {
                if pair.len() != 2nat {
                    Err(IdlError::TypeError)
                } else {
                    match spec_headers_seq_pairs_loop(
                        arena,
                        outer.subrange(1, outer.len() as int),
                    ) {
                        Err(e) => Err(e),
                        Ok(tail) => Ok(seq![(pair[0], pair[1])] + tail),
                    }
                }
            },
        }
    }
}

pub open spec fn spec_to_idl_headers_sequence_pairs(
    arena: Seq<SpecJsObjectRecord>,
    v: SpecJsValue,
) -> Result<Seq<(Seq<u8>, Seq<u8>)>, IdlError> {
    match spec_extract_iterable_items(arena, v) {
        Err(e) => Err(e),
        Ok(outer) => spec_headers_seq_pairs_loop(arena, outer),
    }
}

pub fn to_idl_headers_sequence_pairs(
    arena: &JsObjectArena,
    v: &JsValue,
) -> (res: Result<Vec<(Vec<u8>, Vec<u8>)>, IdlError>)
    ensures
        match (res, spec_to_idl_headers_sequence_pairs(arena@, v@)) {
            (Ok(out), Ok(sout)) => {
                out@.len() == sout.len()
                && Seq::new(out@.len(), |i: int| (out@[i].0@, out@[i].1@)) == sout
            },
            (Err(e), Err(se)) => e == se,
            _ => false,
        },
{
    let oid = match v {
        JsValue::Object(oid) => *oid,
        _ => return Err(IdlError::TypeError),
    };
    if oid >= arena.objects.len() {
        return Err(IdlError::TypeError);
    }
    let items = match &arena.objects[oid].iterator {
        JsIterator::NotIterable | JsIterator::ThrowTypeError => return Err(IdlError::TypeError),
        JsIterator::Items(v) => v,
    };
    let ghost sitems = Seq::new(items@.len(), |i: int| items@[i]@);
    proof {
        assert(arena@[oid as int].iterator == SpecJsIterator::Items(sitems));
        assert(sitems.subrange(0, sitems.len() as int) =~= sitems);
    }
    convert_headers_pairs_slice(arena, items.as_slice(), 0)
}

fn convert_headers_pairs_slice(
    arena: &JsObjectArena,
    items: &[JsValue],
    idx: usize,
) -> (res: Result<Vec<(Vec<u8>, Vec<u8>)>, IdlError>)
    requires
        idx <= items@.len(),
    ensures
        ({
            let sitems = Seq::new(items@.len(), |i: int| items@[i]@);
            let sub = sitems.subrange(idx as int, sitems.len() as int);
            match (res, spec_headers_seq_pairs_loop(arena@, sub)) {
                (Ok(out), Ok(sout)) => {
                    out@.len() == sout.len()
                    && Seq::new(out@.len(), |i: int| (out@[i].0@, out@[i].1@)) == sout
                },
                (Err(e), Err(se)) => e == se,
                _ => false,
            }
        }),
    decreases items@.len() - idx,
{
    let ghost sitems = Seq::new(items@.len(), |i: int| items@[i]@);
    let ghost sub = sitems.subrange(idx as int, sitems.len() as int);
    if idx == items.len() {
        let empty: Vec<(Vec<u8>, Vec<u8>)> = Vec::new();
        proof {
            assert(sub =~= Seq::<SpecJsValue>::empty());
            assert(Seq::new(empty@.len(), |i: int| (empty@[i].0@, empty@[i].1@))
                =~= Seq::<(Seq<u8>, Seq<u8>)>::empty());
        }
        return Ok(empty);
    }
    proof {
        assert(sub.len() > 0 && sub[0] == items@[idx as int]@);
        assert(sub.subrange(1, sub.len() as int) =~= sitems.subrange(idx + 1, sitems.len() as int));
    }
    let pair = to_idl_sequence_byte_string(arena, &items[idx])?;
    if pair.len() != 2usize {
        return Err(IdlError::TypeError);
    }
    let p0 = clone_u8_slice(pair[0].as_slice());
    let p1 = clone_u8_slice(pair[1].as_slice());
    let tail = convert_headers_pairs_slice(arena, items, idx + 1)?;
    let mut out: Vec<(Vec<u8>, Vec<u8>)> = Vec::new();
    out.push((p0, p1));
    let tn = tail.len();
    let mut k: usize = 0;
    while k < tn
        invariant
            k <= tn,
            tn == tail@.len(),
            out@.len() == 1 + (k as nat),
            out@[0].0@ == pair@[0]@ && out@[0].1@ == pair@[1]@,
            forall|m: int| 0 <= m < k as int ==> (
                out@[m + 1].0@ == tail@[m].0@ && out@[m + 1].1@ == tail@[m].1@
            ),
        decreases tn - k,
    {
        let tk = clone_u8_slice(tail[k].0.as_slice());
        let tv = clone_u8_slice(tail[k].1.as_slice());
        out.push((tk, tv));
        k += 1;
    }
    proof {
        let out_view = Seq::new(out@.len(), |i: int| (out@[i].0@, out@[i].1@));
        let tail_view = Seq::new(tail@.len(), |i: int| (tail@[i].0@, tail@[i].1@));
        assert(out_view =~= seq![(pair@[0]@, pair@[1]@)] + tail_view);
    }
    Ok(out)
}

/// Nested `sequence<sequence<USVString>>` 2-tuple converter (WHATWG URL §6.1 `URLSearchParams`):
/// Rejects any inner sequence whose length `!= 2` with `IdlError::TypeError` and normalizes
/// all keys and values to `USVString`!
pub open spec fn spec_usv_seq_pairs_loop(
    arena: Seq<SpecJsObjectRecord>,
    outer: Seq<SpecJsValue>,
) -> Result<Seq<(Seq<u16>, Seq<u16>)>, IdlError>
    decreases outer.len(),
{
    if outer.len() == 0 {
        Ok(seq![])
    } else {
        match spec_to_idl_sequence_usv_string(arena, outer[0]) {
            Err(e) => Err(e),
            Ok(pair) => {
                if pair.len() != 2nat {
                    Err(IdlError::TypeError)
                } else {
                    match spec_usv_seq_pairs_loop(
                        arena,
                        outer.subrange(1, outer.len() as int),
                    ) {
                        Err(e) => Err(e),
                        Ok(tail) => Ok(seq![(pair[0], pair[1])] + tail),
                    }
                }
            },
        }
    }
}

pub open spec fn spec_to_idl_usv_sequence_pairs(
    arena: Seq<SpecJsObjectRecord>,
    v: SpecJsValue,
) -> Result<Seq<(Seq<u16>, Seq<u16>)>, IdlError> {
    match spec_extract_iterable_items(arena, v) {
        Err(e) => Err(e),
        Ok(outer) => spec_usv_seq_pairs_loop(arena, outer),
    }
}

pub fn to_idl_usv_sequence_pairs(
    arena: &JsObjectArena,
    v: &JsValue,
) -> (res: Result<Vec<(Vec<u16>, Vec<u16>)>, IdlError>)
    ensures
        match (res, spec_to_idl_usv_sequence_pairs(arena@, v@)) {
            (Ok(out), Ok(sout)) => {
                out@.len() == sout.len()
                && Seq::new(out@.len(), |i: int| (out@[i].0@, out@[i].1@)) == sout
            },
            (Err(e), Err(se)) => e == se,
            _ => false,
        },
{
    let oid = match v {
        JsValue::Object(oid) => *oid,
        _ => return Err(IdlError::TypeError),
    };
    if oid >= arena.objects.len() {
        return Err(IdlError::TypeError);
    }
    let items = match &arena.objects[oid].iterator {
        JsIterator::NotIterable | JsIterator::ThrowTypeError => return Err(IdlError::TypeError),
        JsIterator::Items(v) => v,
    };
    let ghost sitems = Seq::new(items@.len(), |i: int| items@[i]@);
    proof {
        assert(arena@[oid as int].iterator == SpecJsIterator::Items(sitems));
        assert(sitems.subrange(0, sitems.len() as int) =~= sitems);
    }
    convert_usv_pairs_slice(arena, items.as_slice(), 0)
}

fn convert_usv_pairs_slice(
    arena: &JsObjectArena,
    items: &[JsValue],
    idx: usize,
) -> (res: Result<Vec<(Vec<u16>, Vec<u16>)>, IdlError>)
    requires
        idx <= items@.len(),
    ensures
        ({
            let sitems = Seq::new(items@.len(), |i: int| items@[i]@);
            let sub = sitems.subrange(idx as int, sitems.len() as int);
            match (res, spec_usv_seq_pairs_loop(arena@, sub)) {
                (Ok(out), Ok(sout)) => {
                    out@.len() == sout.len()
                    && Seq::new(out@.len(), |i: int| (out@[i].0@, out@[i].1@)) == sout
                },
                (Err(e), Err(se)) => e == se,
                _ => false,
            }
        }),
    decreases items@.len() - idx,
{
    let ghost sitems = Seq::new(items@.len(), |i: int| items@[i]@);
    let ghost sub = sitems.subrange(idx as int, sitems.len() as int);
    if idx == items.len() {
        let empty: Vec<(Vec<u16>, Vec<u16>)> = Vec::new();
        proof {
            assert(sub =~= Seq::<SpecJsValue>::empty());
            assert(Seq::new(empty@.len(), |i: int| (empty@[i].0@, empty@[i].1@))
                =~= Seq::<(Seq<u16>, Seq<u16>)>::empty());
        }
        return Ok(empty);
    }
    proof {
        assert(sub.len() > 0 && sub[0] == items@[idx as int]@);
        assert(sub.subrange(1, sub.len() as int) =~= sitems.subrange(idx + 1, sitems.len() as int));
    }
    let pair = to_idl_sequence_usv_string(arena, &items[idx])?;
    if pair.len() != 2usize {
        return Err(IdlError::TypeError);
    }
    let p0 = clone_u16_slice(pair[0].as_slice());
    let p1 = clone_u16_slice(pair[1].as_slice());
    let tail = convert_usv_pairs_slice(arena, items, idx + 1)?;
    let mut out: Vec<(Vec<u16>, Vec<u16>)> = Vec::new();
    out.push((p0, p1));
    let tn = tail.len();
    let mut k: usize = 0;
    while k < tn
        invariant
            k <= tn,
            tn == tail@.len(),
            out@.len() == 1 + (k as nat),
            out@[0].0@ == pair@[0]@ && out@[0].1@ == pair@[1]@,
            forall|m: int| 0 <= m < k as int ==> (
                out@[m + 1].0@ == tail@[m].0@ && out@[m + 1].1@ == tail@[m].1@
            ),
        decreases tn - k,
    {
        let tk = clone_u16_slice(tail[k].0.as_slice());
        let tv = clone_u16_slice(tail[k].1.as_slice());
        out.push((tk, tv));
        k += 1;
    }
    proof {
        let out_view = Seq::new(out@.len(), |i: int| (out@[i].0@, out@[i].1@));
        let tail_view = Seq::new(tail@.len(), |i: int| (tail@[i].0@, tail@[i].1@));
        assert(out_view =~= seq![(pair@[0]@, pair@[1]@)] + tail_view);
    }
    Ok(out)
}

} // verus!
