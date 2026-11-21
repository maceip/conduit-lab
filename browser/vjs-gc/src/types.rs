//! Shared ECMAScript runtime value representation, `SameValue` (§7.2.10), verified string atom
//! pool (`JSAtom`), and completion error types for `vjs_gc`.
use vstd::prelude::*;

verus! {

pub type ObjId = usize;
pub type PromiseId = usize;
pub type GenId = usize;
pub type AsyncId = usize;
pub type AtomId = u32;
pub type SymId = u32;

/// ECMAScript language value (§6.1) with interned string atoms (`AtomId`) and IEEE-754 `f64` bit
/// representation so `SameValue` (§7.2.10) accurately distinguishes `+0.0` vs `-0.0` and equates `NaN`s.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum JsVal {
    Undefined,
    Null,
    Bool(bool),
    Int(i64),
    FloatBits(u64),
    Str(AtomId),
    Symbol(SymId),
    Object(ObjId),
    Promise(PromiseId),
}

/// Abrupt completion / engine error reason.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum JsError {
    TypeError,
    RangeError,
    QuotaExceeded,
    Thrown(JsVal),
}

/// IEEE-754 binary64 NaN check on raw bits: exponent all 1s (`0x7ff`) and non-zero significand.
pub open spec fn spec_is_nan_bits(bits: u64) -> bool {
    (bits & 0x7ff0_0000_0000_0000u64) == 0x7ff0_0000_0000_0000u64
        && (bits & 0x000f_ffff_ffff_ffffu64) != 0u64
}

pub fn is_nan_bits(bits: u64) -> (r: bool)
    ensures
        r == spec_is_nan_bits(bits),
{
    (bits & 0x7ff0_0000_0000_0000u64) == 0x7ff0_0000_0000_0000u64
        && (bits & 0x000f_ffff_ffff_ffffu64) != 0u64
}

/// ECMA-262 §7.2.10 `SameValue(x, y)`:
/// - For `FloatBits`, two NaNs are `SameValue`-equal even with distinct payloads, while `+0.0`
///   (`0x0000_0000_0000_0000`) and `-0.0` (`0x8000_0000_0000_0000`) are distinct (differing sign bit).
/// - All other variants compare structurally.
pub open spec fn spec_same_value(x: JsVal, y: JsVal) -> bool {
    match (x, y) {
        (JsVal::FloatBits(bx), JsVal::FloatBits(by)) => {
            if spec_is_nan_bits(bx) && spec_is_nan_bits(by) {
                true
            } else {
                bx == by
            }
        },
        _ => x == y,
    }
}

pub fn same_value(x: JsVal, y: JsVal) -> (r: bool)
    ensures
        r == spec_same_value(x, y),
{
    match (x, y) {
        (JsVal::Undefined, JsVal::Undefined) => true,
        (JsVal::Null, JsVal::Null) => true,
        (JsVal::Bool(a), JsVal::Bool(b)) => a == b,
        (JsVal::Int(a), JsVal::Int(b)) => a == b,
        (JsVal::FloatBits(bx), JsVal::FloatBits(by)) => {
            if is_nan_bits(bx) && is_nan_bits(by) {
                true
            } else {
                bx == by
            }
        },
        (JsVal::Str(a), JsVal::Str(b)) => a == b,
        (JsVal::Symbol(a), JsVal::Symbol(b)) => a == b,
        (JsVal::Object(a), JsVal::Object(b)) => a == b,
        (JsVal::Promise(a), JsVal::Promise(b)) => a == b,
        _ => false,
    }
}

/// `SameValue` is an equivalence relation (reflexive, symmetric, transitive), and distinguishes `+0.0` from `-0.0`.
pub proof fn lemma_same_value_equivalence(x: JsVal, y: JsVal, z: JsVal)
    ensures
        spec_same_value(x, x),
        spec_same_value(x, y) == spec_same_value(y, x),
        (spec_same_value(x, y) && spec_same_value(y, z)) ==> spec_same_value(x, z),
        !spec_same_value(JsVal::FloatBits(0x0000_0000_0000_0000u64), JsVal::FloatBits(0x8000_0000_0000_0000u64)),
        spec_same_value(JsVal::FloatBits(0x7ff8_0000_0000_0000u64), JsVal::FloatBits(0x7ff8_0000_0000_0001u64)),
{
    assert((0x0000_0000_0000_0000u64 & 0x7ff0_0000_0000_0000u64) == 0u64) by (bit_vector);
    assert((0x8000_0000_0000_0000u64 & 0x7ff0_0000_0000_0000u64) == 0u64) by (bit_vector);
    assert((0x7ff8_0000_0000_0000u64 & 0x7ff0_0000_0000_0000u64) == 0x7ff0_0000_0000_0000u64) by (bit_vector);
    assert((0x7ff8_0000_0000_0000u64 & 0x000f_ffff_ffff_ffffu64) != 0u64) by (bit_vector);
    assert((0x7ff8_0000_0000_0001u64 & 0x7ff0_0000_0000_0000u64) == 0x7ff0_0000_0000_0000u64) by (bit_vector);
    assert((0x7ff8_0000_0000_0001u64 & 0x000f_ffff_ffff_ffffu64) != 0u64) by (bit_vector);
}

/// Verified byte-slice equality helper (`decreases a.len() - i`).
pub fn bytes_eq(a: &[u8], b: &[u8]) -> (eq: bool)
    ensures
        eq == (a@ == b@),
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

pub fn clone_bytes(s: &[u8]) -> (out: Vec<u8>)
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
            out@.len() == i as int,
            forall|k: int| 0 <= k < i as int ==> out@[k] == s@[k],
        decreases n - i,
    {
        out.push(s[i]);
        i += 1;
    }
    proof {
        assert(out@ =~= s@);
    }
    out
}

/// Verified string atom table (`AtomId -> Seq<u8>`) with deduplicating `intern`.
pub struct AtomTable {
    pub entries: Vec<Vec<u8>>,
}

impl AtomTable {
    pub open spec fn wf(&self) -> bool {
        self.entries@.len() <= u32::MAX as int
            && forall|i: int, j: int|
                0 <= i < j < self.entries@.len() ==> self.entries@[i]@ != self.entries@[j]@
    }

    pub open spec fn spec_get(&self, id: AtomId) -> Option<Seq<u8>> {
        if (id as int) < self.entries@.len() {
            Some(self.entries@[id as int]@)
        } else {
            None
        }
    }

    pub fn new() -> (t: Self)
        ensures
            t.wf(),
            t.entries@.len() == 0,
    {
        AtomTable { entries: Vec::new() }
    }

    pub fn intern(&mut self, bytes: &[u8]) -> (res: Result<AtomId, JsError>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            match res {
                Ok(id) => {
                    final(self).spec_get(id) == Some(bytes@)
                    && forall|old_id: AtomId|
                        (old_id as int) < old(self).entries@.len()
                            ==> final(self).spec_get(old_id) == old(self).spec_get(old_id)
                },
                Err(e) => e == JsError::QuotaExceeded && final(self).entries@ == old(self).entries@,
            },
    {
        let n = self.entries.len();
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                n == self.entries@.len(),
                self.wf(),
                forall|k: int| 0 <= k < i as int ==> self.entries@[k]@ != bytes@,
            decreases n - i,
        {
            if bytes_eq(self.entries[i].as_slice(), bytes) {
                return Ok(i as u32);
            }
            i += 1;
        }
        if n >= u32::MAX as usize {
            return Err(JsError::QuotaExceeded);
        }
        let owned = clone_bytes(bytes);
        self.entries.push(owned);
        Ok(n as u32)
    }

    pub fn get(&self, id: AtomId) -> (res: Option<&Vec<u8>>)
        ensures
            match res {
                Some(v) => self.spec_get(id) == Some(v@),
                None => self.spec_get(id) is None,
            },
    {
        if (id as usize) < self.entries.len() {
            Some(&self.entries[id as usize])
        } else {
            None
        }
    }
}

} // verus!
