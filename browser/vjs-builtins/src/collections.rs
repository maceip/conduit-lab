//! ECMA-262 §24.1 `Map` and §24.2 `Set` built-in collections with `SameValueZero` key
//! equality (§7.2.11), `CanonicalizeKeyedCollectionKey` (§24.1.1.2), and deterministic
//! insertion-order preservation.
use vstd::prelude::*;

verus! {

/// IEEE-754 binary64 `+0.0` bit pattern.
pub const POS_ZERO_BITS: u64 = 0x0000_0000_0000_0000u64;
/// IEEE-754 binary64 `-0.0` bit pattern.
pub const NEG_ZERO_BITS: u64 = 0x8000_0000_0000_0000u64;
/// IEEE-754 binary64 `+Infinity` bit pattern.
pub const POS_INF_BITS: u64 = 0x7FF0_0000_0000_0000u64;
/// IEEE-754 binary64 `-Infinity` bit pattern.
pub const NEG_INF_BITS: u64 = 0xFFF0_0000_0000_0000u64;
/// Canonical quiet `NaN` bit pattern.
pub const CANONICAL_NAN_BITS: u64 = 0x7FF8_0000_0000_0000u64;

/// Spec-level ECMAScript value/key representation for collections and array search ops.
pub enum SpecJsKey {
    Undefined,
    Null,
    Bool(bool),
    NumberBits(u64),
    Str(Seq<u16>),
    Symbol(u64),
    ObjectRef(u64),
}

/// Exec-level ECMAScript value/key representation for collections and array search ops.
#[derive(PartialEq, Eq, Debug)]
pub enum JsKey {
    Undefined,
    Null,
    Bool(bool),
    NumberBits(u64),
    Str(Vec<u16>),
    Symbol(u64),
    ObjectRef(u64),
}

impl View for JsKey {
    type V = SpecJsKey;

    open spec fn view(&self) -> SpecJsKey {
        match self {
            JsKey::Undefined => SpecJsKey::Undefined,
            JsKey::Null => SpecJsKey::Null,
            JsKey::Bool(b) => SpecJsKey::Bool(*b),
            JsKey::NumberBits(bits) => SpecJsKey::NumberBits(*bits),
            JsKey::Str(s) => SpecJsKey::Str(s@),
            JsKey::Symbol(id) => SpecJsKey::Symbol(*id),
            JsKey::ObjectRef(id) => SpecJsKey::ObjectRef(*id),
        }
    }
}

/// Verified clone of a UTF-16 code unit buffer.
pub fn clone_u16_slice(s: &[u16]) -> (out: Vec<u16>)
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

/// Verified clone for `JsKey` preserving `View`.
pub fn clone_js_key(k: &JsKey) -> (out: JsKey)
    ensures
        out@ == k@,
{
    match k {
        JsKey::Undefined => JsKey::Undefined,
        JsKey::Null => JsKey::Null,
        JsKey::Bool(b) => JsKey::Bool(*b),
        JsKey::NumberBits(bits) => JsKey::NumberBits(*bits),
        JsKey::Str(s) => JsKey::Str(clone_u16_slice(s.as_slice())),
        JsKey::Symbol(id) => JsKey::Symbol(*id),
        JsKey::ObjectRef(id) => JsKey::ObjectRef(*id),
    }
}

/// Verified exact equality on UTF-16 slices.
pub fn eq_u16_slice(a: &[u16], b: &[u16]) -> (res: bool)
    ensures
        res == (a@ == b@),
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
            proof {
                assert(a@[i as int] != b@[i as int]);
            }
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
// Spec: IEEE-754 bit predicates, SameValue, SameValueZero, IsStrictlyEqual
// ---------------------------------------------------------------------------------------

/// True iff `bits` encodes `+0.0` or `-0.0` in IEEE-754 binary64.
pub open spec fn spec_is_zero_bits(bits: u64) -> bool {
    bits == POS_ZERO_BITS || bits == NEG_ZERO_BITS
}

/// True iff `bits` encodes any quiet or signaling IEEE-754 binary64 `NaN`
/// (exponent all 1s `0x7FF`, non-zero 52-bit significand, either sign bit).
pub open spec fn spec_is_nan_bits(bits: u64) -> bool {
    (bits > POS_INF_BITS && bits <= 0x7FFF_FFFF_FFFF_FFFFu64) || bits > NEG_INF_BITS
}

/// ECMA-262 §6.1.6.1.14 `Number::sameValue ( x, y )`.
pub open spec fn spec_number_same_value(x: u64, y: u64) -> bool {
    if spec_is_nan_bits(x) || spec_is_nan_bits(y) {
        spec_is_nan_bits(x) && spec_is_nan_bits(y)
    } else {
        x == y
    }
}

/// ECMA-262 §6.1.6.1.15 `Number::sameValueZero ( x, y )`:
/// `-0.0` equals `+0.0`, and `NaN` equals `NaN`.
pub open spec fn spec_number_same_value_zero(x: u64, y: u64) -> bool {
    if spec_is_nan_bits(x) || spec_is_nan_bits(y) {
        spec_is_nan_bits(x) && spec_is_nan_bits(y)
    } else if spec_is_zero_bits(x) && spec_is_zero_bits(y) {
        true
    } else {
        x == y
    }
}

/// ECMA-262 §6.1.6.1.13 `Number::equal ( x, y )` (used by `IsStrictlyEqual` `===`):
/// `-0.0 === +0.0` is true, while `NaN === NaN` is false.
pub open spec fn spec_number_strict_equal(x: u64, y: u64) -> bool {
    if spec_is_nan_bits(x) || spec_is_nan_bits(y) {
        false
    } else if spec_is_zero_bits(x) && spec_is_zero_bits(y) {
        true
    } else {
        x == y
    }
}

/// ECMA-262 §7.2.11 `SameValueZero ( x, y )`.
pub open spec fn spec_same_value_zero(x: SpecJsKey, y: SpecJsKey) -> bool {
    match (x, y) {
        (SpecJsKey::Undefined, SpecJsKey::Undefined) => true,
        (SpecJsKey::Null, SpecJsKey::Null) => true,
        (SpecJsKey::Bool(a), SpecJsKey::Bool(b)) => a == b,
        (SpecJsKey::NumberBits(a), SpecJsKey::NumberBits(b)) => spec_number_same_value_zero(a, b),
        (SpecJsKey::Str(a), SpecJsKey::Str(b)) => a == b,
        (SpecJsKey::Symbol(a), SpecJsKey::Symbol(b)) => a == b,
        (SpecJsKey::ObjectRef(a), SpecJsKey::ObjectRef(b)) => a == b,
        _ => false,
    }
}

/// ECMA-262 §7.2.14 `IsStrictlyEqual ( x, y )` (`===`).
pub open spec fn spec_is_strictly_equal(x: SpecJsKey, y: SpecJsKey) -> bool {
    match (x, y) {
        (SpecJsKey::Undefined, SpecJsKey::Undefined) => true,
        (SpecJsKey::Null, SpecJsKey::Null) => true,
        (SpecJsKey::Bool(a), SpecJsKey::Bool(b)) => a == b,
        (SpecJsKey::NumberBits(a), SpecJsKey::NumberBits(b)) => spec_number_strict_equal(a, b),
        (SpecJsKey::Str(a), SpecJsKey::Str(b)) => a == b,
        (SpecJsKey::Symbol(a), SpecJsKey::Symbol(b)) => a == b,
        (SpecJsKey::ObjectRef(a), SpecJsKey::ObjectRef(b)) => a == b,
        _ => false,
    }
}

/// ECMA-262 §24.1.1.2 `CanonicalizeKeyedCollectionKey ( key )`:
/// if `key` is `-0`, return `+0`; otherwise return `key`.
pub open spec fn spec_canonicalize_key(k: SpecJsKey) -> SpecJsKey {
    match k {
        SpecJsKey::NumberBits(bits) => {
            if bits == NEG_ZERO_BITS {
                SpecJsKey::NumberBits(POS_ZERO_BITS)
            } else {
                SpecJsKey::NumberBits(bits)
            }
        },
        _ => k,
    }
}

// ---------------------------------------------------------------------------------------
// Spec: Map and Set abstract state & transitions (§24.1 / §24.2)
// ---------------------------------------------------------------------------------------

/// First index `i` in `entries` whose key satisfies `SameValueZero(entries[i].0, k)`.
pub open spec fn spec_map_find_index(entries: Seq<(SpecJsKey, SpecJsKey)>, k: SpecJsKey) -> Option<nat>
    decreases entries.len(),
{
    if entries.len() == 0 {
        None
    } else if spec_same_value_zero(entries[0].0, k) {
        Some(0)
    } else {
        match spec_map_find_index(entries.subrange(1, entries.len() as int), k) {
            Some(idx) => Some(idx + 1),
            None => None,
        }
    }
}

/// Well-formedness invariant for `JsMap`:
/// 1. Every stored key is canonicalized (`-0.0` never stored directly),
/// 2. No two distinct indices have `SameValueZero`-equal keys.
pub open spec fn spec_map_wf(entries: Seq<(SpecJsKey, SpecJsKey)>) -> bool {
    (forall|i: int| 0 <= i < entries.len() ==> #[trigger] entries[i].0 != SpecJsKey::NumberBits(NEG_ZERO_BITS))
    && (forall|i: int, j: int|
        0 <= i < j < entries.len() ==> !spec_same_value_zero(#[trigger] entries[i].0, #[trigger] entries[j].0))
}

/// ECMA-262 §24.1.3.6 `Map.prototype.get ( key )`.
pub open spec fn spec_map_get(entries: Seq<(SpecJsKey, SpecJsKey)>, k: SpecJsKey) -> Option<SpecJsKey> {
    match spec_map_find_index(entries, k) {
        Some(idx) => Some(entries[idx as int].1),
        None => None,
    }
}

/// ECMA-262 §24.1.3.7 `Map.prototype.has ( key )`.
pub open spec fn spec_map_has(entries: Seq<(SpecJsKey, SpecJsKey)>, k: SpecJsKey) -> bool {
    spec_map_find_index(entries, k).is_some()
}

/// ECMA-262 §24.1.3.9 `Map.prototype.set ( key, value )`:
/// updates value in-place if key exists (preserving existing key position),
/// otherwise appends `(CanonicalizeKeyedCollectionKey(key), value)` at the end.
pub open spec fn spec_map_set(
    entries: Seq<(SpecJsKey, SpecJsKey)>,
    k: SpecJsKey,
    v: SpecJsKey,
) -> Seq<(SpecJsKey, SpecJsKey)> {
    match spec_map_find_index(entries, k) {
        Some(idx) => entries.update(idx as int, (entries[idx as int].0, v)),
        None => entries.push((spec_canonicalize_key(k), v)),
    }
}

/// ECMA-262 §24.1.3.3 `Map.prototype.delete ( key )`:
/// removes the matching entry while preserving relative insertion order of remaining entries.
pub open spec fn spec_map_delete(
    entries: Seq<(SpecJsKey, SpecJsKey)>,
    k: SpecJsKey,
) -> (Seq<(SpecJsKey, SpecJsKey)>, bool) {
    match spec_map_find_index(entries, k) {
        Some(idx) => (
            entries.subrange(0, idx as int) + entries.subrange(idx as int + 1, entries.len() as int),
            true,
        ),
        None => (entries, false),
    }
}

/// First index `i` in `items` satisfying `SameValueZero(items[i], v)`.
pub open spec fn spec_set_find_index(items: Seq<SpecJsKey>, v: SpecJsKey) -> Option<nat>
    decreases items.len(),
{
    if items.len() == 0 {
        None
    } else if spec_same_value_zero(items[0], v) {
        Some(0)
    } else {
        match spec_set_find_index(items.subrange(1, items.len() as int), v) {
            Some(idx) => Some(idx + 1),
            None => None,
        }
    }
}

/// Well-formedness invariant for `JsSet`.
pub open spec fn spec_set_wf(items: Seq<SpecJsKey>) -> bool {
    (forall|i: int| 0 <= i < items.len() ==> #[trigger] items[i] != SpecJsKey::NumberBits(NEG_ZERO_BITS))
    && (forall|i: int, j: int|
        0 <= i < j < items.len() ==> !spec_same_value_zero(#[trigger] items[i], #[trigger] items[j]))
}

/// ECMA-262 §24.2.3.6 `Set.prototype.has ( value )`.
pub open spec fn spec_set_has(items: Seq<SpecJsKey>, v: SpecJsKey) -> bool {
    spec_set_find_index(items, v).is_some()
}

/// ECMA-262 §24.2.3.1 `Set.prototype.add ( value )`.
pub open spec fn spec_set_add(items: Seq<SpecJsKey>, v: SpecJsKey) -> Seq<SpecJsKey> {
    match spec_set_find_index(items, v) {
        Some(_) => items,
        None => items.push(spec_canonicalize_key(v)),
    }
}

/// ECMA-262 §24.2.3.4 `Set.prototype.delete ( value )`.
pub open spec fn spec_set_delete(items: Seq<SpecJsKey>, v: SpecJsKey) -> (Seq<SpecJsKey>, bool) {
    match spec_set_find_index(items, v) {
        Some(idx) => (
            items.subrange(0, idx as int) + items.subrange(idx as int + 1, items.len() as int),
            true,
        ),
        None => (items, false),
    }
}

// ---------------------------------------------------------------------------------------
// Proofs: SameValueZero algebra, wf preservation, and insertion-order theorems
// ---------------------------------------------------------------------------------------

/// `SameValueZero` is an equivalence relation (reflexive, symmetric, transitive).
pub proof fn lemma_same_value_zero_equivalence(a: SpecJsKey, b: SpecJsKey, c: SpecJsKey)
    ensures
        spec_same_value_zero(a, a),
        spec_same_value_zero(a, b) == spec_same_value_zero(b, a),
        (spec_same_value_zero(a, b) && spec_same_value_zero(b, c)) ==> spec_same_value_zero(a, c),
{
}

/// `-0.0` and `+0.0` are equal under `SameValueZero` and `IsStrictlyEqual`, but distinct under `SameValue`.
pub proof fn lemma_signed_zero_equality_laws()
    ensures
        spec_same_value_zero(SpecJsKey::NumberBits(NEG_ZERO_BITS), SpecJsKey::NumberBits(POS_ZERO_BITS)),
        spec_is_strictly_equal(SpecJsKey::NumberBits(NEG_ZERO_BITS), SpecJsKey::NumberBits(POS_ZERO_BITS)),
        !spec_number_same_value(NEG_ZERO_BITS, POS_ZERO_BITS),
        spec_canonicalize_key(SpecJsKey::NumberBits(NEG_ZERO_BITS)) == SpecJsKey::NumberBits(POS_ZERO_BITS),
{
}

/// Any two IEEE-754 `NaN` encodings are equal under `SameValueZero`, yet unequal under `IsStrictlyEqual`.
pub proof fn lemma_nan_equality_laws(nan1: u64, nan2: u64)
    requires
        spec_is_nan_bits(nan1),
        spec_is_nan_bits(nan2),
    ensures
        spec_same_value_zero(SpecJsKey::NumberBits(nan1), SpecJsKey::NumberBits(nan2)),
        !spec_is_strictly_equal(SpecJsKey::NumberBits(nan1), SpecJsKey::NumberBits(nan2)),
{
}

/// Canonicalization preserves `SameValueZero` equivalence and eliminates `-0.0`.
pub proof fn lemma_canonicalize_key_properties(k: SpecJsKey)
    ensures
        spec_same_value_zero(spec_canonicalize_key(k), k),
        spec_canonicalize_key(k) != SpecJsKey::NumberBits(NEG_ZERO_BITS),
{
}

/// Soundness and completeness of `spec_map_find_index`:
/// returns `Some(idx)` iff `idx` is the least index matching `k` under `SameValueZero`.
pub proof fn lemma_map_find_index_spec(entries: Seq<(SpecJsKey, SpecJsKey)>, k: SpecJsKey)
    ensures
        match spec_map_find_index(entries, k) {
            Some(idx) => {
                &&& (idx as int) < entries.len()
                &&& spec_same_value_zero(entries[idx as int].0, k)
                &&& forall|j: int| 0 <= j < idx as int ==> !spec_same_value_zero(#[trigger] entries[j].0, k)
            },
            None => forall|j: int| 0 <= j < entries.len() ==> !spec_same_value_zero(#[trigger] entries[j].0, k),
        },
    decreases entries.len(),
{
    if entries.len() > 0 && !spec_same_value_zero(entries[0].0, k) {
        let tail = entries.subrange(1, entries.len() as int);
        lemma_map_find_index_spec(tail, k);
        match spec_map_find_index(tail, k) {
            Some(idx) => {
                assert(tail[idx as int] == entries[idx as int + 1]);
                assert forall|j: int| 0 <= j < idx as int + 1 implies !spec_same_value_zero(
                    #[trigger] entries[j].0,
                    k,
                ) by {
                    if j > 0 {
                        assert(entries[j] == tail[j - 1]);
                    }
                }
            },
            None => {
                assert forall|j: int| 0 <= j < entries.len() implies !spec_same_value_zero(
                    #[trigger] entries[j].0,
                    k,
                ) by {
                    if j > 0 {
                        assert(entries[j] == tail[j - 1]);
                    }
                }
            },
        }
    }
}

/// Under `spec_map_wf`, if `entries[idx]` matches `k`, `spec_map_find_index` returns `Some(idx)`.
pub proof fn lemma_map_find_unique_under_wf(
    entries: Seq<(SpecJsKey, SpecJsKey)>,
    k: SpecJsKey,
    idx: nat,
)
    requires
        spec_map_wf(entries),
        (idx as int) < entries.len(),
        spec_same_value_zero(entries[idx as int].0, k),
    ensures
        spec_map_find_index(entries, k) == Some(idx),
{
    lemma_map_find_index_spec(entries, k);
    match spec_map_find_index(entries, k) {
        Some(found) => {
            if found < idx {
                lemma_same_value_zero_equivalence(entries[found as int].0, k, entries[idx as int].0);
                assert(spec_same_value_zero(entries[found as int].0, entries[idx as int].0));
            } else if found > idx {
                assert(!spec_same_value_zero(entries[idx as int].0, k));
            }
        },
        None => {
            assert(!spec_same_value_zero(entries[idx as int].0, k));
        },
    }
}

/// `spec_map_set` preserves `spec_map_wf`.
pub proof fn lemma_map_set_preserves_wf(
    entries: Seq<(SpecJsKey, SpecJsKey)>,
    k: SpecJsKey,
    v: SpecJsKey,
)
    requires
        spec_map_wf(entries),
    ensures
        spec_map_wf(spec_map_set(entries, k, v)),
{
    lemma_map_find_index_spec(entries, k);
    let next = spec_map_set(entries, k, v);
    match spec_map_find_index(entries, k) {
        Some(idx) => {
            assert forall|i: int, j: int| 0 <= i < j < next.len() implies !spec_same_value_zero(
                #[trigger] next[i].0,
                #[trigger] next[j].0,
            ) by {
                assert(next[i].0 == entries[i].0);
                assert(next[j].0 == entries[j].0);
            }
        },
        None => {
            lemma_canonicalize_key_properties(k);
            assert forall|i: int, j: int| 0 <= i < j < next.len() implies !spec_same_value_zero(
                #[trigger] next[i].0,
                #[trigger] next[j].0,
            ) by {
                if j < entries.len() {
                    assert(next[i].0 == entries[i].0);
                    assert(next[j].0 == entries[j].0);
                } else {
                    assert(next[i].0 == entries[i].0);
                    assert(next[j].0 == spec_canonicalize_key(k));
                    if spec_same_value_zero(entries[i].0, spec_canonicalize_key(k)) {
                        lemma_same_value_zero_equivalence(entries[i].0, spec_canonicalize_key(k), k);
                        assert(spec_same_value_zero(entries[i].0, k));
                    }
                }
            }
        },
    }
}

/// `spec_map_delete` preserves `spec_map_wf`.
pub proof fn lemma_map_delete_preserves_wf(entries: Seq<(SpecJsKey, SpecJsKey)>, k: SpecJsKey)
    requires
        spec_map_wf(entries),
    ensures
        spec_map_wf(spec_map_delete(entries, k).0),
        !spec_map_has(spec_map_delete(entries, k).0, k),
{
    lemma_map_find_index_spec(entries, k);
    let (next, removed) = spec_map_delete(entries, k);
    if removed {
        let idx = spec_map_find_index(entries, k).unwrap() as int;
        assert forall|i: int| 0 <= i < next.len() implies #[trigger] next[i].0 != SpecJsKey::NumberBits(
            NEG_ZERO_BITS,
        ) by {
            if i < idx {
                assert(next[i] == entries[i]);
            } else {
                assert(next[i] == entries[i + 1]);
            }
        }
        assert forall|i: int, j: int| 0 <= i < j < next.len() implies !spec_same_value_zero(
            #[trigger] next[i].0,
            #[trigger] next[j].0,
        ) by {
            let oi = if i < idx { i } else { i + 1 };
            let oj = if j < idx { j } else { j + 1 };
            assert(next[i] == entries[oi]);
            assert(next[j] == entries[oj]);
        }
        lemma_map_find_index_spec(next, k);
        if let Some(f) = spec_map_find_index(next, k) {
            let fi = f as int;
            let orig = if fi < idx { fi } else { fi + 1 };
            assert(next[fi] == entries[orig]);
            if orig > idx {
                lemma_same_value_zero_equivalence(entries[idx].0, k, entries[orig].0);
                assert(spec_same_value_zero(entries[idx].0, entries[orig].0));
            }
        }
    } else {
        lemma_map_find_index_spec(next, k);
    }
}

/// Insertion-order theorem 1 (`Map.prototype.set` in-place update):
/// Setting an existing key updates its value in place without moving any key's index.
pub proof fn lemma_map_set_existing_preserves_order(
    entries: Seq<(SpecJsKey, SpecJsKey)>,
    k: SpecJsKey,
    v: SpecJsKey,
    idx: nat,
)
    requires
        spec_map_wf(entries),
        (idx as int) < entries.len(),
        spec_same_value_zero(entries[idx as int].0, k),
    ensures
        spec_map_set(entries, k, v).len() == entries.len(),
        spec_map_set(entries, k, v)[idx as int] == (entries[idx as int].0, v),
        forall|j: int|
            0 <= j < entries.len() && j != idx as int
                ==> #[trigger] spec_map_set(entries, k, v)[j] == entries[j],
{
    lemma_map_find_unique_under_wf(entries, k, idx);
}

/// Insertion-order theorem 2 (`Map.prototype.delete` + `Map.prototype.set` moves to end):
/// Deleting an existing key at `idx` and re-inserting it places it at the final slot `len - 1`.
pub proof fn lemma_map_delete_then_set_moves_to_end(
    entries: Seq<(SpecJsKey, SpecJsKey)>,
    k: SpecJsKey,
    v: SpecJsKey,
    idx: nat,
)
    requires
        spec_map_wf(entries),
        (idx as int) < entries.len(),
        spec_same_value_zero(entries[idx as int].0, k),
    ensures
        ({
            let (after_del, did_del) = spec_map_delete(entries, k);
            let after_set = spec_map_set(after_del, k, v);
            &&& did_del
            &&& after_set.len() == entries.len()
            &&& after_set[entries.len() - 1] == (spec_canonicalize_key(k), v)
            &&& (forall|j: int| 0 <= j < idx as int ==> #[trigger] after_set[j] == entries[j])
            &&& (forall|j: int|
                idx as int <= j < entries.len() - 1 ==> #[trigger] after_set[j] == entries[j + 1])
        }),
{
    lemma_map_find_unique_under_wf(entries, k, idx);
    lemma_map_delete_preserves_wf(entries, k);
    let (after_del, _) = spec_map_delete(entries, k);
    lemma_map_find_index_spec(after_del, k);
}

/// Soundness and completeness of `spec_set_find_index`.
pub proof fn lemma_set_find_index_spec(items: Seq<SpecJsKey>, v: SpecJsKey)
    ensures
        match spec_set_find_index(items, v) {
            Some(idx) => {
                &&& (idx as int) < items.len()
                &&& spec_same_value_zero(items[idx as int], v)
                &&& forall|j: int| 0 <= j < idx as int ==> !spec_same_value_zero(#[trigger] items[j], v)
            },
            None => forall|j: int| 0 <= j < items.len() ==> !spec_same_value_zero(#[trigger] items[j], v),
        },
    decreases items.len(),
{
    if items.len() > 0 && !spec_same_value_zero(items[0], v) {
        let tail = items.subrange(1, items.len() as int);
        lemma_set_find_index_spec(tail, v);
        match spec_set_find_index(tail, v) {
            Some(idx) => {
                assert(tail[idx as int] == items[idx as int + 1]);
                assert forall|j: int| 0 <= j < idx as int + 1 implies !spec_same_value_zero(
                    #[trigger] items[j],
                    v,
                ) by {
                    if j > 0 {
                        assert(items[j] == tail[j - 1]);
                    }
                }
            },
            None => {
                assert forall|j: int| 0 <= j < items.len() implies !spec_same_value_zero(
                    #[trigger] items[j],
                    v,
                ) by {
                    if j > 0 {
                        assert(items[j] == tail[j - 1]);
                    }
                }
            },
        }
    }
}

/// `spec_set_add` preserves `spec_set_wf`.
pub proof fn lemma_set_add_preserves_wf(items: Seq<SpecJsKey>, v: SpecJsKey)
    requires
        spec_set_wf(items),
    ensures
        spec_set_wf(spec_set_add(items, v)),
{
    lemma_set_find_index_spec(items, v);
    if spec_set_find_index(items, v).is_none() {
        let next = spec_set_add(items, v);
        lemma_canonicalize_key_properties(v);
        assert forall|i: int, j: int| 0 <= i < j < next.len() implies !spec_same_value_zero(
            #[trigger] next[i],
            #[trigger] next[j],
        ) by {
            if j < items.len() {
                assert(next[i] == items[i]);
                assert(next[j] == items[j]);
            } else {
                assert(next[i] == items[i]);
                assert(next[j] == spec_canonicalize_key(v));
                if spec_same_value_zero(items[i], spec_canonicalize_key(v)) {
                    lemma_same_value_zero_equivalence(items[i], spec_canonicalize_key(v), v);
                    assert(spec_same_value_zero(items[i], v));
                }
            }
        }
    }
}

/// `spec_set_delete` preserves `spec_set_wf`.
pub proof fn lemma_set_delete_preserves_wf(items: Seq<SpecJsKey>, v: SpecJsKey)
    requires
        spec_set_wf(items),
    ensures
        spec_set_wf(spec_set_delete(items, v).0),
        !spec_set_has(spec_set_delete(items, v).0, v),
{
    lemma_set_find_index_spec(items, v);
    let (next, removed) = spec_set_delete(items, v);
    if removed {
        let idx = spec_set_find_index(items, v).unwrap() as int;
        assert forall|i: int| 0 <= i < next.len() implies #[trigger] next[i] != SpecJsKey::NumberBits(
            NEG_ZERO_BITS,
        ) by {
            if i < idx {
                assert(next[i] == items[i]);
            } else {
                assert(next[i] == items[i + 1]);
            }
        }
        assert forall|i: int, j: int| 0 <= i < j < next.len() implies !spec_same_value_zero(
            #[trigger] next[i],
            #[trigger] next[j],
        ) by {
            let oi = if i < idx { i } else { i + 1 };
            let oj = if j < idx { j } else { j + 1 };
            assert(next[i] == items[oi]);
            assert(next[j] == items[oj]);
        }
        lemma_set_find_index_spec(next, v);
        if let Some(f) = spec_set_find_index(next, v) {
            let fi = f as int;
            let orig = if fi < idx { fi } else { fi + 1 };
            assert(next[fi] == items[orig]);
            if orig > idx {
                lemma_same_value_zero_equivalence(items[idx], v, items[orig]);
                assert(spec_same_value_zero(items[idx], items[orig]));
            }
        }
    } else {
        lemma_set_find_index_spec(next, v);
    }
}

/// Under `spec_set_wf`, if `items[idx]` matches `v`, `spec_set_find_index` returns `Some(idx)`.
pub proof fn lemma_set_find_unique_under_wf(items: Seq<SpecJsKey>, v: SpecJsKey, idx: nat)
    requires
        spec_set_wf(items),
        (idx as int) < items.len(),
        spec_same_value_zero(items[idx as int], v),
    ensures
        spec_set_find_index(items, v) == Some(idx),
{
    lemma_set_find_index_spec(items, v);
    match spec_set_find_index(items, v) {
        Some(found) => {
            if found < idx {
                lemma_same_value_zero_equivalence(items[found as int], v, items[idx as int]);
                assert(spec_same_value_zero(items[found as int], items[idx as int]));
            } else if found > idx {
                assert(!spec_same_value_zero(items[idx as int], v));
            }
        },
        None => {
            assert(!spec_same_value_zero(items[idx as int], v));
        },
    }
}

/// `Set.prototype.add` on an existing value leaves insertion order completely unchanged.
pub proof fn lemma_set_add_existing_preserves_order(items: Seq<SpecJsKey>, v: SpecJsKey, idx: nat)
    requires
        spec_set_wf(items),
        (idx as int) < items.len(),
        spec_same_value_zero(items[idx as int], v),
    ensures
        spec_set_add(items, v) == items,
{
    lemma_set_find_unique_under_wf(items, v, idx);
}

/// `Set.prototype.delete` followed by `Set.prototype.add` moves an existing element to the end.
pub proof fn lemma_set_delete_then_add_moves_to_end(items: Seq<SpecJsKey>, v: SpecJsKey, idx: nat)
    requires
        spec_set_wf(items),
        (idx as int) < items.len(),
        spec_same_value_zero(items[idx as int], v),
    ensures
        ({
            let (after_del, did_del) = spec_set_delete(items, v);
            let after_add = spec_set_add(after_del, v);
            &&& did_del
            &&& after_add.len() == items.len()
            &&& after_add[items.len() - 1] == spec_canonicalize_key(v)
            &&& (forall|j: int| 0 <= j < idx as int ==> #[trigger] after_add[j] == items[j])
            &&& (forall|j: int|
                idx as int <= j < items.len() - 1 ==> #[trigger] after_add[j] == items[j + 1])
        }),
{
    lemma_set_find_unique_under_wf(items, v, idx);
    lemma_set_delete_preserves_wf(items, v);
    let (after_del, _) = spec_set_delete(items, v);
    lemma_set_find_index_spec(after_del, v);
}

// ---------------------------------------------------------------------------------------
// Exec: Key comparisons, CanonicalizeKeyedCollectionKey, JsMap, and JsSet
// ---------------------------------------------------------------------------------------

/// Exec check for `+0.0` or `-0.0` IEEE-754 bits.
pub fn is_zero_bits(bits: u64) -> (res: bool)
    ensures
        res == spec_is_zero_bits(bits),
{
    bits == POS_ZERO_BITS || bits == NEG_ZERO_BITS
}

/// Exec check for IEEE-754 `NaN` bits.
pub fn is_nan_bits(bits: u64) -> (res: bool)
    ensures
        res == spec_is_nan_bits(bits),
{
    (bits > POS_INF_BITS && bits <= 0x7FFF_FFFF_FFFF_FFFFu64) || bits > NEG_INF_BITS
}

/// Exec ECMA-262 §7.2.11 `SameValueZero`.
pub fn same_value_zero(x: &JsKey, y: &JsKey) -> (res: bool)
    ensures
        res == spec_same_value_zero(x@, y@),
{
    match (x, y) {
        (JsKey::Undefined, JsKey::Undefined) => true,
        (JsKey::Null, JsKey::Null) => true,
        (JsKey::Bool(a), JsKey::Bool(b)) => *a == *b,
        (JsKey::NumberBits(a), JsKey::NumberBits(b)) => {
            if is_nan_bits(*a) || is_nan_bits(*b) {
                is_nan_bits(*a) && is_nan_bits(*b)
            } else if is_zero_bits(*a) && is_zero_bits(*b) {
                true
            } else {
                *a == *b
            }
        },
        (JsKey::Str(a), JsKey::Str(b)) => eq_u16_slice(a.as_slice(), b.as_slice()),
        (JsKey::Symbol(a), JsKey::Symbol(b)) => *a == *b,
        (JsKey::ObjectRef(a), JsKey::ObjectRef(b)) => *a == *b,
        _ => false,
    }
}

/// Exec ECMA-262 §7.2.14 `IsStrictlyEqual` (`===`).
pub fn is_strictly_equal(x: &JsKey, y: &JsKey) -> (res: bool)
    ensures
        res == spec_is_strictly_equal(x@, y@),
{
    match (x, y) {
        (JsKey::Undefined, JsKey::Undefined) => true,
        (JsKey::Null, JsKey::Null) => true,
        (JsKey::Bool(a), JsKey::Bool(b)) => *a == *b,
        (JsKey::NumberBits(a), JsKey::NumberBits(b)) => {
            if is_nan_bits(*a) || is_nan_bits(*b) {
                false
            } else if is_zero_bits(*a) && is_zero_bits(*b) {
                true
            } else {
                *a == *b
            }
        },
        (JsKey::Str(a), JsKey::Str(b)) => eq_u16_slice(a.as_slice(), b.as_slice()),
        (JsKey::Symbol(a), JsKey::Symbol(b)) => *a == *b,
        (JsKey::ObjectRef(a), JsKey::ObjectRef(b)) => *a == *b,
        _ => false,
    }
}

/// Exec ECMA-262 §24.1.1.2 `CanonicalizeKeyedCollectionKey`.
pub fn canonicalize_key(k: JsKey) -> (out: JsKey)
    ensures
        out@ == spec_canonicalize_key(k@),
{
    match k {
        JsKey::NumberBits(bits) => {
            if bits == NEG_ZERO_BITS {
                JsKey::NumberBits(POS_ZERO_BITS)
            } else {
                JsKey::NumberBits(bits)
            }
        },
        other => other,
    }
}

/// Exec pair `(key, value)` in `JsMap`.
pub struct MapEntry {
    pub key: JsKey,
    pub value: JsKey,
}

impl View for MapEntry {
    type V = (SpecJsKey, SpecJsKey);

    open spec fn view(&self) -> (SpecJsKey, SpecJsKey) {
        (self.key@, self.value@)
    }
}

/// Spec view of a sequence of `MapEntry`.
pub open spec fn spec_entries_view(entries: Seq<MapEntry>) -> Seq<(SpecJsKey, SpecJsKey)> {
    Seq::new(entries.len(), |i: int| entries[i]@)
}

/// Verified deterministic insertion-order ECMAScript `Map` (§24.1).
pub struct JsMap {
    pub entries: Vec<MapEntry>,
}

impl JsMap {
    pub open spec fn view(&self) -> Seq<(SpecJsKey, SpecJsKey)> {
        spec_entries_view(self.entries@)
    }

    pub open spec fn wf(&self) -> bool {
        spec_map_wf(self@)
    }

    /// Construct an empty `JsMap`.
    pub fn new() -> (m: Self)
        ensures
            m@ == Seq::<(SpecJsKey, SpecJsKey)>::empty(),
            m.wf(),
    {
        let m = JsMap { entries: Vec::new() };
        proof {
            assert(m@ =~= Seq::<(SpecJsKey, SpecJsKey)>::empty());
        }
        m
    }

    /// Number of entries (`get Map.prototype.size`, §24.1.3.10).
    pub fn size(&self) -> (n: usize)
        ensures
            n == self@.len(),
    {
        self.entries.len()
    }

    fn find_index(&self, key: &JsKey) -> (res: Option<usize>)
        ensures
            match res {
                Some(idx) => spec_map_find_index(self@, key@) == Some(idx as nat) && (idx as int) < self@.len(),
                None => spec_map_find_index(self@, key@) == None::<nat>,
            },
    {
        let n = self.entries.len();
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                n == self@.len(),
                forall|j: int| 0 <= j < i as int ==> !spec_same_value_zero(#[trigger] self@[j].0, key@),
            decreases n - i,
        {
            if same_value_zero(&self.entries[i].key, key) {
                proof {
                    lemma_map_find_index_spec(self@, key@);
                    assert(self@[i as int].0 == self.entries@[i as int].key@);
                    let found = spec_map_find_index(self@, key@);
                    assert(found.is_some());
                    let f = found.unwrap();
                    if (f as int) < i as int {
                        assert(!spec_same_value_zero(self@[f as int].0, key@));
                    } else if (f as int) > i as int {
                        assert(!spec_same_value_zero(self@[i as int].0, key@));
                    }
                }
                return Some(i);
            }
            i += 1;
        }
        proof {
            lemma_map_find_index_spec(self@, key@);
        }
        None
    }

    /// `Map.prototype.has ( key )` (§24.1.3.7).
    pub fn has(&self, key: &JsKey) -> (res: bool)
        ensures
            res == spec_map_has(self@, key@),
    {
        self.find_index(key).is_some()
    }

    /// `Map.prototype.get ( key )` (§24.1.3.6).
    pub fn get(&self, key: &JsKey) -> (res: Option<JsKey>)
        ensures
            match res {
                Some(v) => spec_map_get(self@, key@) == Some(v@),
                None => spec_map_get(self@, key@) == None::<SpecJsKey>,
            },
    {
        match self.find_index(key) {
            Some(idx) => Some(clone_js_key(&self.entries[idx].value)),
            None => None,
        }
    }

    /// `Map.prototype.set ( key, value )` (§24.1.3.9):
    /// updates in-place if `key` already exists, else appends canonicalized key at end.
    pub fn set(&mut self, key: JsKey, value: JsKey)
        requires
            old(self).wf(),
        ensures
            final(self)@ == spec_map_set(old(self)@, key@, value@),
            final(self).wf(),
    {
        proof {
            lemma_map_set_preserves_wf(self@, key@, value@);
        }
        match self.find_index(&key) {
            Some(idx) => {
                let existing_key = clone_js_key(&self.entries[idx].key);
                self.entries.set(idx, MapEntry { key: existing_key, value });
                proof {
                    assert(self@ =~= spec_map_set(old(self)@, key@, value@));
                }
            },
            None => {
                let ck = canonicalize_key(key);
                self.entries.push(MapEntry { key: ck, value });
                proof {
                    assert(self@ =~= spec_map_set(old(self)@, key@, value@));
                }
            },
        }
    }

    /// `Map.prototype.delete ( key )` (§24.1.3.3):
    /// removes matching entry while preserving insertion order of all surviving entries.
    pub fn delete(&mut self, key: &JsKey) -> (removed: bool)
        requires
            old(self).wf(),
        ensures
            (final(self)@, removed) == spec_map_delete(old(self)@, key@),
            final(self).wf(),
    {
        proof {
            lemma_map_delete_preserves_wf(self@, key@);
        }
        match self.find_index(key) {
            Some(idx) => {
                let n = self.entries.len();
                let mut next: Vec<MapEntry> = Vec::new();
                let mut i: usize = 0;
                while i < n
                    invariant
                        i <= n,
                        idx < n,
                        n == self@.len(),
                        next@.len() == (if i <= idx { i as int } else { i as int - 1 }),
                        forall|j: int|
                            0 <= j < next@.len() ==> next@[j]@ == (if j < idx as int {
                                self@[j]
                            } else {
                                self@[j + 1]
                            }),
                    decreases n - i,
                {
                    if i != idx {
                        let ek = clone_js_key(&self.entries[i].key);
                        let ev = clone_js_key(&self.entries[i].value);
                        next.push(MapEntry { key: ek, value: ev });
                    }
                    i += 1;
                }
                self.entries = next;
                proof {
                    assert(self@ =~= spec_map_delete(old(self)@, key@).0);
                }
                true
            },
            None => false,
        }
    }

    /// `Map.prototype.clear ( )` (§24.1.3.1).
    pub fn clear(&mut self)
        ensures
            final(self)@ == Seq::<(SpecJsKey, SpecJsKey)>::empty(),
            final(self).wf(),
    {
        self.entries = Vec::new();
        proof {
            assert(self@ =~= Seq::<(SpecJsKey, SpecJsKey)>::empty());
        }
    }

    /// Deterministic insertion-order snapshot of keys (`Map.prototype.keys`, §24.1.3.8).
    pub fn keys(&self) -> (out: Vec<JsKey>)
        ensures
            out@.len() == self@.len(),
            forall|i: int| 0 <= i < out@.len() ==> out@[i]@ == self@[i].0,
    {
        let n = self.entries.len();
        let mut out: Vec<JsKey> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                n == self@.len(),
                out@.len() == i as int,
                forall|j: int| 0 <= j < i as int ==> out@[j]@ == self@[j].0,
            decreases n - i,
        {
            out.push(clone_js_key(&self.entries[i].key));
            i += 1;
        }
        out
    }

    /// Deterministic insertion-order snapshot of values (`Map.prototype.values`, §24.1.3.11).
    pub fn values(&self) -> (out: Vec<JsKey>)
        ensures
            out@.len() == self@.len(),
            forall|i: int| 0 <= i < out@.len() ==> out@[i]@ == self@[i].1,
    {
        let n = self.entries.len();
        let mut out: Vec<JsKey> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                n == self@.len(),
                out@.len() == i as int,
                forall|j: int| 0 <= j < i as int ==> out@[j]@ == self@[j].1,
            decreases n - i,
        {
            out.push(clone_js_key(&self.entries[i].value));
            i += 1;
        }
        out
    }
}

/// Spec view of a sequence of `JsKey`.
pub open spec fn spec_keys_view(items: Seq<JsKey>) -> Seq<SpecJsKey> {
    Seq::new(items.len(), |i: int| items[i]@)
}

/// Verified deterministic insertion-order ECMAScript `Set` (§24.2).
pub struct JsSet {
    pub items: Vec<JsKey>,
}

impl JsSet {
    pub open spec fn view(&self) -> Seq<SpecJsKey> {
        spec_keys_view(self.items@)
    }

    pub open spec fn wf(&self) -> bool {
        spec_set_wf(self@)
    }

    /// Construct an empty `JsSet`.
    pub fn new() -> (s: Self)
        ensures
            s@ == Seq::<SpecJsKey>::empty(),
            s.wf(),
    {
        let s = JsSet { items: Vec::new() };
        proof {
            assert(s@ =~= Seq::<SpecJsKey>::empty());
        }
        s
    }

    /// Number of elements (`get Set.prototype.size`, §24.2.3.9).
    pub fn size(&self) -> (n: usize)
        ensures
            n == self@.len(),
    {
        self.items.len()
    }

    fn find_index(&self, value: &JsKey) -> (res: Option<usize>)
        ensures
            match res {
                Some(idx) => spec_set_find_index(self@, value@) == Some(idx as nat) && (idx as int) < self@.len(),
                None => spec_set_find_index(self@, value@) == None::<nat>,
            },
    {
        let n = self.items.len();
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                n == self@.len(),
                forall|j: int| 0 <= j < i as int ==> !spec_same_value_zero(#[trigger] self@[j], value@),
            decreases n - i,
        {
            if same_value_zero(&self.items[i], value) {
                proof {
                    lemma_set_find_index_spec(self@, value@);
                    assert(self@[i as int] == self.items@[i as int]@);
                    let found = spec_set_find_index(self@, value@);
                    assert(found.is_some());
                    let f = found.unwrap();
                    if (f as int) < i as int {
                        assert(!spec_same_value_zero(self@[f as int], value@));
                    } else if (f as int) > i as int {
                        assert(!spec_same_value_zero(self@[i as int], value@));
                    }
                }
                return Some(i);
            }
            i += 1;
        }
        proof {
            lemma_set_find_index_spec(self@, value@);
        }
        None
    }

    /// `Set.prototype.has ( value )` (§24.2.3.6).
    pub fn has(&self, value: &JsKey) -> (res: bool)
        ensures
            res == spec_set_has(self@, value@),
    {
        self.find_index(value).is_some()
    }

    /// `Set.prototype.add ( value )` (§24.2.3.1):
    /// keeps order unchanged if already present, else appends canonicalized value (`-0 -> +0`).
    pub fn add(&mut self, value: JsKey)
        requires
            old(self).wf(),
        ensures
            final(self)@ == spec_set_add(old(self)@, value@),
            final(self).wf(),
    {
        proof {
            lemma_set_add_preserves_wf(self@, value@);
        }
        if self.find_index(&value).is_none() {
            let cv = canonicalize_key(value);
            self.items.push(cv);
            proof {
                assert(self@ =~= spec_set_add(old(self)@, value@));
            }
        }
    }

    /// `Set.prototype.delete ( value )` (§24.2.3.4).
    pub fn delete(&mut self, value: &JsKey) -> (removed: bool)
        requires
            old(self).wf(),
        ensures
            (final(self)@, removed) == spec_set_delete(old(self)@, value@),
            final(self).wf(),
    {
        proof {
            lemma_set_delete_preserves_wf(self@, value@);
        }
        match self.find_index(value) {
            Some(idx) => {
                let n = self.items.len();
                let mut next: Vec<JsKey> = Vec::new();
                let mut i: usize = 0;
                while i < n
                    invariant
                        i <= n,
                        idx < n,
                        n == self@.len(),
                        next@.len() == (if i <= idx { i as int } else { i as int - 1 }),
                        forall|j: int|
                            0 <= j < next@.len() ==> next@[j]@ == (if j < idx as int {
                                self@[j]
                            } else {
                                self@[j + 1]
                            }),
                    decreases n - i,
                {
                    if i != idx {
                        next.push(clone_js_key(&self.items[i]));
                    }
                    i += 1;
                }
                self.items = next;
                proof {
                    assert(self@ =~= spec_set_delete(old(self)@, value@).0);
                }
                true
            },
            None => false,
        }
    }

    /// `Set.prototype.clear ( )` (§24.2.3.2).
    pub fn clear(&mut self)
        ensures
            final(self)@ == Seq::<SpecJsKey>::empty(),
            final(self).wf(),
    {
        self.items = Vec::new();
        proof {
            assert(self@ =~= Seq::<SpecJsKey>::empty());
        }
    }

    /// Deterministic insertion-order snapshot of elements (`Set.prototype.values`, §24.2.3.10).
    pub fn values(&self) -> (out: Vec<JsKey>)
        ensures
            out@.len() == self@.len(),
            forall|i: int| 0 <= i < out@.len() ==> out@[i]@ == self@[i],
    {
        let n = self.items.len();
        let mut out: Vec<JsKey> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                i <= n,
                n == self@.len(),
                out@.len() == i as int,
                forall|j: int| 0 <= j < i as int ==> out@[j]@ == self@[j],
            decreases n - i,
        {
            out.push(clone_js_key(&self.items[i]));
            i += 1;
        }
        out
    }
}

} // verus!
