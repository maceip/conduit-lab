//! Index-Based Arena `Heap` (`ECMA-262 §6.1.7`), `Heap::wf` invariant (valid allocated
//! prototype pointers with strictly decreasing `proto_rank` acyclicity witness, duplicate-free
//! ordered property tables, valid `ObjId` references, and §10.4.2 Array exotic `length` invariant),
//! and verified property-table operations.
pub use crate::value::{
    bigint_same_value, check_prop_key_wf, clone_js_val, clone_prop_key, clone_vec_u16,
    clone_vec_u32, eq_vec_u16, eq_vec_u32, f64_bits_to_exact_u32, is_length_key, is_nan_bits,
    is_zero_bits, js_val_from_u32, length_prop_key, msb_u32, parse_array_index_utf16,
    prop_key_eq, prop_key_from_ascii, prop_key_from_utf16, same_value, same_value_zero,
    u32_to_f64_bits, JsBigInt, JsBigIntView, JsError, JsVal, JsValView, ObjId, PropKey,
    PropKeyView, UnsupportedFeature, CANONICAL_NAN_BITS, NEG_ZERO_BITS, POS_ZERO_BITS,
};
#[cfg(verus_keep_ghost)]
pub use crate::value::{
    lemma_f64_bits_to_exact_u32_canonical, lemma_length_key_wf, lemma_nan_payloads_equal_in_same_value,
    lemma_pos_neg_zero_distinct_in_same_value, lemma_same_value_refl, lemma_same_value_sym,
    lemma_same_value_trans, lemma_u32_f64_bits_injective, lemma_u32_f64_bits_roundtrip,
    prop_key_wf, spec_ascii_to_utf16, spec_bigint_same_value, spec_decimal_digits_value,
    spec_f64_bits_to_exact_u32, spec_is_ascii_digit_u16, spec_is_nan_bits, spec_is_zero_bits,
    spec_length_key, spec_length_utf16, spec_msb_u32, spec_parse_array_index_utf16,
    spec_prop_key_from_utf16, spec_same_value, spec_same_value_zero, spec_u32_to_f64_bits,
};

use crate::descriptor::{
    clone_complete_descriptor, CompleteDescView, CompleteDescriptor, PropertyDescriptor,
};
#[cfg(verus_keep_ghost)]
use crate::descriptor::{
    PropDescView, spec_complete_configurable, spec_complete_enumerable, spec_complete_is_accessor,
    spec_complete_is_data,
};
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------------------
// Object & Arena Data Structures
// ---------------------------------------------------------------------------------------

/// Distinguishes Ordinary ECMAScript objects (§10.1) from Array exotic objects (§10.4.2).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ObjectKind {
    Ordinary,
    Array,
}

pub struct PropEntryView {
    pub key: PropKeyView,
    pub desc: CompleteDescView,
}

/// Ordered own-property entry on an object (preserving chronological creation order per §10.1.11.1).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct PropertyEntry {
    pub key: PropKey,
    pub desc: CompleteDescriptor,
}

impl View for PropertyEntry {
    type V = PropEntryView;

    open spec fn view(&self) -> PropEntryView {
        PropEntryView { key: self.key@, desc: self.desc@ }
    }
}

pub fn clone_property_entry(e: &PropertyEntry) -> (out: PropertyEntry)
    ensures
        out@ == e@,
{
    PropertyEntry {
        key: clone_prop_key(&e.key),
        desc: clone_complete_descriptor(&e.desc),
    }
}

pub fn clone_prop_entries(entries: &Vec<PropertyEntry>) -> (out: Vec<PropertyEntry>)
    ensures
        out@.len() == entries@.len(),
        forall|i: int| 0 <= i < entries@.len() ==> (#[trigger] out@[i])@ == entries@[i]@,
{
    let n = entries.len();
    let mut out: Vec<PropertyEntry> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == entries@.len(),
            out@.len() == i as int,
            forall|k: int| 0 <= k < i as int ==> (#[trigger] out@[k])@ == entries@[k]@,
        decreases n - i,
    {
        let cloned = clone_property_entry(&entries[i]);
        out.push(cloned);
        i += 1;
    }
    out
}

pub struct ObjectView {
    pub kind: ObjectKind,
    pub prototype: Option<ObjId>,
    pub extensible: bool,
    pub properties: Seq<PropEntryView>,
}

/// Heap-allocated ECMAScript object record.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct JsObject {
    pub kind: ObjectKind,
    pub prototype: Option<ObjId>,
    pub extensible: bool,
    pub properties: Vec<PropertyEntry>,
}

impl View for JsObject {
    type V = ObjectView;

    open spec fn view(&self) -> ObjectView {
        ObjectView {
            kind: self.kind,
            prototype: self.prototype,
            extensible: self.extensible,
            properties: Seq::new(self.properties@.len(), |i: int| self.properties@[i]@),
        }
    }
}

pub fn clone_js_object(obj: &JsObject) -> (out: JsObject)
    ensures
        out@ == obj@,
{
    let props = clone_prop_entries(&obj.properties);
    let out = JsObject {
        kind: obj.kind,
        prototype: obj.prototype,
        extensible: obj.extensible,
        properties: props,
    };
    proof {
        assert(out@.properties =~= obj@.properties);
    }
    out
}

pub struct HeapView {
    pub objects: Seq<ObjectView>,
    pub proto_ranks: Seq<nat>,
}

/// Index-based safe-Rust arena heap for ECMAScript objects (`§6.1.7`), carrying a ghost
/// `proto_ranks` sequence witnessing strict prototype-depth decrease along every `[[Prototype]]` edge.
pub struct Heap {
    pub objects: Vec<JsObject>,
    pub proto_ranks: Ghost<Seq<nat>>,
}

impl View for Heap {
    type V = HeapView;

    open spec fn view(&self) -> HeapView {
        HeapView {
            objects: Seq::new(self.objects@.len(), |i: int| self.objects@[i]@),
            proto_ranks: self.proto_ranks@,
        }
    }
}

// ---------------------------------------------------------------------------------------
// Property List Specs & Verified Helpers
// ---------------------------------------------------------------------------------------

pub open spec fn spec_no_duplicate_keys(props: Seq<PropEntryView>) -> bool {
    forall|i: int, j: int|
        0 <= i < j < props.len() ==> (#[trigger] props[i]).key != (#[trigger] props[j]).key
}

pub open spec fn spec_find_prop_from(
    props: Seq<PropEntryView>,
    key: PropKeyView,
    start: nat,
) -> Option<nat>
    decreases props.len() - start,
{
    if start >= props.len() {
        None
    } else if props[start as int].key == key {
        Some(start)
    } else {
        spec_find_prop_from(props, key, start + 1)
    }
}

pub open spec fn spec_find_prop(props: Seq<PropEntryView>, key: PropKeyView) -> Option<nat> {
    spec_find_prop_from(props, key, 0)
}

pub open spec fn spec_lookup_prop(
    props: Seq<PropEntryView>,
    key: PropKeyView,
) -> Option<CompleteDescView> {
    match spec_find_prop(props, key) {
        None => None,
        Some(idx) => Some(props[idx as int].desc),
    }
}

pub proof fn lemma_find_prop_from_spec(
    props: Seq<PropEntryView>,
    key: PropKeyView,
    start: nat,
)
    requires
        start <= props.len(),
    ensures
        match spec_find_prop_from(props, key, start) {
            None => forall|k: int| start as int <= k < props.len() ==> (#[trigger] props[k]).key != key,
            Some(idx) =>
                start <= idx < props.len()
                && props[idx as int].key == key
                && (forall|k: int| start as int <= k < idx as int ==> (#[trigger] props[k]).key != key),
        },
    decreases props.len() - start,
{
    if start < props.len() {
        if props[start as int].key != key {
            lemma_find_prop_from_spec(props, key, start + 1);
        }
    }
}

pub proof fn lemma_find_prop_spec(props: Seq<PropEntryView>, key: PropKeyView)
    ensures
        match spec_find_prop(props, key) {
            None => forall|k: int| 0 <= k < props.len() ==> (#[trigger] props[k]).key != key,
            Some(idx) =>
                idx < props.len()
                && props[idx as int].key == key
                && (forall|k: int| 0 <= k < idx as int ==> (#[trigger] props[k]).key != key),
        },
{
    lemma_find_prop_from_spec(props, key, 0);
}

pub proof fn lemma_find_prop_unique_index(
    props: Seq<PropEntryView>,
    key: PropKeyView,
    i: int,
)
    requires
        spec_no_duplicate_keys(props),
        0 <= i < props.len(),
        props[i].key == key,
    ensures
        spec_find_prop(props, key) == Some(i as nat),
        spec_lookup_prop(props, key) == Some(props[i].desc),
{
    lemma_find_prop_spec(props, key);
    match spec_find_prop(props, key) {
        None => {
            assert(props[i].key != key);
        },
        Some(idx) => {
            if (idx as int) < i {
                assert(props[idx as int].key != props[i].key);
            } else if i < (idx as int) {
                assert(props[i].key != key);
            }
        },
    }
}

pub open spec fn spec_upsert_prop(
    props: Seq<PropEntryView>,
    key: PropKeyView,
    desc: CompleteDescView,
) -> Seq<PropEntryView> {
    match spec_find_prop(props, key) {
        Some(idx) => props.update(idx as int, PropEntryView { key, desc }),
        None => props.push(PropEntryView { key, desc }),
    }
}

pub open spec fn spec_remove_prop(
    props: Seq<PropEntryView>,
    key: PropKeyView,
) -> Seq<PropEntryView> {
    match spec_find_prop(props, key) {
        None => props,
        Some(idx) =>
            props.subrange(0, idx as int) + props.subrange((idx + 1) as int, props.len() as int),
    }
}

pub proof fn lemma_upsert_lookup(
    props: Seq<PropEntryView>,
    key: PropKeyView,
    desc: CompleteDescView,
    other_key: PropKeyView,
)
    requires
        spec_no_duplicate_keys(props),
    ensures
        spec_no_duplicate_keys(spec_upsert_prop(props, key, desc)),
        spec_lookup_prop(spec_upsert_prop(props, key, desc), other_key)
            == if other_key == key {
                Some(desc)
            } else {
                spec_lookup_prop(props, other_key)
            },
{
    lemma_find_prop_spec(props, key);
    let next = spec_upsert_prop(props, key, desc);
    assert(spec_no_duplicate_keys(next));
    if other_key == key {
        match spec_find_prop(props, key) {
            Some(idx) => {
                lemma_find_prop_unique_index(next, key, idx as int);
            },
            None => {
                lemma_find_prop_unique_index(next, key, (next.len() - 1) as int);
            },
        }
    } else {
        lemma_find_prop_spec(props, other_key);
        match spec_find_prop(props, other_key) {
            Some(oidx) => {
                lemma_find_prop_unique_index(next, other_key, oidx as int);
            },
            None => {
                lemma_find_prop_spec(next, other_key);
            },
        }
    }
}

pub proof fn lemma_remove_lookup(
    props: Seq<PropEntryView>,
    key: PropKeyView,
    other_key: PropKeyView,
)
    requires
        spec_no_duplicate_keys(props),
    ensures
        spec_no_duplicate_keys(spec_remove_prop(props, key)),
        spec_lookup_prop(spec_remove_prop(props, key), other_key)
            == if other_key == key {
                None
            } else {
                spec_lookup_prop(props, other_key)
            },
{
    lemma_find_prop_spec(props, key);
    let next = spec_remove_prop(props, key);
    match spec_find_prop(props, key) {
        None => {},
        Some(idx) => {
            let ii = idx as int;
            assert forall|a: int, b: int| 0 <= a < b < next.len() implies (#[trigger] next[a]).key != (#[trigger] next[b]).key by {
                let src_a = if a < ii { a } else { a + 1 };
                let src_b = if b < ii { b } else { b + 1 };
                assert(next[a] == props[src_a]);
                assert(next[b] == props[src_b]);
                assert(0 <= src_a < src_b < props.len());
            };
            if other_key == key {
                assert forall|m: int| 0 <= m < next.len() implies (#[trigger] next[m]).key != key by {
                    let src_m = if m < ii { m } else { m + 1 };
                    assert(next[m] == props[src_m]);
                    assert(props[src_m].key != props[ii].key);
                };
                lemma_find_prop_spec(next, key);
            } else {
                lemma_find_prop_spec(props, other_key);
                match spec_find_prop(props, other_key) {
                    None => {
                        assert forall|m: int| 0 <= m < next.len() implies (#[trigger] next[m]).key != other_key by {
                            let src_m = if m < ii { m } else { m + 1 };
                            assert(next[m] == props[src_m]);
                        };
                        lemma_find_prop_spec(next, other_key);
                    },
                    Some(oidx) => {
                        let oi = oidx as int;
                        assert(oi != ii);
                        let dst = if oi < ii { oi } else { oi - 1 };
                        assert(next[dst] == props[oi]);
                        lemma_find_prop_unique_index(next, other_key, dst);
                    },
                }
            }
        },
    }
}

// ---------------------------------------------------------------------------------------
// Heap Well-Formedness (`Heap::wf`) & Prototype-Rank Acyclicity Invariants
// ---------------------------------------------------------------------------------------

pub open spec fn val_refs_wf(num_objs: nat, v: JsValView) -> bool {
    match v {
        JsValView::Object(oid) => (oid.0 as nat) < num_objs,
        _ => true,
    }
}

pub open spec fn complete_desc_refs_wf(num_objs: nat, d: CompleteDescView) -> bool {
    match d {
        CompleteDescView::Data { value, .. } => val_refs_wf(num_objs, value),
        CompleteDescView::Accessor { get, set, .. } =>
            (match get {
                None => true,
                Some(gid) => (gid.0 as nat) < num_objs,
            })
            && (match set {
                None => true,
                Some(sid) => (sid.0 as nat) < num_objs,
            }),
    }
}

pub open spec fn prop_desc_refs_wf(num_objs: nat, d: PropDescView) -> bool {
    (match d.value {
        None => true,
        Some(v) => val_refs_wf(num_objs, v),
    })
    && (match d.get {
        Some(Some(gid)) => (gid.0 as nat) < num_objs,
        _ => true,
    })
    && (match d.set {
        Some(Some(sid)) => (sid.0 as nat) < num_objs,
        _ => true,
    })
}

pub open spec fn object_props_wf(num_objs: nat, props: Seq<PropEntryView>) -> bool {
    spec_no_duplicate_keys(props)
        && (forall|i: int|
            0 <= i < props.len() ==> prop_key_wf((#[trigger] props[i]).key)
                && complete_desc_refs_wf(num_objs, props[i].desc))
}

/// ECMA-262 §10.4.2 Array exotic length invariant:
/// - Own property `"length"` is a non-configurable, non-enumerable Data property;
/// - Its value is a canonical IEEE-754 `u32` `len_u32` (`len_bits == spec_u32_to_f64_bits(len_u32)`);
/// - Every own array-index property `PropKeyView::ArrayIndex(idx)` satisfies `idx < len_u32`
///   (and by `prop_key_wf`, `idx < u32::MAX`, covering all `idx < u32::MAX - 1` as well).
pub open spec fn array_object_wf(obj: ObjectView) -> bool {
    match spec_lookup_prop(obj.properties, spec_length_key()) {
        Some(CompleteDescView::Data {
            value: JsValView::NumberBits(len_bits),
            writable: _,
            enumerable: false,
            configurable: false,
        }) =>
            match spec_f64_bits_to_exact_u32(len_bits) {
                Some(len_u32) =>
                    len_bits == spec_u32_to_f64_bits(len_u32)
                    && (forall|i: int|
                        0 <= i < obj.properties.len() ==> match (#[trigger] obj.properties[i]).key {
                            PropKeyView::ArrayIndex(idx) => idx < len_u32,
                            _ => true,
                        }),
                None => false,
            },
        _ => false,
    }
}

pub open spec fn object_wf(num_objs: nat, obj: ObjectView) -> bool {
    object_props_wf(num_objs, obj.properties)
        && (obj.kind == ObjectKind::Array ==> array_object_wf(obj))
}

/// Prototype-graph well-formedness: every `Some(pid)` points to a valid allocated `ObjId`
/// with strictly smaller `proto_rank`, making infinite prototype loops impossible.
pub open spec fn proto_wf(h: HeapView) -> bool {
    h.objects.len() <= (usize::MAX as int)
        && h.proto_ranks.len() == h.objects.len()
        && (forall|i: int|
            0 <= i < h.objects.len() ==> match (#[trigger] h.objects[i]).prototype {
                None => true,
                Some(pid) =>
                    (pid.0 as int) < h.objects.len()
                    && h.proto_ranks[pid.0 as int] < h.proto_ranks[i],
            })
}

pub open spec fn heap_wf(h: HeapView) -> bool {
    proto_wf(h)
        && (forall|i: int|
            0 <= i < h.objects.len() ==> object_wf(h.objects.len() as nat, #[trigger] h.objects[i]))
}

pub open spec fn valid_obj(h: HeapView, id: ObjId) -> bool {
    (id.0 as int) < h.objects.len()
}

/// Exact ECMA-262 §6.1.7.3 invariant relation for a non-configurable own property `old_desc`
/// transitioning to `new_opt`.
pub open spec fn spec_nonconfigurable_preserved(
    old_desc: CompleteDescView,
    new_opt: Option<CompleteDescView>,
) -> bool {
    match new_opt {
        None => false,
        Some(nd) =>
            !spec_complete_configurable(nd)
            && spec_complete_enumerable(nd) == spec_complete_enumerable(old_desc)
            && spec_complete_is_data(nd) == spec_complete_is_data(old_desc)
            && spec_complete_is_accessor(nd) == spec_complete_is_accessor(old_desc)
            && (match (old_desc, nd) {
                (
                    CompleteDescView::Data { value: ov, writable: ow, .. },
                    CompleteDescView::Data { value: nv, writable: nw, .. },
                ) => !ow ==> (!nw && spec_same_value(nv, ov)),
                (
                    CompleteDescView::Accessor { get: og, set: os, .. },
                    CompleteDescView::Accessor { get: ng, set: ns, .. },
                ) => ng == og && ns == os,
                _ => false,
            }),
    }
}

/// Combined ECMA-262 §6.1.7.3 Essential Internal Method Invariants from pre-heap `h1` to post-heap `h2`
/// for any allocated object `o` and property key `k`.
pub open spec fn spec_essential_invariants_hold(
    h1: HeapView,
    h2: HeapView,
    o: ObjId,
    k: PropKeyView,
) -> bool {
    heap_wf(h2)
        && valid_obj(h2, o)
        && (!h1.objects[o.0 as int].extensible ==> (
            !h2.objects[o.0 as int].extensible
            && h2.objects[o.0 as int].prototype == h1.objects[o.0 as int].prototype
            && (spec_lookup_prop(h1.objects[o.0 as int].properties, k) is None
                ==> spec_lookup_prop(h2.objects[o.0 as int].properties, k) is None)
        ))
        && (match spec_lookup_prop(h1.objects[o.0 as int].properties, k) {
            Some(old_d) =>
                !spec_complete_configurable(old_d)
                    ==> spec_nonconfigurable_preserved(
                        old_d,
                        spec_lookup_prop(h2.objects[o.0 as int].properties, k),
                    ),
            None => true,
        })
}

pub proof fn lemma_nonconfigurable_preserved_refl(d: CompleteDescView)
    requires
        !spec_complete_configurable(d),
    ensures
        spec_nonconfigurable_preserved(d, Some(d)),
{
    if let CompleteDescView::Data { value: v, .. } = d {
        lemma_same_value_refl(v);
    }
}

pub proof fn lemma_nonconfigurable_preserved_trans(
    d0: CompleteDescView,
    d1: CompleteDescView,
    d2_opt: Option<CompleteDescView>,
)
    requires
        !spec_complete_configurable(d0),
        spec_nonconfigurable_preserved(d0, Some(d1)),
        spec_nonconfigurable_preserved(d1, d2_opt),
    ensures
        spec_nonconfigurable_preserved(d0, d2_opt),
{
    let d2 = d2_opt.unwrap();
    if let (
        CompleteDescView::Data { value: v0, writable: w0, .. },
        CompleteDescView::Data { value: v1, writable: w1, .. },
        CompleteDescView::Data { value: v2, writable: w2, .. },
    ) = (d0, d1, d2)
    {
        if !w0 {
            assert(!w1);
            assert(!w2);
            lemma_same_value_trans(v2, v1, v0);
        }
    }
}

pub proof fn lemma_essential_invariants_refl(h: HeapView, o: ObjId, k: PropKeyView)
    requires
        heap_wf(h),
        valid_obj(h, o),
    ensures
        spec_essential_invariants_hold(h, h, o, k),
{
    if let Some(d) = spec_lookup_prop(h.objects[o.0 as int].properties, k) {
        if !spec_complete_configurable(d) {
            lemma_nonconfigurable_preserved_refl(d);
        }
    }
}

pub open spec fn spec_all_essential_invariants(h1: HeapView, h2: HeapView) -> bool {
    forall|obs_o: ObjId, obs_k: PropKeyView|
        valid_obj(h1, obs_o) ==> #[trigger] spec_essential_invariants_hold(h1, h2, obs_o, obs_k)
}

pub proof fn lemma_all_essential_invariants_refl(h: HeapView)
    requires
        heap_wf(h),
    ensures
        spec_all_essential_invariants(h, h),
{
    assert forall|obs_o: ObjId, obs_k: PropKeyView| valid_obj(h, obs_o) implies
        #[trigger] spec_essential_invariants_hold(h, h, obs_o, obs_k)
    by {
        lemma_essential_invariants_refl(h, obs_o, obs_k);
    };
}

pub proof fn lemma_essential_invariants_trans(
    h0: HeapView,
    h1: HeapView,
    h2: HeapView,
    o: ObjId,
    k: PropKeyView,
)
    requires
        spec_essential_invariants_hold(h0, h1, o, k),
        spec_essential_invariants_hold(h1, h2, o, k),
    ensures
        spec_essential_invariants_hold(h0, h2, o, k),
{
    if let Some(d0) = spec_lookup_prop(h0.objects[o.0 as int].properties, k) {
        if !spec_complete_configurable(d0) {
            let d1 = spec_lookup_prop(h1.objects[o.0 as int].properties, k).unwrap();
            lemma_nonconfigurable_preserved_trans(
                d0,
                d1,
                spec_lookup_prop(h2.objects[o.0 as int].properties, k),
            );
        }
    }
}

pub open spec fn spec_opt_rank(h: HeapView, opt: Option<ObjId>) -> nat {
    match opt {
        None => 0,
        Some(id) =>
            if (id.0 as int) < h.proto_ranks.len() {
                h.proto_ranks[id.0 as int] + 1
            } else {
                0
            },
    }
}

/// Prototype reachability (`start == Some(target)` or reachable by following `[[Prototype]]` links).
/// Terminates unconditionally via `spec_opt_rank(h, start)`.
pub open spec fn spec_proto_reaches(h: HeapView, start: Option<ObjId>, target: ObjId) -> bool
    decreases spec_opt_rank(h, start),
{
    match start {
        None => false,
        Some(cur) =>
            if (cur.0 as int) >= h.objects.len() || (cur.0 as int) >= h.proto_ranks.len() {
                false
            } else if cur == target {
                true
            } else {
                let next = h.objects[cur.0 as int].prototype;
                if spec_opt_rank(h, next) < spec_opt_rank(h, Some(cur)) {
                    spec_proto_reaches(h, next, target)
                } else {
                    false
                }
            },
    }
}

pub proof fn lemma_proto_reaches_rank_le(h: HeapView, cur: ObjId, target: ObjId)
    requires
        proto_wf(h),
        valid_obj(h, cur),
        spec_proto_reaches(h, Some(cur), target),
    ensures
        valid_obj(h, target),
        h.proto_ranks[target.0 as int] <= h.proto_ranks[cur.0 as int],
        cur != target ==> h.proto_ranks[target.0 as int] < h.proto_ranks[cur.0 as int],
    decreases spec_opt_rank(h, Some(cur)),
{
    if cur != target {
        reveal_with_fuel(spec_proto_reaches, 2);
        let next = h.objects[cur.0 as int].prototype;
        assert(h.objects[cur.0 as int].prototype == next);
        match next {
            None => {},
            Some(pid) => {
                assert(spec_opt_rank(h, Some(pid)) < spec_opt_rank(h, Some(cur)));
                lemma_proto_reaches_rank_le(h, pid, target);
            },
        }
    }
}

/// Proves prototype chains are strictly acyclic: no allocated object can reach itself
/// through one or more `[[Prototype]]` steps.
pub proof fn lemma_proto_chain_acyclic(h: HeapView, id: ObjId)
    requires
        proto_wf(h),
        valid_obj(h, id),
    ensures
        !spec_proto_reaches(h, h.objects[id.0 as int].prototype, id),
{
    let next = h.objects[id.0 as int].prototype;
    if let Some(pid) = next {
        if spec_proto_reaches(h, Some(pid), id) {
            lemma_proto_reaches_rank_le(h, pid, id);
            assert(h.proto_ranks[id.0 as int] <= h.proto_ranks[pid.0 as int]);
            assert(h.proto_ranks[pid.0 as int] < h.proto_ranks[id.0 as int]);
        }
    }
}

/// Proves that re-pointing `o.prototype = new_proto` when `new_proto` does NOT reach `o`
/// preserves `proto_wf` with an explicit updated `proto_ranks` sequence.
pub open spec fn spec_recompute_proto_ranks(
    h: HeapView,
    o: ObjId,
    new_proto: Option<ObjId>,
) -> Seq<nat> {
    match new_proto {
        None => h.proto_ranks,
        Some(v) => {
            let delta: nat = h.proto_ranks[v.0 as int] + 1;
            Seq::new(
                h.proto_ranks.len(),
                |x: int|
                    if spec_proto_reaches(h, Some(ObjId(x as usize)), o) {
                        h.proto_ranks[x] + delta
                    } else {
                        h.proto_ranks[x]
                    },
            )
        },
    }
}

pub proof fn lemma_set_proto_preserves_proto_wf(
    h: HeapView,
    o: ObjId,
    new_proto: Option<ObjId>,
    updated_obj: ObjectView,
)
    requires
        proto_wf(h),
        valid_obj(h, o),
        updated_obj.prototype == new_proto,
        match new_proto {
            None => true,
            Some(v) => valid_obj(h, v) && !spec_proto_reaches(h, Some(v), o),
        },
    ensures
        proto_wf(
            HeapView {
                objects: h.objects.update(o.0 as int, updated_obj),
                proto_ranks: spec_recompute_proto_ranks(h, o, new_proto),
            },
        ),
{
    let new_objs = h.objects.update(o.0 as int, updated_obj);
    let new_ranks = spec_recompute_proto_ranks(h, o, new_proto);
    let nh = HeapView { objects: new_objs, proto_ranks: new_ranks };
    assert(nh.proto_ranks.len() == nh.objects.len());

    assert forall|i: int| 0 <= i < nh.objects.len() implies match (#[trigger] nh.objects[i]).prototype {
        None => true,
        Some(pid) => (pid.0 as int) < nh.objects.len() && nh.proto_ranks[pid.0 as int] < nh.proto_ranks[i],
    } by {
        match new_proto {
            None => {
                if i == o.0 as int {
                    assert(nh.objects[i].prototype is None);
                } else {
                    assert(nh.objects[i] == h.objects[i]);
                }
            },
            Some(v) => {
                let delta: nat = h.proto_ranks[v.0 as int] + 1;
                if i == o.0 as int {
                    assert(ObjId(i as usize) == o);
                    assert(spec_proto_reaches(h, Some(o), o));
                    assert(nh.proto_ranks[i] == h.proto_ranks[i] + delta);
                    assert(ObjId((v.0 as int) as usize) == v);
                    assert(!spec_proto_reaches(h, Some(v), o));
                    assert(nh.proto_ranks[v.0 as int] == h.proto_ranks[v.0 as int]);
                    assert(nh.proto_ranks[v.0 as int] < nh.proto_ranks[i]);
                } else {
                    assert(nh.objects[i] == h.objects[i]);
                    if let Some(pid) = h.objects[i].prototype {
                        reveal_with_fuel(spec_proto_reaches, 2);
                        let xi = ObjId(i as usize);
                        assert(xi.0 as int == i);
                        assert(xi != o);
                        assert(ObjId((pid.0 as int) as usize) == pid);
                        assert(h.proto_ranks[pid.0 as int] < h.proto_ranks[i]);
                        assert(spec_opt_rank(h, Some(pid)) < spec_opt_rank(h, Some(xi)));
                        assert(spec_proto_reaches(h, Some(xi), o) == spec_proto_reaches(h, Some(pid), o));
                    }
                }
            },
        }
    };
}

pub proof fn lemma_object_wf_monotonic(n1: nat, n2: nat, obj: ObjectView)
    requires
        n1 <= n2,
        object_wf(n1, obj),
    ensures
        object_wf(n2, obj),
{
    assert forall|i: int| 0 <= i < obj.properties.len() implies
        prop_key_wf((#[trigger] obj.properties[i]).key)
        && complete_desc_refs_wf(n2, obj.properties[i].desc)
    by {
        assert(complete_desc_refs_wf(n1, obj.properties[i].desc));
    };
}

// ---------------------------------------------------------------------------------------
// Executable Property Table Helpers & Heap Methods
// ---------------------------------------------------------------------------------------

pub fn find_prop_index(props: &Vec<PropertyEntry>, key: &PropKey) -> (res: Option<usize>)
    ensures
        match res {
            None => spec_find_prop(
                Seq::new(props@.len(), |i: int| props@[i]@),
                key@,
            ) is None,
            Some(idx) =>
                (idx as int) < props@.len()
                && spec_find_prop(
                    Seq::new(props@.len(), |i: int| props@[i]@),
                    key@,
                ) == Some(idx as nat),
        },
{
    let ghost pview = Seq::new(props@.len(), |i: int| props@[i]@);
    let n = props.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == props@.len(),
            pview == Seq::new(props@.len(), |k: int| props@[k]@),
            spec_find_prop(pview, key@) == spec_find_prop_from(pview, key@, i as nat),
        decreases n - i,
    {
        if prop_key_eq(&props[i].key, key) {
            proof {
                assert(pview[i as int].key == key@);
            }
            return Some(i);
        }
        proof {
            assert(pview[i as int].key != key@);
        }
        i += 1;
    }
    None
}

pub fn lookup_prop_in_vec(
    props: &Vec<PropertyEntry>,
    key: &PropKey,
) -> (res: Option<CompleteDescriptor>)
    ensures
        ({
            let pview = Seq::new(props@.len(), |i: int| props@[i]@);
            let rview = match &res {
                None => None,
                Some(d) => Some(d@),
            };
            rview == spec_lookup_prop(pview, key@)
        }),
{
    match find_prop_index(props, key) {
        None => None,
        Some(idx) => Some(clone_complete_descriptor(&props[idx].desc)),
    }
}

pub fn upsert_prop_in_vec(
    props: &mut Vec<PropertyEntry>,
    key: PropKey,
    desc: CompleteDescriptor,
)
    ensures
        Seq::new(final(props)@.len(), |i: int| final(props)@[i]@)
            == spec_upsert_prop(
                Seq::new(old(props)@.len(), |i: int| old(props)@[i]@),
                key@,
                desc@,
            ),
{
    let ghost old_view = Seq::new(old(props)@.len(), |i: int| old(props)@[i]@);
    match find_prop_index(props, &key) {
        Some(idx) => {
            props.set(idx, PropertyEntry { key, desc });
            proof {
                let new_view = Seq::new(props@.len(), |i: int| props@[i]@);
                assert(new_view =~= old_view.update(idx as int, PropEntryView { key: key@, desc: desc@ }));
            }
        },
        None => {
            props.push(PropertyEntry { key, desc });
            proof {
                let new_view = Seq::new(props@.len(), |i: int| props@[i]@);
                assert(new_view =~= old_view.push(PropEntryView { key: key@, desc: desc@ }));
            }
        },
    }
}

pub fn remove_prop_in_vec(props: &mut Vec<PropertyEntry>, key: &PropKey)
    ensures
        Seq::new(final(props)@.len(), |i: int| final(props)@[i]@)
            == spec_remove_prop(
                Seq::new(old(props)@.len(), |i: int| old(props)@[i]@),
                key@,
            ),
{
    let ghost old_view = Seq::new(old(props)@.len(), |i: int| old(props)@[i]@);
    match find_prop_index(props, key) {
        None => {},
        Some(idx) => {
            let n = props.len();
            let mut rebuilt: Vec<PropertyEntry> = Vec::new();
            let mut i: usize = 0;
            while i < n
                invariant
                    i <= n,
                    idx < n,
                    n == props@.len(),
                    old_view == Seq::new(props@.len(), |k: int| props@[k]@),
                    rebuilt@.len() == if i <= idx { i as int } else { (i - 1) as int },
                    forall|m: int|
                        0 <= m < rebuilt@.len() ==> (#[trigger] rebuilt@[m])@
                            == if m < idx as int {
                                old_view[m]
                            } else {
                                old_view[m + 1]
                            },
                decreases n - i,
            {
                if i != idx {
                    let e = clone_property_entry(&props[i]);
                    rebuilt.push(e);
                }
                i += 1;
            }
            *props = rebuilt;
            proof {
                let new_view = Seq::new(props@.len(), |k: int| props@[k]@);
                let target = old_view.subrange(0, idx as int)
                    + old_view.subrange((idx + 1) as int, old_view.len() as int);
                assert(new_view =~= target);
            }
        },
    }
}

impl Heap {
    /// Full heap well-formedness predicate (`§6.1.7` & `§10.4.2`).
    pub open spec fn wf(&self) -> bool {
        heap_wf(self@)
    }

    pub open spec fn valid_obj(&self, id: ObjId) -> bool {
        valid_obj(self@, id)
    }

    pub open spec fn proto_rank(&self, id: ObjId) -> nat {
        self.proto_ranks@[id.0 as int]
    }

    pub open spec fn val_wf(&self, v: JsValView) -> bool {
        val_refs_wf(self@.objects.len() as nat, v)
    }

    pub open spec fn desc_wf(&self, d: PropDescView) -> bool {
        crate::descriptor::prop_desc_wf(d) && prop_desc_refs_wf(self@.objects.len() as nat, d)
    }

    pub fn new() -> (h: Heap)
        ensures
            h.wf(),
            h@.objects.len() == 0,
    {
        let h = Heap {
            objects: Vec::new(),
            proto_ranks: Ghost(Seq::empty()),
        };
        proof {
            assert(h@.objects =~= Seq::<ObjectView>::empty());
        }
        h
    }

    pub fn len(&self) -> (n: usize)
        ensures
            n == self@.objects.len(),
    {
        self.objects.len()
    }

    pub fn is_valid_obj(&self, id: ObjId) -> (r: bool)
        ensures
            r == self.valid_obj(id),
    {
        id.0 < self.objects.len()
    }

    pub fn check_val_wf(&self, v: &JsVal) -> (r: bool)
        ensures
            r == self.val_wf(v@),
    {
        match v {
            JsVal::Object(oid) => oid.0 < self.objects.len(),
            _ => true,
        }
    }

    pub fn check_desc_wf(&self, d: &PropertyDescriptor) -> (r: bool)
        ensures
            r == self.desc_wf(d@),
    {
        if crate::descriptor::is_data_descriptor(d) && crate::descriptor::is_accessor_descriptor(d) {
            return false;
        }
        let val_ok = match &d.value {
            None => true,
            Some(v) => self.check_val_wf(v),
        };
        let get_ok = match d.get {
            Some(Some(gid)) => gid.0 < self.objects.len(),
            _ => true,
        };
        let set_ok = match d.set {
            Some(Some(sid)) => sid.0 < self.objects.len(),
            _ => true,
        };
        val_ok && get_ok && set_ok
    }

    /// Allocates a new Ordinary object (`OrdinaryObjectCreate`, §10.1.12) in the arena.
    pub fn alloc_ordinary(&mut self, prototype: Option<ObjId>) -> (id: ObjId)
        requires
            old(self).wf(),
            old(self)@.objects.len() < usize::MAX,
            match prototype {
                None => true,
                Some(pid) => old(self).valid_obj(pid),
            },
        ensures
            final(self).wf(),
            final(self).valid_obj(id),
            id.0 == old(self)@.objects.len(),
            final(self)@.objects.len() == old(self)@.objects.len() + 1,
            forall|k: int| 0 <= k < old(self)@.objects.len() ==> (#[trigger] final(self)@.objects[k]) == old(self)@.objects[k],
            final(self)@.objects[id.0 as int] == (ObjectView {
                kind: ObjectKind::Ordinary,
                prototype,
                extensible: true,
                properties: Seq::empty(),
            }),
    {
        let idx = self.objects.len();
        let ghost old_h = self@;
        let ghost new_rank: nat = match prototype {
            None => 0,
            Some(pid) => old_h.proto_ranks[pid.0 as int] + 1,
        };
        let obj = JsObject {
            kind: ObjectKind::Ordinary,
            prototype,
            extensible: true,
            properties: Vec::new(),
        };
        self.objects.push(obj);
        proof {
            self.proto_ranks@ = old_h.proto_ranks.push(new_rank);
            assert(self.objects@[idx as int]@.properties =~= Seq::<PropEntryView>::empty());
            assert(self@.objects =~= old_h.objects.push(ObjectView {
                kind: ObjectKind::Ordinary,
                prototype,
                extensible: true,
                properties: Seq::empty(),
            }));
            assert forall|i: int| 0 <= i < self@.objects.len() implies
                object_wf(self@.objects.len() as nat, #[trigger] self@.objects[i])
            by {
                if i < old_h.objects.len() {
                    assert(object_wf(old_h.objects.len() as nat, old_h.objects[i]));
                    lemma_object_wf_monotonic(
                        old_h.objects.len() as nat,
                        self@.objects.len() as nat,
                        old_h.objects[i],
                    );
                } else {
                    assert(self@.objects[i].properties =~= Seq::<PropEntryView>::empty());
                }
            };
        }
        ObjId(idx)
    }
}

} // verus!
