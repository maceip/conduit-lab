//! Array Exotic Object (`ECMA-262 §10.4.2`):
//! - `ArrayCreate` (`§10.4.2.2`),
//! - `ArraySetLength` (`§10.4.2.4` — including `ToUint32`/`ToNumber` `RangeError` check,
//!   `-0.0 -> +0.0` canonicalization, descending sparse-array element deletion, and stopping at
//!   the highest non-configurable element `idx` with `length = idx + 1` and returning `false`),
//! - Array `[[DefineOwnProperty]]` (`§10.4.2.1` — auto-extending `length` when `writable` and
//!   rejecting index `>= length` when `!writable`),
//! - Polymorphic internal methods (`define_own_property`, `js_set`, `js_set_with_own_descriptor`)
//!   dispatching across Ordinary (`§10.1`) and Array (`§10.4.2`) objects.
use crate::descriptor::{
    CompleteDescriptor, PropertyDescriptor,
};
#[cfg(verus_keep_ghost)]
use crate::descriptor::{
    prop_desc_wf, spec_complete_configurable, spec_validate_and_apply_property_descriptor,
    CompleteDescView, PropDescView,
};
use crate::heap::{
    clone_js_object, clone_js_val, f64_bits_to_exact_u32, is_length_key, js_val_from_u32,
    length_prop_key, lookup_prop_in_vec, Heap, JsError, JsObject, JsVal, ObjId, ObjectKind,
    PropKey, PropertyEntry, UnsupportedFeature,
};
#[cfg(verus_keep_ghost)]
use crate::heap::{
    array_object_wf, complete_desc_refs_wf, heap_wf, lemma_all_essential_invariants_refl,
    lemma_essential_invariants_refl, lemma_f64_bits_to_exact_u32_canonical, lemma_find_prop_spec,
    lemma_length_key_wf, lemma_nonconfigurable_preserved_refl, lemma_object_wf_monotonic,
    lemma_remove_lookup, lemma_u32_f64_bits_injective, lemma_u32_f64_bits_roundtrip,
    lemma_upsert_lookup, object_props_wf, object_wf, prop_desc_refs_wf, prop_key_wf,
    spec_all_essential_invariants, spec_essential_invariants_hold, spec_f64_bits_to_exact_u32,
    spec_find_prop, spec_length_key, spec_lookup_prop, spec_no_duplicate_keys,
    spec_nonconfigurable_preserved, spec_remove_prop, spec_u32_to_f64_bits, spec_upsert_prop,
    val_refs_wf, valid_obj, HeapView, JsValView, ObjectView, PropEntryView, PropKeyView,
};
use crate::ordinary::{
    apply_ordinary_define_on_object, apply_ordinary_delete_on_object,
    collect_sorted_array_indices, ordinary_define_own_property, ordinary_get_own_property,
    resolve_set_descriptor, SetOutcome,
};
#[cfg(verus_keep_ghost)]
use crate::ordinary::{
    lemma_collect_sorted_indices_props, lemma_delete_preserves_object_wf,
    lemma_ordinary_define_obj_essential, lemma_ordinary_define_preserves_props_wf,
    spec_collect_sorted_indices, spec_ordinary_define_on_object,
    spec_ordinary_define_own_property, spec_ordinary_delete_on_object,
    spec_ordinary_get_own_property, spec_props_has_array_index, spec_resolve_set_descriptor,
    spec_seq_u32_contains, spec_strictly_sorted_u32, SetOutcomeView,
};
use crate::string_to_f64::string_to_f64_bits;
#[cfg(verus_keep_ghost)]
use crate::string_to_f64::spec_string_to_f64_bits;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------------------
// String & Primitive Coercion for `ArraySetLength` (`§10.4.2.4` steps 3–5)
// ---------------------------------------------------------------------------------------

/// ECMA-262 §10.4.2.4 steps 3–5 for String inputs: first rounds `s` to IEEE-754 binary64 `Number`
/// via `StringToNumber` (§7.1.4.1.1 RNE), then checks `SameValueZero(𝔽(ToUint32(n)), n)`.
pub open spec fn spec_str_to_array_length(s: Seq<u16>) -> Option<u32> {
    spec_f64_bits_to_exact_u32(spec_string_to_f64_bits(s))
}

fn str_to_array_length(s: &Vec<u16>) -> (res: Option<u32>)
    ensures
        res == spec_str_to_array_length(s@),
{
    f64_bits_to_exact_u32(string_to_f64_bits(s))
}

/// ECMA-262 §10.4.2.4 steps 3–5: coerces `Desc.[[Value]]` to `newLen: u32` iff
/// `SameValueZero(𝔽(ToUint32(v)), ToNumber(v))` holds; throws `TypeError` on `Symbol`/`BigInt`,
/// `RangeError` on invalid numeric range (`NaN`, negative, fractional, `>= 2^32`, `undefined`),
/// or `Unsupported(ObjectToPrimitiveCoercion)` on an uncoerced Object value.
pub open spec fn spec_coerce_array_length_value(v: JsValView) -> Result<u32, JsError> {
    match v {
        JsValView::NumberBits(bits) =>
            match spec_f64_bits_to_exact_u32(bits) {
                Some(n) => Ok(n),
                None => Err(JsError::RangeError),
            },
        JsValView::Bool(b) => Ok(if b { 1u32 } else { 0u32 }),
        JsValView::Null => Ok(0u32),
        JsValView::Undefined => Err(JsError::RangeError),
        JsValView::BigInt(_) => Err(JsError::TypeError),
        JsValView::Symbol(_) => Err(JsError::TypeError),
        JsValView::Str(s) =>
            match spec_str_to_array_length(s) {
                Some(n) => Ok(n),
                None => Err(JsError::RangeError),
            },
        JsValView::Object(_) =>
            Err(JsError::Unsupported(UnsupportedFeature::ObjectToPrimitiveCoercion)),
    }
}

pub fn coerce_array_length_value(v: &JsVal) -> (res: Result<u32, JsError>)
    ensures
        res == spec_coerce_array_length_value(v@),
{
    match v {
        JsVal::NumberBits(bits) =>
            match f64_bits_to_exact_u32(*bits) {
                Some(n) => Ok(n),
                None => Err(JsError::RangeError),
            },
        JsVal::Bool(b) => Ok(if *b { 1u32 } else { 0u32 }),
        JsVal::Null => Ok(0u32),
        JsVal::Undefined => Err(JsError::RangeError),
        JsVal::BigInt(_) => Err(JsError::TypeError),
        JsVal::Symbol(_) => Err(JsError::TypeError),
        JsVal::Str(s) =>
            match str_to_array_length(s) {
                Some(n) => Ok(n),
                None => Err(JsError::RangeError),
            },
        JsVal::Object(_) =>
            Err(JsError::Unsupported(UnsupportedFeature::ObjectToPrimitiveCoercion)),
    }
}

// ---------------------------------------------------------------------------------------
// §10.4.2.2 `ArrayCreate` & Array Length Inspection
// ---------------------------------------------------------------------------------------

pub open spec fn spec_array_length_obj(obj: ObjectView) -> u32 {
    match spec_lookup_prop(obj.properties, spec_length_key()) {
        Some(CompleteDescView::Data { value: JsValView::NumberBits(bits), .. }) =>
            spec_f64_bits_to_exact_u32(bits).unwrap(),
        _ => 0u32,
    }
}

pub open spec fn spec_array_length(h: HeapView, a: ObjId) -> u32 {
    spec_array_length_obj(h.objects[a.0 as int])
}

pub open spec fn spec_array_length_writable_obj(obj: ObjectView) -> bool {
    match spec_lookup_prop(obj.properties, spec_length_key()) {
        Some(CompleteDescView::Data { writable, .. }) => writable,
        _ => false,
    }
}

fn read_array_length_and_writable(obj: &JsObject) -> (res: (u32, bool))
    requires
        array_object_wf(obj@),
    ensures
        res.0 == spec_array_length_obj(obj@),
        res.1 == spec_array_length_writable_obj(obj@),
{
    let lkey = length_prop_key();
    let d = lookup_prop_in_vec(&obj.properties, &lkey);
    match d {
        Some(CompleteDescriptor::Data { value: JsVal::NumberBits(bits), writable, .. }) => {
            let len = f64_bits_to_exact_u32(bits).unwrap();
            (len, writable)
        },
        _ => {
            proof {
                assert(false);
            }
            (0u32, false)
        },
    }
}

pub fn array_length(heap: &Heap, a: ObjId) -> (len: u32)
    requires
        heap.wf(),
        heap.valid_obj(a),
        heap@.objects[a.0 as int].kind == ObjectKind::Array,
    ensures
        len == spec_array_length(heap@, a),
{
    proof {
        assert(object_wf(heap@.objects.len() as nat, heap@.objects[a.0 as int]));
    }
    let (len, _) = read_array_length_and_writable(&heap.objects[a.0]);
    len
}

/// ECMA-262 §10.4.2.2 `ArrayCreate ( length [ , proto ] )`.
pub fn array_create(
    heap: &mut Heap,
    length: u32,
    prototype: Option<ObjId>,
) -> (id: ObjId)
    requires
        old(heap).wf(),
        old(heap)@.objects.len() < usize::MAX,
        match prototype {
            None => true,
            Some(pid) => old(heap).valid_obj(pid),
        },
    ensures
        final(heap).wf(),
        final(heap).valid_obj(id),
        id.0 == old(heap)@.objects.len(),
        final(heap)@.objects.len() == old(heap)@.objects.len() + 1,
        forall|k: int|
            0 <= k < old(heap)@.objects.len()
                ==> (#[trigger] final(heap)@.objects[k]) == old(heap)@.objects[k],
        final(heap)@.objects[id.0 as int].kind == ObjectKind::Array,
        final(heap)@.objects[id.0 as int].prototype == prototype,
        final(heap)@.objects[id.0 as int].extensible == true,
        spec_array_length(final(heap)@, id) == length,
{
    let idx = heap.objects.len();
    let ghost old_h = heap@;
    let ghost new_rank: nat = match prototype {
        None => 0,
        Some(pid) => old_h.proto_ranks[pid.0 as int] + 1,
    };
    let lkey = length_prop_key();
    let ldesc = CompleteDescriptor::Data {
        value: js_val_from_u32(length),
        writable: true,
        enumerable: false,
        configurable: false,
    };
    let mut props: Vec<PropertyEntry> = Vec::new();
    props.push(PropertyEntry { key: lkey, desc: ldesc });

    let obj = JsObject {
        kind: ObjectKind::Array,
        prototype,
        extensible: true,
        properties: props,
    };
    let ghost obj_view = obj@;
    heap.objects.push(obj);
    proof {
        heap.proto_ranks@ = old_h.proto_ranks.push(new_rank);
        lemma_u32_f64_bits_roundtrip(length);
        lemma_length_key_wf();
        assert(obj_view.properties.len() == 1);
        assert(obj_view.properties[0] == (PropEntryView {
            key: spec_length_key(),
            desc: CompleteDescView::Data {
                value: JsValView::NumberBits(spec_u32_to_f64_bits(length)),
                writable: true,
                enumerable: false,
                configurable: false,
            },
        }));
        assert(spec_find_prop(obj_view.properties, spec_length_key()) == Some(0nat));
        assert(array_object_wf(obj_view));
        assert(object_wf(heap@.objects.len() as nat, obj_view));
        assert(heap@.objects =~= old_h.objects.push(obj_view));
        assert forall|i: int| 0 <= i < heap@.objects.len() implies
            object_wf(heap@.objects.len() as nat, #[trigger] heap@.objects[i])
        by {
            if i < old_h.objects.len() {
                assert(object_wf(old_h.objects.len() as nat, old_h.objects[i]));
                lemma_object_wf_monotonic(
                    old_h.objects.len() as nat,
                    heap@.objects.len() as nat,
                    old_h.objects[i],
                );
            } else {
                assert(heap@.objects[i] == obj_view);
            }
        };
    }
    ObjId(idx)
}

/// Checked `ArrayCreate` enforcing ECMA-262 §10.4.2.2 step 1 (`length > 2^32 - 1` -> `RangeError`).
pub fn array_create_checked(
    heap: &mut Heap,
    length: u64,
    prototype: Option<ObjId>,
) -> (res: Result<ObjId, JsError>)
    requires
        old(heap).wf(),
        old(heap)@.objects.len() < usize::MAX,
        match prototype {
            None => true,
            Some(pid) => old(heap).valid_obj(pid),
        },
    ensures
        final(heap).wf(),
        length > (u32::MAX as u64) ==> (res == Err::<ObjId, JsError>(JsError::RangeError) && final(heap)@ == old(heap)@),
        length <= (u32::MAX as u64) ==> (res is Ok && final(heap).valid_obj(res.unwrap()) && spec_array_length(final(heap)@, res.unwrap()) == length as u32),
{
    if length > (u32::MAX as u64) {
        Err(JsError::RangeError)
    } else {
        Ok(array_create(heap, length as u32, prototype))
    }
}

// ---------------------------------------------------------------------------------------
// §10.4.2.4 `ArraySetLength` (Exact ECMA-262 Semantics with Descending Element Deletion)
// ---------------------------------------------------------------------------------------

/// Recursive spec of ECMA-262 §10.4.2.4 step 15 descending array-index deletion loop:
/// Iterates `sorted_idxs[0..k]` from `k - 1` down to `0` while `sorted_idxs[k - 1] >= new_len`.
/// Stops immediately if `!deleteSucceeded` (non-configurable element `idx`), setting `"length"`
/// to `idx + 1` (with `writable = new_writable`) and returning `false`.
pub open spec fn spec_shrink_elements_desc(
    obj: ObjectView,
    sorted_idxs: Seq<u32>,
    k: nat,
    new_len: u32,
    new_writable: bool,
) -> (bool, ObjectView)
    decreases k,
{
    if k == 0 || k > sorted_idxs.len() || sorted_idxs[(k - 1) as int] < new_len {
        let final_obj = if !new_writable {
            let w_false = PropDescView {
                value: None,
                writable: Some(false),
                get: None,
                set: None,
                enumerable: None,
                configurable: None,
            };
            spec_ordinary_define_on_object(obj, spec_length_key(), w_false).1
        } else {
            obj
        };
        (true, final_obj)
    } else {
        let idx = sorted_idxs[(k - 1) as int];
        let elem_key = PropKeyView::ArrayIndex(idx);
        let (del_ok, after_del) = spec_ordinary_delete_on_object(obj, elem_key);
        if !del_ok {
            let stopped_len: u32 = if idx < u32::MAX { add(idx, 1u32) } else { u32::MAX };
            let stop_desc = PropDescView {
                value: Some(JsValView::NumberBits(spec_u32_to_f64_bits(stopped_len))),
                writable: if !new_writable { Some(false) } else { None },
                get: None,
                set: None,
                enumerable: None,
                configurable: None,
            };
            let (_, stopped_obj) =
                spec_ordinary_define_on_object(after_del, spec_length_key(), stop_desc);
            (false, stopped_obj)
        } else {
            spec_shrink_elements_desc(after_del, sorted_idxs, (k - 1) as nat, new_len, new_writable)
        }
    }
}

/// Complete ECMA-262 §10.4.2.4 `ArraySetLength ( A, Desc )` spec on object `obj`.
pub open spec fn spec_array_set_length_on_object(
    obj: ObjectView,
    desc: PropDescView,
) -> Result<(bool, ObjectView), JsError> {
    if desc.value is None {
        Ok(spec_ordinary_define_on_object(obj, spec_length_key(), desc))
    } else {
        match spec_coerce_array_length_value(desc.value.unwrap()) {
            Err(e) => Err(e),
            Ok(new_len) => {
                let new_len_val = JsValView::NumberBits(spec_u32_to_f64_bits(new_len));
                let new_len_desc = PropDescView { value: Some(new_len_val), ..desc };
                let old_len = spec_array_length_obj(obj);
                let old_writable = spec_array_length_writable_obj(obj);
                if new_len >= old_len {
                    Ok(spec_ordinary_define_on_object(obj, spec_length_key(), new_len_desc))
                } else if !old_writable {
                    Ok((false, obj))
                } else {
                    let new_writable = match new_len_desc.writable {
                        Some(false) => false,
                        _ => true,
                    };
                    let temp_desc = if !new_writable {
                        PropDescView { writable: Some(true), ..new_len_desc }
                    } else {
                        new_len_desc
                    };
                    let (succeeded, after_len) =
                        spec_ordinary_define_on_object(obj, spec_length_key(), temp_desc);
                    if !succeeded {
                        Ok((false, obj))
                    } else {
                        let sorted_idxs = spec_collect_sorted_indices(after_len.properties);
                        Ok(spec_shrink_elements_desc(
                            after_len,
                            sorted_idxs,
                            sorted_idxs.len(),
                            new_len,
                            new_writable,
                        ))
                    }
                }
            },
        }
    }
}

pub open spec fn spec_array_set_length(
    h: HeapView,
    a: ObjId,
    desc: PropDescView,
) -> Result<(bool, HeapView), JsError> {
    match spec_array_set_length_on_object(h.objects[a.0 as int], desc) {
        Err(e) => Err(e),
        Ok((ok, new_obj)) => Ok((
            ok,
            HeapView {
                objects: h.objects.update(a.0 as int, new_obj),
                proto_ranks: h.proto_ranks,
            },
        )),
    }
}

pub proof fn lemma_shrink_elements_invariants(
    num_objs: nat,
    orig_props: Seq<PropEntryView>,
    obj: ObjectView,
    sorted_idxs: Seq<u32>,
    k: nat,
    new_len: u32,
    new_writable: bool,
)
    requires
        obj.kind == ObjectKind::Array,
        object_props_wf(num_objs, obj.properties),
        spec_no_duplicate_keys(orig_props),
        k <= sorted_idxs.len(),
        spec_strictly_sorted_u32(sorted_idxs),
        forall|t: int| 0 <= t < sorted_idxs.len() ==> (#[trigger] sorted_idxs[t]) < u32::MAX,
        spec_lookup_prop(obj.properties, spec_length_key())
            == Some(CompleteDescView::Data {
                value: JsValView::NumberBits(spec_u32_to_f64_bits(new_len)),
                writable: true,
                enumerable: false,
                configurable: false,
            }),
        forall|y: u32|
            #[trigger] spec_props_has_array_index(obj.properties, y)
                ==> exists|t: int| 0 <= t < k as int && (#[trigger] sorted_idxs[t]) == y,
        forall|q: PropKeyView|
            q != spec_length_key() ==> (match #[trigger] spec_lookup_prop(orig_props, q) {
                None => spec_lookup_prop(obj.properties, q) is None,
                Some(cd) =>
                    if !spec_complete_configurable(cd) {
                        spec_lookup_prop(obj.properties, q) == Some(cd)
                    } else {
                        spec_lookup_prop(obj.properties, q) is None
                            || spec_lookup_prop(obj.properties, q) == Some(cd)
                    },
            }),
    ensures
        ({
            let (_, fin) =
                spec_shrink_elements_desc(obj, sorted_idxs, k, new_len, new_writable);
            fin.kind == obj.kind
            && fin.prototype == obj.prototype
            && fin.extensible == obj.extensible
            && object_wf(num_objs, fin)
            && (forall|q: PropKeyView|
                q != spec_length_key() ==> (match #[trigger] spec_lookup_prop(orig_props, q) {
                    None => spec_lookup_prop(fin.properties, q) is None,
                    Some(cd) =>
                        if !spec_complete_configurable(cd) {
                            spec_lookup_prop(fin.properties, q) == Some(cd)
                        } else {
                            spec_lookup_prop(fin.properties, q) is None
                                || spec_lookup_prop(fin.properties, q) == Some(cd)
                        },
                }))
        }),
    decreases k,
{
    lemma_length_key_wf();
    if k == 0 || k > sorted_idxs.len() || sorted_idxs[(k - 1) as int] < new_len {
        assert forall|i: int| 0 <= i < obj.properties.len() implies
            match (#[trigger] obj.properties[i]).key {
                PropKeyView::ArrayIndex(aidx) => aidx < new_len,
                _ => true,
            }
        by {
            if let PropKeyView::ArrayIndex(aidx) = obj.properties[i].key {
                assert(spec_props_has_array_index(obj.properties, aidx));
                let t = choose|t: int| 0 <= t < k as int && (#[trigger] sorted_idxs[t]) == aidx;
                if t < (k - 1) as int {
                    assert(sorted_idxs[t] < sorted_idxs[(k - 1) as int]);
                }
                assert(aidx < new_len);
            }
        };
        lemma_u32_f64_bits_roundtrip(new_len);
        assert(array_object_wf(obj));
        if !new_writable {
            let w_false = PropDescView {
                value: None,
                writable: Some(false),
                get: None,
                set: None,
                enumerable: None,
                configurable: None,
            };
            lemma_ordinary_define_preserves_props_wf(num_objs, obj, spec_length_key(), w_false);
            let fin = spec_ordinary_define_on_object(obj, spec_length_key(), w_false).1;
            let new_len_stored = CompleteDescView::Data {
                value: JsValView::NumberBits(spec_u32_to_f64_bits(new_len)),
                writable: false,
                enumerable: false,
                configurable: false,
            };
            lemma_upsert_lookup(obj.properties, spec_length_key(), new_len_stored, spec_length_key());
            assert forall|i: int| 0 <= i < fin.properties.len() implies
                match (#[trigger] fin.properties[i]).key {
                    PropKeyView::ArrayIndex(aidx) => aidx < new_len,
                    _ => true,
                }
            by {
                if let PropKeyView::ArrayIndex(aidx) = fin.properties[i].key {
                    let key_i = fin.properties[i].key;
                    assert(key_i != spec_length_key());
                    lemma_find_prop_spec(obj.properties, spec_length_key());
                    let lidx = spec_find_prop(obj.properties, spec_length_key()).unwrap();
                    assert(fin.properties[i] == obj.properties[i]);
                }
            };
            assert forall|q: PropKeyView| q != spec_length_key() implies
                spec_lookup_prop(fin.properties, q) == spec_lookup_prop(obj.properties, q)
            by {
                lemma_upsert_lookup(obj.properties, spec_length_key(), new_len_stored, q);
            };
        }
    } else {
        let idx = sorted_idxs[(k - 1) as int];
        assert(idx < u32::MAX);
        let elem_key = PropKeyView::ArrayIndex(idx);
        assert(elem_key != spec_length_key());
        let (del_ok, after_del) = spec_ordinary_delete_on_object(obj, elem_key);
        if !del_ok {
            assert(after_del == obj);
            let stopped_len: u32 = add(idx, 1u32);
            lemma_u32_f64_bits_roundtrip(stopped_len);
            let stop_desc = PropDescView {
                value: Some(JsValView::NumberBits(spec_u32_to_f64_bits(stopped_len))),
                writable: if !new_writable { Some(false) } else { None },
                get: None,
                set: None,
                enumerable: None,
                configurable: None,
            };
            lemma_ordinary_define_preserves_props_wf(
                num_objs,
                after_del,
                spec_length_key(),
                stop_desc,
            );
            let (_, stopped_obj) =
                spec_ordinary_define_on_object(after_del, spec_length_key(), stop_desc);
            let stop_stored = CompleteDescView::Data {
                value: JsValView::NumberBits(spec_u32_to_f64_bits(stopped_len)),
                writable: new_writable,
                enumerable: false,
                configurable: false,
            };
            lemma_upsert_lookup(
                after_del.properties,
                spec_length_key(),
                stop_stored,
                spec_length_key(),
            );
            assert forall|i: int| 0 <= i < stopped_obj.properties.len() implies
                match (#[trigger] stopped_obj.properties[i]).key {
                    PropKeyView::ArrayIndex(aidx) => aidx < stopped_len,
                    _ => true,
                }
            by {
                if let PropKeyView::ArrayIndex(aidx) = stopped_obj.properties[i].key {
                    lemma_find_prop_spec(after_del.properties, spec_length_key());
                    assert(stopped_obj.properties[i] == after_del.properties[i]);
                    assert(spec_props_has_array_index(obj.properties, aidx));
                    let t = choose|t: int| 0 <= t < k as int && (#[trigger] sorted_idxs[t]) == aidx;
                    if t < (k - 1) as int {
                        assert(sorted_idxs[t] < sorted_idxs[(k - 1) as int]);
                    }
                    assert(aidx <= idx);
                    assert(aidx < stopped_len);
                }
            };
            assert forall|q: PropKeyView| q != spec_length_key() implies
                spec_lookup_prop(stopped_obj.properties, q) == spec_lookup_prop(obj.properties, q)
            by {
                lemma_upsert_lookup(after_del.properties, spec_length_key(), stop_stored, q);
            };
        } else {
            // `elem_key` was configurable and removed from `obj.properties`
            lemma_find_prop_spec(obj.properties, elem_key);
            let next_props = after_del.properties;
            lemma_remove_lookup(obj.properties, elem_key, elem_key);
            lemma_remove_lookup(obj.properties, elem_key, spec_length_key());
            match spec_find_prop(obj.properties, elem_key) {
                None => {},
                Some(ridx) => {
                    let ri = ridx as int;
                    assert forall|m: int| 0 <= m < next_props.len() implies
                        prop_key_wf((#[trigger] next_props[m]).key)
                        && complete_desc_refs_wf(num_objs, next_props[m].desc)
                    by {
                        let src = if m < ri { m } else { m + 1 };
                        assert(next_props[m] == obj.properties[src]);
                    };
                },
            }
            assert forall|y: u32|
                #[trigger] spec_props_has_array_index(after_del.properties, y)
                implies exists|t: int| 0 <= t < (k - 1) as int && (#[trigger] sorted_idxs[t]) == y
            by {
                let m = choose|m: int| 0 <= m < after_del.properties.len()
                    && (#[trigger] after_del.properties[m]).key == PropKeyView::ArrayIndex(y);
                lemma_remove_lookup(obj.properties, elem_key, PropKeyView::ArrayIndex(y));
                lemma_find_prop_spec(after_del.properties, PropKeyView::ArrayIndex(y));
                assert(spec_lookup_prop(after_del.properties, PropKeyView::ArrayIndex(y)) is Some);
                assert(y != idx);
                lemma_find_prop_spec(obj.properties, PropKeyView::ArrayIndex(y));
                let om = spec_find_prop(obj.properties, PropKeyView::ArrayIndex(y)).unwrap();
                assert(obj.properties[om as int].key == PropKeyView::ArrayIndex(y));
                assert(spec_props_has_array_index(obj.properties, y));
                let t = choose|t: int| 0 <= t < k as int && (#[trigger] sorted_idxs[t]) == y;
                assert(t != (k - 1) as int);
                assert(0 <= t < (k - 1) as int);
            };
            assert forall|q: PropKeyView| q != spec_length_key() implies
                match #[trigger] spec_lookup_prop(orig_props, q) {
                    None => spec_lookup_prop(after_del.properties, q) is None,
                    Some(cd) =>
                        if !spec_complete_configurable(cd) {
                            spec_lookup_prop(after_del.properties, q) == Some(cd)
                        } else {
                            spec_lookup_prop(after_del.properties, q) is None
                                || spec_lookup_prop(after_del.properties, q) == Some(cd)
                        },
                }
            by {
                lemma_remove_lookup(obj.properties, elem_key, q);
                if q == elem_key {
                    // Since del_ok == true, if elem_key was in obj.properties it had configurable == true!
                    if let Some(cd) = spec_lookup_prop(orig_props, q) {
                        assert(spec_complete_configurable(cd));
                    }
                }
            };
            lemma_shrink_elements_invariants(
                num_objs,
                orig_props,
                after_del,
                sorted_idxs,
                (k - 1) as nat,
                new_len,
                new_writable,
            );
        }
    }
}

pub proof fn lemma_array_set_length_preserves_wf(
    num_objs: nat,
    obj: ObjectView,
    desc: PropDescView,
)
    requires
        obj.kind == ObjectKind::Array,
        object_wf(num_objs, obj),
        prop_desc_wf(desc),
        prop_desc_refs_wf(num_objs, desc),
    ensures
        match spec_array_set_length_on_object(obj, desc) {
            Err(_) => true,
            Ok((_, fin)) =>
                fin.kind == ObjectKind::Array
                && fin.prototype == obj.prototype
                && fin.extensible == obj.extensible
                && object_wf(num_objs, fin),
        },
{
    lemma_length_key_wf();
    let old_len = spec_array_length_obj(obj);
    if desc.value is None {
        lemma_ordinary_define_preserves_props_wf(num_objs, obj, spec_length_key(), desc);
        let (ok, fin) = spec_ordinary_define_on_object(obj, spec_length_key(), desc);
        if ok {
            let cur_len = spec_lookup_prop(obj.properties, spec_length_key()).unwrap();
            let (_, next_len_opt) =
                spec_validate_and_apply_property_descriptor(true, obj.extensible, desc, Some(cur_len));
            let next_len = next_len_opt.unwrap();
            lemma_upsert_lookup(obj.properties, spec_length_key(), next_len, spec_length_key());
            lemma_find_prop_spec(obj.properties, spec_length_key());
            assert forall|i: int| 0 <= i < fin.properties.len() implies
                match (#[trigger] fin.properties[i]).key {
                    PropKeyView::ArrayIndex(aidx) => aidx < old_len,
                    _ => true,
                }
            by {
                if let PropKeyView::ArrayIndex(aidx) = fin.properties[i].key {
                    assert(fin.properties[i] == obj.properties[i]);
                }
            };
        }
    } else {
        if let Ok(new_len) = spec_coerce_array_length_value(desc.value.unwrap()) {
            lemma_u32_f64_bits_roundtrip(new_len);
            lemma_u32_f64_bits_roundtrip(old_len);
            let new_len_val = JsValView::NumberBits(spec_u32_to_f64_bits(new_len));
            let new_len_desc = PropDescView { value: Some(new_len_val), ..desc };
            if new_len >= old_len {
                lemma_ordinary_define_preserves_props_wf(
                    num_objs,
                    obj,
                    spec_length_key(),
                    new_len_desc,
                );
                let (ok, fin) =
                    spec_ordinary_define_on_object(obj, spec_length_key(), new_len_desc);
                if ok {
                    let cur_len = spec_lookup_prop(obj.properties, spec_length_key()).unwrap();
                    let (_, next_len_opt) = spec_validate_and_apply_property_descriptor(
                        true,
                        obj.extensible,
                        new_len_desc,
                        Some(cur_len),
                    );
                    let next_len = next_len_opt.unwrap();
                    lemma_upsert_lookup(
                        obj.properties,
                        spec_length_key(),
                        next_len,
                        spec_length_key(),
                    );
                    lemma_find_prop_spec(obj.properties, spec_length_key());
                    assert forall|i: int| 0 <= i < fin.properties.len() implies
                        match (#[trigger] fin.properties[i]).key {
                            PropKeyView::ArrayIndex(aidx) => aidx < new_len,
                            _ => true,
                        }
                    by {
                        if let PropKeyView::ArrayIndex(aidx) = fin.properties[i].key {
                            assert(fin.properties[i] == obj.properties[i]);
                            assert(aidx < old_len);
                        }
                    };
                }
            } else if !spec_array_length_writable_obj(obj) {
            } else {
                let new_writable = match new_len_desc.writable {
                    Some(false) => false,
                    _ => true,
                };
                let temp_desc = if !new_writable {
                    PropDescView { writable: Some(true), ..new_len_desc }
                } else {
                    new_len_desc
                };
                lemma_ordinary_define_preserves_props_wf(
                    num_objs,
                    obj,
                    spec_length_key(),
                    temp_desc,
                );
                let (succeeded, after_len) =
                    spec_ordinary_define_on_object(obj, spec_length_key(), temp_desc);
                if succeeded {
                    let cur_len = spec_lookup_prop(obj.properties, spec_length_key()).unwrap();
                    let (_, next_len_opt) = spec_validate_and_apply_property_descriptor(
                        true,
                        obj.extensible,
                        temp_desc,
                        Some(cur_len),
                    );
                    let next_len = next_len_opt.unwrap();
                    lemma_upsert_lookup(
                        obj.properties,
                        spec_length_key(),
                        next_len,
                        spec_length_key(),
                    );
                    assert forall|q: PropKeyView| q != spec_length_key() implies
                        spec_lookup_prop(after_len.properties, q)
                            == spec_lookup_prop(obj.properties, q)
                    by {
                        lemma_upsert_lookup(obj.properties, spec_length_key(), next_len, q);
                    };
                    crate::ordinary::lemma_collect_sorted_indices_props(after_len.properties);
                    let sorted_idxs = spec_collect_sorted_indices(after_len.properties);
                    assert forall|t: int| 0 <= t < sorted_idxs.len() implies
                        (#[trigger] sorted_idxs[t]) < u32::MAX
                    by {
                        let y = sorted_idxs[t];
                        assert(spec_seq_u32_contains(sorted_idxs, y));
                        assert(spec_props_has_array_index(after_len.properties, y));
                        let m = choose|m: int| 0 <= m < after_len.properties.len()
                            && (#[trigger] after_len.properties[m]).key == PropKeyView::ArrayIndex(y);
                        assert(prop_key_wf(after_len.properties[m].key));
                    };
                    assert forall|y: u32|
                        #[trigger] spec_props_has_array_index(after_len.properties, y)
                        implies exists|t: int| 0 <= t < sorted_idxs.len() && (#[trigger] sorted_idxs[t]) == y
                    by {
                        assert(spec_seq_u32_contains(sorted_idxs, y));
                    };
                    lemma_shrink_elements_invariants(
                        num_objs,
                        obj.properties,
                        after_len,
                        sorted_idxs,
                        sorted_idxs.len(),
                        new_len,
                        new_writable,
                    );
                }
            }
        }
    }
}

fn shrink_elements_desc_exec(
    obj: &mut JsObject,
    sorted_idxs: &Vec<u32>,
    new_len: u32,
    new_writable: bool,
) -> (res: bool)
    requires
        object_props_wf(0, old(obj)@ .properties) || spec_no_duplicate_keys(old(obj)@.properties),
        forall|t: int| 0 <= t < sorted_idxs@.len() ==> (#[trigger] sorted_idxs@[t]) < u32::MAX,
    ensures
        (res, final(obj)@)
            == spec_shrink_elements_desc(
                old(obj)@,
                sorted_idxs@,
                sorted_idxs@.len(),
                new_len,
                new_writable,
            ),
{
    let lkey = length_prop_key();
    let mut k: usize = sorted_idxs.len();
    while k > 0 && sorted_idxs[k - 1] >= new_len
        invariant
            k <= sorted_idxs@.len(),
            lkey@ == spec_length_key(),
            forall|t: int| 0 <= t < sorted_idxs@.len() ==> (#[trigger] sorted_idxs@[t]) < u32::MAX,
            spec_shrink_elements_desc(
                old(obj)@,
                sorted_idxs@,
                sorted_idxs@.len(),
                new_len,
                new_writable,
            ) == spec_shrink_elements_desc(
                obj@,
                sorted_idxs@,
                k as nat,
                new_len,
                new_writable,
            ),
        decreases k,
    {
        let idx = sorted_idxs[k - 1];
        proof {
            assert(sorted_idxs@[(k - 1) as int] == idx);
            assert(idx < u32::MAX);
        }
        let elem_key = PropKey::ArrayIndex(idx);
        let ghost pre_del = obj@;
        let del_ok = apply_ordinary_delete_on_object(obj, &elem_key);
        if !del_ok {
            let ghost after_del_view = obj@;
            let stopped_len: u32 = idx + 1u32;
            let stop_desc = PropertyDescriptor {
                value: Some(js_val_from_u32(stopped_len)),
                writable: if !new_writable { Some(false) } else { None },
                get: None,
                set: None,
                enumerable: None,
                configurable: None,
            };
            let _ = apply_ordinary_define_on_object(obj, &lkey, &stop_desc);
            proof {
                assert(stop_desc@ == (PropDescView {
                    value: Some(JsValView::NumberBits(spec_u32_to_f64_bits(stopped_len))),
                    writable: if !new_writable { Some(false) } else { None },
                    get: None,
                    set: None,
                    enumerable: None,
                    configurable: None,
                }));
                assert(spec_shrink_elements_desc(
                    pre_del,
                    sorted_idxs@,
                    k as nat,
                    new_len,
                    new_writable,
                ) == (false, spec_ordinary_define_on_object(after_del_view, spec_length_key(), stop_desc@).1));
            }
            return false;
        }
        proof {
            reveal_with_fuel(spec_shrink_elements_desc, 2);
        }
        k -= 1;
    }
    if !new_writable {
        let w_false = PropertyDescriptor {
            value: None,
            writable: Some(false),
            get: None,
            set: None,
            enumerable: None,
            configurable: None,
        };
        let _ = apply_ordinary_define_on_object(obj, &lkey, &w_false);
    }
    proof {
        reveal_with_fuel(spec_shrink_elements_desc, 2);
    }
    true
}

fn apply_array_set_length_on_object(
    obj: &mut JsObject,
    desc: &PropertyDescriptor,
    Ghost(num_objs): Ghost<nat>,
) -> (res: Result<bool, JsError>)
    requires
        old(obj)@.kind == ObjectKind::Array,
        object_wf(num_objs, old(obj)@),
        prop_desc_wf(desc@),
        prop_desc_refs_wf(num_objs, desc@),
    ensures
        match (res, spec_array_set_length_on_object(old(obj)@, desc@)) {
            (Err(e1), Err(e2)) => e1 == e2 && final(obj)@ == old(obj)@,
            (Ok(b1), Ok((b2, fin_spec))) =>
                b1 == b2
                && final(obj)@ == fin_spec
                && final(obj)@.kind == ObjectKind::Array
                && final(obj)@.prototype == old(obj)@.prototype
                && final(obj)@.extensible == old(obj)@.extensible
                && object_wf(num_objs, final(obj)@),
            _ => false,
        },
{
    let ghost orig_view = obj@;
    proof {
        lemma_array_set_length_preserves_wf(num_objs, orig_view, desc@);
    }
    let lkey = length_prop_key();
    if desc.value.is_none() {
        let ok = apply_ordinary_define_on_object(obj, &lkey, desc);
        return Ok(ok);
    }
    let raw_val = desc.value.as_ref().unwrap();
    let new_len = match coerce_array_length_value(raw_val) {
        Err(e) => return Err(e),
        Ok(n) => n,
    };
    let new_len_desc = PropertyDescriptor {
        value: Some(js_val_from_u32(new_len)),
        writable: desc.writable,
        get: desc.get,
        set: desc.set,
        enumerable: desc.enumerable,
        configurable: desc.configurable,
    };
    let (old_len, old_writable) = read_array_length_and_writable(obj);
    if new_len >= old_len {
        let ok = apply_ordinary_define_on_object(obj, &lkey, &new_len_desc);
        return Ok(ok);
    }
    if !old_writable {
        return Ok(false);
    }
    let new_writable = match new_len_desc.writable {
        Some(false) => false,
        _ => true,
    };
    let temp_desc = if !new_writable {
        PropertyDescriptor {
            value: Some(js_val_from_u32(new_len)),
            writable: Some(true),
            get: new_len_desc.get,
            set: new_len_desc.set,
            enumerable: new_len_desc.enumerable,
            configurable: new_len_desc.configurable,
        }
    } else {
        new_len_desc
    };
    let succeeded = apply_ordinary_define_on_object(obj, &lkey, &temp_desc);
    if !succeeded {
        return Ok(false);
    }
    proof {
        lemma_length_key_wf();
        lemma_u32_f64_bits_roundtrip(new_len);
        lemma_ordinary_define_preserves_props_wf(num_objs, orig_view, spec_length_key(), temp_desc@);
    }
    let sorted_idxs = collect_sorted_array_indices(&obj.properties);
    proof {
        assert forall|t: int| 0 <= t < sorted_idxs@.len() implies (#[trigger] sorted_idxs@[t]) < u32::MAX by {
            let y = sorted_idxs@[t];
            assert(spec_seq_u32_contains(sorted_idxs@, y));
            assert(spec_props_has_array_index(obj@.properties, y));
            let m = choose|m: int| 0 <= m < obj@.properties.len()
                && (#[trigger] obj@.properties[m]).key == PropKeyView::ArrayIndex(y);
            assert(prop_key_wf(obj@.properties[m].key));
        };
    }
    let shrink_ok = shrink_elements_desc_exec(obj, &sorted_idxs, new_len, new_writable);
    Ok(shrink_ok)
}

pub proof fn lemma_array_set_length_essential(
    h: HeapView,
    a: ObjId,
    desc: PropDescView,
    o: ObjId,
    k: PropKeyView,
)
    requires
        heap_wf(h),
        valid_obj(h, a),
        valid_obj(h, o),
        h.objects[a.0 as int].kind == ObjectKind::Array,
        prop_desc_wf(desc),
        prop_desc_refs_wf(h.objects.len() as nat, desc),
    ensures
        match spec_array_set_length(h, a, desc) {
            Err(_) => true,
            Ok((_, nh)) => spec_essential_invariants_hold(h, nh, o, k),
        },
{
    lemma_length_key_wf();
    let num_objs = h.objects.len() as nat;
    let obj = h.objects[a.0 as int];
    assert(object_wf(num_objs, obj));
    lemma_array_set_length_preserves_wf(num_objs, obj, desc);

    if let Ok((_, nh)) = spec_array_set_length(h, a, desc) {
        let (_, fin) = spec_array_set_length_on_object(obj, desc).unwrap();
        assert forall|i: int| 0 <= i < nh.objects.len() implies
            object_wf(nh.objects.len() as nat, #[trigger] nh.objects[i])
        by {
            if i == a.0 as int {
                assert(nh.objects[i] == fin);
            } else {
                assert(nh.objects[i] == h.objects[i]);
            }
        };

        if a != o {
            if let Some(old_d) = spec_lookup_prop(h.objects[o.0 as int].properties, k) {
                if !spec_complete_configurable(old_d) {
                    lemma_nonconfigurable_preserved_refl(old_d);
                }
            }
        } else {
            let old_len = spec_array_length_obj(obj);
            let old_writable = spec_array_length_writable_obj(obj);
            if desc.value is None {
                lemma_ordinary_define_obj_essential(obj, spec_length_key(), desc, k);
            } else {
                let new_len = spec_coerce_array_length_value(desc.value.unwrap()).unwrap();
                lemma_u32_f64_bits_roundtrip(new_len);
                lemma_u32_f64_bits_roundtrip(old_len);
                let new_len_val = JsValView::NumberBits(spec_u32_to_f64_bits(new_len));
                let new_len_desc = PropDescView { value: Some(new_len_val), ..desc };
                if new_len >= old_len {
                    lemma_ordinary_define_obj_essential(obj, spec_length_key(), new_len_desc, k);
                } else if !old_writable {
                    if let Some(old_d) = spec_lookup_prop(obj.properties, k) {
                        if !spec_complete_configurable(old_d) {
                            lemma_nonconfigurable_preserved_refl(old_d);
                        }
                    }
                } else {
                    let new_writable = match new_len_desc.writable {
                        Some(false) => false,
                        _ => true,
                    };
                    let temp_desc = if !new_writable {
                        PropDescView { writable: Some(true), ..new_len_desc }
                    } else {
                        new_len_desc
                    };
                    let (succeeded, after_len) =
                        spec_ordinary_define_on_object(obj, spec_length_key(), temp_desc);
                    if !succeeded {
                        if let Some(old_d) = spec_lookup_prop(obj.properties, k) {
                            if !spec_complete_configurable(old_d) {
                                lemma_nonconfigurable_preserved_refl(old_d);
                            }
                        }
                    } else {
                        lemma_ordinary_define_preserves_props_wf(
                            num_objs,
                            obj,
                            spec_length_key(),
                            temp_desc,
                        );
                        let cur_len = spec_lookup_prop(obj.properties, spec_length_key()).unwrap();
                        let (_, next_len_opt) = spec_validate_and_apply_property_descriptor(
                            true,
                            obj.extensible,
                            temp_desc,
                            Some(cur_len),
                        );
                        let next_len = next_len_opt.unwrap();
                        lemma_upsert_lookup(
                            obj.properties,
                            spec_length_key(),
                            next_len,
                            spec_length_key(),
                        );
                        assert forall|q: PropKeyView| q != spec_length_key() implies
                            spec_lookup_prop(after_len.properties, q)
                                == spec_lookup_prop(obj.properties, q)
                        by {
                            lemma_upsert_lookup(obj.properties, spec_length_key(), next_len, q);
                        };
                        lemma_collect_sorted_indices_props(after_len.properties);
                        let sorted_idxs = spec_collect_sorted_indices(after_len.properties);
                        assert forall|t: int| 0 <= t < sorted_idxs.len() implies
                            (#[trigger] sorted_idxs[t]) < u32::MAX
                        by {
                            let y = sorted_idxs[t];
                            assert(spec_seq_u32_contains(sorted_idxs, y));
                            assert(spec_props_has_array_index(after_len.properties, y));
                            let m = choose|m: int| 0 <= m < after_len.properties.len()
                                && (#[trigger] after_len.properties[m]).key == PropKeyView::ArrayIndex(y);
                            assert(prop_key_wf(after_len.properties[m].key));
                        };
                        assert forall|y: u32|
                            #[trigger] spec_props_has_array_index(after_len.properties, y)
                            implies exists|t: int| 0 <= t < sorted_idxs.len() && (#[trigger] sorted_idxs[t]) == y
                        by {
                            assert(spec_seq_u32_contains(sorted_idxs, y));
                        };
                        lemma_shrink_elements_invariants(
                            num_objs,
                            obj.properties,
                            after_len,
                            sorted_idxs,
                            sorted_idxs.len(),
                            new_len,
                            new_writable,
                        );
                        if k == spec_length_key() {
                            assert(array_object_wf(fin));
                        } else {
                            if let Some(old_d) = spec_lookup_prop(obj.properties, k) {
                                if !spec_complete_configurable(old_d) {
                                    lemma_nonconfigurable_preserved_refl(old_d);
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

/// ECMA-262 §10.4.2.4 `ArraySetLength ( A, Desc )`, proved `exec == spec`, `Heap::wf`-preserving,
/// and §6.1.7.3-preserving across all objects and keys.
pub fn array_set_length(
    heap: &mut Heap,
    a: ObjId,
    desc: &PropertyDescriptor,
) -> (res: Result<bool, JsError>)
    requires
        old(heap).wf(),
        old(heap).valid_obj(a),
        old(heap)@.objects[a.0 as int].kind == ObjectKind::Array,
        old(heap).desc_wf(desc@),
    ensures
        final(heap).wf(),
        spec_all_essential_invariants(old(heap)@, final(heap)@),
        match (res, spec_array_set_length(old(heap)@, a, desc@)) {
            (Err(e1), Err(e2)) => e1 == e2 && final(heap)@ == old(heap)@,
            (Ok(b1), Ok((b2, h_spec))) => b1 == b2 && final(heap)@ == h_spec,
            _ => false,
        },
{
    let ghost old_h = heap@;
    let ghost num_objs = old_h.objects.len() as nat;
    proof {
        assert(object_wf(num_objs, old_h.objects[a.0 as int]));
    }
    let mut obj = clone_js_object(&heap.objects[a.0]);
    match apply_array_set_length_on_object(&mut obj, desc, Ghost(num_objs)) {
        Err(e) => {
            proof {
                lemma_all_essential_invariants_refl(heap@);
            }
            Err(e)
        },
        Ok(ok) => {
            let ghost updated_view = obj@;
            heap.objects.set(a.0, obj);
            proof {
                assert(heap@.objects =~= old_h.objects.update(a.0 as int, updated_view));
                assert forall|i: int| 0 <= i < heap@.objects.len() implies
                    object_wf(heap@.objects.len() as nat, #[trigger] heap@.objects[i])
                by {
                    if i == a.0 as int {
                        assert(heap@.objects[i] == updated_view);
                    } else {
                        assert(heap@.objects[i] == old_h.objects[i]);
                        assert(object_wf(num_objs, old_h.objects[i]));
                    }
                };
                assert forall|obs_o: ObjId, obs_k: PropKeyView| valid_obj(old_h, obs_o) implies
                    #[trigger] spec_essential_invariants_hold(old_h, heap@, obs_o, obs_k)
                by {
                    lemma_array_set_length_essential(old_h, a, desc@, obs_o, obs_k);
                };
            }
            Ok(ok)
        },
    }
}

// ---------------------------------------------------------------------------------------
// §10.4.2.1 Array `[[DefineOwnProperty]] ( P, Desc )`
// ---------------------------------------------------------------------------------------

/// ECMA-262 §10.4.2.1 Array `[[DefineOwnProperty]]` on object `obj`.
pub open spec fn spec_array_define_on_object(
    obj: ObjectView,
    key: PropKeyView,
    desc: PropDescView,
) -> Result<(bool, ObjectView), JsError> {
    if key == spec_length_key() {
        spec_array_set_length_on_object(obj, desc)
    } else {
        match key {
            PropKeyView::ArrayIndex(index) => {
                let old_len = spec_array_length_obj(obj);
                let old_writable = spec_array_length_writable_obj(obj);
                if index >= old_len && !old_writable {
                    Ok((false, obj))
                } else {
                    let (succeeded, after_elem) = spec_ordinary_define_on_object(obj, key, desc);
                    if !succeeded {
                        Ok((false, obj))
                    } else if index >= old_len {
                        let new_len: u32 = if index < u32::MAX { add(index, 1u32) } else { u32::MAX };
                        let len_update = PropDescView {
                            value: Some(JsValView::NumberBits(spec_u32_to_f64_bits(new_len))),
                            writable: None,
                            get: None,
                            set: None,
                            enumerable: None,
                            configurable: None,
                        };
                        let (_, after_len) = spec_ordinary_define_on_object(
                            after_elem,
                            spec_length_key(),
                            len_update,
                        );
                        Ok((true, after_len))
                    } else {
                        Ok((true, after_elem))
                    }
                }
            },
            _ => Ok(spec_ordinary_define_on_object(obj, key, desc)),
        }
    }
}

pub open spec fn spec_array_define_own_property(
    h: HeapView,
    a: ObjId,
    key: PropKeyView,
    desc: PropDescView,
) -> Result<(bool, HeapView), JsError> {
    match spec_array_define_on_object(h.objects[a.0 as int], key, desc) {
        Err(e) => Err(e),
        Ok((ok, new_obj)) => Ok((
            ok,
            HeapView {
                objects: h.objects.update(a.0 as int, new_obj),
                proto_ranks: h.proto_ranks,
            },
        )),
    }
}

pub proof fn lemma_array_define_preserves_wf(
    num_objs: nat,
    obj: ObjectView,
    key: PropKeyView,
    desc: PropDescView,
)
    requires
        obj.kind == ObjectKind::Array,
        object_wf(num_objs, obj),
        prop_key_wf(key),
        prop_desc_wf(desc),
        prop_desc_refs_wf(num_objs, desc),
    ensures
        match spec_array_define_on_object(obj, key, desc) {
            Err(_) => true,
            Ok((_, fin)) =>
                fin.kind == ObjectKind::Array
                && fin.prototype == obj.prototype
                && fin.extensible == obj.extensible
                && object_wf(num_objs, fin),
        },
{
    lemma_length_key_wf();
    if key == spec_length_key() {
        lemma_array_set_length_preserves_wf(num_objs, obj, desc);
    } else {
        let old_len = spec_array_length_obj(obj);
        let old_writable = spec_array_length_writable_obj(obj);
        match key {
            PropKeyView::ArrayIndex(index) => {
                assert(index < u32::MAX);
                if !(index >= old_len && !old_writable) {
                    lemma_ordinary_define_preserves_props_wf(num_objs, obj, key, desc);
                    let (succeeded, after_elem) = spec_ordinary_define_on_object(obj, key, desc);
                    if succeeded {
                        let cur_elem = spec_lookup_prop(obj.properties, key);
                        let (_, stored_elem_opt) = spec_validate_and_apply_property_descriptor(
                            true,
                            obj.extensible,
                            desc,
                            cur_elem,
                        );
                        let stored_elem = stored_elem_opt.unwrap();
                        lemma_upsert_lookup(obj.properties, key, stored_elem, spec_length_key());
                        if index >= old_len {
                            let new_len: u32 = add(index, 1u32);
                            lemma_u32_f64_bits_roundtrip(new_len);
                            let len_update = PropDescView {
                                value: Some(JsValView::NumberBits(spec_u32_to_f64_bits(new_len))),
                                writable: None,
                                get: None,
                                set: None,
                                enumerable: None,
                                configurable: None,
                            };
                            lemma_ordinary_define_preserves_props_wf(
                                num_objs,
                                after_elem,
                                spec_length_key(),
                                len_update,
                            );
                            let (_, after_len) = spec_ordinary_define_on_object(
                                after_elem,
                                spec_length_key(),
                                len_update,
                            );
                            let stored_len = CompleteDescView::Data {
                                value: JsValView::NumberBits(spec_u32_to_f64_bits(new_len)),
                                writable: true,
                                enumerable: false,
                                configurable: false,
                            };
                            lemma_upsert_lookup(
                                after_elem.properties,
                                spec_length_key(),
                                stored_len,
                                spec_length_key(),
                            );
                            assert forall|i: int| 0 <= i < after_len.properties.len() implies
                                match (#[trigger] after_len.properties[i]).key {
                                    PropKeyView::ArrayIndex(aidx) => aidx < new_len,
                                    _ => true,
                                }
                            by {
                                if let PropKeyView::ArrayIndex(aidx) = after_len.properties[i].key {
                                    lemma_find_prop_spec(after_elem.properties, spec_length_key());
                                    assert(after_len.properties[i] == after_elem.properties[i]);
                                    lemma_find_prop_spec(obj.properties, key);
                                    match spec_find_prop(obj.properties, key) {
                                        Some(eidx) => {
                                            if i == eidx as int {
                                                assert(aidx == index);
                                            } else {
                                                assert(after_elem.properties[i] == obj.properties[i]);
                                                assert(aidx < old_len);
                                            }
                                        },
                                        None => {
                                            if i < obj.properties.len() {
                                                assert(after_elem.properties[i] == obj.properties[i]);
                                                assert(aidx < old_len);
                                            } else {
                                                assert(aidx == index);
                                            }
                                        },
                                    }
                                    assert(aidx < new_len);
                                }
                            };
                        } else {
                            assert forall|i: int| 0 <= i < after_elem.properties.len() implies
                                match (#[trigger] after_elem.properties[i]).key {
                                    PropKeyView::ArrayIndex(aidx) => aidx < old_len,
                                    _ => true,
                                }
                            by {
                                if let PropKeyView::ArrayIndex(aidx) = after_elem.properties[i].key {
                                    lemma_find_prop_spec(obj.properties, key);
                                    match spec_find_prop(obj.properties, key) {
                                        Some(eidx) => {
                                            if i == eidx as int {
                                                assert(aidx == index);
                                            } else {
                                                assert(after_elem.properties[i] == obj.properties[i]);
                                            }
                                        },
                                        None => {
                                            if i < obj.properties.len() {
                                                assert(after_elem.properties[i] == obj.properties[i]);
                                            } else {
                                                assert(aidx == index);
                                            }
                                        },
                                    }
                                }
                            };
                        }
                    }
                }
            },
            _ => {
                lemma_ordinary_define_preserves_props_wf(num_objs, obj, key, desc);
                let (succeeded, after_prop) = spec_ordinary_define_on_object(obj, key, desc);
                if succeeded {
                    let cur_p = spec_lookup_prop(obj.properties, key);
                    let (_, stored_p_opt) = spec_validate_and_apply_property_descriptor(
                        true,
                        obj.extensible,
                        desc,
                        cur_p,
                    );
                    let stored_p = stored_p_opt.unwrap();
                    lemma_upsert_lookup(obj.properties, key, stored_p, spec_length_key());
                    assert forall|i: int| 0 <= i < after_prop.properties.len() implies
                        match (#[trigger] after_prop.properties[i]).key {
                            PropKeyView::ArrayIndex(aidx) => aidx < old_len,
                            _ => true,
                        }
                    by {
                        if let PropKeyView::ArrayIndex(aidx) = after_prop.properties[i].key {
                            lemma_find_prop_spec(obj.properties, key);
                            match spec_find_prop(obj.properties, key) {
                                Some(pidx) => {
                                    assert(i != pidx as int);
                                    assert(after_prop.properties[i] == obj.properties[i]);
                                },
                                None => {
                                    assert(i < obj.properties.len());
                                    assert(after_prop.properties[i] == obj.properties[i]);
                                },
                            }
                        }
                    };
                }
            },
        }
    }
}

pub proof fn lemma_array_define_essential(
    h: HeapView,
    a: ObjId,
    key: PropKeyView,
    desc: PropDescView,
    o: ObjId,
    k: PropKeyView,
)
    requires
        heap_wf(h),
        valid_obj(h, a),
        valid_obj(h, o),
        h.objects[a.0 as int].kind == ObjectKind::Array,
        prop_key_wf(key),
        prop_desc_wf(desc),
        prop_desc_refs_wf(h.objects.len() as nat, desc),
    ensures
        match spec_array_define_own_property(h, a, key, desc) {
            Err(_) => true,
            Ok((_, nh)) => spec_essential_invariants_hold(h, nh, o, k),
        },
{
    lemma_length_key_wf();
    if key == spec_length_key() {
        lemma_array_set_length_essential(h, a, desc, o, k);
    } else {
        let num_objs = h.objects.len() as nat;
        let obj = h.objects[a.0 as int];
        assert(object_wf(num_objs, obj));
        lemma_array_define_preserves_wf(num_objs, obj, key, desc);
        let (_, nh) = spec_array_define_own_property(h, a, key, desc).unwrap();
        let (_, fin) = spec_array_define_on_object(obj, key, desc).unwrap();
        assert forall|i: int| 0 <= i < nh.objects.len() implies
            object_wf(nh.objects.len() as nat, #[trigger] nh.objects[i])
        by {
            if i == a.0 as int {
                assert(nh.objects[i] == fin);
            } else {
                assert(nh.objects[i] == h.objects[i]);
            }
        };

        if a != o {
            if let Some(old_d) = spec_lookup_prop(h.objects[o.0 as int].properties, k) {
                if !spec_complete_configurable(old_d) {
                    lemma_nonconfigurable_preserved_refl(old_d);
                }
            }
        } else {
            match key {
                PropKeyView::ArrayIndex(index) => {
                    let old_len = spec_array_length_obj(obj);
                    let old_writable = spec_array_length_writable_obj(obj);
                    if index >= old_len && !old_writable {
                        if let Some(old_d) = spec_lookup_prop(obj.properties, k) {
                            if !spec_complete_configurable(old_d) {
                                lemma_nonconfigurable_preserved_refl(old_d);
                            }
                        }
                    } else {
                        lemma_ordinary_define_obj_essential(obj, key, desc, k);
                        let (succeeded, after_elem) =
                            spec_ordinary_define_on_object(obj, key, desc);
                        if !succeeded {
                            if let Some(old_d) = spec_lookup_prop(obj.properties, k) {
                                if !spec_complete_configurable(old_d) {
                                    lemma_nonconfigurable_preserved_refl(old_d);
                                }
                            }
                        } else if index >= old_len {
                            lemma_ordinary_define_preserves_props_wf(num_objs, obj, key, desc);
                            let cur_elem = spec_lookup_prop(obj.properties, key);
                            let (_, stored_elem_opt) = spec_validate_and_apply_property_descriptor(
                                true,
                                obj.extensible,
                                desc,
                                cur_elem,
                            );
                            let stored_elem = stored_elem_opt.unwrap();
                            lemma_upsert_lookup(
                                obj.properties,
                                key,
                                stored_elem,
                                spec_length_key(),
                            );
                            let new_len = add(index, 1u32);
                            let len_update = PropDescView {
                                value: Some(JsValView::NumberBits(spec_u32_to_f64_bits(new_len))),
                                writable: None,
                                get: None,
                                set: None,
                                enumerable: None,
                                configurable: None,
                            };
                            let stored_len = CompleteDescView::Data {
                                value: JsValView::NumberBits(spec_u32_to_f64_bits(new_len)),
                                writable: true,
                                enumerable: false,
                                configurable: false,
                            };
                            assert(spec_ordinary_define_on_object(
                                after_elem,
                                spec_length_key(),
                                len_update,
                            ).1.properties == spec_upsert_prop(
                                after_elem.properties,
                                spec_length_key(),
                                stored_len,
                            ));
                            lemma_upsert_lookup(
                                after_elem.properties,
                                spec_length_key(),
                                stored_len,
                                k,
                            );
                            if k == spec_length_key() {
                                assert(array_object_wf(fin));
                            }
                        }
                    }
                },
                _ => {
                    lemma_ordinary_define_obj_essential(obj, key, desc, k);
                },
            }
        }
    }
}

/// ECMA-262 §10.4.2.1 Array `[[DefineOwnProperty]] ( P, Desc )`, proved `exec == spec`,
/// `Heap::wf`-preserving, and §6.1.7.3-preserving across all objects and keys.
pub fn array_define_own_property(
    heap: &mut Heap,
    a: ObjId,
    key: &PropKey,
    desc: &PropertyDescriptor,
) -> (res: Result<bool, JsError>)
    requires
        old(heap).wf(),
        old(heap).valid_obj(a),
        old(heap)@.objects[a.0 as int].kind == ObjectKind::Array,
        prop_key_wf(key@),
        old(heap).desc_wf(desc@),
    ensures
        final(heap).wf(),
        spec_all_essential_invariants(old(heap)@, final(heap)@),
        match (res, spec_array_define_own_property(old(heap)@, a, key@, desc@)) {
            (Err(e1), Err(e2)) => e1 == e2 && final(heap)@ == old(heap)@,
            (Ok(b1), Ok((b2, h_spec))) => b1 == b2 && final(heap)@ == h_spec,
            _ => false,
        },
{
    if is_length_key(key) {
        return array_set_length(heap, a, desc);
    }
    let ghost old_h = heap@;
    let ghost num_objs = old_h.objects.len() as nat;
    proof {
        assert(object_wf(num_objs, old_h.objects[a.0 as int]));
        lemma_array_define_preserves_wf(num_objs, old_h.objects[a.0 as int], key@, desc@);
    }
    match key {
        PropKey::ArrayIndex(index) => {
            let mut obj = clone_js_object(&heap.objects[a.0]);
            let (old_len, old_writable) = read_array_length_and_writable(&obj);
            if *index >= old_len && !old_writable {
                proof {
                    assert(old_h.objects.update(a.0 as int, old_h.objects[a.0 as int]) =~= old_h.objects);
                    lemma_all_essential_invariants_refl(heap@);
                }
                return Ok(false);
            }
            let succeeded = apply_ordinary_define_on_object(&mut obj, key, desc);
            if !succeeded {
                proof {
                    assert(old_h.objects.update(a.0 as int, old_h.objects[a.0 as int]) =~= old_h.objects);
                    lemma_all_essential_invariants_refl(heap@);
                }
                return Ok(false);
            }
            if *index >= old_len {
                let new_len: u32 = *index + 1u32;
                let lkey = length_prop_key();
                let len_update = PropertyDescriptor {
                    value: Some(js_val_from_u32(new_len)),
                    writable: None,
                    get: None,
                    set: None,
                    enumerable: None,
                    configurable: None,
                };
                let _ = apply_ordinary_define_on_object(&mut obj, &lkey, &len_update);
            }
            let ghost updated_view = obj@;
            heap.objects.set(a.0, obj);
            proof {
                assert(heap@.objects =~= old_h.objects.update(a.0 as int, updated_view));
                assert forall|i: int| 0 <= i < heap@.objects.len() implies
                    object_wf(heap@.objects.len() as nat, #[trigger] heap@.objects[i])
                by {
                    if i == a.0 as int {
                        assert(heap@.objects[i] == updated_view);
                    } else {
                        assert(heap@.objects[i] == old_h.objects[i]);
                        assert(object_wf(num_objs, old_h.objects[i]));
                    }
                };
                assert forall|obs_o: ObjId, obs_k: PropKeyView| valid_obj(old_h, obs_o) implies
                    #[trigger] spec_essential_invariants_hold(old_h, heap@, obs_o, obs_k)
                by {
                    lemma_array_define_essential(old_h, a, key@, desc@, obs_o, obs_k);
                };
            }
            Ok(true)
        },
        _ => {
            let mut obj = clone_js_object(&heap.objects[a.0]);
            let succeeded = apply_ordinary_define_on_object(&mut obj, key, desc);
            let ghost updated_view = obj@;
            heap.objects.set(a.0, obj);
            proof {
                assert(heap@.objects =~= old_h.objects.update(a.0 as int, updated_view));
                assert forall|i: int| 0 <= i < heap@.objects.len() implies
                    object_wf(heap@.objects.len() as nat, #[trigger] heap@.objects[i])
                by {
                    if i == a.0 as int {
                        assert(heap@.objects[i] == updated_view);
                    } else {
                        assert(heap@.objects[i] == old_h.objects[i]);
                        assert(object_wf(num_objs, old_h.objects[i]));
                    }
                };
                assert forall|obs_o: ObjId, obs_k: PropKeyView| valid_obj(old_h, obs_o) implies
                    #[trigger] spec_essential_invariants_hold(old_h, heap@, obs_o, obs_k)
                by {
                    lemma_array_define_essential(old_h, a, key@, desc@, obs_o, obs_k);
                };
            }
            Ok(succeeded)
        },
    }
}

// ---------------------------------------------------------------------------------------
// Polymorphic Internal Method Dispatch (Ordinary §10.1 + Array Exotic §10.4.2)
// ---------------------------------------------------------------------------------------

pub open spec fn spec_define_own_property(
    h: HeapView,
    o: ObjId,
    key: PropKeyView,
    desc: PropDescView,
) -> Result<(bool, HeapView), JsError> {
    match h.objects[o.0 as int].kind {
        ObjectKind::Ordinary => Ok(spec_ordinary_define_own_property(h, o, key, desc)),
        ObjectKind::Array => spec_array_define_own_property(h, o, key, desc),
    }
}

/// Polymorphic `O.[[DefineOwnProperty]] ( P, Desc )` dispatching on `ObjectKind::Ordinary | Array`.
pub fn define_own_property(
    heap: &mut Heap,
    o: ObjId,
    key: &PropKey,
    desc: &PropertyDescriptor,
) -> (res: Result<bool, JsError>)
    requires
        old(heap).wf(),
        old(heap).valid_obj(o),
        prop_key_wf(key@),
        old(heap).desc_wf(desc@),
    ensures
        final(heap).wf(),
        spec_all_essential_invariants(old(heap)@, final(heap)@),
        match (res, spec_define_own_property(old(heap)@, o, key@, desc@)) {
            (Err(e1), Err(e2)) => e1 == e2 && final(heap)@ == old(heap)@,
            (Ok(b1), Ok((b2, h_spec))) => b1 == b2 && final(heap)@ == h_spec,
            _ => false,
        },
{
    match heap.objects[o.0].kind {
        ObjectKind::Ordinary => Ok(ordinary_define_own_property(heap, o, key, desc)),
        ObjectKind::Array => array_define_own_property(heap, o, key, desc),
    }
}

/// Polymorphic ECMA-262 §10.1.9.2 `OrdinarySetWithOwnDescriptor` supporting BOTH Ordinary and Array `Receiver`s!
pub open spec fn spec_js_set_with_own_descriptor(
    h: HeapView,
    o: ObjId,
    key: PropKeyView,
    v: JsValView,
    receiver: JsValView,
    own_desc: Option<CompleteDescView>,
) -> Result<(SetOutcomeView, HeapView), JsError> {
    let eff = spec_resolve_set_descriptor(h, o, key, own_desc);
    match eff {
        CompleteDescView::Data { writable, .. } => {
            if !writable {
                Ok((SetOutcomeView::Result(false), h))
            } else {
                match receiver {
                    JsValView::Object(recv_id) => {
                        let existing = spec_ordinary_get_own_property(h, recv_id, key);
                        match existing {
                            Some(CompleteDescView::Accessor { .. }) =>
                                Ok((SetOutcomeView::Result(false), h)),
                            Some(CompleteDescView::Data { writable: false, .. }) =>
                                Ok((SetOutcomeView::Result(false), h)),
                            Some(CompleteDescView::Data { writable: true, .. }) => {
                                let value_desc = PropDescView {
                                    value: Some(v),
                                    writable: None,
                                    get: None,
                                    set: None,
                                    enumerable: None,
                                    configurable: None,
                                };
                                match spec_define_own_property(h, recv_id, key, value_desc) {
                                    Err(e) => Err(e),
                                    Ok((ok, nh)) => Ok((SetOutcomeView::Result(ok), nh)),
                                }
                            },
                            None => {
                                let create_desc = PropDescView {
                                    value: Some(v),
                                    writable: Some(true),
                                    get: None,
                                    set: None,
                                    enumerable: Some(true),
                                    configurable: Some(true),
                                };
                                match spec_define_own_property(h, recv_id, key, create_desc) {
                                    Err(e) => Err(e),
                                    Ok((ok, nh)) => Ok((SetOutcomeView::Result(ok), nh)),
                                }
                            },
                        }
                    },
                    _ => Ok((SetOutcomeView::Result(false), h)),
                }
            }
        },
        CompleteDescView::Accessor { set, .. } => {
            match set {
                None => Ok((SetOutcomeView::Result(false), h)),
                Some(setter_id) => Ok((
                    SetOutcomeView::CallSetter { setter: setter_id, receiver, value: v },
                    h,
                )),
            }
        },
    }
}

pub open spec fn spec_js_set(
    h: HeapView,
    o: ObjId,
    key: PropKeyView,
    v: JsValView,
    receiver: JsValView,
) -> Result<(SetOutcomeView, HeapView), JsError> {
    let own = spec_ordinary_get_own_property(h, o, key);
    spec_js_set_with_own_descriptor(h, o, key, v, receiver, own)
}

pub fn js_set_with_own_descriptor(
    heap: &mut Heap,
    o: ObjId,
    key: &PropKey,
    v: &JsVal,
    receiver: &JsVal,
    own_desc: Option<CompleteDescriptor>,
) -> (res: Result<SetOutcome, JsError>)
    requires
        old(heap).wf(),
        old(heap).valid_obj(o),
        prop_key_wf(key@),
        old(heap).val_wf(v@),
        old(heap).val_wf(receiver@),
        match &own_desc {
            None => true,
            Some(d) => complete_desc_refs_wf(old(heap)@.objects.len() as nat, d@),
        },
    ensures
        final(heap).wf(),
        spec_all_essential_invariants(old(heap)@, final(heap)@),
        match (
            &res,
            spec_js_set_with_own_descriptor(
                old(heap)@,
                o,
                key@,
                v@,
                receiver@,
                match &own_desc {
                    None => None,
                    Some(d) => Some(d@),
                },
            ),
        ) {
            (Err(e1), Err(e2)) => *e1 == e2 && final(heap)@ == old(heap)@,
            (Ok(s1), Ok((s2, h_spec))) => s1@ == s2 && final(heap)@ == h_spec,
            _ => false,
        },
{
    let eff = resolve_set_descriptor(heap, o, key, own_desc);
    match eff {
        CompleteDescriptor::Data { writable, .. } => {
            if !writable {
                proof {
                    lemma_all_essential_invariants_refl(heap@);
                }
                return Ok(SetOutcome::Result(false));
            }
            match receiver {
                JsVal::Object(recv_id) => {
                    let existing = ordinary_get_own_property(heap, *recv_id, key);
                    match existing {
                        Some(CompleteDescriptor::Accessor { .. }) => {
                            proof {
                                lemma_all_essential_invariants_refl(heap@);
                            }
                            Ok(SetOutcome::Result(false))
                        },
                        Some(CompleteDescriptor::Data { writable: false, .. }) => {
                            proof {
                                lemma_all_essential_invariants_refl(heap@);
                            }
                            Ok(SetOutcome::Result(false))
                        },
                        Some(CompleteDescriptor::Data { writable: true, .. }) => {
                            let value_desc = PropertyDescriptor {
                                value: Some(clone_js_val(v)),
                                writable: None,
                                get: None,
                                set: None,
                                enumerable: None,
                                configurable: None,
                            };
                            match define_own_property(heap, *recv_id, key, &value_desc) {
                                Err(e) => Err(e),
                                Ok(ok) => Ok(SetOutcome::Result(ok)),
                            }
                        },
                        None => {
                            let create_desc =
                                PropertyDescriptor::data(clone_js_val(v), true, true, true);
                            match define_own_property(heap, *recv_id, key, &create_desc) {
                                Err(e) => Err(e),
                                Ok(ok) => Ok(SetOutcome::Result(ok)),
                            }
                        },
                    }
                },
                _ => {
                    proof {
                        lemma_all_essential_invariants_refl(heap@);
                    }
                    Ok(SetOutcome::Result(false))
                },
            }
        },
        CompleteDescriptor::Accessor { set, .. } => {
            proof {
                lemma_all_essential_invariants_refl(heap@);
            }
            match set {
                None => Ok(SetOutcome::Result(false)),
                Some(setter_id) => Ok(SetOutcome::CallSetter {
                    setter: setter_id,
                    receiver: clone_js_val(receiver),
                    value: clone_js_val(v),
                }),
            }
        },
    }
}

/// Polymorphic `O.[[Set]] ( P, V, Receiver )` supporting both Ordinary and Array exotic objects!
pub fn js_set(
    heap: &mut Heap,
    o: ObjId,
    key: &PropKey,
    v: &JsVal,
    receiver: &JsVal,
) -> (res: Result<SetOutcome, JsError>)
    requires
        old(heap).wf(),
        old(heap).valid_obj(o),
        prop_key_wf(key@),
        old(heap).val_wf(v@),
        old(heap).val_wf(receiver@),
    ensures
        final(heap).wf(),
        spec_all_essential_invariants(old(heap)@, final(heap)@),
        match (&res, spec_js_set(old(heap)@, o, key@, v@, receiver@)) {
            (Err(e1), Err(e2)) => *e1 == e2 && final(heap)@ == old(heap)@,
            (Ok(s1), Ok((s2, h_spec))) => s1@ == s2 && final(heap)@ == h_spec,
            _ => false,
        },
{
    let own = ordinary_get_own_property(heap, o, key);
    js_set_with_own_descriptor(heap, o, key, v, receiver, own)
}

} // verus!
