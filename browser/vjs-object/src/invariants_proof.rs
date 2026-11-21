//! Machine-Checked ECMA-262 §6.1.7.3 Essential Internal Method Invariants
//! for BOTH Ordinary (`§10.1`) and Array Exotic (`§10.4.2`) Objects:
//!
//! 1. **Heap Well-Formedness & Prototype Acyclicity**:
//!    `Heap::wf` (valid prototype `ObjId`s with strictly decreasing `proto_rank`, duplicate-free
//!    ordered property maps, valid descriptor references, and §10.4.2 Array `length` invariant)
//!    is preserved by every internal method and across arbitrary transition traces.
//! 2. **Non-Extensibility Monotonicity (`§6.1.7.3` `[[IsExtensible]]`, `[[GetPrototypeOf]]`, `[[GetOwnProperty]]`)**:
//!    Once `!is_extensible(o)`, `is_extensible(o)` remains `false` forever, `get_prototype_of(o)`
//!    can never change, and no new own property key can ever appear on `o`.
//! 3. **Non-Configurable Property Integrity (`§6.1.7.3` `[[GetOwnProperty]]`, `[[DefineOwnProperty]]`, `[[Delete]]`)**:
//!    Whenever own property `k` on `o` has `configurable == false`:
//!    - `delete(o, k)` unconditionally returns `false` and leaves `o` untouched;
//!    - Across ANY internal method on ANY object/key (including `ArraySetLength` shrinking!),
//!      `get_own_property(o, k)` remains `Some` with `configurable == false`, preserves
//!      Data vs Accessor kind, preserves `enumerable`, never flips `writable` `false -> true`,
//!      keeps Accessor `get`/`set` identical, and when Data with `!writable`, keeps `value` `SameValue`!
use crate::descriptor::PropDescView;
#[cfg(verus_keep_ghost)]
use crate::array::{
    lemma_array_define_preserves_wf, lemma_array_set_length_preserves_wf,
    lemma_shrink_elements_invariants, spec_array_define_on_object,
    spec_array_define_own_property, spec_array_length, spec_array_length_obj,
    spec_array_length_writable_obj, spec_array_set_length, spec_array_set_length_on_object,
    spec_coerce_array_length_value, spec_define_own_property, spec_js_set,
    spec_shrink_elements_desc,
};
#[cfg(verus_keep_ghost)]
use crate::descriptor::{
    lemma_validate_nonconfigurable_invariants, prop_desc_wf, spec_complete_configurable,
    spec_complete_enumerable, spec_complete_is_accessor, spec_complete_is_data,
    spec_validate_and_apply_property_descriptor, CompleteDescView,
};
use crate::heap::{JsValView, ObjId, PropKeyView};
#[cfg(verus_keep_ghost)]
pub use crate::heap::{
    lemma_all_essential_invariants_refl, lemma_essential_invariants_refl,
    lemma_essential_invariants_trans, lemma_nonconfigurable_preserved_refl,
    lemma_nonconfigurable_preserved_trans, spec_all_essential_invariants,
    spec_essential_invariants_hold, spec_nonconfigurable_preserved,
};
#[cfg(verus_keep_ghost)]
use crate::heap::{
    array_object_wf, heap_wf, lemma_length_key_wf, lemma_object_wf_monotonic,
    lemma_proto_chain_acyclic, lemma_remove_lookup, lemma_same_value_refl,
    lemma_same_value_trans, lemma_set_proto_preserves_proto_wf, lemma_u32_f64_bits_injective,
    lemma_u32_f64_bits_roundtrip, lemma_upsert_lookup, object_wf, prop_desc_refs_wf, prop_key_wf,
    spec_f64_bits_to_exact_u32, spec_length_key, spec_lookup_prop, spec_proto_reaches,
    spec_same_value, spec_u32_to_f64_bits, val_refs_wf, valid_obj, HeapView, ObjectKind,
    ObjectView, PropEntryView,
};
use crate::ordinary::IntegrityLevel;
#[cfg(verus_keep_ghost)]
use crate::ordinary::{
    lemma_collect_sorted_indices_props, lemma_delete_preserves_object_wf,
    lemma_ordinary_define_preserves_props_wf, lemma_set_integrity_preserves_wf_and_satisfies_test,
    spec_collect_sorted_indices, spec_ordinary_define_on_object,
    spec_ordinary_define_own_property, spec_ordinary_delete, spec_ordinary_delete_on_object,
    spec_ordinary_get_own_property, spec_ordinary_get_prototype_of,
    spec_ordinary_is_extensible, spec_ordinary_prevent_extensions,
    spec_ordinary_set_prototype_of, spec_props_has_array_index, spec_resolve_set_descriptor,
    spec_seq_u32_contains, spec_set_integrity_level, spec_test_integrity_level,
};
#[cfg(verus_keep_ghost)]
use crate::descriptor::PropDescView as GhostPropDescView;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------------------
// Individual §6.1.7.3 Theorems for Every Internal Method (Ordinary & Array Exotic)
// ---------------------------------------------------------------------------------------

/// Theorem 1: Prototype chains in any well-formed `Heap` are strictly acyclic (`proto_rank` witness).
pub proof fn theorem_prototype_chain_acyclic(h: HeapView, o: ObjId)
    requires
        heap_wf(h),
        valid_obj(h, o),
    ensures
        !spec_proto_reaches(h, spec_ordinary_get_prototype_of(h, o), o),
{
    lemma_proto_chain_acyclic(h, o);
}

/// Theorem 2: `[[SetPrototypeOf]]` (§10.1.2.1) preserves `Heap::wf`, rejects cycles,
/// refuses to change `[[Prototype]]` when `!is_extensible`, and preserves all §6.1.7.3 invariants.
pub proof fn theorem_set_prototype_of_invariants(
    h: HeapView,
    target: ObjId,
    v: Option<ObjId>,
    o: ObjId,
    k: PropKeyView,
)
    requires
        heap_wf(h),
        valid_obj(h, target),
        valid_obj(h, o),
        match v {
            None => true,
            Some(vid) => valid_obj(h, vid),
        },
    ensures
        ({
            let (ok, nh) = spec_ordinary_set_prototype_of(h, target, v);
            spec_essential_invariants_hold(h, nh, o, k)
            && (spec_proto_reaches(h, v, target) ==> (!ok && nh == h))
            && (!spec_ordinary_is_extensible(h, target) && v != spec_ordinary_get_prototype_of(h, target)
                ==> (!ok && nh == h))
        }),
{
    lemma_essential_invariants_refl(h, o, k);
    let cur = h.objects[target.0 as int].prototype;
    if v != cur && h.objects[target.0 as int].extensible && !spec_proto_reaches(h, v, target) {
        let old_obj = h.objects[target.0 as int];
        let new_obj = ObjectView { prototype: v, ..old_obj };
        lemma_set_proto_preserves_proto_wf(h, target, v, new_obj);
        let (_, nh) = spec_ordinary_set_prototype_of(h, target, v);
        assert forall|i: int| 0 <= i < nh.objects.len() implies
            object_wf(nh.objects.len() as nat, #[trigger] nh.objects[i])
        by {
            if i == target.0 as int {
                assert(object_wf(h.objects.len() as nat, old_obj));
            } else {
                assert(nh.objects[i] == h.objects[i]);
            }
        };
        assert(nh.objects[o.0 as int].properties == h.objects[o.0 as int].properties);
        if let Some(d) = spec_ordinary_get_own_property(h, o, k) {
            if !spec_complete_configurable(d) {
                lemma_nonconfigurable_preserved_refl(d);
            }
        }
    } else if v == cur && spec_proto_reaches(h, v, target) {
        // Impossible by acyclicity!
        lemma_proto_chain_acyclic(h, target);
        assert(false);
    }
}

/// Theorem 3: `[[PreventExtensions]]` (§10.1.4.1) preserves `Heap::wf`, makes `target` permanently
/// non-extensible, and preserves all §6.1.7.3 invariants.
pub proof fn theorem_prevent_extensions_invariants(
    h: HeapView,
    target: ObjId,
    o: ObjId,
    k: PropKeyView,
)
    requires
        heap_wf(h),
        valid_obj(h, target),
        valid_obj(h, o),
    ensures
        ({
            let nh = spec_ordinary_prevent_extensions(h, target);
            !spec_ordinary_is_extensible(nh, target)
            && spec_essential_invariants_hold(h, nh, o, k)
        }),
{
    let nh = spec_ordinary_prevent_extensions(h, target);
    assert forall|i: int| 0 <= i < nh.objects.len() implies
        object_wf(nh.objects.len() as nat, #[trigger] nh.objects[i])
    by {
        if i == target.0 as int {
            assert(object_wf(h.objects.len() as nat, h.objects[i]));
        } else {
            assert(nh.objects[i] == h.objects[i]);
        }
    };
    if let Some(d) = spec_ordinary_get_own_property(h, o, k) {
        if !spec_complete_configurable(d) {
            lemma_nonconfigurable_preserved_refl(d);
        }
    }
}

/// Theorem 4: `[[Delete]]` (§10.1.10.1) returns `false` on every non-configurable property
/// (leaving the object untouched) and preserves all §6.1.7.3 invariants for BOTH Ordinary & Array objects.
pub proof fn theorem_delete_invariants(
    h: HeapView,
    target: ObjId,
    del_key: PropKeyView,
    o: ObjId,
    k: PropKeyView,
)
    requires
        heap_wf(h),
        valid_obj(h, target),
        valid_obj(h, o),
    ensures
        ({
            let (ok, nh) = spec_ordinary_delete(h, target, del_key);
            spec_essential_invariants_hold(h, nh, o, k)
            && (match spec_ordinary_get_own_property(h, target, del_key) {
                Some(d) => !spec_complete_configurable(d) ==> (!ok && nh == h),
                None => ok && nh == h,
            })
        }),
{
    lemma_essential_invariants_refl(h, o, k);
    let orig_t = h.objects[target.0 as int];
    assert(object_wf(h.objects.len() as nat, orig_t));
    lemma_delete_preserves_object_wf(h.objects.len() as nat, orig_t, del_key);
    let (ok, nh) = spec_ordinary_delete(h, target, del_key);
    match spec_lookup_prop(orig_t.properties, del_key) {
        None => {
            assert(nh.objects =~= h.objects);
        },
        Some(dd) => {
            if spec_complete_configurable(dd) {
                assert forall|i: int| 0 <= i < nh.objects.len() implies
                    object_wf(nh.objects.len() as nat, #[trigger] nh.objects[i])
                by {
                    if i != target.0 as int {
                        assert(nh.objects[i] == h.objects[i]);
                    }
                };
                if target == o {
                    lemma_remove_lookup(orig_t.properties, del_key, k);
                    if let Some(d_k) = spec_ordinary_get_own_property(h, o, k) {
                        if !spec_complete_configurable(d_k) {
                            assert(k != del_key);
                            lemma_nonconfigurable_preserved_refl(d_k);
                        }
                    }
                } else {
                    if let Some(d_k) = spec_ordinary_get_own_property(h, o, k) {
                        if !spec_complete_configurable(d_k) {
                            lemma_nonconfigurable_preserved_refl(d_k);
                        }
                    }
                }
            }
        },
    }
}

/// Object-level helper: `spec_ordinary_define_on_object` preserves non-extensibility & non-configurable properties.
proof fn lemma_ordinary_define_obj_essential(
    obj: ObjectView,
    key: PropKeyView,
    desc: PropDescView,
    k: PropKeyView,
)
    requires
        object_wf(0, obj) || crate::heap::spec_no_duplicate_keys(obj.properties),
        prop_desc_wf(desc),
    ensures
        ({
            let (_, nobj) = spec_ordinary_define_on_object(obj, key, desc);
            nobj.extensible == obj.extensible
            && nobj.prototype == obj.prototype
            && (!obj.extensible && spec_lookup_prop(obj.properties, k) is None
                ==> spec_lookup_prop(nobj.properties, k) is None)
            && (match spec_lookup_prop(obj.properties, k) {
                Some(old_d) =>
                    !spec_complete_configurable(old_d)
                        ==> spec_nonconfigurable_preserved(
                            old_d,
                            spec_lookup_prop(nobj.properties, k),
                        ),
                None => true,
            })
        }),
{
    let cur = spec_lookup_prop(obj.properties, key);
    let (ok, next_opt) =
        spec_validate_and_apply_property_descriptor(true, obj.extensible, desc, cur);
    if ok {
        let stored = next_opt.unwrap();
        lemma_upsert_lookup(obj.properties, key, stored, k);
        if k == key {
            if let Some(old_d) = cur {
                if !spec_complete_configurable(old_d) {
                    lemma_validate_nonconfigurable_invariants(true, obj.extensible, desc, old_d);
                }
            }
        } else {
            if let Some(old_d) = spec_lookup_prop(obj.properties, k) {
                if !spec_complete_configurable(old_d) {
                    lemma_nonconfigurable_preserved_refl(old_d);
                }
            }
        }
    } else {
        if let Some(old_d) = spec_lookup_prop(obj.properties, k) {
            if !spec_complete_configurable(old_d) {
                lemma_nonconfigurable_preserved_refl(old_d);
            }
        }
    }
}

/// Theorem 5: `OrdinaryDefineOwnProperty` (§10.1.6.1) preserves `Heap::wf` and all §6.1.7.3 invariants.
pub proof fn theorem_ordinary_define_own_property_invariants(
    h: HeapView,
    target: ObjId,
    key: PropKeyView,
    desc: PropDescView,
    o: ObjId,
    k: PropKeyView,
)
    requires
        heap_wf(h),
        valid_obj(h, target),
        valid_obj(h, o),
        h.objects[target.0 as int].kind == ObjectKind::Ordinary,
        prop_key_wf(key),
        prop_desc_wf(desc),
        prop_desc_refs_wf(h.objects.len() as nat, desc),
    ensures
        spec_essential_invariants_hold(
            h,
            spec_ordinary_define_own_property(h, target, key, desc).1,
            o,
            k,
        ),
{
    lemma_essential_invariants_refl(h, o, k);
    let orig_t = h.objects[target.0 as int];
    assert(object_wf(h.objects.len() as nat, orig_t));
    lemma_ordinary_define_preserves_props_wf(h.objects.len() as nat, orig_t, key, desc);
    let (ok, nh) = spec_ordinary_define_own_property(h, target, key, desc);
    if ok {
        assert forall|i: int| 0 <= i < nh.objects.len() implies
            object_wf(nh.objects.len() as nat, #[trigger] nh.objects[i])
        by {
            if i != target.0 as int {
                assert(nh.objects[i] == h.objects[i]);
            }
        };
        if target == o {
            lemma_ordinary_define_obj_essential(orig_t, key, desc, k);
        } else {
            if let Some(old_d) = spec_ordinary_get_own_property(h, o, k) {
                if !spec_complete_configurable(old_d) {
                    lemma_nonconfigurable_preserved_refl(old_d);
                }
            }
        }
    }
}

/// Theorem 6: `ArraySetLength` (§10.4.2.4) preserves `Heap::wf` and ALL §6.1.7.3 invariants
/// across BOTH `k == "length"` AND arbitrary own properties `k != "length"` (including non-configurable
/// array elements hit during shrinking!).
pub proof fn theorem_array_set_length_invariants(
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
            assert(nh.objects[o.0 as int] == h.objects[o.0 as int]);
            if let Some(old_d) = spec_ordinary_get_own_property(h, o, k) {
                if !spec_complete_configurable(old_d) {
                    lemma_nonconfigurable_preserved_refl(old_d);
                }
            }
        } else {
            // Case `a == o`: prove §6.1.7.3 for BOTH `k == "length"` and `k != "length"`!
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
                    assert(fin == obj);
                    if let Some(old_d) = spec_lookup_prop(obj.properties, k) {
                        if !spec_complete_configurable(old_d) {
                            lemma_nonconfigurable_preserved_refl(old_d);
                        }
                    }
                } else {
                    // Here `old_writable == true`!
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
                        assert(fin == obj);
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
                            // `cur_len` had `old_writable == true`, `enumerable == false`, `configurable == false`
                            // and `fin` satisfies `array_object_wf(fin)`, so `"length"` on `fin` is Data
                            // with `enumerable == false, configurable == false`, and since `old_writable == true`,
                            // `!old_writable ==> ...` is vacuously satisfied!
                            assert(array_object_wf(fin));
                        } else {
                            assert(k != spec_length_key());
                            if let Some(old_d) = spec_lookup_prop(obj.properties, k) {
                                if !spec_complete_configurable(old_d) {
                                    assert(spec_lookup_prop(fin.properties, k) == Some(old_d));
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

/// Theorem 7: Explicit ECMA-262 §10.4.2.4 non-configurable barrier theorem:
/// When shrinking an Array whose highest element `idx >= new_len` is non-configurable
/// (i.e. no element `> idx` exists), `ArraySetLength` returns `Ok(false)`, preserves `ArrayIndex(idx)`,
/// and sets `length` to `idx + 1`!
pub proof fn theorem_array_shrink_stops_at_nonconfigurable_element(
    h: HeapView,
    a: ObjId,
    new_len: u32,
    idx: u32,
    elem_desc: CompleteDescView,
)
    requires
        heap_wf(h),
        valid_obj(h, a),
        h.objects[a.0 as int].kind == ObjectKind::Array,
        spec_array_length_writable_obj(h.objects[a.0 as int]),
        new_len <= idx,
        idx < spec_array_length(h, a),
        spec_ordinary_get_own_property(h, a, PropKeyView::ArrayIndex(idx)) == Some(elem_desc),
        !spec_complete_configurable(elem_desc),
        forall|y: u32|
            y > idx ==> !(#[trigger] spec_props_has_array_index(h.objects[a.0 as int].properties, y)),
    ensures
        ({
            let desc = PropDescView {
                value: Some(JsValView::NumberBits(spec_u32_to_f64_bits(new_len))),
                writable: None,
                get: None,
                set: None,
                enumerable: None,
                configurable: None,
            };
            match spec_array_set_length(h, a, desc) {
                Ok((ok, nh)) =>
                    !ok
                    && spec_array_length(nh, a) == add(idx, 1u32)
                    && spec_ordinary_get_own_property(nh, a, PropKeyView::ArrayIndex(idx))
                        == Some(elem_desc),
                Err(_) => false,
            }
        }),
{
    lemma_length_key_wf();
    lemma_u32_f64_bits_roundtrip(new_len);
    let num_objs = h.objects.len() as nat;
    let obj = h.objects[a.0 as int];
    assert(object_wf(num_objs, obj));
    crate::heap::lemma_find_prop_spec(obj.properties, PropKeyView::ArrayIndex(idx));
    let eidx = crate::heap::spec_find_prop(obj.properties, PropKeyView::ArrayIndex(idx)).unwrap();
    assert(obj.properties[eidx as int].key == PropKeyView::ArrayIndex(idx));
    assert(idx < u32::MAX);

    let desc = PropDescView {
        value: Some(JsValView::NumberBits(spec_u32_to_f64_bits(new_len))),
        writable: None,
        get: None,
        set: None,
        enumerable: None,
        configurable: None,
    };
    lemma_ordinary_define_preserves_props_wf(num_objs, obj, spec_length_key(), desc);
    let (succeeded, after_len) = spec_ordinary_define_on_object(obj, spec_length_key(), desc);
    assert(succeeded);
    let next_len = CompleteDescView::Data {
        value: JsValView::NumberBits(spec_u32_to_f64_bits(new_len)),
        writable: true,
        enumerable: false,
        configurable: false,
    };
    lemma_upsert_lookup(
        obj.properties,
        spec_length_key(),
        next_len,
        PropKeyView::ArrayIndex(idx),
    );
    lemma_collect_sorted_indices_props(after_len.properties);
    let sorted_idxs = spec_collect_sorted_indices(after_len.properties);

    // Show `idx` is in `sorted_idxs` and is the last (largest) element of `sorted_idxs`!
    crate::heap::lemma_find_prop_spec(after_len.properties, PropKeyView::ArrayIndex(idx));
    let aeidx =
        crate::heap::spec_find_prop(after_len.properties, PropKeyView::ArrayIndex(idx)).unwrap();
    assert(after_len.properties[aeidx as int].key == PropKeyView::ArrayIndex(idx));
    assert(spec_props_has_array_index(after_len.properties, idx));
    assert(spec_seq_u32_contains(sorted_idxs, idx));
    let pos = choose|t: int| 0 <= t < sorted_idxs.len() && (#[trigger] sorted_idxs[t]) == idx;
    assert(sorted_idxs.len() > 0);
    let last_t = (sorted_idxs.len() - 1) as int;
    if pos < last_t {
        let top = sorted_idxs[last_t];
        assert(idx < top);
        assert(spec_seq_u32_contains(sorted_idxs, top));
        assert(spec_props_has_array_index(after_len.properties, top));
        let tm = choose|m: int| 0 <= m < after_len.properties.len()
            && (#[trigger] after_len.properties[m]).key == PropKeyView::ArrayIndex(top);
        crate::heap::lemma_find_prop_spec(obj.properties, spec_length_key());
        assert(after_len.properties[tm] == obj.properties[tm]);
        assert(spec_props_has_array_index(obj.properties, top));
        assert(false);
    }
    assert(pos == last_t);
    assert(sorted_idxs[last_t] == idx);

    let stopped_len = add(idx, 1u32);
    lemma_u32_f64_bits_roundtrip(stopped_len);
    assert((PropDescView {
        value: Some(JsValView::NumberBits(spec_u32_to_f64_bits(new_len))),
        ..desc
    }) == desc);
    assert(spec_lookup_prop(after_len.properties, PropKeyView::ArrayIndex(idx)) == Some(elem_desc));
    assert(spec_ordinary_delete_on_object(after_len, PropKeyView::ArrayIndex(idx)) == (false, after_len));
    lemma_upsert_lookup(
        obj.properties,
        spec_length_key(),
        next_len,
        spec_length_key(),
    );
    let stop_desc = PropDescView {
        value: Some(JsValView::NumberBits(spec_u32_to_f64_bits(stopped_len))),
        writable: None,
        get: None,
        set: None,
        enumerable: None,
        configurable: None,
    };
    let stop_stored = CompleteDescView::Data {
        value: JsValView::NumberBits(spec_u32_to_f64_bits(stopped_len)),
        writable: true,
        enumerable: false,
        configurable: false,
    };
    assert(spec_ordinary_define_on_object(after_len, spec_length_key(), stop_desc)
        == (true, ObjectView {
            properties: crate::heap::spec_upsert_prop(after_len.properties, spec_length_key(), stop_stored),
            ..after_len
        }));
    assert(spec_shrink_elements_desc(
        after_len,
        sorted_idxs,
        sorted_idxs.len(),
        new_len,
        true,
    ) == (false, spec_ordinary_define_on_object(after_len, spec_length_key(), stop_desc).1));
    lemma_upsert_lookup(
        after_len.properties,
        spec_length_key(),
        stop_stored,
        spec_length_key(),
    );
    lemma_upsert_lookup(
        after_len.properties,
        spec_length_key(),
        stop_stored,
        PropKeyView::ArrayIndex(idx),
    );
}

/// Theorem 8: Array `[[DefineOwnProperty]]` (§10.4.2.1) preserves `Heap::wf` and ALL §6.1.7.3
/// invariants for every property key `key` and every observed `(o, k)`!
pub proof fn theorem_array_define_own_property_invariants(
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
        theorem_array_set_length_invariants(h, a, desc, o, k);
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
            if let Some(old_d) = spec_ordinary_get_own_property(h, o, k) {
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
                        assert(fin == obj);
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
                            assert(fin == obj);
                            if let Some(old_d) = spec_lookup_prop(obj.properties, k) {
                                if !spec_complete_configurable(old_d) {
                                    lemma_nonconfigurable_preserved_refl(old_d);
                                }
                            }
                        } else if index >= old_len {
                            // Here `old_writable == true`!
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
                            ).1.properties == crate::heap::spec_upsert_prop(
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
                                // `old_writable == true`, and `"length"` already existed on `obj`!
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

/// Theorem 9: Polymorphic `[[DefineOwnProperty]]` across BOTH Ordinary and Array exotic objects
/// preserves `Heap::wf` and all §6.1.7.3 invariants.
pub proof fn theorem_define_own_property_invariants(
    h: HeapView,
    target: ObjId,
    key: PropKeyView,
    desc: PropDescView,
    o: ObjId,
    k: PropKeyView,
)
    requires
        heap_wf(h),
        valid_obj(h, target),
        valid_obj(h, o),
        prop_key_wf(key),
        prop_desc_wf(desc),
        prop_desc_refs_wf(h.objects.len() as nat, desc),
    ensures
        match spec_define_own_property(h, target, key, desc) {
            Err(_) => true,
            Ok((_, nh)) => spec_essential_invariants_hold(h, nh, o, k),
        },
{
    match h.objects[target.0 as int].kind {
        ObjectKind::Ordinary => {
            theorem_ordinary_define_own_property_invariants(h, target, key, desc, o, k);
        },
        ObjectKind::Array => {
            theorem_array_define_own_property_invariants(h, target, key, desc, o, k);
        },
    }
}

/// Theorem 10: Polymorphic `[[Set]]` (§10.1.9) preserves `Heap::wf` and all §6.1.7.3 invariants.
pub proof fn theorem_js_set_invariants(
    h: HeapView,
    target: ObjId,
    key: PropKeyView,
    v: JsValView,
    receiver: JsValView,
    o: ObjId,
    k: PropKeyView,
)
    requires
        heap_wf(h),
        valid_obj(h, target),
        valid_obj(h, o),
        prop_key_wf(key),
        val_refs_wf(h.objects.len() as nat, v),
        val_refs_wf(h.objects.len() as nat, receiver),
    ensures
        match spec_js_set(h, target, key, v, receiver) {
            Err(_) => true,
            Ok((_, nh)) => spec_essential_invariants_hold(h, nh, o, k),
        },
{
    lemma_essential_invariants_refl(h, o, k);
    let own = spec_ordinary_get_own_property(h, target, key);
    let eff = spec_resolve_set_descriptor(h, target, key, own);
    if let CompleteDescView::Data { writable: true, .. } = eff {
        if let JsValView::Object(recv_id) = receiver {
            assert(valid_obj(h, recv_id));
            match spec_ordinary_get_own_property(h, recv_id, key) {
                Some(CompleteDescView::Data { writable: true, .. }) => {
                    let value_desc = GhostPropDescView {
                        value: Some(v),
                        writable: None,
                        get: None,
                        set: None,
                        enumerable: None,
                        configurable: None,
                    };
                    theorem_define_own_property_invariants(h, recv_id, key, value_desc, o, k);
                },
                None => {
                    let create_desc = GhostPropDescView {
                        value: Some(v),
                        writable: Some(true),
                        get: None,
                        set: None,
                        enumerable: Some(true),
                        configurable: Some(true),
                    };
                    theorem_define_own_property_invariants(h, recv_id, key, create_desc, o, k);
                },
                _ => {},
            }
        }
    }
}

/// Theorem 11: `SetIntegrityLevel` (`Object.seal` / `Object.freeze`, §7.3.15) preserves `Heap::wf`
/// and all §6.1.7.3 invariants across BOTH Ordinary and Array exotic objects.
pub proof fn theorem_set_integrity_level_invariants(
    h: HeapView,
    target: ObjId,
    level: IntegrityLevel,
    o: ObjId,
    k: PropKeyView,
)
    requires
        heap_wf(h),
        valid_obj(h, target),
        valid_obj(h, o),
    ensures
        spec_essential_invariants_hold(
            h,
            spec_set_integrity_level(h, target, level),
            o,
            k,
        ),
{
    let num_objs = h.objects.len() as nat;
    let orig_t = h.objects[target.0 as int];
    assert(object_wf(num_objs, orig_t));
    lemma_set_integrity_preserves_wf_and_satisfies_test(num_objs, orig_t, level);
    let nh = spec_set_integrity_level(h, target, level);
    assert forall|i: int| 0 <= i < nh.objects.len() implies
        object_wf(nh.objects.len() as nat, #[trigger] nh.objects[i])
    by {
        if i != target.0 as int {
            assert(nh.objects[i] == h.objects[i]);
        }
    };
    if target != o {
        if let Some(old_d) = spec_ordinary_get_own_property(h, o, k) {
            if !spec_complete_configurable(old_d) {
                lemma_nonconfigurable_preserved_refl(old_d);
            }
        }
    } else {
        let new_props = nh.objects[o.0 as int].properties;
        crate::heap::lemma_find_prop_spec(orig_t.properties, k);
        match crate::heap::spec_find_prop(orig_t.properties, k) {
            None => {
                assert forall|m: int| 0 <= m < new_props.len() implies
                    (#[trigger] new_props[m]).key != k
                by {
                    assert(new_props[m].key == orig_t.properties[m].key);
                };
                crate::heap::lemma_find_prop_spec(new_props, k);
            },
            Some(idx) => {
                assert(new_props[idx as int].key == k);
                crate::heap::lemma_find_prop_unique_index(new_props, k, idx as int);
                let old_d = orig_t.properties[idx as int].desc;
                if !spec_complete_configurable(old_d) {
                    if let CompleteDescView::Data { value: v, .. } = old_d {
                        lemma_same_value_refl(v);
                    }
                }
            },
        }
    }
}

/// Theorem 12: Frozen Object Total Immutability Corollary:
/// If `Object.isFrozen(o)` (`spec_test_integrity_level(h, o, Frozen)`) holds, then after ANY
/// internal transition reaching `nh` with `spec_essential_invariants_hold(h, nh, o, k)`:
/// - `o` remains frozen (`!is_extensible` and every existing own Data property keeps `writable == false`
///   and `SameValue` value; every Accessor keeps identical `get`/`set`; no new keys appear; no keys deleted).
pub proof fn theorem_frozen_object_property_immutable(
    h1: HeapView,
    h2: HeapView,
    o: ObjId,
    k: PropKeyView,
)
    requires
        heap_wf(h1),
        valid_obj(h1, o),
        spec_test_integrity_level(h1, o, IntegrityLevel::Frozen),
        spec_essential_invariants_hold(h1, h2, o, k),
    ensures
        !spec_ordinary_is_extensible(h2, o),
        spec_ordinary_get_prototype_of(h2, o) == spec_ordinary_get_prototype_of(h1, o),
        match (
            spec_ordinary_get_own_property(h1, o, k),
            spec_ordinary_get_own_property(h2, o, k),
        ) {
            (None, None) => true,
            (
                Some(CompleteDescView::Data { value: v1, writable: w1, enumerable: e1, configurable: c1 }),
                Some(CompleteDescView::Data { value: v2, writable: w2, enumerable: e2, configurable: c2 }),
            ) => !w1 && !w2 && !c1 && !c2 && e1 == e2 && spec_same_value(v2, v1),
            (Some(d1), Some(d2)) =>
                spec_complete_is_accessor(d1) && d2 == d1,
            _ => false,
        },
{
    let props = h1.objects[o.0 as int].properties;
    crate::heap::lemma_find_prop_spec(props, k);
    if let Some(idx) = crate::heap::spec_find_prop(props, k) {
        assert(crate::ordinary::spec_entry_matches_integrity(
            props[idx as int].desc,
            IntegrityLevel::Frozen,
        ));
    }
}

// ---------------------------------------------------------------------------------------
// Multi-Step Trace Invariance ("Forever" Theorem over Arbitrary Operation Sequences)
// ---------------------------------------------------------------------------------------

/// Symbolic internal-method transition command over the heap.
pub enum InternalOp {
    SetPrototypeOf { target: ObjId, proto: Option<ObjId> },
    PreventExtensions { target: ObjId },
    DefineOwnProperty { target: ObjId, key: PropKeyView, desc: PropDescView },
    Delete { target: ObjId, key: PropKeyView },
    Set { target: ObjId, key: PropKeyView, value: JsValView, receiver: JsValView },
    SetIntegrity { target: ObjId, level: IntegrityLevel },
}

/// Applies a single `InternalOp` to `h` if its preconditions hold (otherwise is a no-op),
/// allowing arbitrary unbounded-length traces `Seq<InternalOp>` to be reasoned about cleanly.
pub open spec fn spec_apply_op(h: HeapView, op: InternalOp) -> HeapView {
    if !heap_wf(h) {
        h
    } else {
        match op {
            InternalOp::SetPrototypeOf { target, proto } =>
                if valid_obj(h, target) && (match proto { None => true, Some(p) => valid_obj(h, p) }) {
                    spec_ordinary_set_prototype_of(h, target, proto).1
                } else {
                    h
                },
            InternalOp::PreventExtensions { target } =>
                if valid_obj(h, target) {
                    spec_ordinary_prevent_extensions(h, target)
                } else {
                    h
                },
            InternalOp::DefineOwnProperty { target, key, desc } =>
                if valid_obj(h, target)
                    && prop_key_wf(key)
                    && prop_desc_wf(desc)
                    && prop_desc_refs_wf(h.objects.len() as nat, desc)
                {
                    match spec_define_own_property(h, target, key, desc) {
                        Ok((_, nh)) => nh,
                        Err(_) => h,
                    }
                } else {
                    h
                },
            InternalOp::Delete { target, key } =>
                if valid_obj(h, target) {
                    spec_ordinary_delete(h, target, key).1
                } else {
                    h
                },
            InternalOp::Set { target, key, value, receiver } =>
                if valid_obj(h, target)
                    && prop_key_wf(key)
                    && val_refs_wf(h.objects.len() as nat, value)
                    && val_refs_wf(h.objects.len() as nat, receiver)
                {
                    match spec_js_set(h, target, key, value, receiver) {
                        Ok((_, nh)) => nh,
                        Err(_) => h,
                    }
                } else {
                    h
                },
            InternalOp::SetIntegrity { target, level } =>
                if valid_obj(h, target) {
                    spec_set_integrity_level(h, target, level)
                } else {
                    h
                },
        }
    }
}

pub open spec fn spec_apply_trace(h: HeapView, trace: Seq<InternalOp>) -> HeapView
    decreases trace.len(),
{
    if trace.len() == 0 {
        h
    } else {
        let prev = spec_apply_trace(h, trace.drop_last());
        spec_apply_op(prev, trace.last())
    }
}

pub proof fn lemma_single_op_preserves_essential_invariants(
    h: HeapView,
    op: InternalOp,
    o: ObjId,
    k: PropKeyView,
)
    requires
        heap_wf(h),
        valid_obj(h, o),
    ensures
        spec_essential_invariants_hold(h, spec_apply_op(h, op), o, k),
{
    lemma_essential_invariants_refl(h, o, k);
    match op {
        InternalOp::SetPrototypeOf { target, proto } => {
            if valid_obj(h, target) && (match proto { None => true, Some(p) => valid_obj(h, p) }) {
                theorem_set_prototype_of_invariants(h, target, proto, o, k);
            }
        },
        InternalOp::PreventExtensions { target } => {
            if valid_obj(h, target) {
                theorem_prevent_extensions_invariants(h, target, o, k);
            }
        },
        InternalOp::DefineOwnProperty { target, key, desc } => {
            if valid_obj(h, target)
                && prop_key_wf(key)
                && prop_desc_wf(desc)
                && prop_desc_refs_wf(h.objects.len() as nat, desc)
            {
                theorem_define_own_property_invariants(h, target, key, desc, o, k);
            }
        },
        InternalOp::Delete { target, key } => {
            if valid_obj(h, target) {
                theorem_delete_invariants(h, target, key, o, k);
            }
        },
        InternalOp::Set { target, key, value, receiver } => {
            if valid_obj(h, target)
                && prop_key_wf(key)
                && val_refs_wf(h.objects.len() as nat, value)
                && val_refs_wf(h.objects.len() as nat, receiver)
            {
                theorem_js_set_invariants(h, target, key, value, receiver, o, k);
            }
        },
        InternalOp::SetIntegrity { target, level } => {
            if valid_obj(h, target) {
                theorem_set_integrity_level_invariants(h, target, level, o, k);
            }
        },
    }
}

/// Master Theorem (ECMA-262 §6.1.7.3 Multi-Step Trace Invariance):
/// Across ANY arbitrary sequence `trace` of internal method operations on a well-formed `Heap`,
/// `Heap::wf`, non-extensibility monotonicity ("remains `false` forever", prototype locked,
/// no new own property keys), and non-configurable property integrity hold permanently!
pub proof fn theorem_trace_preserves_all_6_1_7_3_invariants(
    h: HeapView,
    trace: Seq<InternalOp>,
    o: ObjId,
    k: PropKeyView,
)
    requires
        heap_wf(h),
        valid_obj(h, o),
    ensures
        spec_essential_invariants_hold(h, spec_apply_trace(h, trace), o, k),
    decreases trace.len(),
{
    if trace.len() == 0 {
        lemma_essential_invariants_refl(h, o, k);
    } else {
        let prefix = trace.drop_last();
        theorem_trace_preserves_all_6_1_7_3_invariants(h, prefix, o, k);
        let mid = spec_apply_trace(h, prefix);
        lemma_single_op_preserves_essential_invariants(mid, trace.last(), o, k);
        let fin = spec_apply_op(mid, trace.last());
        lemma_essential_invariants_trans(h, mid, fin, o, k);
    }
}

} // verus!
