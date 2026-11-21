//! Ordinary Object Internal Methods (`ECMA-262 §10.1`) and Object Integrity Operations
//! (`SetIntegrityLevel` & `TestIntegrityLevel`, `§7.3.15–7.3.16`: `Object.seal`,
//! `Object.freeze`, `Object.isSealed`, `Object.isFrozen`), formally proved `exec == spec`
//! and `Heap::wf`-preserving in Verus.
use crate::descriptor::{
    clone_complete_descriptor, validate_and_apply_property_descriptor, CompleteDescriptor,
    PropertyDescriptor,
};
#[cfg(verus_keep_ghost)]
use crate::descriptor::{
    lemma_validate_nonconfigurable_invariants, prop_desc_wf, spec_complete_configurable,
    spec_complete_is_accessor, spec_complete_is_data, spec_complete_to_stored,
    spec_validate_and_apply_property_descriptor, CompleteDescView, PropDescView,
};
use crate::heap::{
    clone_js_object, clone_js_val, clone_prop_key, lookup_prop_in_vec, remove_prop_in_vec,
    upsert_prop_in_vec, Heap, JsObject, JsVal, JsValView, ObjId, PropKey, PropertyEntry,
};
#[cfg(verus_keep_ghost)]
use crate::heap::{
    array_object_wf, complete_desc_refs_wf, heap_wf, lemma_all_essential_invariants_refl,
    lemma_essential_invariants_refl, lemma_find_prop_spec, lemma_find_prop_unique_index,
    lemma_nonconfigurable_preserved_refl, lemma_proto_reaches_rank_le, lemma_remove_lookup,
    lemma_same_value_refl, lemma_set_proto_preserves_proto_wf, lemma_upsert_lookup,
    object_props_wf, object_wf, prop_desc_refs_wf, prop_key_wf, proto_wf,
    spec_all_essential_invariants, spec_essential_invariants_hold, spec_f64_bits_to_exact_u32,
    spec_find_prop, spec_length_key, spec_lookup_prop, spec_no_duplicate_keys,
    spec_nonconfigurable_preserved, spec_opt_rank, spec_proto_reaches, spec_recompute_proto_ranks,
    spec_remove_prop, spec_upsert_prop, val_refs_wf, valid_obj, HeapView, ObjectKind, ObjectView,
    PropEntryView, PropKeyView,
};
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------------------
// Outcomes for `[[Get]]` and `[[Set]]` (supporting both direct values and accessor hooks)
// ---------------------------------------------------------------------------------------

pub enum GetOutcomeView {
    Value(JsValView),
    CallGetter { getter: ObjId, receiver: JsValView },
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum GetOutcome {
    Value(JsVal),
    CallGetter { getter: ObjId, receiver: JsVal },
}

impl View for GetOutcome {
    type V = GetOutcomeView;

    open spec fn view(&self) -> GetOutcomeView {
        match self {
            GetOutcome::Value(v) => GetOutcomeView::Value(v@),
            GetOutcome::CallGetter { getter, receiver } =>
                GetOutcomeView::CallGetter { getter: *getter, receiver: receiver@ },
        }
    }
}

pub enum SetOutcomeView {
    Result(bool),
    CallSetter { setter: ObjId, receiver: JsValView, value: JsValView },
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum SetOutcome {
    Result(bool),
    CallSetter { setter: ObjId, receiver: JsVal, value: JsVal },
}

impl View for SetOutcome {
    type V = SetOutcomeView;

    open spec fn view(&self) -> SetOutcomeView {
        match self {
            SetOutcome::Result(b) => SetOutcomeView::Result(*b),
            SetOutcome::CallSetter { setter, receiver, value } =>
                SetOutcomeView::CallSetter {
                    setter: *setter,
                    receiver: receiver@,
                    value: value@,
                },
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum IntegrityLevel {
    Sealed,
    Frozen,
}

// ---------------------------------------------------------------------------------------
// §10.1.1 [[GetPrototypeOf]] & §10.1.2 [[SetPrototypeOf]]
// ---------------------------------------------------------------------------------------

/// ECMA-262 §10.1.1.1 `OrdinaryGetPrototypeOf ( O )`.
pub open spec fn spec_ordinary_get_prototype_of(h: HeapView, o: ObjId) -> Option<ObjId> {
    h.objects[o.0 as int].prototype
}

pub fn ordinary_get_prototype_of(heap: &Heap, o: ObjId) -> (res: Option<ObjId>)
    requires
        heap.wf(),
        heap.valid_obj(o),
    ensures
        res == spec_ordinary_get_prototype_of(heap@, o),
        match res {
            None => true,
            Some(pid) => heap.valid_obj(pid) && heap.proto_rank(pid) < heap.proto_rank(o),
        },
{
    heap.objects[o.0].prototype
}

fn opt_obj_eq(a: Option<ObjId>, b: Option<ObjId>) -> (r: bool)
    ensures
        r == (a == b),
{
    match (a, b) {
        (None, None) => true,
        (Some(x), Some(y)) => x.0 == y.0,
        _ => false,
    }
}

/// ECMA-262 §10.1.2.1 `OrdinarySetPrototypeOf ( O, V )`.
pub open spec fn spec_ordinary_set_prototype_of(
    h: HeapView,
    o: ObjId,
    v: Option<ObjId>,
) -> (bool, HeapView) {
    let cur = h.objects[o.0 as int].prototype;
    if v == cur {
        (true, h)
    } else if !h.objects[o.0 as int].extensible {
        (false, h)
    } else if spec_proto_reaches(h, v, o) {
        (false, h)
    } else {
        let old_obj = h.objects[o.0 as int];
        let new_obj = ObjectView { prototype: v, ..old_obj };
        let new_ranks = spec_recompute_proto_ranks(h, o, v);
        (
            true,
            HeapView {
                objects: h.objects.update(o.0 as int, new_obj),
                proto_ranks: new_ranks,
            },
        )
    }
}

/// Executable prototype-chain cycle check (`Step 7` of `OrdinarySetPrototypeOf`),
/// guaranteed to terminate in `<= proto_rank(v) + 1` steps via `spec_opt_rank`.
pub fn proto_chain_reaches(heap: &Heap, start: Option<ObjId>, target: ObjId) -> (res: bool)
    requires
        heap.wf(),
        heap.valid_obj(target),
        match start {
            None => true,
            Some(s) => heap.valid_obj(s),
        },
    ensures
        res == spec_proto_reaches(heap@, start, target),
{
    let mut p: Option<ObjId> = start;
    while p.is_some()
        invariant
            heap.wf(),
            heap.valid_obj(target),
            match p {
                None => true,
                Some(cur) => heap.valid_obj(cur),
            },
            spec_proto_reaches(heap@, start, target) == spec_proto_reaches(heap@, p, target),
        decreases spec_opt_rank(heap@, p),
    {
        let cur = p.unwrap();
        if cur.0 == target.0 {
            proof {
                assert(cur == target);
            }
            return true;
        }
        let next = heap.objects[cur.0].prototype;
        proof {
            reveal_with_fuel(spec_proto_reaches, 2);
            assert(cur != target);
            assert(spec_opt_rank(heap@, next) < spec_opt_rank(heap@, Some(cur)));
        }
        p = next;
    }
    proof {
        reveal_with_fuel(spec_proto_reaches, 2);
    }
    false
}

/// ECMA-262 §10.1.2.1 `OrdinarySetPrototypeOf ( O, V )`, proved `exec == spec` and `Heap::wf`-preserving
/// (including full cycle rejection and non-extensible `SameValue` check).
pub fn ordinary_set_prototype_of(heap: &mut Heap, o: ObjId, v: Option<ObjId>) -> (res: bool)
    requires
        old(heap).wf(),
        old(heap).valid_obj(o),
        match v {
            None => true,
            Some(vid) => old(heap).valid_obj(vid),
        },
    ensures
        final(heap).wf(),
        (res, final(heap)@) == spec_ordinary_set_prototype_of(old(heap)@, o, v),
        spec_all_essential_invariants(old(heap)@, final(heap)@),
        !spec_ordinary_is_extensible(old(heap)@, o) && v != spec_ordinary_get_prototype_of(old(heap)@, o)
            ==> (!res && final(heap)@ == old(heap)@),
{
    let cur = heap.objects[o.0].prototype;
    if opt_obj_eq(v, cur) {
        proof {
            lemma_all_essential_invariants_refl(heap@);
        }
        return true;
    }
    if !heap.objects[o.0].extensible {
        proof {
            lemma_all_essential_invariants_refl(heap@);
        }
        return false;
    }
    if proto_chain_reaches(heap, v, o) {
        proof {
            lemma_all_essential_invariants_refl(heap@);
        }
        return false;
    }
    let ghost old_h = heap@;
    let mut obj = clone_js_object(&heap.objects[o.0]);
    obj.prototype = v;
    let ghost updated_view = obj@;
    heap.objects.set(o.0, obj);
    proof {
        heap.proto_ranks@ = spec_recompute_proto_ranks(old_h, o, v);
        assert(updated_view == (ObjectView { prototype: v, ..old_h.objects[o.0 as int] }));
        assert(heap@.objects =~= old_h.objects.update(o.0 as int, updated_view));
        lemma_set_proto_preserves_proto_wf(old_h, o, v, updated_view);
        assert forall|i: int| 0 <= i < heap@.objects.len() implies
            object_wf(heap@.objects.len() as nat, #[trigger] heap@.objects[i])
        by {
            if i == o.0 as int {
                assert(old_h.objects[i].properties == updated_view.properties);
                assert(object_wf(old_h.objects.len() as nat, old_h.objects[i]));
            } else {
                assert(heap@.objects[i] == old_h.objects[i]);
                assert(object_wf(old_h.objects.len() as nat, old_h.objects[i]));
            }
        };
        assert forall|obs_o: ObjId, obs_k: PropKeyView| valid_obj(old_h, obs_o) implies
            #[trigger] spec_essential_invariants_hold(old_h, heap@, obs_o, obs_k)
        by {
            assert(heap@.objects[obs_o.0 as int].properties == old_h.objects[obs_o.0 as int].properties);
            if let Some(d) = spec_lookup_prop(old_h.objects[obs_o.0 as int].properties, obs_k) {
                if !spec_complete_configurable(d) {
                    lemma_nonconfigurable_preserved_refl(d);
                }
            }
        };
    }
    true
}

// ---------------------------------------------------------------------------------------
// §10.1.3 [[IsExtensible]] & §10.1.4 [[PreventExtensions]]
// ---------------------------------------------------------------------------------------

/// ECMA-262 §10.1.3.1 `OrdinaryIsExtensible ( O )`.
pub open spec fn spec_ordinary_is_extensible(h: HeapView, o: ObjId) -> bool {
    h.objects[o.0 as int].extensible
}

pub fn ordinary_is_extensible(heap: &Heap, o: ObjId) -> (res: bool)
    requires
        heap.wf(),
        heap.valid_obj(o),
    ensures
        res == spec_ordinary_is_extensible(heap@, o),
{
    heap.objects[o.0].extensible
}

/// ECMA-262 §10.1.4.1 `OrdinaryPreventExtensions ( O )`.
pub open spec fn spec_ordinary_prevent_extensions(h: HeapView, o: ObjId) -> HeapView {
    let old_obj = h.objects[o.0 as int];
    let new_obj = ObjectView { extensible: false, ..old_obj };
    HeapView {
        objects: h.objects.update(o.0 as int, new_obj),
        proto_ranks: h.proto_ranks,
    }
}

pub fn ordinary_prevent_extensions(heap: &mut Heap, o: ObjId) -> (res: bool)
    requires
        old(heap).wf(),
        old(heap).valid_obj(o),
    ensures
        res == true,
        final(heap).wf(),
        final(heap)@ == spec_ordinary_prevent_extensions(old(heap)@, o),
        !spec_ordinary_is_extensible(final(heap)@, o),
        spec_all_essential_invariants(old(heap)@, final(heap)@),
{
    let ghost old_h = heap@;
    let mut obj = clone_js_object(&heap.objects[o.0]);
    obj.extensible = false;
    let ghost updated_view = obj@;
    heap.objects.set(o.0, obj);
    proof {
        assert(updated_view == (ObjectView { extensible: false, ..old_h.objects[o.0 as int] }));
        assert(heap@.objects =~= old_h.objects.update(o.0 as int, updated_view));
        assert forall|i: int| 0 <= i < heap@.objects.len() implies
            object_wf(heap@.objects.len() as nat, #[trigger] heap@.objects[i])
        by {
            if i == o.0 as int {
                assert(object_wf(old_h.objects.len() as nat, old_h.objects[i]));
            } else {
                assert(heap@.objects[i] == old_h.objects[i]);
            }
        };
        assert forall|obs_o: ObjId, obs_k: PropKeyView| valid_obj(old_h, obs_o) implies
            #[trigger] spec_essential_invariants_hold(old_h, heap@, obs_o, obs_k)
        by {
            if let Some(d) = spec_lookup_prop(old_h.objects[obs_o.0 as int].properties, obs_k) {
                if !spec_complete_configurable(d) {
                    lemma_nonconfigurable_preserved_refl(d);
                }
            }
        };
    }
    true
}

// ---------------------------------------------------------------------------------------
// §10.1.5 [[GetOwnProperty]] & §10.1.6 [[DefineOwnProperty]]
// ---------------------------------------------------------------------------------------

/// ECMA-262 §10.1.5.1 `OrdinaryGetOwnProperty ( O, P )`.
pub open spec fn spec_ordinary_get_own_property(
    h: HeapView,
    o: ObjId,
    key: PropKeyView,
) -> Option<CompleteDescView> {
    spec_lookup_prop(h.objects[o.0 as int].properties, key)
}

pub fn ordinary_get_own_property(
    heap: &Heap,
    o: ObjId,
    key: &PropKey,
) -> (res: Option<CompleteDescriptor>)
    requires
        heap.wf(),
        heap.valid_obj(o),
    ensures
        ({
            let rview = match &res {
                None => None,
                Some(d) => Some(d@),
            };
            rview == spec_ordinary_get_own_property(heap@, o, key@)
        }),
        match &res {
            None => true,
            Some(d) => complete_desc_refs_wf(heap@.objects.len() as nat, d@),
        },
{
    let res = lookup_prop_in_vec(&heap.objects[o.0].properties, key);
    proof {
        let props = heap@.objects[o.0 as int].properties;
        assert(object_wf(heap@.objects.len() as nat, heap@.objects[o.0 as int]));
        lemma_find_prop_spec(props, key@);
        if let Some(idx) = spec_find_prop(props, key@) {
            assert(complete_desc_refs_wf(heap@.objects.len() as nat, props[idx as int].desc));
        }
    }
    res
}

/// Object-level `OrdinaryDefineOwnProperty ( O, P, Desc )` transition (`§10.1.6.1`),
/// shared by both Ordinary objects and Array exotic internal steps.
pub open spec fn spec_ordinary_define_on_object(
    obj: ObjectView,
    key: PropKeyView,
    desc: PropDescView,
) -> (bool, ObjectView) {
    let cur = spec_lookup_prop(obj.properties, key);
    let (ok, next_desc) =
        spec_validate_and_apply_property_descriptor(true, obj.extensible, desc, cur);
    if !ok {
        (false, obj)
    } else {
        let stored = next_desc.unwrap();
        let new_props = spec_upsert_prop(obj.properties, key, stored);
        (true, ObjectView { properties: new_props, ..obj })
    }
}

pub proof fn lemma_validate_preserves_desc_refs_wf(
    num_objs: nat,
    extensible: bool,
    desc: PropDescView,
    cur: Option<CompleteDescView>,
)
    requires
        prop_desc_wf(desc),
        prop_desc_refs_wf(num_objs, desc),
        match cur {
            None => true,
            Some(c) => complete_desc_refs_wf(num_objs, c),
        },
    ensures
        ({
            let (ok, next_opt) =
                spec_validate_and_apply_property_descriptor(true, extensible, desc, cur);
            ok ==> (next_opt is Some && complete_desc_refs_wf(num_objs, next_opt.unwrap()))
        }),
{
}

pub proof fn lemma_ordinary_define_preserves_props_wf(
    num_objs: nat,
    obj: ObjectView,
    key: PropKeyView,
    desc: PropDescView,
)
    requires
        object_props_wf(num_objs, obj.properties),
        prop_key_wf(key),
        prop_desc_wf(desc),
        prop_desc_refs_wf(num_objs, desc),
    ensures
        object_props_wf(num_objs, spec_ordinary_define_on_object(obj, key, desc).1.properties),
{
    lemma_find_prop_spec(obj.properties, key);
    let cur = spec_lookup_prop(obj.properties, key);
    if let Some(idx) = spec_find_prop(obj.properties, key) {
        assert(complete_desc_refs_wf(num_objs, obj.properties[idx as int].desc));
    }
    lemma_validate_preserves_desc_refs_wf(num_objs, obj.extensible, desc, cur);
    let (ok, next_desc) =
        spec_validate_and_apply_property_descriptor(true, obj.extensible, desc, cur);
    if ok {
        let stored = next_desc.unwrap();
        lemma_upsert_lookup(obj.properties, key, stored, key);
        let new_props = spec_upsert_prop(obj.properties, key, stored);
        assert forall|i: int| 0 <= i < new_props.len() implies
            prop_key_wf((#[trigger] new_props[i]).key)
            && complete_desc_refs_wf(num_objs, new_props[i].desc)
        by {
            match spec_find_prop(obj.properties, key) {
                Some(idx) => {
                    if i == idx as int {
                    } else {
                        assert(new_props[i] == obj.properties[i]);
                    }
                },
                None => {
                    if i < obj.properties.len() {
                        assert(new_props[i] == obj.properties[i]);
                    } else {
                        assert(new_props[i] == (PropEntryView { key, desc: stored }));
                    }
                },
            }
        };
    }
}

pub fn apply_ordinary_define_on_object(
    obj: &mut JsObject,
    key: &PropKey,
    desc: &PropertyDescriptor,
) -> (res: bool)
    requires
        prop_desc_wf(desc@),
    ensures
        (res, final(obj)@) == spec_ordinary_define_on_object(old(obj)@, key@, desc@),
{
    let cur = lookup_prop_in_vec(&obj.properties, key);
    let (ok, next_opt) = validate_and_apply_property_descriptor(true, obj.extensible, desc, &cur);
    if !ok {
        return false;
    }
    let stored = next_opt.unwrap();
    upsert_prop_in_vec(&mut obj.properties, clone_prop_key(key), stored);
    true
}

/// ECMA-262 §10.1.6.1 `OrdinaryDefineOwnProperty ( O, P, Desc )` on an Ordinary object.
pub open spec fn spec_ordinary_define_own_property(
    h: HeapView,
    o: ObjId,
    key: PropKeyView,
    desc: PropDescView,
) -> (bool, HeapView) {
    let (ok, new_obj) = spec_ordinary_define_on_object(h.objects[o.0 as int], key, desc);
    if !ok {
        (false, h)
    } else {
        (
            true,
            HeapView {
                objects: h.objects.update(o.0 as int, new_obj),
                proto_ranks: h.proto_ranks,
            },
        )
    }
}

pub proof fn lemma_ordinary_define_obj_essential(
    obj: ObjectView,
    key: PropKeyView,
    desc: PropDescView,
    k: PropKeyView,
)
    requires
        spec_no_duplicate_keys(obj.properties),
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

pub fn ordinary_define_own_property(
    heap: &mut Heap,
    o: ObjId,
    key: &PropKey,
    desc: &PropertyDescriptor,
) -> (res: bool)
    requires
        old(heap).wf(),
        old(heap).valid_obj(o),
        old(heap)@.objects[o.0 as int].kind == ObjectKind::Ordinary,
        prop_key_wf(key@),
        old(heap).desc_wf(desc@),
    ensures
        final(heap).wf(),
        (res, final(heap)@) == spec_ordinary_define_own_property(old(heap)@, o, key@, desc@),
        spec_all_essential_invariants(old(heap)@, final(heap)@),
{
    let ghost old_h = heap@;
    let mut obj = clone_js_object(&heap.objects[o.0]);
    let ok = apply_ordinary_define_on_object(&mut obj, key, desc);
    if !ok {
        proof {
            lemma_all_essential_invariants_refl(heap@);
        }
        return false;
    }
    let ghost updated_view = obj@;
    heap.objects.set(o.0, obj);
    proof {
        assert(heap@.objects =~= old_h.objects.update(o.0 as int, updated_view));
        assert(object_wf(old_h.objects.len() as nat, old_h.objects[o.0 as int]));
        lemma_ordinary_define_preserves_props_wf(
            old_h.objects.len() as nat,
            old_h.objects[o.0 as int],
            key@,
            desc@,
        );
        assert forall|i: int| 0 <= i < heap@.objects.len() implies
            object_wf(heap@.objects.len() as nat, #[trigger] heap@.objects[i])
        by {
            if i == o.0 as int {
                assert(heap@.objects[i] == updated_view);
                assert(updated_view.kind == ObjectKind::Ordinary);
            } else {
                assert(heap@.objects[i] == old_h.objects[i]);
                assert(object_wf(old_h.objects.len() as nat, old_h.objects[i]));
            }
        };
        assert forall|obs_o: ObjId, obs_k: PropKeyView| valid_obj(old_h, obs_o) implies
            #[trigger] spec_essential_invariants_hold(old_h, heap@, obs_o, obs_k)
        by {
            if obs_o == o {
                lemma_ordinary_define_obj_essential(old_h.objects[o.0 as int], key@, desc@, obs_k);
            } else {
                if let Some(d) = spec_lookup_prop(old_h.objects[obs_o.0 as int].properties, obs_k) {
                    if !spec_complete_configurable(d) {
                        lemma_nonconfigurable_preserved_refl(d);
                    }
                }
            }
        };
    }
    true
}

// ---------------------------------------------------------------------------------------
// §10.1.7 [[HasProperty]] & §10.1.8 [[Get]] (Prototype Chain Walk Bounded by `proto_rank`)
// ---------------------------------------------------------------------------------------

/// ECMA-262 §10.1.7.1 `OrdinaryHasProperty ( O, P )`.
/// Terminates unconditionally via `spec_opt_rank(h, Some(o))`.
pub open spec fn spec_ordinary_has_property(
    h: HeapView,
    o: ObjId,
    key: PropKeyView,
) -> bool
    decreases spec_opt_rank(h, Some(o)),
{
    if !valid_obj(h, o) {
        false
    } else if spec_lookup_prop(h.objects[o.0 as int].properties, key) is Some {
        true
    } else {
        match h.objects[o.0 as int].prototype {
            None => false,
            Some(parent) =>
                if spec_opt_rank(h, Some(parent)) < spec_opt_rank(h, Some(o)) {
                    spec_ordinary_has_property(h, parent, key)
                } else {
                    false
                },
        }
    }
}

pub fn ordinary_has_property(heap: &Heap, o: ObjId, key: &PropKey) -> (res: bool)
    requires
        heap.wf(),
        heap.valid_obj(o),
    ensures
        res == spec_ordinary_has_property(heap@, o, key@),
{
    let mut cur: ObjId = o;
    loop
        invariant
            heap.wf(),
            heap.valid_obj(cur),
            spec_ordinary_has_property(heap@, o, key@)
                == spec_ordinary_has_property(heap@, cur, key@),
        decreases spec_opt_rank(heap@, Some(cur)),
    {
        let own = ordinary_get_own_property(heap, cur, key);
        if own.is_some() {
            proof {
                reveal_with_fuel(spec_ordinary_has_property, 2);
            }
            return true;
        }
        match heap.objects[cur.0].prototype {
            None => {
                proof {
                    reveal_with_fuel(spec_ordinary_has_property, 2);
                }
                return false;
            },
            Some(parent) => {
                proof {
                    reveal_with_fuel(spec_ordinary_has_property, 2);
                    assert(spec_opt_rank(heap@, Some(parent)) < spec_opt_rank(heap@, Some(cur)));
                }
                cur = parent;
            },
        }
    }
}

/// ECMA-262 §10.1.8.1 `OrdinaryGet ( O, P, Receiver )`.
/// Terminates unconditionally via `spec_opt_rank(h, Some(o))`.
pub open spec fn spec_ordinary_get(
    h: HeapView,
    o: ObjId,
    key: PropKeyView,
    receiver: JsValView,
) -> GetOutcomeView
    decreases spec_opt_rank(h, Some(o)),
{
    if !valid_obj(h, o) {
        GetOutcomeView::Value(JsValView::Undefined)
    } else {
        match spec_lookup_prop(h.objects[o.0 as int].properties, key) {
            None => {
                match h.objects[o.0 as int].prototype {
                    None => GetOutcomeView::Value(JsValView::Undefined),
                    Some(parent) =>
                        if spec_opt_rank(h, Some(parent)) < spec_opt_rank(h, Some(o)) {
                            spec_ordinary_get(h, parent, key, receiver)
                        } else {
                            GetOutcomeView::Value(JsValView::Undefined)
                        },
                }
            },
            Some(CompleteDescView::Data { value, .. }) => GetOutcomeView::Value(value),
            Some(CompleteDescView::Accessor { get, .. }) => {
                match get {
                    None => GetOutcomeView::Value(JsValView::Undefined),
                    Some(getter_id) => GetOutcomeView::CallGetter { getter: getter_id, receiver },
                }
            },
        }
    }
}

pub fn ordinary_get(
    heap: &Heap,
    o: ObjId,
    key: &PropKey,
    receiver: &JsVal,
) -> (res: GetOutcome)
    requires
        heap.wf(),
        heap.valid_obj(o),
        heap.val_wf(receiver@),
    ensures
        res@ == spec_ordinary_get(heap@, o, key@, receiver@),
        match res@ {
            GetOutcomeView::Value(v) => heap.val_wf(v),
            GetOutcomeView::CallGetter { getter, receiver: r } =>
                heap.valid_obj(getter) && heap.val_wf(r),
        },
{
    let mut cur: ObjId = o;
    loop
        invariant
            heap.wf(),
            heap.valid_obj(cur),
            heap.val_wf(receiver@),
            spec_ordinary_get(heap@, o, key@, receiver@)
                == spec_ordinary_get(heap@, cur, key@, receiver@),
        decreases spec_opt_rank(heap@, Some(cur)),
    {
        let own = ordinary_get_own_property(heap, cur, key);
        match own {
            None => {
                match heap.objects[cur.0].prototype {
                    None => {
                        proof {
                            reveal_with_fuel(spec_ordinary_get, 2);
                        }
                        return GetOutcome::Value(JsVal::Undefined);
                    },
                    Some(parent) => {
                        proof {
                            reveal_with_fuel(spec_ordinary_get, 2);
                            assert(spec_opt_rank(heap@, Some(parent)) < spec_opt_rank(heap@, Some(cur)));
                        }
                        cur = parent;
                    },
                }
            },
            Some(CompleteDescriptor::Data { value, .. }) => {
                proof {
                    reveal_with_fuel(spec_ordinary_get, 2);
                }
                return GetOutcome::Value(value);
            },
            Some(CompleteDescriptor::Accessor { get, .. }) => {
                proof {
                    reveal_with_fuel(spec_ordinary_get, 2);
                }
                match get {
                    None => return GetOutcome::Value(JsVal::Undefined),
                    Some(getter_id) => {
                        return GetOutcome::CallGetter {
                            getter: getter_id,
                            receiver: clone_js_val(receiver),
                        };
                    },
                }
            },
        }
    }
}

// ---------------------------------------------------------------------------------------
// §10.1.9 [[Set]] & §10.1.9.2 `OrdinarySetWithOwnDescriptor` (for Ordinary Receiver)
// ---------------------------------------------------------------------------------------

/// ECMA-262 §10.1.9.2 `OrdinarySetWithOwnDescriptor ( O, P, V, Receiver, ownDesc )`
/// once prototype resolution has produced `effective_desc` (`ownDesc` or default writable Data).
pub open spec fn spec_finish_ordinary_set_ordinary_receiver(
    h: HeapView,
    key: PropKeyView,
    v: JsValView,
    receiver: JsValView,
    effective_desc: CompleteDescView,
) -> (SetOutcomeView, HeapView) {
    match effective_desc {
        CompleteDescView::Data { writable, .. } => {
            if !writable {
                (SetOutcomeView::Result(false), h)
            } else {
                match receiver {
                    JsValView::Object(recv_id) => {
                        let existing = spec_ordinary_get_own_property(h, recv_id, key);
                        match existing {
                            Some(CompleteDescView::Accessor { .. }) =>
                                (SetOutcomeView::Result(false), h),
                            Some(CompleteDescView::Data { writable: false, .. }) =>
                                (SetOutcomeView::Result(false), h),
                            Some(CompleteDescView::Data { writable: true, .. }) => {
                                let value_desc = PropDescView {
                                    value: Some(v),
                                    writable: None,
                                    get: None,
                                    set: None,
                                    enumerable: None,
                                    configurable: None,
                                };
                                let (ok, nh) =
                                    spec_ordinary_define_own_property(h, recv_id, key, value_desc);
                                (SetOutcomeView::Result(ok), nh)
                            },
                            None => {
                                // CreateDataProperty(Receiver, P, V)
                                let create_desc = PropDescView {
                                    value: Some(v),
                                    writable: Some(true),
                                    get: None,
                                    set: None,
                                    enumerable: Some(true),
                                    configurable: Some(true),
                                };
                                let (ok, nh) =
                                    spec_ordinary_define_own_property(h, recv_id, key, create_desc);
                                (SetOutcomeView::Result(ok), nh)
                            },
                        }
                    },
                    _ => (SetOutcomeView::Result(false), h),
                }
            }
        },
        CompleteDescView::Accessor { set, .. } => {
            match set {
                None => (SetOutcomeView::Result(false), h),
                Some(setter_id) => (
                    SetOutcomeView::CallSetter { setter: setter_id, receiver, value: v },
                    h,
                ),
            }
        },
    }
}

/// Prototype lookup phase of `OrdinarySet` / `OrdinarySetWithOwnDescriptor`:
/// walks `[[Prototype]]` from `o` until finding an own descriptor or reaching `None`
/// (in which case ECMA-262 §10.1.9.2 step 1.c synthesizes `{ value: undefined, writable: true, enumerable: true, configurable: true }`).
pub open spec fn spec_resolve_set_descriptor(
    h: HeapView,
    o: ObjId,
    key: PropKeyView,
    own_desc: Option<CompleteDescView>,
) -> CompleteDescView
    decreases spec_opt_rank(h, Some(o)), (if own_desc is None { 1int } else { 0int }),
{
    match own_desc {
        Some(d) => d,
        None => {
            if !valid_obj(h, o) {
                CompleteDescView::Data {
                    value: JsValView::Undefined,
                    writable: true,
                    enumerable: true,
                    configurable: true,
                }
            } else {
                match h.objects[o.0 as int].prototype {
                    None => CompleteDescView::Data {
                        value: JsValView::Undefined,
                        writable: true,
                        enumerable: true,
                        configurable: true,
                    },
                    Some(parent) =>
                        if spec_opt_rank(h, Some(parent)) < spec_opt_rank(h, Some(o)) {
                            let p_own = spec_lookup_prop(h.objects[parent.0 as int].properties, key);
                            spec_resolve_set_descriptor(h, parent, key, p_own)
                        } else {
                            CompleteDescView::Data {
                                value: JsValView::Undefined,
                                writable: true,
                                enumerable: true,
                                configurable: true,
                            }
                        },
                }
            }
        },
    }
}

pub open spec fn spec_ordinary_set_with_own_descriptor(
    h: HeapView,
    o: ObjId,
    key: PropKeyView,
    v: JsValView,
    receiver: JsValView,
    own_desc: Option<CompleteDescView>,
) -> (SetOutcomeView, HeapView) {
    let eff = spec_resolve_set_descriptor(h, o, key, own_desc);
    spec_finish_ordinary_set_ordinary_receiver(h, key, v, receiver, eff)
}

pub open spec fn spec_ordinary_set(
    h: HeapView,
    o: ObjId,
    key: PropKeyView,
    v: JsValView,
    receiver: JsValView,
) -> (SetOutcomeView, HeapView) {
    let own = spec_ordinary_get_own_property(h, o, key);
    spec_ordinary_set_with_own_descriptor(h, o, key, v, receiver, own)
}

pub fn resolve_set_descriptor(
    heap: &Heap,
    o: ObjId,
    key: &PropKey,
    own_desc: Option<CompleteDescriptor>,
) -> (eff: CompleteDescriptor)
    requires
        heap.wf(),
        heap.valid_obj(o),
        match &own_desc {
            None => true,
            Some(d) => complete_desc_refs_wf(heap@.objects.len() as nat, d@),
        },
    ensures
        eff@ == spec_resolve_set_descriptor(
            heap@,
            o,
            key@,
            match &own_desc {
                None => None,
                Some(d) => Some(d@),
            },
        ),
        complete_desc_refs_wf(heap@.objects.len() as nat, eff@),
{
    if let Some(d) = own_desc {
        return d;
    }
    let mut cur: ObjId = o;
    loop
        invariant
            own_desc is None,
            heap.wf(),
            heap.valid_obj(cur),
            spec_resolve_set_descriptor(heap@, o, key@, None)
                == spec_resolve_set_descriptor(heap@, cur, key@, None),
        decreases spec_opt_rank(heap@, Some(cur)),
    {
        match heap.objects[cur.0].prototype {
            None => {
                proof {
                    reveal_with_fuel(spec_resolve_set_descriptor, 2);
                }
                return CompleteDescriptor::Data {
                    value: JsVal::Undefined,
                    writable: true,
                    enumerable: true,
                    configurable: true,
                };
            },
            Some(parent) => {
                let p_own = ordinary_get_own_property(heap, parent, key);
                proof {
                    reveal_with_fuel(spec_resolve_set_descriptor, 2);
                    assert(spec_opt_rank(heap@, Some(parent)) < spec_opt_rank(heap@, Some(cur)));
                }
                if let Some(d) = p_own {
                    proof {
                        reveal_with_fuel(spec_resolve_set_descriptor, 2);
                    }
                    return d;
                }
                cur = parent;
            },
        }
    }
}

/// ECMA-262 §10.1.9.2 `OrdinarySetWithOwnDescriptor` (when `Receiver`, if an Object, is Ordinary).
/// Note: `array::js_set` generalizes `Receiver` to both Ordinary and Array exotic objects.
pub fn ordinary_set_with_own_descriptor(
    heap: &mut Heap,
    o: ObjId,
    key: &PropKey,
    v: &JsVal,
    receiver: &JsVal,
    own_desc: Option<CompleteDescriptor>,
) -> (res: SetOutcome)
    requires
        old(heap).wf(),
        old(heap).valid_obj(o),
        prop_key_wf(key@),
        old(heap).val_wf(v@),
        old(heap).val_wf(receiver@),
        match receiver {
            JsVal::Object(rid) =>
                old(heap).valid_obj(*rid)
                && old(heap)@.objects[rid.0 as int].kind == ObjectKind::Ordinary,
            _ => true,
        },
        match &own_desc {
            None => true,
            Some(d) => complete_desc_refs_wf(old(heap)@.objects.len() as nat, d@),
        },
    ensures
        final(heap).wf(),
        (res@, final(heap)@) == spec_ordinary_set_with_own_descriptor(
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
        spec_all_essential_invariants(old(heap)@, final(heap)@),
{
    let eff = resolve_set_descriptor(heap, o, key, own_desc);
    match eff {
        CompleteDescriptor::Data { writable, .. } => {
            if !writable {
                proof {
                    lemma_all_essential_invariants_refl(heap@);
                }
                return SetOutcome::Result(false);
            }
            match receiver {
                JsVal::Object(recv_id) => {
                    let existing = ordinary_get_own_property(heap, *recv_id, key);
                    match existing {
                        Some(CompleteDescriptor::Accessor { .. }) => {
                            proof {
                                lemma_all_essential_invariants_refl(heap@);
                            }
                            SetOutcome::Result(false)
                        },
                        Some(CompleteDescriptor::Data { writable: false, .. }) => {
                            proof {
                                lemma_all_essential_invariants_refl(heap@);
                            }
                            SetOutcome::Result(false)
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
                            let ok = ordinary_define_own_property(heap, *recv_id, key, &value_desc);
                            SetOutcome::Result(ok)
                        },
                        None => {
                            let create_desc =
                                PropertyDescriptor::data(clone_js_val(v), true, true, true);
                            let ok =
                                ordinary_define_own_property(heap, *recv_id, key, &create_desc);
                            SetOutcome::Result(ok)
                        },
                    }
                },
                _ => {
                    proof {
                        lemma_all_essential_invariants_refl(heap@);
                    }
                    SetOutcome::Result(false)
                },
            }
        },
        CompleteDescriptor::Accessor { set, .. } => {
            proof {
                lemma_all_essential_invariants_refl(heap@);
            }
            match set {
                None => SetOutcome::Result(false),
                Some(setter_id) => SetOutcome::CallSetter {
                    setter: setter_id,
                    receiver: clone_js_val(receiver),
                    value: clone_js_val(v),
                },
            }
        },
    }
}

/// ECMA-262 §10.1.9.1 `OrdinarySet ( O, P, V, Receiver )`.
pub fn ordinary_set(
    heap: &mut Heap,
    o: ObjId,
    key: &PropKey,
    v: &JsVal,
    receiver: &JsVal,
) -> (res: SetOutcome)
    requires
        old(heap).wf(),
        old(heap).valid_obj(o),
        prop_key_wf(key@),
        old(heap).val_wf(v@),
        old(heap).val_wf(receiver@),
        match receiver {
            JsVal::Object(rid) =>
                old(heap).valid_obj(*rid)
                && old(heap)@.objects[rid.0 as int].kind == ObjectKind::Ordinary,
            _ => true,
        },
    ensures
        final(heap).wf(),
        (res@, final(heap)@) == spec_ordinary_set(old(heap)@, o, key@, v@, receiver@),
        spec_all_essential_invariants(old(heap)@, final(heap)@),
{
    let own = ordinary_get_own_property(heap, o, key);
    ordinary_set_with_own_descriptor(heap, o, key, v, receiver, own)
}

// ---------------------------------------------------------------------------------------
// §10.1.10 [[Delete]] (Works on BOTH Ordinary AND Array Exotic Objects!)
// ---------------------------------------------------------------------------------------

/// ECMA-262 §10.1.10.1 `OrdinaryDelete ( O, P )`.
pub open spec fn spec_ordinary_delete_on_object(
    obj: ObjectView,
    key: PropKeyView,
) -> (bool, ObjectView) {
    match spec_lookup_prop(obj.properties, key) {
        None => (true, obj),
        Some(desc) => {
            if spec_complete_configurable(desc) {
                (true, ObjectView { properties: spec_remove_prop(obj.properties, key), ..obj })
            } else {
                (false, obj)
            }
        },
    }
}

pub open spec fn spec_ordinary_delete(
    h: HeapView,
    o: ObjId,
    key: PropKeyView,
) -> (bool, HeapView) {
    let (ok, new_obj) = spec_ordinary_delete_on_object(h.objects[o.0 as int], key);
    if !ok {
        (false, h)
    } else {
        (
            true,
            HeapView {
                objects: h.objects.update(o.0 as int, new_obj),
                proto_ranks: h.proto_ranks,
            },
        )
    }
}

pub proof fn lemma_delete_preserves_object_wf(
    num_objs: nat,
    obj: ObjectView,
    key: PropKeyView,
)
    requires
        object_wf(num_objs, obj),
    ensures
        object_wf(num_objs, spec_ordinary_delete_on_object(obj, key).1),
{
    let props = obj.properties;
    lemma_find_prop_spec(props, key);
    match spec_lookup_prop(props, key) {
        None => {},
        Some(desc) => {
            if spec_complete_configurable(desc) {
                let idx = spec_find_prop(props, key).unwrap();
                let ii = idx as int;
                let next_props = spec_remove_prop(props, key);
                lemma_remove_lookup(props, key, key);
                assert forall|m: int| 0 <= m < next_props.len() implies
                    prop_key_wf((#[trigger] next_props[m]).key)
                    && complete_desc_refs_wf(num_objs, next_props[m].desc)
                by {
                    let src = if m < ii { m } else { m + 1 };
                    assert(next_props[m] == props[src]);
                };
                if obj.kind == ObjectKind::Array {
                    // On an Array, `"length"` has `configurable == false`, so `key != spec_length_key()`!
                    assert(key != spec_length_key());
                    lemma_remove_lookup(props, key, spec_length_key());
                    assert(spec_lookup_prop(next_props, spec_length_key())
                        == spec_lookup_prop(props, spec_length_key()));
                    let len_desc = spec_lookup_prop(props, spec_length_key()).unwrap();
                    if let CompleteDescView::Data { value: JsValView::NumberBits(len_bits), .. } = len_desc {
                        let len_u32 = spec_f64_bits_to_exact_u32(len_bits).unwrap();
                        assert forall|m: int| 0 <= m < next_props.len() implies
                            match (#[trigger] next_props[m]).key {
                                PropKeyView::ArrayIndex(aidx) => aidx < len_u32,
                                _ => true,
                            }
                        by {
                            let src = if m < ii { m } else { m + 1 };
                            assert(next_props[m] == props[src]);
                        };
                    }
                }
            }
        },
    }
}

pub fn apply_ordinary_delete_on_object(obj: &mut JsObject, key: &PropKey) -> (res: bool)
    ensures
        (res, final(obj)@) == spec_ordinary_delete_on_object(old(obj)@, key@),
{
    let cur = lookup_prop_in_vec(&obj.properties, key);
    match cur {
        None => true,
        Some(desc) => {
            if desc.configurable() {
                remove_prop_in_vec(&mut obj.properties, key);
                true
            } else {
                false
            }
        },
    }
}

/// ECMA-262 §10.1.10.1 `OrdinaryDelete ( O, P )`, proved `exec == spec` and `Heap::wf`-preserving
/// on BOTH Ordinary and Array exotic objects.
pub fn ordinary_delete(heap: &mut Heap, o: ObjId, key: &PropKey) -> (res: bool)
    requires
        old(heap).wf(),
        old(heap).valid_obj(o),
    ensures
        final(heap).wf(),
        (res, final(heap)@) == spec_ordinary_delete(old(heap)@, o, key@),
        spec_all_essential_invariants(old(heap)@, final(heap)@),
        match spec_ordinary_get_own_property(old(heap)@, o, key@) {
            Some(d) => !spec_complete_configurable(d) ==> (!res && final(heap)@ == old(heap)@),
            None => res && final(heap)@ == old(heap)@,
        },
{
    let ghost old_h = heap@;
    let mut obj = clone_js_object(&heap.objects[o.0]);
    let ok = apply_ordinary_delete_on_object(&mut obj, key);
    if !ok {
        proof {
            lemma_all_essential_invariants_refl(heap@);
        }
        return false;
    }
    let ghost updated_view = obj@;
    heap.objects.set(o.0, obj);
    proof {
        assert(heap@.objects =~= old_h.objects.update(o.0 as int, updated_view));
        assert(object_wf(old_h.objects.len() as nat, old_h.objects[o.0 as int]));
        lemma_delete_preserves_object_wf(
            old_h.objects.len() as nat,
            old_h.objects[o.0 as int],
            key@,
        );
        if spec_lookup_prop(old_h.objects[o.0 as int].properties, key@) is None {
            assert(updated_view == old_h.objects[o.0 as int]);
            assert(heap@.objects =~= old_h.objects);
        }
        assert forall|i: int| 0 <= i < heap@.objects.len() implies
            object_wf(heap@.objects.len() as nat, #[trigger] heap@.objects[i])
        by {
            if i == o.0 as int {
                assert(heap@.objects[i] == updated_view);
            } else {
                assert(heap@.objects[i] == old_h.objects[i]);
                assert(object_wf(old_h.objects.len() as nat, old_h.objects[i]));
            }
        };
        assert forall|obs_o: ObjId, obs_k: PropKeyView| valid_obj(old_h, obs_o) implies
            #[trigger] spec_essential_invariants_hold(old_h, heap@, obs_o, obs_k)
        by {
            if obs_o == o {
                let orig_props = old_h.objects[o.0 as int].properties;
                if spec_lookup_prop(orig_props, key@) is None {
                    lemma_essential_invariants_refl(old_h, obs_o, obs_k);
                } else {
                    lemma_remove_lookup(orig_props, key@, obs_k);
                    if let Some(d_k) = spec_lookup_prop(orig_props, obs_k) {
                        if !spec_complete_configurable(d_k) {
                            assert(obs_k != key@);
                            lemma_nonconfigurable_preserved_refl(d_k);
                        }
                    }
                }
            } else {
                if let Some(d_k) = spec_lookup_prop(old_h.objects[obs_o.0 as int].properties, obs_k) {
                    if !spec_complete_configurable(d_k) {
                        lemma_nonconfigurable_preserved_refl(d_k);
                    }
                }
            }
        };
    }
    true
}

// ---------------------------------------------------------------------------------------
// §10.1.11 [[OwnPropertyKeys]] (`OrdinaryOwnPropertyKeys`: ascending indices -> strings -> symbols)
// ---------------------------------------------------------------------------------------

pub open spec fn spec_strictly_sorted_u32(s: Seq<u32>) -> bool {
    forall|a: int, b: int| 0 <= a < b < s.len() ==> (#[trigger] s[a]) < (#[trigger] s[b])
}

pub open spec fn spec_lower_bound_u32(s: Seq<u32>, x: u32, start: nat) -> nat
    decreases s.len() - start,
{
    if start >= s.len() {
        s.len()
    } else if s[start as int] >= x {
        start
    } else {
        spec_lower_bound_u32(s, x, start + 1)
    }
}

pub open spec fn spec_insert_u32_sorted(s: Seq<u32>, x: u32) -> Seq<u32> {
    let pos = spec_lower_bound_u32(s, x, 0) as int;
    s.subrange(0, pos) + seq![x] + s.subrange(pos, s.len() as int)
}

pub proof fn lemma_lower_bound_u32(s: Seq<u32>, x: u32, start: nat)
    requires
        spec_strictly_sorted_u32(s),
        start <= s.len(),
        forall|k: int| 0 <= k < start as int ==> (#[trigger] s[k]) < x,
    ensures
        ({
            let pos = spec_lower_bound_u32(s, x, start) as int;
            start as int <= pos <= s.len()
            && (forall|k: int| 0 <= k < pos ==> (#[trigger] s[k]) < x)
            && (forall|k: int| pos <= k < s.len() ==> x <= (#[trigger] s[k]))
        }),
    decreases s.len() - start,
{
    if start < s.len() {
        if s[start as int] >= x {
            let pos = start as int;
            assert forall|k: int| pos <= k < s.len() implies x <= (#[trigger] s[k]) by {
                if k > pos {
                    assert(s[pos] < s[k]);
                }
            };
        } else {
            lemma_lower_bound_u32(s, x, start + 1);
        }
    }
}

pub open spec fn spec_seq_u32_contains(s: Seq<u32>, y: u32) -> bool {
    exists|k: int| 0 <= k < s.len() && (#[trigger] s[k]) == y
}

pub open spec fn spec_props_has_array_index(props: Seq<PropEntryView>, y: u32) -> bool {
    exists|m: int| 0 <= m < props.len() && (#[trigger] props[m]).key == PropKeyView::ArrayIndex(y)
}

pub proof fn lemma_insert_u32_sorted(s: Seq<u32>, x: u32)
    requires
        spec_strictly_sorted_u32(s),
        forall|k: int| 0 <= k < s.len() ==> (#[trigger] s[k]) != x,
    ensures
        spec_strictly_sorted_u32(spec_insert_u32_sorted(s, x)),
        spec_insert_u32_sorted(s, x).len() == s.len() + 1,
        forall|y: u32|
            #[trigger] spec_seq_u32_contains(spec_insert_u32_sorted(s, x), y)
            <==> (y == x || spec_seq_u32_contains(s, y)),
{
    lemma_lower_bound_u32(s, x, 0);
    let pos = spec_lower_bound_u32(s, x, 0) as int;
    let out = spec_insert_u32_sorted(s, x);
    assert(out.len() == s.len() + 1);
    assert forall|a: int, b: int| 0 <= a < b < out.len() implies (#[trigger] out[a]) < (#[trigger] out[b]) by {
        if b < pos {
            assert(out[a] == s[a]);
            assert(out[b] == s[b]);
        } else if b == pos {
            assert(out[a] == s[a]);
            assert(out[b] == x);
        } else if a < pos && b > pos {
            assert(out[a] == s[a]);
            assert(out[b] == s[b - 1]);
            assert(s[a] < x);
            assert(x <= s[b - 1]);
            assert(s[b - 1] != x);
        } else if a == pos && b > pos {
            assert(out[a] == x);
            assert(out[b] == s[b - 1]);
            assert(x <= s[b - 1]);
            assert(s[b - 1] != x);
        } else {
            assert(out[a] == s[a - 1]);
            assert(out[b] == s[b - 1]);
        }
    };
    assert forall|y: u32|
        #[trigger] spec_seq_u32_contains(out, y)
        <==> (y == x || spec_seq_u32_contains(s, y))
    by {
        if spec_seq_u32_contains(out, y) {
            let k = choose|k: int| 0 <= k < out.len() && (#[trigger] out[k]) == y;
            if k < pos {
                assert(s[k] == y);
            } else if k == pos {
                assert(y == x);
            } else {
                assert(s[k - 1] == y);
            }
        }
        if y == x {
            assert(out[pos] == x);
        } else if spec_seq_u32_contains(s, y) {
            let k = choose|k: int| 0 <= k < s.len() && (#[trigger] s[k]) == y;
            if k < pos {
                assert(out[k] == y);
            } else {
                assert(out[k + 1] == y);
            }
        }
    };
}

pub open spec fn spec_collect_sorted_indices(props: Seq<PropEntryView>) -> Seq<u32>
    decreases props.len(),
{
    if props.len() == 0 {
        seq![]
    } else {
        let prev = spec_collect_sorted_indices(props.drop_last());
        match props.last().key {
            PropKeyView::ArrayIndex(idx) => spec_insert_u32_sorted(prev, idx),
            _ => prev,
        }
    }
}

pub open spec fn spec_collect_string_keys(props: Seq<PropEntryView>) -> Seq<PropKeyView>
    decreases props.len(),
{
    if props.len() == 0 {
        seq![]
    } else {
        let prev = spec_collect_string_keys(props.drop_last());
        match props.last().key {
            PropKeyView::Str(s) => prev.push(PropKeyView::Str(s)),
            _ => prev,
        }
    }
}

pub open spec fn spec_collect_symbol_keys(props: Seq<PropEntryView>) -> Seq<PropKeyView>
    decreases props.len(),
{
    if props.len() == 0 {
        seq![]
    } else {
        let prev = spec_collect_symbol_keys(props.drop_last());
        match props.last().key {
            PropKeyView::Symbol(sym) => prev.push(PropKeyView::Symbol(sym)),
            _ => prev,
        }
    }
}

/// ECMA-262 §10.1.11.1 `OrdinaryOwnPropertyKeys ( O )`:
/// 1. Array indices in ascending numeric order;
/// 2. Non-index String keys in chronological creation order;
/// 3. Symbol keys in chronological creation order.
pub open spec fn spec_ordinary_own_property_keys_from_props(
    props: Seq<PropEntryView>,
) -> Seq<PropKeyView> {
    let sorted_idxs = spec_collect_sorted_indices(props);
    let idx_keys = Seq::new(sorted_idxs.len(), |i: int| PropKeyView::ArrayIndex(sorted_idxs[i]));
    idx_keys + spec_collect_string_keys(props) + spec_collect_symbol_keys(props)
}

pub open spec fn spec_ordinary_own_property_keys(h: HeapView, o: ObjId) -> Seq<PropKeyView> {
    spec_ordinary_own_property_keys_from_props(h.objects[o.0 as int].properties)
}

pub proof fn lemma_collect_sorted_indices_props(props: Seq<PropEntryView>)
    requires
        spec_no_duplicate_keys(props),
    ensures
        spec_strictly_sorted_u32(spec_collect_sorted_indices(props)),
        forall|idx: u32|
            #[trigger] spec_seq_u32_contains(spec_collect_sorted_indices(props), idx)
            <==> spec_props_has_array_index(props, idx),
    decreases props.len(),
{
    if props.len() > 0 {
        let prefix = props.drop_last();
        assert(spec_no_duplicate_keys(prefix));
        lemma_collect_sorted_indices_props(prefix);
        let prev = spec_collect_sorted_indices(prefix);
        match props.last().key {
            PropKeyView::ArrayIndex(idx) => {
                assert forall|k: int| 0 <= k < prev.len() implies (#[trigger] prev[k]) != idx by {
                    if prev[k] == idx {
                        assert(spec_seq_u32_contains(prev, idx));
                        let m = choose|m: int| 0 <= m < prefix.len() && (#[trigger] prefix[m]).key == PropKeyView::ArrayIndex(idx);
                        assert(props[m].key == props[(props.len() - 1) as int].key);
                    }
                };
                lemma_insert_u32_sorted(prev, idx);
                let cur = spec_insert_u32_sorted(prev, idx);
                assert forall|y: u32|
                    #[trigger] spec_seq_u32_contains(cur, y)
                    <==> spec_props_has_array_index(props, y)
                by {
                    if spec_seq_u32_contains(cur, y) {
                        if y == idx {
                            assert(props[(props.len() - 1) as int].key == PropKeyView::ArrayIndex(y));
                        } else {
                            assert(spec_seq_u32_contains(prev, y));
                            let m = choose|m: int| 0 <= m < prefix.len() && (#[trigger] prefix[m]).key == PropKeyView::ArrayIndex(y);
                            assert(props[m].key == PropKeyView::ArrayIndex(y));
                        }
                    }
                    if spec_props_has_array_index(props, y) {
                        let m = choose|m: int| 0 <= m < props.len() && (#[trigger] props[m]).key == PropKeyView::ArrayIndex(y);
                        if m == props.len() - 1 {
                            assert(y == idx);
                        } else {
                            assert(prefix[m].key == PropKeyView::ArrayIndex(y));
                            assert(spec_props_has_array_index(prefix, y));
                            assert(spec_seq_u32_contains(prev, y));
                        }
                    }
                };
            },
            _ => {
                assert forall|y: u32|
                    #[trigger] spec_seq_u32_contains(prev, y)
                    <==> spec_props_has_array_index(props, y)
                by {
                    if spec_seq_u32_contains(prev, y) {
                        let m = choose|m: int| 0 <= m < prefix.len() && (#[trigger] prefix[m]).key == PropKeyView::ArrayIndex(y);
                        assert(props[m].key == PropKeyView::ArrayIndex(y));
                    }
                    if spec_props_has_array_index(props, y) {
                        let m = choose|m: int| 0 <= m < props.len() && (#[trigger] props[m]).key == PropKeyView::ArrayIndex(y);
                        assert(m < prefix.len());
                        assert(prefix[m].key == PropKeyView::ArrayIndex(y));
                        assert(spec_props_has_array_index(prefix, y));
                    }
                };
            },
        }
    }
}

fn insert_u32_sorted_exec(sorted: &Vec<u32>, x: u32) -> (out: Vec<u32>)
    requires
        spec_strictly_sorted_u32(sorted@),
    ensures
        out@ == spec_insert_u32_sorted(sorted@, x),
{
    let n = sorted.len();
    let mut pos: usize = 0;
    while pos < n && sorted[pos] < x
        invariant
            pos <= n,
            n == sorted@.len(),
            spec_strictly_sorted_u32(sorted@),
            spec_lower_bound_u32(sorted@, x, 0) == spec_lower_bound_u32(sorted@, x, pos as nat),
        decreases n - pos,
    {
        pos += 1;
    }
    proof {
        assert(pos as nat == spec_lower_bound_u32(sorted@, x, 0));
    }
    let mut out: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    while i < pos
        invariant
            i <= pos,
            pos <= n,
            n == sorted@.len(),
            out@ == sorted@.subrange(0, i as int),
        decreases pos - i,
    {
        out.push(sorted[i]);
        proof {
            assert(sorted@.subrange(0, (i + 1) as int) =~= sorted@.subrange(0, i as int).push(sorted@[i as int]));
        }
        i += 1;
    }
    out.push(x);
    let mut j: usize = pos;
    while j < n
        invariant
            pos <= j <= n,
            n == sorted@.len(),
            out@ == sorted@.subrange(0, pos as int) + seq![x] + sorted@.subrange(pos as int, j as int),
        decreases n - j,
    {
        out.push(sorted[j]);
        proof {
            assert(
                (sorted@.subrange(0, pos as int) + seq![x] + sorted@.subrange(pos as int, j as int)).push(sorted@[j as int])
                =~= sorted@.subrange(0, pos as int) + seq![x] + sorted@.subrange(pos as int, (j + 1) as int)
            );
        }
        j += 1;
    }
    out
}

fn partition_own_keys(
    props: &Vec<PropertyEntry>,
) -> (res: (Vec<u32>, Vec<PropKey>, Vec<PropKey>))
    requires
        spec_no_duplicate_keys(Seq::new(props@.len(), |k: int| props@[k]@)),
    ensures
        ({
            let pview = Seq::new(props@.len(), |k: int| props@[k]@);
            res.0@ == spec_collect_sorted_indices(pview)
            && Seq::new(res.1@.len(), |k: int| res.1@[k]@) == spec_collect_string_keys(pview)
            && Seq::new(res.2@.len(), |k: int| res.2@[k]@) == spec_collect_symbol_keys(pview)
        }),
{
    let ghost pview = Seq::new(props@.len(), |k: int| props@[k]@);
    let n = props.len();
    let mut sorted_idxs: Vec<u32> = Vec::new();
    let mut str_keys: Vec<PropKey> = Vec::new();
    let mut sym_keys: Vec<PropKey> = Vec::new();

    let mut i: usize = 0;
    proof {
        assert(pview.subrange(0, 0) =~= Seq::<PropEntryView>::empty());
    }
    while i < n
        invariant
            i <= n,
            n == props@.len(),
            pview == Seq::new(props@.len(), |k: int| props@[k]@),
            spec_no_duplicate_keys(pview),
            sorted_idxs@ == spec_collect_sorted_indices(pview.subrange(0, i as int)),
            spec_strictly_sorted_u32(sorted_idxs@),
            Seq::new(str_keys@.len(), |k: int| str_keys@[k]@)
                == spec_collect_string_keys(pview.subrange(0, i as int)),
            Seq::new(sym_keys@.len(), |k: int| sym_keys@[k]@)
                == spec_collect_symbol_keys(pview.subrange(0, i as int)),
        decreases n - i,
    {
        let ghost prev_sub = pview.subrange(0, i as int);
        let ghost next_sub = pview.subrange(0, (i + 1) as int);
        proof {
            assert(next_sub.drop_last() =~= prev_sub);
            assert(next_sub.last() == pview[i as int]);
            assert(spec_no_duplicate_keys(next_sub));
        }
        match &props[i].key {
            PropKey::ArrayIndex(idx) => {
                sorted_idxs = insert_u32_sorted_exec(&sorted_idxs, *idx);
                proof {
                    lemma_collect_sorted_indices_props(next_sub);
                }
            },
            PropKey::Str(s) => {
                let ghost old_strs = Seq::new(str_keys@.len(), |k: int| str_keys@[k]@);
                str_keys.push(PropKey::Str(crate::heap::clone_vec_u16(s)));
                proof {
                    let new_strs = Seq::new(str_keys@.len(), |k: int| str_keys@[k]@);
                    assert(new_strs =~= old_strs.push(PropKeyView::Str(s@)));
                }
            },
            PropKey::Symbol(sym) => {
                let ghost old_syms = Seq::new(sym_keys@.len(), |k: int| sym_keys@[k]@);
                sym_keys.push(PropKey::Symbol(*sym));
                proof {
                    let new_syms = Seq::new(sym_keys@.len(), |k: int| sym_keys@[k]@);
                    assert(new_syms =~= old_syms.push(PropKeyView::Symbol(*sym)));
                }
            },
        }
        i += 1;
    }
    proof {
        assert(pview.subrange(0, n as int) =~= pview);
    }
    (sorted_idxs, str_keys, sym_keys)
}

pub fn collect_sorted_array_indices(props: &Vec<PropertyEntry>) -> (sorted_idxs: Vec<u32>)
    requires
        spec_no_duplicate_keys(Seq::new(props@.len(), |k: int| props@[k]@)),
    ensures
        sorted_idxs@ == spec_collect_sorted_indices(Seq::new(props@.len(), |k: int| props@[k]@)),
        spec_strictly_sorted_u32(sorted_idxs@),
        forall|idx: u32|
            #[trigger] spec_seq_u32_contains(sorted_idxs@, idx)
            <==> spec_props_has_array_index(Seq::new(props@.len(), |k: int| props@[k]@), idx),
{
    let (sorted_idxs, _, _) = partition_own_keys(props);
    proof {
        let pview = Seq::new(props@.len(), |k: int| props@[k]@);
        lemma_collect_sorted_indices_props(pview);
    }
    sorted_idxs
}

fn append_prop_keys(out: &mut Vec<PropKey>, extra: &Vec<PropKey>)
    ensures
        Seq::new(final(out)@.len(), |m: int| final(out)@[m]@)
            == Seq::new(old(out)@.len(), |m: int| old(out)@[m]@)
                + Seq::new(extra@.len(), |m: int| extra@[m]@),
{
    let ghost base = Seq::new(old(out)@.len(), |m: int| old(out)@[m]@);
    let ghost ext_view = Seq::new(extra@.len(), |m: int| extra@[m]@);
    let n = extra.len();
    let mut i: usize = 0;
    proof {
        assert(ext_view.subrange(0, 0) =~= Seq::<PropKeyView>::empty());
        assert(base + Seq::<PropKeyView>::empty() =~= base);
    }
    while i < n
        invariant
            i <= n,
            n == extra@.len(),
            ext_view == Seq::new(extra@.len(), |m: int| extra@[m]@),
            Seq::new(out@.len(), |m: int| out@[m]@) == base + ext_view.subrange(0, i as int),
        decreases n - i,
    {
        let k = clone_prop_key(&extra[i]);
        let ghost before = Seq::new(out@.len(), |m: int| out@[m]@);
        out.push(k);
        proof {
            let after = Seq::new(out@.len(), |m: int| out@[m]@);
            assert(after =~= before.push(ext_view[i as int]));
            assert(
                (base + ext_view.subrange(0, i as int)).push(ext_view[i as int])
                =~= base + ext_view.subrange(0, (i + 1) as int)
            );
        }
        i += 1;
    }
    proof {
        assert(ext_view.subrange(0, n as int) =~= ext_view);
    }
}

/// ECMA-262 §10.1.11.1 `OrdinaryOwnPropertyKeys ( O )`, proved `exec == spec`
/// with strictly sorted array indices, insertion-order strings, and insertion-order symbols.
pub fn ordinary_own_property_keys(heap: &Heap, o: ObjId) -> (keys: Vec<PropKey>)
    requires
        heap.wf(),
        heap.valid_obj(o),
    ensures
        Seq::new(keys@.len(), |i: int| keys@[i]@) == spec_ordinary_own_property_keys(heap@, o),
{
    let props = &heap.objects[o.0].properties;
    proof {
        assert(object_wf(heap@.objects.len() as nat, heap@.objects[o.0 as int]));
    }
    let (sorted_idxs, str_keys, sym_keys) = partition_own_keys(props);

    let mut out: Vec<PropKey> = Vec::new();
    let n_idx = sorted_idxs.len();
    let mut a: usize = 0;
    while a < n_idx
        invariant
            a <= n_idx,
            n_idx == sorted_idxs@.len(),
            out@.len() == a as int,
            forall|m: int| 0 <= m < a as int ==> (#[trigger] out@[m])@ == PropKeyView::ArrayIndex(sorted_idxs@[m]),
        decreases n_idx - a,
    {
        out.push(PropKey::ArrayIndex(sorted_idxs[a]));
        a += 1;
    }
    let ghost idx_keys_view = Seq::new(sorted_idxs@.len(), |m: int| PropKeyView::ArrayIndex(sorted_idxs@[m]));
    proof {
        assert(Seq::new(out@.len(), |m: int| out@[m]@) =~= idx_keys_view);
    }
    append_prop_keys(&mut out, &str_keys);
    append_prop_keys(&mut out, &sym_keys);
    out
}

// ---------------------------------------------------------------------------------------
// §7.3.15 `SetIntegrityLevel` & §7.3.16 `TestIntegrityLevel`
// (`Object.seal`, `Object.freeze`, `Object.isSealed`, `Object.isFrozen`)
// Works on BOTH Ordinary AND Array Exotic Objects!
// ---------------------------------------------------------------------------------------

pub open spec fn spec_entry_matches_integrity(
    d: CompleteDescView,
    level: IntegrityLevel,
) -> bool {
    match level {
        IntegrityLevel::Sealed => !spec_complete_configurable(d),
        IntegrityLevel::Frozen =>
            !spec_complete_configurable(d)
            && (match d {
                CompleteDescView::Data { writable, .. } => !writable,
                CompleteDescView::Accessor { .. } => true,
            }),
    }
}

/// ECMA-262 §7.3.16 `TestIntegrityLevel ( O, level )`.
pub open spec fn spec_test_integrity_level_obj(
    obj: ObjectView,
    level: IntegrityLevel,
) -> bool {
    !obj.extensible
        && (forall|i: int|
            0 <= i < obj.properties.len() ==> spec_entry_matches_integrity(
                (#[trigger] obj.properties[i]).desc,
                level,
            ))
}

pub open spec fn spec_test_integrity_level(
    h: HeapView,
    o: ObjId,
    level: IntegrityLevel,
) -> bool {
    spec_test_integrity_level_obj(h.objects[o.0 as int], level)
}

pub open spec fn spec_harden_descriptor(
    d: CompleteDescView,
    level: IntegrityLevel,
) -> CompleteDescView {
    match (d, level) {
        (CompleteDescView::Data { value, writable, enumerable, configurable: _ }, IntegrityLevel::Sealed) =>
            CompleteDescView::Data { value, writable, enumerable, configurable: false },
        (CompleteDescView::Data { value, writable: _, enumerable, configurable: _ }, IntegrityLevel::Frozen) =>
            CompleteDescView::Data { value, writable: false, enumerable, configurable: false },
        (CompleteDescView::Accessor { get, set, enumerable, configurable: _ }, _) =>
            CompleteDescView::Accessor { get, set, enumerable, configurable: false },
    }
}

/// ECMA-262 §7.3.15 `SetIntegrityLevel ( O, level )` on Ordinary or Array exotic object `O`.
pub open spec fn spec_set_integrity_level_obj(
    obj: ObjectView,
    level: IntegrityLevel,
) -> ObjectView {
    ObjectView {
        kind: obj.kind,
        prototype: obj.prototype,
        extensible: false,
        properties: Seq::new(
            obj.properties.len(),
            |i: int| PropEntryView {
                key: obj.properties[i].key,
                desc: spec_harden_descriptor(obj.properties[i].desc, level),
            },
        ),
    }
}

pub open spec fn spec_set_integrity_level(
    h: HeapView,
    o: ObjId,
    level: IntegrityLevel,
) -> HeapView {
    HeapView {
        objects: h.objects.update(
            o.0 as int,
            spec_set_integrity_level_obj(h.objects[o.0 as int], level),
        ),
        proto_ranks: h.proto_ranks,
    }
}

pub proof fn lemma_set_integrity_preserves_wf_and_satisfies_test(
    num_objs: nat,
    obj: ObjectView,
    level: IntegrityLevel,
)
    requires
        object_wf(num_objs, obj),
    ensures
        object_wf(num_objs, spec_set_integrity_level_obj(obj, level)),
        spec_test_integrity_level_obj(spec_set_integrity_level_obj(obj, level), level),
        level == IntegrityLevel::Frozen
            ==> spec_test_integrity_level_obj(spec_set_integrity_level_obj(obj, level), IntegrityLevel::Sealed),
{
    let out = spec_set_integrity_level_obj(obj, level);
    assert(spec_no_duplicate_keys(out.properties));
    assert forall|i: int| 0 <= i < out.properties.len() implies
        prop_key_wf((#[trigger] out.properties[i]).key)
        && complete_desc_refs_wf(num_objs, out.properties[i].desc)
    by {
        assert(prop_key_wf(obj.properties[i].key));
        assert(complete_desc_refs_wf(num_objs, obj.properties[i].desc));
    };
    if obj.kind == ObjectKind::Array {
        lemma_find_prop_spec(obj.properties, spec_length_key());
        let lidx = spec_find_prop(obj.properties, spec_length_key()).unwrap();
        assert(out.properties[lidx as int].key == spec_length_key());
        lemma_find_prop_unique_index(out.properties, spec_length_key(), lidx as int);
        let len_desc = spec_lookup_prop(obj.properties, spec_length_key()).unwrap();
        if let CompleteDescView::Data { value: JsValView::NumberBits(len_bits), .. } = len_desc {
            let len_u32 = spec_f64_bits_to_exact_u32(len_bits).unwrap();
            assert forall|i: int| 0 <= i < out.properties.len() implies
                match (#[trigger] out.properties[i]).key {
                    PropKeyView::ArrayIndex(aidx) => aidx < len_u32,
                    _ => true,
                }
            by {
                assert(out.properties[i].key == obj.properties[i].key);
            };
        }
    }
}

pub proof fn lemma_frozen_implies_sealed(h: HeapView, o: ObjId)
    requires
        valid_obj(h, o),
        spec_test_integrity_level(h, o, IntegrityLevel::Frozen),
    ensures
        spec_test_integrity_level(h, o, IntegrityLevel::Sealed),
{
    let props = h.objects[o.0 as int].properties;
    assert forall|i: int| 0 <= i < props.len() implies
        spec_entry_matches_integrity((#[trigger] props[i]).desc, IntegrityLevel::Sealed)
    by {
        assert(spec_entry_matches_integrity(props[i].desc, IntegrityLevel::Frozen));
    };
}

/// ECMA-262 §7.3.16 `TestIntegrityLevel ( O, level )`.
pub fn test_integrity_level(heap: &Heap, o: ObjId, level: IntegrityLevel) -> (res: bool)
    requires
        heap.wf(),
        heap.valid_obj(o),
    ensures
        res == spec_test_integrity_level(heap@, o, level),
{
    if heap.objects[o.0].extensible {
        return false;
    }
    let props = &heap.objects[o.0].properties;
    let ghost pview = heap@.objects[o.0 as int].properties;
    let n = props.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            !heap@.objects[o.0 as int].extensible,
            n == props@.len(),
            n == pview.len(),
            pview == heap@.objects[o.0 as int].properties,
            pview == Seq::new(props@.len(), |k: int| props@[k]@),
            forall|m: int|
                0 <= m < i as int ==> spec_entry_matches_integrity((#[trigger] pview[m]).desc, level),
        decreases n - i,
    {
        let d = &props[i].desc;
        if d.configurable() {
            proof {
                assert(pview[i as int] == props@[i as int]@);
                assert(!spec_entry_matches_integrity(pview[i as int].desc, level));
                assert(!spec_test_integrity_level_obj(heap@.objects[o.0 as int], level));
            }
            return false;
        }
        if let IntegrityLevel::Frozen = level {
            if let CompleteDescriptor::Data { writable: true, .. } = d {
                proof {
                    assert(pview[i as int] == props@[i as int]@);
                    assert(!spec_entry_matches_integrity(pview[i as int].desc, level));
                    assert(!spec_test_integrity_level_obj(heap@.objects[o.0 as int], level));
                }
                return false;
            }
        }
        proof {
            assert(pview[i as int] == props@[i as int]@);
            assert(spec_entry_matches_integrity(pview[i as int].desc, level));
        }
        i += 1;
    }
    true
}

/// ECMA-262 §7.3.15 `SetIntegrityLevel ( O, level )`: prevents extensions and applies
/// `{ configurable: false }` (`Sealed`) or `{ configurable: false, writable: false }` (`Frozen`)
/// to every own property via `ValidateAndApplyPropertyDescriptor`.
pub fn set_integrity_level(heap: &mut Heap, o: ObjId, level: IntegrityLevel) -> (res: bool)
    requires
        old(heap).wf(),
        old(heap).valid_obj(o),
    ensures
        res == true,
        final(heap).wf(),
        final(heap)@ == spec_set_integrity_level(old(heap)@, o, level),
        spec_test_integrity_level(final(heap)@, o, level),
        spec_all_essential_invariants(old(heap)@, final(heap)@),
{
    let ghost old_h = heap@;
    let ghost orig_obj = old_h.objects[o.0 as int];
    let mut obj = clone_js_object(&heap.objects[o.0]);
    obj.extensible = false;

    let n = obj.properties.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == obj.properties@.len(),
            n == orig_obj.properties.len(),
            obj.kind == orig_obj.kind,
            obj.prototype == orig_obj.prototype,
            obj.extensible == false,
            forall|m: int|
                0 <= m < i as int ==> (#[trigger] obj.properties@[m])@
                    == (PropEntryView {
                        key: orig_obj.properties[m].key,
                        desc: spec_harden_descriptor(orig_obj.properties[m].desc, level),
                    }),
            forall|m: int|
                i as int <= m < n as int ==> (#[trigger] obj.properties@[m])@
                    == orig_obj.properties[m],
        decreases n - i,
    {
        let cur_desc = clone_complete_descriptor(&obj.properties[i].desc);
        let patch = match (&cur_desc, level) {
            (_, IntegrityLevel::Sealed) => PropertyDescriptor {
                value: None,
                writable: None,
                get: None,
                set: None,
                enumerable: None,
                configurable: Some(false),
            },
            (CompleteDescriptor::Accessor { .. }, IntegrityLevel::Frozen) => PropertyDescriptor {
                value: None,
                writable: None,
                get: None,
                set: None,
                enumerable: None,
                configurable: Some(false),
            },
            (CompleteDescriptor::Data { .. }, IntegrityLevel::Frozen) => PropertyDescriptor {
                value: None,
                writable: Some(false),
                get: None,
                set: None,
                enumerable: None,
                configurable: Some(false),
            },
        };
        let cur_opt = Some(cur_desc);
        let (_ok, next_opt) = validate_and_apply_property_descriptor(true, false, &patch, &cur_opt);
        proof {
            assert(_ok);
            assert(next_opt.unwrap()@ == spec_harden_descriptor(orig_obj.properties[i as int].desc, level));
        }
        let next_desc = next_opt.unwrap();
        let entry_key = clone_prop_key(&obj.properties[i].key);
        obj.properties.set(i, PropertyEntry { key: entry_key, desc: next_desc });
        i += 1;
    }

    let ghost updated_view = obj@;
    heap.objects.set(o.0, obj);
    proof {
        assert(updated_view.properties =~= spec_set_integrity_level_obj(orig_obj, level).properties);
        assert(updated_view == spec_set_integrity_level_obj(orig_obj, level));
        assert(heap@.objects =~= old_h.objects.update(o.0 as int, spec_set_integrity_level_obj(orig_obj, level)));
        lemma_set_integrity_preserves_wf_and_satisfies_test(
            old_h.objects.len() as nat,
            orig_obj,
            level,
        );
        assert forall|k: int| 0 <= k < heap@.objects.len() implies
            object_wf(heap@.objects.len() as nat, #[trigger] heap@.objects[k])
        by {
            if k == o.0 as int {
                assert(heap@.objects[k] == spec_set_integrity_level_obj(orig_obj, level));
            } else {
                assert(heap@.objects[k] == old_h.objects[k]);
                assert(object_wf(old_h.objects.len() as nat, old_h.objects[k]));
            }
        };
        assert forall|obs_o: ObjId, obs_k: PropKeyView| valid_obj(old_h, obs_o) implies
            #[trigger] spec_essential_invariants_hold(old_h, heap@, obs_o, obs_k)
        by {
            if obs_o != o {
                if let Some(old_d) = spec_lookup_prop(old_h.objects[obs_o.0 as int].properties, obs_k) {
                    if !spec_complete_configurable(old_d) {
                        lemma_nonconfigurable_preserved_refl(old_d);
                    }
                }
            } else {
                let new_props = heap@.objects[o.0 as int].properties;
                lemma_find_prop_spec(orig_obj.properties, obs_k);
                match spec_find_prop(orig_obj.properties, obs_k) {
                    None => {
                        assert forall|m: int| 0 <= m < new_props.len() implies
                            (#[trigger] new_props[m]).key != obs_k
                        by {
                            assert(new_props[m].key == orig_obj.properties[m].key);
                        };
                        lemma_find_prop_spec(new_props, obs_k);
                    },
                    Some(idx) => {
                        assert(new_props[idx as int].key == obs_k);
                        lemma_find_prop_unique_index(new_props, obs_k, idx as int);
                        let old_d = orig_obj.properties[idx as int].desc;
                        if !spec_complete_configurable(old_d) {
                            if let CompleteDescView::Data { value: v, .. } = old_d {
                                lemma_same_value_refl(v);
                            }
                        }
                    },
                }
            }
        };
    }
    true
}

/// `Object.seal ( O )` (`§20.1.2.20`).
pub fn object_seal(heap: &mut Heap, o: ObjId) -> (res: ObjId)
    requires
        old(heap).wf(),
        old(heap).valid_obj(o),
    ensures
        res == o,
        final(heap).wf(),
        final(heap)@ == spec_set_integrity_level(old(heap)@, o, IntegrityLevel::Sealed),
        spec_test_integrity_level(final(heap)@, o, IntegrityLevel::Sealed),
        spec_all_essential_invariants(old(heap)@, final(heap)@),
{
    let _ = set_integrity_level(heap, o, IntegrityLevel::Sealed);
    o
}

/// `Object.freeze ( O )` (`§20.1.2.6`).
pub fn object_freeze(heap: &mut Heap, o: ObjId) -> (res: ObjId)
    requires
        old(heap).wf(),
        old(heap).valid_obj(o),
    ensures
        res == o,
        final(heap).wf(),
        final(heap)@ == spec_set_integrity_level(old(heap)@, o, IntegrityLevel::Frozen),
        spec_test_integrity_level(final(heap)@, o, IntegrityLevel::Frozen),
        spec_test_integrity_level(final(heap)@, o, IntegrityLevel::Sealed),
        spec_all_essential_invariants(old(heap)@, final(heap)@),
{
    let _ = set_integrity_level(heap, o, IntegrityLevel::Frozen);
    proof {
        lemma_frozen_implies_sealed(heap@, o);
    }
    o
}

/// `Object.isSealed ( O )` (`§20.1.2.16`).
pub fn object_is_sealed(heap: &Heap, o: ObjId) -> (res: bool)
    requires
        heap.wf(),
        heap.valid_obj(o),
    ensures
        res == spec_test_integrity_level(heap@, o, IntegrityLevel::Sealed),
{
    test_integrity_level(heap, o, IntegrityLevel::Sealed)
}

/// `Object.isFrozen ( O )` (`§20.1.2.15`).
pub fn object_is_frozen(heap: &Heap, o: ObjId) -> (res: bool)
    requires
        heap.wf(),
        heap.valid_obj(o),
    ensures
        res == spec_test_integrity_level(heap@, o, IntegrityLevel::Frozen),
{
    test_integrity_level(heap, o, IntegrityLevel::Frozen)
}

} // verus!
