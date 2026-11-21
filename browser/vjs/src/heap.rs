//! Realm-tagged Arena Object Heap (`ObjId`, `RealmId`, `Heap`), Ordinary / Array / Function /
//! Error objects, Per-Realm Heap Quota enforcement, Cross-Realm Isolation theorem, and
//! Safe Iterative Worklist Mark-Sweep Garbage Collector proved `exec == spec` with `decreases`.
use crate::ast::FuncId;
use crate::env::{Binding, BindingStatus, EnvArena, EnvId, EnvSlot, SpecEnvSlot};
#[cfg(verus_keep_ghost)]
use crate::env::{env_wf, spec_bindings_view, spec_sweep_envs, SpecBindingStatus, SpecEnvArena};
use crate::value::{
    clone_js_str, clone_val, js_str_eq, num_from_usize, num_to_uint32, prim_to_number, JsStr,
    ObjId, SpecVal, Val,
};
#[cfg(verus_keep_ghost)]
use crate::value::{spec_num_exact_safe_int, spec_num_from_usize, spec_prim_to_number, spec_to_uint32};
use vstd::prelude::*;

verus! {

/// Per-realm isolation tag (§9.3 Realms).
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct RealmId(pub u32);

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum ErrorKind {
    Error,
    ReferenceError,
    TypeError,
    SyntaxError,
    RangeError,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum BuiltinFn {
    ErrorCtor(ErrorKind),
    StringConv,
    NumberConv,
    BooleanConv,
    ObjectCtor,
    ObjectIs,
    ObjectKeys,
    ObjectToString,
    ObjectHasOwnProperty,
    ArrayCtor,
    ArrayIsArray,
    ArrayPush,
    ArrayPop,
    ArrayJoin,
    ErrorToString,
    FunctionCall,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct PropEntry {
    pub key: JsStr,
    pub value: Val,
    pub writable: bool,
    pub enumerable: bool,
    pub configurable: bool,
}

pub struct SpecPropEntry {
    pub key: Seq<u16>,
    pub value: SpecVal,
    pub writable: bool,
    pub enumerable: bool,
    pub configurable: bool,
}

impl View for PropEntry {
    type V = SpecPropEntry;

    open spec fn view(&self) -> SpecPropEntry {
        SpecPropEntry {
            key: self.key@,
            value: self.value@,
            writable: self.writable,
            enumerable: self.enumerable,
            configurable: self.configurable,
        }
    }
}

pub fn clone_prop_entry(p: &PropEntry) -> (r: PropEntry)
    ensures r@ == p@,
{
    PropEntry {
        key: clone_js_str(&p.key),
        value: clone_val(&p.value),
        writable: p.writable,
        enumerable: p.enumerable,
        configurable: p.configurable,
    }
}

pub open spec fn spec_props_view(ps: Seq<PropEntry>) -> Seq<SpecPropEntry> {
    Seq::new(ps.len(), |i: int| ps[i]@)
}

#[allow(inconsistent_fields)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ObjectKind {
    Ordinary,
    Array { length: usize },
    Function {
        func_id: FuncId,
        env: EnvId,
        is_strict: bool,
        is_arrow: bool,
        prototype_obj: Option<ObjId>,
    },
    BuiltinFunction {
        builtin: BuiltinFn,
        prototype_obj: Option<ObjId>,
    },
    Error { kind: ErrorKind },
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct HeapObject {
    pub realm: RealmId,
    pub prototype: Option<ObjId>,
    pub extensible: bool,
    pub kind: ObjectKind,
    pub props: Vec<PropEntry>,
}

pub struct SpecHeapObject {
    pub realm: RealmId,
    pub prototype: Option<ObjId>,
    pub extensible: bool,
    pub kind: ObjectKind,
    pub props: Seq<SpecPropEntry>,
}

impl View for HeapObject {
    type V = SpecHeapObject;

    open spec fn view(&self) -> SpecHeapObject {
        SpecHeapObject {
            realm: self.realm,
            prototype: self.prototype,
            extensible: self.extensible,
            kind: self.kind,
            props: spec_props_view(self.props@),
        }
    }
}

pub fn clone_heap_object(obj: &HeapObject) -> (r: HeapObject)
    ensures r@ == obj@,
{
    let n = obj.props.len();
    let mut ps: Vec<PropEntry> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n == obj.props@.len(),
            ps@.len() == i,
            forall|k: int| 0 <= k < i as int ==> ps@[k]@ == obj.props@[k]@,
        decreases n - i,
    {
        ps.push(clone_prop_entry(&obj.props[i]));
        i += 1;
    }
    let r = HeapObject {
        realm: obj.realm,
        prototype: obj.prototype,
        extensible: obj.extensible,
        kind: obj.kind,
        props: ps,
    };
    proof { assert(r@.props =~= obj@.props); }
    r
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Slot {
    Free,
    Live(HeapObject),
}

pub enum SpecSlot {
    Free,
    Live(SpecHeapObject),
}

impl View for Slot {
    type V = SpecSlot;

    open spec fn view(&self) -> SpecSlot {
        match self {
            Slot::Free => SpecSlot::Free,
            Slot::Live(o) => SpecSlot::Live(o@),
        }
    }
}

pub open spec fn spec_slots_view(ss: Seq<Slot>) -> Seq<SpecSlot> {
    Seq::new(ss.len(), |i: int| ss[i]@)
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct RealmIntrinsics {
    pub realm: RealmId,
    pub global_obj: ObjId,
    pub object_proto: ObjId,
    pub function_proto: ObjId,
    pub array_proto: ObjId,
    pub error_proto: ObjId,
    pub ref_error_proto: ObjId,
    pub type_error_proto: ObjId,
    pub syntax_error_proto: ObjId,
    pub range_error_proto: ObjId,
    pub error_ctor: ObjId,
    pub ref_error_ctor: ObjId,
    pub type_error_ctor: ObjId,
    pub syntax_error_ctor: ObjId,
    pub range_error_ctor: ObjId,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Heap {
    pub slots: Vec<Slot>,
    pub realm_heap_quota: usize,
}

pub struct SpecHeap {
    pub slots: Seq<SpecSlot>,
    pub realm_heap_quota: nat,
}

impl View for Heap {
    type V = SpecHeap;

    open spec fn view(&self) -> SpecHeap {
        SpecHeap {
            slots: spec_slots_view(self.slots@),
            realm_heap_quota: self.realm_heap_quota as nat,
        }
    }
}

// ---------------------------------------------------------------------------
// Access Outcomes & Realm Isolation
// ---------------------------------------------------------------------------

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum HeapReadVal {
    Ok(Val),
    InvalidObject,
    CrossRealmAccess,
}

pub enum SpecHeapReadVal {
    Ok(SpecVal),
    InvalidObject,
    CrossRealmAccess,
}

impl View for HeapReadVal {
    type V = SpecHeapReadVal;

    open spec fn view(&self) -> SpecHeapReadVal {
        match self {
            HeapReadVal::Ok(v) => SpecHeapReadVal::Ok(v@),
            HeapReadVal::InvalidObject => SpecHeapReadVal::InvalidObject,
            HeapReadVal::CrossRealmAccess => SpecHeapReadVal::CrossRealmAccess,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum HeapWriteRes {
    Ok(bool),
    InvalidObject,
    CrossRealmAccess,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum AllocRes {
    Ok(ObjId),
    QuotaExceeded,
}

// ---------------------------------------------------------------------------
// Mark-Sweep Collector Spec & Termination Proofs
// ---------------------------------------------------------------------------

pub open spec fn spec_count_false(m: Seq<bool>) -> nat
    decreases m.len(),
{
    if m.len() == 0 {
        0
    } else {
        let rest = spec_count_false(m.drop_last());
        if m.last() { rest } else { rest + 1 }
    }
}

pub proof fn lemma_flip_false_decreases_count(m: Seq<bool>, idx: int)
    requires
        0 <= idx < m.len(),
        !m[idx],
    ensures
        spec_count_false(m.update(idx, true)) + 1 == spec_count_false(m),
    decreases m.len(),
{
    if idx == m.len() - 1 {
        assert(m.update(idx, true).drop_last() =~= m.drop_last());
        assert(m.update(idx, true).last() == true);
        assert(m.last() == false);
    } else {
        assert(m.update(idx, true).drop_last() =~= m.drop_last().update(idx, true));
        assert(m.update(idx, true).last() == m.last());
        lemma_flip_false_decreases_count(m.drop_last(), idx);
    }
}

pub open spec fn spec_gray_slot(marks: Seq<bool>, wl: Seq<usize>, id: usize) -> (Seq<bool>, Seq<usize>) {
    if (id as int) < marks.len() && !marks[id as int] {
        (marks.update(id as int, true), wl.push(id))
    } else {
        (marks, wl)
    }
}

pub proof fn lemma_gray_slot_measure(marks: Seq<bool>, wl: Seq<usize>, id: usize)
    ensures ({
        let (m2, w2) = spec_gray_slot(marks, wl, id);
        m2.len() == marks.len()
        && ((m2 == marks && w2 == wl) || spec_count_false(m2) < spec_count_false(marks))
    }),
{
    if (id as int) < marks.len() && !marks[id as int] {
        lemma_flip_false_decreases_count(marks, id as int);
    }
}

fn gray_slot_exec(marks: &mut Vec<bool>, wl: &mut Vec<usize>, id: usize)
    ensures
        (final(marks)@, final(wl)@) == spec_gray_slot(old(marks)@, old(wl)@, id),
        final(marks)@.len() == old(marks)@.len(),
        (final(marks)@ == old(marks)@ && final(wl)@ == old(wl)@)
            || spec_count_false(final(marks)@) < spec_count_false(old(marks)@),
{
    let ghost om = old(marks)@;
    let ghost owl = old(wl)@;
    if id < marks.len() && !marks[id] {
        marks.set(id, true);
        wl.push(id);
        proof {
            lemma_flip_false_decreases_count(om, id as int);
        }
    }
}

pub open spec fn spec_gray_val(marks: Seq<bool>, wl: Seq<usize>, v: SpecVal) -> (Seq<bool>, Seq<usize>) {
    match v {
        SpecVal::Object(oid) => spec_gray_slot(marks, wl, oid.0),
        _ => (marks, wl),
    }
}

fn gray_val_exec(marks: &mut Vec<bool>, wl: &mut Vec<usize>, v: &Val)
    ensures
        (final(marks)@, final(wl)@) == spec_gray_val(old(marks)@, old(wl)@, v@),
        final(marks)@.len() == old(marks)@.len(),
        (final(marks)@ == old(marks)@ && final(wl)@ == old(wl)@)
            || spec_count_false(final(marks)@) < spec_count_false(old(marks)@),
{
    match v {
        Val::Object(oid) => gray_slot_exec(marks, wl, oid.0),
        _ => {}
    }
}

pub open spec fn spec_gray_props(
    props: Seq<SpecPropEntry>,
    idx: nat,
    marks: Seq<bool>,
    wl: Seq<usize>,
) -> (Seq<bool>, Seq<usize>)
    decreases props.len() - idx,
{
    if idx >= props.len() {
        (marks, wl)
    } else {
        let (m1, w1) = spec_gray_val(marks, wl, props[idx as int].value);
        spec_gray_props(props, idx + 1, m1, w1)
    }
}

pub proof fn lemma_gray_props_measure(
    props: Seq<SpecPropEntry>,
    idx: nat,
    marks: Seq<bool>,
    wl: Seq<usize>,
)
    requires idx <= props.len(),
    ensures ({
        let (m2, w2) = spec_gray_props(props, idx, marks, wl);
        m2.len() == marks.len()
        && ((m2 == marks && w2 == wl) || spec_count_false(m2) < spec_count_false(marks))
    }),
    decreases props.len() - idx,
{
    if idx < props.len() {
        match props[idx as int].value {
            SpecVal::Object(oid) => lemma_gray_slot_measure(marks, wl, oid.0),
            _ => {}
        }
        let (m1, w1) = spec_gray_val(marks, wl, props[idx as int].value);
        lemma_gray_props_measure(props, idx + 1, m1, w1);
    }
}

fn gray_props_exec(props: &Vec<PropEntry>, marks: &mut Vec<bool>, wl: &mut Vec<usize>)
    ensures
        (final(marks)@, final(wl)@) == spec_gray_props(spec_props_view(props@), 0, old(marks)@, old(wl)@),
        final(marks)@.len() == old(marks)@.len(),
        (final(marks)@ == old(marks)@ && final(wl)@ == old(wl)@)
            || spec_count_false(final(marks)@) < spec_count_false(old(marks)@),
{
    let n = props.len();
    let mut i: usize = 0;
    let ghost sprops = spec_props_view(props@);
    let ghost om = old(marks)@;
    let ghost owl = old(wl)@;
    while i < n
        invariant
            i <= n == props@.len(),
            sprops == spec_props_view(props@),
            marks@.len() == om.len(),
            spec_gray_props(sprops, 0, om, owl) == spec_gray_props(sprops, i as nat, marks@, wl@),
            (marks@ == om && wl@ == owl) || spec_count_false(marks@) < spec_count_false(om),
        decreases n - i,
    {
        gray_val_exec(marks, wl, &props[i].value);
        i += 1;
    }
}

pub open spec fn spec_wl_has_int(wl: Seq<usize>, target: int) -> bool {
    exists|w: int| 0 <= w < wl.len() && (#[trigger] wl[w]) as int == target
}

pub open spec fn spec_env_black_closed(
    envs: Seq<SpecEnvSlot>,
    env_marks: Seq<bool>,
    env_wl: Seq<usize>,
) -> bool {
    forall|i: int|
        1 <= i < envs.len() && i < env_marks.len() && (#[trigger] env_marks[i]) && !spec_wl_has_int(env_wl, i) ==>
            match envs[i] {
                SpecEnvSlot::Live(rec) => match rec.outer {
                    Some(p) => p.0 == 0 || ((p.0 as int) < env_marks.len() ==> env_marks[p.0 as int]),
                    None => true,
                },
                SpecEnvSlot::Free => true,
            }
}

pub proof fn lemma_gray_env_slot_preserves_closed(
    envs: Seq<SpecEnvSlot>,
    env_marks: Seq<bool>,
    env_wl: Seq<usize>,
    id: usize,
)
    requires
        env_marks.len() == envs.len(),
        spec_env_black_closed(envs, env_marks, env_wl),
    ensures ({
        let (em2, ew2) = spec_gray_slot(env_marks, env_wl, id);
        em2.len() == envs.len()
        && spec_env_black_closed(envs, em2, ew2)
        && ((id as int) < em2.len() ==> em2[id as int])
        && (forall|k: int| 0 <= k < env_marks.len() && env_marks[k] ==> em2[k])
    }),
{
    lemma_gray_slot_measure(env_marks, env_wl, id);
    if (id as int) < env_marks.len() && !env_marks[id as int] {
        let (em2, ew2) = spec_gray_slot(env_marks, env_wl, id);
        assert(ew2[env_wl.len() as int] == id);
        assert(spec_wl_has_int(ew2, id as int));
        assert forall|i: int|
            1 <= i < envs.len() && i < em2.len() && (#[trigger] em2[i]) && !spec_wl_has_int(ew2, i)
        implies match envs[i] {
            SpecEnvSlot::Live(rec) => match rec.outer {
                Some(p) => p.0 == 0 || ((p.0 as int) < em2.len() ==> em2[p.0 as int]),
                None => true,
            },
            SpecEnvSlot::Free => true,
        } by {
            assert(i != id as int);
            assert(env_marks[i]);
            if spec_wl_has_int(env_wl, i) {
                let widx = choose|widx: int| 0 <= widx < env_wl.len() && (#[trigger] env_wl[widx]) as int == i;
                assert(ew2[widx] == env_wl[widx]);
                assert(spec_wl_has_int(ew2, i));
                assert(false);
            }
            if let SpecEnvSlot::Live(rec) = envs[i] {
                if let Some(p) = rec.outer {
                    if p.0 != 0 && (p.0 as int) < env_marks.len() {
                        assert(env_marks[p.0 as int]);
                        assert(em2[p.0 as int]);
                    }
                }
            }
        }
    }
}

pub open spec fn spec_gray_bindings(
    bs: Seq<crate::env::SpecBinding>,
    idx: nat,
    marks: Seq<bool>,
    wl: Seq<usize>,
) -> (Seq<bool>, Seq<usize>)
    decreases bs.len() - idx,
{
    if idx >= bs.len() {
        (marks, wl)
    } else {
        let (m1, w1) = match bs[idx as int].status {
            SpecBindingStatus::Initialized(v) => spec_gray_val(marks, wl, v),
            SpecBindingStatus::Uninitialized => (marks, wl),
        };
        spec_gray_bindings(bs, idx + 1, m1, w1)
    }
}

pub proof fn lemma_gray_bindings_measure(
    bs: Seq<crate::env::SpecBinding>,
    idx: nat,
    marks: Seq<bool>,
    wl: Seq<usize>,
)
    requires idx <= bs.len(),
    ensures ({
        let (m2, w2) = spec_gray_bindings(bs, idx, marks, wl);
        m2.len() == marks.len()
        && ((m2 == marks && w2 == wl) || spec_count_false(m2) < spec_count_false(marks))
    }),
    decreases bs.len() - idx,
{
    if idx < bs.len() {
        if let SpecBindingStatus::Initialized(SpecVal::Object(oid)) = bs[idx as int].status {
            lemma_gray_slot_measure(marks, wl, oid.0);
        }
        let (m1, w1) = match bs[idx as int].status {
            SpecBindingStatus::Initialized(v) => spec_gray_val(marks, wl, v),
            SpecBindingStatus::Uninitialized => (marks, wl),
        };
        lemma_gray_bindings_measure(bs, idx + 1, m1, w1);
    }
}

fn gray_bindings_exec(bs: &Vec<Binding>, marks: &mut Vec<bool>, wl: &mut Vec<usize>)
    ensures
        (final(marks)@, final(wl)@) == spec_gray_bindings(spec_bindings_view(bs@), 0, old(marks)@, old(wl)@),
        final(marks)@.len() == old(marks)@.len(),
        (final(marks)@ == old(marks)@ && final(wl)@ == old(wl)@)
            || spec_count_false(final(marks)@) < spec_count_false(old(marks)@),
{
    let nb = bs.len();
    let mut j: usize = 0;
    let ghost sbs = spec_bindings_view(bs@);
    let ghost om = old(marks)@;
    let ghost owl = old(wl)@;
    while j < nb
        invariant
            j <= nb == bs@.len(),
            sbs == spec_bindings_view(bs@),
            marks@.len() == om.len(),
            spec_gray_bindings(sbs, 0, om, owl) == spec_gray_bindings(sbs, j as nat, marks@, wl@),
            (marks@ == om && wl@ == owl) || spec_count_false(marks@) < spec_count_false(om),
        decreases nb - j,
    {
        if let BindingStatus::Initialized(v) = &bs[j].status {
            gray_val_exec(marks, wl, v);
        }
        j += 1;
    }
}

pub open spec fn spec_gray_env_children(
    rec: crate::env::SpecEnvRecord,
    obj_marks: Seq<bool>,
    obj_wl: Seq<usize>,
    env_marks: Seq<bool>,
    env_wl: Seq<usize>,
) -> (Seq<bool>, Seq<usize>, Seq<bool>, Seq<usize>) {
    let (em1, ew1) = match rec.outer {
        Some(p) => spec_gray_slot(env_marks, env_wl, p.0),
        None => (env_marks, env_wl),
    };
    let (om1, ow1) = match rec.this_binding {
        Some(v) => spec_gray_val(obj_marks, obj_wl, v),
        None => (obj_marks, obj_wl),
    };
    let (om2, ow2) = spec_gray_bindings(rec.bindings, 0, om1, ow1);
    (om2, ow2, em1, ew1)
}

pub proof fn lemma_gray_env_children_measure(
    rec: crate::env::SpecEnvRecord,
    obj_marks: Seq<bool>,
    obj_wl: Seq<usize>,
    env_marks: Seq<bool>,
    env_wl: Seq<usize>,
)
    ensures ({
        let (om2, ow2, em2, ew2) = spec_gray_env_children(rec, obj_marks, obj_wl, env_marks, env_wl);
        om2.len() == obj_marks.len()
        && em2.len() == env_marks.len()
        && ((om2 == obj_marks && ow2 == obj_wl && em2 == env_marks && ew2 == env_wl)
            || spec_count_false(om2) + spec_count_false(em2) < spec_count_false(obj_marks) + spec_count_false(env_marks))
    }),
{
    if let Some(p) = rec.outer {
        lemma_gray_slot_measure(env_marks, env_wl, p.0);
    }
    if let Some(SpecVal::Object(oid)) = rec.this_binding {
        lemma_gray_slot_measure(obj_marks, obj_wl, oid.0);
    }
    let (om1, ow1) = match rec.this_binding {
        Some(v) => spec_gray_val(obj_marks, obj_wl, v),
        None => (obj_marks, obj_wl),
    };
    lemma_gray_bindings_measure(rec.bindings, 0, om1, ow1);
}

pub open spec fn spec_gray_object_children(
    obj: SpecHeapObject,
    obj_marks: Seq<bool>,
    obj_wl: Seq<usize>,
    env_marks: Seq<bool>,
    env_wl: Seq<usize>,
) -> (Seq<bool>, Seq<usize>, Seq<bool>, Seq<usize>) {
    let (m1, w1) = match obj.prototype {
        Some(p) => spec_gray_slot(obj_marks, obj_wl, p.0),
        None => (obj_marks, obj_wl),
    };
    let (m2, w2, em1, ew1) = match obj.kind {
        ObjectKind::Function { env, prototype_obj, .. } => {
            let (ema, ewa) = spec_gray_slot(env_marks, env_wl, env.0);
            let (ma, wa) = match prototype_obj {
                Some(p) => spec_gray_slot(m1, w1, p.0),
                None => (m1, w1),
            };
            (ma, wa, ema, ewa)
        }
        ObjectKind::BuiltinFunction { prototype_obj: Some(p), .. } => {
            let (ma, wa) = spec_gray_slot(m1, w1, p.0);
            (ma, wa, env_marks, env_wl)
        }
        _ => (m1, w1, env_marks, env_wl),
    };
    let (m3, w3) = spec_gray_props(obj.props, 0, m2, w2);
    (m3, w3, em1, ew1)
}

pub proof fn lemma_gray_object_children_measure(
    obj: SpecHeapObject,
    obj_marks: Seq<bool>,
    obj_wl: Seq<usize>,
    env_marks: Seq<bool>,
    env_wl: Seq<usize>,
)
    ensures ({
        let (mf, wf, emf, ewf) = spec_gray_object_children(obj, obj_marks, obj_wl, env_marks, env_wl);
        mf.len() == obj_marks.len()
        && emf.len() == env_marks.len()
        && ((mf == obj_marks && wf == obj_wl && emf == env_marks && ewf == env_wl)
            || spec_count_false(mf) + spec_count_false(emf) < spec_count_false(obj_marks) + spec_count_false(env_marks))
    }),
{
    if let Some(p) = obj.prototype {
        lemma_gray_slot_measure(obj_marks, obj_wl, p.0);
    }
    let (m1, w1) = match obj.prototype {
        Some(p) => spec_gray_slot(obj_marks, obj_wl, p.0),
        None => (obj_marks, obj_wl),
    };
    match obj.kind {
        ObjectKind::Function { env, prototype_obj, .. } => {
            lemma_gray_slot_measure(env_marks, env_wl, env.0);
            if let Some(p) = prototype_obj {
                lemma_gray_slot_measure(m1, w1, p.0);
            }
        }
        ObjectKind::BuiltinFunction { prototype_obj: Some(p), .. } => lemma_gray_slot_measure(m1, w1, p.0),
        _ => {}
    }
    let (m2, w2, _, _) = match obj.kind {
        ObjectKind::Function { env, prototype_obj, .. } => {
            let (ema, ewa) = spec_gray_slot(env_marks, env_wl, env.0);
            let (ma, wa) = match prototype_obj {
                Some(p) => spec_gray_slot(m1, w1, p.0),
                None => (m1, w1),
            };
            (ma, wa, ema, ewa)
        }
        ObjectKind::BuiltinFunction { prototype_obj: Some(p), .. } => {
            let (ma, wa) = spec_gray_slot(m1, w1, p.0);
            (ma, wa, env_marks, env_wl)
        }
        _ => (m1, w1, env_marks, env_wl),
    };
    lemma_gray_props_measure(obj.props, 0, m2, w2);
}

pub open spec fn spec_trace_joint_worklist(
    slots: Seq<SpecSlot>,
    envs: Seq<SpecEnvSlot>,
    obj_marks: Seq<bool>,
    obj_wl: Seq<usize>,
    env_marks: Seq<bool>,
    env_wl: Seq<usize>,
) -> (Seq<bool>, Seq<bool>)
    decreases spec_count_false(obj_marks) + spec_count_false(env_marks), obj_wl.len() + env_wl.len(),
{
    if (obj_wl.len() == 0 && env_wl.len() == 0)
        || obj_marks.len() != slots.len()
        || env_marks.len() != envs.len()
    {
        (obj_marks, env_marks)
    } else if env_wl.len() > 0 {
        let cur = env_wl.last();
        let ew_pop = env_wl.drop_last();
        if (cur as int) < envs.len() {
            match envs[cur as int] {
                SpecEnvSlot::Live(rec) => {
                    let (om2, ow2, em2, ew2) = spec_gray_env_children(rec, obj_marks, obj_wl, env_marks, ew_pop);
                    proof { lemma_gray_env_children_measure(rec, obj_marks, obj_wl, env_marks, ew_pop); }
                    spec_trace_joint_worklist(slots, envs, om2, ow2, em2, ew2)
                }
                SpecEnvSlot::Free => spec_trace_joint_worklist(slots, envs, obj_marks, obj_wl, env_marks, ew_pop),
            }
        } else {
            spec_trace_joint_worklist(slots, envs, obj_marks, obj_wl, env_marks, ew_pop)
        }
    } else {
        let cur = obj_wl.last();
        let ow_pop = obj_wl.drop_last();
        if (cur as int) < slots.len() {
            match slots[cur as int] {
                SpecSlot::Live(obj) => {
                    let (om2, ow2, em2, ew2) = spec_gray_object_children(obj, obj_marks, ow_pop, env_marks, env_wl);
                    proof { lemma_gray_object_children_measure(obj, obj_marks, ow_pop, env_marks, env_wl); }
                    spec_trace_joint_worklist(slots, envs, om2, ow2, em2, ew2)
                }
                SpecSlot::Free => spec_trace_joint_worklist(slots, envs, obj_marks, ow_pop, env_marks, env_wl),
            }
        } else {
            spec_trace_joint_worklist(slots, envs, obj_marks, ow_pop, env_marks, env_wl)
        }
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(25)]
fn trace_joint_worklist_exec(
    slots: &Vec<Slot>,
    envs: &EnvArena,
    obj_marks: &mut Vec<bool>,
    obj_wl: &mut Vec<usize>,
    env_marks: &mut Vec<bool>,
    env_wl: &mut Vec<usize>,
)
    requires
        old(obj_marks)@.len() == slots@.len(),
        old(env_marks)@.len() == envs@.envs.len(),
        spec_env_black_closed(envs@.envs, old(env_marks)@, old(env_wl)@),
    ensures
        (final(obj_marks)@, final(env_marks)@) == spec_trace_joint_worklist(
            spec_slots_view(slots@),
            envs@.envs,
            old(obj_marks)@,
            old(obj_wl)@,
            old(env_marks)@,
            old(env_wl)@,
        ),
        final(obj_marks)@.len() == slots@.len(),
        final(env_marks)@.len() == envs@.envs.len(),
        final(env_wl)@.len() == 0,
        spec_env_black_closed(envs@.envs, final(env_marks)@, final(env_wl)@),
{
    let ghost sslots = spec_slots_view(slots@);
    let ghost senvs = envs@.envs;
    let ghost init_om = old(obj_marks)@;
    let ghost init_ow = old(obj_wl)@;
    let ghost init_em = old(env_marks)@;
    let ghost init_ew = old(env_wl)@;
    while obj_wl.len() > 0 || env_wl.len() > 0
        invariant
            obj_marks@.len() == slots@.len(),
            env_marks@.len() == senvs.len(),
            senvs == envs@.envs,
            sslots == spec_slots_view(slots@),
            spec_env_black_closed(senvs, env_marks@, env_wl@),
            spec_trace_joint_worklist(sslots, senvs, init_om, init_ow, init_em, init_ew)
                == spec_trace_joint_worklist(sslots, senvs, obj_marks@, obj_wl@, env_marks@, env_wl@),
        decreases spec_count_false(obj_marks@) + spec_count_false(env_marks@), obj_wl@.len() + env_wl@.len(),
    {
        let ghost pre_om = obj_marks@;
        let ghost pre_ow = obj_wl@;
        let ghost pre_em = env_marks@;
        let ghost pre_ew = env_wl@;
        if env_wl.len() > 0 {
            let cur = env_wl.pop().unwrap();
            let ghost ew_pop = env_wl@;
            proof {
                assert(cur == pre_ew.last());
                assert(ew_pop =~= pre_ew.drop_last());
                assert forall|k: int| 0 <= k < senvs.len() && k != cur as int && !#[trigger] spec_wl_has_int(ew_pop, k)
                implies !spec_wl_has_int(pre_ew, k) by {
                    if spec_wl_has_int(pre_ew, k) {
                        let widx = choose|widx: int| 0 <= widx < pre_ew.len() && (#[trigger] pre_ew[widx]) as int == k;
                        if widx < ew_pop.len() {
                            assert(ew_pop[widx] == pre_ew[widx]);
                            assert(spec_wl_has_int(ew_pop, k));
                        } else {
                            assert(pre_ew[widx] == cur);
                        }
                        assert(false);
                    }
                }
            }
            if cur < envs.envs.len() {
                proof { assert(senvs[cur as int] == envs.envs@[cur as int]@); }
                match &envs.envs[cur] {
                    EnvSlot::Live(rec) => {
                        if let Some(p) = rec.outer {
                            gray_slot_exec(env_marks, env_wl, p.0);
                        }
                        if let Some(v) = &rec.this_binding {
                            gray_val_exec(obj_marks, obj_wl, v);
                        }
                        gray_bindings_exec(&rec.bindings, obj_marks, obj_wl);
                        proof {
                            lemma_gray_env_children_measure(rec@, pre_om, pre_ow, pre_em, ew_pop);
                            let em_after = env_marks@;
                            let ew_after = env_wl@;
                            if let Some(p) = rec.outer {
                                lemma_gray_slot_measure(pre_em, ew_pop, p.0);
                                if (p.0 as int) < pre_em.len() {
                                    assert(em_after[p.0 as int]);
                                }
                            }
                            assert forall|i: int|
                                1 <= i < senvs.len() && i < em_after.len() && (#[trigger] em_after[i]) && !spec_wl_has_int(ew_after, i)
                            implies match senvs[i] {
                                SpecEnvSlot::Live(r2) => match r2.outer {
                                    Some(p2) => p2.0 == 0 || ((p2.0 as int) < em_after.len() ==> em_after[p2.0 as int]),
                                    None => true,
                                },
                                SpecEnvSlot::Free => true,
                            } by {
                                if i == cur as int {
                                } else {
                                    if !pre_em[i] {
                                        if let Some(p) = rec.outer {
                                            assert(i == p.0 as int);
                                            assert(ew_after[ew_pop.len() as int] == p.0);
                                            assert(spec_wl_has_int(ew_after, p.0 as int));
                                            assert(false);
                                        } else {
                                            assert(false);
                                        }
                                    }
                                    if spec_wl_has_int(ew_pop, i) {
                                        let widx = choose|widx: int| 0 <= widx < ew_pop.len() && (#[trigger] ew_pop[widx]) as int == i;
                                        assert(ew_after[widx] == ew_pop[widx]);
                                        assert(spec_wl_has_int(ew_after, i));
                                        assert(false);
                                    }
                                    assert(!spec_wl_has_int(pre_ew, i));
                                    if let SpecEnvSlot::Live(r2) = senvs[i] {
                                        if let Some(p2) = r2.outer {
                                            if p2.0 != 0 && (p2.0 as int) < pre_em.len() {
                                                assert(pre_em[p2.0 as int]);
                                                assert(em_after[p2.0 as int]);
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                    EnvSlot::Free => {
                        proof {
                            assert forall|i: int|
                                1 <= i < senvs.len() && i < env_marks@.len() && (#[trigger] env_marks@[i]) && !spec_wl_has_int(ew_pop, i)
                            implies match senvs[i] {
                                SpecEnvSlot::Live(r2) => match r2.outer {
                                    Some(p2) => p2.0 == 0 || ((p2.0 as int) < env_marks@.len() ==> env_marks@[p2.0 as int]),
                                    None => true,
                                },
                                SpecEnvSlot::Free => true,
                            } by {
                                if i != cur as int {
                                    assert(!spec_wl_has_int(pre_ew, i));
                                }
                            }
                        }
                    }
                }
            } else {
                proof {
                    assert forall|i: int|
                        1 <= i < senvs.len() && i < env_marks@.len() && (#[trigger] env_marks@[i]) && !spec_wl_has_int(ew_pop, i)
                    implies match senvs[i] {
                        SpecEnvSlot::Live(r2) => match r2.outer {
                            Some(p2) => p2.0 == 0 || ((p2.0 as int) < env_marks@.len() ==> env_marks@[p2.0 as int]),
                            None => true,
                        },
                        SpecEnvSlot::Free => true,
                    } by {
                        assert(i != cur as int);
                        assert(!spec_wl_has_int(pre_ew, i));
                    }
                }
            }
        } else {
            let cur = obj_wl.pop().unwrap();
            let ghost ow_pop = obj_wl@;
            proof {
                assert(cur == pre_ow.last());
                assert(ow_pop =~= pre_ow.drop_last());
            }
            if cur < slots.len() {
                if let Slot::Live(obj) = &slots[cur] {
                    if let Some(p) = obj.prototype {
                        gray_slot_exec(obj_marks, obj_wl, p.0);
                    }
                    match obj.kind {
                        ObjectKind::Function { env, prototype_obj, .. } => {
                            proof {
                                lemma_gray_env_slot_preserves_closed(senvs, pre_em, pre_ew, env.0);
                            }
                            gray_slot_exec(env_marks, env_wl, env.0);
                            if let Some(p) = prototype_obj {
                                gray_slot_exec(obj_marks, obj_wl, p.0);
                            }
                        }
                        ObjectKind::BuiltinFunction { prototype_obj: Some(p), .. } => {
                            gray_slot_exec(obj_marks, obj_wl, p.0);
                        }
                        _ => {}
                    }
                    gray_props_exec(&obj.props, obj_marks, obj_wl);
                    proof {
                        lemma_gray_object_children_measure(obj@, pre_om, ow_pop, pre_em, pre_ew);
                    }
                }
            }
        }
    }
}

pub open spec fn spec_gray_intrinsics(
    intr: RealmIntrinsics,
    marks: Seq<bool>,
    wl: Seq<usize>,
) -> (Seq<bool>, Seq<usize>) {
    let (m, w) = spec_gray_slot(marks, wl, intr.global_obj.0);
    let (m, w) = spec_gray_slot(m, w, intr.object_proto.0);
    let (m, w) = spec_gray_slot(m, w, intr.function_proto.0);
    let (m, w) = spec_gray_slot(m, w, intr.array_proto.0);
    let (m, w) = spec_gray_slot(m, w, intr.error_proto.0);
    let (m, w) = spec_gray_slot(m, w, intr.ref_error_proto.0);
    let (m, w) = spec_gray_slot(m, w, intr.type_error_proto.0);
    let (m, w) = spec_gray_slot(m, w, intr.syntax_error_proto.0);
    let (m, w) = spec_gray_slot(m, w, intr.range_error_proto.0);
    let (m, w) = spec_gray_slot(m, w, intr.error_ctor.0);
    let (m, w) = spec_gray_slot(m, w, intr.ref_error_ctor.0);
    let (m, w) = spec_gray_slot(m, w, intr.type_error_ctor.0);
    let (m, w) = spec_gray_slot(m, w, intr.syntax_error_ctor.0);
    spec_gray_slot(m, w, intr.range_error_ctor.0)
}

fn gray_intrinsics_exec(intr: &RealmIntrinsics, marks: &mut Vec<bool>, wl: &mut Vec<usize>)
    ensures
        (final(marks)@, final(wl)@) == spec_gray_intrinsics(*intr, old(marks)@, old(wl)@),
        final(marks)@.len() == old(marks)@.len(),
{
    gray_slot_exec(marks, wl, intr.global_obj.0);
    gray_slot_exec(marks, wl, intr.object_proto.0);
    gray_slot_exec(marks, wl, intr.function_proto.0);
    gray_slot_exec(marks, wl, intr.array_proto.0);
    gray_slot_exec(marks, wl, intr.error_proto.0);
    gray_slot_exec(marks, wl, intr.ref_error_proto.0);
    gray_slot_exec(marks, wl, intr.type_error_proto.0);
    gray_slot_exec(marks, wl, intr.syntax_error_proto.0);
    gray_slot_exec(marks, wl, intr.range_error_proto.0);
    gray_slot_exec(marks, wl, intr.error_ctor.0);
    gray_slot_exec(marks, wl, intr.ref_error_ctor.0);
    gray_slot_exec(marks, wl, intr.type_error_ctor.0);
    gray_slot_exec(marks, wl, intr.syntax_error_ctor.0);
    gray_slot_exec(marks, wl, intr.range_error_ctor.0);
}

pub open spec fn spec_gray_env_roots(
    roots: Seq<EnvId>,
    idx: nat,
    env_marks: Seq<bool>,
    env_wl: Seq<usize>,
) -> (Seq<bool>, Seq<usize>)
    decreases roots.len() - idx,
{
    if idx >= roots.len() {
        (env_marks, env_wl)
    } else {
        let (em1, ew1) = spec_gray_slot(env_marks, env_wl, roots[idx as int].0);
        spec_gray_env_roots(roots, idx + 1, em1, ew1)
    }
}

fn gray_env_roots_exec(
    _envs_ghost: Ghost<Seq<SpecEnvSlot>>,
    roots: &Vec<EnvId>,
    env_marks: &mut Vec<bool>,
    env_wl: &mut Vec<usize>,
)
    requires
        old(env_marks)@.len() == _envs_ghost@.len(),
        spec_env_black_closed(_envs_ghost@, old(env_marks)@, old(env_wl)@),
    ensures
        (final(env_marks)@, final(env_wl)@) == spec_gray_env_roots(roots@, 0, old(env_marks)@, old(env_wl)@),
        final(env_marks)@.len() == old(env_marks)@.len(),
        spec_env_black_closed(_envs_ghost@, final(env_marks)@, final(env_wl)@),
{
    let n = roots.len();
    let mut i: usize = 0;
    let ghost om = old(env_marks)@;
    let ghost owl = old(env_wl)@;
    while i < n
        invariant
            i <= n == roots@.len(),
            env_marks@.len() == om.len() == _envs_ghost@.len(),
            spec_env_black_closed(_envs_ghost@, env_marks@, env_wl@),
            spec_gray_env_roots(roots@, 0, om, owl) == spec_gray_env_roots(roots@, i as nat, env_marks@, env_wl@),
        decreases n - i,
    {
        proof {
            lemma_gray_env_slot_preserves_closed(_envs_ghost@, env_marks@, env_wl@, roots[i as int].0);
        }
        gray_slot_exec(env_marks, env_wl, roots[i].0);
        i += 1;
    }
}

pub open spec fn spec_vals_view(vs: Seq<Val>) -> Seq<SpecVal> {
    Seq::new(vs.len(), |i: int| vs[i]@)
}

pub open spec fn spec_gray_extra_roots(
    roots: Seq<SpecVal>,
    idx: nat,
    marks: Seq<bool>,
    wl: Seq<usize>,
) -> (Seq<bool>, Seq<usize>)
    decreases roots.len() - idx,
{
    if idx >= roots.len() {
        (marks, wl)
    } else {
        let (m1, w1) = spec_gray_val(marks, wl, roots[idx as int]);
        spec_gray_extra_roots(roots, idx + 1, m1, w1)
    }
}

fn gray_extra_roots_exec(roots: &Vec<Val>, marks: &mut Vec<bool>, wl: &mut Vec<usize>)
    ensures
        (final(marks)@, final(wl)@) == spec_gray_extra_roots(spec_vals_view(roots@), 0, old(marks)@, old(wl)@),
        final(marks)@.len() == old(marks)@.len(),
{
    let n = roots.len();
    let mut i: usize = 0;
    let ghost sroots = spec_vals_view(roots@);
    let ghost om = old(marks)@;
    let ghost owl = old(wl)@;
    while i < n
        invariant
            i <= n == roots@.len(),
            sroots == spec_vals_view(roots@),
            marks@.len() == om.len(),
            spec_gray_extra_roots(sroots, 0, om, owl) == spec_gray_extra_roots(sroots, i as nat, marks@, wl@),
        decreases n - i,
    {
        gray_val_exec(marks, wl, &roots[i]);
        i += 1;
    }
}

pub open spec fn spec_sweep_slots(slots: Seq<SpecSlot>, marks: Seq<bool>) -> Seq<SpecSlot> {
    Seq::new(slots.len(), |i: int| if i < marks.len() && marks[i] { slots[i] } else { SpecSlot::Free })
}

pub open spec fn spec_mark_sweep_collect(
    heap: SpecHeap,
    envs: SpecEnvArena,
    current_env: EnvId,
    env_roots: Seq<EnvId>,
    intr: RealmIntrinsics,
    extra_roots: Seq<SpecVal>,
) -> (SpecHeap, SpecEnvArena) {
    let init_om = Seq::new(heap.slots.len(), |_i: int| false);
    let init_ow = Seq::<usize>::empty();
    let init_em = Seq::new(envs.envs.len(), |_i: int| false);
    let init_ew = Seq::<usize>::empty();
    let (em1, ew1) = spec_gray_slot(init_em, init_ew, 0);
    let (em2, ew2) = spec_gray_slot(em1, ew1, current_env.0);
    let (em3, ew3) = spec_gray_env_roots(env_roots, 0, em2, ew2);
    let (om1, ow1) = spec_gray_intrinsics(intr, init_om, init_ow);
    let (om2, ow2) = spec_gray_extra_roots(extra_roots, 0, om1, ow1);
    let (final_om, final_em) = spec_trace_joint_worklist(heap.slots, envs.envs, om2, ow2, em3, ew3);
    (
        SpecHeap {
            slots: spec_sweep_slots(heap.slots, final_om),
            realm_heap_quota: heap.realm_heap_quota,
        },
        spec_sweep_envs(envs, final_em),
    )
}

// ---------------------------------------------------------------------------
// Per-Realm Live Counting & Allocation Under Quota
// ---------------------------------------------------------------------------

pub open spec fn spec_count_realm_live_from(slots: Seq<SpecSlot>, realm: RealmId, idx: nat) -> nat
    decreases slots.len() - idx,
{
    if idx >= slots.len() {
        0
    } else {
        let rest = spec_count_realm_live_from(slots, realm, idx + 1);
        match slots[idx as int] {
            SpecSlot::Live(obj) => if obj.realm == realm { rest + 1 } else { rest },
            SpecSlot::Free => rest,
        }
    }
}

pub open spec fn spec_count_realm_live(slots: Seq<SpecSlot>, realm: RealmId) -> nat {
    spec_count_realm_live_from(slots, realm, 0)
}

pub proof fn lemma_count_realm_live_le_len(slots: Seq<SpecSlot>, realm: RealmId, idx: nat)
    requires idx <= slots.len(),
    ensures spec_count_realm_live_from(slots, realm, idx) <= slots.len() - idx,
    decreases slots.len() - idx,
{
    if idx < slots.len() {
        lemma_count_realm_live_le_len(slots, realm, idx + 1);
    }
}

pub open spec fn spec_find_free_slot_from(slots: Seq<SpecSlot>, idx: nat) -> Option<nat>
    decreases slots.len() - idx,
{
    if idx >= slots.len() {
        None
    } else if slots[idx as int] is Free {
        Some(idx)
    } else {
        spec_find_free_slot_from(slots, idx + 1)
    }
}

pub open spec fn spec_insert_object(heap: SpecHeap, obj: SpecHeapObject) -> (SpecHeap, ObjId) {
    match spec_find_free_slot_from(heap.slots, 0) {
        Some(idx) => (
            SpecHeap {
                slots: heap.slots.update(idx as int, SpecSlot::Live(obj)),
                realm_heap_quota: heap.realm_heap_quota,
            },
            ObjId(idx as usize),
        ),
        None => {
            let id = ObjId(heap.slots.len() as usize);
            (
                SpecHeap {
                    slots: heap.slots.push(SpecSlot::Live(obj)),
                    realm_heap_quota: heap.realm_heap_quota,
                },
                id,
            )
        }
    }
}

pub open spec fn spec_alloc_with_gc(
    heap: SpecHeap,
    envs: SpecEnvArena,
    current_env: EnvId,
    env_roots: Seq<EnvId>,
    intr: RealmIntrinsics,
    extra_roots: Seq<SpecVal>,
    obj: SpecHeapObject,
) -> (SpecHeap, SpecEnvArena, AllocRes) {
    let live1 = spec_count_realm_live(heap.slots, obj.realm);
    if live1 < heap.realm_heap_quota {
        let (h2, oid) = spec_insert_object(heap, obj);
        (h2, envs, AllocRes::Ok(oid))
    } else {
        let (h_gc, e_gc) = spec_mark_sweep_collect(heap, envs, current_env, env_roots, intr, extra_roots);
        let live2 = spec_count_realm_live(h_gc.slots, obj.realm);
        if live2 >= h_gc.realm_heap_quota {
            (h_gc, e_gc, AllocRes::QuotaExceeded)
        } else {
            let (h2, oid) = spec_insert_object(h_gc, obj);
            (h2, e_gc, AllocRes::Ok(oid))
        }
    }
}

// ---------------------------------------------------------------------------
// Object Property Lookup, Mutation, Array Length, & Prototype Chain Specs
// ---------------------------------------------------------------------------

pub open spec fn spec_find_prop_from(props: Seq<SpecPropEntry>, key: Seq<u16>, idx: nat) -> Option<nat>
    decreases props.len() - idx,
{
    if idx >= props.len() {
        None
    } else if props[idx as int].key == key {
        Some(idx)
    } else {
        spec_find_prop_from(props, key, idx + 1)
    }
}

pub open spec fn spec_find_prop(props: Seq<SpecPropEntry>, key: Seq<u16>) -> Option<nat> {
    spec_find_prop_from(props, key, 0)
}

pub open spec fn spec_is_length_key(k: Seq<u16>) -> bool {
    k.len() == 6
    && k[0] == 0x6Cu16
    && k[1] == 0x65u16
    && k[2] == 0x6Eu16
    && k[3] == 0x67u16
    && k[4] == 0x74u16
    && k[5] == 0x68u16
}

pub fn is_length_key(k: &JsStr) -> (r: bool)
    ensures r == spec_is_length_key(k@),
{
    k.0.len() == 6
    && k.0[0] == 0x6C
    && k.0[1] == 0x65
    && k.0[2] == 0x6E
    && k.0[3] == 0x67
    && k.0[4] == 0x74
    && k.0[5] == 0x68
}

/// Canonical ECMA-262 array index key (`"0"` or `[1-9][0-9]*` `< 2^32 - 1`).
pub open spec fn spec_parse_array_index(k: Seq<u16>) -> Option<usize> {
    if k.len() == 0 || k.len() > 10 {
        None
    } else if k.len() == 1 && k[0] == 0x30u16 {
        Some(0usize)
    } else if k[0] < 0x31u16 || k[0] > 0x39u16 {
        None
    } else {
        spec_parse_array_idx_loop(k, 0, 0u64)
    }
}

pub open spec fn spec_parse_array_idx_loop(k: Seq<u16>, idx: nat, acc: u64) -> Option<usize>
    decreases k.len() - idx,
{
    if idx >= k.len() {
        if acc < 0xFFFF_FFFFu64 { Some(acc as usize) } else { None }
    } else {
        let c = k[idx as int];
        if 0x30u16 <= c && c <= 0x39u16 && acc <= 0xFFFF_FFFFu64 {
            spec_parse_array_idx_loop(k, idx + 1, (acc * 10u64 + ((c - 0x30u16) as u64)) as u64)
        } else {
            None
        }
    }
}

pub fn parse_array_index(k: &JsStr) -> (r: Option<usize>)
    ensures r == spec_parse_array_index(k@),
{
    let n = k.0.len();
    if n == 0 || n > 10 {
        return None;
    }
    if n == 1 && k.0[0] == 0x30 {
        return Some(0);
    }
    if k.0[0] < 0x31 || k.0[0] > 0x39 {
        return None;
    }
    let mut i: usize = 0;
    let mut acc: u64 = 0;
    while i < n
        invariant
            i <= n == k@.len(),
            1 <= n <= 10,
            !(n == 1 && k@[0] == 0x30u16),
            0x31u16 <= k@[0] <= 0x39u16,
            acc <= 0xFFFF_FFFFu64 * 10u64 + 9u64,
            spec_parse_array_idx_loop(k@, 0, 0u64) == spec_parse_array_idx_loop(k@, i as nat, acc),
        decreases n - i,
    {
        let c = k.0[i];
        if 0x30 <= c && c <= 0x39 && acc <= 0xFFFF_FFFFu64 {
            acc = acc * 10u64 + ((c - 0x30) as u64);
            i += 1;
        } else {
            proof { assert(spec_parse_array_idx_loop(k@, i as nat, acc) is None); }
            return None;
        }
    }
    if acc < 0xFFFF_FFFFu64 { Some(acc as usize) } else { None }
}

/// Bounded prototype-chain `[[Get]]` enforcing `obj.realm == caller_realm` at every step.
pub open spec fn spec_heap_get_steps(
    heap: SpecHeap,
    caller_realm: RealmId,
    oid: ObjId,
    key: Seq<u16>,
    steps: nat,
) -> SpecHeapReadVal
    decreases steps,
{
    if steps == 0 {
        SpecHeapReadVal::Ok(SpecVal::Undefined)
    } else if (oid.0 as int) >= heap.slots.len() {
        SpecHeapReadVal::InvalidObject
    } else {
        match heap.slots[oid.0 as int] {
            SpecSlot::Free => SpecHeapReadVal::InvalidObject,
            SpecSlot::Live(obj) => {
                if obj.realm != caller_realm {
                    SpecHeapReadVal::CrossRealmAccess
                } else {
                    match obj.kind {
                        ObjectKind::Array { length } => {
                            if spec_is_length_key(key) {
                                SpecHeapReadVal::Ok(SpecVal::Number(spec_num_from_usize(length)))
                            } else {
                                match spec_find_prop(obj.props, key) {
                                    Some(idx) => SpecHeapReadVal::Ok(obj.props[idx as int].value),
                                    None => match obj.prototype {
                                        Some(p) => spec_heap_get_steps(heap, caller_realm, p, key, (steps - 1) as nat),
                                        None => SpecHeapReadVal::Ok(SpecVal::Undefined),
                                    },
                                }
                            }
                        }
                        _ => {
                            match spec_find_prop(obj.props, key) {
                                Some(idx) => SpecHeapReadVal::Ok(obj.props[idx as int].value),
                                None => match obj.prototype {
                                    Some(p) => spec_heap_get_steps(heap, caller_realm, p, key, (steps - 1) as nat),
                                    None => SpecHeapReadVal::Ok(SpecVal::Undefined),
                                },
                            }
                        }
                    }
                }
            }
        }
    }
}

pub open spec fn spec_heap_get_prop(
    heap: SpecHeap,
    caller_realm: RealmId,
    oid: ObjId,
    key: Seq<u16>,
) -> SpecHeapReadVal {
    spec_heap_get_steps(heap, caller_realm, oid, key, if heap.slots.len() == 0 { 1 } else { heap.slots.len() })
}

pub open spec fn spec_filter_props_below_len(
    props: Seq<SpecPropEntry>,
    idx: nat,
    new_len: usize,
    acc: Seq<SpecPropEntry>,
) -> Seq<SpecPropEntry>
    decreases props.len() - idx,
{
    if idx >= props.len() {
        acc
    } else {
        let entry = props[idx as int];
        let keep = match spec_parse_array_index(entry.key) {
            Some(ai) => ai < new_len || !entry.configurable,
            None => true,
        };
        let next_acc = if keep { acc.push(entry) } else { acc };
        spec_filter_props_below_len(props, idx + 1, new_len, next_acc)
    }
}

/// Own property `[[Set]]` enforcing `obj.realm == caller_realm`, `writable`/`extensible`,
/// and Array exotic `length` synchronization (§10.4.2).
pub open spec fn spec_heap_set_prop(
    heap: SpecHeap,
    caller_realm: RealmId,
    oid: ObjId,
    key: Seq<u16>,
    val: SpecVal,
) -> (SpecHeap, HeapWriteRes) {
    if (oid.0 as int) >= heap.slots.len() {
        (heap, HeapWriteRes::InvalidObject)
    } else {
        match heap.slots[oid.0 as int] {
            SpecSlot::Free => (heap, HeapWriteRes::InvalidObject),
            SpecSlot::Live(obj) => {
                if obj.realm != caller_realm {
                    (heap, HeapWriteRes::CrossRealmAccess)
                } else {
                    match obj.kind {
                        ObjectKind::Array { length } => {
                            if spec_is_length_key(key) {
                                let ulen = spec_to_uint32(spec_prim_to_number(val)) as usize;
                                let new_props = spec_filter_props_below_len(obj.props, 0, ulen, seq![]);
                                let obj2 = SpecHeapObject {
                                    kind: ObjectKind::Array { length: ulen },
                                    props: new_props,
                                    ..obj
                                };
                                (
                                    SpecHeap { slots: heap.slots.update(oid.0 as int, SpecSlot::Live(obj2)), ..heap },
                                    HeapWriteRes::Ok(true),
                                )
                            } else {
                                spec_set_ordinary_or_array_elem(heap, oid, obj, key, val)
                            }
                        }
                        _ => spec_set_ordinary_or_array_elem(heap, oid, obj, key, val),
                    }
                }
            }
        }
    }
}

pub open spec fn spec_set_ordinary_or_array_elem(
    heap: SpecHeap,
    oid: ObjId,
    obj: SpecHeapObject,
    key: Seq<u16>,
    val: SpecVal,
) -> (SpecHeap, HeapWriteRes) {
    match spec_find_prop(obj.props, key) {
        Some(idx) => {
            let entry = obj.props[idx as int];
            if !entry.writable {
                (heap, HeapWriteRes::Ok(false))
            } else {
                let entry2 = SpecPropEntry { value: val, ..entry };
                let next_kind = match obj.kind {
                    ObjectKind::Array { length } => match spec_parse_array_index(key) {
                        Some(ai) => if ai >= length && ai < usize::MAX {
                            ObjectKind::Array { length: (ai + 1) as usize }
                        } else {
                            obj.kind
                        },
                        None => obj.kind,
                    },
                    _ => obj.kind,
                };
                let obj2 = SpecHeapObject {
                    kind: next_kind,
                    props: obj.props.update(idx as int, entry2),
                    ..obj
                };
                (
                    SpecHeap { slots: heap.slots.update(oid.0 as int, SpecSlot::Live(obj2)), ..heap },
                    HeapWriteRes::Ok(true),
                )
            }
        }
        None => {
            if !obj.extensible {
                (heap, HeapWriteRes::Ok(false))
            } else {
                let new_entry = SpecPropEntry {
                    key,
                    value: val,
                    writable: true,
                    enumerable: true,
                    configurable: true,
                };
                let next_kind = match obj.kind {
                    ObjectKind::Array { length } => match spec_parse_array_index(key) {
                        Some(ai) => if ai >= length && ai < usize::MAX {
                            ObjectKind::Array { length: (ai + 1) as usize }
                        } else {
                            obj.kind
                        },
                        None => obj.kind,
                    },
                    _ => obj.kind,
                };
                let obj2 = SpecHeapObject {
                    kind: next_kind,
                    props: obj.props.push(new_entry),
                    ..obj
                };
                (
                    SpecHeap { slots: heap.slots.update(oid.0 as int, SpecSlot::Live(obj2)), ..heap },
                    HeapWriteRes::Ok(true),
                )
            }
        }
    }
}

pub open spec fn spec_remove_prop_at(props: Seq<SpecPropEntry>, rm_idx: nat) -> Seq<SpecPropEntry> {
    props.subrange(0, rm_idx as int) + props.subrange((rm_idx + 1) as int, props.len() as int)
}

pub open spec fn spec_heap_delete_prop(
    heap: SpecHeap,
    caller_realm: RealmId,
    oid: ObjId,
    key: Seq<u16>,
) -> (SpecHeap, HeapWriteRes) {
    if (oid.0 as int) >= heap.slots.len() {
        (heap, HeapWriteRes::InvalidObject)
    } else {
        match heap.slots[oid.0 as int] {
            SpecSlot::Free => (heap, HeapWriteRes::InvalidObject),
            SpecSlot::Live(obj) => {
                if obj.realm != caller_realm {
                    (heap, HeapWriteRes::CrossRealmAccess)
                } else if (obj.kind is Array) && spec_is_length_key(key) {
                    // Array `length` is non-configurable (§10.4.2)
                    (heap, HeapWriteRes::Ok(false))
                } else {
                    match spec_find_prop(obj.props, key) {
                        None => (heap, HeapWriteRes::Ok(true)),
                        Some(idx) => {
                            if !obj.props[idx as int].configurable {
                                (heap, HeapWriteRes::Ok(false))
                            } else {
                                let obj2 = SpecHeapObject {
                                    props: spec_remove_prop_at(obj.props, idx),
                                    ..obj
                                };
                                (
                                    SpecHeap { slots: heap.slots.update(oid.0 as int, SpecSlot::Live(obj2)), ..heap },
                                    HeapWriteRes::Ok(true),
                                )
                            }
                        }
                    }
                }
            }
        }
    }
}

pub open spec fn spec_heap_has_steps(
    heap: SpecHeap,
    caller_realm: RealmId,
    oid: ObjId,
    key: Seq<u16>,
    steps: nat,
) -> HeapWriteRes
    decreases steps,
{
    if steps == 0 {
        HeapWriteRes::Ok(false)
    } else if (oid.0 as int) >= heap.slots.len() {
        HeapWriteRes::InvalidObject
    } else {
        match heap.slots[oid.0 as int] {
            SpecSlot::Free => HeapWriteRes::InvalidObject,
            SpecSlot::Live(obj) => {
                if obj.realm != caller_realm {
                    HeapWriteRes::CrossRealmAccess
                } else if (obj.kind is Array) && spec_is_length_key(key) {
                    HeapWriteRes::Ok(true)
                } else if spec_find_prop(obj.props, key) is Some {
                    HeapWriteRes::Ok(true)
                } else {
                    match obj.prototype {
                        Some(p) => spec_heap_has_steps(heap, caller_realm, p, key, (steps - 1) as nat),
                        None => HeapWriteRes::Ok(false),
                    }
                }
            }
        }
    }
}

pub open spec fn spec_define_global_var_prop(
    heap: SpecHeap,
    caller_realm: RealmId,
    oid: ObjId,
    key: Seq<u16>,
) -> SpecHeap {
    if (oid.0 as int) >= heap.slots.len() {
        heap
    } else {
        match heap.slots[oid.0 as int] {
            SpecSlot::Free => heap,
            SpecSlot::Live(obj) => {
                if obj.realm != caller_realm || !obj.extensible || (spec_find_prop(obj.props, key) is Some) {
                    heap
                } else {
                    let entry = SpecPropEntry {
                        key,
                        value: SpecVal::Undefined,
                        writable: true,
                        enumerable: true,
                        configurable: false,
                    };
                    let obj2 = SpecHeapObject { props: obj.props.push(entry), ..obj };
                    SpecHeap { slots: heap.slots.update(oid.0 as int, SpecSlot::Live(obj2)), ..heap }
                }
            }
        }
    }
}

pub open spec fn spec_heap_has_own_prop(
    heap: SpecHeap,
    caller_realm: RealmId,
    oid: ObjId,
    key: Seq<u16>,
) -> HeapWriteRes {
    if (oid.0 as int) >= heap.slots.len() {
        HeapWriteRes::InvalidObject
    } else {
        match heap.slots[oid.0 as int] {
            SpecSlot::Free => HeapWriteRes::InvalidObject,
            SpecSlot::Live(obj) => {
                if obj.realm != caller_realm {
                    HeapWriteRes::CrossRealmAccess
                } else if (obj.kind is Array) && spec_is_length_key(key) {
                    HeapWriteRes::Ok(true)
                } else {
                    HeapWriteRes::Ok(spec_find_prop(obj.props, key) is Some)
                }
            }
        }
    }
}

pub open spec fn spec_heap_has_prop(
    heap: SpecHeap,
    caller_realm: RealmId,
    oid: ObjId,
    key: Seq<u16>,
) -> HeapWriteRes {
    spec_heap_has_steps(heap, caller_realm, oid, key, if heap.slots.len() == 0 { 1 } else { heap.slots.len() })
}

pub open spec fn spec_is_instance_of_steps(
    heap: SpecHeap,
    caller_realm: RealmId,
    cur: ObjId,
    target_proto: ObjId,
    steps: nat,
) -> HeapWriteRes
    decreases steps,
{
    if steps == 0 {
        HeapWriteRes::Ok(false)
    } else if (cur.0 as int) >= heap.slots.len() {
        HeapWriteRes::InvalidObject
    } else {
        match heap.slots[cur.0 as int] {
            SpecSlot::Free => HeapWriteRes::InvalidObject,
            SpecSlot::Live(obj) => {
                if obj.realm != caller_realm {
                    HeapWriteRes::CrossRealmAccess
                } else {
                    match obj.prototype {
                        None => HeapWriteRes::Ok(false),
                        Some(p) => if p == target_proto {
                            HeapWriteRes::Ok(true)
                        } else {
                            spec_is_instance_of_steps(heap, caller_realm, p, target_proto, (steps - 1) as nat)
                        },
                    }
                }
            }
        }
    }
}

/// **Cross-Realm Isolation Theorem**:
/// Any property read, write, or delete issued by `caller_realm` against an object owned by
/// `other_realm != caller_realm` unconditionally rejects with `CrossRealmAccess`, and no
/// `set_prop` or `delete_prop` ever modifies any live object belonging to another realm.
pub proof fn theorem_cross_realm_isolation(
    heap: SpecHeap,
    caller_realm: RealmId,
    oid: ObjId,
    key: Seq<u16>,
    val: SpecVal,
)
    ensures
        ((oid.0 as int) < heap.slots.len()
            && match heap.slots[oid.0 as int] {
                SpecSlot::Live(o) => o.realm != caller_realm,
                SpecSlot::Free => false,
            }) ==> (
                spec_heap_get_prop(heap, caller_realm, oid, key) == SpecHeapReadVal::CrossRealmAccess
                && spec_heap_set_prop(heap, caller_realm, oid, key, val) == (heap, HeapWriteRes::CrossRealmAccess)
                && spec_heap_delete_prop(heap, caller_realm, oid, key) == (heap, HeapWriteRes::CrossRealmAccess)
            ),
        forall|k: int| 0 <= k < heap.slots.len() ==> (
            match #[trigger] heap.slots[k] {
                SpecSlot::Live(o) => o.realm != caller_realm ==> (
                    spec_heap_set_prop(heap, caller_realm, oid, key, val).0.slots[k] == heap.slots[k]
                    && spec_heap_delete_prop(heap, caller_realm, oid, key).0.slots[k] == heap.slots[k]
                ),
                SpecSlot::Free => true,
            }
        ),
{
}

// ---------------------------------------------------------------------------
// Executable `Heap` Implementation Proved Equal to Spec
// ---------------------------------------------------------------------------

fn find_prop_exec(props: &Vec<PropEntry>, key: &JsStr) -> (r: Option<usize>)
    ensures
        match r {
            Some(idx) => spec_find_prop(spec_props_view(props@), key@) == Some(idx as nat)
                && idx < props@.len()
                && props@[idx as int].key@ == key@,
            None => spec_find_prop(spec_props_view(props@), key@) is None,
        },
{
    let n = props.len();
    let mut i: usize = 0;
    let ghost sprops = spec_props_view(props@);
    while i < n
        invariant
            i <= n == props@.len(),
            sprops == spec_props_view(props@),
            spec_find_prop_from(sprops, key@, 0) == spec_find_prop_from(sprops, key@, i as nat),
        decreases n - i,
    {
        if js_str_eq(&props[i].key, key) {
            return Some(i);
        }
        i += 1;
    }
    None
}

impl Heap {
    pub fn new(realm_heap_quota: usize) -> (h: Self)
        ensures
            h@.slots.len() == 0,
            h@.realm_heap_quota == realm_heap_quota as nat,
    {
        let h = Heap {
            slots: Vec::new(),
            realm_heap_quota,
        };
        proof { assert(h@.slots =~= Seq::<SpecSlot>::empty()); }
        h
    }

    /// Raw bootstrap allocation used while constructing initial realm intrinsics (before scripts run).
    pub fn alloc_bootstrap(&mut self, obj: HeapObject) -> (id: ObjId)
        ensures
            id.0 == old(self)@.slots.len(),
            final(self)@.slots =~= old(self)@.slots.push(SpecSlot::Live(obj@)),
            final(self)@.realm_heap_quota == old(self)@.realm_heap_quota,
    {
        let idx = self.slots.len();
        self.slots.push(Slot::Live(obj));
        ObjId(idx)
    }

    pub fn count_realm_live(&self, realm: RealmId) -> (cnt: usize)
        ensures cnt as nat == spec_count_realm_live(self@.slots, realm),
    {
        let n = self.slots.len();
        let mut i: usize = n;
        let mut cnt: usize = 0;
        let ghost sslots = self@.slots;
        while i > 0
            invariant
                i <= n == sslots.len(),
                sslots == self@.slots,
                cnt as nat == spec_count_realm_live_from(sslots, realm, i as nat),
                cnt <= n - i,
            decreases i,
        {
            i -= 1;
            proof { assert(sslots[i as int] == self.slots@[i as int]@); }
            if let Slot::Live(obj) = &self.slots[i] {
                if obj.realm.0 == realm.0 {
                    cnt += 1;
                }
            }
        }
        cnt
    }

    pub fn mark_sweep_collect(
        &mut self,
        envs: &mut EnvArena,
        current_env: EnvId,
        env_roots: &Vec<EnvId>,
        intr: &RealmIntrinsics,
        extra_roots: &Vec<Val>,
    )
        ensures
            (final(self)@, final(envs)@) == spec_mark_sweep_collect(
                old(self)@,
                old(envs)@,
                current_env,
                env_roots@,
                *intr,
                spec_vals_view(extra_roots@),
            ),
            env_wf(old(envs)@) ==> env_wf(final(envs)@),
    {
        let n = self.slots.len();
        let mut obj_marks: Vec<bool> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                k <= n == self.slots@.len(),
                obj_marks@.len() == k,
                forall|j: int| 0 <= j < k as int ==> obj_marks@[j] == false,
            decreases n - k,
        {
            obj_marks.push(false);
            k += 1;
        }
        let ne = envs.envs.len();
        let mut env_marks: Vec<bool> = Vec::new();
        let mut ek: usize = 0;
        while ek < ne
            invariant
                ek <= ne == envs.envs@.len(),
                env_marks@.len() == ek,
                forall|j: int| 0 <= j < ek as int ==> env_marks@[j] == false,
            decreases ne - ek,
        {
            env_marks.push(false);
            ek += 1;
        }
        let mut obj_wl: Vec<usize> = Vec::new();
        let mut env_wl: Vec<usize> = Vec::new();
        let ghost senvs = envs@.envs;
        proof {
            assert(obj_marks@ =~= Seq::new(self@.slots.len(), |_i: int| false));
            assert(obj_wl@ =~= Seq::<usize>::empty());
            assert(env_marks@ =~= Seq::new(senvs.len(), |_i: int| false));
            assert(env_wl@ =~= Seq::<usize>::empty());
            assert(spec_env_black_closed(senvs, env_marks@, env_wl@));
            lemma_gray_env_slot_preserves_closed(senvs, env_marks@, env_wl@, 0);
        }
        gray_slot_exec(&mut env_marks, &mut env_wl, 0);
        proof {
            lemma_gray_env_slot_preserves_closed(senvs, env_marks@, env_wl@, current_env.0);
        }
        gray_slot_exec(&mut env_marks, &mut env_wl, current_env.0);
        gray_env_roots_exec(Ghost(senvs), env_roots, &mut env_marks, &mut env_wl);

        gray_intrinsics_exec(intr, &mut obj_marks, &mut obj_wl);
        gray_extra_roots_exec(extra_roots, &mut obj_marks, &mut obj_wl);
        trace_joint_worklist_exec(&self.slots, envs, &mut obj_marks, &mut obj_wl, &mut env_marks, &mut env_wl);

        let ghost pre_sweep = self@.slots;
        let mut s: usize = 0;
        while s < n
            invariant
                s <= n == self.slots@.len(),
                n == obj_marks@.len() == pre_sweep.len(),
                self.realm_heap_quota == old(self).realm_heap_quota,
                forall|j: int| 0 <= j < s as int ==> #[trigger] self@.slots[j] == (if obj_marks@[j] { pre_sweep[j] } else { SpecSlot::Free }),
                forall|j: int| s as int <= j < n as int ==> #[trigger] self@.slots[j] == pre_sweep[j],
            decreases n - s,
        {
            let ghost before_s = self@;
            if !obj_marks[s] {
                self.slots.set(s, Slot::Free);
            }
            proof {
                assert forall|j: int| 0 <= j <= s as int implies #[trigger] self@.slots[j] == (if obj_marks@[j] { pre_sweep[j] } else { SpecSlot::Free }) by {
                    if j < s as int {
                        assert(self@.slots[j] == before_s.slots[j]);
                    } else if obj_marks@[s as int] {
                        assert(self@.slots[s as int] == before_s.slots[s as int]);
                    } else {
                        assert(self@.slots[s as int] == SpecSlot::Free);
                    }
                }
                assert forall|j: int| (s + 1) as int <= j < n as int implies #[trigger] self@.slots[j] == pre_sweep[j] by {
                    assert(self@.slots[j] == before_s.slots[j]);
                }
            }
            s += 1;
        }
        proof {
            assert(self@.slots =~= spec_sweep_slots(pre_sweep, obj_marks@));
            assert forall|i: int| 1 <= i < senvs.len() && env_marks@[i] implies match #[trigger] senvs[i] {
                SpecEnvSlot::Live(rec) => match rec.outer {
                    Some(p) => (p.0 as int) == 0 || ((p.0 as int) < env_marks@.len() ==> env_marks@[p.0 as int]),
                    None => true,
                },
                SpecEnvSlot::Free => true,
            } by {
                assert(!spec_wl_has_int(env_wl@, i));
                assert(env_marks@[i]);
            }
        }
        envs.sweep_unmarked(&env_marks);
    }

    fn find_free_slot(&self) -> (r: Option<usize>)
        ensures
            match r {
                Some(idx) => spec_find_free_slot_from(self@.slots, 0) == Some(idx as nat)
                    && (idx as int) < self@.slots.len(),
                None => spec_find_free_slot_from(self@.slots, 0) is None,
            },
    {
        let n = self.slots.len();
        let mut i: usize = 0;
        let ghost sslots = self@.slots;
        while i < n
            invariant
                i <= n == sslots.len(),
                sslots == self@.slots,
                spec_find_free_slot_from(sslots, 0) == spec_find_free_slot_from(sslots, i as nat),
            decreases n - i,
        {
            if matches!(self.slots[i], Slot::Free) {
                return Some(i);
            }
            i += 1;
        }
        None
    }

    fn insert_object(&mut self, obj: HeapObject) -> (id: ObjId)
        ensures (final(self)@, id) == spec_insert_object(old(self)@, obj@),
    {
        let ghost old_h = old(self)@;
        let ghost sobj = obj@;
        match self.find_free_slot() {
            Some(idx) => {
                self.slots.set(idx, Slot::Live(obj));
                proof {
                    assert(self@.slots =~= old_h.slots.update(idx as int, SpecSlot::Live(sobj)));
                }
                ObjId(idx)
            }
            None => {
                let idx = self.slots.len();
                self.slots.push(Slot::Live(obj));
                proof {
                    assert(self@.slots =~= old_h.slots.push(SpecSlot::Live(sobj)));
                }
                ObjId(idx)
            }
        }
    }

    /// Allocate `obj` under `self.realm_heap_quota`, running Mark-Sweep GC first if live count
    /// reaches quota, and returning `AllocRes::QuotaExceeded` if live objects still reach quota.
    pub fn alloc_with_gc(
        &mut self,
        envs: &mut EnvArena,
        current_env: EnvId,
        env_roots: &Vec<EnvId>,
        intr: &RealmIntrinsics,
        extra_roots: &Vec<Val>,
        obj: HeapObject,
    ) -> (res: AllocRes)
        ensures
            (final(self)@, final(envs)@, res) == spec_alloc_with_gc(
                old(self)@,
                old(envs)@,
                current_env,
                env_roots@,
                *intr,
                spec_vals_view(extra_roots@),
                obj@,
            ),
            env_wf(old(envs)@) ==> env_wf(final(envs)@),
    {
        let live1 = self.count_realm_live(obj.realm);
        if live1 < self.realm_heap_quota {
            let oid = self.insert_object(obj);
            AllocRes::Ok(oid)
        } else {
            self.mark_sweep_collect(envs, current_env, env_roots, intr, extra_roots);
            let live2 = self.count_realm_live(obj.realm);
            if live2 >= self.realm_heap_quota {
                AllocRes::QuotaExceeded
            } else {
                let oid = self.insert_object(obj);
                AllocRes::Ok(oid)
            }
        }
    }

    fn get_steps(&self, caller_realm: RealmId, oid: ObjId, key: &JsStr, steps: usize) -> (r: HeapReadVal)
        ensures r@ == spec_heap_get_steps(self@, caller_realm, oid, key@, steps as nat),
    {
        let mut cur = oid;
        let mut rem = steps;
        let ghost sh = self@;
        while rem > 0
            invariant
                rem <= steps,
                sh == self@,
                spec_heap_get_steps(sh, caller_realm, oid, key@, steps as nat)
                    == spec_heap_get_steps(sh, caller_realm, cur, key@, rem as nat),
            decreases rem,
        {
            if cur.0 >= self.slots.len() {
                return HeapReadVal::InvalidObject;
            }
            proof { assert(sh.slots[cur.0 as int] == self.slots@[cur.0 as int]@); }
            match &self.slots[cur.0] {
                Slot::Free => return HeapReadVal::InvalidObject,
                Slot::Live(obj) => {
                    if obj.realm.0 != caller_realm.0 {
                        return HeapReadVal::CrossRealmAccess;
                    }
                    if let ObjectKind::Array { length } = obj.kind {
                        if is_length_key(key) {
                            return HeapReadVal::Ok(Val::Number(num_from_usize(length)));
                        }
                    }
                    match find_prop_exec(&obj.props, key) {
                        Some(idx) => return HeapReadVal::Ok(clone_val(&obj.props[idx].value)),
                        None => match obj.prototype {
                            Some(p) => {
                                cur = p;
                                rem -= 1;
                            }
                            None => return HeapReadVal::Ok(Val::Undefined),
                        },
                    }
                }
            }
        }
        HeapReadVal::Ok(Val::Undefined)
    }

    pub fn get_prop(&self, caller_realm: RealmId, oid: ObjId, key: &JsStr) -> (r: HeapReadVal)
        ensures r@ == spec_heap_get_prop(self@, caller_realm, oid, key@),
    {
        let steps = if self.slots.len() == 0 { 1 } else { self.slots.len() };
        self.get_steps(caller_realm, oid, key, steps)
    }

    pub fn set_prop(
        &mut self,
        caller_realm: RealmId,
        oid: ObjId,
        key: JsStr,
        val: Val,
    ) -> (res: HeapWriteRes)
        ensures (final(self)@, res) == spec_heap_set_prop(old(self)@, caller_realm, oid, key@, val@),
    {
        if oid.0 >= self.slots.len() {
            return HeapWriteRes::InvalidObject;
        }
        proof { assert(self@.slots[oid.0 as int] == self.slots@[oid.0 as int]@); }
        match &self.slots[oid.0] {
            Slot::Free => return HeapWriteRes::InvalidObject,
            Slot::Live(o) => {
                if o.realm.0 != caller_realm.0 {
                    return HeapWriteRes::CrossRealmAccess;
                }
            }
        }
        let ghost old_h = old(self)@;
        let ghost skey = key@;
        let ghost sval = val@;
        let mut obj = match &self.slots[oid.0] {
            Slot::Live(o) => clone_heap_object(o),
            Slot::Free => return HeapWriteRes::InvalidObject,
        };
        if let ObjectKind::Array { .. } = obj.kind {
            if is_length_key(&key) {
                let ulen = num_to_uint32(prim_to_number(&val)) as usize;
                let mut filtered: Vec<PropEntry> = Vec::new();
                let np = obj.props.len();
                let mut i: usize = 0;
                let ghost src_props = obj@.props;
                proof {
                    assert(spec_props_view(filtered@) =~= Seq::<SpecPropEntry>::empty());
                }
                while i < np
                    invariant
                        i <= np == obj.props@.len(),
                        src_props == obj@.props,
                        spec_filter_props_below_len(src_props, 0, ulen, seq![])
                            == spec_filter_props_below_len(src_props, i as nat, ulen, spec_props_view(filtered@)),
                    decreases np - i,
                {
                    let keep = match parse_array_index(&obj.props[i].key) {
                        Some(ai) => ai < ulen || !obj.props[i].configurable,
                        None => true,
                    };
                    if keep {
                        let ghost pre_f = spec_props_view(filtered@);
                        let ce = clone_prop_entry(&obj.props[i]);
                        filtered.push(ce);
                        proof {
                            assert(spec_props_view(filtered@) =~= pre_f.push(src_props[i as int]));
                        }
                    }
                    i += 1;
                }
                obj.kind = ObjectKind::Array { length: ulen };
                obj.props = filtered;
                self.slots.set(oid.0, Slot::Live(obj));
                proof {
                    assert(self@.slots =~= spec_heap_set_prop(old_h, caller_realm, oid, skey, sval).0.slots);
                }
                return HeapWriteRes::Ok(true);
            }
        }
        match find_prop_exec(&obj.props, &key) {
            Some(idx) => {
                if !obj.props[idx].writable {
                    return HeapWriteRes::Ok(false);
                }
                let next_kind = match obj.kind {
                    ObjectKind::Array { length } => match parse_array_index(&key) {
                        Some(ai) => if ai >= length && ai < usize::MAX {
                            ObjectKind::Array { length: ai + 1 }
                        } else {
                            obj.kind
                        },
                        None => obj.kind,
                    },
                    _ => obj.kind,
                };
                let old_e = clone_prop_entry(&obj.props[idx]);
                obj.props.set(idx, PropEntry {
                    key: old_e.key,
                    value: val,
                    writable: old_e.writable,
                    enumerable: old_e.enumerable,
                    configurable: old_e.configurable,
                });
                obj.kind = next_kind;
                self.slots.set(oid.0, Slot::Live(obj));
                proof {
                    let orig_props = old_h.slots[oid.0 as int]->Live_0.props;
                    assert(self@.slots[oid.0 as int]->Live_0.props =~= orig_props.update(idx as int, SpecPropEntry {
                        value: sval,
                        ..orig_props[idx as int]
                    }));
                    assert(self@.slots =~= spec_heap_set_prop(old_h, caller_realm, oid, skey, sval).0.slots);
                }
                HeapWriteRes::Ok(true)
            }
            None => {
                if !obj.extensible {
                    return HeapWriteRes::Ok(false);
                }
                let next_kind = match obj.kind {
                    ObjectKind::Array { length } => match parse_array_index(&key) {
                        Some(ai) => if ai >= length && ai < usize::MAX {
                            ObjectKind::Array { length: ai + 1 }
                        } else {
                            obj.kind
                        },
                        None => obj.kind,
                    },
                    _ => obj.kind,
                };
                obj.props.push(PropEntry {
                    key,
                    value: val,
                    writable: true,
                    enumerable: true,
                    configurable: true,
                });
                obj.kind = next_kind;
                self.slots.set(oid.0, Slot::Live(obj));
                proof {
                    let orig_props = old_h.slots[oid.0 as int]->Live_0.props;
                    assert(self@.slots[oid.0 as int]->Live_0.props =~= orig_props.push(SpecPropEntry {
                        key: skey,
                        value: sval,
                        writable: true,
                        enumerable: true,
                        configurable: true,
                    }));
                    assert(self@.slots =~= spec_heap_set_prop(old_h, caller_realm, oid, skey, sval).0.slots);
                }
                HeapWriteRes::Ok(true)
            }
        }
    }

    pub fn delete_prop(&mut self, caller_realm: RealmId, oid: ObjId, key: &JsStr) -> (res: HeapWriteRes)
        ensures (final(self)@, res) == spec_heap_delete_prop(old(self)@, caller_realm, oid, key@),
    {
        if oid.0 >= self.slots.len() {
            return HeapWriteRes::InvalidObject;
        }
        proof { assert(self@.slots[oid.0 as int] == self.slots@[oid.0 as int]@); }
        match &self.slots[oid.0] {
            Slot::Free => return HeapWriteRes::InvalidObject,
            Slot::Live(o) => {
                if o.realm.0 != caller_realm.0 {
                    return HeapWriteRes::CrossRealmAccess;
                }
                if let ObjectKind::Array { .. } = o.kind {
                    if is_length_key(key) {
                        return HeapWriteRes::Ok(false);
                    }
                }
            }
        }
        let ghost old_h = old(self)@;
        let ghost skey = key@;
        let mut obj = match &self.slots[oid.0] {
            Slot::Live(o) => clone_heap_object(o),
            Slot::Free => return HeapWriteRes::InvalidObject,
        };
        match find_prop_exec(&obj.props, key) {
            None => HeapWriteRes::Ok(true),
            Some(idx) => {
                if !obj.props[idx].configurable {
                    return HeapWriteRes::Ok(false);
                }
                let np = obj.props.len();
                let mut new_ps: Vec<PropEntry> = Vec::new();
                let mut i: usize = 0;
                let ghost src_ps = obj@.props;
                while i < idx
                    invariant
                        i <= idx < np == obj.props@.len(),
                        src_ps == obj@.props,
                        spec_props_view(new_ps@) =~= src_ps.subrange(0, i as int),
                    decreases idx - i,
                {
                    let ghost pre = spec_props_view(new_ps@);
                    let ce = clone_prop_entry(&obj.props[i]);
                    new_ps.push(ce);
                    proof {
                        assert(spec_props_view(new_ps@) =~= pre.push(src_ps[i as int]));
                        assert(src_ps.subrange(0, (i + 1) as int) =~= src_ps.subrange(0, i as int).push(src_ps[i as int]));
                    }
                    i += 1;
                }
                let mut j: usize = idx + 1;
                while j < np
                    invariant
                        idx + 1 <= j <= np == obj.props@.len(),
                        src_ps == obj@.props,
                        spec_props_view(new_ps@) =~= src_ps.subrange(0, idx as int) + src_ps.subrange((idx + 1) as int, j as int),
                    decreases np - j,
                {
                    let ghost pre = spec_props_view(new_ps@);
                    let ce = clone_prop_entry(&obj.props[j]);
                    new_ps.push(ce);
                    proof {
                        assert(spec_props_view(new_ps@) =~= pre.push(src_ps[j as int]));
                        assert(src_ps.subrange((idx + 1) as int, (j + 1) as int) =~= src_ps.subrange((idx + 1) as int, j as int).push(src_ps[j as int]));
                    }
                    j += 1;
                }
                obj.props = new_ps;
                self.slots.set(oid.0, Slot::Live(obj));
                proof {
                    assert(self@.slots =~= spec_heap_delete_prop(old_h, caller_realm, oid, skey).0.slots);
                }
                HeapWriteRes::Ok(true)
            }
        }
    }

    fn has_steps(&self, caller_realm: RealmId, oid: ObjId, key: &JsStr, steps: usize) -> (r: HeapWriteRes)
        ensures r == spec_heap_has_steps(self@, caller_realm, oid, key@, steps as nat),
    {
        let mut cur = oid;
        let mut rem = steps;
        let ghost sh = self@;
        while rem > 0
            invariant
                rem <= steps,
                sh == self@,
                spec_heap_has_steps(sh, caller_realm, oid, key@, steps as nat)
                    == spec_heap_has_steps(sh, caller_realm, cur, key@, rem as nat),
            decreases rem,
        {
            if cur.0 >= self.slots.len() {
                return HeapWriteRes::InvalidObject;
            }
            proof { assert(sh.slots[cur.0 as int] == self.slots@[cur.0 as int]@); }
            match &self.slots[cur.0] {
                Slot::Free => return HeapWriteRes::InvalidObject,
                Slot::Live(obj) => {
                    if obj.realm.0 != caller_realm.0 {
                        return HeapWriteRes::CrossRealmAccess;
                    } else if matches!(obj.kind, ObjectKind::Array { .. }) && is_length_key(key) {
                        return HeapWriteRes::Ok(true);
                    } else if find_prop_exec(&obj.props, key).is_some() {
                        return HeapWriteRes::Ok(true);
                    } else {
                        match obj.prototype {
                            Some(p) => {
                                cur = p;
                                rem -= 1;
                            }
                            None => return HeapWriteRes::Ok(false),
                        }
                    }
                }
            }
        }
        HeapWriteRes::Ok(false)
    }

    pub fn define_global_var_prop(&mut self, caller_realm: RealmId, oid: ObjId, key: JsStr)
        ensures final(self)@ == spec_define_global_var_prop(old(self)@, caller_realm, oid, key@),
    {
        if oid.0 >= self.slots.len() {
            return;
        }
        proof { assert(self@.slots[oid.0 as int] == self.slots@[oid.0 as int]@); }
        match &self.slots[oid.0] {
            Slot::Free => return,
            Slot::Live(o) => {
                if o.realm.0 != caller_realm.0 || !o.extensible || find_prop_exec(&o.props, &key).is_some() {
                    return;
                }
            }
        }
        let ghost old_h = old(self)@;
        let ghost skey = key@;
        let mut obj = match &self.slots[oid.0] {
            Slot::Live(o) => clone_heap_object(o),
            Slot::Free => return,
        };
        obj.props.push(PropEntry {
            key,
            value: Val::Undefined,
            writable: true,
            enumerable: true,
            configurable: false,
        });
        self.slots.set(oid.0, Slot::Live(obj));
        proof {
            let orig_ps = old_h.slots[oid.0 as int]->Live_0.props;
            assert(self@.slots[oid.0 as int]->Live_0.props =~= orig_ps.push(SpecPropEntry {
                key: skey,
                value: SpecVal::Undefined,
                writable: true,
                enumerable: true,
                configurable: false,
            }));
            assert(self@.slots =~= spec_define_global_var_prop(old_h, caller_realm, oid, skey).slots);
        }
    }

    pub fn has_own_prop(&self, caller_realm: RealmId, oid: ObjId, key: &JsStr) -> (r: HeapWriteRes)
        ensures r == spec_heap_has_own_prop(self@, caller_realm, oid, key@),
    {
        if oid.0 >= self.slots.len() {
            return HeapWriteRes::InvalidObject;
        }
        proof { assert(self@.slots[oid.0 as int] == self.slots@[oid.0 as int]@); }
        match &self.slots[oid.0] {
            Slot::Free => HeapWriteRes::InvalidObject,
            Slot::Live(obj) => {
                if obj.realm.0 != caller_realm.0 {
                    HeapWriteRes::CrossRealmAccess
                } else if matches!(obj.kind, ObjectKind::Array { .. }) && is_length_key(key) {
                    HeapWriteRes::Ok(true)
                } else {
                    HeapWriteRes::Ok(find_prop_exec(&obj.props, key).is_some())
                }
            }
        }
    }

    pub fn has_prop(&self, caller_realm: RealmId, oid: ObjId, key: &JsStr) -> (r: HeapWriteRes)
        ensures r == spec_heap_has_prop(self@, caller_realm, oid, key@),
    {
        let steps = if self.slots.len() == 0 { 1 } else { self.slots.len() };
        self.has_steps(caller_realm, oid, key, steps)
    }

    pub fn is_instance_of_steps(
        &self,
        caller_realm: RealmId,
        cur: ObjId,
        target_proto: ObjId,
        steps: usize,
    ) -> (r: HeapWriteRes)
        ensures r == spec_is_instance_of_steps(self@, caller_realm, cur, target_proto, steps as nat),
    {
        let mut c = cur;
        let mut rem = steps;
        let ghost sh = self@;
        while rem > 0
            invariant
                rem <= steps,
                sh == self@,
                spec_is_instance_of_steps(sh, caller_realm, cur, target_proto, steps as nat)
                    == spec_is_instance_of_steps(sh, caller_realm, c, target_proto, rem as nat),
            decreases rem,
        {
            if c.0 >= self.slots.len() {
                return HeapWriteRes::InvalidObject;
            }
            proof { assert(sh.slots[c.0 as int] == self.slots@[c.0 as int]@); }
            match &self.slots[c.0] {
                Slot::Free => return HeapWriteRes::InvalidObject,
                Slot::Live(obj) => {
                    if obj.realm.0 != caller_realm.0 {
                        return HeapWriteRes::CrossRealmAccess;
                    } else {
                        match obj.prototype {
                            None => return HeapWriteRes::Ok(false),
                            Some(p) => if p.0 == target_proto.0 {
                                return HeapWriteRes::Ok(true);
                            } else {
                                c = p;
                                rem -= 1;
                            },
                        }
                    }
                }
            }
        }
        HeapWriteRes::Ok(false)
    }

    pub fn is_live_same_realm_array(&self, caller_realm: RealmId, oid: ObjId) -> (r: bool)
        ensures r == spec_is_live_same_realm_array(self@, caller_realm, oid),
    {
        if oid.0 >= self.slots.len() {
            return false;
        }
        proof { assert(self@.slots[oid.0 as int] == self.slots@[oid.0 as int]@); }
        match &self.slots[oid.0] {
            Slot::Live(obj) => obj.realm.0 == caller_realm.0 && matches!(obj.kind, ObjectKind::Array { .. }),
            Slot::Free => false,
        }
    }

    pub fn set_array_length(
        &mut self,
        caller_realm: RealmId,
        oid: ObjId,
        new_len: usize,
    ) -> (res: HeapWriteRes)
        ensures (final(self)@, res) == spec_heap_set_array_length(old(self)@, caller_realm, oid, new_len),
    {
        if oid.0 >= self.slots.len() {
            return HeapWriteRes::InvalidObject;
        }
        proof { assert(self@.slots[oid.0 as int] == self.slots@[oid.0 as int]@); }
        match &self.slots[oid.0] {
            Slot::Free => return HeapWriteRes::InvalidObject,
            Slot::Live(o) => {
                if o.realm.0 != caller_realm.0 {
                    return HeapWriteRes::CrossRealmAccess;
                }
                if !matches!(o.kind, ObjectKind::Array { .. }) {
                    return HeapWriteRes::Ok(false);
                }
            }
        }
        let ghost old_h = old(self)@;
        let mut obj = match &self.slots[oid.0] {
            Slot::Live(o) => clone_heap_object(o),
            Slot::Free => return HeapWriteRes::InvalidObject,
        };
        let mut filtered: Vec<PropEntry> = Vec::new();
        let np = obj.props.len();
        let mut i: usize = 0;
        let ghost src_props = obj@.props;
        proof {
            assert(spec_props_view(filtered@) =~= Seq::<SpecPropEntry>::empty());
        }
        while i < np
            invariant
                i <= np == obj.props@.len(),
                src_props == obj@.props,
                spec_filter_props_below_len(src_props, 0, new_len, seq![])
                    == spec_filter_props_below_len(src_props, i as nat, new_len, spec_props_view(filtered@)),
            decreases np - i,
        {
            let keep = match parse_array_index(&obj.props[i].key) {
                Some(ai) => ai < new_len || !obj.props[i].configurable,
                None => true,
            };
            if keep {
                let ghost pre_f = spec_props_view(filtered@);
                let ce = clone_prop_entry(&obj.props[i]);
                filtered.push(ce);
                proof {
                    assert(spec_props_view(filtered@) =~= pre_f.push(src_props[i as int]));
                }
            }
            i += 1;
        }
        obj.kind = ObjectKind::Array { length: new_len };
        obj.props = filtered;
        self.slots.set(oid.0, Slot::Live(obj));
        proof {
            assert(self@.slots =~= spec_heap_set_array_length(old_h, caller_realm, oid, new_len).0.slots);
        }
        HeapWriteRes::Ok(true)
    }

    pub fn collect_for_in_candidates(
        &self,
        caller_realm: RealmId,
        oid: ObjId,
    ) -> (r: Option<Vec<JsStr>>)
        ensures
            match r {
                Some(ks) => spec_collect_for_in_candidates(self@, caller_realm, oid)
                    == Some(crate::ast::spec_str_seq_view(ks@)),
                None => spec_collect_for_in_candidates(self@, caller_realm, oid) is None,
            },
    {
        let mut steps: usize = if self.slots.len() == 0 { 1 } else { self.slots.len() };
        let mut cur_opt: Option<ObjId> = Some(oid);
        let mut seen: Vec<JsStr> = Vec::new();
        let mut out: Vec<JsStr> = Vec::new();
        let ghost sh = self@;
        let ghost init_steps: nat = steps as nat;
        proof {
            assert(crate::ast::spec_str_seq_view(seen@) =~= Seq::<Seq<u16>>::empty());
            assert(crate::ast::spec_str_seq_view(out@) =~= Seq::<Seq<u16>>::empty());
        }
        while steps > 0 && cur_opt.is_some()
            invariant
                steps <= init_steps,
                sh == self@,
                init_steps == (if sh.slots.len() == 0 { 1nat } else { sh.slots.len() }),
                spec_collect_for_in_steps(sh, caller_realm, Some(oid), init_steps, seq![], seq![])
                    == spec_collect_for_in_steps(
                        sh,
                        caller_realm,
                        cur_opt,
                        steps as nat,
                        crate::ast::spec_str_seq_view(seen@),
                        crate::ast::spec_str_seq_view(out@),
                    ),
            decreases steps,
        {
            let cur = cur_opt.unwrap();
            if cur.0 >= self.slots.len() {
                return None;
            }
            proof { assert(sh.slots[cur.0 as int] == self.slots@[cur.0 as int]@); }
            match &self.slots[cur.0] {
                Slot::Free => return None,
                Slot::Live(obj) => {
                    if obj.realm.0 != caller_realm.0 {
                        return None;
                    }
                    if matches!(obj.kind, ObjectKind::Array { .. }) {
                        let mut lk_v: Vec<u16> = Vec::new();
                        lk_v.push(0x6C); lk_v.push(0x65); lk_v.push(0x6E);
                        lk_v.push(0x67); lk_v.push(0x74); lk_v.push(0x68);
                        let lk = JsStr(lk_v);
                        proof { assert(lk@ =~= seq![0x6Cu16, 0x65u16, 0x6Eu16, 0x67u16, 0x74u16, 0x68u16]); }
                        if !str_vec_contains_exec(&seen, &lk) {
                            let ghost pre_s = crate::ast::spec_str_seq_view(seen@);
                            seen.push(lk);
                            proof {
                                assert(crate::ast::spec_str_seq_view(seen@) =~= pre_s.push(seq![0x6Cu16, 0x65u16, 0x6Eu16, 0x67u16, 0x74u16, 0x68u16]));
                            }
                        }
                    }
                    let ghost seen_before_props = crate::ast::spec_str_seq_view(seen@);
                    let ghost out_before_props = crate::ast::spec_str_seq_view(out@);
                    let ghost src_ps = obj@.props;
                    let np = obj.props.len();
                    let mut i: usize = 0;
                    while i < np
                        invariant
                            i <= np == obj.props@.len(),
                            src_ps == obj@.props,
                            spec_collect_for_in_obj_props(src_ps, 0, seen_before_props, out_before_props)
                                == spec_collect_for_in_obj_props(
                                    src_ps,
                                    i as nat,
                                    crate::ast::spec_str_seq_view(seen@),
                                    crate::ast::spec_str_seq_view(out@),
                                ),
                        decreases np - i,
                    {
                        if !str_vec_contains_exec(&seen, &obj.props[i].key) {
                            let ghost pre_s = crate::ast::spec_str_seq_view(seen@);
                            seen.push(clone_js_str(&obj.props[i].key));
                            proof {
                                assert(crate::ast::spec_str_seq_view(seen@) =~= pre_s.push(src_ps[i as int].key));
                            }
                            if obj.props[i].enumerable {
                                let ghost pre_o = crate::ast::spec_str_seq_view(out@);
                                out.push(clone_js_str(&obj.props[i].key));
                                proof {
                                    assert(crate::ast::spec_str_seq_view(out@) =~= pre_o.push(src_ps[i as int].key));
                                }
                            }
                        }
                        i += 1;
                    }
                    cur_opt = obj.prototype;
                    steps -= 1;
                }
            }
        }
        Some(out)
    }

    pub fn is_for_in_key_live_enumerable(
        &self,
        caller_realm: RealmId,
        oid: ObjId,
        key: &JsStr,
    ) -> (r: bool)
        ensures r == spec_is_for_in_key_live_enumerable(self@, caller_realm, oid, key@),
    {
        let mut steps: usize = if self.slots.len() == 0 { 1 } else { self.slots.len() };
        let mut cur = oid;
        let ghost sh = self@;
        let ghost init_steps = steps as nat;
        while steps > 0
            invariant
                steps <= init_steps,
                sh == self@,
                init_steps == (if sh.slots.len() == 0 { 1nat } else { sh.slots.len() }),
                spec_is_for_in_key_live_steps(sh, caller_realm, oid, key@, init_steps)
                    == spec_is_for_in_key_live_steps(sh, caller_realm, cur, key@, steps as nat),
            decreases steps,
        {
            if cur.0 >= self.slots.len() {
                return false;
            }
            proof { assert(sh.slots[cur.0 as int] == self.slots@[cur.0 as int]@); }
            match &self.slots[cur.0] {
                Slot::Free => return false,
                Slot::Live(obj) => {
                    if obj.realm.0 != caller_realm.0 {
                        return false;
                    }
                    if matches!(obj.kind, ObjectKind::Array { .. }) && is_length_key(key) {
                        return false;
                    }
                    match find_prop_exec(&obj.props, key) {
                        Some(idx) => return obj.props[idx].enumerable,
                        None => match obj.prototype {
                            Some(p) => {
                                cur = p;
                                steps -= 1;
                            }
                            None => return false,
                        },
                    }
                }
            }
        }
        false
    }

    pub fn own_enumerable_keys(&self, caller_realm: RealmId, oid: ObjId) -> (r: Option<Vec<JsStr>>)
        ensures
            match r {
                Some(ks) => crate::ast::spec_str_seq_view(ks@) == spec_own_enumerable_keys(self@, caller_realm, oid).unwrap(),
                None => spec_own_enumerable_keys(self@, caller_realm, oid) is None,
            },
            r.is_some() == (spec_own_enumerable_keys(self@, caller_realm, oid) is Some),
    {
        if oid.0 >= self.slots.len() {
            return None;
        }
        proof { assert(self@.slots[oid.0 as int] == self.slots@[oid.0 as int]@); }
        match &self.slots[oid.0] {
            Slot::Free => None,
            Slot::Live(obj) => {
                if obj.realm.0 != caller_realm.0 {
                    return None;
                }
                let np = obj.props.len();
                let mut out: Vec<JsStr> = Vec::new();
                let mut i: usize = 0;
                let ghost src_ps = obj@.props;
                proof {
                    assert(crate::ast::spec_str_seq_view(out@) =~= Seq::<Seq<u16>>::empty());
                }
                while i < np
                    invariant
                        i <= np == obj.props@.len(),
                        src_ps == obj@.props,
                        spec_collect_enum_keys(src_ps, 0, seq![])
                            == spec_collect_enum_keys(src_ps, i as nat, crate::ast::spec_str_seq_view(out@)),
                    decreases np - i,
                {
                    if obj.props[i].enumerable {
                        let ghost pre = crate::ast::spec_str_seq_view(out@);
                        let ck = clone_js_str(&obj.props[i].key);
                        out.push(ck);
                        proof {
                            assert(crate::ast::spec_str_seq_view(out@) =~= pre.push(src_ps[i as int].key));
                        }
                    }
                    i += 1;
                }
                Some(out)
            }
        }
    }
}

pub open spec fn spec_collect_enum_keys(
    props: Seq<SpecPropEntry>,
    idx: nat,
    acc: Seq<Seq<u16>>,
) -> Seq<Seq<u16>>
    decreases props.len() - idx,
{
    if idx >= props.len() {
        acc
    } else {
        let next_acc = if props[idx as int].enumerable {
            acc.push(props[idx as int].key)
        } else {
            acc
        };
        spec_collect_enum_keys(props, idx + 1, next_acc)
    }
}

pub open spec fn spec_own_enumerable_keys(
    heap: SpecHeap,
    caller_realm: RealmId,
    oid: ObjId,
) -> Option<Seq<Seq<u16>>> {
    if (oid.0 as int) >= heap.slots.len() {
        None
    } else {
        match heap.slots[oid.0 as int] {
            SpecSlot::Free => None,
            SpecSlot::Live(obj) => {
                if obj.realm != caller_realm {
                    None
                } else {
                    Some(spec_collect_enum_keys(obj.props, 0, seq![]))
                }
            }
        }
    }
}


pub open spec fn spec_is_live_same_realm_array(
    heap: SpecHeap,
    caller_realm: RealmId,
    oid: ObjId,
) -> bool {
    if (oid.0 as int) >= heap.slots.len() {
        false
    } else {
        match heap.slots[oid.0 as int] {
            SpecSlot::Live(obj) => obj.realm == caller_realm && (obj.kind is Array),
            SpecSlot::Free => false,
        }
    }
}

pub open spec fn spec_heap_set_array_length(
    heap: SpecHeap,
    caller_realm: RealmId,
    oid: ObjId,
    new_len: usize,
) -> (SpecHeap, HeapWriteRes) {
    if (oid.0 as int) >= heap.slots.len() {
        (heap, HeapWriteRes::InvalidObject)
    } else {
        match heap.slots[oid.0 as int] {
            SpecSlot::Free => (heap, HeapWriteRes::InvalidObject),
            SpecSlot::Live(obj) => {
                if obj.realm != caller_realm {
                    (heap, HeapWriteRes::CrossRealmAccess)
                } else if !(obj.kind is Array) {
                    (heap, HeapWriteRes::Ok(false))
                } else {
                    let new_props = spec_filter_props_below_len(obj.props, 0, new_len, seq![]);
                    let obj2 = SpecHeapObject {
                        kind: ObjectKind::Array { length: new_len },
                        props: new_props,
                        ..obj
                    };
                    (
                        SpecHeap { slots: heap.slots.update(oid.0 as int, SpecSlot::Live(obj2)), ..heap },
                        HeapWriteRes::Ok(true),
                    )
                }
            }
        }
    }
}

pub open spec fn spec_str_seq_contains_from(v: Seq<Seq<u16>>, key: Seq<u16>, idx: nat) -> bool
    decreases v.len() - idx,
{
    if idx >= v.len() {
        false
    } else if v[idx as int] == key {
        true
    } else {
        spec_str_seq_contains_from(v, key, idx + 1)
    }
}

pub(crate) fn str_vec_contains_exec(v: &Vec<JsStr>, key: &JsStr) -> (r: bool)
    ensures r == spec_str_seq_contains_from(crate::ast::spec_str_seq_view(v@), key@, 0),
{
    let n = v.len();
    let mut i: usize = 0;
    let ghost sv = crate::ast::spec_str_seq_view(v@);
    while i < n
        invariant
            i <= n == v@.len(),
            sv == crate::ast::spec_str_seq_view(v@),
            spec_str_seq_contains_from(sv, key@, 0) == spec_str_seq_contains_from(sv, key@, i as nat),
        decreases n - i,
    {
        if js_str_eq(&v[i], key) {
            return true;
        }
        i += 1;
    }
    false
}

pub open spec fn spec_collect_for_in_obj_props(
    props: Seq<SpecPropEntry>,
    idx: nat,
    seen: Seq<Seq<u16>>,
    out: Seq<Seq<u16>>,
) -> (Seq<Seq<u16>>, Seq<Seq<u16>>)
    decreases props.len() - idx,
{
    if idx >= props.len() {
        (seen, out)
    } else {
        let e = props[idx as int];
        if spec_str_seq_contains_from(seen, e.key, 0) {
            spec_collect_for_in_obj_props(props, idx + 1, seen, out)
        } else {
            let s2 = seen.push(e.key);
            let o2 = if e.enumerable { out.push(e.key) } else { out };
            spec_collect_for_in_obj_props(props, idx + 1, s2, o2)
        }
    }
}

pub open spec fn spec_collect_for_in_steps(
    heap: SpecHeap,
    caller_realm: RealmId,
    cur_opt: Option<ObjId>,
    steps: nat,
    seen: Seq<Seq<u16>>,
    out: Seq<Seq<u16>>,
) -> Option<Seq<Seq<u16>>>
    decreases steps,
{
    if steps == 0 || (cur_opt is None) {
        Some(out)
    } else {
        let cur = cur_opt.unwrap();
        if (cur.0 as int) >= heap.slots.len() {
            None
        } else {
            match heap.slots[cur.0 as int] {
                SpecSlot::Free => None,
                SpecSlot::Live(obj) => {
                    if obj.realm != caller_realm {
                        None
                    } else {
                        let lk = seq![0x6Cu16, 0x65u16, 0x6Eu16, 0x67u16, 0x74u16, 0x68u16];
                        let s1 = if (obj.kind is Array) && !spec_str_seq_contains_from(seen, lk, 0) {
                            seen.push(lk)
                        } else {
                            seen
                        };
                        let (s2, o2) = spec_collect_for_in_obj_props(obj.props, 0, s1, out);
                        spec_collect_for_in_steps(heap, caller_realm, obj.prototype, (steps - 1) as nat, s2, o2)
                    }
                }
            }
        }
    }
}

pub open spec fn spec_collect_for_in_candidates(
    heap: SpecHeap,
    caller_realm: RealmId,
    oid: ObjId,
) -> Option<Seq<Seq<u16>>> {
    let steps = if heap.slots.len() == 0 { 1 } else { heap.slots.len() };
    spec_collect_for_in_steps(heap, caller_realm, Some(oid), steps, seq![], seq![])
}

pub open spec fn spec_is_for_in_key_live_steps(
    heap: SpecHeap,
    caller_realm: RealmId,
    cur: ObjId,
    key: Seq<u16>,
    steps: nat,
) -> bool
    decreases steps,
{
    if steps == 0 || (cur.0 as int) >= heap.slots.len() {
        false
    } else {
        match heap.slots[cur.0 as int] {
            SpecSlot::Free => false,
            SpecSlot::Live(obj) => {
                if obj.realm != caller_realm {
                    false
                } else if (obj.kind is Array) && spec_is_length_key(key) {
                    false
                } else {
                    match spec_find_prop(obj.props, key) {
                        Some(idx) => obj.props[idx as int].enumerable,
                        None => match obj.prototype {
                            Some(p) => spec_is_for_in_key_live_steps(heap, caller_realm, p, key, (steps - 1) as nat),
                            None => false,
                        },
                    }
                }
            }
        }
    }
}

pub open spec fn spec_is_for_in_key_live_enumerable(
    heap: SpecHeap,
    caller_realm: RealmId,
    oid: ObjId,
    key: Seq<u16>,
) -> bool {
    let steps = if heap.slots.len() == 0 { 1 } else { heap.slots.len() };
    spec_is_for_in_key_live_steps(heap, caller_realm, oid, key, steps)
}

} // verus!
