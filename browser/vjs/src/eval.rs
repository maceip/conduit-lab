//! Verified ECMAScript Interpreter Core (`VmState`, `spec_eval_*`, `eval_*`, `run`, `run_with_quota`)
//! and End-to-End Step-Refinement + Fuel-Exactness Theorems (`docs/verified-browser-engine.md` §3.3).
use crate::ast::{
    AssignOp, BinOp, ChainStep, ExprId, ExprNode, ForEachLhs, FuncId, LogicalOp, Program, PropInit,
    PropKeyInit, StmtId, StmtNode, SwitchCase, UnaryOp, UnsupportedFeature, UpdateOp,
    VarDeclarator, VarKind,
};
#[cfg(verus_keep_ghost)]
use crate::ast::{
    spec_chain_steps_view, spec_opt_str_view, spec_prop_inits_view, spec_str_seq_view,
    spec_switch_cases_view, spec_var_decls_view, SpecChainStep, SpecExprNode, SpecForEachLhs,
    SpecProgram, SpecPropInit, SpecPropKeyInit, SpecStmtNode, SpecSwitchCase, SpecVarDeclarator,
};
use crate::completion::{
    unwrap_or_undefined, update_empty, update_empty_val, Completion, CompletionValue, ExprStep,
    RunResult, ScriptCompletion, SpecCompletionValue, SpecExprStep, SpecStmtStep, StmtStep,
};
#[cfg(verus_keep_ghost)]
use crate::completion::{
    spec_unwrap_or_undefined, spec_update_empty, spec_update_empty_val, SpecCompletion,
    SpecOutcome, SpecScriptCompletion,
};
use crate::env::{EnvArena, EnvId, EnvKind, IdentAssignOutcome, IdentLookup, SpecEnvArena};
#[cfg(verus_keep_ghost)]
use crate::env::{
    env_wf, spec_alloc_env, spec_bind_initialized, spec_clone_per_iter_env, spec_declare_tdz,
    spec_declare_var, spec_delete_identifier, spec_find_var_env, spec_get_identifier,
    spec_initialize_lexical, spec_new_global_env, spec_resolve_binding_loc, spec_resolve_this,
    spec_set_identifier, SpecIdentLookup,
};
use crate::heap::{
    is_length_key, parse_array_index, AllocRes, BuiltinFn, ErrorKind, Heap, HeapObject,
    HeapReadVal, HeapWriteRes, ObjectKind, PropEntry, RealmId, RealmIntrinsics, Slot, SpecHeap,
};
#[cfg(verus_keep_ghost)]
use crate::heap::{
    spec_alloc_with_gc, spec_collect_for_in_candidates, spec_define_global_var_prop,
    spec_heap_delete_prop, spec_heap_get_prop, spec_heap_has_own_prop, spec_heap_has_prop,
    spec_heap_set_array_length, spec_heap_set_prop, spec_is_for_in_key_live_enumerable,
    spec_is_instance_of_steps, spec_is_length_key, spec_is_live_same_realm_array,
    spec_own_enumerable_keys, spec_parse_array_index, spec_props_view, spec_str_seq_contains_from,
    spec_vals_view, SpecHeapObject, SpecHeapReadVal, SpecPropEntry, SpecSlot,
};
use crate::value::{
    clone_js_str, clone_val, js_str_concat, js_str_eq, js_str_lt, num_add, num_bit_and,
    num_bit_not, num_bit_or, num_bit_xor, num_div, num_equal, num_exp,
    num_from_usize, num_less_than, num_mul, num_neg, num_rem, num_shl, num_shr, num_sub,
    num_to_uint32, num_ushr, number_to_js_str, prim_to_js_str, prim_to_number, val_loose_eq_prim,
    val_same_value, val_strict_eq, val_to_boolean, JsNum, JsStr, ObjId, SpecVal, Val, NAN_BITS, ONE_BITS,
    POS_INF_BITS, POS_ZERO_BITS,
};
#[cfg(verus_keep_ghost)]
use crate::value::{
    spec_loose_eq_prim, spec_num_add, spec_num_bit_and, spec_num_bit_not, spec_num_bit_or,
    spec_num_bit_xor, spec_num_div, spec_num_equal, spec_num_exp, spec_num_from_i64,
    spec_num_from_usize, spec_num_less_than, spec_num_mul, spec_num_neg, spec_num_rem,
    spec_num_shl, spec_num_shr, spec_num_sub, spec_num_ushr, spec_number_to_string,
    spec_prim_to_number, spec_prim_to_string, spec_same_value, spec_str_lt, spec_strict_eq,
    spec_to_boolean, spec_to_uint32,
};
use vstd::prelude::*;

verus! {

pub const DEFAULT_REALM_HEAP_QUOTA: usize = 65_536;

/// Complete executable VM state for a single ECMAScript realm.
pub struct VmState {
    pub envs: EnvArena,
    pub heap: Heap,
    pub intr: RealmIntrinsics,
    pub current_env: EnvId,
    pub env_roots: Vec<EnvId>,
    pub strict: bool,
    pub fuel: usize,
    pub temp_roots: Vec<Val>,
}

/// Complete ghost specification state.
pub struct SpecState {
    pub envs: SpecEnvArena,
    pub heap: SpecHeap,
    pub intr: RealmIntrinsics,
    pub current_env: EnvId,
    pub env_roots: Seq<EnvId>,
    pub strict: bool,
    pub fuel: nat,
    pub temp_roots: Seq<SpecVal>,
}

impl View for VmState {
    type V = SpecState;

    open spec fn view(&self) -> SpecState {
        SpecState {
            envs: self.envs@,
            heap: self.heap@,
            intr: self.intr,
            current_env: self.current_env,
            env_roots: self.env_roots@,
            strict: self.strict,
            fuel: self.fuel as nat,
            temp_roots: spec_vals_view(self.temp_roots@),
        }
    }
}

// ---------------------------------------------------------------------------
// Verified UTF-16 Property & Intrinsic Identifier Constants
// ---------------------------------------------------------------------------

} // verus!

macro_rules! def_js_key {
    ($spec_fn:ident, $exec_fn:ident, [ $( $ch:expr ),* ]) => {
        verus! {
        pub open spec fn $spec_fn() -> Seq<u16> {
            seq![ $( $ch as u16 ),* ]
        }

        #[allow(unused_mut)]
        pub fn $exec_fn() -> (r: JsStr)
            ensures r@ == $spec_fn(),
        {
            let mut v: Vec<u16> = Vec::new();
            $( v.push($ch); )*
            proof { assert(v@ =~= $spec_fn()); }
            JsStr(v)
        }
        }
    };
}

def_js_key!(spec_k_empty, k_empty, []);
def_js_key!(spec_k_comma, k_comma, [0x2C]);
def_js_key!(spec_k_colon_space, k_colon_space, [0x3A, 0x20]);
def_js_key!(spec_k_prototype, k_prototype, [0x70, 0x72, 0x6F, 0x74, 0x6F, 0x74, 0x79, 0x70, 0x65]);
def_js_key!(spec_k_constructor, k_constructor, [0x63, 0x6F, 0x6E, 0x73, 0x74, 0x72, 0x75, 0x63, 0x74, 0x6F, 0x72]);
def_js_key!(spec_k_length, k_length, [0x6C, 0x65, 0x6E, 0x67, 0x74, 0x68]);
def_js_key!(spec_k_name, k_name, [0x6E, 0x61, 0x6D, 0x65]);
def_js_key!(spec_k_message, k_message, [0x6D, 0x65, 0x73, 0x73, 0x61, 0x67, 0x65]);
def_js_key!(spec_k_to_string, k_to_string, [0x74, 0x6F, 0x53, 0x74, 0x72, 0x69, 0x6E, 0x67]);
def_js_key!(spec_k_value_of, k_value_of, [0x76, 0x61, 0x6C, 0x75, 0x65, 0x4F, 0x66]);
def_js_key!(spec_k_push, k_push, [0x70, 0x75, 0x73, 0x68]);
def_js_key!(spec_k_pop, k_pop, [0x70, 0x6F, 0x70]);
def_js_key!(spec_k_join, k_join, [0x6A, 0x6F, 0x69, 0x6E]);
def_js_key!(spec_k_call, k_call, [0x63, 0x61, 0x6C, 0x6C]);
def_js_key!(spec_k_is_array, k_is_array, [0x69, 0x73, 0x41, 0x72, 0x72, 0x61, 0x79]);
def_js_key!(spec_k_is, k_is, [0x69, 0x73]);
def_js_key!(spec_k_keys, k_keys, [0x6B, 0x65, 0x79, 0x73]);
def_js_key!(spec_k_has_own, k_has_own, [0x68, 0x61, 0x73, 0x4F, 0x77, 0x6E, 0x50, 0x72, 0x6F, 0x70, 0x65, 0x72, 0x74, 0x79]);
def_js_key!(spec_k_arguments, k_arguments, [0x61, 0x72, 0x67, 0x75, 0x6D, 0x65, 0x6E, 0x74, 0x73]);
def_js_key!(spec_k_undefined, k_undefined, [0x75, 0x6E, 0x64, 0x65, 0x66, 0x69, 0x6E, 0x65, 0x64]);
def_js_key!(spec_k_nan, k_nan, [0x4E, 0x61, 0x4E]);
def_js_key!(spec_k_infinity, k_infinity, [0x49, 0x6E, 0x66, 0x69, 0x6E, 0x69, 0x74, 0x79]);
def_js_key!(spec_k_global_this, k_global_this, [0x67, 0x6C, 0x6F, 0x62, 0x61, 0x6C, 0x54, 0x68, 0x69, 0x73]);

def_js_key!(spec_k_error, k_error, [0x45, 0x72, 0x72, 0x6F, 0x72]);
def_js_key!(spec_k_ref_error, k_ref_error, [0x52, 0x65, 0x66, 0x65, 0x72, 0x65, 0x6E, 0x63, 0x65, 0x45, 0x72, 0x72, 0x6F, 0x72]);
def_js_key!(spec_k_type_error, k_type_error, [0x54, 0x79, 0x70, 0x65, 0x45, 0x72, 0x72, 0x6F, 0x72]);
def_js_key!(spec_k_syntax_error, k_syntax_error, [0x53, 0x79, 0x6E, 0x74, 0x61, 0x78, 0x45, 0x72, 0x72, 0x6F, 0x72]);
def_js_key!(spec_k_range_error, k_range_error, [0x52, 0x61, 0x6E, 0x67, 0x65, 0x45, 0x72, 0x72, 0x6F, 0x72]);
def_js_key!(spec_k_ctor_object, k_ctor_object, [0x4F, 0x62, 0x6A, 0x65, 0x63, 0x74]);
def_js_key!(spec_k_ctor_array, k_ctor_array, [0x41, 0x72, 0x72, 0x61, 0x79]);
def_js_key!(spec_k_ctor_string, k_ctor_string, [0x53, 0x74, 0x72, 0x69, 0x6E, 0x67]);
def_js_key!(spec_k_ctor_number, k_ctor_number, [0x4E, 0x75, 0x6D, 0x62, 0x65, 0x72]);
def_js_key!(spec_k_ctor_boolean, k_ctor_boolean, [0x42, 0x6F, 0x6F, 0x6C, 0x65, 0x61, 0x6E]);

def_js_key!(spec_t_object, t_object, [0x6F, 0x62, 0x6A, 0x65, 0x63, 0x74]);
def_js_key!(spec_t_function, t_function, [0x66, 0x75, 0x6E, 0x63, 0x74, 0x69, 0x6F, 0x6E]);
def_js_key!(spec_t_boolean, t_boolean, [0x62, 0x6F, 0x6F, 0x6C, 0x65, 0x61, 0x6E]);
def_js_key!(spec_t_number, t_number, [0x6E, 0x75, 0x6D, 0x62, 0x65, 0x72]);
def_js_key!(spec_t_string, t_string, [0x73, 0x74, 0x72, 0x69, 0x6E, 0x67]);

def_js_key!(spec_tag_undef, tag_undef, [0x5B, 0x6F, 0x62, 0x6A, 0x65, 0x63, 0x74, 0x20, 0x55, 0x6E, 0x64, 0x65, 0x66, 0x69, 0x6E, 0x65, 0x64, 0x5D]);
def_js_key!(spec_tag_null, tag_null, [0x5B, 0x6F, 0x62, 0x6A, 0x65, 0x63, 0x74, 0x20, 0x4E, 0x75, 0x6C, 0x6C, 0x5D]);
def_js_key!(spec_tag_bool, tag_bool, [0x5B, 0x6F, 0x62, 0x6A, 0x65, 0x63, 0x74, 0x20, 0x42, 0x6F, 0x6F, 0x6C, 0x65, 0x61, 0x6E, 0x5D]);
def_js_key!(spec_tag_num, tag_num, [0x5B, 0x6F, 0x62, 0x6A, 0x65, 0x63, 0x74, 0x20, 0x4E, 0x75, 0x6D, 0x62, 0x65, 0x72, 0x5D]);
def_js_key!(spec_tag_str, tag_str, [0x5B, 0x6F, 0x62, 0x6A, 0x65, 0x63, 0x74, 0x20, 0x53, 0x74, 0x72, 0x69, 0x6E, 0x67, 0x5D]);
def_js_key!(spec_tag_arr, tag_arr, [0x5B, 0x6F, 0x62, 0x6A, 0x65, 0x63, 0x74, 0x20, 0x41, 0x72, 0x72, 0x61, 0x79, 0x5D]);
def_js_key!(spec_tag_fn, tag_fn, [0x5B, 0x6F, 0x62, 0x6A, 0x65, 0x63, 0x74, 0x20, 0x46, 0x75, 0x6E, 0x63, 0x74, 0x69, 0x6F, 0x6E, 0x5D]);
def_js_key!(spec_tag_err, tag_err, [0x5B, 0x6F, 0x62, 0x6A, 0x65, 0x63, 0x74, 0x20, 0x45, 0x72, 0x72, 0x6F, 0x72, 0x5D]);
def_js_key!(spec_tag_obj, tag_obj, [0x5B, 0x6F, 0x62, 0x6A, 0x65, 0x63, 0x74, 0x20, 0x4F, 0x62, 0x6A, 0x65, 0x63, 0x74, 0x5D]);

verus! {

// ---------------------------------------------------------------------------
// Realm Bootstrap (`spec_bootstrap_realm` & `bootstrap_realm`)
// ---------------------------------------------------------------------------

pub open spec fn spec_prop_data(key: Seq<u16>, value: SpecVal, enumerable: bool) -> SpecPropEntry {
    SpecPropEntry {
        key,
        value,
        writable: true,
        enumerable,
        configurable: true,
    }
}

fn make_prop_data(key: JsStr, value: Val, enumerable: bool) -> (r: PropEntry)
    ensures r@ == spec_prop_data(key@, value@, enumerable),
{
    PropEntry {
        key,
        value,
        writable: true,
        enumerable,
        configurable: true,
    }
}

pub open spec fn spec_error_proto_for(intr: RealmIntrinsics, kind: ErrorKind) -> ObjId {
    match kind {
        ErrorKind::Error => intr.error_proto,
        ErrorKind::ReferenceError => intr.ref_error_proto,
        ErrorKind::TypeError => intr.type_error_proto,
        ErrorKind::SyntaxError => intr.syntax_error_proto,
        ErrorKind::RangeError => intr.range_error_proto,
    }
}

pub fn error_proto_for(intr: &RealmIntrinsics, kind: ErrorKind) -> (r: ObjId)
    ensures r == spec_error_proto_for(*intr, kind),
{
    match kind {
        ErrorKind::Error => intr.error_proto,
        ErrorKind::ReferenceError => intr.ref_error_proto,
        ErrorKind::TypeError => intr.type_error_proto,
        ErrorKind::SyntaxError => intr.syntax_error_proto,
        ErrorKind::RangeError => intr.range_error_proto,
    }
}

pub open spec fn spec_mk_builtin_obj(
    realm: RealmId,
    fn_proto: ObjId,
    b: BuiltinFn,
    proto_obj: Option<ObjId>,
    name: Seq<u16>,
) -> SpecHeapObject {
    let p0 = spec_prop_data(spec_k_name(), SpecVal::Str(name), false);
    let props = match proto_obj {
        Some(po) => seq![p0, spec_prop_data(spec_k_prototype(), SpecVal::Object(po), false)],
        None => seq![p0],
    };
    SpecHeapObject {
        realm,
        prototype: Some(fn_proto),
        extensible: true,
        kind: ObjectKind::BuiltinFunction { builtin: b, prototype_obj: proto_obj },
        props,
    }
}

fn mk_builtin_obj(
    realm: RealmId,
    fn_proto: ObjId,
    b: BuiltinFn,
    proto_obj: Option<ObjId>,
    name: JsStr,
) -> (r: HeapObject)
    ensures r@ == spec_mk_builtin_obj(realm, fn_proto, b, proto_obj, name@),
{
    let mut props: Vec<PropEntry> = Vec::new();
    let ghost sname = name@;
    props.push(make_prop_data(k_name(), Val::Str(name), false));
    if let Some(po) = proto_obj {
        props.push(make_prop_data(k_prototype(), Val::Object(po), false));
    }
    let r = HeapObject {
        realm,
        prototype: Some(fn_proto),
        extensible: true,
        kind: ObjectKind::BuiltinFunction { builtin: b, prototype_obj: proto_obj },
        props,
    };
    proof {
        assert(r@.props =~= spec_mk_builtin_obj(realm, fn_proto, b, proto_obj, sname).props);
    }
    r
}

#[verifier::opaque]
pub open spec fn spec_bootstrap_slots_a() -> Seq<SpecSlot> {
    let realm = RealmId(1);
    let object_proto = ObjId(0);
    let error_proto = ObjId(3);
    let error_ctor = ObjId(8);
    let ref_error_ctor = ObjId(9);
    let type_error_ctor = ObjId(10);
    let syntax_error_ctor = ObjId(11);
    let object_ctor = ObjId(13);
    let array_ctor = ObjId(14);
    let fn_obj_to_str = ObjId(18);
    let fn_err_to_str = ObjId(19);
    let fn_fn_call = ObjId(20);
    let fn_arr_push = ObjId(21);
    let fn_arr_pop = ObjId(22);
    let fn_arr_join = ObjId(23);
    let fn_obj_has_own = ObjId(27);

    let s0 = SpecSlot::Live(SpecHeapObject {
        realm,
        prototype: None,
        extensible: true,
        kind: ObjectKind::Ordinary,
        props: seq![
            spec_prop_data(spec_k_constructor(), SpecVal::Object(object_ctor), false),
            spec_prop_data(spec_k_to_string(), SpecVal::Object(fn_obj_to_str), false),
            spec_prop_data(spec_k_has_own(), SpecVal::Object(fn_obj_has_own), false),
        ],
    });
    let s1 = SpecSlot::Live(SpecHeapObject {
        realm,
        prototype: Some(object_proto),
        extensible: true,
        kind: ObjectKind::BuiltinFunction { builtin: BuiltinFn::FunctionCall, prototype_obj: None },
        props: seq![spec_prop_data(spec_k_call(), SpecVal::Object(fn_fn_call), false)],
    });
    let s2 = SpecSlot::Live(SpecHeapObject {
        realm,
        prototype: Some(object_proto),
        extensible: true,
        kind: ObjectKind::Array { length: 0 },
        props: seq![
            spec_prop_data(spec_k_constructor(), SpecVal::Object(array_ctor), false),
            spec_prop_data(spec_k_push(), SpecVal::Object(fn_arr_push), false),
            spec_prop_data(spec_k_pop(), SpecVal::Object(fn_arr_pop), false),
            spec_prop_data(spec_k_join(), SpecVal::Object(fn_arr_join), false),
            spec_prop_data(spec_k_to_string(), SpecVal::Object(fn_arr_join), false),
        ],
    });
    let s3 = SpecSlot::Live(SpecHeapObject {
        realm,
        prototype: Some(object_proto),
        extensible: true,
        kind: ObjectKind::Ordinary,
        props: seq![
            spec_prop_data(spec_k_constructor(), SpecVal::Object(error_ctor), false),
            spec_prop_data(spec_k_name(), SpecVal::Str(spec_k_error()), false),
            spec_prop_data(spec_k_message(), SpecVal::Str(spec_k_empty()), false),
            spec_prop_data(spec_k_to_string(), SpecVal::Object(fn_err_to_str), false),
        ],
    });
    let s4 = SpecSlot::Live(SpecHeapObject {
        realm,
        prototype: Some(error_proto),
        extensible: true,
        kind: ObjectKind::Ordinary,
        props: seq![
            spec_prop_data(spec_k_constructor(), SpecVal::Object(ref_error_ctor), false),
            spec_prop_data(spec_k_name(), SpecVal::Str(spec_k_ref_error()), false),
            spec_prop_data(spec_k_message(), SpecVal::Str(spec_k_empty()), false),
        ],
    });
    let s5 = SpecSlot::Live(SpecHeapObject {
        realm,
        prototype: Some(error_proto),
        extensible: true,
        kind: ObjectKind::Ordinary,
        props: seq![
            spec_prop_data(spec_k_constructor(), SpecVal::Object(type_error_ctor), false),
            spec_prop_data(spec_k_name(), SpecVal::Str(spec_k_type_error()), false),
            spec_prop_data(spec_k_message(), SpecVal::Str(spec_k_empty()), false),
        ],
    });
    let s6 = SpecSlot::Live(SpecHeapObject {
        realm,
        prototype: Some(error_proto),
        extensible: true,
        kind: ObjectKind::Ordinary,
        props: seq![
            spec_prop_data(spec_k_constructor(), SpecVal::Object(syntax_error_ctor), false),
            spec_prop_data(spec_k_name(), SpecVal::Str(spec_k_syntax_error()), false),
            spec_prop_data(spec_k_message(), SpecVal::Str(spec_k_empty()), false),
        ],
    });
    seq![s0, s1, s2, s3, s4, s5, s6]
}

fn bootstrap_slots_a(heap: &mut Heap)
    requires old(heap)@.slots.len() == 0,
    ensures
        final(heap)@.slots == spec_bootstrap_slots_a(),
        final(heap)@.realm_heap_quota == old(heap)@.realm_heap_quota,
{
    reveal(spec_bootstrap_slots_a);
    let realm = RealmId(1);
    let object_proto = ObjId(0);
    let error_proto = ObjId(3);
    let error_ctor = ObjId(8);
    let ref_error_ctor = ObjId(9);
    let type_error_ctor = ObjId(10);
    let syntax_error_ctor = ObjId(11);
    let object_ctor = ObjId(13);
    let array_ctor = ObjId(14);
    let fn_obj_to_str = ObjId(18);
    let fn_err_to_str = ObjId(19);
    let fn_fn_call = ObjId(20);
    let fn_arr_push = ObjId(21);
    let fn_arr_pop = ObjId(22);
    let fn_arr_join = ObjId(23);
    let fn_obj_has_own = ObjId(27);

    let mut p0: Vec<PropEntry> = Vec::new();
    p0.push(make_prop_data(k_constructor(), Val::Object(object_ctor), false));
    p0.push(make_prop_data(k_to_string(), Val::Object(fn_obj_to_str), false));
    p0.push(make_prop_data(k_has_own(), Val::Object(fn_obj_has_own), false));
    let o0 = HeapObject { realm, prototype: None, extensible: true, kind: ObjectKind::Ordinary, props: p0 };
    proof {
        assert(o0@.props =~= seq![
            spec_prop_data(spec_k_constructor(), SpecVal::Object(object_ctor), false),
            spec_prop_data(spec_k_to_string(), SpecVal::Object(fn_obj_to_str), false),
            spec_prop_data(spec_k_has_own(), SpecVal::Object(fn_obj_has_own), false),
        ]);
    }
    heap.alloc_bootstrap(o0);

    let mut p1: Vec<PropEntry> = Vec::new();
    p1.push(make_prop_data(k_call(), Val::Object(fn_fn_call), false));
    let o1 = HeapObject { realm, prototype: Some(object_proto), extensible: true, kind: ObjectKind::BuiltinFunction { builtin: BuiltinFn::FunctionCall, prototype_obj: None }, props: p1 };
    proof { assert(o1@.props =~= seq![spec_prop_data(spec_k_call(), SpecVal::Object(fn_fn_call), false)]); }
    heap.alloc_bootstrap(o1);

    let mut p2: Vec<PropEntry> = Vec::new();
    p2.push(make_prop_data(k_constructor(), Val::Object(array_ctor), false));
    p2.push(make_prop_data(k_push(), Val::Object(fn_arr_push), false));
    p2.push(make_prop_data(k_pop(), Val::Object(fn_arr_pop), false));
    p2.push(make_prop_data(k_join(), Val::Object(fn_arr_join), false));
    p2.push(make_prop_data(k_to_string(), Val::Object(fn_arr_join), false));
    let o2 = HeapObject { realm, prototype: Some(object_proto), extensible: true, kind: ObjectKind::Array { length: 0 }, props: p2 };
    proof {
        assert(o2@.props =~= seq![
            spec_prop_data(spec_k_constructor(), SpecVal::Object(array_ctor), false),
            spec_prop_data(spec_k_push(), SpecVal::Object(fn_arr_push), false),
            spec_prop_data(spec_k_pop(), SpecVal::Object(fn_arr_pop), false),
            spec_prop_data(spec_k_join(), SpecVal::Object(fn_arr_join), false),
            spec_prop_data(spec_k_to_string(), SpecVal::Object(fn_arr_join), false),
        ]);
    }
    heap.alloc_bootstrap(o2);

    let mut p3: Vec<PropEntry> = Vec::new();
    p3.push(make_prop_data(k_constructor(), Val::Object(error_ctor), false));
    p3.push(make_prop_data(k_name(), Val::Str(k_error()), false));
    p3.push(make_prop_data(k_message(), Val::Str(k_empty()), false));
    p3.push(make_prop_data(k_to_string(), Val::Object(fn_err_to_str), false));
    let o3 = HeapObject { realm, prototype: Some(object_proto), extensible: true, kind: ObjectKind::Ordinary, props: p3 };
    proof {
        assert(o3@.props =~= seq![
            spec_prop_data(spec_k_constructor(), SpecVal::Object(error_ctor), false),
            spec_prop_data(spec_k_name(), SpecVal::Str(spec_k_error()), false),
            spec_prop_data(spec_k_message(), SpecVal::Str(spec_k_empty()), false),
            spec_prop_data(spec_k_to_string(), SpecVal::Object(fn_err_to_str), false),
        ]);
    }
    heap.alloc_bootstrap(o3);

    let mut p4: Vec<PropEntry> = Vec::new();
    p4.push(make_prop_data(k_constructor(), Val::Object(ref_error_ctor), false));
    p4.push(make_prop_data(k_name(), Val::Str(k_ref_error()), false));
    p4.push(make_prop_data(k_message(), Val::Str(k_empty()), false));
    let o4 = HeapObject { realm, prototype: Some(error_proto), extensible: true, kind: ObjectKind::Ordinary, props: p4 };
    proof { assert(o4@.props =~= seq![spec_prop_data(spec_k_constructor(), SpecVal::Object(ref_error_ctor), false), spec_prop_data(spec_k_name(), SpecVal::Str(spec_k_ref_error()), false), spec_prop_data(spec_k_message(), SpecVal::Str(spec_k_empty()), false)]); }
    heap.alloc_bootstrap(o4);

    let mut p5: Vec<PropEntry> = Vec::new();
    p5.push(make_prop_data(k_constructor(), Val::Object(type_error_ctor), false));
    p5.push(make_prop_data(k_name(), Val::Str(k_type_error()), false));
    p5.push(make_prop_data(k_message(), Val::Str(k_empty()), false));
    let o5 = HeapObject { realm, prototype: Some(error_proto), extensible: true, kind: ObjectKind::Ordinary, props: p5 };
    proof { assert(o5@.props =~= seq![spec_prop_data(spec_k_constructor(), SpecVal::Object(type_error_ctor), false), spec_prop_data(spec_k_name(), SpecVal::Str(spec_k_type_error()), false), spec_prop_data(spec_k_message(), SpecVal::Str(spec_k_empty()), false)]); }
    heap.alloc_bootstrap(o5);

    let mut p6: Vec<PropEntry> = Vec::new();
    p6.push(make_prop_data(k_constructor(), Val::Object(syntax_error_ctor), false));
    p6.push(make_prop_data(k_name(), Val::Str(k_syntax_error()), false));
    p6.push(make_prop_data(k_message(), Val::Str(k_empty()), false));
    let o6 = HeapObject { realm, prototype: Some(error_proto), extensible: true, kind: ObjectKind::Ordinary, props: p6 };
    proof { assert(o6@.props =~= seq![spec_prop_data(spec_k_constructor(), SpecVal::Object(syntax_error_ctor), false), spec_prop_data(spec_k_name(), SpecVal::Str(spec_k_syntax_error()), false), spec_prop_data(spec_k_message(), SpecVal::Str(spec_k_empty()), false)]); }
    heap.alloc_bootstrap(o6);

    proof { assert(heap@.slots =~= spec_bootstrap_slots_a()); }
}

#[verifier::opaque]
pub open spec fn spec_bootstrap_slots_b() -> Seq<SpecSlot> {
    let realm = RealmId(1);
    let object_proto = ObjId(0);
    let function_proto = ObjId(1);
    let error_proto = ObjId(3);
    let ref_error_proto = ObjId(4);
    let type_error_proto = ObjId(5);
    let syntax_error_proto = ObjId(6);
    let range_error_proto = ObjId(7);
    let range_error_ctor = ObjId(12);
    let fn_obj_is = ObjId(25);
    let fn_obj_keys = ObjId(26);

    let s7 = SpecSlot::Live(SpecHeapObject {
        realm,
        prototype: Some(error_proto),
        extensible: true,
        kind: ObjectKind::Ordinary,
        props: seq![
            spec_prop_data(spec_k_constructor(), SpecVal::Object(range_error_ctor), false),
            spec_prop_data(spec_k_name(), SpecVal::Str(spec_k_range_error()), false),
            spec_prop_data(spec_k_message(), SpecVal::Str(spec_k_empty()), false),
        ],
    });
    let s8 = SpecSlot::Live(spec_mk_builtin_obj(realm, function_proto, BuiltinFn::ErrorCtor(ErrorKind::Error), Some(error_proto), spec_k_error()));
    let s9 = SpecSlot::Live(spec_mk_builtin_obj(realm, function_proto, BuiltinFn::ErrorCtor(ErrorKind::ReferenceError), Some(ref_error_proto), spec_k_ref_error()));
    let s10 = SpecSlot::Live(spec_mk_builtin_obj(realm, function_proto, BuiltinFn::ErrorCtor(ErrorKind::TypeError), Some(type_error_proto), spec_k_type_error()));
    let s11 = SpecSlot::Live(spec_mk_builtin_obj(realm, function_proto, BuiltinFn::ErrorCtor(ErrorKind::SyntaxError), Some(syntax_error_proto), spec_k_syntax_error()));
    let s12 = SpecSlot::Live(spec_mk_builtin_obj(realm, function_proto, BuiltinFn::ErrorCtor(ErrorKind::RangeError), Some(range_error_proto), spec_k_range_error()));
    let s13 = SpecSlot::Live(SpecHeapObject {
        realm,
        prototype: Some(function_proto),
        extensible: true,
        kind: ObjectKind::BuiltinFunction { builtin: BuiltinFn::ObjectCtor, prototype_obj: Some(object_proto) },
        props: seq![
            spec_prop_data(spec_k_name(), SpecVal::Str(spec_k_ctor_object()), false),
            spec_prop_data(spec_k_prototype(), SpecVal::Object(object_proto), false),
            spec_prop_data(spec_k_is(), SpecVal::Object(fn_obj_is), false),
            spec_prop_data(spec_k_keys(), SpecVal::Object(fn_obj_keys), false),
        ],
    });
    seq![s7, s8, s9, s10, s11, s12, s13]
}

fn bootstrap_slots_b(heap: &mut Heap)
    ensures
        final(heap)@.slots == old(heap)@.slots + spec_bootstrap_slots_b(),
        final(heap)@.realm_heap_quota == old(heap)@.realm_heap_quota,
{
    reveal(spec_bootstrap_slots_b);
    let ghost pre = old(heap)@.slots;
    let realm = RealmId(1);
    let object_proto = ObjId(0);
    let function_proto = ObjId(1);
    let error_proto = ObjId(3);
    let ref_error_proto = ObjId(4);
    let type_error_proto = ObjId(5);
    let syntax_error_proto = ObjId(6);
    let range_error_proto = ObjId(7);
    let range_error_ctor = ObjId(12);
    let fn_obj_is = ObjId(25);
    let fn_obj_keys = ObjId(26);

    let mut p7: Vec<PropEntry> = Vec::new();
    p7.push(make_prop_data(k_constructor(), Val::Object(range_error_ctor), false));
    p7.push(make_prop_data(k_name(), Val::Str(k_range_error()), false));
    p7.push(make_prop_data(k_message(), Val::Str(k_empty()), false));
    let o7 = HeapObject { realm, prototype: Some(error_proto), extensible: true, kind: ObjectKind::Ordinary, props: p7 };
    proof { assert(o7@.props =~= seq![spec_prop_data(spec_k_constructor(), SpecVal::Object(range_error_ctor), false), spec_prop_data(spec_k_name(), SpecVal::Str(spec_k_range_error()), false), spec_prop_data(spec_k_message(), SpecVal::Str(spec_k_empty()), false)]); }
    heap.alloc_bootstrap(o7);

    heap.alloc_bootstrap(mk_builtin_obj(realm, function_proto, BuiltinFn::ErrorCtor(ErrorKind::Error), Some(error_proto), k_error()));
    heap.alloc_bootstrap(mk_builtin_obj(realm, function_proto, BuiltinFn::ErrorCtor(ErrorKind::ReferenceError), Some(ref_error_proto), k_ref_error()));
    heap.alloc_bootstrap(mk_builtin_obj(realm, function_proto, BuiltinFn::ErrorCtor(ErrorKind::TypeError), Some(type_error_proto), k_type_error()));
    heap.alloc_bootstrap(mk_builtin_obj(realm, function_proto, BuiltinFn::ErrorCtor(ErrorKind::SyntaxError), Some(syntax_error_proto), k_syntax_error()));
    heap.alloc_bootstrap(mk_builtin_obj(realm, function_proto, BuiltinFn::ErrorCtor(ErrorKind::RangeError), Some(range_error_proto), k_range_error()));

    let mut p13: Vec<PropEntry> = Vec::new();
    p13.push(make_prop_data(k_name(), Val::Str(k_ctor_object()), false));
    p13.push(make_prop_data(k_prototype(), Val::Object(object_proto), false));
    p13.push(make_prop_data(k_is(), Val::Object(fn_obj_is), false));
    p13.push(make_prop_data(k_keys(), Val::Object(fn_obj_keys), false));
    let o13 = HeapObject { realm, prototype: Some(function_proto), extensible: true, kind: ObjectKind::BuiltinFunction { builtin: BuiltinFn::ObjectCtor, prototype_obj: Some(object_proto) }, props: p13 };
    proof {
        assert(o13@.props =~= seq![
            spec_prop_data(spec_k_name(), SpecVal::Str(spec_k_ctor_object()), false),
            spec_prop_data(spec_k_prototype(), SpecVal::Object(object_proto), false),
            spec_prop_data(spec_k_is(), SpecVal::Object(fn_obj_is), false),
            spec_prop_data(spec_k_keys(), SpecVal::Object(fn_obj_keys), false),
        ]);
    }
    heap.alloc_bootstrap(o13);
    proof { assert(heap@.slots =~= pre + spec_bootstrap_slots_b()); }
}

#[verifier::opaque]
pub open spec fn spec_bootstrap_slots_c() -> Seq<SpecSlot> {
    let realm = RealmId(1);
    let object_proto = ObjId(0);
    let function_proto = ObjId(1);
    let array_proto = ObjId(2);
    let fn_arr_is_array = ObjId(24);

    let s14 = SpecSlot::Live(SpecHeapObject {
        realm,
        prototype: Some(function_proto),
        extensible: true,
        kind: ObjectKind::BuiltinFunction { builtin: BuiltinFn::ArrayCtor, prototype_obj: Some(array_proto) },
        props: seq![
            spec_prop_data(spec_k_name(), SpecVal::Str(spec_k_ctor_array()), false),
            spec_prop_data(spec_k_prototype(), SpecVal::Object(array_proto), false),
            spec_prop_data(spec_k_is_array(), SpecVal::Object(fn_arr_is_array), false),
        ],
    });
    let s15 = SpecSlot::Live(spec_mk_builtin_obj(realm, function_proto, BuiltinFn::StringConv, Some(object_proto), spec_k_ctor_string()));
    let s16 = SpecSlot::Live(spec_mk_builtin_obj(realm, function_proto, BuiltinFn::NumberConv, Some(object_proto), spec_k_ctor_number()));
    let s17 = SpecSlot::Live(spec_mk_builtin_obj(realm, function_proto, BuiltinFn::BooleanConv, Some(object_proto), spec_k_ctor_boolean()));
    let s18 = SpecSlot::Live(spec_mk_builtin_obj(realm, function_proto, BuiltinFn::ObjectToString, None, spec_k_to_string()));
    let s19 = SpecSlot::Live(spec_mk_builtin_obj(realm, function_proto, BuiltinFn::ErrorToString, None, spec_k_to_string()));
    let s20 = SpecSlot::Live(spec_mk_builtin_obj(realm, function_proto, BuiltinFn::FunctionCall, None, spec_k_call()));
    seq![s14, s15, s16, s17, s18, s19, s20]
}

fn bootstrap_slots_c(heap: &mut Heap)
    ensures
        final(heap)@.slots == old(heap)@.slots + spec_bootstrap_slots_c(),
        final(heap)@.realm_heap_quota == old(heap)@.realm_heap_quota,
{
    reveal(spec_bootstrap_slots_c);
    let ghost pre = old(heap)@.slots;
    let realm = RealmId(1);
    let object_proto = ObjId(0);
    let function_proto = ObjId(1);
    let array_proto = ObjId(2);
    let fn_arr_is_array = ObjId(24);

    let mut p14: Vec<PropEntry> = Vec::new();
    p14.push(make_prop_data(k_name(), Val::Str(k_ctor_array()), false));
    p14.push(make_prop_data(k_prototype(), Val::Object(array_proto), false));
    p14.push(make_prop_data(k_is_array(), Val::Object(fn_arr_is_array), false));
    let o14 = HeapObject { realm, prototype: Some(function_proto), extensible: true, kind: ObjectKind::BuiltinFunction { builtin: BuiltinFn::ArrayCtor, prototype_obj: Some(array_proto) }, props: p14 };
    proof {
        assert(o14@.props =~= seq![
            spec_prop_data(spec_k_name(), SpecVal::Str(spec_k_ctor_array()), false),
            spec_prop_data(spec_k_prototype(), SpecVal::Object(array_proto), false),
            spec_prop_data(spec_k_is_array(), SpecVal::Object(fn_arr_is_array), false),
        ]);
    }
    heap.alloc_bootstrap(o14);

    heap.alloc_bootstrap(mk_builtin_obj(realm, function_proto, BuiltinFn::StringConv, Some(object_proto), k_ctor_string()));
    heap.alloc_bootstrap(mk_builtin_obj(realm, function_proto, BuiltinFn::NumberConv, Some(object_proto), k_ctor_number()));
    heap.alloc_bootstrap(mk_builtin_obj(realm, function_proto, BuiltinFn::BooleanConv, Some(object_proto), k_ctor_boolean()));
    heap.alloc_bootstrap(mk_builtin_obj(realm, function_proto, BuiltinFn::ObjectToString, None, k_to_string()));
    heap.alloc_bootstrap(mk_builtin_obj(realm, function_proto, BuiltinFn::ErrorToString, None, k_to_string()));
    heap.alloc_bootstrap(mk_builtin_obj(realm, function_proto, BuiltinFn::FunctionCall, None, k_call()));
    proof { assert(heap@.slots =~= pre + spec_bootstrap_slots_c()); }
}

#[verifier::opaque]
pub open spec fn spec_global_props_a() -> Seq<SpecPropEntry> {
    let global_obj = ObjId(28);
    seq![
        SpecPropEntry { key: spec_k_undefined(), value: SpecVal::Undefined, writable: false, enumerable: false, configurable: false },
        SpecPropEntry { key: spec_k_nan(), value: SpecVal::Number(JsNum(NAN_BITS)), writable: false, enumerable: false, configurable: false },
        SpecPropEntry { key: spec_k_infinity(), value: SpecVal::Number(JsNum(POS_INF_BITS)), writable: false, enumerable: false, configurable: false },
        spec_prop_data(spec_k_global_this(), SpecVal::Object(global_obj), false),
        spec_prop_data(spec_k_error(), SpecVal::Object(ObjId(8)), false),
        spec_prop_data(spec_k_ref_error(), SpecVal::Object(ObjId(9)), false),
        spec_prop_data(spec_k_type_error(), SpecVal::Object(ObjId(10)), false),
    ]
}

fn push_global_props_a(ps: &mut Vec<PropEntry>)
    requires old(ps)@.len() == 0,
    ensures spec_props_view(final(ps)@) == spec_global_props_a(),
{
    reveal(spec_global_props_a);
    let global_obj = ObjId(28);
    ps.push(PropEntry { key: k_undefined(), value: Val::Undefined, writable: false, enumerable: false, configurable: false });
    ps.push(PropEntry { key: k_nan(), value: Val::Number(JsNum(NAN_BITS)), writable: false, enumerable: false, configurable: false });
    ps.push(PropEntry { key: k_infinity(), value: Val::Number(JsNum(POS_INF_BITS)), writable: false, enumerable: false, configurable: false });
    ps.push(make_prop_data(k_global_this(), Val::Object(global_obj), false));
    ps.push(make_prop_data(k_error(), Val::Object(ObjId(8)), false));
    ps.push(make_prop_data(k_ref_error(), Val::Object(ObjId(9)), false));
    ps.push(make_prop_data(k_type_error(), Val::Object(ObjId(10)), false));
    proof { assert(spec_props_view(ps@) =~= spec_global_props_a()); }
}

#[verifier::opaque]
pub open spec fn spec_global_props_b() -> Seq<SpecPropEntry> {
    seq![
        spec_prop_data(spec_k_syntax_error(), SpecVal::Object(ObjId(11)), false),
        spec_prop_data(spec_k_range_error(), SpecVal::Object(ObjId(12)), false),
        spec_prop_data(spec_k_ctor_object(), SpecVal::Object(ObjId(13)), false),
        spec_prop_data(spec_k_ctor_array(), SpecVal::Object(ObjId(14)), false),
        spec_prop_data(spec_k_ctor_string(), SpecVal::Object(ObjId(15)), false),
        spec_prop_data(spec_k_ctor_number(), SpecVal::Object(ObjId(16)), false),
        spec_prop_data(spec_k_ctor_boolean(), SpecVal::Object(ObjId(17)), false),
    ]
}

fn push_global_props_b(ps: &mut Vec<PropEntry>)
    ensures spec_props_view(final(ps)@) == spec_props_view(old(ps)@) + spec_global_props_b(),
{
    reveal(spec_global_props_b);
    let ghost pre = spec_props_view(old(ps)@);
    ps.push(make_prop_data(k_syntax_error(), Val::Object(ObjId(11)), false));
    ps.push(make_prop_data(k_range_error(), Val::Object(ObjId(12)), false));
    ps.push(make_prop_data(k_ctor_object(), Val::Object(ObjId(13)), false));
    ps.push(make_prop_data(k_ctor_array(), Val::Object(ObjId(14)), false));
    ps.push(make_prop_data(k_ctor_string(), Val::Object(ObjId(15)), false));
    ps.push(make_prop_data(k_ctor_number(), Val::Object(ObjId(16)), false));
    ps.push(make_prop_data(k_ctor_boolean(), Val::Object(ObjId(17)), false));
    proof { assert(spec_props_view(ps@) =~= pre + spec_global_props_b()); }
}

#[verifier::opaque]
pub open spec fn spec_bootstrap_slots_d() -> Seq<SpecSlot> {
    let realm = RealmId(1);
    let object_proto = ObjId(0);
    let function_proto = ObjId(1);

    let s21 = SpecSlot::Live(spec_mk_builtin_obj(realm, function_proto, BuiltinFn::ArrayPush, None, spec_k_push()));
    let s22 = SpecSlot::Live(spec_mk_builtin_obj(realm, function_proto, BuiltinFn::ArrayPop, None, spec_k_pop()));
    let s23 = SpecSlot::Live(spec_mk_builtin_obj(realm, function_proto, BuiltinFn::ArrayJoin, None, spec_k_join()));
    let s24 = SpecSlot::Live(spec_mk_builtin_obj(realm, function_proto, BuiltinFn::ArrayIsArray, None, spec_k_is_array()));
    let s25 = SpecSlot::Live(spec_mk_builtin_obj(realm, function_proto, BuiltinFn::ObjectIs, None, spec_k_is()));
    let s26 = SpecSlot::Live(spec_mk_builtin_obj(realm, function_proto, BuiltinFn::ObjectKeys, None, spec_k_keys()));
    let s27 = SpecSlot::Live(spec_mk_builtin_obj(realm, function_proto, BuiltinFn::ObjectHasOwnProperty, None, spec_k_has_own()));
    let s28 = SpecSlot::Live(SpecHeapObject {
        realm,
        prototype: Some(object_proto),
        extensible: true,
        kind: ObjectKind::Ordinary,
        props: spec_global_props_a() + spec_global_props_b(),
    });
    seq![s21, s22, s23, s24, s25, s26, s27, s28]
}

fn bootstrap_slots_d(heap: &mut Heap)
    ensures
        final(heap)@.slots == old(heap)@.slots + spec_bootstrap_slots_d(),
        final(heap)@.realm_heap_quota == old(heap)@.realm_heap_quota,
{
    reveal(spec_bootstrap_slots_d);
    let ghost pre = old(heap)@.slots;
    let realm = RealmId(1);
    let object_proto = ObjId(0);
    let function_proto = ObjId(1);

    heap.alloc_bootstrap(mk_builtin_obj(realm, function_proto, BuiltinFn::ArrayPush, None, k_push()));
    heap.alloc_bootstrap(mk_builtin_obj(realm, function_proto, BuiltinFn::ArrayPop, None, k_pop()));
    heap.alloc_bootstrap(mk_builtin_obj(realm, function_proto, BuiltinFn::ArrayJoin, None, k_join()));
    heap.alloc_bootstrap(mk_builtin_obj(realm, function_proto, BuiltinFn::ArrayIsArray, None, k_is_array()));
    heap.alloc_bootstrap(mk_builtin_obj(realm, function_proto, BuiltinFn::ObjectIs, None, k_is()));
    heap.alloc_bootstrap(mk_builtin_obj(realm, function_proto, BuiltinFn::ObjectKeys, None, k_keys()));
    heap.alloc_bootstrap(mk_builtin_obj(realm, function_proto, BuiltinFn::ObjectHasOwnProperty, None, k_has_own()));
    let mut gps: Vec<PropEntry> = Vec::new();
    push_global_props_a(&mut gps);
    push_global_props_b(&mut gps);
    let o28 = HeapObject { realm, prototype: Some(object_proto), extensible: true, kind: ObjectKind::Ordinary, props: gps };
    heap.alloc_bootstrap(o28);
    proof { assert(heap@.slots =~= pre + spec_bootstrap_slots_d()); }
}

pub open spec fn spec_bootstrap_realm(fuel: nat, user_heap_quota: nat) -> SpecState {
    let global_obj = ObjId(28);
    let slots = spec_bootstrap_slots_a()
        + spec_bootstrap_slots_b()
        + spec_bootstrap_slots_c()
        + spec_bootstrap_slots_d();
    let eff_quota: nat = if user_heap_quota > (usize::MAX - 29usize) as nat {
        usize::MAX as nat
    } else {
        (29nat + user_heap_quota) as nat
    };
    let heap = SpecHeap { slots, realm_heap_quota: eff_quota };
    let intr = RealmIntrinsics {
        realm: RealmId(1),
        global_obj,
        object_proto: ObjId(0),
        function_proto: ObjId(1),
        array_proto: ObjId(2),
        error_proto: ObjId(3),
        ref_error_proto: ObjId(4),
        type_error_proto: ObjId(5),
        syntax_error_proto: ObjId(6),
        range_error_proto: ObjId(7),
        error_ctor: ObjId(8),
        ref_error_ctor: ObjId(9),
        type_error_ctor: ObjId(10),
        syntax_error_ctor: ObjId(11),
        range_error_ctor: ObjId(12),
    };
    let envs = spec_new_global_env(SpecVal::Object(global_obj));
    SpecState {
        envs,
        heap,
        intr,
        current_env: EnvId(0),
        env_roots: seq![],
        strict: false,
        fuel,
        temp_roots: seq![],
    }
}

pub fn bootstrap_realm(fuel: usize, user_heap_quota: usize) -> (st: VmState)
    ensures
        st@ == spec_bootstrap_realm(fuel as nat, user_heap_quota as nat),
        env_wf(st@.envs),
        st.fuel == fuel,
{
    let global_obj = ObjId(28);
    let eff_quota = if user_heap_quota > usize::MAX - 29 {
        usize::MAX
    } else {
        29 + user_heap_quota
    };
    let mut heap = Heap::new(eff_quota);
    bootstrap_slots_a(&mut heap);
    bootstrap_slots_b(&mut heap);
    bootstrap_slots_c(&mut heap);
    bootstrap_slots_d(&mut heap);

    let intr = RealmIntrinsics {
        realm: RealmId(1),
        global_obj,
        object_proto: ObjId(0),
        function_proto: ObjId(1),
        array_proto: ObjId(2),
        error_proto: ObjId(3),
        ref_error_proto: ObjId(4),
        type_error_proto: ObjId(5),
        syntax_error_proto: ObjId(6),
        range_error_proto: ObjId(7),
        error_ctor: ObjId(8),
        ref_error_ctor: ObjId(9),
        type_error_ctor: ObjId(10),
        syntax_error_ctor: ObjId(11),
        range_error_ctor: ObjId(12),
    };
    let envs = EnvArena::new_global(Val::Object(global_obj));
    let st = VmState {
        envs,
        heap,
        intr,
        current_env: EnvId(0),
        env_roots: Vec::new(),
        strict: false,
        fuel,
        temp_roots: Vec::new(),
    };
    proof {
        assert(st@.env_roots =~= seq![]);
        assert(st@.temp_roots =~= seq![]);
    }
    st
}

// ---------------------------------------------------------------------------
// Stack-Disciplined Temporary Root Management & Fuel Cap Helper
// ---------------------------------------------------------------------------

pub open spec fn spec_push_root(st: SpecState, v: SpecVal) -> SpecState {
    SpecState { temp_roots: st.temp_roots.push(v), ..st }
}

pub open spec fn spec_pop_root(st: SpecState) -> SpecState {
    if st.temp_roots.len() == 0 {
        st
    } else {
        SpecState { temp_roots: st.temp_roots.drop_last(), ..st }
    }
}

pub open spec fn spec_truncate_roots(st: SpecState, target_len: nat) -> SpecState {
    if target_len >= st.temp_roots.len() {
        st
    } else {
        SpecState { temp_roots: st.temp_roots.subrange(0, target_len as int), ..st }
    }
}

pub open spec fn spec_push_env_root(st: SpecState, eid: EnvId) -> SpecState {
    SpecState { env_roots: st.env_roots.push(eid), ..st }
}

pub open spec fn spec_truncate_env_roots(st: SpecState, target_len: nat) -> SpecState {
    if target_len >= st.env_roots.len() {
        st
    } else {
        SpecState { env_roots: st.env_roots.subrange(0, target_len as int), ..st }
    }
}

pub open spec fn spec_state_alloc_obj(st: SpecState, obj: SpecHeapObject) -> (SpecState, AllocRes) {
    let (h2, e2, ares) = spec_alloc_with_gc(
        st.heap,
        st.envs,
        st.current_env,
        st.env_roots,
        st.intr,
        st.temp_roots,
        obj,
    );
    (SpecState { heap: h2, envs: e2, ..st }, ares)
}

pub open spec fn spec_cap_fuel(st: SpecState, bound: nat) -> SpecState {
    if st.fuel <= bound {
        st
    } else {
        SpecState { fuel: bound, ..st }
    }
}

impl VmState {
    pub fn push_env_root(&mut self, eid: EnvId)
        ensures
            final(self)@ == spec_push_env_root(old(self)@, eid),
            final(self).fuel == old(self).fuel,
    {
        self.env_roots.push(eid);
    }

    pub fn truncate_env_roots(&mut self, target_len: usize)
        ensures
            final(self)@ == spec_truncate_env_roots(old(self)@, target_len as nat),
            final(self).fuel == old(self).fuel,
    {
        if target_len >= self.env_roots.len() {
            return;
        }
        let ghost orig = old(self).env_roots@;
        while self.env_roots.len() > target_len
            invariant
                target_len <= self.env_roots@.len() <= orig.len(),
                self.env_roots@ =~= orig.subrange(0, self.env_roots@.len() as int),
                self.envs@ == old(self).envs@,
                self.heap@ == old(self).heap@,
                self.intr == old(self).intr,
                self.current_env == old(self).current_env,
                self.strict == old(self).strict,
                self.fuel == old(self).fuel,
                self.temp_roots@ == old(self).temp_roots@,
            decreases self.env_roots@.len() - target_len,
        {
            let ghost cur_len = self.env_roots@.len() as int;
            let _ = self.env_roots.pop();
            proof {
                assert(orig.subrange(0, cur_len).drop_last() =~= orig.subrange(0, cur_len - 1));
            }
        }
    }

    pub fn push_root(&mut self, v: &Val)
        ensures
            final(self)@ == spec_push_root(old(self)@, v@),
            final(self).fuel == old(self).fuel,
    {
        let ghost pre = spec_vals_view(self.temp_roots@);
        let cv = clone_val(v);
        self.temp_roots.push(cv);
        proof { assert(spec_vals_view(self.temp_roots@) =~= pre.push(v@)); }
    }

    pub fn pop_root(&mut self)
        ensures
            final(self)@ == spec_pop_root(old(self)@),
            final(self).fuel == old(self).fuel,
    {
        if self.temp_roots.len() > 0 {
            let ghost pre = spec_vals_view(self.temp_roots@);
            let _ = self.temp_roots.pop();
            proof { assert(spec_vals_view(self.temp_roots@) =~= pre.drop_last()); }
        }
    }

    pub fn truncate_roots(&mut self, target_len: usize)
        ensures
            final(self)@ == spec_truncate_roots(old(self)@, target_len as nat),
            final(self).fuel == old(self).fuel,
    {
        if target_len >= self.temp_roots.len() {
            return;
        }
        let ghost orig = spec_vals_view(old(self).temp_roots@);
        while self.temp_roots.len() > target_len
            invariant
                target_len <= self.temp_roots@.len() <= orig.len(),
                spec_vals_view(self.temp_roots@) =~= orig.subrange(0, self.temp_roots@.len() as int),
                self.envs@ == old(self).envs@,
                self.heap@ == old(self).heap@,
                self.intr == old(self).intr,
                self.current_env == old(self).current_env,
                self.env_roots@ == old(self).env_roots@,
                self.strict == old(self).strict,
                self.fuel == old(self).fuel,
            decreases self.temp_roots@.len() - target_len,
        {
            let ghost cur_len = self.temp_roots@.len() as int;
            let _ = self.temp_roots.pop();
            proof {
                assert(orig.subrange(0, cur_len).drop_last() =~= orig.subrange(0, cur_len - 1));
                assert(spec_vals_view(self.temp_roots@) =~= orig.subrange(0, cur_len - 1));
            }
        }
    }

    pub fn alloc_obj(&mut self, obj: HeapObject) -> (res: AllocRes)
        ensures
            (final(self)@, res) == spec_state_alloc_obj(old(self)@, obj@),
            final(self).fuel == old(self).fuel,
            env_wf(old(self)@.envs) ==> env_wf(final(self)@.envs),
    {
        self.heap.alloc_with_gc(
            &mut self.envs,
            self.current_env,
            &self.env_roots,
            &self.intr,
            &self.temp_roots,
            obj,
        )
    }
}

// ---------------------------------------------------------------------------
// Error Construction, Closure Allocation, `typeof`, Property & Identifier Ops
// ---------------------------------------------------------------------------

#[verifier::opaque]
pub open spec fn spec_throw_error(
    st: SpecState,
    kind: ErrorKind,
    msg: Seq<u16>,
) -> (SpecState, SpecExprStep) {
    let proto = spec_error_proto_for(st.intr, kind);
    let obj = SpecHeapObject {
        realm: st.intr.realm,
        prototype: Some(proto),
        extensible: true,
        kind: ObjectKind::Error { kind },
        props: seq![spec_prop_data(spec_k_message(), SpecVal::Str(msg), false)],
    };
    let (st2, ares) = spec_state_alloc_obj(st, obj);
    match ares {
        AllocRes::Ok(oid) => (st2, SpecExprStep::Throw(SpecVal::Object(oid))),
        AllocRes::QuotaExceeded => (st2, SpecExprStep::HeapQuotaExceeded),
    }
}

pub fn throw_error_exec(
    st: &mut VmState,
    kind: ErrorKind,
    msg: JsStr,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_throw_error(old(st)@, kind, msg@),
        final(st).fuel == old(st).fuel,
        !(res@ is OutOfFuel),
        !(res@ is Val),
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
{
    reveal(spec_throw_error);
    let proto = error_proto_for(&st.intr, kind);
    let ghost smsg = msg@;
    let mut props: Vec<PropEntry> = Vec::new();
    props.push(make_prop_data(k_message(), Val::Str(msg), false));
    let obj = HeapObject {
        realm: st.intr.realm,
        prototype: Some(proto),
        extensible: true,
        kind: ObjectKind::Error { kind },
        props,
    };
    proof {
        assert(obj@.props =~= seq![spec_prop_data(spec_k_message(), SpecVal::Str(smsg), false)]);
    }
    let ares = st.alloc_obj(obj);
    match ares {
        AllocRes::Ok(oid) => ExprStep::Throw(Val::Object(oid)),
        AllocRes::QuotaExceeded => ExprStep::HeapQuotaExceeded,
    }
}

pub open spec fn spec_is_callable(heap: SpecHeap, realm: RealmId, v: SpecVal) -> bool {
    match v {
        SpecVal::Object(oid) => {
            if (oid.0 as int) >= heap.slots.len() {
                false
            } else {
                match heap.slots[oid.0 as int] {
                    SpecSlot::Live(obj) => obj.realm == realm
                        && ((obj.kind is Function) || (obj.kind is BuiltinFunction)),
                    SpecSlot::Free => false,
                }
            }
        }
        _ => false,
    }
}

pub fn is_callable_exec(heap: &Heap, realm: RealmId, v: &Val) -> (r: bool)
    ensures r == spec_is_callable(heap@, realm, v@),
{
    match v {
        Val::Object(oid) => {
            if oid.0 >= heap.slots.len() {
                false
            } else {
                proof { assert(heap@.slots[oid.0 as int] == heap.slots@[oid.0 as int]@); }
                match &heap.slots[oid.0] {
                    Slot::Live(obj) => obj.realm.0 == realm.0
                        && (matches!(obj.kind, ObjectKind::Function { .. })
                            || matches!(obj.kind, ObjectKind::BuiltinFunction { .. })),
                    Slot::Free => false,
                }
            }
        }
        _ => false,
    }
}

/// §13.5.3 The `typeof` Operator
pub open spec fn spec_typeof_val(heap: SpecHeap, realm: RealmId, v: SpecVal) -> Seq<u16> {
    match v {
        SpecVal::Undefined => spec_k_undefined(),
        SpecVal::Null => spec_t_object(),
        SpecVal::Bool(_) => spec_t_boolean(),
        SpecVal::Number(_) => spec_t_number(),
        SpecVal::Str(_) => spec_t_string(),
        SpecVal::Object(_) => if spec_is_callable(heap, realm, v) {
            spec_t_function()
        } else {
            spec_t_object()
        },
    }
}

pub fn typeof_val_exec(heap: &Heap, realm: RealmId, v: &Val) -> (r: JsStr)
    ensures r@ == spec_typeof_val(heap@, realm, v@),
{
    match v {
        Val::Undefined => k_undefined(),
        Val::Null => t_object(),
        Val::Bool(_) => t_boolean(),
        Val::Number(_) => t_number(),
        Val::Str(_) => t_string(),
        Val::Object(_) => if is_callable_exec(heap, realm, v) {
            t_function()
        } else {
            t_object()
        },
    }
}

#[verifier::opaque]
pub open spec fn spec_alloc_closure(
    prog: SpecProgram,
    func_id: FuncId,
    env: EnvId,
    st: SpecState,
) -> (SpecState, SpecExprStep) {
    if (func_id.0 as int) >= prog.funcs.len() {
        (st, SpecExprStep::Unsupported(UnsupportedFeature::InvalidAstReference))
    } else {
        let f = prog.funcs[func_id.0 as int];
        let fn_strict = st.strict || f.strict;
        let fname = match f.name {
            Some(nm) => nm,
            None => spec_k_empty(),
        };
        if f.is_arrow {
            let fn_obj = SpecHeapObject {
                realm: st.intr.realm,
                prototype: Some(st.intr.function_proto),
                extensible: true,
                kind: ObjectKind::Function {
                    func_id,
                    env,
                    is_strict: fn_strict,
                    is_arrow: true,
                    prototype_obj: None,
                },
                props: seq![
                    spec_prop_data(spec_k_name(), SpecVal::Str(fname), false),
                    spec_prop_data(spec_k_length(), SpecVal::Number(spec_num_from_usize(f.params.len() as usize)), false),
                ],
            };
            let (st2, ares) = spec_state_alloc_obj(st, fn_obj);
            match ares {
                AllocRes::Ok(oid) => (st2, SpecExprStep::Val(SpecVal::Object(oid))),
                AllocRes::QuotaExceeded => (st2, SpecExprStep::HeapQuotaExceeded),
            }
        } else {
            let proto_obj = SpecHeapObject {
                realm: st.intr.realm,
                prototype: Some(st.intr.object_proto),
                extensible: true,
                kind: ObjectKind::Ordinary,
                props: seq![spec_prop_data(spec_k_constructor(), SpecVal::Undefined, false)],
            };
            let (st1, ares1) = spec_state_alloc_obj(st, proto_obj);
            match ares1 {
                AllocRes::QuotaExceeded => (st1, SpecExprStep::HeapQuotaExceeded),
                AllocRes::Ok(proto_oid) => {
                    let st_r = spec_push_root(st1, SpecVal::Object(proto_oid));
                    let fn_obj = SpecHeapObject {
                        realm: st_r.intr.realm,
                        prototype: Some(st_r.intr.function_proto),
                        extensible: true,
                        kind: ObjectKind::Function {
                            func_id,
                            env,
                            is_strict: fn_strict,
                            is_arrow: false,
                            prototype_obj: Some(proto_oid),
                        },
                        props: seq![
                            spec_prop_data(spec_k_name(), SpecVal::Str(fname), false),
                            spec_prop_data(spec_k_length(), SpecVal::Number(spec_num_from_usize(f.params.len() as usize)), false),
                            spec_prop_data(spec_k_prototype(), SpecVal::Object(proto_oid), false),
                        ],
                    };
                    let (st_alloc, ares2) = spec_state_alloc_obj(st_r, fn_obj);
                    let st2 = spec_pop_root(st_alloc);
                    match ares2 {
                        AllocRes::QuotaExceeded => (st2, SpecExprStep::HeapQuotaExceeded),
                        AllocRes::Ok(fn_oid) => {
                            let (h3, _) = spec_heap_set_prop(
                                st2.heap,
                                st2.intr.realm,
                                proto_oid,
                                spec_k_constructor(),
                                SpecVal::Object(fn_oid),
                            );
                            (SpecState { heap: h3, ..st2 }, SpecExprStep::Val(SpecVal::Object(fn_oid)))
                        }
                    }
                }
            }
        }
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(25)]
pub fn alloc_closure_exec(
    prog: &Program,
    func_id: FuncId,
    env: EnvId,
    st: &mut VmState,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_alloc_closure(prog@, func_id, env, old(st)@),
        final(st).fuel == old(st).fuel,
        !(res@ is OutOfFuel),
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
{
    reveal(spec_alloc_closure);
    if func_id.0 >= prog.funcs.len() {
        return ExprStep::Unsupported(UnsupportedFeature::InvalidAstReference);
    }
    proof { assert(prog@.funcs[func_id.0 as int] == prog.funcs@[func_id.0 as int]@); }
    let f = &prog.funcs[func_id.0];
    let fn_strict = st.strict || f.strict;
    let fname = match &f.name {
        Some(nm) => clone_js_str(nm),
        None => k_empty(),
    };
    let plen = f.params.len();
    if f.is_arrow {
        let ghost sfname = fname@;
        let mut props: Vec<PropEntry> = Vec::new();
        props.push(make_prop_data(k_name(), Val::Str(fname), false));
        props.push(make_prop_data(k_length(), Val::Number(num_from_usize(plen)), false));
        let fn_obj = HeapObject {
            realm: st.intr.realm,
            prototype: Some(st.intr.function_proto),
            extensible: true,
            kind: ObjectKind::Function {
                func_id,
                env,
                is_strict: fn_strict,
                is_arrow: true,
                prototype_obj: None,
            },
            props,
        };
        proof {
            assert(fn_obj@.props =~= seq![
                spec_prop_data(spec_k_name(), SpecVal::Str(sfname), false),
                spec_prop_data(spec_k_length(), SpecVal::Number(spec_num_from_usize(plen)), false),
            ]);
        }
        match st.alloc_obj(fn_obj) {
            AllocRes::Ok(oid) => ExprStep::Val(Val::Object(oid)),
            AllocRes::QuotaExceeded => ExprStep::HeapQuotaExceeded,
        }
    } else {
        let mut p_props: Vec<PropEntry> = Vec::new();
        p_props.push(make_prop_data(k_constructor(), Val::Undefined, false));
        let proto_obj = HeapObject {
            realm: st.intr.realm,
            prototype: Some(st.intr.object_proto),
            extensible: true,
            kind: ObjectKind::Ordinary,
            props: p_props,
        };
        proof {
            assert(proto_obj@.props =~= seq![
                spec_prop_data(spec_k_constructor(), SpecVal::Undefined, false),
            ]);
        }
        match st.alloc_obj(proto_obj) {
            AllocRes::QuotaExceeded => ExprStep::HeapQuotaExceeded,
            AllocRes::Ok(proto_oid) => {
                let pv = Val::Object(proto_oid);
                st.push_root(&pv);
                let ghost sfname = fname@;
                let mut props: Vec<PropEntry> = Vec::new();
                props.push(make_prop_data(k_name(), Val::Str(fname), false));
                props.push(make_prop_data(k_length(), Val::Number(num_from_usize(plen)), false));
                props.push(make_prop_data(k_prototype(), Val::Object(proto_oid), false));
                let fn_obj = HeapObject {
                    realm: st.intr.realm,
                    prototype: Some(st.intr.function_proto),
                    extensible: true,
                    kind: ObjectKind::Function {
                        func_id,
                        env,
                        is_strict: fn_strict,
                        is_arrow: false,
                        prototype_obj: Some(proto_oid),
                    },
                    props,
                };
                proof {
                    assert(fn_obj@.props =~= seq![
                        spec_prop_data(spec_k_name(), SpecVal::Str(sfname), false),
                        spec_prop_data(spec_k_length(), SpecVal::Number(spec_num_from_usize(plen)), false),
                        spec_prop_data(spec_k_prototype(), SpecVal::Object(proto_oid), false),
                    ]);
                }
                let ares2 = st.alloc_obj(fn_obj);
                st.pop_root();
                match ares2 {
                    AllocRes::QuotaExceeded => ExprStep::HeapQuotaExceeded,
                    AllocRes::Ok(fn_oid) => {
                        let _ = st.heap.set_prop(
                            st.intr.realm,
                            proto_oid,
                            k_constructor(),
                            Val::Object(fn_oid),
                        );
                        ExprStep::Val(Val::Object(fn_oid))
                    }
                }
            }
        }
    }
}

/// Property read supporting Objects + auto-boxed String `.length` and `str[idx]` +
/// `TypeError` on `Undefined`/`Null` (§6.2.5.5 / §7.1.18).
#[verifier::opaque]
pub open spec fn spec_get_property_val_body(
    st: SpecState,
    base: SpecVal,
    key: Seq<u16>,
) -> (SpecState, SpecExprStep) {
    match base {
        SpecVal::Undefined | SpecVal::Null =>
            spec_throw_error(st, ErrorKind::TypeError, spec_k_empty()),
        SpecVal::Object(oid) => {
            match spec_heap_get_prop(st.heap, st.intr.realm, oid, key) {
                SpecHeapReadVal::Ok(v) => (st, SpecExprStep::Val(v)),
                SpecHeapReadVal::InvalidObject | SpecHeapReadVal::CrossRealmAccess =>
                    spec_throw_error(st, ErrorKind::TypeError, spec_k_empty()),
            }
        }
        SpecVal::Str(s) => {
            if key == spec_k_length() {
                (st, SpecExprStep::Val(SpecVal::Number(spec_num_from_usize(s.len() as usize))))
            } else {
                match spec_parse_array_index(key) {
                    Some(idx) => if (idx as int) < s.len() {
                        (st, SpecExprStep::Val(SpecVal::Str(seq![s[idx as int]])))
                    } else {
                        (st, SpecExprStep::Val(SpecVal::Undefined))
                    },
                    None => (st, SpecExprStep::Val(SpecVal::Undefined)),
                }
            }
        }
        _ => (st, SpecExprStep::Val(SpecVal::Undefined)),
    }
}

pub open spec fn spec_get_property_val(
    st: SpecState,
    base: SpecVal,
    key: Seq<u16>,
) -> (SpecState, SpecExprStep) {
    let (st2, r) = spec_get_property_val_body(st, base, key);
    (SpecState { fuel: st.fuel, ..st2 }, r)
}

pub fn get_property_val_exec(
    st: &mut VmState,
    base: &Val,
    key: &JsStr,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_get_property_val(old(st)@, base@, key@),
        final(st).fuel == old(st).fuel,
        !(res@ is OutOfFuel),
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
{
    reveal(spec_get_property_val_body);
    match base {
        Val::Undefined | Val::Null =>
            throw_error_exec(st, ErrorKind::TypeError, k_empty()),
        Val::Object(oid) => {
            match st.heap.get_prop(st.intr.realm, *oid, key) {
                HeapReadVal::Ok(v) => ExprStep::Val(v),
                HeapReadVal::InvalidObject | HeapReadVal::CrossRealmAccess =>
                    throw_error_exec(st, ErrorKind::TypeError, k_empty()),
            }
        }
        Val::Str(s) => {
            let lk = k_length();
            if js_str_eq(key, &lk) {
                ExprStep::Val(Val::Number(num_from_usize(s.0.len())))
            } else {
                match parse_array_index(key) {
                    Some(idx) => if idx < s.0.len() {
                        let mut one: Vec<u16> = Vec::new();
                        one.push(s.0[idx]);
                        proof { assert(one@ =~= seq![s@[idx as int]]); }
                        ExprStep::Val(Val::Str(JsStr(one)))
                    } else {
                        ExprStep::Val(Val::Undefined)
                    },
                    None => ExprStep::Val(Val::Undefined),
                }
            }
        }
        _ => ExprStep::Val(Val::Undefined),
    }
}

/// Property write enforcing `TypeError` on `Null`/`Undefined`, CrossRealm rejection,
/// and strict-mode `TypeError` when writing to non-writable / non-extensible properties!
#[verifier::opaque]
pub open spec fn spec_set_property_val_body(
    st: SpecState,
    base: SpecVal,
    key: Seq<u16>,
    val: SpecVal,
) -> (SpecState, SpecExprStep) {
    match base {
        SpecVal::Undefined | SpecVal::Null =>
            spec_throw_error(st, ErrorKind::TypeError, spec_k_empty()),
        SpecVal::Object(oid) => {
            let (h2, wres) = spec_heap_set_prop(st.heap, st.intr.realm, oid, key, val);
            let st2 = SpecState { heap: h2, ..st };
            match wres {
                HeapWriteRes::Ok(ok) => {
                    if !ok && st2.strict {
                        spec_throw_error(st2, ErrorKind::TypeError, spec_k_empty())
                    } else {
                        (st2, SpecExprStep::Val(val))
                    }
                }
                HeapWriteRes::InvalidObject | HeapWriteRes::CrossRealmAccess =>
                    spec_throw_error(st2, ErrorKind::TypeError, spec_k_empty()),
            }
        }
        _ => {
            if st.strict {
                spec_throw_error(st, ErrorKind::TypeError, spec_k_empty())
            } else {
                (st, SpecExprStep::Val(val))
            }
        }
    }
}

pub open spec fn spec_set_property_val(
    st: SpecState,
    base: SpecVal,
    key: Seq<u16>,
    val: SpecVal,
) -> (SpecState, SpecExprStep) {
    let (st2, r) = spec_set_property_val_body(st, base, key, val);
    (SpecState { fuel: st.fuel, ..st2 }, r)
}

pub fn set_property_val_exec(
    st: &mut VmState,
    base: &Val,
    key: JsStr,
    val: Val,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_set_property_val(old(st)@, base@, key@, val@),
        final(st).fuel == old(st).fuel,
        !(res@ is OutOfFuel),
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
{
    reveal(spec_set_property_val_body);
    match base {
        Val::Undefined | Val::Null =>
            throw_error_exec(st, ErrorKind::TypeError, k_empty()),
        Val::Object(oid) => {
            let val_ret = clone_val(&val);
            let wres = st.heap.set_prop(st.intr.realm, *oid, key, val);
            match wres {
                HeapWriteRes::Ok(ok) => {
                    if !ok && st.strict {
                        throw_error_exec(st, ErrorKind::TypeError, k_empty())
                    } else {
                        ExprStep::Val(val_ret)
                    }
                }
                HeapWriteRes::InvalidObject | HeapWriteRes::CrossRealmAccess =>
                    throw_error_exec(st, ErrorKind::TypeError, k_empty()),
            }
        }
        _ => {
            if st.strict {
                throw_error_exec(st, ErrorKind::TypeError, k_empty())
            } else {
                ExprStep::Val(val)
            }
        }
    }
}

// ---------------------------------------------------------------------------
// ECMA-262 §9.1.1.4 Global + Lexical Identifier Resolution & Scope Hoisting
// ---------------------------------------------------------------------------

#[verifier::opaque]
pub open spec fn spec_eval_ident_get_body(st: SpecState, name: Seq<u16>) -> (SpecState, SpecExprStep) {
    match spec_get_identifier(st.envs, st.current_env, name) {
        SpecIdentLookup::Found(v) => (st, SpecExprStep::Val(v)),
        SpecIdentLookup::TdzUninitialized =>
            spec_throw_error(st, ErrorKind::ReferenceError, name),
        SpecIdentLookup::Undeclared => {
            match spec_heap_has_prop(st.heap, st.intr.realm, st.intr.global_obj, name) {
                HeapWriteRes::Ok(true) =>
                    spec_get_property_val(st, SpecVal::Object(st.intr.global_obj), name),
                _ => spec_throw_error(st, ErrorKind::ReferenceError, name),
            }
        }
    }
}

pub open spec fn spec_eval_ident_get(st: SpecState, name: Seq<u16>) -> (SpecState, SpecExprStep) {
    let (st2, r) = spec_eval_ident_get_body(st, name);
    (SpecState { fuel: st.fuel, ..st2 }, r)
}

pub fn eval_ident_get_exec(st: &mut VmState, name: &JsStr) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_eval_ident_get(old(st)@, name@),
        final(st).fuel == old(st).fuel,
        !(res@ is OutOfFuel),
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
{
    reveal(spec_eval_ident_get_body);
    match st.envs.get_identifier(st.current_env, name) {
        IdentLookup::Found(v) => ExprStep::Val(v),
        IdentLookup::TdzUninitialized =>
            throw_error_exec(st, ErrorKind::ReferenceError, clone_js_str(name)),
        IdentLookup::Undeclared => {
            match st.heap.has_prop(st.intr.realm, st.intr.global_obj, name) {
                HeapWriteRes::Ok(true) => {
                    let g = Val::Object(st.intr.global_obj);
                    get_property_val_exec(st, &g, name)
                }
                _ => throw_error_exec(st, ErrorKind::ReferenceError, clone_js_str(name)),
            }
        }
    }
}

#[verifier::opaque]
pub open spec fn spec_eval_typeof_ident(st: SpecState, name: Seq<u16>) -> (SpecState, SpecExprStep) {
    match spec_get_identifier(st.envs, st.current_env, name) {
        SpecIdentLookup::Found(v) =>
            (st, SpecExprStep::Val(SpecVal::Str(spec_typeof_val(st.heap, st.intr.realm, v)))),
        SpecIdentLookup::TdzUninitialized =>
            spec_throw_error(st, ErrorKind::ReferenceError, name),
        SpecIdentLookup::Undeclared => {
            match spec_heap_has_prop(st.heap, st.intr.realm, st.intr.global_obj, name) {
                HeapWriteRes::Ok(true) => {
                    match spec_heap_get_prop(st.heap, st.intr.realm, st.intr.global_obj, name) {
                        SpecHeapReadVal::Ok(v) =>
                            (st, SpecExprStep::Val(SpecVal::Str(spec_typeof_val(st.heap, st.intr.realm, v)))),
                        _ => (st, SpecExprStep::Val(SpecVal::Str(spec_k_undefined()))),
                    }
                }
                _ => (st, SpecExprStep::Val(SpecVal::Str(spec_k_undefined()))),
            }
        }
    }
}

pub fn eval_typeof_ident_exec(st: &mut VmState, name: &JsStr) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_eval_typeof_ident(old(st)@, name@),
        final(st).fuel == old(st).fuel,
        !(res@ is OutOfFuel),
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
{
    reveal(spec_eval_typeof_ident);
    match st.envs.get_identifier(st.current_env, name) {
        IdentLookup::Found(v) =>
            ExprStep::Val(Val::Str(typeof_val_exec(&st.heap, st.intr.realm, &v))),
        IdentLookup::TdzUninitialized =>
            throw_error_exec(st, ErrorKind::ReferenceError, clone_js_str(name)),
        IdentLookup::Undeclared => {
            match st.heap.has_prop(st.intr.realm, st.intr.global_obj, name) {
                HeapWriteRes::Ok(true) => {
                    match st.heap.get_prop(st.intr.realm, st.intr.global_obj, name) {
                        HeapReadVal::Ok(v) =>
                            ExprStep::Val(Val::Str(typeof_val_exec(&st.heap, st.intr.realm, &v))),
                        _ => ExprStep::Val(Val::Str(k_undefined())),
                    }
                }
                _ => ExprStep::Val(Val::Str(k_undefined())),
            }
        }
    }
}

#[verifier::opaque]
pub open spec fn spec_eval_ident_put_body(
    st: SpecState,
    name: Seq<u16>,
    val: SpecVal,
) -> (SpecState, SpecExprStep) {
    match spec_resolve_binding_loc(st.envs, st.current_env, name) {
        Some(_) => {
            let (envs2, out) = spec_set_identifier(st.envs, st.current_env, name, val, st.strict);
            let st2 = SpecState { envs: envs2, ..st };
            match out {
                IdentAssignOutcome::Ok => (st2, SpecExprStep::Val(val)),
                IdentAssignOutcome::TdzUninitialized =>
                    spec_throw_error(st2, ErrorKind::ReferenceError, name),
                IdentAssignOutcome::ImmutableConst =>
                    spec_throw_error(st2, ErrorKind::TypeError, name),
                IdentAssignOutcome::UndeclaredStrict =>
                    spec_throw_error(st2, ErrorKind::ReferenceError, name),
            }
        }
        None => {
            match spec_heap_has_prop(st.heap, st.intr.realm, st.intr.global_obj, name) {
                HeapWriteRes::Ok(true) =>
                    spec_set_property_val(st, SpecVal::Object(st.intr.global_obj), name, val),
                _ => {
                    if st.strict {
                        spec_throw_error(st, ErrorKind::ReferenceError, name)
                    } else {
                        spec_set_property_val(st, SpecVal::Object(st.intr.global_obj), name, val)
                    }
                }
            }
        }
    }
}

pub open spec fn spec_eval_ident_put(
    st: SpecState,
    name: Seq<u16>,
    val: SpecVal,
) -> (SpecState, SpecExprStep) {
    let (st2, r) = spec_eval_ident_put_body(st, name, val);
    (SpecState { fuel: st.fuel, ..st2 }, r)
}

pub fn eval_ident_put_exec(st: &mut VmState, name: &JsStr, val: Val) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_eval_ident_put(old(st)@, name@, val@),
        final(st).fuel == old(st).fuel,
        !(res@ is OutOfFuel),
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
{
    reveal(spec_eval_ident_put_body);
    if st.envs.resolve_binding_loc(st.current_env, name).is_some() {
        let v_ret = clone_val(&val);
        let strict = st.strict;
        let out = st.envs.set_identifier(st.current_env, name, val, strict);
        match out {
            IdentAssignOutcome::Ok => ExprStep::Val(v_ret),
            IdentAssignOutcome::TdzUninitialized =>
                throw_error_exec(st, ErrorKind::ReferenceError, clone_js_str(name)),
            IdentAssignOutcome::ImmutableConst =>
                throw_error_exec(st, ErrorKind::TypeError, clone_js_str(name)),
            IdentAssignOutcome::UndeclaredStrict =>
                throw_error_exec(st, ErrorKind::ReferenceError, clone_js_str(name)),
        }
    } else {
        match st.heap.has_prop(st.intr.realm, st.intr.global_obj, name) {
            HeapWriteRes::Ok(true) => {
                let g = Val::Object(st.intr.global_obj);
                set_property_val_exec(st, &g, clone_js_str(name), val)
            }
            _ => {
                if st.strict {
                    throw_error_exec(st, ErrorKind::ReferenceError, clone_js_str(name))
                } else {
                    let g = Val::Object(st.intr.global_obj);
                    set_property_val_exec(st, &g, clone_js_str(name), val)
                }
            }
        }
    }
}

#[verifier::opaque]
pub open spec fn spec_eval_delete_ident(st: SpecState, name: Seq<u16>) -> (SpecState, SpecExprStep) {
    if spec_resolve_binding_loc(st.envs, st.current_env, name) is Some {
        (st, SpecExprStep::Val(SpecVal::Bool(false)))
    } else {
        let (h2, wres) = spec_heap_delete_prop(st.heap, st.intr.realm, st.intr.global_obj, name);
        let st2 = SpecState { heap: h2, ..st };
        match wres {
            HeapWriteRes::Ok(ok) => (st2, SpecExprStep::Val(SpecVal::Bool(ok))),
            _ => spec_throw_error(st2, ErrorKind::TypeError, spec_k_empty()),
        }
    }
}

pub fn eval_delete_ident_exec(st: &mut VmState, name: &JsStr) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_eval_delete_ident(old(st)@, name@),
        final(st).fuel == old(st).fuel,
        !(res@ is OutOfFuel),
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
{
    reveal(spec_eval_delete_ident);
    if st.envs.resolve_binding_loc(st.current_env, name).is_some() {
        ExprStep::Val(Val::Bool(false))
    } else {
        match st.heap.delete_prop(st.intr.realm, st.intr.global_obj, name) {
            HeapWriteRes::Ok(ok) => ExprStep::Val(Val::Bool(ok)),
            _ => throw_error_exec(st, ErrorKind::TypeError, k_empty()),
        }
    }
}

/// Named & anonymous `FunctionExpression` allocation (§15.2.5):
/// Named function expressions bind their own name immutably in a dedicated inner lexical scope!
#[verifier::opaque]
pub open spec fn spec_alloc_func_expr(
    prog: SpecProgram,
    func_id: FuncId,
    st: SpecState,
) -> (SpecState, SpecExprStep) {
    if (func_id.0 as int) >= prog.funcs.len() {
        (st, SpecExprStep::Unsupported(UnsupportedFeature::InvalidAstReference))
    } else {
        let f = prog.funcs[func_id.0 as int];
        match f.name {
            None => spec_alloc_closure(prog, func_id, st.current_env, st),
            Some(nm) => {
                let erbase = st.env_roots.len();
                let (envs1, name_env) = spec_alloc_env(st.envs, EnvKind::Block, st.current_env, None);
                let st1 = spec_push_env_root(SpecState { envs: envs1, ..st }, name_env);
                let (st2_raw, cstep) = spec_alloc_closure(prog, func_id, name_env, st1);
                let st2 = spec_truncate_env_roots(st2_raw, erbase);
                match cstep {
                    SpecExprStep::Val(fv) => {
                        let fn_strict = st2.strict || f.strict;
                        let envs3 = spec_bind_initialized(st2.envs, name_env, nm, fv, false, fn_strict);
                        (SpecState { envs: envs3, ..st2 }, SpecExprStep::Val(fv))
                    }
                    other => (st2, other),
                }
            }
        }
    }
}

pub fn alloc_func_expr_exec(
    prog: &Program,
    func_id: FuncId,
    st: &mut VmState,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_alloc_func_expr(prog@, func_id, old(st)@),
        final(st).fuel == old(st).fuel,
        !(res@ is OutOfFuel),
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
{
    reveal(spec_alloc_func_expr);
    if func_id.0 >= prog.funcs.len() {
        return ExprStep::Unsupported(UnsupportedFeature::InvalidAstReference);
    }
    proof { assert(prog@.funcs[func_id.0 as int] == prog.funcs@[func_id.0 as int]@); }
    let has_name = prog.funcs[func_id.0].name.is_some();
    if !has_name {
        let cur = st.current_env;
        alloc_closure_exec(prog, func_id, cur, st)
    } else {
        let nm = match &prog.funcs[func_id.0].name {
            Some(s) => clone_js_str(s),
            None => k_empty(),
        };
        let f_strict = prog.funcs[func_id.0].strict;
        let erbase = st.env_roots.len();
        let cur = st.current_env;
        let name_env = st.envs.alloc_env(EnvKind::Block, cur, None);
        st.push_env_root(name_env);
        let cstep = alloc_closure_exec(prog, func_id, name_env, st);
        st.truncate_env_roots(erbase);
        match cstep {
            ExprStep::Val(fv) => {
                let fn_strict = st.strict || f_strict;
                let fv_copy = clone_val(&fv);
                st.envs.bind_initialized(name_env, nm, fv_copy, false, fn_strict);
                ExprStep::Val(fv)
            }
            other => other,
        }
    }
}

/// Hoist `var` declarations into `target_env` (`Global` -> `global_obj`, `Function` -> `EnvArena`).
pub open spec fn spec_hoist_one_var(
    st: SpecState,
    target_env: EnvId,
    name: Seq<u16>,
    strict: bool,
) -> SpecState {
    if target_env == EnvId(0) {
        let h2 = spec_define_global_var_prop(st.heap, st.intr.realm, st.intr.global_obj, name);
        SpecState { heap: h2, ..st }
    } else {
        let e2 = spec_declare_var(st.envs, target_env, name, strict);
        SpecState { envs: e2, ..st }
    }
}

pub open spec fn spec_hoist_vars_from(
    vars: Seq<Seq<u16>>,
    idx: nat,
    target_env: EnvId,
    strict: bool,
    st: SpecState,
) -> SpecState
    decreases vars.len() - idx,
{
    if idx >= vars.len() {
        st
    } else {
        let st1 = spec_hoist_one_var(st, target_env, vars[idx as int], strict);
        spec_hoist_vars_from(vars, idx + 1, target_env, strict, st1)
    }
}

pub fn hoist_vars_exec(
    vars: &Vec<JsStr>,
    target_env: EnvId,
    strict: bool,
    st: &mut VmState,
)
    ensures
        final(st)@ == spec_hoist_vars_from(spec_str_seq_view(vars@), 0, target_env, strict, old(st)@),
        final(st).fuel == old(st).fuel,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
{
    let n = vars.len();
    let mut i: usize = 0;
    let ghost svars = spec_str_seq_view(vars@);
    let ghost init_st = old(st)@;
    while i < n
        invariant
            i <= n == vars@.len(),
            svars == spec_str_seq_view(vars@),
            st.fuel == old(st).fuel,
            env_wf(old(st)@.envs) ==> env_wf(st@.envs),
            spec_hoist_vars_from(svars, 0, target_env, strict, init_st)
                == spec_hoist_vars_from(svars, i as nat, target_env, strict, st@),
        decreases n - i,
    {
        if target_env.0 == 0 {
            st.heap.define_global_var_prop(st.intr.realm, st.intr.global_obj, clone_js_str(&vars[i]));
        } else {
            st.envs.declare_var(target_env, clone_js_str(&vars[i]), strict);
        }
        i += 1;
    }
}

pub open spec fn spec_declare_tdz_list(
    envs: SpecEnvArena,
    env_id: EnvId,
    decls: Seq<SpecVarDeclarator>,
    idx: nat,
    mutable: bool,
) -> SpecEnvArena
    decreases decls.len() - idx,
{
    if idx >= decls.len() {
        envs
    } else {
        let e1 = spec_declare_tdz(envs, env_id, decls[idx as int].name, mutable, true);
        spec_declare_tdz_list(e1, env_id, decls, idx + 1, mutable)
    }
}

fn declare_tdz_list_exec(
    envs: &mut EnvArena,
    env_id: EnvId,
    decls: &Vec<VarDeclarator>,
    mutable: bool,
)
    ensures
        final(envs)@ == spec_declare_tdz_list(old(envs)@, env_id, spec_var_decls_view(decls@), 0, mutable),
        env_wf(old(envs)@) ==> env_wf(final(envs)@),
{
    let n = decls.len();
    let mut i: usize = 0;
    let ghost sdecls = spec_var_decls_view(decls@);
    let ghost init_e = old(envs)@;
    while i < n
        invariant
            i <= n == decls@.len(),
            sdecls == spec_var_decls_view(decls@),
            env_wf(old(envs)@) ==> env_wf(envs@),
            spec_declare_tdz_list(init_e, env_id, sdecls, 0, mutable)
                == spec_declare_tdz_list(envs@, env_id, sdecls, i as nat, mutable),
        decreases n - i,
    {
        envs.declare_tdz(env_id, clone_js_str(&decls[i].name), mutable, true);
        i += 1;
    }
}

/// Hoist block-level lexical declarations (`let`/`const` -> TDZ `Uninitialized`) and
/// `FunctionDeclaration`s (`FuncDecl` -> initialized closure).
pub open spec fn spec_unwrap_labeled_stmt(
    stmts: Seq<SpecStmtNode>,
    sid: StmtId,
    steps: nat,
) -> StmtId
    decreases steps,
{
    if steps == 0 || (sid.0 as int) >= stmts.len() {
        sid
    } else {
        match stmts[sid.0 as int] {
            SpecStmtNode::Labeled { body, .. } => spec_unwrap_labeled_stmt(stmts, body, (steps - 1) as nat),
            _ => sid,
        }
    }
}

fn unwrap_labeled_stmt_exec(prog: &Program, sid: StmtId) -> (r: StmtId)
    ensures r == spec_unwrap_labeled_stmt(prog@.stmts, sid, prog@.stmts.len()),
{
    let mut cur = sid;
    let mut rem = prog.stmts.len();
    let ghost sstmts = prog@.stmts;
    while rem > 0
        invariant
            rem <= prog.stmts@.len(),
            sstmts == prog@.stmts,
            spec_unwrap_labeled_stmt(sstmts, sid, prog@.stmts.len())
                == spec_unwrap_labeled_stmt(sstmts, cur, rem as nat),
        decreases rem,
    {
        if cur.0 >= prog.stmts.len() {
            return cur;
        }
        proof { assert(sstmts[cur.0 as int] == prog.stmts@[cur.0 as int]@); }
        match &prog.stmts[cur.0] {
            StmtNode::Labeled { body, .. } => {
                cur = *body;
                rem -= 1;
            }
            _ => return cur,
        }
    }
    cur
}

#[verifier::opaque]
pub open spec fn spec_hoist_one_stmt_decl_body(
    prog: SpecProgram,
    sid_in: StmtId,
    target_env: EnvId,
    st: SpecState,
) -> (SpecState, SpecExprStep) {
    let sid = spec_unwrap_labeled_stmt(prog.stmts, sid_in, prog.stmts.len());
    if (sid.0 as int) >= prog.stmts.len() {
        (st, SpecExprStep::Unsupported(UnsupportedFeature::InvalidAstReference))
    } else {
        match prog.stmts[sid.0 as int] {
            SpecStmtNode::VarDecl { kind: VarKind::Let, decls } => {
                let e2 = spec_declare_tdz_list(st.envs, target_env, decls, 0, true);
                (SpecState { envs: e2, ..st }, SpecExprStep::Val(SpecVal::Undefined))
            }
            SpecStmtNode::VarDecl { kind: VarKind::Const, decls } => {
                let e2 = spec_declare_tdz_list(st.envs, target_env, decls, 0, false);
                (SpecState { envs: e2, ..st }, SpecExprStep::Val(SpecVal::Undefined))
            }
            SpecStmtNode::FuncDecl { func } => {
                if (func.0 as int) >= prog.funcs.len() {
                    (st, SpecExprStep::Unsupported(UnsupportedFeature::InvalidAstReference))
                } else {
                    let (st1, cstep) = spec_alloc_closure(prog, func, target_env, st);
                    match cstep {
                        SpecExprStep::Val(fv) => {
                            match prog.funcs[func.0 as int].name {
                                Some(nm) => {
                                    if target_env == EnvId(0) {
                                        let (st2, sres) = spec_set_property_val(
                                            st1,
                                            SpecVal::Object(st1.intr.global_obj),
                                            nm,
                                            fv,
                                        );
                                        match sres {
                                            SpecExprStep::Val(_) => (st2, SpecExprStep::Val(SpecVal::Undefined)),
                                            abrupt => (st2, abrupt),
                                        }
                                    } else {
                                        let e2 = spec_bind_initialized(st1.envs, target_env, nm, fv, true, st1.strict);
                                        (SpecState { envs: e2, ..st1 }, SpecExprStep::Val(SpecVal::Undefined))
                                    }
                                }
                                None => (st1, SpecExprStep::Val(SpecVal::Undefined)),
                            }
                        }
                        abrupt => (st1, abrupt),
                    }
                }
            }
            _ => (st, SpecExprStep::Val(SpecVal::Undefined)),
        }
    }
}

pub open spec fn spec_hoist_one_stmt_decl(
    prog: SpecProgram,
    sid: StmtId,
    target_env: EnvId,
    st: SpecState,
) -> (SpecState, SpecExprStep) {
    let (st2, r) = spec_hoist_one_stmt_decl_body(prog, sid, target_env, st);
    (SpecState { fuel: st.fuel, ..st2 }, r)
}

pub fn hoist_one_stmt_decl_exec(
    prog: &Program,
    sid_in: StmtId,
    target_env: EnvId,
    st: &mut VmState,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_hoist_one_stmt_decl(prog@, sid_in, target_env, old(st)@),
        final(st).fuel == old(st).fuel,
        !(res@ is OutOfFuel),
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
{
    reveal(spec_hoist_one_stmt_decl_body);
    let sid = unwrap_labeled_stmt_exec(prog, sid_in);
    if sid.0 >= prog.stmts.len() {
        return ExprStep::Unsupported(UnsupportedFeature::InvalidAstReference);
    }
    proof { assert(prog@.stmts[sid.0 as int] == prog.stmts@[sid.0 as int]@); }
    match &prog.stmts[sid.0] {
        StmtNode::VarDecl { kind: VarKind::Let, decls } => {
            declare_tdz_list_exec(&mut st.envs, target_env, decls, true);
            ExprStep::Val(Val::Undefined)
        }
        StmtNode::VarDecl { kind: VarKind::Const, decls } => {
            declare_tdz_list_exec(&mut st.envs, target_env, decls, false);
            ExprStep::Val(Val::Undefined)
        }
        StmtNode::FuncDecl { func } => {
            let fid = *func;
            if fid.0 >= prog.funcs.len() {
                return ExprStep::Unsupported(UnsupportedFeature::InvalidAstReference);
            }
            proof { assert(prog@.funcs[fid.0 as int] == prog.funcs@[fid.0 as int]@); }
            let cstep = alloc_closure_exec(prog, fid, target_env, st);
            match cstep {
                ExprStep::Val(fv) => {
                    match &prog.funcs[fid.0].name {
                        Some(nm) => {
                            if target_env.0 == 0 {
                                let g = Val::Object(st.intr.global_obj);
                                let sres = set_property_val_exec(st, &g, clone_js_str(nm), fv);
                                match sres {
                                    ExprStep::Val(_) => ExprStep::Val(Val::Undefined),
                                    abrupt => abrupt,
                                }
                            } else {
                                let strict = st.strict;
                                st.envs.bind_initialized(target_env, clone_js_str(nm), fv, true, strict);
                                ExprStep::Val(Val::Undefined)
                            }
                        }
                        None => ExprStep::Val(Val::Undefined),
                    }
                }
                abrupt => abrupt,
            }
        }
        _ => ExprStep::Val(Val::Undefined),
    }
}

pub open spec fn spec_hoist_block_stmts(
    prog: SpecProgram,
    stmts: Seq<StmtId>,
    idx: nat,
    target_env: EnvId,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases stmts.len() - idx,
{
    if idx >= stmts.len() {
        (st, SpecExprStep::Val(SpecVal::Undefined))
    } else {
        let (st1, step) = spec_hoist_one_stmt_decl(prog, stmts[idx as int], target_env, st);
        match step {
            SpecExprStep::Val(_) => spec_hoist_block_stmts(prog, stmts, idx + 1, target_env, st1),
            abrupt => (st1, abrupt),
        }
    }
}

pub fn hoist_block_stmts_exec(
    prog: &Program,
    stmts: &Vec<StmtId>,
    target_env: EnvId,
    st: &mut VmState,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_hoist_block_stmts(prog@, stmts@, 0, target_env, old(st)@),
        final(st).fuel == old(st).fuel,
        !(res@ is OutOfFuel),
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
{
    let n = stmts.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n == stmts@.len(),
            st.fuel == old(st).fuel,
            env_wf(old(st)@.envs) ==> env_wf(st@.envs),
            spec_hoist_block_stmts(prog@, stmts@, 0, target_env, old(st)@)
                == spec_hoist_block_stmts(prog@, stmts@, i as nat, target_env, st@),
        decreases n - i,
    {
        let sid = stmts[i];
        let step = hoist_one_stmt_decl_exec(prog, sid, target_env, st);
        match &step {
            ExprStep::Val(_) => {
                i += 1;
            }
            _ => return step,
        }
    }
    ExprStep::Val(Val::Undefined)
}

#[verifier::opaque]
pub open spec fn spec_index_key(idx: usize) -> Seq<u16> {
    spec_number_to_string(spec_num_from_usize(idx))
}

fn index_key_exec(idx: usize) -> (r: JsStr)
    ensures r@ == spec_index_key(idx),
{
    reveal(spec_index_key);
    number_to_js_str(num_from_usize(idx))
}

/// Allocate `arguments` object `{ "0": args[0], ..., "length": args.len() }` for non-arrow calls.
pub open spec fn spec_build_args_props(
    args: Seq<SpecVal>,
    idx: nat,
    acc: Seq<SpecPropEntry>,
) -> Seq<SpecPropEntry>
    decreases args.len() - idx,
{
    if idx >= args.len() {
        acc.push(spec_prop_data(spec_k_length(), SpecVal::Number(spec_num_from_usize(args.len() as usize)), false))
    } else {
        let key = spec_index_key(idx as usize);
        let next_acc = acc.push(spec_prop_data(key, args[idx as int], true));
        spec_build_args_props(args, idx + 1, next_acc)
    }
}

#[verifier::opaque]
pub open spec fn spec_alloc_arguments_obj_body(
    args: Seq<SpecVal>,
    st: SpecState,
) -> (SpecState, AllocRes) {
    let obj = SpecHeapObject {
        realm: st.intr.realm,
        prototype: Some(st.intr.object_proto),
        extensible: true,
        kind: ObjectKind::Ordinary,
        props: spec_build_args_props(args, 0, seq![]),
    };
    spec_state_alloc_obj(st, obj)
}

pub open spec fn spec_alloc_arguments_obj(
    args: Seq<SpecVal>,
    st: SpecState,
) -> (SpecState, AllocRes) {
    let (st2, r) = spec_alloc_arguments_obj_body(args, st);
    (SpecState { fuel: st.fuel, ..st2 }, r)
}

pub fn alloc_arguments_obj_exec(
    args: &Vec<Val>,
    st: &mut VmState,
) -> (res: AllocRes)
    ensures
        (final(st)@, res) == spec_alloc_arguments_obj(spec_vals_view(args@), old(st)@),
        final(st).fuel == old(st).fuel,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
{
    reveal(spec_alloc_arguments_obj_body);
    let n = args.len();
    let mut ps: Vec<PropEntry> = Vec::new();
    let mut i: usize = 0;
    let ghost sargs = spec_vals_view(args@);
    proof { assert(spec_props_view(ps@) =~= Seq::<SpecPropEntry>::empty()); }
    while i < n
        invariant
            i <= n == args@.len(),
            sargs == spec_vals_view(args@),
            spec_build_args_props(sargs, 0, seq![])
                == spec_build_args_props(sargs, i as nat, spec_props_view(ps@)),
        decreases n - i,
    {
        let ghost pre = spec_props_view(ps@);
        let key = index_key_exec(i);
        let cv = clone_val(&args[i]);
        ps.push(make_prop_data(key, cv, true));
        proof {
            assert(spec_props_view(ps@) =~= pre.push(
                spec_prop_data(spec_index_key(i), sargs[i as int], true)
            ));
        }
        i += 1;
    }
    let ghost pre_len = spec_props_view(ps@);
    ps.push(make_prop_data(k_length(), Val::Number(num_from_usize(n)), false));
    proof {
        assert(spec_props_view(ps@) =~= pre_len.push(
            spec_prop_data(spec_k_length(), SpecVal::Number(spec_num_from_usize(n)), false)
        ));
    }
    let obj = HeapObject {
        realm: st.intr.realm,
        prototype: Some(st.intr.object_proto),
        extensible: true,
        kind: ObjectKind::Ordinary,
        props: ps,
    };
    st.alloc_obj(obj)
}

pub open spec fn spec_bind_params(
    envs: SpecEnvArena,
    fn_env: EnvId,
    params: Seq<Seq<u16>>,
    args: Seq<SpecVal>,
    idx: nat,
    strict: bool,
) -> SpecEnvArena
    decreases params.len() - idx,
{
    if idx >= params.len() {
        envs
    } else {
        let av = if idx < args.len() { args[idx as int] } else { SpecVal::Undefined };
        let e1 = spec_bind_initialized(envs, fn_env, params[idx as int], av, true, strict);
        spec_bind_params(e1, fn_env, params, args, idx + 1, strict)
    }
}

fn bind_params_exec(
    envs: &mut EnvArena,
    fn_env: EnvId,
    params: &Vec<JsStr>,
    args: &Vec<Val>,
    strict: bool,
)
    ensures
        final(envs)@ == spec_bind_params(
            old(envs)@,
            fn_env,
            spec_str_seq_view(params@),
            spec_vals_view(args@),
            0,
            strict,
        ),
        env_wf(old(envs)@) ==> env_wf(final(envs)@),
{
    let np = params.len();
    let na = args.len();
    let mut i: usize = 0;
    let ghost sparams = spec_str_seq_view(params@);
    let ghost sargs = spec_vals_view(args@);
    while i < np
        invariant
            i <= np == params@.len(),
            na == args@.len(),
            sparams == spec_str_seq_view(params@),
            sargs == spec_vals_view(args@),
            env_wf(old(envs)@) ==> env_wf(envs@),
            spec_bind_params(old(envs)@, fn_env, sparams, sargs, 0, strict)
                == spec_bind_params(envs@, fn_env, sparams, sargs, i as nat, strict),
        decreases np - i,
    {
        let av = if i < na { clone_val(&args[i]) } else { Val::Undefined };
        envs.bind_initialized(fn_env, clone_js_str(&params[i]), av, true, strict);
        i += 1;
    }
}

pub open spec fn spec_params_contain(params: Seq<Seq<u16>>, target: Seq<u16>, idx: nat) -> bool
    decreases params.len() - idx,
{
    if idx >= params.len() {
        false
    } else if params[idx as int] == target {
        true
    } else {
        spec_params_contain(params, target, idx + 1)
    }
}

fn params_contain_exec(params: &Vec<JsStr>, target: &JsStr) -> (r: bool)
    ensures r == spec_params_contain(spec_str_seq_view(params@), target@, 0),
{
    let n = params.len();
    let mut i: usize = 0;
    let ghost sp = spec_str_seq_view(params@);
    while i < n
        invariant
            i <= n == params@.len(),
            sp == spec_str_seq_view(params@),
            spec_params_contain(sp, target@, 0) == spec_params_contain(sp, target@, i as nat),
        decreases n - i,
    {
        if js_str_eq(&params[i], target) {
            return true;
        }
        i += 1;
    }
    false
}

pub open spec fn spec_opt_str_eq(a: Option<Seq<u16>>, b: Option<Seq<u16>>) -> bool {
    match (a, b) {
        (None, None) => true,
        (Some(sa), Some(sb)) => sa == sb,
        _ => false,
    }
}

pub open spec fn spec_loop_target_matches(loop_label: Option<Seq<u16>>, target: Option<Seq<u16>>) -> bool {
    match target {
        None => true,
        Some(t) => match loop_label {
            Some(l) => l == t,
            None => false,
        },
    }
}

fn loop_target_matches_exec(loop_label: &Option<JsStr>, target: &Option<JsStr>) -> (r: bool)
    ensures r == spec_loop_target_matches(spec_opt_str_view(loop_label), spec_opt_str_view(target)),
{
    match target {
        None => true,
        Some(t) => match loop_label {
            Some(l) => js_str_eq(l, t),
            None => false,
        },
    }
}

pub open spec fn spec_iter_target_matches(labels: Seq<Seq<u16>>, target: Option<Seq<u16>>) -> bool {
    match target {
        None => true,
        Some(t) => spec_str_seq_contains_from(labels, t, 0),
    }
}

fn iter_target_matches_exec(labels: &Vec<JsStr>, target: &Option<JsStr>) -> (r: bool)
    ensures r == spec_iter_target_matches(spec_str_seq_view(labels@), spec_opt_str_view(target)),
{
    match target {
        None => true,
        Some(t) => crate::heap::str_vec_contains_exec(labels, t),
    }
}

// ===========================================================================
// Mutually Recursive Verified Interpreter Core (Ranks 1..14)
// Lexicographic Termination Measure: `decreases (st.fuel, rank, sub)`
// ===========================================================================

// ---------------------------------------------------------------------------
// Rank 1: `eval_call` (`decreases (st.fuel, 1nat, 0nat)`)
// ---------------------------------------------------------------------------

#[verifier::opaque]
pub open spec fn spec_setup_user_call_env_body(
    params: Seq<Seq<u16>>,
    cap_env: EnvId,
    fn_strict: bool,
    is_arrow: bool,
    this_arg: SpecVal,
    args: Seq<SpecVal>,
    st: SpecState,
) -> (SpecState, Option<EnvId>) {
    let (st1, this_res): (SpecState, Result<Option<SpecVal>, ()>) = if is_arrow {
        (st, Ok(None))
    } else if fn_strict {
        (st, Ok(Some(this_arg)))
    } else {
        match this_arg {
            SpecVal::Undefined | SpecVal::Null => (st, Ok(Some(SpecVal::Object(st.intr.global_obj)))),
            SpecVal::Object(oid) => (st, Ok(Some(SpecVal::Object(oid)))),
            _ => {
                // §10.2.1.2 OrdinaryCallBindThis: non-strict primitive `this` is boxed via `ToObject`.
                let box_obj = SpecHeapObject {
                    realm: st.intr.realm,
                    prototype: Some(st.intr.object_proto),
                    extensible: true,
                    kind: ObjectKind::Ordinary,
                    props: seq![],
                };
                let (stb, bres) = spec_state_alloc_obj(st, box_obj);
                match bres {
                    AllocRes::Ok(boid) => (stb, Ok(Some(SpecVal::Object(boid)))),
                    AllocRes::QuotaExceeded => (stb, Err(())),
                }
            }
        }
    };
    match this_res {
        Err(()) => (st1, None),
        Ok(fn_this) => {
            let (envs1, fn_env) = spec_alloc_env(st1.envs, EnvKind::Function, cap_env, fn_this);
            let envs2 = spec_bind_params(envs1, fn_env, params, args, 0, fn_strict);
            let st2 = SpecState { envs: envs2, ..st1 };
            if !is_arrow && !spec_params_contain(params, spec_k_arguments(), 0) {
                let erbase = st2.env_roots.len();
                let st2_r = spec_push_env_root(st2, fn_env);
                let (st_a_raw, ares) = spec_alloc_arguments_obj(args, st2_r);
                let st_a = spec_truncate_env_roots(st_a_raw, erbase);
                match ares {
                    AllocRes::QuotaExceeded => (st_a, None),
                    AllocRes::Ok(aoid) => {
                        let ea = spec_bind_initialized(st_a.envs, fn_env, spec_k_arguments(), SpecVal::Object(aoid), true, false);
                        (SpecState { envs: ea, ..st_a }, Some(fn_env))
                    }
                }
            } else {
                (st2, Some(fn_env))
            }
        }
    }
}

pub open spec fn spec_setup_user_call_env(
    params: Seq<Seq<u16>>,
    cap_env: EnvId,
    fn_strict: bool,
    is_arrow: bool,
    this_arg: SpecVal,
    args: Seq<SpecVal>,
    st: SpecState,
) -> (SpecState, Option<EnvId>) {
    let (st2, r) = spec_setup_user_call_env_body(params, cap_env, fn_strict, is_arrow, this_arg, args, st);
    (SpecState { fuel: st.fuel, ..st2 }, r)
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
fn setup_user_call_env_exec(
    params: &Vec<JsStr>,
    cap_env: EnvId,
    fn_strict: bool,
    is_arrow: bool,
    this_arg: Val,
    args: &Vec<Val>,
    st: &mut VmState,
) -> (res: Option<EnvId>)
    ensures
        (final(st)@, res) == spec_setup_user_call_env(
            spec_str_seq_view(params@),
            cap_env,
            fn_strict,
            is_arrow,
            this_arg@,
            spec_vals_view(args@),
            old(st)@,
        ),
        final(st).fuel == old(st).fuel,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
{
    reveal(spec_setup_user_call_env_body);
    let fn_this: Option<Val> = if is_arrow {
        None
    } else if fn_strict {
        Some(this_arg)
    } else {
        match this_arg {
            Val::Undefined | Val::Null => Some(Val::Object(st.intr.global_obj)),
            Val::Object(oid) => Some(Val::Object(oid)),
            _ => {
                let box_obj = HeapObject {
                    realm: st.intr.realm,
                    prototype: Some(st.intr.object_proto),
                    extensible: true,
                    kind: ObjectKind::Ordinary,
                    props: Vec::new(),
                };
                proof { assert(box_obj@.props =~= seq![]); }
                match st.alloc_obj(box_obj) {
                    AllocRes::Ok(boid) => Some(Val::Object(boid)),
                    AllocRes::QuotaExceeded => return None,
                }
            }
        }
    };
    let fn_env = st.envs.alloc_env(EnvKind::Function, cap_env, fn_this);
    bind_params_exec(&mut st.envs, fn_env, params, args, fn_strict);

    let ak = k_arguments();
    if !is_arrow && !params_contain_exec(params, &ak) {
        let erbase = st.env_roots.len();
        st.push_env_root(fn_env);
        let a_res = alloc_arguments_obj_exec(args, st);
        st.truncate_env_roots(erbase);
        match a_res {
            AllocRes::QuotaExceeded => None,
            AllocRes::Ok(aoid) => {
                st.envs.bind_initialized(fn_env, ak, Val::Object(aoid), true, false);
                Some(fn_env)
            }
        }
    } else {
        Some(fn_env)
    }
}

pub open spec fn spec_eval_user_call_body(
    prog: SpecProgram,
    func_id: FuncId,
    cap_env: EnvId,
    fn_strict: bool,
    is_arrow: bool,
    this_arg: SpecVal,
    args: Seq<SpecVal>,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 12nat, 1nat,
{
    spec_eval_user_call_body_inner(prog, func_id, cap_env, fn_strict, is_arrow, this_arg, args, st)
}

#[verifier::opaque]
pub open spec fn spec_eval_user_call_body_inner(
    prog: SpecProgram,
    func_id: FuncId,
    cap_env: EnvId,
    fn_strict: bool,
    is_arrow: bool,
    this_arg: SpecVal,
    args: Seq<SpecVal>,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 12nat, 0nat,
{
    if (func_id.0 as int) >= prog.funcs.len() {
        (st, SpecExprStep::Unsupported(UnsupportedFeature::InvalidAstReference))
    } else {
        let f = prog.funcs[func_id.0 as int];
        let erbase = st.env_roots.len();
        let st_er = spec_push_env_root(spec_push_env_root(st, st.current_env), cap_env);
        let (st3, env_opt) = spec_setup_user_call_env(f.params, cap_env, fn_strict, is_arrow, this_arg, args, st_er);
        match env_opt {
            None => (spec_truncate_env_roots(st3, erbase), SpecExprStep::HeapQuotaExceeded),
            Some(fn_env) => {
                let saved_env = st.current_env;
                let saved_strict = st3.strict;
                let st4_raw = spec_hoist_vars_from(f.hoisted_vars, 0, fn_env, fn_strict, SpecState {
                    current_env: fn_env,
                    strict: fn_strict,
                    ..st3
                });
                let st4 = spec_cap_fuel(st4_raw, st3.fuel);
                let (st5_raw, hstep) = spec_hoist_block_stmts(prog, f.body, 0, fn_env, st4);
                let st5 = spec_cap_fuel(st5_raw, st4.fuel);
                match hstep {
                    SpecExprStep::Val(_) => {
                        let (st6_raw, bstep) = spec_eval_stmt_list(prog, f.body, 0, SpecCompletionValue::Empty, st5);
                        let st6 = spec_truncate_env_roots(SpecState {
                            current_env: saved_env,
                            strict: saved_strict,
                            ..spec_cap_fuel(st6_raw, st5.fuel)
                        }, erbase);
                        match bstep {
                            SpecStmtStep::Comp(SpecCompletion::Return(rv)) => (st6, SpecExprStep::Val(rv)),
                            SpecStmtStep::Comp(SpecCompletion::Normal(_)) => (st6, SpecExprStep::Val(SpecVal::Undefined)),
                            SpecStmtStep::Comp(SpecCompletion::Throw(tv)) => (st6, SpecExprStep::Throw(tv)),
                            SpecStmtStep::Comp(_) => (st6, SpecExprStep::Val(SpecVal::Undefined)),
                            SpecStmtStep::HeapQuotaExceeded => (st6, SpecExprStep::HeapQuotaExceeded),
                            SpecStmtStep::OutOfFuel => (st6, SpecExprStep::OutOfFuel),
                            SpecStmtStep::Unsupported(feat) => (st6, SpecExprStep::Unsupported(feat)),
                        }
                    }
                    abrupt => (spec_truncate_env_roots(SpecState { current_env: saved_env, strict: saved_strict, ..st5 }, erbase), abrupt),
                }
            }
        }
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(35)]
fn eval_user_call_body_exec(
    prog: &Program,
    func_id: FuncId,
    cap_env: EnvId,
    fn_strict: bool,
    is_arrow: bool,
    this_arg: Val,
    args: &Vec<Val>,
    st: &mut VmState,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_eval_user_call_body(
            prog@,
            func_id,
            cap_env,
            fn_strict,
            is_arrow,
            this_arg@,
            spec_vals_view(args@),
            old(st)@,
        ),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 12nat, 0nat,
{
    reveal(spec_eval_user_call_body_inner);
    if func_id.0 >= prog.funcs.len() {
        return ExprStep::Unsupported(UnsupportedFeature::InvalidAstReference);
    }
    proof { assert(prog@.funcs[func_id.0 as int] == prog.funcs@[func_id.0 as int]@); }
    let erbase = st.env_roots.len();
    let saved_env = st.current_env;
    st.push_env_root(saved_env);
    st.push_env_root(cap_env);
    let fn_env = match setup_user_call_env_exec(
        &prog.funcs[func_id.0].params,
        cap_env,
        fn_strict,
        is_arrow,
        this_arg,
        args,
        st,
    ) {
        None => {
            st.truncate_env_roots(erbase);
            return ExprStep::HeapQuotaExceeded;
        }
        Some(eid) => eid,
    };

    let saved_strict = st.strict;
    st.current_env = fn_env;
    st.strict = fn_strict;

    hoist_vars_exec(&prog.funcs[func_id.0].hoisted_vars, fn_env, fn_strict, st);
    let hstep = hoist_block_stmts_exec(prog, &prog.funcs[func_id.0].body, fn_env, st);
    match hstep {
        ExprStep::Val(_) => {
            let bstep = eval_stmt_list(prog, &prog.funcs[func_id.0].body, CompletionValue::Empty, st);
            st.current_env = saved_env;
            st.strict = saved_strict;
            st.truncate_env_roots(erbase);
            match bstep {
                StmtStep::Comp(Completion::Return(rv)) => ExprStep::Val(rv),
                StmtStep::Comp(Completion::Normal(_)) => ExprStep::Val(Val::Undefined),
                StmtStep::Comp(Completion::Throw(tv)) => ExprStep::Throw(tv),
                StmtStep::Comp(_) => ExprStep::Val(Val::Undefined),
                StmtStep::HeapQuotaExceeded => ExprStep::HeapQuotaExceeded,
                StmtStep::OutOfFuel => ExprStep::OutOfFuel,
                StmtStep::Unsupported(feat) => ExprStep::Unsupported(feat),
            }
        }
        abrupt => {
            st.current_env = saved_env;
            st.strict = saved_strict;
            st.truncate_env_roots(erbase);
            abrupt
        }
    }
}

pub open spec fn spec_eval_call(
    prog: SpecProgram,
    callee: SpecVal,
    this_arg: SpecVal,
    args: Seq<SpecVal>,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 1nat, 1nat,
{
    spec_eval_call_inner(prog, callee, this_arg, args, st)
}

#[verifier::opaque]
pub open spec fn spec_eval_call_inner(
    prog: SpecProgram,
    callee: SpecVal,
    this_arg: SpecVal,
    args: Seq<SpecVal>,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 1nat, 0nat,
{
    if st.fuel == 0 {
        (st, SpecExprStep::OutOfFuel)
    } else {
        let st_dec = SpecState { fuel: (st.fuel - 1) as nat, ..st };
        match callee {
            SpecVal::Object(oid) => {
                if (oid.0 as int) >= st_dec.heap.slots.len() {
                    spec_throw_error(st_dec, ErrorKind::TypeError, spec_k_empty())
                } else {
                    match st_dec.heap.slots[oid.0 as int] {
                        SpecSlot::Live(obj) => {
                            if obj.realm != st_dec.intr.realm {
                                spec_throw_error(st_dec, ErrorKind::TypeError, spec_k_empty())
                            } else {
                                match obj.kind {
                                    ObjectKind::BuiltinFunction { builtin, .. } => {
                                        let (st_out, r) = spec_eval_builtin_call(prog, builtin, this_arg, args, st_dec);
                                        (spec_cap_fuel(st_out, st_dec.fuel), r)
                                    }
                                    ObjectKind::Function { func_id, env: cap_env, is_strict, is_arrow, .. } => {
                                        let rbase = st_dec.temp_roots.len();
                                        let st_r = spec_push_root(st_dec, callee);
                                        let (st_out, r) = spec_eval_user_call_body(
                                            prog, func_id, cap_env, is_strict, is_arrow, this_arg, args, st_r,
                                        );
                                        (spec_truncate_roots(spec_cap_fuel(st_out, st_dec.fuel), rbase), r)
                                    }
                                    _ => spec_throw_error(st_dec, ErrorKind::TypeError, spec_k_empty()),
                                }
                            }
                        }
                        SpecSlot::Free => spec_throw_error(st_dec, ErrorKind::TypeError, spec_k_empty()),
                    }
                }
            }
            _ => spec_throw_error(st_dec, ErrorKind::TypeError, spec_k_empty()),
        }
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(25)]
pub fn eval_call(
    prog: &Program,
    callee: Val,
    this_arg: Val,
    args: &Vec<Val>,
    st: &mut VmState,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_eval_call(prog@, callee@, this_arg@, spec_vals_view(args@), old(st)@),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        !(res@ is OutOfFuel) ==> old(st).fuel > 0 && final(st).fuel < old(st).fuel,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 1nat, 0nat,
{
    reveal(spec_eval_call_inner);
    if st.fuel == 0 {
        return ExprStep::OutOfFuel;
    }
    st.fuel -= 1;
    let oid = match &callee {
        Val::Object(id) => *id,
        _ => return throw_error_exec(st, ErrorKind::TypeError, k_empty()),
    };
    if oid.0 >= st.heap.slots.len() {
        return throw_error_exec(st, ErrorKind::TypeError, k_empty());
    }
    proof { assert(st@.heap.slots[oid.0 as int] == st.heap.slots@[oid.0 as int]@); }
    let (obj_realm, obj_kind) = match &st.heap.slots[oid.0] {
        Slot::Live(o) => (o.realm, o.kind),
        Slot::Free => return throw_error_exec(st, ErrorKind::TypeError, k_empty()),
    };
    if obj_realm.0 != st.intr.realm.0 {
        return throw_error_exec(st, ErrorKind::TypeError, k_empty());
    }
    match obj_kind {
        ObjectKind::BuiltinFunction { builtin, .. } => {
            eval_builtin_call(prog, builtin, this_arg, args, st)
        }
        ObjectKind::Function { func_id, env: cap_env, is_strict, is_arrow, .. } => {
            let rbase = st.temp_roots.len();
            st.push_root(&callee);
            let res = eval_user_call_body_exec(prog, func_id, cap_env, is_strict, is_arrow, this_arg, args, st);
            st.truncate_roots(rbase);
            res
        }
        _ => throw_error_exec(st, ErrorKind::TypeError, k_empty()),
    }
}

// ---------------------------------------------------------------------------
// Rank 2: Abstract Type Conversions & Comparison Operations (§7.1, §7.2)
// ---------------------------------------------------------------------------

pub open spec fn spec_eval_to_primitive_obj(
    prog: SpecProgram,
    oid: ObjId,
    prefer_string: bool,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 2nat, 1nat,
{
    spec_eval_to_primitive_obj_inner(prog, oid, prefer_string, st)
}

#[verifier::opaque]
pub open spec fn spec_eval_to_primitive_obj_inner(
    prog: SpecProgram,
    oid: ObjId,
    prefer_string: bool,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 2nat, 0nat,
{
    let rbase = st.temp_roots.len();
    let obj_val = SpecVal::Object(oid);
    let st_r = spec_push_root(st, obj_val);
    let k1 = if prefer_string { spec_k_to_string() } else { spec_k_value_of() };
    let k2 = if prefer_string { spec_k_value_of() } else { spec_k_to_string() };
    let (st1, m1_step) = spec_get_property_val(st_r, obj_val, k1);
    match m1_step {
        SpecExprStep::Val(m1) => {
            let (st2, done1): (SpecState, Option<SpecExprStep>) = if spec_is_callable(st1.heap, st1.intr.realm, m1) {
                let (st_c_raw, c1) = spec_eval_call(prog, m1, obj_val, seq![], st1);
                let st_c = spec_cap_fuel(st_c_raw, st1.fuel);
                match c1 {
                    SpecExprStep::Val(v1) => {
                        if !(v1 is Object) {
                            (st_c, Some(SpecExprStep::Val(v1)))
                        } else {
                            (st_c, None)
                        }
                    }
                    abrupt => (st_c, Some(abrupt)),
                }
            } else {
                (st1, None)
            };
            match done1 {
                Some(res1) => (spec_truncate_roots(st2, rbase), res1),
                None => {
                    let (st3, m2_step) = spec_get_property_val(st2, obj_val, k2);
                    match m2_step {
                        SpecExprStep::Val(m2) => {
                            if spec_is_callable(st3.heap, st3.intr.realm, m2) {
                                let (st4_raw, c2) = spec_eval_call(prog, m2, obj_val, seq![], st3);
                                let st4 = spec_truncate_roots(spec_cap_fuel(st4_raw, st3.fuel), rbase);
                                match c2 {
                                    SpecExprStep::Val(v2) => {
                                        if !(v2 is Object) {
                                            (st4, SpecExprStep::Val(v2))
                                        } else {
                                            spec_throw_error(st4, ErrorKind::TypeError, spec_k_empty())
                                        }
                                    }
                                    abrupt => (st4, abrupt),
                                }
                            } else {
                                let st4 = spec_truncate_roots(st3, rbase);
                                spec_throw_error(st4, ErrorKind::TypeError, spec_k_empty())
                            }
                        }
                        abrupt2 => (spec_truncate_roots(st3, rbase), abrupt2),
                    }
                }
            }
        }
        abrupt1 => (spec_truncate_roots(st1, rbase), abrupt1),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(25)]
pub fn eval_to_primitive_obj(
    prog: &Program,
    oid: ObjId,
    prefer_string: bool,
    st: &mut VmState,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_eval_to_primitive_obj(prog@, oid, prefer_string, old(st)@),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        !(res@ is OutOfFuel) && old(st).fuel > 0 ==> final(st).fuel <= old(st).fuel,
        (res@ is Val) ==> !((res@->Val_0) is Object),
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 2nat, 0nat,
{
    reveal(spec_eval_to_primitive_obj_inner);
    let rbase = st.temp_roots.len();
    let obj_val = Val::Object(oid);
    st.push_root(&obj_val);
    let k1 = if prefer_string { k_to_string() } else { k_value_of() };
    let k2 = if prefer_string { k_value_of() } else { k_to_string() };
    let empty_args: Vec<Val> = Vec::new();
    proof { assert(spec_vals_view(empty_args@) =~= Seq::<SpecVal>::empty()); }

    let m1_step = get_property_val_exec(st, &obj_val, &k1);
    let m1 = match m1_step {
        ExprStep::Val(v) => v,
        abrupt1 => {
            st.truncate_roots(rbase);
            return abrupt1;
        }
    };
    if is_callable_exec(&st.heap, st.intr.realm, &m1) {
        let c1 = eval_call(prog, m1, Val::Object(oid), &empty_args, st);
        match c1 {
            ExprStep::Val(v1) => {
                if !matches!(v1, Val::Object(_)) {
                    st.truncate_roots(rbase);
                    return ExprStep::Val(v1);
                }
            }
            abrupt => {
                st.truncate_roots(rbase);
                return abrupt;
            }
        }
    }

    let m2_step = get_property_val_exec(st, &obj_val, &k2);
    let m2 = match m2_step {
        ExprStep::Val(v) => v,
        abrupt2 => {
            st.truncate_roots(rbase);
            return abrupt2;
        }
    };
    if is_callable_exec(&st.heap, st.intr.realm, &m2) {
        let c2 = eval_call(prog, m2, Val::Object(oid), &empty_args, st);
        st.truncate_roots(rbase);
        match c2 {
            ExprStep::Val(v2) => {
                if !matches!(v2, Val::Object(_)) {
                    ExprStep::Val(v2)
                } else {
                    throw_error_exec(st, ErrorKind::TypeError, k_empty())
                }
            }
            abrupt => abrupt,
        }
    } else {
        st.truncate_roots(rbase);
        throw_error_exec(st, ErrorKind::TypeError, k_empty())
    }
}

pub open spec fn spec_eval_to_primitive(
    prog: SpecProgram,
    val: SpecVal,
    prefer_string: bool,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 2nat, 2nat,
{
    match val {
        SpecVal::Object(oid) => {
            let (st1, r) = spec_eval_to_primitive_obj(prog, oid, prefer_string, st);
            (spec_cap_fuel(st1, st.fuel), r)
        }
        _ => (st, SpecExprStep::Val(val)),
    }
}

pub fn eval_to_primitive(
    prog: &Program,
    val: Val,
    prefer_string: bool,
    st: &mut VmState,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_eval_to_primitive(prog@, val@, prefer_string, old(st)@),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        (res@ is Val) ==> !((res@->Val_0) is Object),
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 2nat, 2nat,
{
    match val {
        Val::Object(oid) => eval_to_primitive_obj(prog, oid, prefer_string, st),
        _ => ExprStep::Val(val),
    }
}

pub open spec fn spec_eval_to_number(
    prog: SpecProgram,
    val: SpecVal,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 2nat, 3nat,
{
    let (st1_raw, pstep) = spec_eval_to_primitive(prog, val, false, st);
    let st1 = spec_cap_fuel(st1_raw, st.fuel);
    match pstep {
        SpecExprStep::Val(pv) => (st1, SpecExprStep::Val(SpecVal::Number(spec_prim_to_number(pv)))),
        abrupt => (st1, abrupt),
    }
}

pub fn eval_to_number(
    prog: &Program,
    val: Val,
    st: &mut VmState,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_eval_to_number(prog@, val@, old(st)@),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        (res@ is Val) ==> ((res@->Val_0) is Number),
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 2nat, 3nat,
{
    match eval_to_primitive(prog, val, false, st) {
        ExprStep::Val(pv) => ExprStep::Val(Val::Number(prim_to_number(&pv))),
        abrupt => abrupt,
    }
}

pub open spec fn spec_eval_to_string(
    prog: SpecProgram,
    val: SpecVal,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 2nat, 3nat,
{
    let (st1_raw, pstep) = spec_eval_to_primitive(prog, val, true, st);
    let st1 = spec_cap_fuel(st1_raw, st.fuel);
    match pstep {
        SpecExprStep::Val(pv) => (st1, SpecExprStep::Val(SpecVal::Str(spec_prim_to_string(pv)))),
        abrupt => (st1, abrupt),
    }
}

pub fn eval_to_string(
    prog: &Program,
    val: Val,
    st: &mut VmState,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_eval_to_string(prog@, val@, old(st)@),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        (res@ is Val) ==> ((res@->Val_0) is Str),
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 2nat, 3nat,
{
    match eval_to_primitive(prog, val, true, st) {
        ExprStep::Val(pv) => ExprStep::Val(Val::Str(prim_to_js_str(&pv))),
        abrupt => abrupt,
    }
}

pub open spec fn spec_eval_loose_eq(
    prog: SpecProgram,
    lhs: SpecVal,
    rhs: SpecVal,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 2nat, 5nat,
{
    spec_eval_loose_eq_inner(prog, lhs, rhs, st)
}

#[verifier::opaque]
pub open spec fn spec_eval_loose_eq_inner(
    prog: SpecProgram,
    lhs: SpecVal,
    rhs: SpecVal,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 2nat, 4nat,
{
    match (&lhs, &rhs) {
        (SpecVal::Object(a), SpecVal::Object(b)) =>
            (st, SpecExprStep::Val(SpecVal::Bool(a.0 == b.0))),
        (SpecVal::Undefined, SpecVal::Undefined)
        | (SpecVal::Null, SpecVal::Null)
        | (SpecVal::Undefined, SpecVal::Null)
        | (SpecVal::Null, SpecVal::Undefined) =>
            (st, SpecExprStep::Val(SpecVal::Bool(true))),
        (SpecVal::Undefined, _)
        | (SpecVal::Null, _)
        | (_, SpecVal::Undefined)
        | (_, SpecVal::Null) =>
            (st, SpecExprStep::Val(SpecVal::Bool(false))),
        (SpecVal::Object(_), _) => {
            let rbase = st.temp_roots.len();
            let st_r = spec_push_root(st, rhs);
            let (st1_raw, lstep) = spec_eval_to_primitive(prog, lhs, false, st_r);
            let st1 = spec_truncate_roots(spec_cap_fuel(st1_raw, st.fuel), rbase);
            match lstep {
                SpecExprStep::Val(lp) => (st1, SpecExprStep::Val(SpecVal::Bool(spec_loose_eq_prim(lp, rhs)))),
                abrupt => (st1, abrupt),
            }
        }
        (_, SpecVal::Object(_)) => {
            let rbase = st.temp_roots.len();
            let st_r = spec_push_root(st, lhs);
            let (st1_raw, rstep) = spec_eval_to_primitive(prog, rhs, false, st_r);
            let st1 = spec_truncate_roots(spec_cap_fuel(st1_raw, st.fuel), rbase);
            match rstep {
                SpecExprStep::Val(rp) => (st1, SpecExprStep::Val(SpecVal::Bool(spec_loose_eq_prim(lhs, rp)))),
                abrupt => (st1, abrupt),
            }
        }
        _ => (st, SpecExprStep::Val(SpecVal::Bool(spec_loose_eq_prim(lhs, rhs)))),
    }
}

pub fn eval_loose_eq(
    prog: &Program,
    lhs: Val,
    rhs: Val,
    st: &mut VmState,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_eval_loose_eq(prog@, lhs@, rhs@, old(st)@),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        (res@ is Val) ==> ((res@->Val_0) is Bool),
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 2nat, 4nat,
{
    reveal(spec_eval_loose_eq_inner);
    match (&lhs, &rhs) {
        (Val::Object(a), Val::Object(b)) => ExprStep::Val(Val::Bool(a.0 == b.0)),
        (Val::Undefined, Val::Undefined)
        | (Val::Null, Val::Null)
        | (Val::Undefined, Val::Null)
        | (Val::Null, Val::Undefined) => ExprStep::Val(Val::Bool(true)),
        (Val::Undefined, _)
        | (Val::Null, _)
        | (_, Val::Undefined)
        | (_, Val::Null) => ExprStep::Val(Val::Bool(false)),
        (Val::Object(_), _) => {
            let rbase = st.temp_roots.len();
            st.push_root(&rhs);
            let lstep = eval_to_primitive(prog, lhs, false, st);
            st.truncate_roots(rbase);
            match lstep {
                ExprStep::Val(lp) => ExprStep::Val(Val::Bool(val_loose_eq_prim(&lp, &rhs))),
                abrupt => abrupt,
            }
        }
        (_, Val::Object(_)) => {
            let rbase = st.temp_roots.len();
            st.push_root(&lhs);
            let rstep = eval_to_primitive(prog, rhs, false, st);
            st.truncate_roots(rbase);
            match rstep {
                ExprStep::Val(rp) => ExprStep::Val(Val::Bool(val_loose_eq_prim(&lhs, &rp))),
                abrupt => abrupt,
            }
        }
        _ => ExprStep::Val(Val::Bool(val_loose_eq_prim(&lhs, &rhs))),
    }
}

pub open spec fn spec_prim_less_than(a: SpecVal, b: SpecVal) -> Option<bool> {
    match (a, b) {
        (SpecVal::Str(sa), SpecVal::Str(sb)) => Some(spec_str_lt(sa, sb)),
        (pa, pb) => spec_num_less_than(spec_prim_to_number(pa), spec_prim_to_number(pb)),
    }
}

fn prim_less_than_exec(a: &Val, b: &Val) -> (r: Option<bool>)
    ensures r == spec_prim_less_than(a@, b@),
{
    match (a, b) {
        (Val::Str(sa), Val::Str(sb)) => Some(js_str_lt(sa, sb)),
        (pa, pb) => num_less_than(prim_to_number(pa), prim_to_number(pb)),
    }
}

pub open spec fn spec_eval_binop_add_rel(
    prog: SpecProgram,
    op: BinOp,
    lv: SpecVal,
    rv: SpecVal,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 2nat, 5nat,
{
    spec_eval_binop_add_rel_inner(prog, op, lv, rv, st)
}

#[verifier::opaque]
pub open spec fn spec_eval_binop_add_rel_inner(
    prog: SpecProgram,
    op: BinOp,
    lv: SpecVal,
    rv: SpecVal,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 2nat, 4nat,
{
    let rbase = st.temp_roots.len();
    let st_r1 = spec_push_root(st, rv);
    let (st1_raw, lp_step) = spec_eval_to_primitive(prog, lv, false, st_r1);
    let st1 = spec_truncate_roots(spec_cap_fuel(st1_raw, st.fuel), rbase);
    match lp_step {
        SpecExprStep::Val(lp) => {
            let st_r2 = spec_push_root(st1, lp);
            let (st2_raw, rp_step) = spec_eval_to_primitive(prog, rv, false, st_r2);
            let st2 = spec_truncate_roots(spec_cap_fuel(st2_raw, st1.fuel), rbase);
            match rp_step {
                SpecExprStep::Val(rp) => match op {
                    BinOp::Add => {
                        if (lp is Str) || (rp is Str) {
                            let ls = spec_prim_to_string(lp);
                            let rs = spec_prim_to_string(rp);
                            (st2, SpecExprStep::Val(SpecVal::Str(ls + rs)))
                        } else {
                            let ln = spec_prim_to_number(lp);
                            let rn = spec_prim_to_number(rp);
                            (st2, SpecExprStep::Val(SpecVal::Number(spec_num_add(ln, rn))))
                        }
                    }
                    BinOp::Lt => match spec_prim_less_than(lp, rp) {
                        Some(b) => (st2, SpecExprStep::Val(SpecVal::Bool(b))),
                        None => (st2, SpecExprStep::Val(SpecVal::Bool(false))),
                    },
                    BinOp::Gt => match spec_prim_less_than(rp, lp) {
                        Some(b) => (st2, SpecExprStep::Val(SpecVal::Bool(b))),
                        None => (st2, SpecExprStep::Val(SpecVal::Bool(false))),
                    },
                    BinOp::Le => match spec_prim_less_than(rp, lp) {
                        Some(false) => (st2, SpecExprStep::Val(SpecVal::Bool(true))),
                        _ => (st2, SpecExprStep::Val(SpecVal::Bool(false))),
                    },
                    _ => match spec_prim_less_than(lp, rp) {
                        Some(false) => (st2, SpecExprStep::Val(SpecVal::Bool(true))),
                        _ => (st2, SpecExprStep::Val(SpecVal::Bool(false))),
                    },
                },
                abrupt2 => (st2, abrupt2),
            }
        }
        abrupt1 => (st1, abrupt1),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(25)]
fn eval_binop_add_rel(
    prog: &Program,
    op: BinOp,
    lv: Val,
    rv: Val,
    st: &mut VmState,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_eval_binop_add_rel(prog@, op, lv@, rv@, old(st)@),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 2nat, 4nat,
{
    reveal(spec_eval_binop_add_rel_inner);
    let rbase = st.temp_roots.len();
    st.push_root(&rv);
    let lp_step = eval_to_primitive(prog, lv, false, st);
    st.truncate_roots(rbase);
    let lp = match lp_step {
        ExprStep::Val(v) => v,
        abrupt1 => return abrupt1,
    };
    st.push_root(&lp);
    let rp_step = eval_to_primitive(prog, rv, false, st);
    st.truncate_roots(rbase);
    let rp = match rp_step {
        ExprStep::Val(v) => v,
        abrupt2 => return abrupt2,
    };
    match op {
        BinOp::Add => {
            if matches!(lp, Val::Str(_)) || matches!(rp, Val::Str(_)) {
                let ls = prim_to_js_str(&lp);
                let rs = prim_to_js_str(&rp);
                ExprStep::Val(Val::Str(js_str_concat(&ls, &rs)))
            } else {
                let ln = prim_to_number(&lp);
                let rn = prim_to_number(&rp);
                ExprStep::Val(Val::Number(num_add(ln, rn)))
            }
        }
        BinOp::Lt => match prim_less_than_exec(&lp, &rp) {
            Some(b) => ExprStep::Val(Val::Bool(b)),
            None => ExprStep::Val(Val::Bool(false)),
        },
        BinOp::Gt => match prim_less_than_exec(&rp, &lp) {
            Some(b) => ExprStep::Val(Val::Bool(b)),
            None => ExprStep::Val(Val::Bool(false)),
        },
        BinOp::Le => match prim_less_than_exec(&rp, &lp) {
            Some(false) => ExprStep::Val(Val::Bool(true)),
            _ => ExprStep::Val(Val::Bool(false)),
        },
        _ => match prim_less_than_exec(&lp, &rp) {
            Some(false) => ExprStep::Val(Val::Bool(true)),
            _ => ExprStep::Val(Val::Bool(false)),
        },
    }
}

pub open spec fn spec_eval_binop_numeric(
    prog: SpecProgram,
    op: BinOp,
    lv: SpecVal,
    rv: SpecVal,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 2nat, 5nat,
{
    spec_eval_binop_numeric_inner(prog, op, lv, rv, st)
}

#[verifier::opaque]
pub open spec fn spec_eval_binop_numeric_inner(
    prog: SpecProgram,
    op: BinOp,
    lv: SpecVal,
    rv: SpecVal,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 2nat, 4nat,
{
    let rbase = st.temp_roots.len();
    let st_r = spec_push_root(st, rv);
    let (st1_raw, ln_step) = spec_eval_to_number(prog, lv, st_r);
    let st1 = spec_truncate_roots(spec_cap_fuel(st1_raw, st.fuel), rbase);
    match ln_step {
        SpecExprStep::Val(SpecVal::Number(ln)) => {
            let (st2_raw, rn_step) = spec_eval_to_number(prog, rv, st1);
            let st2 = spec_cap_fuel(st2_raw, st1.fuel);
            match rn_step {
                SpecExprStep::Val(SpecVal::Number(rn)) => match op {
                    BinOp::Sub => (st2, SpecExprStep::Val(SpecVal::Number(spec_num_sub(ln, rn)))),
                    BinOp::Mul => (st2, SpecExprStep::Val(SpecVal::Number(spec_num_mul(ln, rn)))),
                    BinOp::Div => (st2, SpecExprStep::Val(SpecVal::Number(spec_num_div(ln, rn)))),
                    BinOp::Rem => (st2, SpecExprStep::Val(SpecVal::Number(spec_num_rem(ln, rn)))),
                    BinOp::Exp => match spec_num_exp(ln, rn) {
                        Some(res) => (st2, SpecExprStep::Val(SpecVal::Number(res))),
                        None => (st2, SpecExprStep::Unsupported(UnsupportedFeature::NonIntegerExponentiation)),
                    },
                    BinOp::BitAnd => (st2, SpecExprStep::Val(SpecVal::Number(spec_num_bit_and(ln, rn)))),
                    BinOp::BitOr => (st2, SpecExprStep::Val(SpecVal::Number(spec_num_bit_or(ln, rn)))),
                    BinOp::BitXor => (st2, SpecExprStep::Val(SpecVal::Number(spec_num_bit_xor(ln, rn)))),
                    BinOp::Shl => (st2, SpecExprStep::Val(SpecVal::Number(spec_num_shl(ln, rn)))),
                    BinOp::Shr => (st2, SpecExprStep::Val(SpecVal::Number(spec_num_shr(ln, rn)))),
                    _ => (st2, SpecExprStep::Val(SpecVal::Number(spec_num_ushr(ln, rn)))),
                },
                other2 => (st2, other2),
            }
        }
        other1 => (st1, other1),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(25)]
fn eval_binop_numeric(
    prog: &Program,
    op: BinOp,
    lv: Val,
    rv: Val,
    st: &mut VmState,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_eval_binop_numeric(prog@, op, lv@, rv@, old(st)@),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 2nat, 4nat,
{
    reveal(spec_eval_binop_numeric_inner);
    let rbase = st.temp_roots.len();
    st.push_root(&rv);
    let ln_step = eval_to_number(prog, lv, st);
    st.truncate_roots(rbase);
    let ln = match ln_step {
        ExprStep::Val(Val::Number(n)) => n,
        other1 => return other1,
    };
    let rn_step = eval_to_number(prog, rv, st);
    let rn = match rn_step {
        ExprStep::Val(Val::Number(n)) => n,
        other2 => return other2,
    };
    match op {
        BinOp::Sub => ExprStep::Val(Val::Number(num_sub(ln, rn))),
        BinOp::Mul => ExprStep::Val(Val::Number(num_mul(ln, rn))),
        BinOp::Div => ExprStep::Val(Val::Number(num_div(ln, rn))),
        BinOp::Rem => ExprStep::Val(Val::Number(num_rem(ln, rn))),
        BinOp::Exp => match num_exp(ln, rn) {
            Some(res) => ExprStep::Val(Val::Number(res)),
            None => ExprStep::Unsupported(UnsupportedFeature::NonIntegerExponentiation),
        },
        BinOp::BitAnd => ExprStep::Val(Val::Number(num_bit_and(ln, rn))),
        BinOp::BitOr => ExprStep::Val(Val::Number(num_bit_or(ln, rn))),
        BinOp::BitXor => ExprStep::Val(Val::Number(num_bit_xor(ln, rn))),
        BinOp::Shl => ExprStep::Val(Val::Number(num_shl(ln, rn))),
        BinOp::Shr => ExprStep::Val(Val::Number(num_shr(ln, rn))),
        _ => ExprStep::Val(Val::Number(num_ushr(ln, rn))),
    }
}

pub open spec fn spec_eval_apply_binop(
    prog: SpecProgram,
    op: BinOp,
    lv: SpecVal,
    rv: SpecVal,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 2nat, 7nat,
{
    spec_eval_apply_binop_inner(prog, op, lv, rv, st)
}

#[verifier::opaque]
pub open spec fn spec_eval_apply_binop_inner(
    prog: SpecProgram,
    op: BinOp,
    lv: SpecVal,
    rv: SpecVal,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 2nat, 6nat,
{
    match op {
        BinOp::EqStrict => (st, SpecExprStep::Val(SpecVal::Bool(spec_strict_eq(lv, rv)))),
        BinOp::NeStrict => (st, SpecExprStep::Val(SpecVal::Bool(!spec_strict_eq(lv, rv)))),
        BinOp::EqLoose => {
            let (st1, r) = spec_eval_loose_eq(prog, lv, rv, st);
            (spec_cap_fuel(st1, st.fuel), r)
        }
        BinOp::NeLoose => {
            let (st1_raw, r) = spec_eval_loose_eq(prog, lv, rv, st);
            let st1 = spec_cap_fuel(st1_raw, st.fuel);
            match r {
                SpecExprStep::Val(SpecVal::Bool(b)) => (st1, SpecExprStep::Val(SpecVal::Bool(!b))),
                other => (st1, other),
            }
        }
        BinOp::Add | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
            let (st1, r) = spec_eval_binop_add_rel(prog, op, lv, rv, st);
            (spec_cap_fuel(st1, st.fuel), r)
        }
        BinOp::In => {
            match rv {
                SpecVal::Object(roid) => {
                    let rbase = st.temp_roots.len();
                    let st_r = spec_push_root(st, rv);
                    let (st1_raw, kstep) = spec_eval_to_string(prog, lv, st_r);
                    let st1 = spec_truncate_roots(spec_cap_fuel(st1_raw, st.fuel), rbase);
                    match kstep {
                        SpecExprStep::Val(SpecVal::Str(ks)) => {
                            match spec_heap_has_prop(st1.heap, st1.intr.realm, roid, ks) {
                                HeapWriteRes::Ok(b) => (st1, SpecExprStep::Val(SpecVal::Bool(b))),
                                _ => spec_throw_error(st1, ErrorKind::TypeError, spec_k_empty()),
                            }
                        }
                        other => (st1, other),
                    }
                }
                _ => spec_throw_error(st, ErrorKind::TypeError, spec_k_empty()),
            }
        }
        BinOp::Instanceof => {
            if !spec_is_callable(st.heap, st.intr.realm, rv) {
                spec_throw_error(st, ErrorKind::TypeError, spec_k_empty())
            } else {
                let rbase = st.temp_roots.len();
                let st_r = spec_push_root(st, lv);
                let (st1, pstep) = spec_get_property_val(st_r, rv, spec_k_prototype());
                let st2 = spec_truncate_roots(st1, rbase);
                match pstep {
                    SpecExprStep::Val(SpecVal::Object(target_proto)) => {
                        match lv {
                            SpecVal::Object(loid) => {
                                let steps = if st2.heap.slots.len() == 0 { 1nat } else { st2.heap.slots.len() };
                                match spec_is_instance_of_steps(st2.heap, st2.intr.realm, loid, target_proto, steps) {
                                    HeapWriteRes::Ok(b) => (st2, SpecExprStep::Val(SpecVal::Bool(b))),
                                    _ => spec_throw_error(st2, ErrorKind::TypeError, spec_k_empty()),
                                }
                            }
                            _ => (st2, SpecExprStep::Val(SpecVal::Bool(false))),
                        }
                    }
                    SpecExprStep::Val(_) => spec_throw_error(st2, ErrorKind::TypeError, spec_k_empty()),
                    abrupt => (st2, abrupt),
                }
            }
        }
        _ => {
            let (st1, r) = spec_eval_binop_numeric(prog, op, lv, rv, st);
            (spec_cap_fuel(st1, st.fuel), r)
        }
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(25)]
pub fn eval_apply_binop(
    prog: &Program,
    op: BinOp,
    lv: Val,
    rv: Val,
    st: &mut VmState,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_eval_apply_binop(prog@, op, lv@, rv@, old(st)@),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 2nat, 7nat,
{
    reveal(spec_eval_apply_binop_inner);
    match op {
        BinOp::EqStrict => ExprStep::Val(Val::Bool(val_strict_eq(&lv, &rv))),
        BinOp::NeStrict => ExprStep::Val(Val::Bool(!val_strict_eq(&lv, &rv))),
        BinOp::EqLoose => eval_loose_eq(prog, lv, rv, st),
        BinOp::NeLoose => {
            match eval_loose_eq(prog, lv, rv, st) {
                ExprStep::Val(Val::Bool(b)) => ExprStep::Val(Val::Bool(!b)),
                other => other,
            }
        }
        BinOp::Add | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge =>
            eval_binop_add_rel(prog, op, lv, rv, st),
        BinOp::In => {
            match rv {
                Val::Object(roid) => {
                    let rbase = st.temp_roots.len();
                    st.push_root(&rv);
                    let kstep = eval_to_string(prog, lv, st);
                    st.truncate_roots(rbase);
                    match kstep {
                        ExprStep::Val(Val::Str(ks)) => {
                            match st.heap.has_prop(st.intr.realm, roid, &ks) {
                                HeapWriteRes::Ok(b) => ExprStep::Val(Val::Bool(b)),
                                _ => throw_error_exec(st, ErrorKind::TypeError, k_empty()),
                            }
                        }
                        other => other,
                    }
                }
                _ => throw_error_exec(st, ErrorKind::TypeError, k_empty()),
            }
        }
        BinOp::Instanceof => {
            if !is_callable_exec(&st.heap, st.intr.realm, &rv) {
                throw_error_exec(st, ErrorKind::TypeError, k_empty())
            } else {
                let rbase = st.temp_roots.len();
                st.push_root(&lv);
                let pk = k_prototype();
                let pstep = get_property_val_exec(st, &rv, &pk);
                st.truncate_roots(rbase);
                match pstep {
                    ExprStep::Val(Val::Object(target_proto)) => {
                        match lv {
                            Val::Object(loid) => {
                                let steps = if st.heap.slots.len() == 0 { 1 } else { st.heap.slots.len() };
                                match st.heap.is_instance_of_steps(st.intr.realm, loid, target_proto, steps) {
                                    HeapWriteRes::Ok(b) => ExprStep::Val(Val::Bool(b)),
                                    _ => throw_error_exec(st, ErrorKind::TypeError, k_empty()),
                                }
                            }
                            _ => ExprStep::Val(Val::Bool(false)),
                        }
                    }
                    ExprStep::Val(_) => throw_error_exec(st, ErrorKind::TypeError, k_empty()),
                    abrupt => abrupt,
                }
            }
        }
        _ => eval_binop_numeric(prog, op, lv, rv, st),
    }
}

pub open spec fn spec_eval_set_property_val(
    prog: SpecProgram,
    base: SpecVal,
    key: Seq<u16>,
    val: SpecVal,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 2nat, 9nat,
{
    spec_eval_set_property_val_inner(prog, base, key, val, st)
}

#[verifier::opaque]
pub open spec fn spec_eval_set_property_val_inner(
    prog: SpecProgram,
    base: SpecVal,
    key: Seq<u16>,
    val: SpecVal,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 2nat, 8nat,
{
    match base {
        SpecVal::Object(oid) => {
            if spec_is_live_same_realm_array(st.heap, st.intr.realm, oid) && spec_is_length_key(key) {
                let rbase = st.temp_roots.len();
                let st_r = spec_push_root(spec_push_root(st, base), val);
                let (st1_raw, u_step) = spec_eval_to_number(prog, val, st_r);
                let st1 = spec_cap_fuel(st1_raw, st.fuel);
                match u_step {
                    SpecExprStep::Val(SpecVal::Number(u_num)) => {
                        let new_len: usize = spec_to_uint32(u_num) as usize;
                        let (st2_raw, n_step) = spec_eval_to_number(prog, val, st1);
                        let st2 = spec_truncate_roots(spec_cap_fuel(st2_raw, st1.fuel), rbase);
                        match n_step {
                            SpecExprStep::Val(SpecVal::Number(num_len)) => {
                                if !spec_num_equal(spec_num_from_usize(new_len), num_len) {
                                    spec_throw_error(st2, ErrorKind::RangeError, spec_k_empty())
                                } else {
                                    let (h3, wres) = spec_heap_set_array_length(st2.heap, st2.intr.realm, oid, new_len);
                                    let st3 = SpecState { heap: h3, ..st2 };
                                    match wres {
                                        HeapWriteRes::Ok(ok) => {
                                            if !ok && st3.strict {
                                                spec_throw_error(st3, ErrorKind::TypeError, spec_k_empty())
                                            } else {
                                                (st3, SpecExprStep::Val(val))
                                            }
                                        }
                                        _ => spec_throw_error(st3, ErrorKind::TypeError, spec_k_empty()),
                                    }
                                }
                            }
                            other2 => (st2, other2),
                        }
                    }
                    other1 => (spec_truncate_roots(st1, rbase), other1),
                }
            } else {
                spec_set_property_val(st, base, key, val)
            }
        }
        _ => spec_set_property_val(st, base, key, val),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(25)]
pub fn eval_set_property_val(
    prog: &Program,
    base: Val,
    key: JsStr,
    val: Val,
    st: &mut VmState,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_eval_set_property_val(prog@, base@, key@, val@, old(st)@),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 2nat, 8nat,
{
    reveal(spec_eval_set_property_val_inner);
    if let Val::Object(oid) = base {
        if st.heap.is_live_same_realm_array(st.intr.realm, oid) && is_length_key(&key) {
            let rbase = st.temp_roots.len();
            st.push_root(&base);
            st.push_root(&val);
            let u_step = eval_to_number(prog, clone_val(&val), st);
            let u_num = match u_step {
                ExprStep::Val(Val::Number(n)) => n,
                other1 => {
                    st.truncate_roots(rbase);
                    return other1;
                }
            };
            let new_len: usize = num_to_uint32(u_num) as usize;
            let n_step = eval_to_number(prog, clone_val(&val), st);
            st.truncate_roots(rbase);
            let num_len = match n_step {
                ExprStep::Val(Val::Number(n)) => n,
                other2 => return other2,
            };
            if !num_equal(num_from_usize(new_len), num_len) {
                return throw_error_exec(st, ErrorKind::RangeError, k_empty());
            }
            let wres = st.heap.set_array_length(st.intr.realm, oid, new_len);
            return match wres {
                HeapWriteRes::Ok(ok) => {
                    if !ok && st.strict {
                        throw_error_exec(st, ErrorKind::TypeError, k_empty())
                    } else {
                        ExprStep::Val(val)
                    }
                }
                _ => throw_error_exec(st, ErrorKind::TypeError, k_empty()),
            };
        }
    }
    set_property_val_exec(st, &base, key, val)
}

// ---------------------------------------------------------------------------
// Rank 3 & Rank 4: Built-in Intrinsics (`eval_builtin_call`) & `new` (`eval_new`)
// ---------------------------------------------------------------------------

pub open spec fn spec_eval_array_join_loop(
    prog: SpecProgram,
    this_val: SpecVal,
    sep: Seq<u16>,
    len: usize,
    idx: nat,
    acc: Seq<u16>,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 3nat, (len as nat) - idx,
{
    if idx >= (len as nat) {
        (st, SpecExprStep::Val(SpecVal::Str(acc)))
    } else {
        let with_sep = if idx > 0 { acc + sep } else { acc };
        let (st1, estep) = spec_get_property_val(st, this_val, spec_index_key(idx as usize));
        match estep {
            SpecExprStep::Val(ev) => {
                if (ev is Undefined) || (ev is Null) {
                    spec_eval_array_join_loop(prog, this_val, sep, len, idx + 1, with_sep, st1)
                } else {
                    let (st2_raw, sstep) = spec_eval_to_string(prog, ev, st1);
                    let st2 = spec_cap_fuel(st2_raw, st1.fuel);
                    match sstep {
                        SpecExprStep::Val(SpecVal::Str(es)) =>
                            spec_eval_array_join_loop(prog, this_val, sep, len, idx + 1, with_sep + es, st2),
                        other => (st2, other),
                    }
                }
            }
            abrupt => (st1, abrupt),
        }
    }
}

fn eval_array_join_loop(
    prog: &Program,
    this_val: &Val,
    sep: &JsStr,
    len: usize,
    st: &mut VmState,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_eval_array_join_loop(prog@, this_val@, sep@, len, 0, seq![], old(st)@),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 3nat, len as nat,
{
    let mut idx: usize = 0;
    let mut acc = k_empty();
    while idx < len
        invariant
            idx <= len,
            st.fuel <= old(st).fuel,
            env_wf(old(st)@.envs) ==> env_wf(st@.envs),
            spec_eval_array_join_loop(prog@, this_val@, sep@, len, 0, seq![], old(st)@)
                == spec_eval_array_join_loop(prog@, this_val@, sep@, len, idx as nat, acc@, st@),
        decreases len - idx,
    {
        if idx > 0 {
            acc = js_str_concat(&acc, sep);
        }
        let ik = index_key_exec(idx);
        let estep = get_property_val_exec(st, this_val, &ik);
        match estep {
            ExprStep::Val(ev) => {
                if matches!(ev, Val::Undefined | Val::Null) {
                    idx += 1;
                } else {
                    let sstep = eval_to_string(prog, ev, st);
                    match sstep {
                        ExprStep::Val(Val::Str(es)) => {
                            acc = js_str_concat(&acc, &es);
                            idx += 1;
                        }
                        other => return other,
                    }
                }
            }
            abrupt => return abrupt,
        }
    }
    ExprStep::Val(Val::Str(acc))
}

#[verifier::opaque]
pub open spec fn spec_alloc_array_from_vals(
    vals: Seq<SpecVal>,
    st: SpecState,
) -> (SpecState, SpecExprStep) {
    let props = spec_build_indexed_props(vals, 0, seq![]);
    let obj = SpecHeapObject {
        realm: st.intr.realm,
        prototype: Some(st.intr.array_proto),
        extensible: true,
        kind: ObjectKind::Array { length: vals.len() as usize },
        props,
    };
    let (st2, ares) = spec_state_alloc_obj(st, obj);
    match ares {
        AllocRes::Ok(oid) => (st2, SpecExprStep::Val(SpecVal::Object(oid))),
        AllocRes::QuotaExceeded => (st2, SpecExprStep::HeapQuotaExceeded),
    }
}

pub open spec fn spec_build_indexed_props(
    vals: Seq<SpecVal>,
    idx: nat,
    acc: Seq<SpecPropEntry>,
) -> Seq<SpecPropEntry>
    decreases vals.len() - idx,
{
    if idx >= vals.len() {
        acc
    } else {
        let next_acc = acc.push(spec_prop_data(spec_index_key(idx as usize), vals[idx as int], true));
        spec_build_indexed_props(vals, idx + 1, next_acc)
    }
}

pub fn alloc_array_from_vals_exec(
    vals: &Vec<Val>,
    st: &mut VmState,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_alloc_array_from_vals(spec_vals_view(vals@), old(st)@),
        final(st).fuel == old(st).fuel,
        !(res@ is OutOfFuel),
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
{
    reveal(spec_alloc_array_from_vals);
    let n = vals.len();
    let mut ps: Vec<PropEntry> = Vec::new();
    let mut i: usize = 0;
    let ghost svals = spec_vals_view(vals@);
    proof { assert(spec_props_view(ps@) =~= Seq::<SpecPropEntry>::empty()); }
    while i < n
        invariant
            i <= n == vals@.len(),
            svals == spec_vals_view(vals@),
            spec_build_indexed_props(svals, 0, seq![])
                == spec_build_indexed_props(svals, i as nat, spec_props_view(ps@)),
        decreases n - i,
    {
        let ghost pre = spec_props_view(ps@);
        let ik = index_key_exec(i);
        let cv = clone_val(&vals[i]);
        ps.push(make_prop_data(ik, cv, true));
        proof {
            assert(spec_props_view(ps@) =~= pre.push(
                spec_prop_data(spec_index_key(i), svals[i as int], true)
            ));
        }
        i += 1;
    }
    let obj = HeapObject {
        realm: st.intr.realm,
        prototype: Some(st.intr.array_proto),
        extensible: true,
        kind: ObjectKind::Array { length: n },
        props: ps,
    };
    match st.alloc_obj(obj) {
        AllocRes::Ok(oid) => ExprStep::Val(Val::Object(oid)),
        AllocRes::QuotaExceeded => ExprStep::HeapQuotaExceeded,
    }
}

pub open spec fn spec_strs_to_vals(ks: Seq<Seq<u16>>) -> Seq<SpecVal> {
    Seq::new(ks.len(), |i: int| SpecVal::Str(ks[i]))
}

fn strs_to_vals_exec(ks: &Vec<JsStr>) -> (r: Vec<Val>)
    ensures spec_vals_view(r@) == spec_strs_to_vals(spec_str_seq_view(ks@)),
{
    let n = ks.len();
    let mut out: Vec<Val> = Vec::new();
    let mut i: usize = 0;
    let ghost sks = spec_str_seq_view(ks@);
    while i < n
        invariant
            i <= n == ks@.len(),
            sks == spec_str_seq_view(ks@),
            out@.len() == i,
            forall|j: int| 0 <= j < i as int ==> out@[j]@ == SpecVal::Str(sks[j]),
        decreases n - i,
    {
        out.push(Val::Str(clone_js_str(&ks[i])));
        i += 1;
    }
    proof { assert(spec_vals_view(out@) =~= spec_strs_to_vals(sks)); }
    out
}

pub open spec fn spec_array_push_loop(
    this_val: SpecVal,
    base_len: usize,
    args: Seq<SpecVal>,
    idx: nat,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases args.len() - idx,
{
    if idx >= args.len() {
        let final_len = if idx <= (usize::MAX - base_len) as nat { (base_len as nat + idx) as usize } else { usize::MAX };
        let (st2, sres) = spec_set_property_val(
            st,
            this_val,
            spec_k_length(),
            SpecVal::Number(spec_num_from_usize(final_len)),
        );
        match sres {
            SpecExprStep::Val(_) => (st2, SpecExprStep::Val(SpecVal::Number(spec_num_from_usize(final_len)))),
            abrupt => (st2, abrupt),
        }
    } else {
        let pos = if idx <= (usize::MAX - base_len) as nat { (base_len as nat + idx) as usize } else { usize::MAX };
        let (st1, sres) = spec_set_property_val(st, this_val, spec_index_key(pos), args[idx as int]);
        match sres {
            SpecExprStep::Val(_) => spec_array_push_loop(this_val, base_len, args, idx + 1, st1),
            abrupt => (st1, abrupt),
        }
    }
}

fn array_push_loop_exec(
    this_val: &Val,
    base_len: usize,
    args: &Vec<Val>,
    st: &mut VmState,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_array_push_loop(this_val@, base_len, spec_vals_view(args@), 0, old(st)@),
        final(st).fuel == old(st).fuel,
        !(res@ is OutOfFuel),
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
{
    let n = args.len();
    let mut idx: usize = 0;
    let ghost sargs = spec_vals_view(args@);
    while idx < n
        invariant
            idx <= n == args@.len(),
            sargs == spec_vals_view(args@),
            st.fuel == old(st).fuel,
            env_wf(old(st)@.envs) ==> env_wf(st@.envs),
            spec_array_push_loop(this_val@, base_len, sargs, 0, old(st)@)
                == spec_array_push_loop(this_val@, base_len, sargs, idx as nat, st@),
        decreases n - idx,
    {
        let pos = if idx <= usize::MAX - base_len { base_len + idx } else { usize::MAX };
        let ik = index_key_exec(pos);
        let av = clone_val(&args[idx]);
        let sres = set_property_val_exec(st, this_val, ik, av);
        match &sres {
            ExprStep::Val(_) => {
                idx += 1;
            }
            _ => return sres,
        }
    }
    let final_len = if idx <= usize::MAX - base_len { base_len + idx } else { usize::MAX };
    let nval = Val::Number(num_from_usize(final_len));
    let sres = set_property_val_exec(st, this_val, k_length(), nval);
    match sres {
        ExprStep::Val(_) => ExprStep::Val(Val::Number(num_from_usize(final_len))),
        abrupt => abrupt,
    }
}

pub open spec fn spec_eval_builtin_array(
    prog: SpecProgram,
    builtin: BuiltinFn,
    this_val: SpecVal,
    args: Seq<SpecVal>,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 4nat, 1nat,
{
    spec_eval_builtin_array_inner(prog, builtin, this_val, args, st)
}

#[verifier::opaque]
pub open spec fn spec_eval_builtin_array_inner(
    prog: SpecProgram,
    builtin: BuiltinFn,
    this_val: SpecVal,
    args: Seq<SpecVal>,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 4nat, 0nat,
{
    match builtin {
        BuiltinFn::ArrayCtor => {
            if args.len() == 1 && (args[0] is Number) {
                let n = args[0]->Number_0;
                let ulen = spec_to_uint32(n) as usize;
                if !spec_num_equal(spec_num_from_usize(ulen), n) {
                    spec_throw_error(st, ErrorKind::RangeError, spec_k_empty())
                } else {
                    let obj = SpecHeapObject {
                        realm: st.intr.realm,
                        prototype: Some(st.intr.array_proto),
                        extensible: true,
                        kind: ObjectKind::Array { length: ulen },
                        props: seq![],
                    };
                    let (st2, ares) = spec_state_alloc_obj(st, obj);
                    match ares {
                        AllocRes::Ok(oid) => (st2, SpecExprStep::Val(SpecVal::Object(oid))),
                        AllocRes::QuotaExceeded => (st2, SpecExprStep::HeapQuotaExceeded),
                    }
                }
            } else {
                spec_alloc_array_from_vals(args, st)
            }
        }
        BuiltinFn::ArrayIsArray => {
            let a = if args.len() > 0 { args[0] } else { SpecVal::Undefined };
            let is_arr = match a {
                SpecVal::Object(oid) => {
                    if (oid.0 as int) >= st.heap.slots.len() {
                        false
                    } else {
                        match st.heap.slots[oid.0 as int] {
                            SpecSlot::Live(o) => o.realm == st.intr.realm && (o.kind is Array),
                            SpecSlot::Free => false,
                        }
                    }
                }
                _ => false,
            };
            (st, SpecExprStep::Val(SpecVal::Bool(is_arr)))
        }
        BuiltinFn::ArrayPush => {
            let (st1, lstep) = spec_get_property_val(st, this_val, spec_k_length());
            match lstep {
                SpecExprStep::Val(lv) => {
                    let rbase = st1.temp_roots.len();
                    let st_r = spec_push_root(st1, this_val);
                    let (st2_raw, nstep) = spec_eval_to_number(prog, lv, st_r);
                    let st2 = spec_truncate_roots(spec_cap_fuel(st2_raw, st1.fuel), rbase);
                    match nstep {
                        SpecExprStep::Val(SpecVal::Number(ln)) => {
                            let base_len = spec_to_uint32(ln) as usize;
                            spec_array_push_loop(this_val, base_len, args, 0, st2)
                        }
                        other => (st2, other),
                    }
                }
                abrupt => (st1, abrupt),
            }
        }
        BuiltinFn::ArrayPop => {
            let (st1, lstep) = spec_get_property_val(st, this_val, spec_k_length());
            match lstep {
                SpecExprStep::Val(lv) => {
                    let rbase = st1.temp_roots.len();
                    let st_r = spec_push_root(st1, this_val);
                    let (st2_raw, nstep) = spec_eval_to_number(prog, lv, st_r);
                    let st2 = spec_truncate_roots(spec_cap_fuel(st2_raw, st1.fuel), rbase);
                    match nstep {
                        SpecExprStep::Val(SpecVal::Number(ln)) => {
                            let len = spec_to_uint32(ln) as usize;
                            if len == 0 {
                                let (st3, sres) = spec_set_property_val(
                                    st2,
                                    this_val,
                                    spec_k_length(),
                                    SpecVal::Number(JsNum(POS_ZERO_BITS)),
                                );
                                match sres {
                                    SpecExprStep::Val(_) => (st3, SpecExprStep::Val(SpecVal::Undefined)),
                                    abrupt => (st3, abrupt),
                                }
                            } else {
                                let last_idx = (len - 1) as usize;
                                let ik = spec_index_key(last_idx);
                                let (st3, estep) = spec_get_property_val(st2, this_val, ik);
                                match estep {
                                    SpecExprStep::Val(elem) => {
                                        let st4 = match this_val {
                                            SpecVal::Object(oid) => {
                                                let (h4, _) = spec_heap_delete_prop(st3.heap, st3.intr.realm, oid, ik);
                                                SpecState { heap: h4, ..st3 }
                                            }
                                            _ => st3,
                                        };
                                        let (st5, sres) = spec_set_property_val(
                                            st4,
                                            this_val,
                                            spec_k_length(),
                                            SpecVal::Number(spec_num_from_usize(last_idx)),
                                        );
                                        match sres {
                                            SpecExprStep::Val(_) => (st5, SpecExprStep::Val(elem)),
                                            abrupt => (st5, abrupt),
                                        }
                                    }
                                    abrupt => (st3, abrupt),
                                }
                            }
                        }
                        other => (st2, other),
                    }
                }
                abrupt => (st1, abrupt),
            }
        }
        _ => {
            if (this_val is Undefined) || (this_val is Null) {
                spec_throw_error(st, ErrorKind::TypeError, spec_k_empty())
            } else {
                let rbase = st.temp_roots.len();
                let st_r = spec_push_root(st, this_val);
                let (st1, lstep) = spec_get_property_val(st_r, this_val, spec_k_length());
                match lstep {
                    SpecExprStep::Val(lv) => {
                        let (st2_raw, nstep) = spec_eval_to_number(prog, lv, st1);
                        let st2 = spec_cap_fuel(st2_raw, st1.fuel);
                        match nstep {
                            SpecExprStep::Val(SpecVal::Number(ln)) => {
                                let len = spec_to_uint32(ln) as usize;
                                let (st3, sep_step): (SpecState, SpecExprStep) = if args.len() == 0 || (args[0] is Undefined) {
                                    (st2, SpecExprStep::Val(SpecVal::Str(spec_k_comma())))
                                } else {
                                    let (s_raw, sr) = spec_eval_to_string(prog, args[0], st2);
                                    (spec_cap_fuel(s_raw, st2.fuel), sr)
                                };
                                match sep_step {
                                    SpecExprStep::Val(SpecVal::Str(sep)) => {
                                        let (st4_raw, jres) = spec_eval_array_join_loop(prog, this_val, sep, len, 0, seq![], st3);
                                        (spec_truncate_roots(spec_cap_fuel(st4_raw, st3.fuel), rbase), jres)
                                    }
                                    other => (spec_truncate_roots(st3, rbase), other),
                                }
                            }
                            other => (spec_truncate_roots(st2, rbase), other),
                        }
                    }
                    abrupt => (spec_truncate_roots(st1, rbase), abrupt),
                }
            }
        }
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
fn eval_builtin_array(
    prog: &Program,
    builtin: BuiltinFn,
    this_val: Val,
    args: &Vec<Val>,
    st: &mut VmState,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_eval_builtin_array(prog@, builtin, this_val@, spec_vals_view(args@), old(st)@),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 4nat, 0nat,
{
    reveal(spec_eval_builtin_array_inner);
    match builtin {
        BuiltinFn::ArrayCtor => {
            if args.len() == 1 && matches!(args[0], Val::Number(_)) {
                let n = match args[0] { Val::Number(x) => x, _ => JsNum(POS_ZERO_BITS) };
                let ulen = num_to_uint32(n) as usize;
                if !num_equal(num_from_usize(ulen), n) {
                    throw_error_exec(st, ErrorKind::RangeError, k_empty())
                } else {
                    let obj = HeapObject {
                        realm: st.intr.realm,
                        prototype: Some(st.intr.array_proto),
                        extensible: true,
                        kind: ObjectKind::Array { length: ulen },
                        props: Vec::new(),
                    };
                    proof { assert(obj@.props =~= seq![]); }
                    match st.alloc_obj(obj) {
                        AllocRes::Ok(oid) => ExprStep::Val(Val::Object(oid)),
                        AllocRes::QuotaExceeded => ExprStep::HeapQuotaExceeded,
                    }
                }
            } else {
                alloc_array_from_vals_exec(args, st)
            }
        }
        BuiltinFn::ArrayIsArray => {
            let a = if args.len() > 0 { clone_val(&args[0]) } else { Val::Undefined };
            let is_arr = match a {
                Val::Object(oid) => {
                    if oid.0 >= st.heap.slots.len() {
                        false
                    } else {
                        proof { assert(st@.heap.slots[oid.0 as int] == st.heap.slots@[oid.0 as int]@); }
                        match &st.heap.slots[oid.0] {
                            Slot::Live(o) => o.realm.0 == st.intr.realm.0 && matches!(o.kind, ObjectKind::Array { .. }),
                            Slot::Free => false,
                        }
                    }
                }
                _ => false,
            };
            ExprStep::Val(Val::Bool(is_arr))
        }
        BuiltinFn::ArrayPush => {
            let lk = k_length();
            let lstep = get_property_val_exec(st, &this_val, &lk);
            match lstep {
                ExprStep::Val(lv) => {
                    let rbase = st.temp_roots.len();
                    st.push_root(&this_val);
                    let nstep = eval_to_number(prog, lv, st);
                    st.truncate_roots(rbase);
                    match nstep {
                        ExprStep::Val(Val::Number(ln)) => {
                            let base_len = num_to_uint32(ln) as usize;
                            array_push_loop_exec(&this_val, base_len, args, st)
                        }
                        other => other,
                    }
                }
                abrupt => abrupt,
            }
        }
        BuiltinFn::ArrayPop => {
            let lk = k_length();
            let lstep = get_property_val_exec(st, &this_val, &lk);
            match lstep {
                ExprStep::Val(lv) => {
                    let rbase = st.temp_roots.len();
                    st.push_root(&this_val);
                    let nstep = eval_to_number(prog, lv, st);
                    st.truncate_roots(rbase);
                    match nstep {
                        ExprStep::Val(Val::Number(ln)) => {
                            let len = num_to_uint32(ln) as usize;
                            if len == 0 {
                                let sres = set_property_val_exec(st, &this_val, k_length(), Val::Number(JsNum(POS_ZERO_BITS)));
                                match sres {
                                    ExprStep::Val(_) => ExprStep::Val(Val::Undefined),
                                    abrupt => abrupt,
                                }
                            } else {
                                let last_idx = len - 1;
                                let ik = index_key_exec(last_idx);
                                let estep = get_property_val_exec(st, &this_val, &ik);
                                match estep {
                                    ExprStep::Val(elem) => {
                                        if let Val::Object(oid) = &this_val {
                                            let _ = st.heap.delete_prop(st.intr.realm, *oid, &ik);
                                        }
                                        let sres = set_property_val_exec(st, &this_val, k_length(), Val::Number(num_from_usize(last_idx)));
                                        match sres {
                                            ExprStep::Val(_) => ExprStep::Val(elem),
                                            abrupt => abrupt,
                                        }
                                    }
                                    abrupt => abrupt,
                                }
                            }
                        }
                        other => other,
                    }
                }
                abrupt => abrupt,
            }
        }
        _ => {
            if matches!(this_val, Val::Undefined | Val::Null) {
                throw_error_exec(st, ErrorKind::TypeError, k_empty())
            } else {
                let rbase = st.temp_roots.len();
                st.push_root(&this_val);
                let lk = k_length();
                let lstep = get_property_val_exec(st, &this_val, &lk);
                let lv = match lstep {
                    ExprStep::Val(v) => v,
                    abrupt => {
                        st.truncate_roots(rbase);
                        return abrupt;
                    }
                };
                let nstep = eval_to_number(prog, lv, st);
                let ln = match nstep {
                    ExprStep::Val(Val::Number(n)) => n,
                    other => {
                        st.truncate_roots(rbase);
                        return other;
                    }
                };
                let len = num_to_uint32(ln) as usize;
                let sep_step = if args.len() == 0 || matches!(args[0], Val::Undefined) {
                    ExprStep::Val(Val::Str(k_comma()))
                } else {
                    eval_to_string(prog, clone_val(&args[0]), st)
                };
                match sep_step {
                    ExprStep::Val(Val::Str(sep)) => {
                        let jres = eval_array_join_loop(prog, &this_val, &sep, len, st);
                        st.truncate_roots(rbase);
                        jres
                    }
                    other => {
                        st.truncate_roots(rbase);
                        other
                    }
                }
            }
        }
    }
}

pub open spec fn spec_eval_builtin_err_fn(
    prog: SpecProgram,
    builtin: BuiltinFn,
    this_val: SpecVal,
    args: Seq<SpecVal>,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 4nat, 1nat,
{
    spec_eval_builtin_err_fn_inner(prog, builtin, this_val, args, st)
}

#[verifier::opaque]
pub open spec fn spec_eval_builtin_err_fn_inner(
    prog: SpecProgram,
    builtin: BuiltinFn,
    this_val: SpecVal,
    args: Seq<SpecVal>,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 4nat, 0nat,
{
    match builtin {
        BuiltinFn::ErrorToString => {
            if !(this_val is Object) {
                spec_throw_error(st, ErrorKind::TypeError, spec_k_empty())
            } else {
                let rbase = st.temp_roots.len();
                let st_r = spec_push_root(st, this_val);
                let (st1, nstep) = spec_get_property_val(st_r, this_val, spec_k_name());
                match nstep {
                    SpecExprStep::Val(nv) => {
                        let (st2, ns_step) = if nv is Undefined {
                            (st1, SpecExprStep::Val(SpecVal::Str(spec_k_error())))
                        } else {
                            let (s_raw, sr) = spec_eval_to_string(prog, nv, st1);
                            (spec_cap_fuel(s_raw, st1.fuel), sr)
                        };
                        match ns_step {
                            SpecExprStep::Val(SpecVal::Str(ns)) => {
                                let (st3, mstep) = spec_get_property_val(st2, this_val, spec_k_message());
                                match mstep {
                                    SpecExprStep::Val(mv) => {
                                        let (st4, ms_step) = if mv is Undefined {
                                            (st3, SpecExprStep::Val(SpecVal::Str(spec_k_empty())))
                                        } else {
                                            let (s_raw, sr) = spec_eval_to_string(prog, mv, st3);
                                            (spec_cap_fuel(s_raw, st3.fuel), sr)
                                        };
                                        let st_done = spec_truncate_roots(st4, rbase);
                                        match ms_step {
                                            SpecExprStep::Val(SpecVal::Str(ms)) => {
                                                let out = if ns.len() == 0 {
                                                    ms
                                                } else if ms.len() == 0 {
                                                    ns
                                                } else {
                                                    ns + spec_k_colon_space() + ms
                                                };
                                                (st_done, SpecExprStep::Val(SpecVal::Str(out)))
                                            }
                                            other => (st_done, other),
                                        }
                                    }
                                    abrupt => (spec_truncate_roots(st3, rbase), abrupt),
                                }
                            }
                            other => (spec_truncate_roots(st2, rbase), other),
                        }
                    }
                    abrupt => (spec_truncate_roots(st1, rbase), abrupt),
                }
            }
        }
        _ => {
            if !spec_is_callable(st.heap, st.intr.realm, this_val) {
                spec_throw_error(st, ErrorKind::TypeError, spec_k_empty())
            } else {
                let call_this = if args.len() > 0 { args[0] } else { SpecVal::Undefined };
                let call_args = if args.len() > 1 { args.subrange(1, args.len() as int) } else { seq![] };
                let (st1, r) = spec_eval_call(prog, this_val, call_this, call_args, st);
                (spec_cap_fuel(st1, st.fuel), r)
            }
        }
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(25)]
fn eval_builtin_err_fn(
    prog: &Program,
    builtin: BuiltinFn,
    this_val: Val,
    args: &Vec<Val>,
    st: &mut VmState,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_eval_builtin_err_fn(prog@, builtin, this_val@, spec_vals_view(args@), old(st)@),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 4nat, 0nat,
{
    reveal(spec_eval_builtin_err_fn_inner);
    match builtin {
        BuiltinFn::ErrorToString => {
            if !matches!(this_val, Val::Object(_)) {
                throw_error_exec(st, ErrorKind::TypeError, k_empty())
            } else {
                let rbase = st.temp_roots.len();
                st.push_root(&this_val);
                let nk = k_name();
                let nstep = get_property_val_exec(st, &this_val, &nk);
                let nv = match nstep {
                    ExprStep::Val(v) => v,
                    abrupt => {
                        st.truncate_roots(rbase);
                        return abrupt;
                    }
                };
                let ns_step = if matches!(nv, Val::Undefined) {
                    ExprStep::Val(Val::Str(k_error()))
                } else {
                    eval_to_string(prog, nv, st)
                };
                let ns = match ns_step {
                    ExprStep::Val(Val::Str(s)) => s,
                    other => {
                        st.truncate_roots(rbase);
                        return other;
                    }
                };
                let mk = k_message();
                let mstep = get_property_val_exec(st, &this_val, &mk);
                let mv = match mstep {
                    ExprStep::Val(v) => v,
                    abrupt => {
                        st.truncate_roots(rbase);
                        return abrupt;
                    }
                };
                let ms_step = if matches!(mv, Val::Undefined) {
                    ExprStep::Val(Val::Str(k_empty()))
                } else {
                    eval_to_string(prog, mv, st)
                };
                st.truncate_roots(rbase);
                match ms_step {
                    ExprStep::Val(Val::Str(ms)) => {
                        let out = if ns.0.len() == 0 {
                            ms
                        } else if ms.0.len() == 0 {
                            ns
                        } else {
                            let p1 = js_str_concat(&ns, &k_colon_space());
                            js_str_concat(&p1, &ms)
                        };
                        ExprStep::Val(Val::Str(out))
                    }
                    other => other,
                }
            }
        }
        _ => {
            if !is_callable_exec(&st.heap, st.intr.realm, &this_val) {
                throw_error_exec(st, ErrorKind::TypeError, k_empty())
            } else {
                let call_this = if args.len() > 0 { clone_val(&args[0]) } else { Val::Undefined };
                let mut call_args: Vec<Val> = Vec::new();
                let ghost sargs = spec_vals_view(args@);
                if args.len() > 1 {
                    let n = args.len();
                    let mut i: usize = 1;
                    while i < n
                        invariant
                            1 <= i <= n == args@.len(),
                            sargs == spec_vals_view(args@),
                            spec_vals_view(call_args@) =~= sargs.subrange(1, i as int),
                        decreases n - i,
                    {
                        let ghost pre = spec_vals_view(call_args@);
                        call_args.push(clone_val(&args[i]));
                        proof {
                            assert(spec_vals_view(call_args@) =~= pre.push(sargs[i as int]));
                            assert(sargs.subrange(1, (i + 1) as int) =~= sargs.subrange(1, i as int).push(sargs[i as int]));
                        }
                        i += 1;
                    }
                } else {
                    proof { assert(spec_vals_view(call_args@) =~= Seq::<SpecVal>::empty()); }
                }
                eval_call(prog, this_val, call_this, &call_args, st)
            }
        }
    }
}

pub open spec fn spec_eval_builtin_call(
    prog: SpecProgram,
    builtin: BuiltinFn,
    this_val: SpecVal,
    args: Seq<SpecVal>,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 4nat, 3nat,
{
    spec_eval_builtin_call_inner(prog, builtin, this_val, args, st)
}

#[verifier::opaque]
pub open spec fn spec_eval_builtin_call_inner(
    prog: SpecProgram,
    builtin: BuiltinFn,
    this_val: SpecVal,
    args: Seq<SpecVal>,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 4nat, 2nat,
{
    match builtin {
        BuiltinFn::ErrorCtor(kind) => {
            let proto = spec_error_proto_for(st.intr, kind);
            if args.len() == 0 || (args[0] is Undefined) {
                let obj = SpecHeapObject {
                    realm: st.intr.realm,
                    prototype: Some(proto),
                    extensible: true,
                    kind: ObjectKind::Error { kind },
                    props: seq![],
                };
                let (st2, ares) = spec_state_alloc_obj(st, obj);
                match ares {
                    AllocRes::Ok(oid) => (st2, SpecExprStep::Val(SpecVal::Object(oid))),
                    AllocRes::QuotaExceeded => (st2, SpecExprStep::HeapQuotaExceeded),
                }
            } else {
                let (st1_raw, mstep) = spec_eval_to_string(prog, args[0], st);
                let st1 = spec_cap_fuel(st1_raw, st.fuel);
                match mstep {
                    SpecExprStep::Val(SpecVal::Str(ms)) => {
                        let obj = SpecHeapObject {
                            realm: st1.intr.realm,
                            prototype: Some(proto),
                            extensible: true,
                            kind: ObjectKind::Error { kind },
                            props: seq![spec_prop_data(spec_k_message(), SpecVal::Str(ms), false)],
                        };
                        let (st2, ares) = spec_state_alloc_obj(st1, obj);
                        match ares {
                            AllocRes::Ok(oid) => (st2, SpecExprStep::Val(SpecVal::Object(oid))),
                            AllocRes::QuotaExceeded => (st2, SpecExprStep::HeapQuotaExceeded),
                        }
                    }
                    other => (st1, other),
                }
            }
        }
        BuiltinFn::StringConv => {
            if args.len() == 0 {
                (st, SpecExprStep::Val(SpecVal::Str(spec_k_empty())))
            } else {
                let (st1, r) = spec_eval_to_string(prog, args[0], st);
                (spec_cap_fuel(st1, st.fuel), r)
            }
        }
        BuiltinFn::NumberConv => {
            if args.len() == 0 {
                (st, SpecExprStep::Val(SpecVal::Number(JsNum(POS_ZERO_BITS))))
            } else {
                let (st1, r) = spec_eval_to_number(prog, args[0], st);
                (spec_cap_fuel(st1, st.fuel), r)
            }
        }
        BuiltinFn::BooleanConv => {
            let b = if args.len() == 0 { false } else { spec_to_boolean(args[0]) };
            (st, SpecExprStep::Val(SpecVal::Bool(b)))
        }
        BuiltinFn::ObjectCtor => {
            if args.len() > 0 && (args[0] is Object) {
                (st, SpecExprStep::Val(args[0]))
            } else {
                let obj = SpecHeapObject {
                    realm: st.intr.realm,
                    prototype: Some(st.intr.object_proto),
                    extensible: true,
                    kind: ObjectKind::Ordinary,
                    props: seq![],
                };
                let (st2, ares) = spec_state_alloc_obj(st, obj);
                match ares {
                    AllocRes::Ok(oid) => (st2, SpecExprStep::Val(SpecVal::Object(oid))),
                    AllocRes::QuotaExceeded => (st2, SpecExprStep::HeapQuotaExceeded),
                }
            }
        }
        BuiltinFn::ObjectIs => {
            let a = if args.len() > 0 { args[0] } else { SpecVal::Undefined };
            let b = if args.len() > 1 { args[1] } else { SpecVal::Undefined };
            (st, SpecExprStep::Val(SpecVal::Bool(spec_same_value(a, b))))
        }
        BuiltinFn::ObjectKeys => {
            let a = if args.len() > 0 { args[0] } else { SpecVal::Undefined };
            match a {
                SpecVal::Undefined | SpecVal::Null =>
                    spec_throw_error(st, ErrorKind::TypeError, spec_k_empty()),
                SpecVal::Object(oid) => {
                    match spec_own_enumerable_keys(st.heap, st.intr.realm, oid) {
                        Some(ks) => spec_alloc_array_from_vals(spec_strs_to_vals(ks), st),
                        None => spec_throw_error(st, ErrorKind::TypeError, spec_k_empty()),
                    }
                }
                _ => spec_alloc_array_from_vals(seq![], st),
            }
        }
        BuiltinFn::ObjectToString => {
            let tag = match this_val {
                SpecVal::Undefined => spec_tag_undef(),
                SpecVal::Null => spec_tag_null(),
                SpecVal::Bool(_) => spec_tag_bool(),
                SpecVal::Number(_) => spec_tag_num(),
                SpecVal::Str(_) => spec_tag_str(),
                SpecVal::Object(oid) => {
                    if (oid.0 as int) >= st.heap.slots.len() {
                        spec_tag_obj()
                    } else {
                        match st.heap.slots[oid.0 as int] {
                            SpecSlot::Live(o) => {
                                if o.realm != st.intr.realm {
                                    spec_tag_obj()
                                } else {
                                    match o.kind {
                                        ObjectKind::Array { .. } => spec_tag_arr(),
                                        ObjectKind::Function { .. } | ObjectKind::BuiltinFunction { .. } => spec_tag_fn(),
                                        ObjectKind::Error { .. } => spec_tag_err(),
                                        ObjectKind::Ordinary => spec_tag_obj(),
                                    }
                                }
                            }
                            SpecSlot::Free => spec_tag_obj(),
                        }
                    }
                }
            };
            (st, SpecExprStep::Val(SpecVal::Str(tag)))
        }
        BuiltinFn::ObjectHasOwnProperty => {
            if (this_val is Undefined) || (this_val is Null) {
                spec_throw_error(st, ErrorKind::TypeError, spec_k_empty())
            } else {
                let karg = if args.len() > 0 { args[0] } else { SpecVal::Undefined };
                let rbase = st.temp_roots.len();
                let st_r = spec_push_root(st, this_val);
                let (st1_raw, kstep) = spec_eval_to_string(prog, karg, st_r);
                let st1 = spec_truncate_roots(spec_cap_fuel(st1_raw, st.fuel), rbase);
                match kstep {
                    SpecExprStep::Val(SpecVal::Str(ks)) => {
                        match this_val {
                            SpecVal::Object(oid) => {
                                match spec_heap_has_own_prop(st1.heap, st1.intr.realm, oid, ks) {
                                    HeapWriteRes::Ok(b) => (st1, SpecExprStep::Val(SpecVal::Bool(b))),
                                    _ => spec_throw_error(st1, ErrorKind::TypeError, spec_k_empty()),
                                }
                            }
                            SpecVal::Str(s) => {
                                let has = (ks == spec_k_length()) || match spec_parse_array_index(ks) {
                                    Some(idx) => (idx as int) < s.len(),
                                    None => false,
                                };
                                (st1, SpecExprStep::Val(SpecVal::Bool(has)))
                            }
                            _ => (st1, SpecExprStep::Val(SpecVal::Bool(false))),
                        }
                    }
                    other => (st1, other),
                }
            }
        }
        BuiltinFn::ArrayCtor
        | BuiltinFn::ArrayIsArray
        | BuiltinFn::ArrayPush
        | BuiltinFn::ArrayPop
        | BuiltinFn::ArrayJoin => {
            let (st1, r) = spec_eval_builtin_array(prog, builtin, this_val, args, st);
            (spec_cap_fuel(st1, st.fuel), r)
        }
        BuiltinFn::ErrorToString | BuiltinFn::FunctionCall => {
            let (st1, r) = spec_eval_builtin_err_fn(prog, builtin, this_val, args, st);
            (spec_cap_fuel(st1, st.fuel), r)
        }
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub fn eval_builtin_call(
    prog: &Program,
    builtin: BuiltinFn,
    this_val: Val,
    args: &Vec<Val>,
    st: &mut VmState,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_eval_builtin_call(prog@, builtin, this_val@, spec_vals_view(args@), old(st)@),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 4nat, 2nat,
{
    reveal(spec_eval_builtin_call_inner);
    match builtin {
        BuiltinFn::ErrorCtor(kind) => {
            let proto = error_proto_for(&st.intr, kind);
            if args.len() == 0 || matches!(args[0], Val::Undefined) {
                let obj = HeapObject {
                    realm: st.intr.realm,
                    prototype: Some(proto),
                    extensible: true,
                    kind: ObjectKind::Error { kind },
                    props: Vec::new(),
                };
                proof { assert(obj@.props =~= seq![]); }
                match st.alloc_obj(obj) {
                    AllocRes::Ok(oid) => ExprStep::Val(Val::Object(oid)),
                    AllocRes::QuotaExceeded => ExprStep::HeapQuotaExceeded,
                }
            } else {
                let a0 = clone_val(&args[0]);
                match eval_to_string(prog, a0, st) {
                    ExprStep::Val(Val::Str(ms)) => {
                        let ghost sms = ms@;
                        let mut ps: Vec<PropEntry> = Vec::new();
                        ps.push(make_prop_data(k_message(), Val::Str(ms), false));
                        let obj = HeapObject {
                            realm: st.intr.realm,
                            prototype: Some(proto),
                            extensible: true,
                            kind: ObjectKind::Error { kind },
                            props: ps,
                        };
                        proof { assert(obj@.props =~= seq![spec_prop_data(spec_k_message(), SpecVal::Str(sms), false)]); }
                        match st.alloc_obj(obj) {
                            AllocRes::Ok(oid) => ExprStep::Val(Val::Object(oid)),
                            AllocRes::QuotaExceeded => ExprStep::HeapQuotaExceeded,
                        }
                    }
                    other => other,
                }
            }
        }
        BuiltinFn::StringConv => {
            if args.len() == 0 {
                ExprStep::Val(Val::Str(k_empty()))
            } else {
                eval_to_string(prog, clone_val(&args[0]), st)
            }
        }
        BuiltinFn::NumberConv => {
            if args.len() == 0 {
                ExprStep::Val(Val::Number(JsNum(POS_ZERO_BITS)))
            } else {
                eval_to_number(prog, clone_val(&args[0]), st)
            }
        }
        BuiltinFn::BooleanConv => {
            let b = if args.len() == 0 { false } else { val_to_boolean(&args[0]) };
            ExprStep::Val(Val::Bool(b))
        }
        BuiltinFn::ObjectCtor => {
            if args.len() > 0 && matches!(args[0], Val::Object(_)) {
                ExprStep::Val(clone_val(&args[0]))
            } else {
                let obj = HeapObject {
                    realm: st.intr.realm,
                    prototype: Some(st.intr.object_proto),
                    extensible: true,
                    kind: ObjectKind::Ordinary,
                    props: Vec::new(),
                };
                proof { assert(obj@.props =~= seq![]); }
                match st.alloc_obj(obj) {
                    AllocRes::Ok(oid) => ExprStep::Val(Val::Object(oid)),
                    AllocRes::QuotaExceeded => ExprStep::HeapQuotaExceeded,
                }
            }
        }
        BuiltinFn::ObjectIs => {
            let a = if args.len() > 0 { clone_val(&args[0]) } else { Val::Undefined };
            let b = if args.len() > 1 { clone_val(&args[1]) } else { Val::Undefined };
            ExprStep::Val(Val::Bool(val_same_value(&a, &b)))
        }
        BuiltinFn::ObjectKeys => {
            let a = if args.len() > 0 { clone_val(&args[0]) } else { Val::Undefined };
            match a {
                Val::Undefined | Val::Null => throw_error_exec(st, ErrorKind::TypeError, k_empty()),
                Val::Object(oid) => {
                    match st.heap.own_enumerable_keys(st.intr.realm, oid) {
                        Some(ks) => {
                            let kv = strs_to_vals_exec(&ks);
                            alloc_array_from_vals_exec(&kv, st)
                        }
                        None => throw_error_exec(st, ErrorKind::TypeError, k_empty()),
                    }
                }
                _ => {
                    let empty_v: Vec<Val> = Vec::new();
                    proof { assert(spec_vals_view(empty_v@) =~= Seq::<SpecVal>::empty()); }
                    alloc_array_from_vals_exec(&empty_v, st)
                }
            }
        }
        BuiltinFn::ObjectToString => {
            let tag = match &this_val {
                Val::Undefined => tag_undef(),
                Val::Null => tag_null(),
                Val::Bool(_) => tag_bool(),
                Val::Number(_) => tag_num(),
                Val::Str(_) => tag_str(),
                Val::Object(oid) => {
                    if oid.0 >= st.heap.slots.len() {
                        tag_obj()
                    } else {
                        proof { assert(st@.heap.slots[oid.0 as int] == st.heap.slots@[oid.0 as int]@); }
                        match &st.heap.slots[oid.0] {
                            Slot::Live(o) => {
                                if o.realm.0 != st.intr.realm.0 {
                                    tag_obj()
                                } else {
                                    match o.kind {
                                        ObjectKind::Array { .. } => tag_arr(),
                                        ObjectKind::Function { .. } | ObjectKind::BuiltinFunction { .. } => tag_fn(),
                                        ObjectKind::Error { .. } => tag_err(),
                                        ObjectKind::Ordinary => tag_obj(),
                                    }
                                }
                            }
                            Slot::Free => tag_obj(),
                        }
                    }
                }
            };
            ExprStep::Val(Val::Str(tag))
        }
        BuiltinFn::ObjectHasOwnProperty => {
            if matches!(this_val, Val::Undefined | Val::Null) {
                throw_error_exec(st, ErrorKind::TypeError, k_empty())
            } else {
                let karg = if args.len() > 0 { clone_val(&args[0]) } else { Val::Undefined };
                let rbase = st.temp_roots.len();
                st.push_root(&this_val);
                let kstep = eval_to_string(prog, karg, st);
                st.truncate_roots(rbase);
                match kstep {
                    ExprStep::Val(Val::Str(ks)) => {
                        match &this_val {
                            Val::Object(oid) => {
                                match st.heap.has_own_prop(st.intr.realm, *oid, &ks) {
                                    HeapWriteRes::Ok(b) => ExprStep::Val(Val::Bool(b)),
                                    _ => throw_error_exec(st, ErrorKind::TypeError, k_empty()),
                                }
                            }
                            Val::Str(s) => {
                                let lk = k_length();
                                let has = js_str_eq(&ks, &lk) || match parse_array_index(&ks) {
                                    Some(idx) => idx < s.0.len(),
                                    None => false,
                                };
                                ExprStep::Val(Val::Bool(has))
                            }
                            _ => ExprStep::Val(Val::Bool(false)),
                        }
                    }
                    other => other,
                }
            }
        }
        BuiltinFn::ArrayCtor
        | BuiltinFn::ArrayIsArray
        | BuiltinFn::ArrayPush
        | BuiltinFn::ArrayPop
        | BuiltinFn::ArrayJoin => eval_builtin_array(prog, builtin, this_val, args, st),
        BuiltinFn::ErrorToString | BuiltinFn::FunctionCall =>
            eval_builtin_err_fn(prog, builtin, this_val, args, st),
    }
}

pub open spec fn spec_eval_new(
    prog: SpecProgram,
    ctor: SpecVal,
    args: Seq<SpecVal>,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 4nat, 4nat,
{
    match ctor {
        SpecVal::Object(coid) => {
            if (coid.0 as int) >= st.heap.slots.len() {
                spec_throw_error(st, ErrorKind::TypeError, spec_k_empty())
            } else {
                match st.heap.slots[coid.0 as int] {
                    SpecSlot::Live(cobj) => {
                        if cobj.realm != st.intr.realm {
                            spec_throw_error(st, ErrorKind::TypeError, spec_k_empty())
                        } else {
                            match cobj.kind {
                                ObjectKind::Function { is_arrow: true, .. } =>
                                    spec_throw_error(st, ErrorKind::TypeError, spec_k_empty()),
                                ObjectKind::Function { is_arrow: false, .. } => {
                                    let rbase = st.temp_roots.len();
                                    let st_r1 = spec_push_root(st, ctor);
                                    let (st1, pstep) = spec_get_property_val(st_r1, ctor, spec_k_prototype());
                                    match pstep {
                                        SpecExprStep::Val(pv) => {
                                            let inst_proto = match pv {
                                                SpecVal::Object(pid) => pid,
                                                _ => st1.intr.object_proto,
                                            };
                                            let inst_obj = SpecHeapObject {
                                                realm: st1.intr.realm,
                                                prototype: Some(inst_proto),
                                                extensible: true,
                                                kind: ObjectKind::Ordinary,
                                                props: seq![],
                                            };
                                            let (st2, ares) = spec_state_alloc_obj(st1, inst_obj);
                                            match ares {
                                                AllocRes::QuotaExceeded => (spec_truncate_roots(st2, rbase), SpecExprStep::HeapQuotaExceeded),
                                                AllocRes::Ok(inst_oid) => {
                                                    let inst_val = SpecVal::Object(inst_oid);
                                                    let st_r2 = spec_push_root(st2, inst_val);
                                                    let (st3_raw, cstep) = spec_eval_call(prog, ctor, inst_val, args, st_r2);
                                                    let st3 = spec_truncate_roots(spec_cap_fuel(st3_raw, st2.fuel), rbase);
                                                    match cstep {
                                                        SpecExprStep::Val(SpecVal::Object(ret_oid)) =>
                                                            (st3, SpecExprStep::Val(SpecVal::Object(ret_oid))),
                                                        SpecExprStep::Val(_) =>
                                                            (st3, SpecExprStep::Val(inst_val)),
                                                        abrupt => (st3, abrupt),
                                                    }
                                                }
                                            }
                                        }
                                        abrupt => (spec_truncate_roots(st1, rbase), abrupt),
                                    }
                                }
                                ObjectKind::BuiltinFunction { builtin, prototype_obj } => {
                                    if prototype_obj is None {
                                        spec_throw_error(st, ErrorKind::TypeError, spec_k_empty())
                                    } else {
                                        let (st1_raw, bstep) = spec_eval_builtin_call(prog, builtin, SpecVal::Undefined, args, st);
                                        let st1 = spec_cap_fuel(st1_raw, st.fuel);
                                        match bstep {
                                            SpecExprStep::Val(SpecVal::Object(oid)) => (st1, SpecExprStep::Val(SpecVal::Object(oid))),
                                            SpecExprStep::Val(_) => {
                                                // Boxed wrapper object for `new String()`, `new Number()`, `new Boolean()`
                                                let wobj = SpecHeapObject {
                                                    realm: st1.intr.realm,
                                                    prototype: Some(st1.intr.object_proto),
                                                    extensible: true,
                                                    kind: ObjectKind::Ordinary,
                                                    props: seq![],
                                                };
                                                let (st2, ares) = spec_state_alloc_obj(st1, wobj);
                                                match ares {
                                                    AllocRes::Ok(oid) => (st2, SpecExprStep::Val(SpecVal::Object(oid))),
                                                    AllocRes::QuotaExceeded => (st2, SpecExprStep::HeapQuotaExceeded),
                                                }
                                            }
                                            abrupt => (st1, abrupt),
                                        }
                                    }
                                }
                                _ => spec_throw_error(st, ErrorKind::TypeError, spec_k_empty()),
                            }
                        }
                    }
                    SpecSlot::Free => spec_throw_error(st, ErrorKind::TypeError, spec_k_empty()),
                }
            }
        }
        _ => spec_throw_error(st, ErrorKind::TypeError, spec_k_empty()),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub fn eval_new(
    prog: &Program,
    ctor: Val,
    args: &Vec<Val>,
    st: &mut VmState,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_eval_new(prog@, ctor@, spec_vals_view(args@), old(st)@),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 4nat, 4nat,
{
    let coid = match &ctor {
        Val::Object(id) => *id,
        _ => return throw_error_exec(st, ErrorKind::TypeError, k_empty()),
    };
    if coid.0 >= st.heap.slots.len() {
        return throw_error_exec(st, ErrorKind::TypeError, k_empty());
    }
    proof { assert(st@.heap.slots[coid.0 as int] == st.heap.slots@[coid.0 as int]@); }
    let (crealm, ckind) = match &st.heap.slots[coid.0] {
        Slot::Live(o) => (o.realm, o.kind),
        Slot::Free => return throw_error_exec(st, ErrorKind::TypeError, k_empty()),
    };
    if crealm.0 != st.intr.realm.0 {
        return throw_error_exec(st, ErrorKind::TypeError, k_empty());
    }
    match ckind {
        ObjectKind::Function { is_arrow: true, .. } =>
            throw_error_exec(st, ErrorKind::TypeError, k_empty()),
        ObjectKind::Function { is_arrow: false, .. } => {
            let rbase = st.temp_roots.len();
            st.push_root(&ctor);
            let pk = k_prototype();
            let pstep = get_property_val_exec(st, &ctor, &pk);
            let pv = match pstep {
                ExprStep::Val(v) => v,
                abrupt => {
                    st.truncate_roots(rbase);
                    return abrupt;
                }
            };
            let inst_proto = match pv {
                Val::Object(pid) => pid,
                _ => st.intr.object_proto,
            };
            let inst_obj = HeapObject {
                realm: st.intr.realm,
                prototype: Some(inst_proto),
                extensible: true,
                kind: ObjectKind::Ordinary,
                props: Vec::new(),
            };
            proof { assert(inst_obj@.props =~= seq![]); }
            match st.alloc_obj(inst_obj) {
                AllocRes::QuotaExceeded => {
                    st.truncate_roots(rbase);
                    ExprStep::HeapQuotaExceeded
                }
                AllocRes::Ok(inst_oid) => {
                    let inst_val = Val::Object(inst_oid);
                    st.push_root(&inst_val);
                    let cstep = eval_call(prog, ctor, Val::Object(inst_oid), args, st);
                    st.truncate_roots(rbase);
                    match cstep {
                        ExprStep::Val(Val::Object(ret_oid)) => ExprStep::Val(Val::Object(ret_oid)),
                        ExprStep::Val(_) => ExprStep::Val(Val::Object(inst_oid)),
                        abrupt => abrupt,
                    }
                }
            }
        }
        ObjectKind::BuiltinFunction { builtin, prototype_obj } => {
            if prototype_obj.is_none() {
                throw_error_exec(st, ErrorKind::TypeError, k_empty())
            } else {
                let bstep = eval_builtin_call(prog, builtin, Val::Undefined, args, st);
                match bstep {
                    ExprStep::Val(Val::Object(oid)) => ExprStep::Val(Val::Object(oid)),
                    ExprStep::Val(_) => {
                        let wobj = HeapObject {
                            realm: st.intr.realm,
                            prototype: Some(st.intr.object_proto),
                            extensible: true,
                            kind: ObjectKind::Ordinary,
                            props: Vec::new(),
                        };
                        proof { assert(wobj@.props =~= seq![]); }
                        match st.alloc_obj(wobj) {
                            AllocRes::Ok(oid) => ExprStep::Val(Val::Object(oid)),
                            AllocRes::QuotaExceeded => ExprStep::HeapQuotaExceeded,
                        }
                    }
                    abrupt => abrupt,
                }
            }
        }
        _ => throw_error_exec(st, ErrorKind::TypeError, k_empty()),
    }
}

// ---------------------------------------------------------------------------
// Rank 5, 6, 7 & 9: Expressions (`eval_expr`), Sequences, Literals & `VarDecl`
// ---------------------------------------------------------------------------

pub enum ArgListStep {
    Vals(Vec<Val>),
    Abrupt(ExprStep),
}

pub enum SpecArgListStep {
    Vals(Seq<SpecVal>),
    Abrupt(SpecExprStep),
}

impl View for ArgListStep {
    type V = SpecArgListStep;

    open spec fn view(&self) -> SpecArgListStep {
        match self {
            ArgListStep::Vals(vs) => SpecArgListStep::Vals(spec_vals_view(vs@)),
            ArgListStep::Abrupt(es) => SpecArgListStep::Abrupt(es@),
        }
    }
}

pub open spec fn spec_assign_op_binop(op: AssignOp) -> Option<BinOp> {
    match op {
        AssignOp::AddAssign => Some(BinOp::Add),
        AssignOp::SubAssign => Some(BinOp::Sub),
        AssignOp::MulAssign => Some(BinOp::Mul),
        AssignOp::DivAssign => Some(BinOp::Div),
        AssignOp::RemAssign => Some(BinOp::Rem),
        AssignOp::ExpAssign => Some(BinOp::Exp),
        AssignOp::ShlAssign => Some(BinOp::Shl),
        AssignOp::ShrAssign => Some(BinOp::Shr),
        AssignOp::UshrAssign => Some(BinOp::Ushr),
        AssignOp::BitAndAssign => Some(BinOp::BitAnd),
        AssignOp::BitOrAssign => Some(BinOp::BitOr),
        AssignOp::BitXorAssign => Some(BinOp::BitXor),
        _ => None,
    }
}

fn assign_op_binop_exec(op: AssignOp) -> (r: Option<BinOp>)
    ensures r == spec_assign_op_binop(op),
{
    match op {
        AssignOp::AddAssign => Some(BinOp::Add),
        AssignOp::SubAssign => Some(BinOp::Sub),
        AssignOp::MulAssign => Some(BinOp::Mul),
        AssignOp::DivAssign => Some(BinOp::Div),
        AssignOp::RemAssign => Some(BinOp::Rem),
        AssignOp::ExpAssign => Some(BinOp::Exp),
        AssignOp::ShlAssign => Some(BinOp::Shl),
        AssignOp::ShrAssign => Some(BinOp::Shr),
        AssignOp::UshrAssign => Some(BinOp::Ushr),
        AssignOp::BitAndAssign => Some(BinOp::BitAnd),
        AssignOp::BitOrAssign => Some(BinOp::BitOr),
        AssignOp::BitXorAssign => Some(BinOp::BitXor),
        _ => None,
    }
}

pub open spec fn spec_eval_expr_seq(
    prog: SpecProgram,
    exprs: Seq<ExprId>,
    idx: nat,
    last_val: SpecVal,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 6nat, (exprs.len() - idx) as nat,
{
    if idx >= exprs.len() {
        (st, SpecExprStep::Val(last_val))
    } else {
        let (st1_raw, step) = spec_eval_expr(prog, exprs[idx as int], st);
        let st1 = spec_cap_fuel(st1_raw, st.fuel);
        match step {
            SpecExprStep::Val(v) => spec_eval_expr_seq(prog, exprs, idx + 1, v, st1),
            abrupt => (st1, abrupt),
        }
    }
}

fn eval_expr_seq(
    prog: &Program,
    exprs: &Vec<ExprId>,
    st: &mut VmState,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_eval_expr_seq(prog@, exprs@, 0, SpecVal::Undefined, old(st)@),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 6nat, exprs@.len() as nat,
{
    let n = exprs.len();
    let mut i: usize = 0;
    let mut last_val = Val::Undefined;
    while i < n
        invariant
            i <= n == exprs@.len(),
            st.fuel <= old(st).fuel,
            env_wf(old(st)@.envs) ==> env_wf(st@.envs),
            spec_eval_expr_seq(prog@, exprs@, 0, SpecVal::Undefined, old(st)@)
                == spec_eval_expr_seq(prog@, exprs@, i as nat, last_val@, st@),
        decreases n - i,
    {
        let eid = exprs[i];
        let step = eval_expr(prog, eid, st);
        match step {
            ExprStep::Val(v) => {
                last_val = v;
                i += 1;
            }
            abrupt => return abrupt,
        }
    }
    ExprStep::Val(last_val)
}

/// Evaluates `args` left-to-right, pushing each evaluated value onto `st.temp_roots` so GC
/// preserves all previously evaluated arguments while later arguments execute!
pub open spec fn spec_eval_arg_list(
    prog: SpecProgram,
    args: Seq<ExprId>,
    idx: nat,
    acc: Seq<SpecVal>,
    st: SpecState,
) -> (SpecState, SpecArgListStep)
    decreases st.fuel, 6nat, (args.len() - idx) as nat,
{
    if idx >= args.len() {
        (st, SpecArgListStep::Vals(acc))
    } else {
        let (st1_raw, step) = spec_eval_expr(prog, args[idx as int], st);
        let st1 = spec_cap_fuel(st1_raw, st.fuel);
        match step {
            SpecExprStep::Val(v) => {
                let st_r = spec_push_root(st1, v);
                spec_eval_arg_list(prog, args, idx + 1, acc.push(v), st_r)
            }
            abrupt => (st1, SpecArgListStep::Abrupt(abrupt)),
        }
    }
}

fn eval_arg_list(
    prog: &Program,
    args: &Vec<ExprId>,
    st: &mut VmState,
) -> (res: ArgListStep)
    ensures
        (final(st)@, res@) == spec_eval_arg_list(prog@, args@, 0, seq![], old(st)@),
        final(st).fuel <= old(st).fuel,
        match res@ {
            SpecArgListStep::Vals(_) => true,
            SpecArgListStep::Abrupt(es) => (es is OutOfFuel) ==> final(st).fuel == 0,
        },
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 6nat, args@.len() as nat,
{
    let n = args.len();
    let mut i: usize = 0;
    let mut out: Vec<Val> = Vec::new();
    proof { assert(spec_vals_view(out@) =~= Seq::<SpecVal>::empty()); }
    while i < n
        invariant
            i <= n == args@.len(),
            st.fuel <= old(st).fuel,
            env_wf(old(st)@.envs) ==> env_wf(st@.envs),
            spec_eval_arg_list(prog@, args@, 0, seq![], old(st)@)
                == spec_eval_arg_list(prog@, args@, i as nat, spec_vals_view(out@), st@),
        decreases n - i,
    {
        let eid = args[i];
        let step = eval_expr(prog, eid, st);
        match step {
            ExprStep::Val(v) => {
                let ghost pre = spec_vals_view(out@);
                let ghost sv = v@;
                st.push_root(&v);
                out.push(v);
                proof { assert(spec_vals_view(out@) =~= pre.push(sv)); }
                i += 1;
            }
            abrupt => return ArgListStep::Abrupt(abrupt),
        }
    }
    ArgListStep::Vals(out)
}

pub open spec fn spec_eval_array_elems(
    prog: SpecProgram,
    elems: Seq<Option<ExprId>>,
    idx: nat,
    acc_props: Seq<SpecPropEntry>,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 6nat, elems.len() - idx,
{
    if idx >= elems.len() {
        let obj = SpecHeapObject {
            realm: st.intr.realm,
            prototype: Some(st.intr.array_proto),
            extensible: true,
            kind: ObjectKind::Array { length: elems.len() as usize },
            props: acc_props,
        };
        let (st2, ares) = spec_state_alloc_obj(st, obj);
        match ares {
            AllocRes::Ok(oid) => (st2, SpecExprStep::Val(SpecVal::Object(oid))),
            AllocRes::QuotaExceeded => (st2, SpecExprStep::HeapQuotaExceeded),
        }
    } else {
        match elems[idx as int] {
            None => spec_eval_array_elems(prog, elems, idx + 1, acc_props, st),
            Some(eid) => {
                let (st1_raw, step) = spec_eval_expr(prog, eid, st);
                let st1 = spec_cap_fuel(st1_raw, st.fuel);
                match step {
                    SpecExprStep::Val(v) => {
                        let st_r = spec_push_root(st1, v);
                        let next_props = acc_props.push(spec_prop_data(spec_index_key(idx as usize), v, true));
                        spec_eval_array_elems(prog, elems, idx + 1, next_props, st_r)
                    }
                    abrupt => (st1, abrupt),
                }
            }
        }
    }
}

fn eval_array_elems(
    prog: &Program,
    elems: &Vec<Option<ExprId>>,
    st: &mut VmState,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_eval_array_elems(prog@, elems@, 0, seq![], old(st)@),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 6nat, elems@.len() as nat,
{
    let n = elems.len();
    let mut idx: usize = 0;
    let mut ps: Vec<PropEntry> = Vec::new();
    proof { assert(spec_props_view(ps@) =~= Seq::<SpecPropEntry>::empty()); }
    while idx < n
        invariant
            idx <= n == elems@.len(),
            st.fuel <= old(st).fuel,
            env_wf(old(st)@.envs) ==> env_wf(st@.envs),
            spec_eval_array_elems(prog@, elems@, 0, seq![], old(st)@)
                == spec_eval_array_elems(prog@, elems@, idx as nat, spec_props_view(ps@), st@),
        decreases n - idx,
    {
        match elems[idx] {
            None => {
                idx += 1;
            }
            Some(eid) => {
                let step = eval_expr(prog, eid, st);
                match step {
                    ExprStep::Val(v) => {
                        let ghost pre = spec_props_view(ps@);
                        let ghost sv = v@;
                        st.push_root(&v);
                        let ik = index_key_exec(idx);
                        ps.push(make_prop_data(ik, v, true));
                        proof {
                            assert(spec_props_view(ps@) =~= pre.push(spec_prop_data(spec_index_key(idx), sv, true)));
                        }
                        idx += 1;
                    }
                    abrupt => return abrupt,
                }
            }
        }
    }
    let obj = HeapObject {
        realm: st.intr.realm,
        prototype: Some(st.intr.array_proto),
        extensible: true,
        kind: ObjectKind::Array { length: n },
        props: ps,
    };
    match st.alloc_obj(obj) {
        AllocRes::Ok(oid) => ExprStep::Val(Val::Object(oid)),
        AllocRes::QuotaExceeded => ExprStep::HeapQuotaExceeded,
    }
}

pub open spec fn spec_eval_obj_props(
    prog: SpecProgram,
    oid: ObjId,
    props: Seq<SpecPropInit>,
    idx: nat,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 6nat, (props.len() - idx) as nat,
{
    if idx >= props.len() {
        (st, SpecExprStep::Val(SpecVal::Object(oid)))
    } else {
        let p = props[idx as int];
        let (st1, kstep): (SpecState, SpecExprStep) = match p.key {
            SpecPropKeyInit::Static(ks) => (st, SpecExprStep::Val(SpecVal::Str(ks))),
            SpecPropKeyInit::Computed(ke) => {
                let (s_raw, ke_step) = spec_eval_expr(prog, ke, st);
                let s1 = spec_cap_fuel(s_raw, st.fuel);
                match ke_step {
                    SpecExprStep::Val(kv) => {
                        let (s2_raw, ks_step) = spec_eval_to_string(prog, kv, s1);
                        (spec_cap_fuel(s2_raw, s1.fuel), ks_step)
                    }
                    abrupt => (s1, abrupt),
                }
            }
        };
        match kstep {
            SpecExprStep::Val(SpecVal::Str(ks)) => {
                let (st2_raw, vstep) = spec_eval_expr(prog, p.val, st1);
                let st2 = spec_cap_fuel(st2_raw, st1.fuel);
                match vstep {
                    SpecExprStep::Val(vv) => {
                        let (h3, _) = spec_heap_set_prop(st2.heap, st2.intr.realm, oid, ks, vv);
                        spec_eval_obj_props(prog, oid, props, idx + 1, SpecState { heap: h3, ..st2 })
                    }
                    abrupt => (st2, abrupt),
                }
            }
            other => (st1, other),
        }
    }
}

fn eval_obj_props(
    prog: &Program,
    oid: ObjId,
    props: &Vec<PropInit>,
    st: &mut VmState,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_eval_obj_props(prog@, oid, spec_prop_inits_view(props@), 0, old(st)@),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 6nat, props@.len() as nat,
{
    let n = props.len();
    let mut i: usize = 0;
    let ghost sprops = spec_prop_inits_view(props@);
    while i < n
        invariant
            i <= n == props@.len(),
            sprops == spec_prop_inits_view(props@),
            st.fuel <= old(st).fuel,
            env_wf(old(st)@.envs) ==> env_wf(st@.envs),
            spec_eval_obj_props(prog@, oid, sprops, 0, old(st)@)
                == spec_eval_obj_props(prog@, oid, sprops, i as nat, st@),
        decreases n - i,
    {
        proof { assert(sprops[i as int] == props@[i as int]@); }
        let kstep = match &props[i].key {
            PropKeyInit::Static(ks) => ExprStep::Val(Val::Str(clone_js_str(ks))),
            PropKeyInit::Computed(ke) => {
                let ke_id = *ke;
                match eval_expr(prog, ke_id, st) {
                    ExprStep::Val(kv) => eval_to_string(prog, kv, st),
                    abrupt => abrupt,
                }
            }
        };
        let ks = match kstep {
            ExprStep::Val(Val::Str(s)) => s,
            other => return other,
        };
        let ve_id = props[i].val;
        match eval_expr(prog, ve_id, st) {
            ExprStep::Val(vv) => {
                let _ = st.heap.set_prop(st.intr.realm, oid, ks, vv);
                i += 1;
            }
            abrupt => return abrupt,
        }
    }
    ExprStep::Val(Val::Object(oid))
}

pub open spec fn spec_eval_unary_node(
    prog: SpecProgram,
    op: UnaryOp,
    arg: ExprId,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 7nat, 1nat,
{
    spec_eval_unary_node_inner(prog, op, arg, st)
}

#[verifier::opaque]
pub open spec fn spec_eval_unary_node_inner(
    prog: SpecProgram,
    op: UnaryOp,
    arg: ExprId,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 7nat, 0nat,
{
    let (st1_raw, step) = spec_eval_expr(prog, arg, st);
    let st1 = spec_cap_fuel(st1_raw, st.fuel);
    match step {
        SpecExprStep::Val(v) => {
            match op {
                UnaryOp::Void => (st1, SpecExprStep::Val(SpecVal::Undefined)),
                UnaryOp::Delete => (st1, SpecExprStep::Val(SpecVal::Bool(true))),
                UnaryOp::Typeof => (st1, SpecExprStep::Val(SpecVal::Str(spec_typeof_val(st1.heap, st1.intr.realm, v)))),
                UnaryOp::LogicalNot => (st1, SpecExprStep::Val(SpecVal::Bool(!spec_to_boolean(v)))),
                UnaryOp::Plus => {
                    let (st2, nstep) = spec_eval_to_number(prog, v, st1);
                    (spec_cap_fuel(st2, st1.fuel), nstep)
                }
                UnaryOp::Minus => {
                    let (st2_raw, nstep) = spec_eval_to_number(prog, v, st1);
                    let st2 = spec_cap_fuel(st2_raw, st1.fuel);
                    match nstep {
                        SpecExprStep::Val(SpecVal::Number(n)) =>
                            (st2, SpecExprStep::Val(SpecVal::Number(spec_num_neg(n)))),
                        other => (st2, other),
                    }
                }
                UnaryOp::BitNot => {
                    let (st2_raw, nstep) = spec_eval_to_number(prog, v, st1);
                    let st2 = spec_cap_fuel(st2_raw, st1.fuel);
                    match nstep {
                        SpecExprStep::Val(SpecVal::Number(n)) =>
                            (st2, SpecExprStep::Val(SpecVal::Number(spec_num_bit_not(n)))),
                        other => (st2, other),
                    }
                }
            }
        }
        abrupt => (st1, abrupt),
    }
}

fn eval_unary_node(
    prog: &Program,
    op: UnaryOp,
    arg: ExprId,
    st: &mut VmState,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_eval_unary_node(prog@, op, arg, old(st)@),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 7nat, 0nat,
{
    reveal(spec_eval_unary_node_inner);
    match eval_expr(prog, arg, st) {
        ExprStep::Val(v) => match op {
            UnaryOp::Void => ExprStep::Val(Val::Undefined),
            UnaryOp::Delete => ExprStep::Val(Val::Bool(true)),
            UnaryOp::Typeof => ExprStep::Val(Val::Str(typeof_val_exec(&st.heap, st.intr.realm, &v))),
            UnaryOp::LogicalNot => ExprStep::Val(Val::Bool(!val_to_boolean(&v))),
            UnaryOp::Plus => eval_to_number(prog, v, st),
            UnaryOp::Minus => match eval_to_number(prog, v, st) {
                ExprStep::Val(Val::Number(n)) => ExprStep::Val(Val::Number(num_neg(n))),
                other => other,
            },
            UnaryOp::BitNot => match eval_to_number(prog, v, st) {
                ExprStep::Val(Val::Number(n)) => ExprStep::Val(Val::Number(num_bit_not(n))),
                other => other,
            },
        },
        abrupt => abrupt,
    }
}

pub open spec fn spec_eval_delete_member_node(
    prog: SpecProgram,
    obj_expr: ExprId,
    prop_expr: ExprId,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 7nat, 1nat,
{
    spec_eval_delete_member_node_inner(prog, obj_expr, prop_expr, st)
}

#[verifier::opaque]
pub open spec fn spec_eval_delete_member_node_inner(
    prog: SpecProgram,
    obj_expr: ExprId,
    prop_expr: ExprId,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 7nat, 0nat,
{
    let (st1_raw, ostep) = spec_eval_expr(prog, obj_expr, st);
    let st1 = spec_cap_fuel(st1_raw, st.fuel);
    match ostep {
        SpecExprStep::Val(ov) => {
            let rbase = st1.temp_roots.len();
            let st_r = spec_push_root(st1, ov);
            let (st2_raw, pstep) = spec_eval_expr(prog, prop_expr, st_r);
            let st2 = spec_cap_fuel(st2_raw, st1.fuel);
            match pstep {
                SpecExprStep::Val(pv) => {
                    if (ov is Undefined) || (ov is Null) {
                        let st_done = spec_truncate_roots(st2, rbase);
                        spec_throw_error(st_done, ErrorKind::TypeError, spec_k_empty())
                    } else {
                        let (st3_raw, kstep) = spec_eval_to_string(prog, pv, st2);
                        let st3 = spec_truncate_roots(spec_cap_fuel(st3_raw, st2.fuel), rbase);
                        match kstep {
                            SpecExprStep::Val(SpecVal::Str(ks)) => {
                                match ov {
                                    SpecVal::Object(oid) => {
                                        let (h4, wres) = spec_heap_delete_prop(st3.heap, st3.intr.realm, oid, ks);
                                        let st4 = SpecState { heap: h4, ..st3 };
                                        match wres {
                                            HeapWriteRes::Ok(ok) => {
                                                if !ok && st4.strict {
                                                    spec_throw_error(st4, ErrorKind::TypeError, spec_k_empty())
                                                } else {
                                                    (st4, SpecExprStep::Val(SpecVal::Bool(ok)))
                                                }
                                            }
                                            _ => spec_throw_error(st4, ErrorKind::TypeError, spec_k_empty()),
                                        }
                                    }
                                    _ => (st3, SpecExprStep::Val(SpecVal::Bool(true))),
                                }
                            }
                            other => (st3, other),
                        }
                    }
                }
                abrupt => (spec_truncate_roots(st2, rbase), abrupt),
            }
        }
        abrupt => (st1, abrupt),
    }
}

fn eval_delete_member_node(
    prog: &Program,
    obj_expr: ExprId,
    prop_expr: ExprId,
    st: &mut VmState,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_eval_delete_member_node(prog@, obj_expr, prop_expr, old(st)@),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 7nat, 0nat,
{
    reveal(spec_eval_delete_member_node_inner);
    let ov = match eval_expr(prog, obj_expr, st) {
        ExprStep::Val(v) => v,
        abrupt => return abrupt,
    };
    let rbase = st.temp_roots.len();
    st.push_root(&ov);
    let pv = match eval_expr(prog, prop_expr, st) {
        ExprStep::Val(v) => v,
        abrupt => {
            st.truncate_roots(rbase);
            return abrupt;
        }
    };
    if matches!(ov, Val::Undefined | Val::Null) {
        st.truncate_roots(rbase);
        return throw_error_exec(st, ErrorKind::TypeError, k_empty());
    }
    let kstep = eval_to_string(prog, pv, st);
    st.truncate_roots(rbase);
    match kstep {
        ExprStep::Val(Val::Str(ks)) => match ov {
            Val::Object(oid) => {
                match st.heap.delete_prop(st.intr.realm, oid, &ks) {
                    HeapWriteRes::Ok(ok) => {
                        if !ok && st.strict {
                            throw_error_exec(st, ErrorKind::TypeError, k_empty())
                        } else {
                            ExprStep::Val(Val::Bool(ok))
                        }
                    }
                    _ => throw_error_exec(st, ErrorKind::TypeError, k_empty()),
                }
            }
            _ => ExprStep::Val(Val::Bool(true)),
        },
        other => other,
    }
}

pub open spec fn spec_eval_binary_node(
    prog: SpecProgram,
    op: BinOp,
    lhs: ExprId,
    rhs: ExprId,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 7nat, 1nat,
{
    spec_eval_binary_node_inner(prog, op, lhs, rhs, st)
}

#[verifier::opaque]
pub open spec fn spec_eval_binary_node_inner(
    prog: SpecProgram,
    op: BinOp,
    lhs: ExprId,
    rhs: ExprId,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 7nat, 0nat,
{
    let (st1_raw, lstep) = spec_eval_expr(prog, lhs, st);
    let st1 = spec_cap_fuel(st1_raw, st.fuel);
    match lstep {
        SpecExprStep::Val(lv) => {
            let rbase = st1.temp_roots.len();
            let st_r = spec_push_root(st1, lv);
            let (st2_raw, rstep) = spec_eval_expr(prog, rhs, st_r);
            let st2 = spec_truncate_roots(spec_cap_fuel(st2_raw, st1.fuel), rbase);
            match rstep {
                SpecExprStep::Val(rv) => {
                    let (st3, res) = spec_eval_apply_binop(prog, op, lv, rv, st2);
                    (spec_cap_fuel(st3, st2.fuel), res)
                }
                abrupt => (st2, abrupt),
            }
        }
        abrupt => (st1, abrupt),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
fn eval_binary_node(
    prog: &Program,
    op: BinOp,
    lhs: ExprId,
    rhs: ExprId,
    st: &mut VmState,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_eval_binary_node(prog@, op, lhs, rhs, old(st)@),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 7nat, 0nat,
{
    reveal(spec_eval_binary_node_inner);
    let lv = match eval_expr(prog, lhs, st) {
        ExprStep::Val(v) => v,
        abrupt => return abrupt,
    };
    let rbase = st.temp_roots.len();
    st.push_root(&lv);
    let rstep = eval_expr(prog, rhs, st);
    st.truncate_roots(rbase);
    match rstep {
        ExprStep::Val(rv) => eval_apply_binop(prog, op, lv, rv, st),
        abrupt => abrupt,
    }
}

pub open spec fn spec_eval_logical_node(
    prog: SpecProgram,
    op: LogicalOp,
    lhs: ExprId,
    rhs: ExprId,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 7nat, 1nat,
{
    spec_eval_logical_node_inner(prog, op, lhs, rhs, st)
}

#[verifier::opaque]
pub open spec fn spec_eval_logical_node_inner(
    prog: SpecProgram,
    op: LogicalOp,
    lhs: ExprId,
    rhs: ExprId,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 7nat, 0nat,
{
    let (st1_raw, lstep) = spec_eval_expr(prog, lhs, st);
    let st1 = spec_cap_fuel(st1_raw, st.fuel);
    match lstep {
        SpecExprStep::Val(lv) => {
            let short_circuit = match op {
                LogicalOp::And => !spec_to_boolean(lv),
                LogicalOp::Or => spec_to_boolean(lv),
                LogicalOp::Nullish => !((lv is Undefined) || (lv is Null)),
            };
            if short_circuit {
                (st1, SpecExprStep::Val(lv))
            } else {
                let (st2, rstep) = spec_eval_expr(prog, rhs, st1);
                (spec_cap_fuel(st2, st1.fuel), rstep)
            }
        }
        abrupt => (st1, abrupt),
    }
}

fn eval_logical_node(
    prog: &Program,
    op: LogicalOp,
    lhs: ExprId,
    rhs: ExprId,
    st: &mut VmState,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_eval_logical_node(prog@, op, lhs, rhs, old(st)@),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 7nat, 0nat,
{
    reveal(spec_eval_logical_node_inner);
    match eval_expr(prog, lhs, st) {
        ExprStep::Val(lv) => {
            let short_circuit = match op {
                LogicalOp::And => !val_to_boolean(&lv),
                LogicalOp::Or => val_to_boolean(&lv),
                LogicalOp::Nullish => !matches!(lv, Val::Undefined | Val::Null),
            };
            if short_circuit {
                ExprStep::Val(lv)
            } else {
                eval_expr(prog, rhs, st)
            }
        }
        abrupt => abrupt,
    }
}

pub open spec fn spec_eval_cond_node(
    prog: SpecProgram,
    cond: ExprId,
    then_expr: ExprId,
    else_expr: ExprId,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 7nat, 1nat,
{
    spec_eval_cond_node_inner(prog, cond, then_expr, else_expr, st)
}

#[verifier::opaque]
pub open spec fn spec_eval_cond_node_inner(
    prog: SpecProgram,
    cond: ExprId,
    then_expr: ExprId,
    else_expr: ExprId,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 7nat, 0nat,
{
    let (st1_raw, cstep) = spec_eval_expr(prog, cond, st);
    let st1 = spec_cap_fuel(st1_raw, st.fuel);
    match cstep {
        SpecExprStep::Val(cv) => {
            let branch = if spec_to_boolean(cv) { then_expr } else { else_expr };
            let (st2, rstep) = spec_eval_expr(prog, branch, st1);
            (spec_cap_fuel(st2, st1.fuel), rstep)
        }
        abrupt => (st1, abrupt),
    }
}

fn eval_cond_node(
    prog: &Program,
    cond: ExprId,
    then_expr: ExprId,
    else_expr: ExprId,
    st: &mut VmState,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_eval_cond_node(prog@, cond, then_expr, else_expr, old(st)@),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 7nat, 0nat,
{
    reveal(spec_eval_cond_node_inner);
    match eval_expr(prog, cond, st) {
        ExprStep::Val(cv) => {
            let branch = if val_to_boolean(&cv) { then_expr } else { else_expr };
            eval_expr(prog, branch, st)
        }
        abrupt => abrupt,
    }
}

pub open spec fn spec_eval_assign_ident_node(
    prog: SpecProgram,
    op: AssignOp,
    name: Seq<u16>,
    rhs: ExprId,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 7nat, 1nat,
{
    spec_eval_assign_ident_node_inner(prog, op, name, rhs, st)
}

#[verifier::opaque]
pub open spec fn spec_eval_assign_ident_node_inner(
    prog: SpecProgram,
    op: AssignOp,
    name: Seq<u16>,
    rhs: ExprId,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 7nat, 0nat,
{
    match op {
        AssignOp::Assign => {
            let (st1_raw, rstep) = spec_eval_expr(prog, rhs, st);
            let st1 = spec_cap_fuel(st1_raw, st.fuel);
            match rstep {
                SpecExprStep::Val(rv) => spec_eval_ident_put(st1, name, rv),
                abrupt => (st1, abrupt),
            }
        }
        AssignOp::AndAssign | AssignOp::OrAssign | AssignOp::NullishAssign => {
            let (st1, lstep) = spec_eval_ident_get(st, name);
            match lstep {
                SpecExprStep::Val(lv) => {
                    let sc = match op {
                        AssignOp::AndAssign => !spec_to_boolean(lv),
                        AssignOp::OrAssign => spec_to_boolean(lv),
                        _ => !((lv is Undefined) || (lv is Null)),
                    };
                    if sc {
                        (st1, SpecExprStep::Val(lv))
                    } else {
                        let (st2_raw, rstep) = spec_eval_expr(prog, rhs, st1);
                        let st2 = spec_cap_fuel(st2_raw, st1.fuel);
                        match rstep {
                            SpecExprStep::Val(rv) => spec_eval_ident_put(st2, name, rv),
                            abrupt => (st2, abrupt),
                        }
                    }
                }
                abrupt => (st1, abrupt),
            }
        }
        _ => {
            let bop = match spec_assign_op_binop(op) {
                Some(b) => b,
                None => BinOp::Add,
            };
            let (st1, lstep) = spec_eval_ident_get(st, name);
            match lstep {
                SpecExprStep::Val(lv) => {
                    let rbase = st1.temp_roots.len();
                    let st_r = spec_push_root(st1, lv);
                    let (st2_raw, rstep) = spec_eval_expr(prog, rhs, st_r);
                    let st2 = spec_truncate_roots(spec_cap_fuel(st2_raw, st1.fuel), rbase);
                    match rstep {
                        SpecExprStep::Val(rv) => {
                            let (st3_raw, bstep) = spec_eval_apply_binop(prog, bop, lv, rv, st2);
                            let st3 = spec_cap_fuel(st3_raw, st2.fuel);
                            match bstep {
                                SpecExprStep::Val(fv) => spec_eval_ident_put(st3, name, fv),
                                abrupt => (st3, abrupt),
                            }
                        }
                        abrupt => (st2, abrupt),
                    }
                }
                abrupt => (st1, abrupt),
            }
        }
    }
}

fn eval_assign_ident_node(
    prog: &Program,
    op: AssignOp,
    name: &JsStr,
    rhs: ExprId,
    st: &mut VmState,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_eval_assign_ident_node(prog@, op, name@, rhs, old(st)@),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 7nat, 0nat,
{
    reveal(spec_eval_assign_ident_node_inner);
    match op {
        AssignOp::Assign => match eval_expr(prog, rhs, st) {
            ExprStep::Val(rv) => eval_ident_put_exec(st, name, rv),
            abrupt => abrupt,
        },
        AssignOp::AndAssign | AssignOp::OrAssign | AssignOp::NullishAssign => {
            match eval_ident_get_exec(st, name) {
                ExprStep::Val(lv) => {
                    let sc = match op {
                        AssignOp::AndAssign => !val_to_boolean(&lv),
                        AssignOp::OrAssign => val_to_boolean(&lv),
                        _ => !matches!(lv, Val::Undefined | Val::Null),
                    };
                    if sc {
                        ExprStep::Val(lv)
                    } else {
                        match eval_expr(prog, rhs, st) {
                            ExprStep::Val(rv) => eval_ident_put_exec(st, name, rv),
                            abrupt => abrupt,
                        }
                    }
                }
                abrupt => abrupt,
            }
        }
        _ => {
            let bop = match assign_op_binop_exec(op) {
                Some(b) => b,
                None => BinOp::Add,
            };
            let lv = match eval_ident_get_exec(st, name) {
                ExprStep::Val(v) => v,
                abrupt => return abrupt,
            };
            let rbase = st.temp_roots.len();
            st.push_root(&lv);
            let rstep = eval_expr(prog, rhs, st);
            st.truncate_roots(rbase);
            match rstep {
                ExprStep::Val(rv) => match eval_apply_binop(prog, bop, lv, rv, st) {
                    ExprStep::Val(fv) => eval_ident_put_exec(st, name, fv),
                    abrupt => abrupt,
                },
                abrupt => abrupt,
            }
        }
    }
}

pub open spec fn spec_eval_assign_member_node(
    prog: SpecProgram,
    op: AssignOp,
    obj_expr: ExprId,
    prop_expr: ExprId,
    rhs: ExprId,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 7nat, 1nat,
{
    spec_eval_assign_member_node_inner(prog, op, obj_expr, prop_expr, rhs, st)
}

#[verifier::opaque]
pub open spec fn spec_eval_assign_member_node_inner(
    prog: SpecProgram,
    op: AssignOp,
    obj_expr: ExprId,
    prop_expr: ExprId,
    rhs: ExprId,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 7nat, 0nat,
{
    let (st1_raw, ostep) = spec_eval_expr(prog, obj_expr, st);
    let st1 = spec_cap_fuel(st1_raw, st.fuel);
    match ostep {
        SpecExprStep::Val(ov) => {
            let rbase = st1.temp_roots.len();
            let st_r1 = spec_push_root(st1, ov);
            let (st2_raw, pstep) = spec_eval_expr(prog, prop_expr, st_r1);
            let st2 = spec_cap_fuel(st2_raw, st1.fuel);
            match pstep {
                SpecExprStep::Val(pv) => {
                    if (ov is Undefined) || (ov is Null) {
                        let st_done = spec_truncate_roots(st2, rbase);
                        spec_throw_error(st_done, ErrorKind::TypeError, spec_k_empty())
                    } else {
                        let (st3_raw, kstep) = spec_eval_to_string(prog, pv, st2);
                        let st3 = spec_cap_fuel(st3_raw, st2.fuel);
                        match kstep {
                            SpecExprStep::Val(SpecVal::Str(ks)) => {
                                match op {
                                    AssignOp::Assign => {
                                        let (st4_raw, rstep) = spec_eval_expr(prog, rhs, st3);
                                        let st4 = spec_truncate_roots(spec_cap_fuel(st4_raw, st3.fuel), rbase);
                                        match rstep {
                                            SpecExprStep::Val(rv) => { let (s_out, r_out) = spec_eval_set_property_val(prog, ov, ks, rv, st4); (spec_cap_fuel(s_out, st4.fuel), r_out) }
                                            abrupt => (st4, abrupt),
                                        }
                                    }
                                    AssignOp::AndAssign | AssignOp::OrAssign | AssignOp::NullishAssign => {
                                        let (st4, lstep) = spec_get_property_val(st3, ov, ks);
                                        match lstep {
                                            SpecExprStep::Val(lv) => {
                                                let sc = match op {
                                                    AssignOp::AndAssign => !spec_to_boolean(lv),
                                                    AssignOp::OrAssign => spec_to_boolean(lv),
                                                    _ => !((lv is Undefined) || (lv is Null)),
                                                };
                                                if sc {
                                                    (spec_truncate_roots(st4, rbase), SpecExprStep::Val(lv))
                                                } else {
                                                    let (st5_raw, rstep) = spec_eval_expr(prog, rhs, st4);
                                                    let st5 = spec_truncate_roots(spec_cap_fuel(st5_raw, st4.fuel), rbase);
                                                    match rstep {
                                                        SpecExprStep::Val(rv) => { let (s_out, r_out) = spec_eval_set_property_val(prog, ov, ks, rv, st5); (spec_cap_fuel(s_out, st5.fuel), r_out) }
                                                        abrupt => (st5, abrupt),
                                                    }
                                                }
                                            }
                                            abrupt => (spec_truncate_roots(st4, rbase), abrupt),
                                        }
                                    }
                                    _ => {
                                        let bop = match spec_assign_op_binop(op) {
                                            Some(b) => b,
                                            None => BinOp::Add,
                                        };
                                        let (st4, lstep) = spec_get_property_val(st3, ov, ks);
                                        match lstep {
                                            SpecExprStep::Val(lv) => {
                                                let st_r2 = spec_push_root(st4, lv);
                                                let (st5_raw, rstep) = spec_eval_expr(prog, rhs, st_r2);
                                                let st5 = spec_cap_fuel(st5_raw, st4.fuel);
                                                match rstep {
                                                    SpecExprStep::Val(rv) => {
                                                        let (st6_raw, bstep) = spec_eval_apply_binop(prog, bop, lv, rv, st5);
                                                        let st6 = spec_truncate_roots(spec_cap_fuel(st6_raw, st5.fuel), rbase);
                                                        match bstep {
                                                            SpecExprStep::Val(fv) => { let (s_out, r_out) = spec_eval_set_property_val(prog, ov, ks, fv, st6); (spec_cap_fuel(s_out, st6.fuel), r_out) }
                                                            abrupt => (st6, abrupt),
                                                        }
                                                    }
                                                    abrupt => (spec_truncate_roots(st5, rbase), abrupt),
                                                }
                                            }
                                            abrupt => (spec_truncate_roots(st4, rbase), abrupt),
                                        }
                                    }
                                }
                            }
                            other => (spec_truncate_roots(st3, rbase), other),
                        }
                    }
                }
                abrupt => (spec_truncate_roots(st2, rbase), abrupt),
            }
        }
        abrupt => (st1, abrupt),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(35)]
fn eval_assign_member_node(
    prog: &Program,
    op: AssignOp,
    obj_expr: ExprId,
    prop_expr: ExprId,
    rhs: ExprId,
    st: &mut VmState,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_eval_assign_member_node(prog@, op, obj_expr, prop_expr, rhs, old(st)@),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 7nat, 0nat,
{
    reveal(spec_eval_assign_member_node_inner);
    let ov = match eval_expr(prog, obj_expr, st) {
        ExprStep::Val(v) => v,
        abrupt => return abrupt,
    };
    let rbase = st.temp_roots.len();
    st.push_root(&ov);
    let pv = match eval_expr(prog, prop_expr, st) {
        ExprStep::Val(v) => v,
        abrupt => {
            st.truncate_roots(rbase);
            return abrupt;
        }
    };
    if matches!(ov, Val::Undefined | Val::Null) {
        st.truncate_roots(rbase);
        return throw_error_exec(st, ErrorKind::TypeError, k_empty());
    }
    let ks = match eval_to_string(prog, pv, st) {
        ExprStep::Val(Val::Str(s)) => s,
        other => {
            st.truncate_roots(rbase);
            return other;
        }
    };
    match op {
        AssignOp::Assign => {
            let rstep = eval_expr(prog, rhs, st);
            st.truncate_roots(rbase);
            match rstep {
                ExprStep::Val(rv) => eval_set_property_val(prog, ov, ks, rv, st),
                abrupt => abrupt,
            }
        }
        AssignOp::AndAssign | AssignOp::OrAssign | AssignOp::NullishAssign => {
            let lstep = get_property_val_exec(st, &ov, &ks);
            match lstep {
                ExprStep::Val(lv) => {
                    let sc = match op {
                        AssignOp::AndAssign => !val_to_boolean(&lv),
                        AssignOp::OrAssign => val_to_boolean(&lv),
                        _ => !matches!(lv, Val::Undefined | Val::Null),
                    };
                    if sc {
                        st.truncate_roots(rbase);
                        ExprStep::Val(lv)
                    } else {
                        let rstep = eval_expr(prog, rhs, st);
                        st.truncate_roots(rbase);
                        match rstep {
                            ExprStep::Val(rv) => eval_set_property_val(prog, ov, ks, rv, st),
                            abrupt => abrupt,
                        }
                    }
                }
                abrupt => {
                    st.truncate_roots(rbase);
                    abrupt
                }
            }
        }
        _ => {
            let bop = match assign_op_binop_exec(op) {
                Some(b) => b,
                None => BinOp::Add,
            };
            let lv = match get_property_val_exec(st, &ov, &ks) {
                ExprStep::Val(v) => v,
                abrupt => {
                    st.truncate_roots(rbase);
                    return abrupt;
                }
            };
            st.push_root(&lv);
            let rv = match eval_expr(prog, rhs, st) {
                ExprStep::Val(v) => v,
                abrupt => {
                    st.truncate_roots(rbase);
                    return abrupt;
                }
            };
            let bstep = eval_apply_binop(prog, bop, lv, rv, st);
            st.truncate_roots(rbase);
            match bstep {
                ExprStep::Val(fv) => eval_set_property_val(prog, ov, ks, fv, st),
                abrupt => abrupt,
            }
        }
    }
}

pub open spec fn spec_eval_update_ident_node(
    prog: SpecProgram,
    op: UpdateOp,
    prefix: bool,
    name: Seq<u16>,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 7nat, 1nat,
{
    spec_eval_update_ident_node_inner(prog, op, prefix, name, st)
}

#[verifier::opaque]
pub open spec fn spec_eval_update_ident_node_inner(
    prog: SpecProgram,
    op: UpdateOp,
    prefix: bool,
    name: Seq<u16>,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 7nat, 0nat,
{
    let (st1, lstep) = spec_eval_ident_get(st, name);
    match lstep {
        SpecExprStep::Val(lv) => {
            let (st2_raw, nstep) = spec_eval_to_number(prog, lv, st1);
            let st2 = spec_cap_fuel(st2_raw, st1.fuel);
            match nstep {
                SpecExprStep::Val(SpecVal::Number(old_n)) => {
                    let new_n = match op {
                        UpdateOp::Inc => spec_num_add(old_n, JsNum(ONE_BITS)),
                        UpdateOp::Dec => spec_num_sub(old_n, JsNum(ONE_BITS)),
                    };
                    let (st3, pstep) = spec_eval_ident_put(st2, name, SpecVal::Number(new_n));
                    match pstep {
                        SpecExprStep::Val(_) => {
                            let ret_n = if prefix { new_n } else { old_n };
                            (st3, SpecExprStep::Val(SpecVal::Number(ret_n)))
                        }
                        abrupt => (st3, abrupt),
                    }
                }
                other => (st2, other),
            }
        }
        abrupt => (st1, abrupt),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(25)]
fn eval_update_ident_node(
    prog: &Program,
    op: UpdateOp,
    prefix: bool,
    name: &JsStr,
    st: &mut VmState,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_eval_update_ident_node(prog@, op, prefix, name@, old(st)@),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 7nat, 0nat,
{
    reveal(spec_eval_update_ident_node_inner);
    let lv = match eval_ident_get_exec(st, name) {
        ExprStep::Val(v) => v,
        abrupt => return abrupt,
    };
    let old_n = match eval_to_number(prog, lv, st) {
        ExprStep::Val(Val::Number(n)) => n,
        other => return other,
    };
    let new_n = match op {
        UpdateOp::Inc => num_add(old_n, JsNum(ONE_BITS)),
        UpdateOp::Dec => num_sub(old_n, JsNum(ONE_BITS)),
    };
    match eval_ident_put_exec(st, name, Val::Number(new_n)) {
        ExprStep::Val(_) => ExprStep::Val(Val::Number(if prefix { new_n } else { old_n })),
        abrupt => abrupt,
    }
}

pub open spec fn spec_eval_update_member_node(
    prog: SpecProgram,
    op: UpdateOp,
    prefix: bool,
    obj_expr: ExprId,
    prop_expr: ExprId,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 7nat, 1nat,
{
    spec_eval_update_member_node_inner(prog, op, prefix, obj_expr, prop_expr, st)
}

#[verifier::opaque]
pub open spec fn spec_eval_update_member_node_inner(
    prog: SpecProgram,
    op: UpdateOp,
    prefix: bool,
    obj_expr: ExprId,
    prop_expr: ExprId,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 7nat, 0nat,
{
    let (st1_raw, ostep) = spec_eval_expr(prog, obj_expr, st);
    let st1 = spec_cap_fuel(st1_raw, st.fuel);
    match ostep {
        SpecExprStep::Val(ov) => {
            let rbase = st1.temp_roots.len();
            let st_r = spec_push_root(st1, ov);
            let (st2_raw, pstep) = spec_eval_expr(prog, prop_expr, st_r);
            let st2 = spec_cap_fuel(st2_raw, st1.fuel);
            match pstep {
                SpecExprStep::Val(pv) => {
                    if (ov is Undefined) || (ov is Null) {
                        let st_done = spec_truncate_roots(st2, rbase);
                        spec_throw_error(st_done, ErrorKind::TypeError, spec_k_empty())
                    } else {
                        let (st3_raw, kstep) = spec_eval_to_string(prog, pv, st2);
                        let st3 = spec_cap_fuel(st3_raw, st2.fuel);
                        match kstep {
                            SpecExprStep::Val(SpecVal::Str(ks)) => {
                                let (st4, gstep) = spec_get_property_val(st3, ov, ks);
                                match gstep {
                                    SpecExprStep::Val(lv) => {
                                        let (st5_raw, nstep) = spec_eval_to_number(prog, lv, st4);
                                        let st5 = spec_truncate_roots(spec_cap_fuel(st5_raw, st4.fuel), rbase);
                                        match nstep {
                                            SpecExprStep::Val(SpecVal::Number(old_n)) => {
                                                let new_n = match op {
                                                    UpdateOp::Inc => spec_num_add(old_n, JsNum(ONE_BITS)),
                                                    UpdateOp::Dec => spec_num_sub(old_n, JsNum(ONE_BITS)),
                                                };
                                                let (st6_raw, sstep) = spec_eval_set_property_val(prog, ov, ks, SpecVal::Number(new_n), st5);
                                                let st6 = spec_cap_fuel(st6_raw, st5.fuel);
                                                match sstep {
                                                    SpecExprStep::Val(_) => {
                                                        let ret_n = if prefix { new_n } else { old_n };
                                                        (st6, SpecExprStep::Val(SpecVal::Number(ret_n)))
                                                    }
                                                    abrupt => (st6, abrupt),
                                                }
                                            }
                                            other => (st5, other),
                                        }
                                    }
                                    abrupt => (spec_truncate_roots(st4, rbase), abrupt),
                                }
                            }
                            other => (spec_truncate_roots(st3, rbase), other),
                        }
                    }
                }
                abrupt => (spec_truncate_roots(st2, rbase), abrupt),
            }
        }
        abrupt => (st1, abrupt),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(25)]
fn eval_update_member_node(
    prog: &Program,
    op: UpdateOp,
    prefix: bool,
    obj_expr: ExprId,
    prop_expr: ExprId,
    st: &mut VmState,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_eval_update_member_node(prog@, op, prefix, obj_expr, prop_expr, old(st)@),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 7nat, 0nat,
{
    reveal(spec_eval_update_member_node_inner);
    let ov = match eval_expr(prog, obj_expr, st) {
        ExprStep::Val(v) => v,
        abrupt => return abrupt,
    };
    let rbase = st.temp_roots.len();
    st.push_root(&ov);
    let pv = match eval_expr(prog, prop_expr, st) {
        ExprStep::Val(v) => v,
        abrupt => {
            st.truncate_roots(rbase);
            return abrupt;
        }
    };
    if matches!(ov, Val::Undefined | Val::Null) {
        st.truncate_roots(rbase);
        return throw_error_exec(st, ErrorKind::TypeError, k_empty());
    }
    let ks = match eval_to_string(prog, pv, st) {
        ExprStep::Val(Val::Str(s)) => s,
        other => {
            st.truncate_roots(rbase);
            return other;
        }
    };
    let lv = match get_property_val_exec(st, &ov, &ks) {
        ExprStep::Val(v) => v,
        abrupt => {
            st.truncate_roots(rbase);
            return abrupt;
        }
    };
    let nstep = eval_to_number(prog, lv, st);
    st.truncate_roots(rbase);
    let old_n = match nstep {
        ExprStep::Val(Val::Number(n)) => n,
        other => return other,
    };
    let new_n = match op {
        UpdateOp::Inc => num_add(old_n, JsNum(ONE_BITS)),
        UpdateOp::Dec => num_sub(old_n, JsNum(ONE_BITS)),
    };
    match eval_set_property_val(prog, ov, ks, Val::Number(new_n), st) {
        ExprStep::Val(_) => ExprStep::Val(Val::Number(if prefix { new_n } else { old_n })),
        abrupt => abrupt,
    }
}

pub open spec fn spec_eval_member_node(
    prog: SpecProgram,
    obj_expr: ExprId,
    prop_expr: ExprId,
    optional: bool,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 7nat, 1nat,
{
    spec_eval_member_node_inner(prog, obj_expr, prop_expr, optional, st)
}

#[verifier::opaque]
pub open spec fn spec_eval_member_node_inner(
    prog: SpecProgram,
    obj_expr: ExprId,
    prop_expr: ExprId,
    optional: bool,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 7nat, 0nat,
{
    let (st1_raw, ostep) = spec_eval_expr(prog, obj_expr, st);
    let st1 = spec_cap_fuel(st1_raw, st.fuel);
    match ostep {
        SpecExprStep::Val(ov) => {
            if optional && ((ov is Undefined) || (ov is Null)) {
                (st1, SpecExprStep::Val(SpecVal::Undefined))
            } else {
                let rbase = st1.temp_roots.len();
                let st_r = spec_push_root(st1, ov);
                let (st2_raw, pstep) = spec_eval_expr(prog, prop_expr, st_r);
                let st2 = spec_cap_fuel(st2_raw, st1.fuel);
                match pstep {
                    SpecExprStep::Val(pv) => {
                        if (ov is Undefined) || (ov is Null) {
                            let st_done = spec_truncate_roots(st2, rbase);
                            spec_throw_error(st_done, ErrorKind::TypeError, spec_k_empty())
                        } else {
                            let (st3_raw, kstep) = spec_eval_to_string(prog, pv, st2);
                            let st3 = spec_truncate_roots(spec_cap_fuel(st3_raw, st2.fuel), rbase);
                            match kstep {
                                SpecExprStep::Val(SpecVal::Str(ks)) => spec_get_property_val(st3, ov, ks),
                                other => (st3, other),
                            }
                        }
                    }
                    abrupt => (spec_truncate_roots(st2, rbase), abrupt),
                }
            }
        }
        abrupt => (st1, abrupt),
    }
}

fn eval_member_node(
    prog: &Program,
    obj_expr: ExprId,
    prop_expr: ExprId,
    optional: bool,
    st: &mut VmState,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_eval_member_node(prog@, obj_expr, prop_expr, optional, old(st)@),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 7nat, 0nat,
{
    reveal(spec_eval_member_node_inner);
    let ov = match eval_expr(prog, obj_expr, st) {
        ExprStep::Val(v) => v,
        abrupt => return abrupt,
    };
    if optional && matches!(ov, Val::Undefined | Val::Null) {
        return ExprStep::Val(Val::Undefined);
    }
    let rbase = st.temp_roots.len();
    st.push_root(&ov);
    let pv = match eval_expr(prog, prop_expr, st) {
        ExprStep::Val(v) => v,
        abrupt => {
            st.truncate_roots(rbase);
            return abrupt;
        }
    };
    if matches!(ov, Val::Undefined | Val::Null) {
        st.truncate_roots(rbase);
        return throw_error_exec(st, ErrorKind::TypeError, k_empty());
    }
    let kstep = eval_to_string(prog, pv, st);
    st.truncate_roots(rbase);
    match kstep {
        ExprStep::Val(Val::Str(ks)) => get_property_val_exec(st, &ov, &ks),
        other => other,
    }
}

pub open spec fn spec_eval_call_node(
    prog: SpecProgram,
    callee_expr: ExprId,
    optional: bool,
    args: Seq<ExprId>,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 7nat, 1nat,
{
    spec_eval_call_node_inner(prog, callee_expr, optional, args, st)
}

#[verifier::opaque]
pub open spec fn spec_eval_call_node_inner(
    prog: SpecProgram,
    callee_expr: ExprId,
    optional: bool,
    args: Seq<ExprId>,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 7nat, 0nat,
{
    let (st1_raw, cstep) = spec_eval_expr(prog, callee_expr, st);
    let st1 = spec_cap_fuel(st1_raw, st.fuel);
    match cstep {
        SpecExprStep::Val(cv) => {
            if optional && ((cv is Undefined) || (cv is Null)) {
                (st1, SpecExprStep::Val(SpecVal::Undefined))
            } else {
                let rbase = st1.temp_roots.len();
                let st_r = spec_push_root(st1, cv);
                let (st2_raw, astep) = spec_eval_arg_list(prog, args, 0, seq![], st_r);
                let st2 = spec_cap_fuel(st2_raw, st1.fuel);
                match astep {
                    SpecArgListStep::Vals(avals) => {
                        let (st3_raw, res) = spec_eval_call(prog, cv, SpecVal::Undefined, avals, st2);
                        (spec_truncate_roots(spec_cap_fuel(st3_raw, st2.fuel), rbase), res)
                    }
                    SpecArgListStep::Abrupt(abrupt) => (spec_truncate_roots(st2, rbase), abrupt),
                }
            }
        }
        abrupt => (st1, abrupt),
    }
}

fn eval_call_node(
    prog: &Program,
    callee_expr: ExprId,
    optional: bool,
    args: &Vec<ExprId>,
    st: &mut VmState,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_eval_call_node(prog@, callee_expr, optional, args@, old(st)@),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 7nat, 0nat,
{
    reveal(spec_eval_call_node_inner);
    let cv = match eval_expr(prog, callee_expr, st) {
        ExprStep::Val(v) => v,
        abrupt => return abrupt,
    };
    if optional && matches!(cv, Val::Undefined | Val::Null) {
        return ExprStep::Val(Val::Undefined);
    }
    let rbase = st.temp_roots.len();
    st.push_root(&cv);
    match eval_arg_list(prog, args, st) {
        ArgListStep::Vals(avals) => {
            let res = eval_call(prog, cv, Val::Undefined, &avals, st);
            st.truncate_roots(rbase);
            res
        }
        ArgListStep::Abrupt(abrupt) => {
            st.truncate_roots(rbase);
            abrupt
        }
    }
}

pub open spec fn spec_eval_call_method_node(
    prog: SpecProgram,
    obj_expr: ExprId,
    prop_expr: ExprId,
    optional: bool,
    optional_call: bool,
    args: Seq<ExprId>,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 7nat, 1nat,
{
    spec_eval_call_method_node_inner(prog, obj_expr, prop_expr, optional, optional_call, args, st)
}

#[verifier::opaque]
pub open spec fn spec_eval_call_method_node_inner(
    prog: SpecProgram,
    obj_expr: ExprId,
    prop_expr: ExprId,
    optional: bool,
    optional_call: bool,
    args: Seq<ExprId>,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 7nat, 0nat,
{
    let (st1_raw, ostep) = spec_eval_expr(prog, obj_expr, st);
    let st1 = spec_cap_fuel(st1_raw, st.fuel);
    match ostep {
        SpecExprStep::Val(ov) => {
            if optional && ((ov is Undefined) || (ov is Null)) {
                (st1, SpecExprStep::Val(SpecVal::Undefined))
            } else {
                let rbase = st1.temp_roots.len();
                let st_r1 = spec_push_root(st1, ov);
                let (st2_raw, pstep) = spec_eval_expr(prog, prop_expr, st_r1);
                let st2 = spec_cap_fuel(st2_raw, st1.fuel);
                match pstep {
                    SpecExprStep::Val(pv) => {
                        if (ov is Undefined) || (ov is Null) {
                            let st_done = spec_truncate_roots(st2, rbase);
                            spec_throw_error(st_done, ErrorKind::TypeError, spec_k_empty())
                        } else {
                            let (st3_raw, kstep) = spec_eval_to_string(prog, pv, st2);
                            let st3 = spec_cap_fuel(st3_raw, st2.fuel);
                            match kstep {
                                SpecExprStep::Val(SpecVal::Str(ks)) => {
                                    let (st4, mstep) = spec_get_property_val(st3, ov, ks);
                                    match mstep {
                                        SpecExprStep::Val(mv) => {
                                            if optional_call && ((mv is Undefined) || (mv is Null)) {
                                                (spec_truncate_roots(st4, rbase), SpecExprStep::Val(SpecVal::Undefined))
                                            } else {
                                                let st_r2 = spec_push_root(st4, mv);
                                                let (st5_raw, astep) = spec_eval_arg_list(prog, args, 0, seq![], st_r2);
                                                let st5 = spec_cap_fuel(st5_raw, st4.fuel);
                                                match astep {
                                                    SpecArgListStep::Vals(avals) => {
                                                        let (st6_raw, res) = spec_eval_call(prog, mv, ov, avals, st5);
                                                        (spec_truncate_roots(spec_cap_fuel(st6_raw, st5.fuel), rbase), res)
                                                    }
                                                    SpecArgListStep::Abrupt(abrupt) =>
                                                        (spec_truncate_roots(st5, rbase), abrupt),
                                                }
                                            }
                                        }
                                        abrupt => (spec_truncate_roots(st4, rbase), abrupt),
                                    }
                                }
                                other => (spec_truncate_roots(st3, rbase), other),
                            }
                        }
                    }
                    abrupt => (spec_truncate_roots(st2, rbase), abrupt),
                }
            }
        }
        abrupt => (st1, abrupt),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(25)]
fn eval_call_method_node(
    prog: &Program,
    obj_expr: ExprId,
    prop_expr: ExprId,
    optional: bool,
    optional_call: bool,
    args: &Vec<ExprId>,
    st: &mut VmState,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_eval_call_method_node(prog@, obj_expr, prop_expr, optional, optional_call, args@, old(st)@),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 7nat, 0nat,
{
    reveal(spec_eval_call_method_node_inner);
    let ov = match eval_expr(prog, obj_expr, st) {
        ExprStep::Val(v) => v,
        abrupt => return abrupt,
    };
    if optional && matches!(ov, Val::Undefined | Val::Null) {
        return ExprStep::Val(Val::Undefined);
    }
    let rbase = st.temp_roots.len();
    st.push_root(&ov);
    let pv = match eval_expr(prog, prop_expr, st) {
        ExprStep::Val(v) => v,
        abrupt => {
            st.truncate_roots(rbase);
            return abrupt;
        }
    };
    if matches!(ov, Val::Undefined | Val::Null) {
        st.truncate_roots(rbase);
        return throw_error_exec(st, ErrorKind::TypeError, k_empty());
    }
    let ks = match eval_to_string(prog, pv, st) {
        ExprStep::Val(Val::Str(s)) => s,
        other => {
            st.truncate_roots(rbase);
            return other;
        }
    };
    let mv = match get_property_val_exec(st, &ov, &ks) {
        ExprStep::Val(v) => v,
        abrupt => {
            st.truncate_roots(rbase);
            return abrupt;
        }
    };
    if optional_call && matches!(mv, Val::Undefined | Val::Null) {
        st.truncate_roots(rbase);
        return ExprStep::Val(Val::Undefined);
    }
    st.push_root(&mv);
    match eval_arg_list(prog, args, st) {
        ArgListStep::Vals(avals) => {
            let res = eval_call(prog, mv, ov, &avals, st);
            st.truncate_roots(rbase);
            res
        }
        ArgListStep::Abrupt(abrupt) => {
            st.truncate_roots(rbase);
            abrupt
        }
    }
}

pub open spec fn spec_delete_val_prop(
    st: SpecState,
    ov: SpecVal,
    ks: Seq<u16>,
) -> (SpecState, SpecExprStep) {
    match ov {
        SpecVal::Object(oid) => {
            let (h4, wres) = spec_heap_delete_prop(st.heap, st.intr.realm, oid, ks);
            let st4 = SpecState { heap: h4, ..st };
            match wres {
                HeapWriteRes::Ok(ok) => {
                    if !ok && st4.strict {
                        spec_throw_error(st4, ErrorKind::TypeError, spec_k_empty())
                    } else {
                        (st4, SpecExprStep::Val(SpecVal::Bool(ok)))
                    }
                }
                _ => spec_throw_error(st4, ErrorKind::TypeError, spec_k_empty()),
            }
        }
        SpecVal::Str(s) => {
            let non_cfg = (ks == spec_k_length()) || match spec_parse_array_index(ks) {
                Some(ai) => (ai as int) < s.len(),
                None => false,
            };
            if non_cfg {
                if st.strict {
                    spec_throw_error(st, ErrorKind::TypeError, spec_k_empty())
                } else {
                    (st, SpecExprStep::Val(SpecVal::Bool(false)))
                }
            } else {
                (st, SpecExprStep::Val(SpecVal::Bool(true)))
            }
        }
        _ => (st, SpecExprStep::Val(SpecVal::Bool(true))),
    }
}

fn delete_val_prop_exec(st: &mut VmState, ov: Val, ks: &JsStr) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_delete_val_prop(old(st)@, ov@, ks@),
        final(st).fuel == old(st).fuel,
        !(res@ is OutOfFuel),
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
{
    match ov {
        Val::Object(oid) => match st.heap.delete_prop(st.intr.realm, oid, ks) {
            HeapWriteRes::Ok(ok) => {
                if !ok && st.strict {
                    throw_error_exec(st, ErrorKind::TypeError, k_empty())
                } else {
                    ExprStep::Val(Val::Bool(ok))
                }
            }
            _ => throw_error_exec(st, ErrorKind::TypeError, k_empty()),
        },
        Val::Str(s) => {
            let lk = k_length();
            let non_cfg = js_str_eq(ks, &lk) || match parse_array_index(ks) {
                Some(ai) => ai < s.0.len(),
                None => false,
            };
            if non_cfg {
                if st.strict {
                    throw_error_exec(st, ErrorKind::TypeError, k_empty())
                } else {
                    ExprStep::Val(Val::Bool(false))
                }
            } else {
                ExprStep::Val(Val::Bool(true))
            }
        }
        _ => ExprStep::Val(Val::Bool(true)),
    }
}

pub open spec fn spec_eval_opt_chain_steps(
    prog: SpecProgram,
    steps: Seq<SpecChainStep>,
    idx: nat,
    is_delete: bool,
    cur_val: SpecVal,
    cur_this: Option<SpecVal>,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 7nat, (steps.len() - idx) as nat,
{
    if idx >= steps.len() {
        let out_v = if is_delete { SpecVal::Bool(true) } else { cur_val };
        (st, SpecExprStep::Val(out_v))
    } else {
        let step = steps[idx as int];
        let step_opt = match step {
            SpecChainStep::Member { optional, .. } => optional,
            SpecChainStep::Call { optional, .. } => optional,
        };
        if step_opt && ((cur_val is Undefined) || (cur_val is Null)) {
            let out_v = if is_delete { SpecVal::Bool(true) } else { SpecVal::Undefined };
            (st, SpecExprStep::Val(out_v))
        } else {
            match step {
                SpecChainStep::Member { prop, .. } => {
                    let rbase = st.temp_roots.len();
                    let st_r = spec_push_root(st, cur_val);
                    let (st1_raw, pstep) = spec_eval_expr(prog, prop, st_r);
                    let st1 = spec_cap_fuel(st1_raw, st.fuel);
                    match pstep {
                        SpecExprStep::Val(pv) => {
                            if (cur_val is Undefined) || (cur_val is Null) {
                                let st_done = spec_truncate_roots(st1, rbase);
                                spec_throw_error(st_done, ErrorKind::TypeError, spec_k_empty())
                            } else {
                                let (st2_raw, kstep) = spec_eval_to_string(prog, pv, st1);
                                let st2 = spec_truncate_roots(spec_cap_fuel(st2_raw, st1.fuel), rbase);
                                match kstep {
                                    SpecExprStep::Val(SpecVal::Str(ks)) => {
                                        if idx + 1 == steps.len() && is_delete {
                                            spec_delete_val_prop(st2, cur_val, ks)
                                        } else {
                                            let (st3, gstep) = spec_get_property_val(st2, cur_val, ks);
                                            match gstep {
                                                SpecExprStep::Val(nv) => spec_eval_opt_chain_steps(
                                                    prog,
                                                    steps,
                                                    idx + 1,
                                                    is_delete,
                                                    nv,
                                                    Some(cur_val),
                                                    st3,
                                                ),
                                                abrupt => (st3, abrupt),
                                            }
                                        }
                                    }
                                    other => (st2, other),
                                }
                            }
                        }
                        abrupt => (spec_truncate_roots(st1, rbase), abrupt),
                    }
                }
                SpecChainStep::Call { args, .. } => {
                    let this_arg = match cur_this {
                        Some(tv) => tv,
                        None => SpecVal::Undefined,
                    };
                    let rbase = st.temp_roots.len();
                    let st_r = spec_push_root(spec_push_root(st, cur_val), this_arg);
                    let (st1_raw, astep) = spec_eval_arg_list(prog, args, 0, seq![], st_r);
                    let st1 = spec_cap_fuel(st1_raw, st.fuel);
                    match astep {
                        SpecArgListStep::Vals(avals) => {
                            let (st2_raw, cstep) = spec_eval_call(prog, cur_val, this_arg, avals, st1);
                            let st2 = spec_truncate_roots(spec_cap_fuel(st2_raw, st1.fuel), rbase);
                            match cstep {
                                SpecExprStep::Val(nv) => spec_eval_opt_chain_steps(
                                    prog,
                                    steps,
                                    idx + 1,
                                    is_delete,
                                    nv,
                                    None,
                                    st2,
                                ),
                                abrupt => (st2, abrupt),
                            }
                        }
                        SpecArgListStep::Abrupt(abrupt) => (spec_truncate_roots(st1, rbase), abrupt),
                    }
                }
            }
        }
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(35)]
fn eval_opt_chain_steps(
    prog: &Program,
    steps: &Vec<ChainStep>,
    is_delete: bool,
    init_val: Val,
    st: &mut VmState,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_eval_opt_chain_steps(
            prog@,
            spec_chain_steps_view(steps@),
            0,
            is_delete,
            init_val@,
            None,
            old(st)@,
        ),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 7nat, steps@.len() as nat,
{
    let n = steps.len();
    let mut idx: usize = 0;
    let mut cur_val = init_val;
    let mut cur_this: Option<Val> = None;
    let ghost ssteps = spec_chain_steps_view(steps@);
    while idx < n
        invariant
            idx <= n == steps@.len(),
            ssteps == spec_chain_steps_view(steps@),
            st.fuel <= old(st).fuel,
            env_wf(old(st)@.envs) ==> env_wf(st@.envs),
            spec_eval_opt_chain_steps(prog@, ssteps, 0, is_delete, init_val@, None, old(st)@)
                == spec_eval_opt_chain_steps(
                    prog@,
                    ssteps,
                    idx as nat,
                    is_delete,
                    cur_val@,
                    crate::env::spec_opt_val_view(&cur_this),
                    st@,
                ),
        decreases n - idx,
    {
        proof { assert(ssteps[idx as int] == steps@[idx as int]@); }
        let step_opt = match &steps[idx] {
            ChainStep::Member { optional, .. } => *optional,
            ChainStep::Call { optional, .. } => *optional,
        };
        if step_opt && matches!(cur_val, Val::Undefined | Val::Null) {
            return ExprStep::Val(if is_delete { Val::Bool(true) } else { Val::Undefined });
        }
        match &steps[idx] {
            ChainStep::Member { prop, .. } => {
                let rbase = st.temp_roots.len();
                st.push_root(&cur_val);
                let pv = match eval_expr(prog, *prop, st) {
                    ExprStep::Val(v) => v,
                    abrupt => {
                        st.truncate_roots(rbase);
                        return abrupt;
                    }
                };
                if matches!(cur_val, Val::Undefined | Val::Null) {
                    st.truncate_roots(rbase);
                    return throw_error_exec(st, ErrorKind::TypeError, k_empty());
                }
                let kstep = eval_to_string(prog, pv, st);
                st.truncate_roots(rbase);
                let ks = match kstep {
                    ExprStep::Val(Val::Str(s)) => s,
                    other => return other,
                };
                if idx + 1 == n && is_delete {
                    return delete_val_prop_exec(st, cur_val, &ks);
                }
                match get_property_val_exec(st, &cur_val, &ks) {
                    ExprStep::Val(nv) => {
                        cur_this = Some(cur_val);
                        cur_val = nv;
                        idx += 1;
                    }
                    abrupt => return abrupt,
                }
            }
            ChainStep::Call { args, .. } => {
                let this_arg = match cur_this {
                    Some(tv) => tv,
                    None => Val::Undefined,
                };
                let rbase = st.temp_roots.len();
                st.push_root(&cur_val);
                st.push_root(&this_arg);
                let avals = match eval_arg_list(prog, args, st) {
                    ArgListStep::Vals(vs) => vs,
                    ArgListStep::Abrupt(abrupt) => {
                        st.truncate_roots(rbase);
                        return abrupt;
                    }
                };
                let cstep = eval_call(prog, cur_val, this_arg, &avals, st);
                st.truncate_roots(rbase);
                match cstep {
                    ExprStep::Val(nv) => {
                        cur_this = None;
                        cur_val = nv;
                        idx += 1;
                    }
                    abrupt => return abrupt,
                }
            }
        }
    }
    ExprStep::Val(if is_delete { Val::Bool(true) } else { cur_val })
}

pub open spec fn spec_eval_opt_chain_node(
    prog: SpecProgram,
    head: ExprId,
    steps: Seq<SpecChainStep>,
    is_delete: bool,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 8nat, 1nat,
{
    spec_eval_opt_chain_node_inner(prog, head, steps, is_delete, st)
}

#[verifier::opaque]
pub open spec fn spec_eval_opt_chain_node_inner(
    prog: SpecProgram,
    head: ExprId,
    steps: Seq<SpecChainStep>,
    is_delete: bool,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 8nat, 0nat,
{
    let (st1_raw, hstep) = spec_eval_expr(prog, head, st);
    let st1 = spec_cap_fuel(st1_raw, st.fuel);
    match hstep {
        SpecExprStep::Val(hv) => {
            let (st2_raw, res) = spec_eval_opt_chain_steps(prog, steps, 0, is_delete, hv, None, st1);
            (spec_cap_fuel(st2_raw, st1.fuel), res)
        }
        abrupt => (st1, abrupt),
    }
}

fn eval_opt_chain_node(
    prog: &Program,
    head: ExprId,
    steps: &Vec<ChainStep>,
    is_delete: bool,
    st: &mut VmState,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_eval_opt_chain_node(prog@, head, spec_chain_steps_view(steps@), is_delete, old(st)@),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 8nat, 0nat,
{
    reveal(spec_eval_opt_chain_node_inner);
    match eval_expr(prog, head, st) {
        ExprStep::Val(hv) => eval_opt_chain_steps(prog, steps, is_delete, hv, st),
        abrupt => abrupt,
    }
}

pub open spec fn spec_eval_new_node(
    prog: SpecProgram,
    callee_expr: ExprId,
    args: Seq<ExprId>,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 7nat, 1nat,
{
    spec_eval_new_node_inner(prog, callee_expr, args, st)
}

#[verifier::opaque]
pub open spec fn spec_eval_new_node_inner(
    prog: SpecProgram,
    callee_expr: ExprId,
    args: Seq<ExprId>,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 7nat, 0nat,
{
    let (st1_raw, cstep) = spec_eval_expr(prog, callee_expr, st);
    let st1 = spec_cap_fuel(st1_raw, st.fuel);
    match cstep {
        SpecExprStep::Val(cv) => {
            let rbase = st1.temp_roots.len();
            let st_r = spec_push_root(st1, cv);
            let (st2_raw, astep) = spec_eval_arg_list(prog, args, 0, seq![], st_r);
            let st2 = spec_cap_fuel(st2_raw, st1.fuel);
            match astep {
                SpecArgListStep::Vals(avals) => {
                    let (st3_raw, res) = spec_eval_new(prog, cv, avals, st2);
                    (spec_truncate_roots(spec_cap_fuel(st3_raw, st2.fuel), rbase), res)
                }
                SpecArgListStep::Abrupt(abrupt) => (spec_truncate_roots(st2, rbase), abrupt),
            }
        }
        abrupt => (st1, abrupt),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(35)]
fn eval_new_node(
    prog: &Program,
    callee_expr: ExprId,
    args: &Vec<ExprId>,
    st: &mut VmState,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_eval_new_node(prog@, callee_expr, args@, old(st)@),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 7nat, 0nat,
{
    reveal(spec_eval_new_node_inner);
    let cv = match eval_expr(prog, callee_expr, st) {
        ExprStep::Val(v) => v,
        abrupt => return abrupt,
    };
    let rbase = st.temp_roots.len();
    st.push_root(&cv);
    match eval_arg_list(prog, args, st) {
        ArgListStep::Vals(avals) => {
            let res = eval_new(prog, cv, &avals, st);
            st.truncate_roots(rbase);
            res
        }
        ArgListStep::Abrupt(abrupt) => {
            st.truncate_roots(rbase);
            abrupt
        }
    }
}

pub open spec fn spec_eval_array_lit_node(
    prog: SpecProgram,
    elements: Seq<Option<ExprId>>,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 7nat, 1nat,
{
    spec_eval_array_lit_node_inner(prog, elements, st)
}

#[verifier::opaque]
pub open spec fn spec_eval_array_lit_node_inner(
    prog: SpecProgram,
    elements: Seq<Option<ExprId>>,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 7nat, 0nat,
{
    let rbase = st.temp_roots.len();
    let (st1_raw, res) = spec_eval_array_elems(prog, elements, 0, seq![], st);
    (spec_truncate_roots(spec_cap_fuel(st1_raw, st.fuel), rbase), res)
}

fn eval_array_lit_node(
    prog: &Program,
    elements: &Vec<Option<ExprId>>,
    st: &mut VmState,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_eval_array_lit_node(prog@, elements@, old(st)@),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 7nat, 0nat,
{
    reveal(spec_eval_array_lit_node_inner);
    let rbase = st.temp_roots.len();
    let res = eval_array_elems(prog, elements, st);
    st.truncate_roots(rbase);
    res
}

pub open spec fn spec_eval_object_lit_node(
    prog: SpecProgram,
    props: Seq<SpecPropInit>,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 7nat, 1nat,
{
    spec_eval_object_lit_node_inner(prog, props, st)
}

#[verifier::opaque]
pub open spec fn spec_eval_object_lit_node_inner(
    prog: SpecProgram,
    props: Seq<SpecPropInit>,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 7nat, 0nat,
{
    let obj = SpecHeapObject {
        realm: st.intr.realm,
        prototype: Some(st.intr.object_proto),
        extensible: true,
        kind: ObjectKind::Ordinary,
        props: seq![],
    };
    let (st1, ares) = spec_state_alloc_obj(st, obj);
    match ares {
        AllocRes::QuotaExceeded => (st1, SpecExprStep::HeapQuotaExceeded),
        AllocRes::Ok(oid) => {
            let rbase = st1.temp_roots.len();
            let st_r = spec_push_root(st1, SpecVal::Object(oid));
            let (st2_raw, res) = spec_eval_obj_props(prog, oid, props, 0, st_r);
            (spec_truncate_roots(spec_cap_fuel(st2_raw, st1.fuel), rbase), res)
        }
    }
}

fn eval_object_lit_node(
    prog: &Program,
    props: &Vec<PropInit>,
    st: &mut VmState,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_eval_object_lit_node(prog@, spec_prop_inits_view(props@), old(st)@),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 7nat, 0nat,
{
    reveal(spec_eval_object_lit_node_inner);
    let obj = HeapObject {
        realm: st.intr.realm,
        prototype: Some(st.intr.object_proto),
        extensible: true,
        kind: ObjectKind::Ordinary,
        props: Vec::new(),
    };
    proof { assert(obj@.props =~= seq![]); }
    match st.alloc_obj(obj) {
        AllocRes::QuotaExceeded => ExprStep::HeapQuotaExceeded,
        AllocRes::Ok(oid) => {
            let rbase = st.temp_roots.len();
            let ov = Val::Object(oid);
            st.push_root(&ov);
            let res = eval_obj_props(prog, oid, props, st);
            st.truncate_roots(rbase);
            res
        }
    }
}

/// Rank 5: Verified Expression Evaluator (`decreases (st.fuel, 5nat, 0nat)`)
pub open spec fn spec_eval_expr(
    prog: SpecProgram,
    expr_id: ExprId,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 5nat, 1nat,
{
    spec_eval_expr_inner(prog, expr_id, st)
}

#[verifier::opaque]
pub open spec fn spec_eval_expr_inner(
    prog: SpecProgram,
    expr_id: ExprId,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 5nat, 0nat,
{
    if st.fuel == 0 {
        (st, SpecExprStep::OutOfFuel)
    } else {
        let st_dec = SpecState { fuel: (st.fuel - 1) as nat, ..st };
        if (expr_id.0 as int) >= prog.exprs.len() {
            (st_dec, SpecExprStep::Unsupported(UnsupportedFeature::InvalidAstReference))
        } else {
            let (st_out, r) = match prog.exprs[expr_id.0 as int] {
                SpecExprNode::LitUndefined => (st_dec, SpecExprStep::Val(SpecVal::Undefined)),
                SpecExprNode::LitNull => (st_dec, SpecExprStep::Val(SpecVal::Null)),
                SpecExprNode::LitBool(b) => (st_dec, SpecExprStep::Val(SpecVal::Bool(b))),
                SpecExprNode::LitNum(n) => (st_dec, SpecExprStep::Val(SpecVal::Number(n))),
                SpecExprNode::LitStr(s) => (st_dec, SpecExprStep::Val(SpecVal::Str(s))),
                SpecExprNode::This => (st_dec, SpecExprStep::Val(spec_resolve_this(st_dec.envs, st_dec.current_env))),
                SpecExprNode::Ident(nm) => spec_eval_ident_get(st_dec, nm),
                SpecExprNode::TypeofIdent(nm) => spec_eval_typeof_ident(st_dec, nm),
                SpecExprNode::DeleteIdent(nm) => spec_eval_delete_ident(st_dec, nm),
                SpecExprNode::FuncExpr { func } => spec_alloc_func_expr(prog, func, st_dec),
                SpecExprNode::UnsupportedExpr(f) => (st_dec, SpecExprStep::Unsupported(f)),
                SpecExprNode::Unary { op, arg } => spec_eval_unary_node(prog, op, arg, st_dec),
                SpecExprNode::DeleteMember { obj, prop } => spec_eval_delete_member_node(prog, obj, prop, st_dec),
                SpecExprNode::Binary { op, lhs, rhs } => spec_eval_binary_node(prog, op, lhs, rhs, st_dec),
                SpecExprNode::Logical { op, lhs, rhs } => spec_eval_logical_node(prog, op, lhs, rhs, st_dec),
                SpecExprNode::Conditional { cond, then_expr, else_expr } =>
                    spec_eval_cond_node(prog, cond, then_expr, else_expr, st_dec),
                SpecExprNode::Sequence { exprs } =>
                    spec_eval_expr_seq(prog, exprs, 0, SpecVal::Undefined, st_dec),
                SpecExprNode::AssignIdent { op, name, rhs } =>
                    spec_eval_assign_ident_node(prog, op, name, rhs, st_dec),
                SpecExprNode::AssignMember { op, obj, prop, rhs } =>
                    spec_eval_assign_member_node(prog, op, obj, prop, rhs, st_dec),
                SpecExprNode::UpdateIdent { op, prefix, name } =>
                    spec_eval_update_ident_node(prog, op, prefix, name, st_dec),
                SpecExprNode::UpdateMember { op, prefix, obj, prop } =>
                    spec_eval_update_member_node(prog, op, prefix, obj, prop, st_dec),
                SpecExprNode::Member { obj, prop, optional } =>
                    spec_eval_member_node(prog, obj, prop, optional, st_dec),
                SpecExprNode::Call { callee, optional, args } =>
                    spec_eval_call_node(prog, callee, optional, args, st_dec),
                SpecExprNode::CallMethod { obj, prop, optional, optional_call, args } =>
                    spec_eval_call_method_node(prog, obj, prop, optional, optional_call, args, st_dec),
                SpecExprNode::OptChain { head, steps, is_delete } =>
                    spec_eval_opt_chain_node(prog, head, steps, is_delete, st_dec),
                SpecExprNode::New { callee, args } =>
                    spec_eval_new_node(prog, callee, args, st_dec),
                SpecExprNode::ArrayLit { elements } =>
                    spec_eval_array_lit_node(prog, elements, st_dec),
                SpecExprNode::ObjectLit { props } =>
                    spec_eval_object_lit_node(prog, props, st_dec),
            };
            (spec_cap_fuel(st_out, st_dec.fuel), r)
        }
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(25)]
pub fn eval_expr(
    prog: &Program,
    expr_id: ExprId,
    st: &mut VmState,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_eval_expr(prog@, expr_id, old(st)@),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        !(res@ is OutOfFuel) ==> old(st).fuel > 0 && final(st).fuel < old(st).fuel,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 5nat, 0nat,
{
    reveal(spec_eval_expr_inner);
    if st.fuel == 0 {
        return ExprStep::OutOfFuel;
    }
    st.fuel -= 1;
    if expr_id.0 >= prog.exprs.len() {
        return ExprStep::Unsupported(UnsupportedFeature::InvalidAstReference);
    }
    proof { assert(prog@.exprs[expr_id.0 as int] == prog.exprs@[expr_id.0 as int]@); }
    match &prog.exprs[expr_id.0] {
        ExprNode::LitUndefined => ExprStep::Val(Val::Undefined),
        ExprNode::LitNull => ExprStep::Val(Val::Null),
        ExprNode::LitBool(b) => ExprStep::Val(Val::Bool(*b)),
        ExprNode::LitNum(n) => ExprStep::Val(Val::Number(*n)),
        ExprNode::LitStr(s) => ExprStep::Val(Val::Str(clone_js_str(s))),
        ExprNode::This => ExprStep::Val(st.envs.resolve_this(st.current_env)),
        ExprNode::Ident(nm) => eval_ident_get_exec(st, nm),
        ExprNode::TypeofIdent(nm) => eval_typeof_ident_exec(st, nm),
        ExprNode::DeleteIdent(nm) => eval_delete_ident_exec(st, nm),
        ExprNode::FuncExpr { func } => alloc_func_expr_exec(prog, *func, st),
        ExprNode::UnsupportedExpr(f) => ExprStep::Unsupported(*f),
        ExprNode::Unary { op, arg } => eval_unary_node(prog, *op, *arg, st),
        ExprNode::DeleteMember { obj, prop } => eval_delete_member_node(prog, *obj, *prop, st),
        ExprNode::Binary { op, lhs, rhs } => eval_binary_node(prog, *op, *lhs, *rhs, st),
        ExprNode::Logical { op, lhs, rhs } => eval_logical_node(prog, *op, *lhs, *rhs, st),
        ExprNode::Conditional { cond, then_expr, else_expr } =>
            eval_cond_node(prog, *cond, *then_expr, *else_expr, st),
        ExprNode::Sequence { exprs } => eval_expr_seq(prog, exprs, st),
        ExprNode::AssignIdent { op, name, rhs } => eval_assign_ident_node(prog, *op, name, *rhs, st),
        ExprNode::AssignMember { op, obj, prop, rhs } =>
            eval_assign_member_node(prog, *op, *obj, *prop, *rhs, st),
        ExprNode::UpdateIdent { op, prefix, name } =>
            eval_update_ident_node(prog, *op, *prefix, name, st),
        ExprNode::UpdateMember { op, prefix, obj, prop } =>
            eval_update_member_node(prog, *op, *prefix, *obj, *prop, st),
        ExprNode::Member { obj, prop, optional } =>
            eval_member_node(prog, *obj, *prop, *optional, st),
        ExprNode::Call { callee, optional, args } => eval_call_node(prog, *callee, *optional, args, st),
        ExprNode::CallMethod { obj, prop, optional, optional_call, args } =>
            eval_call_method_node(prog, *obj, *prop, *optional, *optional_call, args, st),
        ExprNode::OptChain { head, steps, is_delete } =>
            eval_opt_chain_node(prog, *head, steps, *is_delete, st),
        ExprNode::New { callee, args } => eval_new_node(prog, *callee, args, st),
        ExprNode::ArrayLit { elements } => eval_array_lit_node(prog, elements, st),
        ExprNode::ObjectLit { props } => eval_object_lit_node(prog, props, st),
    }
}

// ---------------------------------------------------------------------------
// Rank 9: Variable & Lexical Declaration Execution (`eval_var_decls`)
// ---------------------------------------------------------------------------

pub open spec fn spec_eval_var_decls(
    prog: SpecProgram,
    kind: VarKind,
    decls: Seq<SpecVarDeclarator>,
    idx: nat,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases st.fuel, 9nat, (decls.len() - idx) as nat,
{
    if idx >= decls.len() {
        (st, SpecExprStep::Val(SpecVal::Undefined))
    } else {
        let d = decls[idx as int];
        match kind {
            VarKind::Var => {
                match d.init {
                    None => spec_eval_var_decls(prog, kind, decls, idx + 1, st),
                    Some(eid) => {
                        let (st1_raw, step) = spec_eval_expr(prog, eid, st);
                        let st1 = spec_cap_fuel(st1_raw, st.fuel);
                        match step {
                            SpecExprStep::Val(v) => {
                                let (st2, pstep) = spec_eval_ident_put(st1, d.name, v);
                                match pstep {
                                    SpecExprStep::Val(_) => spec_eval_var_decls(prog, kind, decls, idx + 1, st2),
                                    abrupt => (st2, abrupt),
                                }
                            }
                            abrupt => (st1, abrupt),
                        }
                    }
                }
            }
            VarKind::Let | VarKind::Const => {
                let (st1, step): (SpecState, SpecExprStep) = match d.init {
                    None => (st, SpecExprStep::Val(SpecVal::Undefined)),
                    Some(eid) => {
                        let (s_raw, s_step) = spec_eval_expr(prog, eid, st);
                        (spec_cap_fuel(s_raw, st.fuel), s_step)
                    }
                };
                match step {
                    SpecExprStep::Val(v) => {
                        let e2 = spec_initialize_lexical(st1.envs, st1.current_env, d.name, v);
                        spec_eval_var_decls(prog, kind, decls, idx + 1, SpecState { envs: e2, ..st1 })
                    }
                    abrupt => (st1, abrupt),
                }
            }
        }
    }
}

fn eval_var_decls(
    prog: &Program,
    kind: VarKind,
    decls: &Vec<VarDeclarator>,
    st: &mut VmState,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_eval_var_decls(prog@, kind, spec_var_decls_view(decls@), 0, old(st)@),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 9nat, decls@.len() as nat,
{
    let n = decls.len();
    let mut i: usize = 0;
    let ghost sdecls = spec_var_decls_view(decls@);
    while i < n
        invariant
            i <= n == decls@.len(),
            sdecls == spec_var_decls_view(decls@),
            st.fuel <= old(st).fuel,
            env_wf(old(st)@.envs) ==> env_wf(st@.envs),
            spec_eval_var_decls(prog@, kind, sdecls, 0, old(st)@)
                == spec_eval_var_decls(prog@, kind, sdecls, i as nat, st@),
        decreases n - i,
    {
        proof { assert(sdecls[i as int] == decls@[i as int]@); }
        match kind {
            VarKind::Var => {
                match decls[i].init {
                    None => {
                        i += 1;
                    }
                    Some(eid) => {
                        match eval_expr(prog, eid, st) {
                            ExprStep::Val(v) => {
                                let pstep = eval_ident_put_exec(st, &decls[i].name, v);
                                match &pstep {
                                    ExprStep::Val(_) => {
                                        i += 1;
                                    }
                                    _ => return pstep,
                                }
                            }
                            abrupt => return abrupt,
                        }
                    }
                }
            }
            VarKind::Let | VarKind::Const => {
                let step = match decls[i].init {
                    None => ExprStep::Val(Val::Undefined),
                    Some(eid) => eval_expr(prog, eid, st),
                };
                match step {
                    ExprStep::Val(v) => {
                        let cenv = st.current_env;
                        st.envs.initialize_lexical(cenv, &decls[i].name, v);
                        i += 1;
                    }
                    abrupt => return abrupt,
                }
            }
        }
    }
    ExprStep::Val(Val::Undefined)
}

// ---------------------------------------------------------------------------
// Ranks 10..14: Statements, Blocks, Control Flow, `switch`, `try/catch/finally`
// ---------------------------------------------------------------------------

pub open spec fn spec_expr_abrupt_to_stmt(es: SpecExprStep) -> SpecStmtStep {
    match es {
        SpecExprStep::Val(v) => SpecStmtStep::Comp(SpecCompletion::Normal(SpecCompletionValue::Present(v))),
        SpecExprStep::Throw(v) => SpecStmtStep::Comp(SpecCompletion::Throw(v)),
        SpecExprStep::HeapQuotaExceeded => SpecStmtStep::HeapQuotaExceeded,
        SpecExprStep::OutOfFuel => SpecStmtStep::OutOfFuel,
        SpecExprStep::Unsupported(f) => SpecStmtStep::Unsupported(f),
    }
}

fn expr_abrupt_to_stmt(es: ExprStep) -> (r: StmtStep)
    ensures
        r@ == spec_expr_abrupt_to_stmt(es@),
        (r@ is OutOfFuel) == (es@ is OutOfFuel),
        !(es@ is Val) ==> !(r@ == SpecStmtStep::Comp(SpecCompletion::Normal(r@->Comp_0->Normal_0)))
            && !(r@ is Comp && (r@->Comp_0 is Normal || r@->Comp_0 is Continue)),
{
    match es {
        ExprStep::Val(v) => StmtStep::Comp(Completion::normal_val(v)),
        ExprStep::Throw(v) => StmtStep::Comp(Completion::Throw(v)),
        ExprStep::HeapQuotaExceeded => StmtStep::HeapQuotaExceeded,
        ExprStep::OutOfFuel => StmtStep::OutOfFuel,
        ExprStep::Unsupported(f) => StmtStep::Unsupported(f),
    }
}

pub open spec fn spec_push_comp_root(st: SpecState, c: SpecCompletion) -> SpecState {
    match c {
        SpecCompletion::Normal(SpecCompletionValue::Present(v))
        | SpecCompletion::Break(SpecCompletionValue::Present(v), _)
        | SpecCompletion::Continue(SpecCompletionValue::Present(v), _)
        | SpecCompletion::Return(v)
        | SpecCompletion::Throw(v) => spec_push_root(st, v),
        _ => st,
    }
}

fn push_comp_root_exec(st: &mut VmState, c: &Completion)
    ensures
        final(st)@ == spec_push_comp_root(old(st)@, c@),
        final(st).fuel == old(st).fuel,
{
    match c {
        Completion::Normal(CompletionValue::Present(v))
        | Completion::Break(CompletionValue::Present(v), _)
        | Completion::Continue(CompletionValue::Present(v), _)
        | Completion::Return(v)
        | Completion::Throw(v) => st.push_root(v),
        _ => {}
    }
}

/// Rank 11: Statement List Evaluation (`UpdateEmpty` threading per §14.2.2)
pub open spec fn spec_eval_stmt_list(
    prog: SpecProgram,
    stmts: Seq<StmtId>,
    idx: nat,
    prev_cv: SpecCompletionValue,
    st: SpecState,
) -> (SpecState, SpecStmtStep)
    decreases st.fuel, 11nat, (stmts.len() - idx) as nat,
{
    if idx >= stmts.len() {
        (st, SpecStmtStep::Comp(SpecCompletion::Normal(prev_cv)))
    } else {
        let rbase = st.temp_roots.len();
        let st_r = match prev_cv {
            SpecCompletionValue::Present(v) => spec_push_root(st, v),
            SpecCompletionValue::Empty => st,
        };
        let (st1_raw, step) = spec_eval_stmt(prog, stmts[idx as int], st_r);
        let st1 = spec_truncate_roots(spec_cap_fuel(st1_raw, st.fuel), rbase);
        match step {
            SpecStmtStep::Comp(c) => {
                let updated = spec_update_empty(c, prev_cv);
                match updated {
                    SpecCompletion::Normal(next_cv) =>
                        spec_eval_stmt_list(prog, stmts, idx + 1, next_cv, st1),
                    abrupt_c => (st1, SpecStmtStep::Comp(abrupt_c)),
                }
            }
            other => (st1, other),
        }
    }
}

pub fn eval_stmt_list(
    prog: &Program,
    stmts: &Vec<StmtId>,
    init_cv: CompletionValue,
    st: &mut VmState,
) -> (res: StmtStep)
    ensures
        (final(st)@, res@) == spec_eval_stmt_list(prog@, stmts@, 0, init_cv@, old(st)@),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 11nat, stmts@.len() as nat,
{
    let n = stmts.len();
    let mut i: usize = 0;
    let mut cur_cv = init_cv;
    while i < n
        invariant
            i <= n == stmts@.len(),
            st.fuel <= old(st).fuel,
            env_wf(old(st)@.envs) ==> env_wf(st@.envs),
            spec_eval_stmt_list(prog@, stmts@, 0, init_cv@, old(st)@)
                == spec_eval_stmt_list(prog@, stmts@, i as nat, cur_cv@, st@),
        decreases n - i,
    {
        let rbase = st.temp_roots.len();
        if let CompletionValue::Present(ref v) = cur_cv {
            st.push_root(v);
        }
        let sid = stmts[i];
        let step = eval_stmt(prog, sid, st);
        st.truncate_roots(rbase);
        match step {
            StmtStep::Comp(c) => {
                let updated = update_empty(c, cur_cv);
                match updated {
                    Completion::Normal(next_cv) => {
                        cur_cv = next_cv;
                        i += 1;
                    }
                    abrupt_c => return StmtStep::Comp(abrupt_c),
                }
            }
            other => return other,
        }
    }
    StmtStep::Comp(Completion::Normal(cur_cv))
}

/// Rank 12: Lexical Block Statement (§14.2.2)
pub open spec fn spec_eval_block_stmt(
    prog: SpecProgram,
    stmts: Seq<StmtId>,
    st: SpecState,
) -> (SpecState, SpecStmtStep)
    decreases st.fuel, 12nat, 0nat,
{
    if stmts.len() == 0 {
        (st, SpecStmtStep::Comp(SpecCompletion::Normal(SpecCompletionValue::Empty)))
    } else {
        let saved_env = st.current_env;
        let (envs1, blk_env) = spec_alloc_env(st.envs, EnvKind::Block, saved_env, None);
        let st1 = SpecState { envs: envs1, current_env: blk_env, ..st };
        let (st2_raw, hstep) = spec_hoist_block_stmts(prog, stmts, 0, blk_env, st1);
        let st2 = spec_cap_fuel(st2_raw, st1.fuel);
        match hstep {
            SpecExprStep::Val(_) => {
                let (st3_raw, bstep) = spec_eval_stmt_list(prog, stmts, 0, SpecCompletionValue::Empty, st2);
                let st3 = SpecState { current_env: saved_env, ..spec_cap_fuel(st3_raw, st2.fuel) };
                (st3, bstep)
            }
            abrupt => (SpecState { current_env: saved_env, ..st2 }, spec_expr_abrupt_to_stmt(abrupt)),
        }
    }
}

fn eval_block_stmt(
    prog: &Program,
    stmts: &Vec<StmtId>,
    st: &mut VmState,
) -> (res: StmtStep)
    ensures
        (final(st)@, res@) == spec_eval_block_stmt(prog@, stmts@, old(st)@),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 12nat, 0nat,
{
    if stmts.len() == 0 {
        return StmtStep::Comp(Completion::normal_empty());
    }
    let saved_env = st.current_env;
    let blk_env = st.envs.alloc_env(EnvKind::Block, saved_env, None);
    st.current_env = blk_env;
    let hstep = hoist_block_stmts_exec(prog, stmts, blk_env, st);
    match hstep {
        ExprStep::Val(_) => {
            let bstep = eval_stmt_list(prog, stmts, CompletionValue::Empty, st);
            st.current_env = saved_env;
            bstep
        }
        abrupt => {
            st.current_env = saved_env;
            expr_abrupt_to_stmt(abrupt)
        }
    }
}

/// Rank 12: `if (cond) then_branch else else_branch` (§14.6.2)
pub open spec fn spec_eval_if_stmt(
    prog: SpecProgram,
    cond: ExprId,
    then_branch: StmtId,
    else_branch: Option<StmtId>,
    st: SpecState,
) -> (SpecState, SpecStmtStep)
    decreases st.fuel, 12nat, 0nat,
{
    let (st1_raw, cstep) = spec_eval_expr(prog, cond, st);
    let st1 = spec_cap_fuel(st1_raw, st.fuel);
    match cstep {
        SpecExprStep::Val(cv) => {
            if spec_to_boolean(cv) {
                let (st2_raw, tstep) = spec_eval_stmt(prog, then_branch, st1);
                let st2 = spec_cap_fuel(st2_raw, st1.fuel);
                match tstep {
                    SpecStmtStep::Comp(c) => (
                        st2,
                        SpecStmtStep::Comp(spec_update_empty(c, SpecCompletionValue::Present(SpecVal::Undefined))),
                    ),
                    other => (st2, other),
                }
            } else {
                match else_branch {
                    Some(eb) => {
                        let (st2_raw, estep) = spec_eval_stmt(prog, eb, st1);
                        let st2 = spec_cap_fuel(st2_raw, st1.fuel);
                        match estep {
                            SpecStmtStep::Comp(c) => (
                                st2,
                                SpecStmtStep::Comp(spec_update_empty(c, SpecCompletionValue::Present(SpecVal::Undefined))),
                            ),
                            other => (st2, other),
                        }
                    }
                    None => (st1, SpecStmtStep::Comp(SpecCompletion::Normal(SpecCompletionValue::Present(SpecVal::Undefined)))),
                }
            }
        }
        abrupt => (st1, spec_expr_abrupt_to_stmt(abrupt)),
    }
}

fn eval_if_stmt(
    prog: &Program,
    cond: ExprId,
    then_branch: StmtId,
    else_branch: Option<StmtId>,
    st: &mut VmState,
) -> (res: StmtStep)
    ensures
        (final(st)@, res@) == spec_eval_if_stmt(prog@, cond, then_branch, else_branch, old(st)@),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 12nat, 0nat,
{
    match eval_expr(prog, cond, st) {
        ExprStep::Val(cv) => {
            if val_to_boolean(&cv) {
                match eval_stmt(prog, then_branch, st) {
                    StmtStep::Comp(c) => StmtStep::Comp(update_empty(c, CompletionValue::Present(Val::Undefined))),
                    other => other,
                }
            } else {
                match else_branch {
                    Some(eb) => match eval_stmt(prog, eb, st) {
                        StmtStep::Comp(c) => StmtStep::Comp(update_empty(c, CompletionValue::Present(Val::Undefined))),
                        other => other,
                    },
                    None => StmtStep::Comp(Completion::normal_val(Val::Undefined)),
                }
            }
        }
        abrupt => expr_abrupt_to_stmt(abrupt),
    }
}

/// Rank 12: `label: body` (§14.13.3)
pub open spec fn spec_eval_labeled_stmt(
    prog: SpecProgram,
    label: Seq<u16>,
    body: StmtId,
    st: SpecState,
) -> (SpecState, SpecStmtStep)
    decreases st.fuel, 12nat, 0nat,
{
    let (st1_raw, bstep) = spec_eval_stmt(prog, body, st);
    let st1 = spec_cap_fuel(st1_raw, st.fuel);
    match bstep {
        SpecStmtStep::Comp(SpecCompletion::Break(cv, Some(target))) => {
            if target == label {
                (st1, SpecStmtStep::Comp(SpecCompletion::Normal(cv)))
            } else {
                (st1, SpecStmtStep::Comp(SpecCompletion::Break(cv, Some(target))))
            }
        }
        other => (st1, other),
    }
}

fn eval_labeled_stmt(
    prog: &Program,
    label: &JsStr,
    body: StmtId,
    st: &mut VmState,
) -> (res: StmtStep)
    ensures
        (final(st)@, res@) == spec_eval_labeled_stmt(prog@, label@, body, old(st)@),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 12nat, 0nat,
{
    match eval_stmt(prog, body, st) {
        StmtStep::Comp(Completion::Break(cv, Some(target))) => {
            if js_str_eq(&target, label) {
                StmtStep::Comp(Completion::Normal(cv))
            } else {
                StmtStep::Comp(Completion::Break(cv, Some(target)))
            }
        }
        other => other,
    }
}

// ---------------------------------------------------------------------------
// Rank 12 & 13: `switch` Statement (§14.12.2) with Fallthrough & `default`
// ---------------------------------------------------------------------------

pub open spec fn spec_hoist_switch_cases(
    prog: SpecProgram,
    cases: Seq<SpecSwitchCase>,
    idx: nat,
    sw_env: EnvId,
    st: SpecState,
) -> (SpecState, SpecExprStep)
    decreases cases.len() - idx,
{
    if idx >= cases.len() {
        (st, SpecExprStep::Val(SpecVal::Undefined))
    } else {
        let (st1, hstep) = spec_hoist_block_stmts(prog, cases[idx as int].consequent, 0, sw_env, st);
        match hstep {
            SpecExprStep::Val(_) => spec_hoist_switch_cases(prog, cases, idx + 1, sw_env, st1),
            abrupt => (st1, abrupt),
        }
    }
}

fn hoist_switch_cases_exec(
    prog: &Program,
    cases: &Vec<SwitchCase>,
    sw_env: EnvId,
    st: &mut VmState,
) -> (res: ExprStep)
    ensures
        (final(st)@, res@) == spec_hoist_switch_cases(prog@, spec_switch_cases_view(cases@), 0, sw_env, old(st)@),
        final(st).fuel == old(st).fuel,
        !(res@ is OutOfFuel),
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
{
    let n = cases.len();
    let mut i: usize = 0;
    let ghost scases = spec_switch_cases_view(cases@);
    while i < n
        invariant
            i <= n == cases@.len(),
            scases == spec_switch_cases_view(cases@),
            st.fuel == old(st).fuel,
            env_wf(old(st)@.envs) ==> env_wf(st@.envs),
            spec_hoist_switch_cases(prog@, scases, 0, sw_env, old(st)@)
                == spec_hoist_switch_cases(prog@, scases, i as nat, sw_env, st@),
        decreases n - i,
    {
        proof { assert(scases[i as int] == cases@[i as int]@); }
        let hstep = hoist_block_stmts_exec(prog, &cases[i].consequent, sw_env, st);
        match &hstep {
            ExprStep::Val(_) => {
                i += 1;
            }
            _ => return hstep,
        }
    }
    ExprStep::Val(Val::Undefined)
}

pub enum SwitchFindRes {
    Found(Option<usize>),
    Abrupt(ExprStep),
}

pub enum SpecSwitchFindRes {
    Found(Option<usize>),
    Abrupt(SpecExprStep),
}

impl View for SwitchFindRes {
    type V = SpecSwitchFindRes;

    open spec fn view(&self) -> SpecSwitchFindRes {
        match self {
            SwitchFindRes::Found(o) => SpecSwitchFindRes::Found(*o),
            SwitchFindRes::Abrupt(e) => SpecSwitchFindRes::Abrupt(e@),
        }
    }
}

pub open spec fn spec_find_switch_case(
    prog: SpecProgram,
    disc: SpecVal,
    cases: Seq<SpecSwitchCase>,
    idx: nat,
    default_idx: Option<usize>,
    st: SpecState,
) -> (SpecState, SpecSwitchFindRes)
    decreases st.fuel, 12nat, cases.len() - idx,
{
    if idx >= cases.len() {
        (st, SpecSwitchFindRes::Found(default_idx))
    } else {
        match cases[idx as int].test {
            None => spec_find_switch_case(prog, disc, cases, idx + 1, Some(idx as usize), st),
            Some(te) => {
                let (st1_raw, tstep) = spec_eval_expr(prog, te, st);
                let st1 = spec_cap_fuel(st1_raw, st.fuel);
                match tstep {
                    SpecExprStep::Val(tv) => {
                        if spec_strict_eq(tv, disc) {
                            (st1, SpecSwitchFindRes::Found(Some(idx as usize)))
                        } else {
                            spec_find_switch_case(prog, disc, cases, idx + 1, default_idx, st1)
                        }
                    }
                    abrupt => (st1, SpecSwitchFindRes::Abrupt(abrupt)),
                }
            }
        }
    }
}

fn find_switch_case_exec(
    prog: &Program,
    disc: &Val,
    cases: &Vec<SwitchCase>,
    st: &mut VmState,
) -> (res: SwitchFindRes)
    ensures
        (final(st)@, res@) == spec_find_switch_case(prog@, disc@, spec_switch_cases_view(cases@), 0, None, old(st)@),
        final(st).fuel <= old(st).fuel,
        match res@ {
            SpecSwitchFindRes::Found(_) => true,
            SpecSwitchFindRes::Abrupt(es) => (es is OutOfFuel) ==> final(st).fuel == 0,
        },
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 12nat, cases@.len() as nat,
{
    let n = cases.len();
    let mut idx: usize = 0;
    let mut default_idx: Option<usize> = None;
    let ghost scases = spec_switch_cases_view(cases@);
    while idx < n
        invariant
            idx <= n == cases@.len(),
            scases == spec_switch_cases_view(cases@),
            st.fuel <= old(st).fuel,
            env_wf(old(st)@.envs) ==> env_wf(st@.envs),
            spec_find_switch_case(prog@, disc@, scases, 0, None, old(st)@)
                == spec_find_switch_case(prog@, disc@, scases, idx as nat, default_idx, st@),
        decreases n - idx,
    {
        proof { assert(scases[idx as int] == cases@[idx as int]@); }
        match cases[idx].test {
            None => {
                default_idx = Some(idx);
                idx += 1;
            }
            Some(te) => {
                match eval_expr(prog, te, st) {
                    ExprStep::Val(tv) => {
                        if val_strict_eq(&tv, disc) {
                            return SwitchFindRes::Found(Some(idx));
                        } else {
                            idx += 1;
                        }
                    }
                    abrupt => return SwitchFindRes::Abrupt(abrupt),
                }
            }
        }
    }
    SwitchFindRes::Found(default_idx)
}

pub open spec fn spec_exec_switch_from(
    prog: SpecProgram,
    label: Option<Seq<u16>>,
    cases: Seq<SpecSwitchCase>,
    idx: nat,
    cur_cv: SpecCompletionValue,
    st: SpecState,
) -> (SpecState, SpecStmtStep)
    decreases st.fuel, 12nat, cases.len() - idx,
{
    if idx >= cases.len() {
        (st, SpecStmtStep::Comp(SpecCompletion::Normal(SpecCompletionValue::Present(spec_unwrap_or_undefined(cur_cv)))))
    } else {
        let (st1_raw, step) = spec_eval_stmt_list(prog, cases[idx as int].consequent, 0, cur_cv, st);
        let st1 = spec_cap_fuel(st1_raw, st.fuel);
        match step {
            SpecStmtStep::Comp(SpecCompletion::Normal(next_cv)) =>
                spec_exec_switch_from(prog, label, cases, idx + 1, next_cv, st1),
            SpecStmtStep::Comp(SpecCompletion::Break(bcv, target)) => {
                let merged = spec_update_empty_val(bcv, cur_cv);
                if spec_loop_target_matches(label, target) {
                    (st1, SpecStmtStep::Comp(SpecCompletion::Normal(SpecCompletionValue::Present(spec_unwrap_or_undefined(merged)))))
                } else {
                    (st1, SpecStmtStep::Comp(SpecCompletion::Break(merged, target)))
                }
            }
            SpecStmtStep::Comp(SpecCompletion::Continue(ccv, target)) => {
                let merged = spec_update_empty_val(ccv, cur_cv);
                (st1, SpecStmtStep::Comp(SpecCompletion::Continue(merged, target)))
            }
            other => (st1, other),
        }
    }
}

fn exec_switch_from(
    prog: &Program,
    label: &Option<JsStr>,
    cases: &Vec<SwitchCase>,
    start_idx: usize,
    st: &mut VmState,
) -> (res: StmtStep)
    ensures
        (final(st)@, res@) == spec_exec_switch_from(
            prog@,
            spec_opt_str_view(label),
            spec_switch_cases_view(cases@),
            start_idx as nat,
            SpecCompletionValue::Empty,
            old(st)@,
        ),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 12nat, if start_idx <= cases@.len() { (cases@.len() - start_idx) as nat } else { 0nat },
{
    let n = cases.len();
    if start_idx >= n {
        return StmtStep::Comp(Completion::normal_val(Val::Undefined));
    }
    let mut idx = start_idx;
    let mut cur_cv = CompletionValue::Empty;
    let ghost scases = spec_switch_cases_view(cases@);
    let ghost slbl = spec_opt_str_view(label);
    while idx < n
        invariant
            start_idx <= idx <= n == cases@.len(),
            scases == spec_switch_cases_view(cases@),
            slbl == spec_opt_str_view(label),
            st.fuel <= old(st).fuel,
            env_wf(old(st)@.envs) ==> env_wf(st@.envs),
            spec_exec_switch_from(prog@, slbl, scases, start_idx as nat, SpecCompletionValue::Empty, old(st)@)
                == spec_exec_switch_from(prog@, slbl, scases, idx as nat, cur_cv@, st@),
        decreases n - idx,
    {
        proof { assert(scases[idx as int] == cases@[idx as int]@); }
        let cur_cv_copy = match &cur_cv {
            CompletionValue::Empty => CompletionValue::Empty,
            CompletionValue::Present(v) => CompletionValue::Present(clone_val(v)),
        };
        let step = eval_stmt_list(prog, &cases[idx].consequent, cur_cv_copy, st);
        match step {
            StmtStep::Comp(Completion::Normal(next_cv)) => {
                cur_cv = next_cv;
                idx += 1;
            }
            StmtStep::Comp(Completion::Break(bcv, target)) => {
                let merged = update_empty_val(bcv, cur_cv);
                if loop_target_matches_exec(label, &target) {
                    return StmtStep::Comp(Completion::normal_val(unwrap_or_undefined(merged)));
                } else {
                    return StmtStep::Comp(Completion::Break(merged, target));
                }
            }
            StmtStep::Comp(Completion::Continue(ccv, target)) => {
                let merged = update_empty_val(ccv, cur_cv);
                return StmtStep::Comp(Completion::Continue(merged, target));
            }
            other => return other,
        }
    }
    StmtStep::Comp(Completion::normal_val(unwrap_or_undefined(cur_cv)))
}

pub open spec fn spec_eval_switch_stmt(
    prog: SpecProgram,
    label: Option<Seq<u16>>,
    discriminant: ExprId,
    cases: Seq<SpecSwitchCase>,
    st: SpecState,
) -> (SpecState, SpecStmtStep)
    decreases st.fuel, 13nat, 0nat,
{
    let (st1_raw, dstep) = spec_eval_expr(prog, discriminant, st);
    let st1 = spec_cap_fuel(st1_raw, st.fuel);
    match dstep {
        SpecExprStep::Val(disc) => {
            let saved_env = st1.current_env;
            let rbase = st1.temp_roots.len();
            let st_r = spec_push_root(st1, disc);
            let (envs2, sw_env) = spec_alloc_env(st_r.envs, EnvKind::Block, saved_env, None);
            let st2 = SpecState { envs: envs2, current_env: sw_env, ..st_r };
            let (st3_raw, hstep) = spec_hoist_switch_cases(prog, cases, 0, sw_env, st2);
            let st3 = spec_cap_fuel(st3_raw, st2.fuel);
            match hstep {
                SpecExprStep::Val(_) => {
                    let (st4_raw, fres) = spec_find_switch_case(prog, disc, cases, 0, None, st3);
                    let st4 = spec_truncate_roots(spec_cap_fuel(st4_raw, st3.fuel), rbase);
                    match fres {
                        SpecSwitchFindRes::Found(None) => (
                            SpecState { current_env: saved_env, ..st4 },
                            SpecStmtStep::Comp(SpecCompletion::Normal(SpecCompletionValue::Present(SpecVal::Undefined))),
                        ),
                        SpecSwitchFindRes::Found(Some(sidx)) => {
                            let (st5_raw, eres) = spec_exec_switch_from(prog, label, cases, sidx as nat, SpecCompletionValue::Empty, st4);
                            (SpecState { current_env: saved_env, ..spec_cap_fuel(st5_raw, st4.fuel) }, eres)
                        }
                        SpecSwitchFindRes::Abrupt(abrupt) => (
                            SpecState { current_env: saved_env, ..st4 },
                            spec_expr_abrupt_to_stmt(abrupt),
                        ),
                    }
                }
                abrupt => (
                    SpecState { current_env: saved_env, ..spec_truncate_roots(st3, rbase) },
                    spec_expr_abrupt_to_stmt(abrupt),
                ),
            }
        }
        abrupt => (st1, spec_expr_abrupt_to_stmt(abrupt)),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(25)]
fn eval_switch_stmt(
    prog: &Program,
    label: &Option<JsStr>,
    discriminant: ExprId,
    cases: &Vec<SwitchCase>,
    st: &mut VmState,
) -> (res: StmtStep)
    ensures
        (final(st)@, res@) == spec_eval_switch_stmt(
            prog@,
            spec_opt_str_view(label),
            discriminant,
            spec_switch_cases_view(cases@),
            old(st)@,
        ),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 13nat, 0nat,
{
    let disc = match eval_expr(prog, discriminant, st) {
        ExprStep::Val(v) => v,
        abrupt => return expr_abrupt_to_stmt(abrupt),
    };
    let saved_env = st.current_env;
    let rbase = st.temp_roots.len();
    st.push_root(&disc);
    let sw_env = st.envs.alloc_env(EnvKind::Block, saved_env, None);
    st.current_env = sw_env;
    let hstep = hoist_switch_cases_exec(prog, cases, sw_env, st);
    match hstep {
        ExprStep::Val(_) => {
            let fres = find_switch_case_exec(prog, &disc, cases, st);
            st.truncate_roots(rbase);
            match fres {
                SwitchFindRes::Found(None) => {
                    st.current_env = saved_env;
                    StmtStep::Comp(Completion::normal_val(Val::Undefined))
                }
                SwitchFindRes::Found(Some(sidx)) => {
                    let eres = exec_switch_from(prog, label, cases, sidx, st);
                    st.current_env = saved_env;
                    eres
                }
                SwitchFindRes::Abrupt(abrupt) => {
                    st.current_env = saved_env;
                    expr_abrupt_to_stmt(abrupt)
                }
            }
        }
        abrupt => {
            st.truncate_roots(rbase);
            st.current_env = saved_env;
            expr_abrupt_to_stmt(abrupt)
        }
    }
}

// ---------------------------------------------------------------------------
// Rank 13: `try / catch(e) / finally` with Exact ECMA-262 §14.15.3 Override
// ---------------------------------------------------------------------------

pub open spec fn spec_eval_try_stmt(
    prog: SpecProgram,
    block: StmtId,
    catch_param: Option<Seq<u16>>,
    catch_body: Option<StmtId>,
    finally_body: Option<StmtId>,
    st: SpecState,
) -> (SpecState, SpecStmtStep)
    decreases st.fuel, 13nat, 0nat,
{
    let (st1_raw, bstep) = spec_eval_stmt(prog, block, st);
    let st1 = spec_cap_fuel(st1_raw, st.fuel);
    let (st2, cstep): (SpecState, SpecStmtStep) = match bstep {
        SpecStmtStep::Comp(SpecCompletion::Throw(exc)) => {
            match catch_body {
                Some(cbody) => {
                    let saved_env = st1.current_env;
                    let (envs_c, c_env) = spec_alloc_env(st1.envs, EnvKind::Catch, saved_env, None);
                    let envs_c2 = match catch_param {
                        Some(pnm) => spec_bind_initialized(envs_c, c_env, pnm, exc, true, st1.strict),
                        None => envs_c,
                    };
                    let st_c = SpecState { envs: envs_c2, current_env: c_env, ..st1 };
                    let (st_c_out, c_res) = spec_eval_stmt(prog, cbody, st_c);
                    (SpecState { current_env: saved_env, ..spec_cap_fuel(st_c_out, st1.fuel) }, c_res)
                }
                None => (st1, SpecStmtStep::Comp(SpecCompletion::Throw(exc))),
            }
        }
        other => (st1, other),
    };
    match cstep {
        SpecStmtStep::Comp(c_comp) => {
            match finally_body {
                None => (
                    st2,
                    SpecStmtStep::Comp(spec_update_empty(c_comp, SpecCompletionValue::Present(SpecVal::Undefined))),
                ),
                Some(fbody) => {
                    let rbase = st2.temp_roots.len();
                    let st_r = spec_push_comp_root(st2, c_comp);
                    let (st3_raw, fstep) = spec_eval_stmt(prog, fbody, st_r);
                    let st3 = spec_truncate_roots(spec_cap_fuel(st3_raw, st2.fuel), rbase);
                    match fstep {
                        SpecStmtStep::Comp(f_comp) => {
                            // ECMA-262 §14.15.3: If F.[[Type]] is normal, set F to C; else F overrides C!
                            let chosen = match f_comp {
                                SpecCompletion::Normal(_) => c_comp,
                                abrupt_f => abrupt_f,
                            };
                            (
                                st3,
                                SpecStmtStep::Comp(spec_update_empty(chosen, SpecCompletionValue::Present(SpecVal::Undefined))),
                            )
                        }
                        other_f => (st3, other_f),
                    }
                }
            }
        }
        non_comp => (st2, non_comp),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(25)]
fn eval_try_stmt(
    prog: &Program,
    block: StmtId,
    catch_param: &Option<JsStr>,
    catch_body: Option<StmtId>,
    finally_body: Option<StmtId>,
    st: &mut VmState,
) -> (res: StmtStep)
    ensures
        (final(st)@, res@) == spec_eval_try_stmt(
            prog@,
            block,
            spec_opt_str_view(catch_param),
            catch_body,
            finally_body,
            old(st)@,
        ),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 13nat, 0nat,
{
    let bstep = eval_stmt(prog, block, st);
    let cstep = match bstep {
        StmtStep::Comp(Completion::Throw(exc)) => {
            match catch_body {
                Some(cbody) => {
                    let saved_env = st.current_env;
                    let c_env = st.envs.alloc_env(EnvKind::Catch, saved_env, None);
                    if let Some(pnm) = catch_param {
                        let strict = st.strict;
                        st.envs.bind_initialized(c_env, clone_js_str(pnm), exc, true, strict);
                    }
                    st.current_env = c_env;
                    let c_res = eval_stmt(prog, cbody, st);
                    st.current_env = saved_env;
                    c_res
                }
                None => StmtStep::Comp(Completion::Throw(exc)),
            }
        }
        other => other,
    };
    match cstep {
        StmtStep::Comp(c_comp) => {
            match finally_body {
                None => StmtStep::Comp(update_empty(c_comp, CompletionValue::Present(Val::Undefined))),
                Some(fbody) => {
                    let rbase = st.temp_roots.len();
                    push_comp_root_exec(st, &c_comp);
                    let fstep = eval_stmt(prog, fbody, st);
                    st.truncate_roots(rbase);
                    match fstep {
                        StmtStep::Comp(f_comp) => {
                            let chosen = match f_comp {
                                Completion::Normal(_) => c_comp,
                                abrupt_f => abrupt_f,
                            };
                            StmtStep::Comp(update_empty(chosen, CompletionValue::Present(Val::Undefined)))
                        }
                        other_f => other_f,
                    }
                }
            }
        }
        non_comp => non_comp,
    }
}

// ---------------------------------------------------------------------------
// Rank 13 & 14: `for-in`, `for-of`, `while`, `do-while`, `for` Loops
// ---------------------------------------------------------------------------

pub open spec fn spec_str_index_keys(len: usize, idx: nat, acc: Seq<Seq<u16>>) -> Seq<Seq<u16>>
    decreases (len as nat) - idx,
{
    if idx >= (len as nat) {
        acc
    } else {
        spec_str_index_keys(len, idx + 1, acc.push(spec_index_key(idx as usize)))
    }
}

fn build_str_index_keys_exec(len: usize) -> (out: Vec<JsStr>)
    ensures spec_str_seq_view(out@) == spec_str_index_keys(len, 0, seq![]),
{
    let mut out: Vec<JsStr> = Vec::new();
    let mut i: usize = 0;
    proof { assert(spec_str_seq_view(out@) =~= Seq::<Seq<u16>>::empty()); }
    while i < len
        invariant
            i <= len,
            spec_str_index_keys(len, 0, seq![]) == spec_str_index_keys(len, i as nat, spec_str_seq_view(out@)),
        decreases len - i,
    {
        let ghost pre = spec_str_seq_view(out@);
        let ik = index_key_exec(i);
        out.push(ik);
        proof { assert(spec_str_seq_view(out@) =~= pre.push(spec_index_key(i))); }
        i += 1;
    }
    out
}

pub open spec fn spec_bind_for_each_iter(
    lhs: SpecForEachLhs,
    val: SpecVal,
    outer_env: EnvId,
    body_id: StmtId,
    prog: SpecProgram,
    st: SpecState,
) -> (SpecState, SpecStmtStep)
    decreases st.fuel, 12nat, 2nat,
{
    spec_bind_for_each_iter_inner(lhs, val, outer_env, body_id, prog, st)
}

#[verifier::opaque]
pub open spec fn spec_bind_for_each_iter_inner(
    lhs: SpecForEachLhs,
    val: SpecVal,
    outer_env: EnvId,
    body_id: StmtId,
    prog: SpecProgram,
    st: SpecState,
) -> (SpecState, SpecStmtStep)
    decreases st.fuel, 12nat, 1nat,
{
    match lhs {
        SpecForEachLhs::Decl { kind: VarKind::Let, name }
        | SpecForEachLhs::Decl { kind: VarKind::Const, name } => {
            let mutable = matches!(lhs, SpecForEachLhs::Decl { kind: VarKind::Let, .. });
            let erbase = st.env_roots.len();
            let (e1, iter_env) = spec_alloc_env(st.envs, EnvKind::Block, outer_env, None);
            let e2 = spec_bind_initialized(e1, iter_env, name, val, mutable, true);
            let st1 = spec_push_env_root(SpecState { envs: e2, current_env: iter_env, ..st }, outer_env);
            let (st2_raw, bstep) = spec_eval_stmt(prog, body_id, st1);
            (
                spec_truncate_env_roots(SpecState { current_env: outer_env, ..spec_cap_fuel(st2_raw, st1.fuel) }, erbase),
                bstep,
            )
        }
        SpecForEachLhs::Decl { kind: VarKind::Var, name }
        | SpecForEachLhs::Ident(name) => {
            let st0 = SpecState { current_env: outer_env, ..st };
            let (st1, pstep) = spec_eval_ident_put(st0, name, val);
            match pstep {
                SpecExprStep::Val(_) => {
                    let (st2_raw, bstep) = spec_eval_stmt(prog, body_id, st1);
                    (SpecState { current_env: outer_env, ..spec_cap_fuel(st2_raw, st1.fuel) }, bstep)
                }
                abrupt => (st1, spec_expr_abrupt_to_stmt(abrupt)),
            }
        }
        SpecForEachLhs::Member { obj, prop } => {
            let st0 = SpecState { current_env: outer_env, ..st };
            let rbase = st0.temp_roots.len();
            let st_r0 = spec_push_root(st0, val);
            let (st1_raw, ostep) = spec_eval_expr(prog, obj, st_r0);
            let st1 = spec_cap_fuel(st1_raw, st0.fuel);
            match ostep {
                SpecExprStep::Val(ov) => {
                    let st_r1 = spec_push_root(st1, ov);
                    let (st2_raw, pstep) = spec_eval_expr(prog, prop, st_r1);
                    let st2 = spec_cap_fuel(st2_raw, st1.fuel);
                    match pstep {
                        SpecExprStep::Val(pv) => {
                            if (ov is Undefined) || (ov is Null) {
                                let st_done = spec_truncate_roots(st2, rbase);
                                let (st_err, err) = spec_throw_error(st_done, ErrorKind::TypeError, spec_k_empty());
                                (st_err, spec_expr_abrupt_to_stmt(err))
                            } else {
                                let (st3_raw, kstep) = spec_eval_to_string(prog, pv, st2);
                                let st3 = spec_truncate_roots(spec_cap_fuel(st3_raw, st2.fuel), rbase);
                                match kstep {
                                    SpecExprStep::Val(SpecVal::Str(ks)) => {
                                        let (st4_raw, sstep) = spec_eval_set_property_val(prog, ov, ks, val, st3);
                                        let st4 = spec_cap_fuel(st4_raw, st3.fuel);
                                        match sstep {
                                            SpecExprStep::Val(_) => {
                                                let (st5_raw, bstep) = spec_eval_stmt(prog, body_id, st4);
                                                (SpecState { current_env: outer_env, ..spec_cap_fuel(st5_raw, st4.fuel) }, bstep)
                                            }
                                            abrupt => (st4, spec_expr_abrupt_to_stmt(abrupt)),
                                        }
                                    }
                                    other => (st3, spec_expr_abrupt_to_stmt(other)),
                                }
                            }
                        }
                        abrupt => (spec_truncate_roots(st2, rbase), spec_expr_abrupt_to_stmt(abrupt)),
                    }
                }
                abrupt => (spec_truncate_roots(st1, rbase), spec_expr_abrupt_to_stmt(abrupt)),
            }
        }
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(35)]
fn bind_for_each_iter_exec(
    lhs: &ForEachLhs,
    val: Val,
    outer_env: EnvId,
    body_id: StmtId,
    prog: &Program,
    st: &mut VmState,
) -> (res: StmtStep)
    ensures
        (final(st)@, res@) == spec_bind_for_each_iter(
            lhs@,
            val@,
            outer_env,
            body_id,
            prog@,
            old(st)@,
        ),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        match res@ {
            SpecStmtStep::Comp(SpecCompletion::Normal(_))
            | SpecStmtStep::Comp(SpecCompletion::Continue(_, _)) =>
                old(st).fuel > 0 && final(st).fuel < old(st).fuel,
            _ => true,
        },
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 12nat, 1nat,
{
    reveal(spec_bind_for_each_iter_inner);
    match lhs {
        ForEachLhs::Decl { kind: VarKind::Let, name }
        | ForEachLhs::Decl { kind: VarKind::Const, name } => {
            let mutable = matches!(lhs, ForEachLhs::Decl { kind: VarKind::Let, .. });
            let erbase = st.env_roots.len();
            let iter_env = st.envs.alloc_env(EnvKind::Block, outer_env, None);
            st.envs.bind_initialized(iter_env, clone_js_str(name), val, mutable, true);
            st.current_env = iter_env;
            st.push_env_root(outer_env);
            let bstep = eval_stmt(prog, body_id, st);
            st.current_env = outer_env;
            st.truncate_env_roots(erbase);
            bstep
        }
        ForEachLhs::Decl { kind: VarKind::Var, name }
        | ForEachLhs::Ident(name) => {
            st.current_env = outer_env;
            let pstep = eval_ident_put_exec(st, name, val);
            match pstep {
                ExprStep::Val(_) => {
                    let bstep = eval_stmt(prog, body_id, st);
                    st.current_env = outer_env;
                    bstep
                }
                abrupt => expr_abrupt_to_stmt(abrupt),
            }
        }
        ForEachLhs::Member { obj, prop } => {
            st.current_env = outer_env;
            let rbase = st.temp_roots.len();
            st.push_root(&val);
            let ov = match eval_expr(prog, *obj, st) {
                ExprStep::Val(v) => v,
                abrupt => {
                    st.truncate_roots(rbase);
                    return expr_abrupt_to_stmt(abrupt);
                }
            };
            st.push_root(&ov);
            let pv = match eval_expr(prog, *prop, st) {
                ExprStep::Val(v) => v,
                abrupt => {
                    st.truncate_roots(rbase);
                    return expr_abrupt_to_stmt(abrupt);
                }
            };
            if matches!(ov, Val::Undefined | Val::Null) {
                st.truncate_roots(rbase);
                return expr_abrupt_to_stmt(throw_error_exec(st, ErrorKind::TypeError, k_empty()));
            }
            let kstep = eval_to_string(prog, pv, st);
            st.truncate_roots(rbase);
            let ks = match kstep {
                ExprStep::Val(Val::Str(s)) => s,
                other => return expr_abrupt_to_stmt(other),
            };
            match eval_set_property_val(prog, ov, ks, val, st) {
                ExprStep::Val(_) => {
                    let bstep = eval_stmt(prog, body_id, st);
                    st.current_env = outer_env;
                    bstep
                }
                abrupt => expr_abrupt_to_stmt(abrupt),
            }
        }
    }
}

pub open spec fn spec_eval_for_in_keys(
    prog: SpecProgram,
    labels: Seq<Seq<u16>>,
    lhs: SpecForEachLhs,
    enum_target: Option<ObjId>,
    keys: Seq<Seq<u16>>,
    idx: nat,
    body: StmtId,
    outer_env: EnvId,
    cur_cv: SpecCompletionValue,
    st: SpecState,
) -> (SpecState, SpecStmtStep)
    decreases st.fuel, 13nat, keys.len() - idx,
{
    if idx >= keys.len() {
        (st, SpecStmtStep::Comp(SpecCompletion::Normal(SpecCompletionValue::Present(spec_unwrap_or_undefined(cur_cv)))))
    } else {
        let key_s = keys[idx as int];
        let live_ok = match enum_target {
            Some(oid) => spec_is_for_in_key_live_enumerable(st.heap, st.intr.realm, oid, key_s),
            None => true,
        };
        if !live_ok {
            spec_eval_for_in_keys(prog, labels, lhs, enum_target, keys, idx + 1, body, outer_env, cur_cv, st)
        } else {
            let kval = SpecVal::Str(key_s);
            let rbase = st.temp_roots.len();
            let st_r = match cur_cv {
                SpecCompletionValue::Present(v) => spec_push_root(st, v),
                SpecCompletionValue::Empty => st,
            };
            let (st1_raw, bstep) = spec_bind_for_each_iter(lhs, kval, outer_env, body, prog, st_r);
            let st1 = spec_truncate_roots(spec_cap_fuel(st1_raw, st.fuel), rbase);
            match bstep {
                SpecStmtStep::Comp(SpecCompletion::Normal(bcv)) => {
                    let next_cv = spec_update_empty_val(bcv, cur_cv);
                    spec_eval_for_in_keys(prog, labels, lhs, enum_target, keys, idx + 1, body, outer_env, next_cv, st1)
                }
                SpecStmtStep::Comp(SpecCompletion::Continue(ccv, target)) => {
                    let next_cv = spec_update_empty_val(ccv, cur_cv);
                    if spec_iter_target_matches(labels, target) {
                        spec_eval_for_in_keys(prog, labels, lhs, enum_target, keys, idx + 1, body, outer_env, next_cv, st1)
                    } else {
                        (st1, SpecStmtStep::Comp(SpecCompletion::Continue(next_cv, target)))
                    }
                }
                SpecStmtStep::Comp(SpecCompletion::Break(bcv, target)) => {
                    let merged = spec_update_empty_val(bcv, cur_cv);
                    if spec_iter_target_matches(labels, target) {
                        (st1, SpecStmtStep::Comp(SpecCompletion::Normal(SpecCompletionValue::Present(spec_unwrap_or_undefined(merged)))))
                    } else {
                        (st1, SpecStmtStep::Comp(SpecCompletion::Break(merged, target)))
                    }
                }
                other => (st1, other),
            }
        }
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(25)]
fn eval_for_in_keys(
    prog: &Program,
    labels: &Vec<JsStr>,
    lhs: &ForEachLhs,
    enum_target: Option<ObjId>,
    keys: &Vec<JsStr>,
    body: StmtId,
    outer_env: EnvId,
    st: &mut VmState,
) -> (res: StmtStep)
    ensures
        (final(st)@, res@) == spec_eval_for_in_keys(
            prog@,
            spec_str_seq_view(labels@),
            lhs@,
            enum_target,
            spec_str_seq_view(keys@),
            0,
            body,
            outer_env,
            SpecCompletionValue::Empty,
            old(st)@,
        ),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 13nat, keys@.len() as nat,
{
    let n = keys.len();
    let mut idx: usize = 0;
    let mut cur_cv = CompletionValue::Empty;
    let ghost skeys = spec_str_seq_view(keys@);
    let ghost slbls = spec_str_seq_view(labels@);
    while idx < n
        invariant
            idx <= n == keys@.len(),
            skeys == spec_str_seq_view(keys@),
            slbls == spec_str_seq_view(labels@),
            st.fuel <= old(st).fuel,
            env_wf(old(st)@.envs) ==> env_wf(st@.envs),
            spec_eval_for_in_keys(prog@, slbls, lhs@, enum_target, skeys, 0, body, outer_env, SpecCompletionValue::Empty, old(st)@)
                == spec_eval_for_in_keys(prog@, slbls, lhs@, enum_target, skeys, idx as nat, body, outer_env, cur_cv@, st@),
        decreases n - idx,
    {
        proof { assert(skeys[idx as int] == keys@[idx as int]@); }
        let live_ok = match enum_target {
            Some(oid) => st.heap.is_for_in_key_live_enumerable(st.intr.realm, oid, &keys[idx]),
            None => true,
        };
        if !live_ok {
            idx += 1;
        } else {
            let rbase = st.temp_roots.len();
            if let CompletionValue::Present(ref v) = cur_cv {
                st.push_root(v);
            }
            let kval = Val::Str(clone_js_str(&keys[idx]));
            let bstep = bind_for_each_iter_exec(lhs, kval, outer_env, body, prog, st);
            st.truncate_roots(rbase);
            match bstep {
                StmtStep::Comp(Completion::Normal(bcv)) => {
                    cur_cv = update_empty_val(bcv, cur_cv);
                    idx += 1;
                }
                StmtStep::Comp(Completion::Continue(ccv, target)) => {
                    let next_cv = update_empty_val(ccv, cur_cv);
                    if iter_target_matches_exec(labels, &target) {
                        cur_cv = next_cv;
                        idx += 1;
                    } else {
                        return StmtStep::Comp(Completion::Continue(next_cv, target));
                    }
                }
                StmtStep::Comp(Completion::Break(bcv, target)) => {
                    let merged = update_empty_val(bcv, cur_cv);
                    if iter_target_matches_exec(labels, &target) {
                        return StmtStep::Comp(Completion::normal_val(unwrap_or_undefined(merged)));
                    } else {
                        return StmtStep::Comp(Completion::Break(merged, target));
                    }
                }
                other => return other,
            }
        }
    }
    StmtStep::Comp(Completion::normal_val(unwrap_or_undefined(cur_cv)))
}

pub open spec fn spec_eval_for_in_stmt(
    prog: SpecProgram,
    labels: Seq<Seq<u16>>,
    lhs: SpecForEachLhs,
    object: ExprId,
    body: StmtId,
    st: SpecState,
) -> (SpecState, SpecStmtStep)
    decreases st.fuel, 14nat, 1nat,
{
    spec_eval_for_in_stmt_inner(prog, labels, lhs, object, body, st)
}

#[verifier::opaque]
pub open spec fn spec_eval_for_in_stmt_inner(
    prog: SpecProgram,
    labels: Seq<Seq<u16>>,
    lhs: SpecForEachLhs,
    object: ExprId,
    body: StmtId,
    st: SpecState,
) -> (SpecState, SpecStmtStep)
    decreases st.fuel, 14nat, 0nat,
{
    let outer_env = st.current_env;
    let erbase = st.env_roots.len();
    let st0 = match lhs {
        SpecForEachLhs::Decl { kind: VarKind::Let, name }
        | SpecForEachLhs::Decl { kind: VarKind::Const, name } => {
            let (e1, tdz_env) = spec_alloc_env(st.envs, EnvKind::Block, outer_env, None);
            let e2 = spec_declare_tdz(e1, tdz_env, name, true, true);
            spec_push_env_root(SpecState { envs: e2, current_env: tdz_env, ..st }, outer_env)
        }
        _ => st,
    };
    let (st1_raw, ostep) = spec_eval_expr(prog, object, st0);
    let st1 = spec_truncate_env_roots(SpecState { current_env: outer_env, ..spec_cap_fuel(st1_raw, st0.fuel) }, erbase);
    match ostep {
        SpecExprStep::Val(ov) => {
            match ov {
                SpecVal::Undefined | SpecVal::Null => (
                    st1,
                    SpecStmtStep::Comp(SpecCompletion::Normal(SpecCompletionValue::Present(SpecVal::Undefined))),
                ),
                SpecVal::Object(oid) => {
                    match spec_collect_for_in_candidates(st1.heap, st1.intr.realm, oid) {
                        Some(ks) => {
                            let rbase = st1.temp_roots.len();
                            let st_r = spec_push_root(st1, SpecVal::Object(oid));
                            let (st2_raw, kres) = spec_eval_for_in_keys(
                                prog, labels, lhs, Some(oid), ks, 0, body, outer_env, SpecCompletionValue::Empty, st_r,
                            );
                            (spec_truncate_roots(spec_cap_fuel(st2_raw, st1.fuel), rbase), kres)
                        }
                        None => {
                            let (st2, err) = spec_throw_error(st1, ErrorKind::TypeError, spec_k_empty());
                            (st2, spec_expr_abrupt_to_stmt(err))
                        }
                    }
                }
                SpecVal::Str(s) => {
                    let ks = spec_str_index_keys(s.len() as usize, 0, seq![]);
                    let (st2_raw, kres) = spec_eval_for_in_keys(
                        prog, labels, lhs, None, ks, 0, body, outer_env, SpecCompletionValue::Empty, st1,
                    );
                    (spec_cap_fuel(st2_raw, st1.fuel), kres)
                }
                _ => (
                    st1,
                    SpecStmtStep::Comp(SpecCompletion::Normal(SpecCompletionValue::Present(SpecVal::Undefined))),
                ),
            }
        }
        abrupt => (st1, spec_expr_abrupt_to_stmt(abrupt)),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
fn eval_for_in_stmt(
    prog: &Program,
    labels: &Vec<JsStr>,
    lhs: &ForEachLhs,
    object: ExprId,
    body: StmtId,
    st: &mut VmState,
) -> (res: StmtStep)
    ensures
        (final(st)@, res@) == spec_eval_for_in_stmt(
            prog@,
            spec_str_seq_view(labels@),
            lhs@,
            object,
            body,
            old(st)@,
        ),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 14nat, 0nat,
{
    reveal(spec_eval_for_in_stmt_inner);
    let outer_env = st.current_env;
    let erbase = st.env_roots.len();
    match lhs {
        ForEachLhs::Decl { kind: VarKind::Let, name }
        | ForEachLhs::Decl { kind: VarKind::Const, name } => {
            let tdz_env = st.envs.alloc_env(EnvKind::Block, outer_env, None);
            st.envs.declare_tdz(tdz_env, clone_js_str(name), true, true);
            st.current_env = tdz_env;
            st.push_env_root(outer_env);
        }
        _ => {}
    }
    let ostep = eval_expr(prog, object, st);
    st.current_env = outer_env;
    st.truncate_env_roots(erbase);
    match ostep {
        ExprStep::Val(ov) => match ov {
            Val::Undefined | Val::Null => StmtStep::Comp(Completion::normal_val(Val::Undefined)),
            Val::Object(oid) => match st.heap.collect_for_in_candidates(st.intr.realm, oid) {
                Some(ks) => {
                    let rbase = st.temp_roots.len();
                    let ov_r = Val::Object(oid);
                    st.push_root(&ov_r);
                    let kres = eval_for_in_keys(prog, labels, lhs, Some(oid), &ks, body, outer_env, st);
                    st.truncate_roots(rbase);
                    kres
                }
                None => expr_abrupt_to_stmt(throw_error_exec(st, ErrorKind::TypeError, k_empty())),
            },
            Val::Str(s) => {
                let ks = build_str_index_keys_exec(s.0.len());
                eval_for_in_keys(prog, labels, lhs, None, &ks, body, outer_env, st)
            }
            _ => StmtStep::Comp(Completion::normal_val(Val::Undefined)),
        },
        abrupt => expr_abrupt_to_stmt(abrupt),
    }
}

pub open spec fn spec_iterable_live_len(heap: SpecHeap, realm: RealmId, iv: SpecVal) -> Option<usize> {
    match iv {
        SpecVal::Str(s) => Some(s.len() as usize),
        SpecVal::Object(oid) => {
            if (oid.0 as int) >= heap.slots.len() {
                None
            } else {
                match heap.slots[oid.0 as int] {
                    SpecSlot::Live(o) => if o.realm == realm {
                        match o.kind {
                            ObjectKind::Array { length } => Some(length),
                            _ => None,
                        }
                    } else {
                        None
                    },
                    SpecSlot::Free => None,
                }
            }
        }
        _ => None,
    }
}

fn iterable_live_len_exec(heap: &Heap, realm: RealmId, iv: &Val) -> (r: Option<usize>)
    ensures r == spec_iterable_live_len(heap@, realm, iv@),
{
    match iv {
        Val::Str(s) => Some(s.0.len()),
        Val::Object(oid) => {
            if oid.0 >= heap.slots.len() {
                None
            } else {
                proof { assert(heap@.slots[oid.0 as int] == heap.slots@[oid.0 as int]@); }
                match &heap.slots[oid.0] {
                    Slot::Live(o) => if o.realm.0 == realm.0 {
                        match o.kind {
                            ObjectKind::Array { length } => Some(length),
                            _ => None,
                        }
                    } else {
                        None
                    },
                    Slot::Free => None,
                }
            }
        }
        _ => None,
    }
}

pub open spec fn spec_eval_for_of_items(
    prog: SpecProgram,
    labels: Seq<Seq<u16>>,
    lhs: SpecForEachLhs,
    iter_val: SpecVal,
    idx: usize,
    body: StmtId,
    outer_env: EnvId,
    cur_cv: SpecCompletionValue,
    st: SpecState,
) -> (SpecState, SpecStmtStep)
    decreases st.fuel, 13nat, 0nat,
{
    let cur_len = match spec_iterable_live_len(st.heap, st.intr.realm, iter_val) {
        Some(l) => l,
        None => 0usize,
    };
    if idx >= cur_len {
        (st, SpecStmtStep::Comp(SpecCompletion::Normal(SpecCompletionValue::Present(spec_unwrap_or_undefined(cur_cv)))))
    } else {
        let rbase = st.temp_roots.len();
        let st_r1 = spec_push_root(st, iter_val);
        let st_r2 = match cur_cv {
            SpecCompletionValue::Present(v) => spec_push_root(st_r1, v),
            SpecCompletionValue::Empty => st_r1,
        };
        let (st1, estep) = spec_get_property_val(st_r2, iter_val, spec_index_key(idx));
        match estep {
            SpecExprStep::Val(ev) => {
                let (st2_raw, bstep) = spec_bind_for_each_iter(lhs, ev, outer_env, body, prog, st1);
                let next_idx: usize = if idx < usize::MAX { (idx + 1) as usize } else { usize::MAX };
                match bstep {
                    SpecStmtStep::Comp(SpecCompletion::Normal(bcv)) => {
                        if st.fuel == 0 {
                            (spec_truncate_roots(spec_cap_fuel(st2_raw, 0), rbase), SpecStmtStep::OutOfFuel)
                        } else {
                            let st2 = spec_truncate_roots(spec_cap_fuel(st2_raw, (st.fuel - 1) as nat), rbase);
                            let next_cv = spec_update_empty_val(bcv, cur_cv);
                            spec_eval_for_of_items(prog, labels, lhs, iter_val, next_idx, body, outer_env, next_cv, st2)
                        }
                    }
                    SpecStmtStep::Comp(SpecCompletion::Continue(ccv, target)) => {
                        let next_cv = spec_update_empty_val(ccv, cur_cv);
                        if spec_iter_target_matches(labels, target) {
                            if st.fuel == 0 {
                                (spec_truncate_roots(spec_cap_fuel(st2_raw, 0), rbase), SpecStmtStep::OutOfFuel)
                            } else {
                                let st2 = spec_truncate_roots(spec_cap_fuel(st2_raw, (st.fuel - 1) as nat), rbase);
                                spec_eval_for_of_items(prog, labels, lhs, iter_val, next_idx, body, outer_env, next_cv, st2)
                            }
                        } else {
                            let st2 = spec_truncate_roots(spec_cap_fuel(st2_raw, st1.fuel), rbase);
                            (st2, SpecStmtStep::Comp(SpecCompletion::Continue(next_cv, target)))
                        }
                    }
                    SpecStmtStep::Comp(SpecCompletion::Break(bcv, target)) => {
                        let st2 = spec_truncate_roots(spec_cap_fuel(st2_raw, st1.fuel), rbase);
                        let merged = spec_update_empty_val(bcv, cur_cv);
                        if spec_iter_target_matches(labels, target) {
                            (st2, SpecStmtStep::Comp(SpecCompletion::Normal(SpecCompletionValue::Present(spec_unwrap_or_undefined(merged)))))
                        } else {
                            (st2, SpecStmtStep::Comp(SpecCompletion::Break(merged, target)))
                        }
                    }
                    other => {
                        let st2 = spec_truncate_roots(spec_cap_fuel(st2_raw, st1.fuel), rbase);
                        (st2, other)
                    }
                }
            }
            abrupt => (spec_truncate_roots(st1, rbase), spec_expr_abrupt_to_stmt(abrupt)),
        }
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
fn eval_for_of_items(
    prog: &Program,
    labels: &Vec<JsStr>,
    lhs: &ForEachLhs,
    iter_val: &Val,
    body: StmtId,
    outer_env: EnvId,
    st: &mut VmState,
) -> (res: StmtStep)
    ensures
        (final(st)@, res@) == spec_eval_for_of_items(
            prog@,
            spec_str_seq_view(labels@),
            lhs@,
            iter_val@,
            0,
            body,
            outer_env,
            SpecCompletionValue::Empty,
            old(st)@,
        ),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 13nat, 1nat,
{
    let mut idx: usize = 0;
    let mut cur_cv = CompletionValue::Empty;
    let ghost slbls = spec_str_seq_view(labels@);
    loop
        invariant
            slbls == spec_str_seq_view(labels@),
            st.fuel <= old(st).fuel,
            env_wf(old(st)@.envs) ==> env_wf(st@.envs),
            spec_eval_for_of_items(prog@, slbls, lhs@, iter_val@, 0, body, outer_env, SpecCompletionValue::Empty, old(st)@)
                == spec_eval_for_of_items(prog@, slbls, lhs@, iter_val@, idx, body, outer_env, cur_cv@, st@),
        decreases st.fuel,
    {
        let cur_len = match iterable_live_len_exec(&st.heap, st.intr.realm, iter_val) {
            Some(l) => l,
            None => 0usize,
        };
        if idx >= cur_len {
            return StmtStep::Comp(Completion::normal_val(unwrap_or_undefined(cur_cv)));
        }
        let rbase = st.temp_roots.len();
        st.push_root(iter_val);
        if let CompletionValue::Present(ref v) = cur_cv {
            st.push_root(v);
        }
        let ik = index_key_exec(idx);
        let estep = get_property_val_exec(st, iter_val, &ik);
        let ev = match estep {
            ExprStep::Val(v) => v,
            abrupt => {
                st.truncate_roots(rbase);
                return expr_abrupt_to_stmt(abrupt);
            }
        };
        let bstep = bind_for_each_iter_exec(lhs, ev, outer_env, body, prog, st);
        st.truncate_roots(rbase);
        let next_idx: usize = if idx < usize::MAX { idx + 1 } else { usize::MAX };
        match bstep {
            StmtStep::Comp(Completion::Normal(bcv)) => {
                cur_cv = update_empty_val(bcv, cur_cv);
                idx = next_idx;
            }
            StmtStep::Comp(Completion::Continue(ccv, target)) => {
                let next_cv = update_empty_val(ccv, cur_cv);
                if iter_target_matches_exec(labels, &target) {
                    cur_cv = next_cv;
                    idx = next_idx;
                } else {
                    return StmtStep::Comp(Completion::Continue(next_cv, target));
                }
            }
            StmtStep::Comp(Completion::Break(bcv, target)) => {
                let merged = update_empty_val(bcv, cur_cv);
                if iter_target_matches_exec(labels, &target) {
                    return StmtStep::Comp(Completion::normal_val(unwrap_or_undefined(merged)));
                } else {
                    return StmtStep::Comp(Completion::Break(merged, target));
                }
            }
            other => return other,
        }
    }
}

pub open spec fn spec_eval_for_of_stmt(
    prog: SpecProgram,
    labels: Seq<Seq<u16>>,
    lhs: SpecForEachLhs,
    iterable: ExprId,
    body: StmtId,
    st: SpecState,
) -> (SpecState, SpecStmtStep)
    decreases st.fuel, 14nat, 1nat,
{
    spec_eval_for_of_stmt_inner(prog, labels, lhs, iterable, body, st)
}

#[verifier::opaque]
pub open spec fn spec_eval_for_of_stmt_inner(
    prog: SpecProgram,
    labels: Seq<Seq<u16>>,
    lhs: SpecForEachLhs,
    iterable: ExprId,
    body: StmtId,
    st: SpecState,
) -> (SpecState, SpecStmtStep)
    decreases st.fuel, 14nat, 0nat,
{
    let outer_env = st.current_env;
    let erbase = st.env_roots.len();
    let st0 = match lhs {
        SpecForEachLhs::Decl { kind: VarKind::Let, name }
        | SpecForEachLhs::Decl { kind: VarKind::Const, name } => {
            let (e1, tdz_env) = spec_alloc_env(st.envs, EnvKind::Block, outer_env, None);
            let e2 = spec_declare_tdz(e1, tdz_env, name, true, true);
            spec_push_env_root(SpecState { envs: e2, current_env: tdz_env, ..st }, outer_env)
        }
        _ => st,
    };
    let (st1_raw, istep) = spec_eval_expr(prog, iterable, st0);
    let st1 = spec_truncate_env_roots(SpecState { current_env: outer_env, ..spec_cap_fuel(st1_raw, st0.fuel) }, erbase);
    match istep {
        SpecExprStep::Val(iv) => {
            match spec_iterable_live_len(st1.heap, st1.intr.realm, iv) {
                Some(_) => {
                    let (st2_raw, res) = spec_eval_for_of_items(
                        prog, labels, lhs, iv, 0, body, outer_env, SpecCompletionValue::Empty, st1,
                    );
                    (spec_cap_fuel(st2_raw, st1.fuel), res)
                }
                None => {
                    let (st2, err) = spec_throw_error(st1, ErrorKind::TypeError, spec_k_empty());
                    (st2, spec_expr_abrupt_to_stmt(err))
                }
            }
        }
        abrupt => (st1, spec_expr_abrupt_to_stmt(abrupt)),
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(25)]
fn eval_for_of_stmt(
    prog: &Program,
    labels: &Vec<JsStr>,
    lhs: &ForEachLhs,
    iterable: ExprId,
    body: StmtId,
    st: &mut VmState,
) -> (res: StmtStep)
    ensures
        (final(st)@, res@) == spec_eval_for_of_stmt(
            prog@,
            spec_str_seq_view(labels@),
            lhs@,
            iterable,
            body,
            old(st)@,
        ),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 14nat, 0nat,
{
    reveal(spec_eval_for_of_stmt_inner);
    let outer_env = st.current_env;
    let erbase = st.env_roots.len();
    match lhs {
        ForEachLhs::Decl { kind: VarKind::Let, name }
        | ForEachLhs::Decl { kind: VarKind::Const, name } => {
            let tdz_env = st.envs.alloc_env(EnvKind::Block, outer_env, None);
            st.envs.declare_tdz(tdz_env, clone_js_str(name), true, true);
            st.current_env = tdz_env;
            st.push_env_root(outer_env);
        }
        _ => {}
    }
    let istep = eval_expr(prog, iterable, st);
    st.current_env = outer_env;
    st.truncate_env_roots(erbase);
    match istep {
        ExprStep::Val(iv) => {
            match iterable_live_len_exec(&st.heap, st.intr.realm, &iv) {
                Some(_) => eval_for_of_items(prog, labels, lhs, &iv, body, outer_env, st),
                None => expr_abrupt_to_stmt(throw_error_exec(st, ErrorKind::TypeError, k_empty())),
            }
        }
        abrupt => expr_abrupt_to_stmt(abrupt),
    }
}

/// Rank 14: `while (cond) body` (§14.7.2.2)
pub open spec fn spec_eval_while_loop(
    prog: SpecProgram,
    labels: Seq<Seq<u16>>,
    cond: ExprId,
    body: StmtId,
    cur_cv: SpecCompletionValue,
    st: SpecState,
) -> (SpecState, SpecStmtStep)
    decreases st.fuel, 14nat, 0nat,
{
    let rbase = st.temp_roots.len();
    let st_r = match cur_cv {
        SpecCompletionValue::Present(v) => spec_push_root(st, v),
        SpecCompletionValue::Empty => st,
    };
    let (st1_raw, cstep) = spec_eval_expr(prog, cond, st_r);
    match cstep {
        SpecExprStep::Val(cv) => {
            if st.fuel == 0 {
                (spec_truncate_roots(spec_cap_fuel(st1_raw, 0), rbase), SpecStmtStep::OutOfFuel)
            } else {
                let st1 = spec_truncate_roots(spec_cap_fuel(st1_raw, (st.fuel - 1) as nat), rbase);
                if !spec_to_boolean(cv) {
                    (st1, SpecStmtStep::Comp(SpecCompletion::Normal(SpecCompletionValue::Present(spec_unwrap_or_undefined(cur_cv)))))
                } else {
                    let st_r2 = match cur_cv {
                        SpecCompletionValue::Present(v) => spec_push_root(st1, v),
                        SpecCompletionValue::Empty => st1,
                    };
                    let (st2_raw, bstep) = spec_eval_stmt(prog, body, st_r2);
                    let st2 = spec_truncate_roots(spec_cap_fuel(st2_raw, st1.fuel), rbase);
                    match bstep {
                        SpecStmtStep::Comp(SpecCompletion::Normal(bcv)) => {
                            let next_cv = spec_update_empty_val(bcv, cur_cv);
                            spec_eval_while_loop(prog, labels, cond, body, next_cv, st2)
                        }
                        SpecStmtStep::Comp(SpecCompletion::Continue(ccv, target)) => {
                            let next_cv = spec_update_empty_val(ccv, cur_cv);
                            if spec_iter_target_matches(labels, target) {
                                spec_eval_while_loop(prog, labels, cond, body, next_cv, st2)
                            } else {
                                (st2, SpecStmtStep::Comp(SpecCompletion::Continue(next_cv, target)))
                            }
                        }
                        SpecStmtStep::Comp(SpecCompletion::Break(bcv, target)) => {
                            let merged = spec_update_empty_val(bcv, cur_cv);
                            if spec_iter_target_matches(labels, target) {
                                (st2, SpecStmtStep::Comp(SpecCompletion::Normal(SpecCompletionValue::Present(spec_unwrap_or_undefined(merged)))))
                            } else {
                                (st2, SpecStmtStep::Comp(SpecCompletion::Break(merged, target)))
                            }
                        }
                        other => (st2, other),
                    }
                }
            }
        }
        abrupt => (spec_truncate_roots(spec_cap_fuel(st1_raw, st.fuel), rbase), spec_expr_abrupt_to_stmt(abrupt)),
    }
}

fn eval_while_loop(
    prog: &Program,
    labels: &Vec<JsStr>,
    cond: ExprId,
    body: StmtId,
    st: &mut VmState,
) -> (res: StmtStep)
    ensures
        (final(st)@, res@) == spec_eval_while_loop(prog@, spec_str_seq_view(labels@), cond, body, SpecCompletionValue::Empty, old(st)@),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 14nat, 1nat,
{
    let mut cur_cv = CompletionValue::Empty;
    let ghost slbls = spec_str_seq_view(labels@);
    loop
        invariant
            slbls == spec_str_seq_view(labels@),
            st.fuel <= old(st).fuel,
            env_wf(old(st)@.envs) ==> env_wf(st@.envs),
            spec_eval_while_loop(prog@, slbls, cond, body, SpecCompletionValue::Empty, old(st)@)
                == spec_eval_while_loop(prog@, slbls, cond, body, cur_cv@, st@),
        decreases st.fuel,
    {
        let rbase = st.temp_roots.len();
        if let CompletionValue::Present(ref v) = cur_cv {
            st.push_root(v);
        }
        let cstep = eval_expr(prog, cond, st);
        st.truncate_roots(rbase);
        let cv = match cstep {
            ExprStep::Val(v) => v,
            abrupt => return expr_abrupt_to_stmt(abrupt),
        };
        if !val_to_boolean(&cv) {
            return StmtStep::Comp(Completion::normal_val(unwrap_or_undefined(cur_cv)));
        }
        if let CompletionValue::Present(ref v) = cur_cv {
            st.push_root(v);
        }
        let bstep = eval_stmt(prog, body, st);
        st.truncate_roots(rbase);
        match bstep {
            StmtStep::Comp(Completion::Normal(bcv)) => {
                cur_cv = update_empty_val(bcv, cur_cv);
            }
            StmtStep::Comp(Completion::Continue(ccv, target)) => {
                let next_cv = update_empty_val(ccv, cur_cv);
                if iter_target_matches_exec(labels, &target) {
                    cur_cv = next_cv;
                } else {
                    return StmtStep::Comp(Completion::Continue(next_cv, target));
                }
            }
            StmtStep::Comp(Completion::Break(bcv, target)) => {
                let merged = update_empty_val(bcv, cur_cv);
                if iter_target_matches_exec(labels, &target) {
                    return StmtStep::Comp(Completion::normal_val(unwrap_or_undefined(merged)));
                } else {
                    return StmtStep::Comp(Completion::Break(merged, target));
                }
            }
            other => return other,
        }
    }
}

/// Rank 14: `do body while (cond)` (§14.7.1.2)
pub open spec fn spec_eval_do_while_loop(
    prog: SpecProgram,
    labels: Seq<Seq<u16>>,
    body: StmtId,
    cond: ExprId,
    cur_cv: SpecCompletionValue,
    st: SpecState,
) -> (SpecState, SpecStmtStep)
    decreases st.fuel, 14nat, 0nat,
{
    let rbase = st.temp_roots.len();
    let st_r = match cur_cv {
        SpecCompletionValue::Present(v) => spec_push_root(st, v),
        SpecCompletionValue::Empty => st,
    };
    let (st1_raw, bstep) = spec_eval_stmt(prog, body, st_r);
    match bstep {
        SpecStmtStep::OutOfFuel =>
            (spec_truncate_roots(spec_cap_fuel(st1_raw, 0), rbase), SpecStmtStep::OutOfFuel),
        SpecStmtStep::HeapQuotaExceeded =>
            (spec_truncate_roots(spec_cap_fuel(st1_raw, st.fuel), rbase), SpecStmtStep::HeapQuotaExceeded),
        SpecStmtStep::Unsupported(f) =>
            (spec_truncate_roots(spec_cap_fuel(st1_raw, st.fuel), rbase), SpecStmtStep::Unsupported(f)),
        SpecStmtStep::Comp(bcomp) => {
            if st.fuel == 0 {
                (spec_truncate_roots(spec_cap_fuel(st1_raw, 0), rbase), SpecStmtStep::OutOfFuel)
            } else {
                let st1 = spec_truncate_roots(spec_cap_fuel(st1_raw, (st.fuel - 1) as nat), rbase);
                let cont_cv: Option<SpecCompletionValue> = match bcomp {
                    SpecCompletion::Normal(bcv) => Some(spec_update_empty_val(bcv, cur_cv)),
                    SpecCompletion::Continue(ccv, target) => {
                        if spec_iter_target_matches(labels, target) {
                            Some(spec_update_empty_val(ccv, cur_cv))
                        } else {
                            None
                        }
                    }
                    _ => None,
                };
                match cont_cv {
                    Some(next_cv) => {
                        let st_r2 = match next_cv {
                            SpecCompletionValue::Present(v) => spec_push_root(st1, v),
                            SpecCompletionValue::Empty => st1,
                        };
                        let (st2_raw, cstep) = spec_eval_expr(prog, cond, st_r2);
                        let st2 = spec_truncate_roots(spec_cap_fuel(st2_raw, st1.fuel), rbase);
                        match cstep {
                            SpecExprStep::Val(cv) => {
                                if spec_to_boolean(cv) {
                                    spec_eval_do_while_loop(prog, labels, body, cond, next_cv, st2)
                                } else {
                                    (st2, SpecStmtStep::Comp(SpecCompletion::Normal(SpecCompletionValue::Present(spec_unwrap_or_undefined(next_cv)))))
                                }
                            }
                            abrupt => (st2, spec_expr_abrupt_to_stmt(abrupt)),
                        }
                    }
                    None => {
                        match bcomp {
                            SpecCompletion::Continue(ccv, target) =>
                                (st1, SpecStmtStep::Comp(SpecCompletion::Continue(spec_update_empty_val(ccv, cur_cv), target))),
                            SpecCompletion::Break(bcv, target) => {
                                let merged = spec_update_empty_val(bcv, cur_cv);
                                if spec_iter_target_matches(labels, target) {
                                    (st1, SpecStmtStep::Comp(SpecCompletion::Normal(SpecCompletionValue::Present(spec_unwrap_or_undefined(merged)))))
                                } else {
                                    (st1, SpecStmtStep::Comp(SpecCompletion::Break(merged, target)))
                                }
                            }
                            other_c => (st1, SpecStmtStep::Comp(other_c)),
                        }
                    }
                }
            }
        }
    }
}

fn eval_do_while_loop(
    prog: &Program,
    labels: &Vec<JsStr>,
    body: StmtId,
    cond: ExprId,
    st: &mut VmState,
) -> (res: StmtStep)
    ensures
        (final(st)@, res@) == spec_eval_do_while_loop(prog@, spec_str_seq_view(labels@), body, cond, SpecCompletionValue::Empty, old(st)@),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 14nat, 1nat,
{
    let mut cur_cv = CompletionValue::Empty;
    let ghost slbls = spec_str_seq_view(labels@);
    loop
        invariant
            slbls == spec_str_seq_view(labels@),
            st.fuel <= old(st).fuel,
            env_wf(old(st)@.envs) ==> env_wf(st@.envs),
            spec_eval_do_while_loop(prog@, slbls, body, cond, SpecCompletionValue::Empty, old(st)@)
                == spec_eval_do_while_loop(prog@, slbls, body, cond, cur_cv@, st@),
        decreases st.fuel,
    {
        let rbase = st.temp_roots.len();
        if let CompletionValue::Present(ref v) = cur_cv {
            st.push_root(v);
        }
        let bstep = eval_stmt(prog, body, st);
        st.truncate_roots(rbase);
        let next_cv = match bstep {
            StmtStep::OutOfFuel => return StmtStep::OutOfFuel,
            StmtStep::HeapQuotaExceeded => return StmtStep::HeapQuotaExceeded,
            StmtStep::Unsupported(f) => return StmtStep::Unsupported(f),
            StmtStep::Comp(Completion::Normal(bcv)) => update_empty_val(bcv, cur_cv),
            StmtStep::Comp(Completion::Continue(ccv, target)) => {
                let merged = update_empty_val(ccv, cur_cv);
                if iter_target_matches_exec(labels, &target) {
                    merged
                } else {
                    return StmtStep::Comp(Completion::Continue(merged, target));
                }
            }
            StmtStep::Comp(Completion::Break(bcv, target)) => {
                let merged = update_empty_val(bcv, cur_cv);
                if iter_target_matches_exec(labels, &target) {
                    return StmtStep::Comp(Completion::normal_val(unwrap_or_undefined(merged)));
                } else {
                    return StmtStep::Comp(Completion::Break(merged, target));
                }
            }
            StmtStep::Comp(other_c) => return StmtStep::Comp(other_c),
        };
        if let CompletionValue::Present(ref v) = next_cv {
            st.push_root(v);
        }
        let cstep = eval_expr(prog, cond, st);
        st.truncate_roots(rbase);
        match cstep {
            ExprStep::Val(cv) => {
                if val_to_boolean(&cv) {
                    cur_cv = next_cv;
                } else {
                    return StmtStep::Comp(Completion::normal_val(unwrap_or_undefined(next_cv)));
                }
            }
            abrupt => return expr_abrupt_to_stmt(abrupt),
        }
    }
}

/// Rank 14: `for (init; cond; update) body` with Per-Iteration `let` Environment Cloning (§14.7.4.3)!
pub enum ForIterStep {
    ContinueIter(CompletionValue),
    Done(StmtStep),
}

pub enum SpecForIterStep {
    ContinueIter(SpecCompletionValue),
    Done(SpecStmtStep),
}

impl View for ForIterStep {
    type V = SpecForIterStep;

    open spec fn view(&self) -> SpecForIterStep {
        match self {
            ForIterStep::ContinueIter(cv) => SpecForIterStep::ContinueIter(cv@),
            ForIterStep::Done(s) => SpecForIterStep::Done(s@),
        }
    }
}

pub open spec fn spec_eval_for_iter_step(
    prog: SpecProgram,
    labels: Seq<Seq<u16>>,
    per_iter_lets: Seq<Seq<u16>>,
    cond: Option<ExprId>,
    update: Option<ExprId>,
    body: StmtId,
    cur_cv: SpecCompletionValue,
    st: SpecState,
) -> (SpecState, SpecForIterStep)
    decreases st.fuel, 13nat, 1nat,
{
    spec_eval_for_iter_step_inner(prog, labels, per_iter_lets, cond, update, body, cur_cv, st)
}

#[verifier::opaque]
pub open spec fn spec_eval_for_iter_step_inner(
    prog: SpecProgram,
    labels: Seq<Seq<u16>>,
    per_iter_lets: Seq<Seq<u16>>,
    cond: Option<ExprId>,
    update: Option<ExprId>,
    body: StmtId,
    cur_cv: SpecCompletionValue,
    st: SpecState,
) -> (SpecState, SpecForIterStep)
    decreases st.fuel, 13nat, 0nat,
{
    let rbase = st.temp_roots.len();
    let (st1, cond_res): (SpecState, Option<SpecStmtStep>) = match cond {
        None => (st, None),
        Some(ce) => {
            let st_r = match cur_cv {
                SpecCompletionValue::Present(v) => spec_push_root(st, v),
                SpecCompletionValue::Empty => st,
            };
            let (sc_raw, cstep) = spec_eval_expr(prog, ce, st_r);
            let sc = spec_truncate_roots(spec_cap_fuel(sc_raw, st.fuel), rbase);
            match cstep {
                SpecExprStep::Val(cv) => {
                    if !spec_to_boolean(cv) {
                        (sc, Some(SpecStmtStep::Comp(SpecCompletion::Normal(SpecCompletionValue::Present(spec_unwrap_or_undefined(cur_cv))))))
                    } else {
                        (sc, None)
                    }
                }
                abrupt => (sc, Some(spec_expr_abrupt_to_stmt(abrupt))),
            }
        }
    };
    match cond_res {
        Some(done) => (st1, SpecForIterStep::Done(done)),
        None => {
            let st_r2 = match cur_cv {
                SpecCompletionValue::Present(v) => spec_push_root(st1, v),
                SpecCompletionValue::Empty => st1,
            };
            let (st2_raw, bstep) = spec_eval_stmt(prog, body, st_r2);
            match bstep {
                SpecStmtStep::OutOfFuel =>
                    (spec_truncate_roots(spec_cap_fuel(st2_raw, 0), rbase), SpecForIterStep::Done(SpecStmtStep::OutOfFuel)),
                SpecStmtStep::HeapQuotaExceeded =>
                    (spec_truncate_roots(spec_cap_fuel(st2_raw, st1.fuel), rbase), SpecForIterStep::Done(SpecStmtStep::HeapQuotaExceeded)),
                SpecStmtStep::Unsupported(f) =>
                    (spec_truncate_roots(spec_cap_fuel(st2_raw, st1.fuel), rbase), SpecForIterStep::Done(SpecStmtStep::Unsupported(f))),
                SpecStmtStep::Comp(bcomp) => {
                    if st.fuel == 0 || st1.fuel == 0 {
                        (spec_truncate_roots(spec_cap_fuel(st2_raw, 0), rbase), SpecForIterStep::Done(SpecStmtStep::OutOfFuel))
                    } else {
                        let st2 = spec_truncate_roots(spec_cap_fuel(st2_raw, (st1.fuel - 1) as nat), rbase);
                        let cont_cv: Option<SpecCompletionValue> = match bcomp {
                            SpecCompletion::Normal(bcv) => Some(spec_update_empty_val(bcv, cur_cv)),
                            SpecCompletion::Continue(ccv, target) => {
                                if spec_iter_target_matches(labels, target) {
                                    Some(spec_update_empty_val(ccv, cur_cv))
                                } else {
                                    None
                                }
                            }
                            _ => None,
                        };
                        match cont_cv {
                            Some(next_cv) => {
                                let (envs3, next_env) = spec_clone_per_iter_env(st2.envs, st2.current_env, per_iter_lets);
                                let st3 = SpecState { envs: envs3, current_env: next_env, ..st2 };
                                match update {
                                    None => (st3, SpecForIterStep::ContinueIter(next_cv)),
                                    Some(ue) => {
                                        let st_r3 = match next_cv {
                                            SpecCompletionValue::Present(v) => spec_push_root(st3, v),
                                            SpecCompletionValue::Empty => st3,
                                        };
                                        let (st4_raw, ustep) = spec_eval_expr(prog, ue, st_r3);
                                        let st4 = spec_truncate_roots(spec_cap_fuel(st4_raw, st3.fuel), rbase);
                                        match ustep {
                                            SpecExprStep::Val(_) => (st4, SpecForIterStep::ContinueIter(next_cv)),
                                            abrupt => (st4, SpecForIterStep::Done(spec_expr_abrupt_to_stmt(abrupt))),
                                        }
                                    }
                                }
                            }
                            None => {
                                match bcomp {
                                    SpecCompletion::Continue(ccv, target) =>
                                        (st2, SpecForIterStep::Done(SpecStmtStep::Comp(SpecCompletion::Continue(spec_update_empty_val(ccv, cur_cv), target)))),
                                    SpecCompletion::Break(bcv, target) => {
                                        let merged = spec_update_empty_val(bcv, cur_cv);
                                        if spec_iter_target_matches(labels, target) {
                                            (st2, SpecForIterStep::Done(SpecStmtStep::Comp(SpecCompletion::Normal(SpecCompletionValue::Present(spec_unwrap_or_undefined(merged))))))
                                        } else {
                                            (st2, SpecForIterStep::Done(SpecStmtStep::Comp(SpecCompletion::Break(merged, target))))
                                        }
                                    }
                                    other_c => (st2, SpecForIterStep::Done(SpecStmtStep::Comp(other_c))),
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
fn eval_for_iter_step(
    prog: &Program,
    labels: &Vec<JsStr>,
    per_iter_lets: &Vec<JsStr>,
    cond: Option<ExprId>,
    update: Option<ExprId>,
    body: StmtId,
    cur_cv: CompletionValue,
    st: &mut VmState,
) -> (res: ForIterStep)
    ensures
        (final(st)@, res@) == spec_eval_for_iter_step(
            prog@,
            spec_str_seq_view(labels@),
            spec_str_seq_view(per_iter_lets@),
            cond,
            update,
            body,
            cur_cv@,
            old(st)@,
        ),
        final(st).fuel <= old(st).fuel,
        match res@ {
            SpecForIterStep::ContinueIter(_) => old(st).fuel > 0 && final(st).fuel < old(st).fuel,
            SpecForIterStep::Done(s) => (s is OutOfFuel) ==> final(st).fuel == 0,
        },
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 13nat, 0nat,
{
    reveal(spec_eval_for_iter_step_inner);
    let rbase = st.temp_roots.len();
    if let Some(ce) = cond {
        if let CompletionValue::Present(ref v) = cur_cv {
            st.push_root(v);
        }
        let cstep = eval_expr(prog, ce, st);
        st.truncate_roots(rbase);
        match cstep {
            ExprStep::Val(cv) => {
                if !val_to_boolean(&cv) {
                    return ForIterStep::Done(StmtStep::Comp(Completion::normal_val(unwrap_or_undefined(cur_cv))));
                }
            }
            abrupt => return ForIterStep::Done(expr_abrupt_to_stmt(abrupt)),
        }
    }
    if let CompletionValue::Present(ref v) = cur_cv {
        st.push_root(v);
    }
    let bstep = eval_stmt(prog, body, st);
    st.truncate_roots(rbase);
    let next_cv = match bstep {
        StmtStep::OutOfFuel => return ForIterStep::Done(StmtStep::OutOfFuel),
        StmtStep::HeapQuotaExceeded => return ForIterStep::Done(StmtStep::HeapQuotaExceeded),
        StmtStep::Unsupported(f) => return ForIterStep::Done(StmtStep::Unsupported(f)),
        StmtStep::Comp(Completion::Normal(bcv)) => update_empty_val(bcv, cur_cv),
        StmtStep::Comp(Completion::Continue(ccv, target)) => {
            let merged = update_empty_val(ccv, cur_cv);
            if iter_target_matches_exec(labels, &target) {
                merged
            } else {
                return ForIterStep::Done(StmtStep::Comp(Completion::Continue(merged, target)));
            }
        }
        StmtStep::Comp(Completion::Break(bcv, target)) => {
            let merged = update_empty_val(bcv, cur_cv);
            if iter_target_matches_exec(labels, &target) {
                return ForIterStep::Done(StmtStep::Comp(Completion::normal_val(unwrap_or_undefined(merged))));
            } else {
                return ForIterStep::Done(StmtStep::Comp(Completion::Break(merged, target)));
            }
        }
        StmtStep::Comp(other_c) => return ForIterStep::Done(StmtStep::Comp(other_c)),
    };
    let cenv = st.current_env;
    let next_env = st.envs.clone_per_iter_env(cenv, per_iter_lets);
    st.current_env = next_env;
    if let Some(ue) = update {
        if let CompletionValue::Present(ref v) = next_cv {
            st.push_root(v);
        }
        let ustep = eval_expr(prog, ue, st);
        st.truncate_roots(rbase);
        match ustep {
            ExprStep::Val(_) => {}
            abrupt => return ForIterStep::Done(expr_abrupt_to_stmt(abrupt)),
        }
    }
    ForIterStep::ContinueIter(next_cv)
}

pub open spec fn spec_eval_for_loop(
    prog: SpecProgram,
    labels: Seq<Seq<u16>>,
    per_iter_lets: Seq<Seq<u16>>,
    cond: Option<ExprId>,
    update: Option<ExprId>,
    body: StmtId,
    cur_cv: SpecCompletionValue,
    st: SpecState,
) -> (SpecState, SpecStmtStep)
    decreases st.fuel, 14nat, 0nat,
{
    let (st1_raw, step) = spec_eval_for_iter_step(prog, labels, per_iter_lets, cond, update, body, cur_cv, st);
    match step {
        SpecForIterStep::Done(s) => (spec_cap_fuel(st1_raw, st.fuel), s),
        SpecForIterStep::ContinueIter(next_cv) => {
            if st.fuel == 0 {
                (spec_cap_fuel(st1_raw, 0), SpecStmtStep::OutOfFuel)
            } else {
                let st1 = spec_cap_fuel(st1_raw, (st.fuel - 1) as nat);
                spec_eval_for_loop(prog, labels, per_iter_lets, cond, update, body, next_cv, st1)
            }
        }
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(25)]
fn eval_for_loop(
    prog: &Program,
    labels: &Vec<JsStr>,
    per_iter_lets: &Vec<JsStr>,
    cond: Option<ExprId>,
    update: Option<ExprId>,
    body: StmtId,
    st: &mut VmState,
) -> (res: StmtStep)
    ensures
        (final(st)@, res@) == spec_eval_for_loop(
            prog@,
            spec_str_seq_view(labels@),
            spec_str_seq_view(per_iter_lets@),
            cond,
            update,
            body,
            SpecCompletionValue::Empty,
            old(st)@,
        ),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 14nat, 1nat,
{
    let mut cur_cv = CompletionValue::Empty;
    let ghost slbls = spec_str_seq_view(labels@);
    let ghost slets = spec_str_seq_view(per_iter_lets@);
    loop
        invariant
            slbls == spec_str_seq_view(labels@),
            slets == spec_str_seq_view(per_iter_lets@),
            st.fuel <= old(st).fuel,
            env_wf(old(st)@.envs) ==> env_wf(st@.envs),
            spec_eval_for_loop(prog@, slbls, slets, cond, update, body, SpecCompletionValue::Empty, old(st)@)
                == spec_eval_for_loop(prog@, slbls, slets, cond, update, body, cur_cv@, st@),
        decreases st.fuel,
    {
        match eval_for_iter_step(prog, labels, per_iter_lets, cond, update, body, cur_cv, st) {
            ForIterStep::ContinueIter(next_cv) => {
                cur_cv = next_cv;
            }
            ForIterStep::Done(done_step) => return done_step,
        }
    }
}

pub open spec fn spec_eval_for_stmt(
    prog: SpecProgram,
    labels: Seq<Seq<u16>>,
    init: Option<StmtId>,
    per_iter_lets: Seq<Seq<u16>>,
    cond: Option<ExprId>,
    update: Option<ExprId>,
    body: StmtId,
    st: SpecState,
) -> (SpecState, SpecStmtStep)
    decreases st.fuel, 14nat, 3nat,
{
    spec_eval_for_stmt_inner(prog, labels, init, per_iter_lets, cond, update, body, st)
}

#[verifier::opaque]
pub open spec fn spec_eval_for_stmt_inner(
    prog: SpecProgram,
    labels: Seq<Seq<u16>>,
    init: Option<StmtId>,
    per_iter_lets: Seq<Seq<u16>>,
    cond: Option<ExprId>,
    update: Option<ExprId>,
    body: StmtId,
    st: SpecState,
) -> (SpecState, SpecStmtStep)
    decreases st.fuel, 14nat, 2nat,
{
    let saved_env = st.current_env;
    let erbase = st.env_roots.len();
    let (envs1, loop_env) = spec_alloc_env(st.envs, EnvKind::Block, saved_env, None);
    let st1 = spec_push_env_root(SpecState { envs: envs1, current_env: loop_env, ..st }, saved_env);
    let (st2, init_err): (SpecState, Option<SpecStmtStep>) = match init {
        None => (st1, None),
        Some(isid) => {
            let (st_h, hstep) = spec_hoist_one_stmt_decl(prog, isid, loop_env, st1);
            match hstep {
                SpecExprStep::Val(_) => {
                    let (st_i_raw, istep) = spec_eval_stmt(prog, isid, st_h);
                    let st_i = spec_cap_fuel(st_i_raw, st_h.fuel);
                    match istep {
                        SpecStmtStep::Comp(SpecCompletion::Normal(_)) => {
                            let (e_first, first_env) = spec_clone_per_iter_env(st_i.envs, loop_env, per_iter_lets);
                            (SpecState { envs: e_first, current_env: first_env, ..st_i }, None)
                        }
                        other => (st_i, Some(other)),
                    }
                }
                abrupt => (st_h, Some(spec_expr_abrupt_to_stmt(abrupt))),
            }
        }
    };
    match init_err {
        Some(err) => (spec_truncate_env_roots(SpecState { current_env: saved_env, ..st2 }, erbase), err),
        None => {
            let (st3_raw, lres) = spec_eval_for_loop(
                prog, labels, per_iter_lets, cond, update, body, SpecCompletionValue::Empty, st2,
            );
            (spec_truncate_env_roots(SpecState { current_env: saved_env, ..spec_cap_fuel(st3_raw, st2.fuel) }, erbase), lres)
        }
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(25)]
fn eval_for_stmt(
    prog: &Program,
    labels: &Vec<JsStr>,
    init: Option<StmtId>,
    per_iter_lets: &Vec<JsStr>,
    cond: Option<ExprId>,
    update: Option<ExprId>,
    body: StmtId,
    st: &mut VmState,
) -> (res: StmtStep)
    ensures
        (final(st)@, res@) == spec_eval_for_stmt(
            prog@,
            spec_str_seq_view(labels@),
            init,
            spec_str_seq_view(per_iter_lets@),
            cond,
            update,
            body,
            old(st)@,
        ),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 14nat, 2nat,
{
    reveal(spec_eval_for_stmt_inner);
    let saved_env = st.current_env;
    let erbase = st.env_roots.len();
    let loop_env = st.envs.alloc_env(EnvKind::Block, saved_env, None);
    st.current_env = loop_env;
    st.push_env_root(saved_env);
    if let Some(isid) = init {
        let hstep = hoist_one_stmt_decl_exec(prog, isid, loop_env, st);
        match hstep {
            ExprStep::Val(_) => {}
            abrupt => {
                st.current_env = saved_env;
                st.truncate_env_roots(erbase);
                return expr_abrupt_to_stmt(abrupt);
            }
        }
        let istep = eval_stmt(prog, isid, st);
        match istep {
            StmtStep::Comp(Completion::Normal(_)) => {
                let first_env = st.envs.clone_per_iter_env(loop_env, per_iter_lets);
                st.current_env = first_env;
            }
            other => {
                st.current_env = saved_env;
                st.truncate_env_roots(erbase);
                return other;
            }
        }
    }
    let lres = eval_for_loop(prog, labels, per_iter_lets, cond, update, body, st);
    st.current_env = saved_env;
    st.truncate_env_roots(erbase);
    lres
}

/// Rank 10: Verified Statement Evaluator (`decreases (st.fuel, 10nat, 0nat)`)
pub open spec fn spec_eval_stmt(
    prog: SpecProgram,
    stmt_id: StmtId,
    st: SpecState,
) -> (SpecState, SpecStmtStep)
    decreases st.fuel, 10nat, 1nat,
{
    spec_eval_stmt_inner(prog, stmt_id, st)
}

#[verifier::opaque]
pub open spec fn spec_eval_stmt_inner(
    prog: SpecProgram,
    stmt_id: StmtId,
    st: SpecState,
) -> (SpecState, SpecStmtStep)
    decreases st.fuel, 10nat, 0nat,
{
    if st.fuel == 0 {
        (st, SpecStmtStep::OutOfFuel)
    } else {
        let st_dec = SpecState { fuel: (st.fuel - 1) as nat, ..st };
        if (stmt_id.0 as int) >= prog.stmts.len() {
            (st_dec, SpecStmtStep::Unsupported(UnsupportedFeature::InvalidAstReference))
        } else {
            let (st_out, r) = match prog.stmts[stmt_id.0 as int] {
                SpecStmtNode::Empty | SpecStmtNode::FuncDecl { .. } =>
                    (st_dec, SpecStmtStep::Comp(SpecCompletion::Normal(SpecCompletionValue::Empty))),
                SpecStmtNode::ExprStmt(eid) => {
                    let (s1, es) = spec_eval_expr(prog, eid, st_dec);
                    (s1, spec_expr_abrupt_to_stmt(es))
                }
                SpecStmtNode::Block { stmts } => spec_eval_block_stmt(prog, stmts, st_dec),
                SpecStmtNode::VarDecl { kind, decls } => {
                    let (s1, es) = spec_eval_var_decls(prog, kind, decls, 0, st_dec);
                    match es {
                        SpecExprStep::Val(_) =>
                            (s1, SpecStmtStep::Comp(SpecCompletion::Normal(SpecCompletionValue::Empty))),
                        abrupt => (s1, spec_expr_abrupt_to_stmt(abrupt)),
                    }
                }
                SpecStmtNode::If { cond, then_branch, else_branch } =>
                    spec_eval_if_stmt(prog, cond, then_branch, else_branch, st_dec),
                SpecStmtNode::While { labels, cond, body } =>
                    spec_eval_while_loop(prog, labels, cond, body, SpecCompletionValue::Empty, st_dec),
                SpecStmtNode::DoWhile { labels, body, cond } =>
                    spec_eval_do_while_loop(prog, labels, body, cond, SpecCompletionValue::Empty, st_dec),
                SpecStmtNode::For { labels, init, per_iter_lets, cond, update, body } =>
                    spec_eval_for_stmt(prog, labels, init, per_iter_lets, cond, update, body, st_dec),
                SpecStmtNode::ForIn { labels, lhs, object, body } =>
                    spec_eval_for_in_stmt(prog, labels, lhs, object, body, st_dec),
                SpecStmtNode::ForOf { labels, lhs, iterable, body } =>
                    spec_eval_for_of_stmt(prog, labels, lhs, iterable, body, st_dec),
                SpecStmtNode::Switch { label, discriminant, cases } =>
                    spec_eval_switch_stmt(prog, label, discriminant, cases, st_dec),
                SpecStmtNode::Return(opt_e) => match opt_e {
                    None => (st_dec, SpecStmtStep::Comp(SpecCompletion::Return(SpecVal::Undefined))),
                    Some(eid) => {
                        let (s1, es) = spec_eval_expr(prog, eid, st_dec);
                        match es {
                            SpecExprStep::Val(v) => (s1, SpecStmtStep::Comp(SpecCompletion::Return(v))),
                            abrupt => (s1, spec_expr_abrupt_to_stmt(abrupt)),
                        }
                    }
                },
                SpecStmtNode::Break(lbl) =>
                    (st_dec, SpecStmtStep::Comp(SpecCompletion::Break(SpecCompletionValue::Empty, lbl))),
                SpecStmtNode::Continue(lbl) =>
                    (st_dec, SpecStmtStep::Comp(SpecCompletion::Continue(SpecCompletionValue::Empty, lbl))),
                SpecStmtNode::Throw(eid) => {
                    let (s1, es) = spec_eval_expr(prog, eid, st_dec);
                    match es {
                        SpecExprStep::Val(v) => (s1, SpecStmtStep::Comp(SpecCompletion::Throw(v))),
                        abrupt => (s1, spec_expr_abrupt_to_stmt(abrupt)),
                    }
                }
                SpecStmtNode::Try { block, catch_param, catch_body, finally_body } =>
                    spec_eval_try_stmt(prog, block, catch_param, catch_body, finally_body, st_dec),
                SpecStmtNode::Labeled { label, body } =>
                    spec_eval_labeled_stmt(prog, label, body, st_dec),
                SpecStmtNode::UnsupportedStmt(f) => (st_dec, SpecStmtStep::Unsupported(f)),
            };
            (spec_cap_fuel(st_out, st_dec.fuel), r)
        }
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub fn eval_stmt(
    prog: &Program,
    stmt_id: StmtId,
    st: &mut VmState,
) -> (res: StmtStep)
    ensures
        (final(st)@, res@) == spec_eval_stmt(prog@, stmt_id, old(st)@),
        final(st).fuel <= old(st).fuel,
        (res@ is OutOfFuel) ==> final(st).fuel == 0,
        !(res@ is OutOfFuel) ==> old(st).fuel > 0 && final(st).fuel < old(st).fuel,
        env_wf(old(st)@.envs) ==> env_wf(final(st)@.envs),
    decreases st.fuel, 10nat, 0nat,
{
    reveal(spec_eval_stmt_inner);
    if st.fuel == 0 {
        return StmtStep::OutOfFuel;
    }
    st.fuel -= 1;
    if stmt_id.0 >= prog.stmts.len() {
        return StmtStep::Unsupported(UnsupportedFeature::InvalidAstReference);
    }
    proof { assert(prog@.stmts[stmt_id.0 as int] == prog.stmts@[stmt_id.0 as int]@); }
    match &prog.stmts[stmt_id.0] {
        StmtNode::Empty | StmtNode::FuncDecl { .. } => StmtStep::Comp(Completion::normal_empty()),
        StmtNode::ExprStmt(eid) => expr_abrupt_to_stmt(eval_expr(prog, *eid, st)),
        StmtNode::Block { stmts } => eval_block_stmt(prog, stmts, st),
        StmtNode::VarDecl { kind, decls } => match eval_var_decls(prog, *kind, decls, st) {
            ExprStep::Val(_) => StmtStep::Comp(Completion::normal_empty()),
            abrupt => expr_abrupt_to_stmt(abrupt),
        },
        StmtNode::If { cond, then_branch, else_branch } =>
            eval_if_stmt(prog, *cond, *then_branch, *else_branch, st),
        StmtNode::While { labels, cond, body } => eval_while_loop(prog, labels, *cond, *body, st),
        StmtNode::DoWhile { labels, body, cond } => eval_do_while_loop(prog, labels, *body, *cond, st),
        StmtNode::For { labels, init, per_iter_lets, cond, update, body } =>
            eval_for_stmt(prog, labels, *init, per_iter_lets, *cond, *update, *body, st),
        StmtNode::ForIn { labels, lhs, object, body } =>
            eval_for_in_stmt(prog, labels, lhs, *object, *body, st),
        StmtNode::ForOf { labels, lhs, iterable, body } =>
            eval_for_of_stmt(prog, labels, lhs, *iterable, *body, st),
        StmtNode::Switch { label, discriminant, cases } =>
            eval_switch_stmt(prog, label, *discriminant, cases, st),
        StmtNode::Return(opt_e) => match opt_e {
            None => StmtStep::Comp(Completion::Return(Val::Undefined)),
            Some(eid) => match eval_expr(prog, *eid, st) {
                ExprStep::Val(v) => StmtStep::Comp(Completion::Return(v)),
                abrupt => expr_abrupt_to_stmt(abrupt),
            },
        },
        StmtNode::Break(lbl) => {
            let cl = match lbl { Some(s) => Some(clone_js_str(s)), None => None };
            StmtStep::Comp(Completion::Break(CompletionValue::Empty, cl))
        }
        StmtNode::Continue(lbl) => {
            let cl = match lbl { Some(s) => Some(clone_js_str(s)), None => None };
            StmtStep::Comp(Completion::Continue(CompletionValue::Empty, cl))
        }
        StmtNode::Throw(eid) => match eval_expr(prog, *eid, st) {
            ExprStep::Val(v) => StmtStep::Comp(Completion::Throw(v)),
            abrupt => expr_abrupt_to_stmt(abrupt),
        },
        StmtNode::Try { block, catch_param, catch_body, finally_body } =>
            eval_try_stmt(prog, *block, catch_param, *catch_body, *finally_body, st),
        StmtNode::Labeled { label, body } => eval_labeled_stmt(prog, label, *body, st),
        StmtNode::UnsupportedStmt(f) => StmtStep::Unsupported(*f),
    }
}

// ===========================================================================
// Top-Level Program Evaluation & End-to-End Step-Refinement Theorem (§3.3)
// ===========================================================================

/// Complete mathematical specification of top-level ECMAScript `ScriptEvaluation` (§16.1.7)
/// returning `(final_state, SpecOutcome)` for program `p`, step budget `fuel`, and `heap_quota`.
pub open spec fn spec_eval_program_state(
    p: SpecProgram,
    fuel: nat,
    heap_quota: nat,
) -> (SpecState, SpecOutcome) {
    let st0 = spec_bootstrap_realm(fuel, heap_quota);
    let st1 = SpecState { strict: p.strict, ..st0 };
    let st2 = spec_hoist_vars_from(p.hoisted_vars, 0, EnvId(0), p.strict, st1);
    let (st3, hstep) = spec_hoist_block_stmts(p, p.body, 0, EnvId(0), st2);
    match hstep {
        SpecExprStep::Val(_) => {
            let (st4_raw, bstep) = spec_eval_stmt_list(p, p.body, 0, SpecCompletionValue::Empty, st3);
            let st4 = spec_cap_fuel(st4_raw, st3.fuel);
            match bstep {
                SpecStmtStep::Comp(SpecCompletion::Normal(cv)) =>
                    (st4, SpecOutcome::Done(SpecScriptCompletion::Normal(spec_unwrap_or_undefined(cv)))),
                SpecStmtStep::Comp(SpecCompletion::Throw(tv)) =>
                    (st4, SpecOutcome::Done(SpecScriptCompletion::Throw(tv))),
                SpecStmtStep::Comp(SpecCompletion::Return(rv)) =>
                    (st4, SpecOutcome::Done(SpecScriptCompletion::Normal(rv))),
                SpecStmtStep::Comp(SpecCompletion::Break(cv, _))
                | SpecStmtStep::Comp(SpecCompletion::Continue(cv, _)) =>
                    (st4, SpecOutcome::Done(SpecScriptCompletion::Normal(spec_unwrap_or_undefined(cv)))),
                SpecStmtStep::HeapQuotaExceeded =>
                    (st4, SpecOutcome::Done(SpecScriptCompletion::HeapQuotaExceeded)),
                SpecStmtStep::OutOfFuel => (st4, SpecOutcome::OutOfFuel),
                SpecStmtStep::Unsupported(feat) => (st4, SpecOutcome::Unsupported(feat)),
            }
        }
        SpecExprStep::Throw(tv) =>
            (st3, SpecOutcome::Done(SpecScriptCompletion::Throw(tv))),
        SpecExprStep::HeapQuotaExceeded =>
            (st3, SpecOutcome::Done(SpecScriptCompletion::HeapQuotaExceeded)),
        SpecExprStep::OutOfFuel => (st3, SpecOutcome::OutOfFuel),
        SpecExprStep::Unsupported(feat) => (st3, SpecOutcome::Unsupported(feat)),
    }
}

pub open spec fn spec_eval_program_with_quota(
    p: SpecProgram,
    fuel: nat,
    heap_quota: nat,
) -> SpecOutcome {
    spec_eval_program_state(p, fuel, heap_quota).1
}

/// Top-level specification `spec_eval_program(p, fuel)` (`docs/verified-browser-engine.md` §3.3).
pub open spec fn spec_eval_program(p: SpecProgram, fuel: nat) -> SpecOutcome {
    spec_eval_program_with_quota(p, fuel, DEFAULT_REALM_HEAP_QUOTA as nat)
}

/// Execute `p` with explicit `fuel` and `heap_quota`, returning `(final_vm_state, RunResult)`
/// with machine-checked end-to-end refinement AND fuel-exhaustion exactness AND `env_wf` preservation!
pub fn run_state_with_quota(
    p: &Program,
    fuel: usize,
    heap_quota: usize,
) -> (out: (VmState, RunResult))
    ensures
        (out.0@, out.1@) == spec_eval_program_state(p@, fuel as nat, heap_quota as nat),
        env_wf(out.0@.envs),
        out.0.fuel <= fuel,
        match out.1 {
            RunResult::Done(ref v) =>
                spec_eval_program_with_quota(p@, fuel as nat, heap_quota as nat) == SpecOutcome::Done(v@),
            RunResult::OutOfFuel =>
                spec_eval_program_with_quota(p@, fuel as nat, heap_quota as nat) == SpecOutcome::OutOfFuel
                && out.0.fuel == 0,
            RunResult::Unsupported(feat) =>
                spec_eval_program_with_quota(p@, fuel as nat, heap_quota as nat) == SpecOutcome::Unsupported(feat@),
        },
{
    let mut st = bootstrap_realm(fuel, heap_quota);
    st.strict = p.strict;
    hoist_vars_exec(&p.hoisted_vars, EnvId(0), p.strict, &mut st);
    let hstep = hoist_block_stmts_exec(p, &p.body, EnvId(0), &mut st);
    let res = match hstep {
        ExprStep::Val(_) => {
            let bstep = eval_stmt_list(p, &p.body, CompletionValue::Empty, &mut st);
            match bstep {
                StmtStep::Comp(Completion::Normal(cv)) =>
                    RunResult::Done(ScriptCompletion::Normal(unwrap_or_undefined(cv))),
                StmtStep::Comp(Completion::Throw(tv)) =>
                    RunResult::Done(ScriptCompletion::Throw(tv)),
                StmtStep::Comp(Completion::Return(rv)) =>
                    RunResult::Done(ScriptCompletion::Normal(rv)),
                StmtStep::Comp(Completion::Break(cv, _))
                | StmtStep::Comp(Completion::Continue(cv, _)) =>
                    RunResult::Done(ScriptCompletion::Normal(unwrap_or_undefined(cv))),
                StmtStep::HeapQuotaExceeded =>
                    RunResult::Done(ScriptCompletion::HeapQuotaExceeded),
                StmtStep::OutOfFuel => RunResult::OutOfFuel,
                StmtStep::Unsupported(feat) => RunResult::Unsupported(feat),
            }
        }
        ExprStep::Throw(tv) => RunResult::Done(ScriptCompletion::Throw(tv)),
        ExprStep::HeapQuotaExceeded => RunResult::Done(ScriptCompletion::HeapQuotaExceeded),
        ExprStep::OutOfFuel => RunResult::OutOfFuel,
        ExprStep::Unsupported(feat) => RunResult::Unsupported(feat),
    };
    (st, res)
}

/// Execute `p` under `fuel` and explicit `heap_quota` (`docs/verified-browser-engine.md` §3.3).
pub fn run_with_quota(p: &Program, fuel: usize, heap_quota: usize) -> (res: RunResult)
    ensures
        res@ == spec_eval_program_with_quota(p@, fuel as nat, heap_quota as nat),
        match res {
            RunResult::Done(ref v) =>
                spec_eval_program_with_quota(p@, fuel as nat, heap_quota as nat) == SpecOutcome::Done(v@),
            RunResult::OutOfFuel =>
                spec_eval_program_with_quota(p@, fuel as nat, heap_quota as nat) == SpecOutcome::OutOfFuel
                && spec_eval_program_state(p@, fuel as nat, heap_quota as nat).0.fuel == 0,
            RunResult::Unsupported(feat) =>
                spec_eval_program_with_quota(p@, fuel as nat, heap_quota as nat) == SpecOutcome::Unsupported(feat@),
        },
{
    let (_, res) = run_state_with_quota(p, fuel, heap_quota);
    res
}

/// Top-level End-to-End Verified Interpreter Entrypoint `vjs::run(p, fuel)` (`docs/verified-browser-engine.md` §3.3):
/// Proves for EVERY program `p` and fuel `n`:
/// - `RunResult::Done(v)` ==> `spec_eval_program(p@, n as nat) == SpecOutcome::Done(v@)`
/// - `RunResult::OutOfFuel` ==> `spec_eval_program(p@, n as nat) == SpecOutcome::OutOfFuel` AND all `n` fuel steps were consumed (`remaining_fuel == 0`)
/// - `RunResult::Unsupported(feat)` ==> `spec_eval_program(p@, n as nat) == SpecOutcome::Unsupported(feat@)`
pub fn run(p: &Program, fuel: usize) -> (res: RunResult)
    ensures
        res@ == spec_eval_program(p@, fuel as nat),
        match res {
            RunResult::Done(ref v) =>
                spec_eval_program(p@, fuel as nat) == SpecOutcome::Done(v@),
            RunResult::OutOfFuel =>
                spec_eval_program(p@, fuel as nat) == SpecOutcome::OutOfFuel
                && spec_eval_program_state(p@, fuel as nat, DEFAULT_REALM_HEAP_QUOTA as nat).0.fuel == 0,
            RunResult::Unsupported(feat) =>
                spec_eval_program(p@, fuel as nat) == SpecOutcome::Unsupported(feat@),
        },
{
    run_with_quota(p, fuel, DEFAULT_REALM_HEAP_QUOTA)
}

/// Top-Level End-to-End Step-Refinement & Fuel-Exactness Theorem (`docs/verified-browser-engine.md` §3.3):
/// Every `RunResult` returned by `vjs::run(p, fuel)` refines `spec_eval_program(p@, fuel as nat)` into
/// mutually exclusive `Done(v@)`, `OutOfFuel` (with remaining fuel `0` — all `fuel` steps consumed),
/// or explicit `Unsupported(feat@)` refusal.
pub proof fn theorem_end_to_end_step_refinement(p: SpecProgram, fuel: nat, res: RunResult, final_st: SpecState)
    requires
        (final_st, res@) == spec_eval_program_state(p, fuel, DEFAULT_REALM_HEAP_QUOTA as nat),
        (res is OutOfFuel) ==> final_st.fuel == 0,
    ensures
        match res {
            RunResult::Done(v) =>
                spec_eval_program(p, fuel) == SpecOutcome::Done(v@),
            RunResult::OutOfFuel =>
                spec_eval_program(p, fuel) == SpecOutcome::OutOfFuel
                && final_st.fuel == 0,
            RunResult::Unsupported(feat) =>
                spec_eval_program(p, fuel) == SpecOutcome::Unsupported(feat@),
        },
{
}

} // verus!
