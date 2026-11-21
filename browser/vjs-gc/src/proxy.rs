//! Proxy Exotic Object (ECMA-262 §10.5) & Reflect (§28.1) with machine-checked §6.1.7.3
//! Essential Internal Method Invariants proved in Verus against arbitrary/malicious handler traps.
//!
//! Covers:
//! - `ProxyCreate` (§10.5.14) and `Proxy.revocable` (§28.2.2.1), clearing BOTH `[[ProxyTarget]]`
//!   and `[[ProxyHandler]]` to `None` on revocation so all 11 internal methods throw `TypeError`.
//! - Ordinary object internal methods (§10.1) including full `ValidateAndApplyPropertyDescriptor`
//!   (§10.1.6.3) and prototype-chain lookup (`[[HasProperty]]`, `[[Get]]`, `[[Set]]`).
//! - All 11 Proxy internal methods (§10.5.1–§10.5.11) + all 11 `Reflect.*` operations (§28.1).
//! - Machine-checked §6.1.7.3 post-trap invariant theorems for every essential internal method.
use vstd::prelude::*;

verus! {

use crate::types::{same_value, AtomId, JsError, JsVal, ObjId, SymId};

// -----------------------------------------------------------------------------------------------
// Property Keys & Property Descriptors (§6.1.7, §6.2.6)
// -----------------------------------------------------------------------------------------------

/// ECMAScript property key (`String` atom or `Symbol`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PropKey {
    Str(AtomId),
    Symbol(SymId),
}

pub fn prop_key_eq(a: PropKey, b: PropKey) -> (r: bool)
    ensures
        r == (a == b),
{
    match (a, b) {
        (PropKey::Str(x), PropKey::Str(y)) => x == y,
        (PropKey::Symbol(x), PropKey::Symbol(y)) => x == y,
        _ => false,
    }
}

pub fn opt_obj_eq(a: Option<ObjId>, b: Option<ObjId>) -> (r: bool)
    ensures
        r == (a == b),
{
    match (a, b) {
        (None, None) => true,
        (Some(x), Some(y)) => x == y,
        _ => false,
    }
}

/// Complete ECMAScript Property Descriptor (§6.2.6).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PropertyDescriptor {
    Data {
        value: JsVal,
        writable: bool,
        enumerable: bool,
        configurable: bool,
    },
    Accessor {
        get: Option<ObjId>,
        set: Option<ObjId>,
        enumerable: bool,
        configurable: bool,
    },
}

pub open spec fn spec_desc_configurable(d: PropertyDescriptor) -> bool {
    match d {
        PropertyDescriptor::Data { configurable, .. } => configurable,
        PropertyDescriptor::Accessor { configurable, .. } => configurable,
    }
}

pub open spec fn spec_desc_enumerable(d: PropertyDescriptor) -> bool {
    match d {
        PropertyDescriptor::Data { enumerable, .. } => enumerable,
        PropertyDescriptor::Accessor { enumerable, .. } => enumerable,
    }
}

pub fn desc_configurable(d: PropertyDescriptor) -> (b: bool)
    ensures
        b == spec_desc_configurable(d),
{
    match d {
        PropertyDescriptor::Data { configurable, .. } => configurable,
        PropertyDescriptor::Accessor { configurable, .. } => configurable,
    }
}

pub fn desc_enumerable(d: PropertyDescriptor) -> (b: bool)
    ensures
        b == spec_desc_enumerable(d),
{
    match d {
        PropertyDescriptor::Data { enumerable, .. } => enumerable,
        PropertyDescriptor::Accessor { enumerable, .. } => enumerable,
    }
}

/// Partial (uncompleted) Property Descriptor (§6.2.6) supplied to `[[DefineOwnProperty]]` / `Reflect.defineProperty`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct PartialDescriptor {
    pub value: Option<JsVal>,
    pub writable: Option<bool>,
    pub get: Option<Option<ObjId>>,
    pub set: Option<Option<ObjId>>,
    pub enumerable: Option<bool>,
    pub configurable: Option<bool>,
}

impl PartialDescriptor {
    pub fn empty() -> (d: Self)
        ensures
            spec_partial_is_empty(d),
            spec_valid_partial_descriptor(d),
    {
        PartialDescriptor {
            value: None,
            writable: None,
            get: None,
            set: None,
            enumerable: None,
            configurable: None,
        }
    }

    pub fn from_complete(desc: PropertyDescriptor) -> (d: Self)
        ensures
            d == spec_partial_from_complete(desc),
            spec_valid_partial_descriptor(d),
            spec_complete_descriptor(d) == desc,
            d.configurable == Some(spec_desc_configurable(desc)),
            d.enumerable == Some(spec_desc_enumerable(desc)),
    {
        match desc {
            PropertyDescriptor::Data { value, writable, enumerable, configurable } => PartialDescriptor {
                value: Some(value),
                writable: Some(writable),
                get: None,
                set: None,
                enumerable: Some(enumerable),
                configurable: Some(configurable),
            },
            PropertyDescriptor::Accessor { get, set, enumerable, configurable } => PartialDescriptor {
                value: None,
                writable: None,
                get: Some(get),
                set: Some(set),
                enumerable: Some(enumerable),
                configurable: Some(configurable),
            },
        }
    }
}

pub open spec fn spec_partial_from_complete(desc: PropertyDescriptor) -> PartialDescriptor {
    match desc {
        PropertyDescriptor::Data { value, writable, enumerable, configurable } => PartialDescriptor {
            value: Some(value),
            writable: Some(writable),
            get: None,
            set: None,
            enumerable: Some(enumerable),
            configurable: Some(configurable),
        },
        PropertyDescriptor::Accessor { get, set, enumerable, configurable } => PartialDescriptor {
            value: None,
            writable: None,
            get: Some(get),
            set: Some(set),
            enumerable: Some(enumerable),
            configurable: Some(configurable),
        },
    }
}

pub open spec fn spec_partial_has_data(d: PartialDescriptor) -> bool {
    (d.value is Some) || (d.writable is Some)
}

pub open spec fn spec_partial_has_accessor(d: PartialDescriptor) -> bool {
    (d.get is Some) || (d.set is Some)
}

/// ECMA-262 §6.2.6.5 step 22: a descriptor cannot simultaneously specify data and accessor fields.
pub open spec fn spec_valid_partial_descriptor(d: PartialDescriptor) -> bool {
    !(spec_partial_has_data(d) && spec_partial_has_accessor(d))
}

pub open spec fn spec_partial_is_generic(d: PartialDescriptor) -> bool {
    !spec_partial_has_data(d) && !spec_partial_has_accessor(d)
}

pub open spec fn spec_partial_is_empty(d: PartialDescriptor) -> bool {
    spec_partial_is_generic(d) && (d.enumerable is None) && (d.configurable is None)
}

pub fn is_valid_partial_descriptor(d: PartialDescriptor) -> (b: bool)
    ensures
        b == spec_valid_partial_descriptor(d),
{
    let has_data = matches!(d.value, Some(_)) || matches!(d.writable, Some(_));
    let has_acc = matches!(d.get, Some(_)) || matches!(d.set, Some(_));
    !(has_data && has_acc)
}

/// ECMA-262 §6.2.6.6 `CompletePropertyDescriptor(Desc)`.
pub open spec fn spec_complete_descriptor(d: PartialDescriptor) -> PropertyDescriptor {
    let enumerable = match d.enumerable {
        Some(e) => e,
        None => false,
    };
    let configurable = match d.configurable {
        Some(c) => c,
        None => false,
    };
    if spec_partial_has_accessor(d) {
        let get = match d.get {
            Some(g) => g,
            None => None,
        };
        let set = match d.set {
            Some(s) => s,
            None => None,
        };
        PropertyDescriptor::Accessor { get, set, enumerable, configurable }
    } else {
        let value = match d.value {
            Some(v) => v,
            None => JsVal::Undefined,
        };
        let writable = match d.writable {
            Some(w) => w,
            None => false,
        };
        PropertyDescriptor::Data { value, writable, enumerable, configurable }
    }
}

pub fn complete_descriptor(d: PartialDescriptor) -> (out: PropertyDescriptor)
    ensures
        out == spec_complete_descriptor(d),
{
    let enumerable = match d.enumerable {
        Some(e) => e,
        None => false,
    };
    let configurable = match d.configurable {
        Some(c) => c,
        None => false,
    };
    if matches!(d.get, Some(_)) || matches!(d.set, Some(_)) {
        let get = match d.get {
            Some(g) => g,
            None => None,
        };
        let set = match d.set {
            Some(s) => s,
            None => None,
        };
        PropertyDescriptor::Accessor { get, set, enumerable, configurable }
    } else {
        let value = match d.value {
            Some(v) => v,
            None => JsVal::Undefined,
        };
        let writable = match d.writable {
            Some(w) => w,
            None => false,
        };
        PropertyDescriptor::Data { value, writable, enumerable, configurable }
    }
}

/// ECMA-262 §10.1.6.2 / §10.1.6.3 `IsCompatiblePropertyDescriptor(Extensible, Desc, Current)`.
pub open spec fn spec_is_compatible_descriptor(
    extensible: bool,
    desc: PartialDescriptor,
    current: Option<PropertyDescriptor>,
) -> bool {
    if !spec_valid_partial_descriptor(desc) {
        false
    } else {
        match current {
            None => extensible,
            Some(cur) => {
                if spec_partial_is_empty(desc) {
                    true
                } else {
                    let cur_conf = spec_desc_configurable(cur);
                    let cur_enum = spec_desc_enumerable(cur);
                    // Step 4: non-configurable restrictions on [[Configurable]] and [[Enumerable]]
                    if !cur_conf && desc.configurable == Some(true) {
                        false
                    } else if !cur_conf && (desc.enumerable is Some) && desc.enumerable != Some(cur_enum) {
                        false
                    } else if spec_partial_is_generic(desc) {
                        // Step 5: generic descriptor needs no further validation
                        true
                    } else {
                        match cur {
                            PropertyDescriptor::Data { value: cv, writable: cw, .. } => {
                                if spec_partial_has_accessor(desc) {
                                    // Step 6: converting Data -> Accessor requires configurable
                                    cur_conf
                                } else if !cur_conf && !cw {
                                    // Step 7.a: non-configurable, non-writable Data property
                                    if desc.writable == Some(true) {
                                        false
                                    } else {
                                        match desc.value {
                                            Some(dv) => crate::types::spec_same_value(dv, cv),
                                            None => true,
                                        }
                                    }
                                } else {
                                    true
                                }
                            },
                            PropertyDescriptor::Accessor { get: cg, set: cs, .. } => {
                                if spec_partial_has_data(desc) {
                                    // Step 6: converting Accessor -> Data requires configurable
                                    cur_conf
                                } else if !cur_conf {
                                    // Step 8.a: non-configurable Accessor property
                                    let get_ok = match desc.get {
                                        Some(dg) => dg == cg,
                                        None => true,
                                    };
                                    let set_ok = match desc.set {
                                        Some(ds) => ds == cs,
                                        None => true,
                                    };
                                    get_ok && set_ok
                                } else {
                                    true
                                }
                            },
                        }
                    }
                }
            },
        }
    }
}

pub fn is_compatible_descriptor(
    extensible: bool,
    desc: PartialDescriptor,
    current: Option<PropertyDescriptor>,
) -> (ok: bool)
    ensures
        ok == spec_is_compatible_descriptor(extensible, desc, current),
{
    if !is_valid_partial_descriptor(desc) {
        return false;
    }
    match current {
        None => extensible,
        Some(cur) => {
            let has_data = matches!(desc.value, Some(_)) || matches!(desc.writable, Some(_));
            let has_acc = matches!(desc.get, Some(_)) || matches!(desc.set, Some(_));
            if !has_data && !has_acc && matches!(desc.enumerable, None) && matches!(desc.configurable, None) {
                return true;
            }
            let cur_conf = desc_configurable(cur);
            let cur_enum = desc_enumerable(cur);
            if !cur_conf {
                if let Some(true) = desc.configurable {
                    return false;
                }
                if let Some(de) = desc.enumerable {
                    if de != cur_enum {
                        return false;
                    }
                }
            }
            if !has_data && !has_acc {
                return true;
            }
            match cur {
                PropertyDescriptor::Data { value: cv, writable: cw, .. } => {
                    if has_acc {
                        cur_conf
                    } else if !cur_conf && !cw {
                        if let Some(true) = desc.writable {
                            false
                        } else if let Some(dv) = desc.value {
                            same_value(dv, cv)
                        } else {
                            true
                        }
                    } else {
                        true
                    }
                },
                PropertyDescriptor::Accessor { get: cg, set: cs, .. } => {
                    if has_data {
                        cur_conf
                    } else if !cur_conf {
                        let get_ok = match desc.get {
                            Some(dg) => opt_obj_eq(dg, cg),
                            None => true,
                        };
                        let set_ok = match desc.set {
                            Some(ds) => opt_obj_eq(ds, cs),
                            None => true,
                        };
                        get_ok && set_ok
                    } else {
                        true
                    }
                },
            }
        },
    }
}

/// Apply validated `PartialDescriptor` onto `current` per §10.1.6.3 steps 2/6/7/8/9.
pub open spec fn spec_apply_descriptor(
    desc: PartialDescriptor,
    current: Option<PropertyDescriptor>,
) -> PropertyDescriptor {
    match current {
        None => spec_complete_descriptor(desc),
        Some(cur) => {
            let enumerable = match desc.enumerable {
                Some(e) => e,
                None => spec_desc_enumerable(cur),
            };
            let configurable = match desc.configurable {
                Some(c) => c,
                None => spec_desc_configurable(cur),
            };
            if spec_partial_is_generic(desc) {
                match cur {
                    PropertyDescriptor::Data { value, writable, .. } =>
                        PropertyDescriptor::Data { value, writable, enumerable, configurable },
                    PropertyDescriptor::Accessor { get, set, .. } =>
                        PropertyDescriptor::Accessor { get, set, enumerable, configurable },
                }
            } else if spec_partial_has_accessor(desc) {
                match cur {
                    PropertyDescriptor::Accessor { get: cg, set: cs, .. } => {
                        let get = match desc.get { Some(g) => g, None => cg };
                        let set = match desc.set { Some(s) => s, None => cs };
                        PropertyDescriptor::Accessor { get, set, enumerable, configurable }
                    },
                    PropertyDescriptor::Data { .. } => {
                        let get = match desc.get { Some(g) => g, None => None };
                        let set = match desc.set { Some(s) => s, None => None };
                        PropertyDescriptor::Accessor { get, set, enumerable, configurable }
                    },
                }
            } else {
                match cur {
                    PropertyDescriptor::Data { value: cv, writable: cw, .. } => {
                        let value = match desc.value { Some(v) => v, None => cv };
                        let writable = match desc.writable { Some(w) => w, None => cw };
                        PropertyDescriptor::Data { value, writable, enumerable, configurable }
                    },
                    PropertyDescriptor::Accessor { .. } => {
                        let value = match desc.value { Some(v) => v, None => JsVal::Undefined };
                        let writable = match desc.writable { Some(w) => w, None => false };
                        PropertyDescriptor::Data { value, writable, enumerable, configurable }
                    },
                }
            }
        },
    }
}

pub fn apply_descriptor(
    desc: PartialDescriptor,
    current: Option<PropertyDescriptor>,
) -> (out: PropertyDescriptor)
    ensures
        out == spec_apply_descriptor(desc, current),
{
    match current {
        None => complete_descriptor(desc),
        Some(cur) => {
            let enumerable = match desc.enumerable {
                Some(e) => e,
                None => desc_enumerable(cur),
            };
            let configurable = match desc.configurable {
                Some(c) => c,
                None => desc_configurable(cur),
            };
            let has_data = matches!(desc.value, Some(_)) || matches!(desc.writable, Some(_));
            let has_acc = matches!(desc.get, Some(_)) || matches!(desc.set, Some(_));
            if !has_data && !has_acc {
                match cur {
                    PropertyDescriptor::Data { value, writable, .. } =>
                        PropertyDescriptor::Data { value, writable, enumerable, configurable },
                    PropertyDescriptor::Accessor { get, set, .. } =>
                        PropertyDescriptor::Accessor { get, set, enumerable, configurable },
                }
            } else if has_acc {
                match cur {
                    PropertyDescriptor::Accessor { get: cg, set: cs, .. } => {
                        let get = match desc.get { Some(g) => g, None => cg };
                        let set = match desc.set { Some(s) => s, None => cs };
                        PropertyDescriptor::Accessor { get, set, enumerable, configurable }
                    },
                    PropertyDescriptor::Data { .. } => {
                        let get = match desc.get { Some(g) => g, None => None };
                        let set = match desc.set { Some(s) => s, None => None };
                        PropertyDescriptor::Accessor { get, set, enumerable, configurable }
                    },
                }
            } else {
                match cur {
                    PropertyDescriptor::Data { value: cv, writable: cw, .. } => {
                        let value = match desc.value { Some(v) => v, None => cv };
                        let writable = match desc.writable { Some(w) => w, None => cw };
                        PropertyDescriptor::Data { value, writable, enumerable, configurable }
                    },
                    PropertyDescriptor::Accessor { .. } => {
                        let value = match desc.value { Some(v) => v, None => JsVal::Undefined };
                        let writable = match desc.writable { Some(w) => w, None => false };
                        PropertyDescriptor::Data { value, writable, enumerable, configurable }
                    },
                }
            }
        },
    }
}

// -----------------------------------------------------------------------------------------------
// §10.5 Post-Trap Validation Core & Machine-Checked §6.1.7.3 Invariant Theorems
// -----------------------------------------------------------------------------------------------

/// Raw trap return value for `getPrototypeOf` before §10.5.1 step 8 type check:
/// handler trap may return `Null`, `Object(id)`, or an invalid primitive (`InvalidPrimitive` -> `TypeError`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ProtoTrapOutput {
    Null,
    Object(ObjId),
    InvalidPrimitive,
}

/// §10.5.1 `[[GetPrototypeOf]]` post-trap validation (steps 8–13).
pub open spec fn spec_validate_get_prototype_of(
    trap_out: ProtoTrapOutput,
    target_extensible: bool,
    target_proto: Option<ObjId>,
) -> Result<Option<ObjId>, JsError> {
    let handler_proto = match trap_out {
        ProtoTrapOutput::Null => Ok(None),
        ProtoTrapOutput::Object(id) => Ok(Some(id)),
        ProtoTrapOutput::InvalidPrimitive => Err(JsError::TypeError),
    };
    match handler_proto {
        Err(e) => Err(e),
        Ok(hp) => {
            if target_extensible {
                Ok(hp)
            } else if hp == target_proto {
                Ok(hp)
            } else {
                Err(JsError::TypeError)
            }
        },
    }
}

pub fn proxy_validate_get_prototype_of(
    trap_out: ProtoTrapOutput,
    target_extensible: bool,
    target_proto: Option<ObjId>,
) -> (res: Result<Option<ObjId>, JsError>)
    ensures
        res == spec_validate_get_prototype_of(trap_out, target_extensible, target_proto),
        // §6.1.7.3 [[GetPrototypeOf]] invariant: non-extensible target forces identical prototype
        match res {
            Ok(proto) => !target_extensible ==> proto == target_proto,
            Err(e) => e == JsError::TypeError,
        },
{
    let hp = match trap_out {
        ProtoTrapOutput::Null => None,
        ProtoTrapOutput::Object(id) => Some(id),
        ProtoTrapOutput::InvalidPrimitive => return Err(JsError::TypeError),
    };
    if target_extensible {
        Ok(hp)
    } else if opt_obj_eq(hp, target_proto) {
        Ok(hp)
    } else {
        Err(JsError::TypeError)
    }
}

/// §10.5.2 `[[SetPrototypeOf]]` post-trap validation (steps 8–14).
pub open spec fn spec_validate_set_prototype_of(
    trap_bool: bool,
    new_proto: Option<ObjId>,
    target_extensible: bool,
    target_proto: Option<ObjId>,
) -> Result<bool, JsError> {
    if !trap_bool {
        Ok(false)
    } else if target_extensible {
        Ok(true)
    } else if new_proto == target_proto {
        Ok(true)
    } else {
        Err(JsError::TypeError)
    }
}

pub fn proxy_validate_set_prototype_of(
    trap_bool: bool,
    new_proto: Option<ObjId>,
    target_extensible: bool,
    target_proto: Option<ObjId>,
) -> (res: Result<bool, JsError>)
    ensures
        res == spec_validate_set_prototype_of(trap_bool, new_proto, target_extensible, target_proto),
        // §6.1.7.3 [[SetPrototypeOf]] invariant: non-extensible target cannot report changing prototype
        match res {
            Ok(true) => !target_extensible ==> new_proto == target_proto,
            Ok(false) => true,
            Err(e) => e == JsError::TypeError,
        },
{
    if !trap_bool {
        Ok(false)
    } else if target_extensible {
        Ok(true)
    } else if opt_obj_eq(new_proto, target_proto) {
        Ok(true)
    } else {
        Err(JsError::TypeError)
    }
}

/// §10.5.3 `[[IsExtensible]]` post-trap validation (steps 7–10).
pub open spec fn spec_validate_is_extensible(
    trap_bool: bool,
    target_extensible: bool,
) -> Result<bool, JsError> {
    if trap_bool == target_extensible {
        Ok(trap_bool)
    } else {
        Err(JsError::TypeError)
    }
}

pub fn proxy_validate_is_extensible(
    trap_bool: bool,
    target_extensible: bool,
) -> (res: Result<bool, JsError>)
    ensures
        res == spec_validate_is_extensible(trap_bool, target_extensible),
        // §6.1.7.3 [[IsExtensible]] invariant: Proxy must report exact same extensibility as target
        match res {
            Ok(b) => b == target_extensible,
            Err(e) => e == JsError::TypeError,
        },
{
    if trap_bool == target_extensible {
        Ok(trap_bool)
    } else {
        Err(JsError::TypeError)
    }
}

/// §10.5.4 `[[PreventExtensions]]` post-trap validation (steps 7–11).
pub open spec fn spec_validate_prevent_extensions(
    trap_bool: bool,
    target_extensible: bool,
) -> Result<bool, JsError> {
    if trap_bool && target_extensible {
        Err(JsError::TypeError)
    } else {
        Ok(trap_bool)
    }
}

pub fn proxy_validate_prevent_extensions(
    trap_bool: bool,
    target_extensible: bool,
) -> (res: Result<bool, JsError>)
    ensures
        res == spec_validate_prevent_extensions(trap_bool, target_extensible),
        // §6.1.7.3 [[PreventExtensions]] invariant: returning true requires target is non-extensible
        match res {
            Ok(true) => !target_extensible,
            Ok(false) => true,
            Err(e) => e == JsError::TypeError,
        },
{
    if trap_bool && target_extensible {
        Err(JsError::TypeError)
    } else {
        Ok(trap_bool)
    }
}

/// Raw trap return value for `getOwnPropertyDescriptor` (§10.5.5 step 8):
/// `Undefined` (`None`), valid descriptor object (`Descriptor(PartialDescriptor)`), or invalid primitive.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum OwnPropDescTrapOutput {
    Undefined,
    Descriptor(PartialDescriptor),
    InvalidPrimitive,
}

/// §10.5.5 `[[GetOwnProperty]]` post-trap validation (steps 8–18).
pub open spec fn spec_validate_get_own_property(
    trap_out: OwnPropDescTrapOutput,
    target_desc: Option<PropertyDescriptor>,
    target_extensible: bool,
) -> Result<Option<PropertyDescriptor>, JsError> {
    match trap_out {
        OwnPropDescTrapOutput::InvalidPrimitive => Err(JsError::TypeError),
        OwnPropDescTrapOutput::Undefined => {
            match target_desc {
                None => Ok(None),
                Some(td) => {
                    if !spec_desc_configurable(td) || !target_extensible {
                        Err(JsError::TypeError)
                    } else {
                        Ok(None)
                    }
                },
            }
        },
        OwnPropDescTrapOutput::Descriptor(raw_desc) => {
            if !spec_valid_partial_descriptor(raw_desc) {
                Err(JsError::TypeError)
            } else {
                let result_desc = spec_complete_descriptor(raw_desc);
                let compat_partial = spec_partial_from_complete(result_desc);
                if !spec_is_compatible_descriptor(target_extensible, compat_partial, target_desc) {
                    Err(JsError::TypeError)
                } else if !spec_desc_configurable(result_desc) {
                    match target_desc {
                        None => Err(JsError::TypeError),
                        Some(td) => {
                            if spec_desc_configurable(td) {
                                Err(JsError::TypeError)
                            } else {
                                // §10.5.5 step 17.b: if resultDesc has [[Writable]]: false, targetDesc cannot have [[Writable]]: true
                                match (result_desc, td) {
                                    (
                                        PropertyDescriptor::Data { writable: false, .. },
                                        PropertyDescriptor::Data { writable: true, .. },
                                    ) => Err(JsError::TypeError),
                                    _ => Ok(Some(result_desc)),
                                }
                            }
                        },
                    }
                } else {
                    Ok(Some(result_desc))
                }
            }
        },
    }
}

pub fn proxy_validate_get_own_property(
    trap_out: OwnPropDescTrapOutput,
    target_desc: Option<PropertyDescriptor>,
    target_extensible: bool,
) -> (res: Result<Option<PropertyDescriptor>, JsError>)
    ensures
        res == spec_validate_get_own_property(trap_out, target_desc, target_extensible),
        // §6.1.7.3 [[GetOwnProperty]] invariants:
        match res {
            Ok(None) => {
                // (1) Cannot hide a non-configurable target property
                &&& match target_desc {
                    Some(td) => spec_desc_configurable(td) && target_extensible,
                    None => true,
                }
            },
            Ok(Some(rd)) => {
                // (2) Cannot fabricate a property on a non-extensible target when absent on target
                &&& ((target_desc is None) ==> target_extensible)
                // (3) Cannot report a property as non-configurable unless it exists as non-configurable on target
                &&& (!spec_desc_configurable(rd) ==> match target_desc {
                    Some(td) => !spec_desc_configurable(td),
                    None => false,
                })
                // (4) Cannot report a non-configurable writable target data property as non-writable
                &&& match (rd, target_desc) {
                    (
                        PropertyDescriptor::Data { configurable: false, writable: false, .. },
                        Some(PropertyDescriptor::Data { writable: true, .. }),
                    ) => false,
                    _ => true,
                }
                // (5) Non-configurable non-writable target data property forces identical SameValue
                &&& match target_desc {
                    Some(PropertyDescriptor::Data { value: tv, writable: false, configurable: false, enumerable: te }) => {
                        match rd {
                            PropertyDescriptor::Data { value: rv, writable: false, configurable: false, enumerable: re } =>
                                crate::types::spec_same_value(rv, tv) && re == te,
                            _ => false,
                        }
                    },
                    _ => true,
                }
            },
            Err(e) => e == JsError::TypeError,
        },
{
    match trap_out {
        OwnPropDescTrapOutput::InvalidPrimitive => Err(JsError::TypeError),
        OwnPropDescTrapOutput::Undefined => {
            match target_desc {
                None => Ok(None),
                Some(td) => {
                    if !desc_configurable(td) || !target_extensible {
                        Err(JsError::TypeError)
                    } else {
                        Ok(None)
                    }
                },
            }
        },
        OwnPropDescTrapOutput::Descriptor(raw_desc) => {
            if !is_valid_partial_descriptor(raw_desc) {
                return Err(JsError::TypeError);
            }
            let result_desc = complete_descriptor(raw_desc);
            let compat_partial = PartialDescriptor::from_complete(result_desc);
            if !is_compatible_descriptor(target_extensible, compat_partial, target_desc) {
                return Err(JsError::TypeError);
            }
            if !desc_configurable(result_desc) {
                match target_desc {
                    None => return Err(JsError::TypeError),
                    Some(td) => {
                        if desc_configurable(td) {
                            return Err(JsError::TypeError);
                        }
                        if let (
                            PropertyDescriptor::Data { writable: false, .. },
                            PropertyDescriptor::Data { writable: true, .. },
                        ) = (result_desc, td) {
                            return Err(JsError::TypeError);
                        }
                    },
                }
            }
            Ok(Some(result_desc))
        },
    }
}

/// §10.5.6 `[[DefineOwnProperty]]` post-trap validation (steps 11–17).
pub open spec fn spec_validate_define_own_property(
    trap_bool: bool,
    desc: PartialDescriptor,
    target_desc: Option<PropertyDescriptor>,
    target_extensible: bool,
) -> Result<bool, JsError> {
    if !spec_valid_partial_descriptor(desc) {
        Err(JsError::TypeError)
    } else if !trap_bool {
        Ok(false)
    } else {
        let setting_config_false = desc.configurable == Some(false);
        match target_desc {
            None => {
                if !target_extensible || setting_config_false {
                    Err(JsError::TypeError)
                } else {
                    Ok(true)
                }
            },
            Some(td) => {
                if !spec_is_compatible_descriptor(target_extensible, desc, Some(td)) {
                    Err(JsError::TypeError)
                } else if setting_config_false && spec_desc_configurable(td) {
                    Err(JsError::TypeError)
                } else {
                    // §10.5.6 step 16.c: non-configurable writable target data property cannot be reported set to writable: false
                    match td {
                        PropertyDescriptor::Data { configurable: false, writable: true, .. } => {
                            if desc.writable == Some(false) {
                                Err(JsError::TypeError)
                            } else {
                                Ok(true)
                            }
                        },
                        _ => Ok(true),
                    }
                }
            },
        }
    }
}

pub fn proxy_validate_define_own_property(
    trap_bool: bool,
    desc: PartialDescriptor,
    target_desc: Option<PropertyDescriptor>,
    target_extensible: bool,
) -> (res: Result<bool, JsError>)
    ensures
        res == spec_validate_define_own_property(trap_bool, desc, target_desc, target_extensible),
        // §6.1.7.3 [[DefineOwnProperty]] invariants:
        match res {
            Ok(true) => {
                &&& spec_is_compatible_descriptor(target_extensible, desc, target_desc)
                &&& ((target_desc is None) ==> target_extensible && desc.configurable != Some(false))
                &&& ((desc.configurable == Some(false)) ==> match target_desc {
                    Some(td) => !spec_desc_configurable(td),
                    None => false,
                })
                &&& match target_desc {
                    Some(PropertyDescriptor::Data { configurable: false, writable: true, .. }) =>
                        desc.writable != Some(false),
                    _ => true,
                }
            },
            Ok(false) => !trap_bool,
            Err(e) => e == JsError::TypeError,
        },
{
    if !is_valid_partial_descriptor(desc) {
        return Err(JsError::TypeError);
    }
    if !trap_bool {
        return Ok(false);
    }
    let setting_config_false = matches!(desc.configurable, Some(false));
    match target_desc {
        None => {
            if !target_extensible || setting_config_false {
                Err(JsError::TypeError)
            } else {
                Ok(true)
            }
        },
        Some(td) => {
            if !is_compatible_descriptor(target_extensible, desc, Some(td)) {
                return Err(JsError::TypeError);
            }
            if setting_config_false && desc_configurable(td) {
                return Err(JsError::TypeError);
            }
            if let PropertyDescriptor::Data { configurable: false, writable: true, .. } = td {
                if matches!(desc.writable, Some(false)) {
                    return Err(JsError::TypeError);
                }
            }
            Ok(true)
        },
    }
}

/// §10.5.7 `[[HasProperty]]` post-trap validation (steps 8–10).
pub open spec fn spec_validate_has_property(
    trap_bool: bool,
    target_desc: Option<PropertyDescriptor>,
    target_extensible: bool,
) -> Result<bool, JsError> {
    if !trap_bool {
        match target_desc {
            None => Ok(false),
            Some(td) => {
                if !spec_desc_configurable(td) || !target_extensible {
                    Err(JsError::TypeError)
                } else {
                    Ok(false)
                }
            },
        }
    } else {
        Ok(true)
    }
}

pub fn proxy_validate_has_property(
    trap_bool: bool,
    target_desc: Option<PropertyDescriptor>,
    target_extensible: bool,
) -> (res: Result<bool, JsError>)
    ensures
        res == spec_validate_has_property(trap_bool, target_desc, target_extensible),
        // §6.1.7.3 [[HasProperty]] invariant: cannot hide non-configurable or non-extensible own property
        match res {
            Ok(false) => match target_desc {
                None => true,
                Some(td) => spec_desc_configurable(td) && target_extensible,
            },
            Ok(true) => true,
            Err(e) => e == JsError::TypeError,
        },
{
    if !trap_bool {
        match target_desc {
            None => Ok(false),
            Some(td) => {
                if !desc_configurable(td) || !target_extensible {
                    Err(JsError::TypeError)
                } else {
                    Ok(false)
                }
            },
        }
    } else {
        Ok(true)
    }
}

/// §10.5.8 `[[Get]]` post-trap validation (steps 8–11).
pub open spec fn spec_validate_get(
    trap_val: JsVal,
    target_desc: Option<PropertyDescriptor>,
) -> Result<JsVal, JsError> {
    match target_desc {
        None => Ok(trap_val),
        Some(PropertyDescriptor::Data { value, writable, configurable, .. }) => {
            if !configurable && !writable && !crate::types::spec_same_value(trap_val, value) {
                Err(JsError::TypeError)
            } else {
                Ok(trap_val)
            }
        },
        Some(PropertyDescriptor::Accessor { get, configurable, .. }) => {
            if !configurable && (get is None) && trap_val != JsVal::Undefined {
                Err(JsError::TypeError)
            } else {
                Ok(trap_val)
            }
        },
    }
}

pub fn proxy_validate_get(
    trap_val: JsVal,
    target_desc: Option<PropertyDescriptor>,
) -> (res: Result<JsVal, JsError>)
    ensures
        res == spec_validate_get(trap_val, target_desc),
        // §6.1.7.3 [[Get]] invariants:
        match res {
            Ok(v) => {
                &&& match target_desc {
                    Some(PropertyDescriptor::Data { value: tv, writable: false, configurable: false, .. }) =>
                        crate::types::spec_same_value(v, tv),
                    Some(PropertyDescriptor::Accessor { get: None, configurable: false, .. }) =>
                        v == JsVal::Undefined,
                    _ => true,
                }
            },
            Err(e) => e == JsError::TypeError,
        },
{
    match target_desc {
        None => Ok(trap_val),
        Some(PropertyDescriptor::Data { value, writable, configurable, .. }) => {
            if !configurable && !writable && !same_value(trap_val, value) {
                Err(JsError::TypeError)
            } else {
                Ok(trap_val)
            }
        },
        Some(PropertyDescriptor::Accessor { get, configurable, .. }) => {
            if !configurable && matches!(get, None) && !matches!(trap_val, JsVal::Undefined) {
                Err(JsError::TypeError)
            } else {
                Ok(trap_val)
            }
        },
    }
}

/// §10.5.9 `[[Set]]` post-trap validation (steps 9–12).
pub open spec fn spec_validate_set(
    trap_bool: bool,
    set_val: JsVal,
    target_desc: Option<PropertyDescriptor>,
) -> Result<bool, JsError> {
    if !trap_bool {
        Ok(false)
    } else {
        match target_desc {
            None => Ok(true),
            Some(PropertyDescriptor::Data { value, writable, configurable, .. }) => {
                if !configurable && !writable && !crate::types::spec_same_value(set_val, value) {
                    Err(JsError::TypeError)
                } else {
                    Ok(true)
                }
            },
            Some(PropertyDescriptor::Accessor { set, configurable, .. }) => {
                if !configurable && (set is None) {
                    Err(JsError::TypeError)
                } else {
                    Ok(true)
                }
            },
        }
    }
}

pub fn proxy_validate_set(
    trap_bool: bool,
    set_val: JsVal,
    target_desc: Option<PropertyDescriptor>,
) -> (res: Result<bool, JsError>)
    ensures
        res == spec_validate_set(trap_bool, set_val, target_desc),
        // §6.1.7.3 [[Set]] invariants:
        match res {
            Ok(true) => {
                &&& match target_desc {
                    Some(PropertyDescriptor::Data { value: tv, writable: false, configurable: false, .. }) =>
                        crate::types::spec_same_value(set_val, tv),
                    Some(PropertyDescriptor::Accessor { set: None, configurable: false, .. }) =>
                        false,
                    _ => true,
                }
            },
            Ok(false) => !trap_bool,
            Err(e) => e == JsError::TypeError,
        },
{
    if !trap_bool {
        return Ok(false);
    }
    match target_desc {
        None => Ok(true),
        Some(PropertyDescriptor::Data { value, writable, configurable, .. }) => {
            if !configurable && !writable && !same_value(set_val, value) {
                Err(JsError::TypeError)
            } else {
                Ok(true)
            }
        },
        Some(PropertyDescriptor::Accessor { set, configurable, .. }) => {
            if !configurable && matches!(set, None) {
                Err(JsError::TypeError)
            } else {
                Ok(true)
            }
        },
    }
}

/// §10.5.10 `[[Delete]]` post-trap validation (steps 8–12).
pub open spec fn spec_validate_delete(
    trap_bool: bool,
    target_desc: Option<PropertyDescriptor>,
    target_extensible: bool,
) -> Result<bool, JsError> {
    if !trap_bool {
        Ok(false)
    } else {
        match target_desc {
            None => Ok(true),
            Some(td) => {
                if !spec_desc_configurable(td) || !target_extensible {
                    Err(JsError::TypeError)
                } else {
                    Ok(true)
                }
            },
        }
    }
}

pub fn proxy_validate_delete(
    trap_bool: bool,
    target_desc: Option<PropertyDescriptor>,
    target_extensible: bool,
) -> (res: Result<bool, JsError>)
    ensures
        res == spec_validate_delete(trap_bool, target_desc, target_extensible),
        // §6.1.7.3 [[Delete]] invariant: cannot report true for non-configurable target property
        // or for an existing own property on a non-extensible target!
        match res {
            Ok(true) => match target_desc {
                None => true,
                Some(td) => spec_desc_configurable(td) && target_extensible,
            },
            Ok(false) => !trap_bool,
            Err(e) => e == JsError::TypeError,
        },
{
    if !trap_bool {
        Ok(false)
    } else {
        match target_desc {
            None => Ok(true),
            Some(td) => {
                if !desc_configurable(td) || !target_extensible {
                    Err(JsError::TypeError)
                } else {
                    Ok(true)
                }
            },
        }
    }
}

// -----------------------------------------------------------------------------------------------
// §10.5.11 `[[OwnPropertyKeys]]` Post-Trap Validation & Duplicate/Containment Proofs
// -----------------------------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct TargetKeyInfo {
    pub key: PropKey,
    pub configurable: bool,
}

pub open spec fn spec_key_in_seq(keys: Seq<PropKey>, k: PropKey) -> bool {
    exists|i: int| 0 <= i < keys.len() && #[trigger] keys[i] == k
}

pub open spec fn spec_no_duplicate_keys(keys: Seq<PropKey>) -> bool {
    forall|i: int, j: int| 0 <= i < j < keys.len() ==> keys[i] != keys[j]
}

pub open spec fn spec_in_target_keys(target_keys: Seq<TargetKeyInfo>, k: PropKey) -> bool {
    exists|i: int| 0 <= i < target_keys.len() && (#[trigger] target_keys[i]).key == k
}

pub fn key_in_slice(keys: &[PropKey], k: PropKey) -> (found: bool)
    ensures
        found == spec_key_in_seq(keys@, k),
{
    let n = keys.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == keys@.len(),
            forall|j: int| 0 <= j < i as int ==> keys@[j] != k,
        decreases n - i,
    {
        if prop_key_eq(keys[i], k) {
            return true;
        }
        i += 1;
    }
    false
}

pub fn check_no_duplicate_keys(keys: &[PropKey]) -> (unique: bool)
    ensures
        unique == spec_no_duplicate_keys(keys@),
{
    let n = keys.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == keys@.len(),
            forall|a: int, b: int| 0 <= a < i as int && a < b < n as int ==> keys@[a] != keys@[b],
        decreases n - i,
    {
        let mut j: usize = i + 1;
        while j < n
            invariant
                i < j <= n,
                n == keys@.len(),
                forall|a: int, b: int| 0 <= a < i as int && a < b < n as int ==> keys@[a] != keys@[b],
                forall|b: int| (i as int) < b < j as int ==> keys@[i as int] != keys@[b],
            decreases n - j,
        {
            if prop_key_eq(keys[i], keys[j]) {
                return false;
            }
            j += 1;
        }
        i += 1;
    }
    true
}

pub fn key_in_target_info(target_keys: &[TargetKeyInfo], k: PropKey) -> (found: bool)
    ensures
        found == spec_in_target_keys(target_keys@, k),
{
    let n = target_keys.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == target_keys@.len(),
            forall|j: int| 0 <= j < i as int ==> (#[trigger] target_keys@[j]).key != k,
        decreases n - i,
    {
        if prop_key_eq(target_keys[i].key, k) {
            proof {
                assert(target_keys@[i as int].key == k);
            }
            return true;
        }
        i += 1;
    }
    false
}

pub fn clone_prop_keys(keys: &[PropKey]) -> (out: Vec<PropKey>)
    ensures
        out@ == keys@,
{
    let n = keys.len();
    let mut out: Vec<PropKey> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == keys@.len(),
            out@.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> out@[j] == keys@[j],
        decreases n - i,
    {
        out.push(keys[i]);
        i += 1;
    }
    proof {
        assert(out@ =~= keys@);
    }
    out
}

/// §10.5.11 `[[OwnPropertyKeys]]` post-trap validation (steps 8–23).
pub fn proxy_validate_own_property_keys(
    trap_is_object_list: bool,
    trap_keys: &[PropKey],
    target_keys: &[TargetKeyInfo],
    target_extensible: bool,
) -> (res: Result<Vec<PropKey>, JsError>)
    ensures
        // §6.1.7.3 [[OwnPropertyKeys]] invariants:
        match res {
            Ok(out) => {
                &&& trap_is_object_list
                &&& out@ == trap_keys@
                // (1) Returned list never contains duplicate keys (§10.5.11 step 9)
                &&& spec_no_duplicate_keys(out@)
                // (2) Every non-configurable own key of target MUST be present (§10.5.11 step 17)
                &&& forall|ti: int| 0 <= ti < target_keys@.len() && !(#[trigger] target_keys@[ti]).configurable
                    ==> spec_key_in_seq(out@, target_keys@[ti].key)
                // (3) If target is non-extensible, ALL own keys of target are present AND no extra keys exist (§10.5.11 steps 21–22)
                &&& (!target_extensible ==> (
                    (forall|ti: int| 0 <= ti < target_keys@.len()
                        ==> spec_key_in_seq(out@, (#[trigger] target_keys@[ti]).key))
                    && (forall|oi: int| 0 <= oi < out@.len()
                        ==> spec_in_target_keys(target_keys@, #[trigger] out@[oi]))
                ))
            },
            Err(e) => e == JsError::TypeError,
        },
{
    if !trap_is_object_list {
        return Err(JsError::TypeError);
    }
    // Step 9: If trapResult contains any duplicate entries, throw a TypeError exception.
    if !check_no_duplicate_keys(trap_keys) {
        return Err(JsError::TypeError);
    }
    // Steps 17–19: Every non-configurable target key must appear in trapResult.
    let tn = target_keys.len();
    let mut ti: usize = 0;
    while ti < tn
        invariant
            ti <= tn,
            tn == target_keys@.len(),
            forall|k: int| 0 <= k < ti as int && !(#[trigger] target_keys@[k]).configurable
                ==> spec_key_in_seq(trap_keys@, target_keys@[k].key),
        decreases tn - ti,
    {
        let info = target_keys[ti];
        if !info.configurable {
            if !key_in_slice(trap_keys, info.key) {
                return Err(JsError::TypeError);
            }
        }
        ti += 1;
    }

    // Step 20: If extensibleTarget is true, return trapResult.
    if target_extensible {
        return Ok(clone_prop_keys(trap_keys));
    }

    // Step 21: Target is non-extensible — every configurable target key must ALSO appear in trapResult.
    let mut ci: usize = 0;
    while ci < tn
        invariant
            ci <= tn,
            tn == target_keys@.len(),
            forall|k: int| 0 <= k < tn as int && !(#[trigger] target_keys@[k]).configurable
                ==> spec_key_in_seq(trap_keys@, target_keys@[k].key),
            forall|k: int| 0 <= k < ci as int
                ==> spec_key_in_seq(trap_keys@, (#[trigger] target_keys@[k]).key),
        decreases tn - ci,
    {
        let info = target_keys[ci];
        if !key_in_slice(trap_keys, info.key) {
            return Err(JsError::TypeError);
        }
        ci += 1;
    }

    // Step 22: No extra unchecked keys may appear in trapResult when target is non-extensible.
    let rn = trap_keys.len();
    let mut ri: usize = 0;
    while ri < rn
        invariant
            ri <= rn,
            rn == trap_keys@.len(),
            forall|k: int| 0 <= k < ri as int
                ==> spec_in_target_keys(target_keys@, #[trigger] trap_keys@[k]),
        decreases rn - ri,
    {
        if !key_in_target_info(target_keys, trap_keys[ri]) {
            return Err(JsError::TypeError);
        }
        ri += 1;
    }

    Ok(clone_prop_keys(trap_keys))
}

// -----------------------------------------------------------------------------------------------
// ObjectStore: Ordinary Objects, Revocable Proxies, Nested Proxies, and Reflect.* (§28.1)
// -----------------------------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct PropEntry {
    pub key: PropKey,
    pub desc: PropertyDescriptor,
}

/// Configurable trap behavior on a Proxy handler object (supports missing traps that forward to
/// `target`, non-callable traps, throwing traps, mutating traps, and arbitrary/malicious outputs).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum BoolTrapStub {
    Missing,
    NotCallable,
    Throw(JsVal),
    Return(bool),
    /// Legitimate `preventExtensions` / `deleteProperty` / `defineProperty` handler that first
    /// applies the operation on `target` and then returns `bool`.
    MutateTargetAndReturn(bool),
    /// Handler calls `Object.preventExtensions(target)` inside the trap body before returning `bool`.
    SealTargetAndReturn(bool),
    /// Handler calls `Object.setPrototypeOf(target, proto)` and `Object.preventExtensions(target)`
    /// inside `setPrototypeOf` before returning `ret`.
    SetTargetProtoSealAndReturn { proto: Option<ObjId>, ret: bool },
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ProtoTrapStub {
    Missing,
    NotCallable,
    Throw(JsVal),
    Return(ProtoTrapOutput),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum OwnPropDescTrapStub {
    Missing,
    NotCallable,
    Throw(JsVal),
    Return(OwnPropDescTrapOutput),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ValTrapStub {
    Missing,
    NotCallable,
    Throw(JsVal),
    Return(JsVal),
}

pub enum OwnKeysTrapStub {
    Missing,
    NotCallable,
    Throw(JsVal),
    InvalidReturnType,
    ReturnKeys(Vec<PropKey>),
}

pub struct HandlerTraps {
    pub get_prototype_of: ProtoTrapStub,
    pub set_prototype_of: BoolTrapStub,
    pub is_extensible: BoolTrapStub,
    pub prevent_extensions: BoolTrapStub,
    pub get_own_property_descriptor: OwnPropDescTrapStub,
    pub define_property: BoolTrapStub,
    pub has: BoolTrapStub,
    pub get: ValTrapStub,
    pub set: BoolTrapStub,
    pub delete_property: BoolTrapStub,
    pub own_keys: OwnKeysTrapStub,
}

impl HandlerTraps {
    pub fn empty() -> Self {
        HandlerTraps {
            get_prototype_of: ProtoTrapStub::Missing,
            set_prototype_of: BoolTrapStub::Missing,
            is_extensible: BoolTrapStub::Missing,
            prevent_extensions: BoolTrapStub::Missing,
            get_own_property_descriptor: OwnPropDescTrapStub::Missing,
            define_property: BoolTrapStub::Missing,
            has: BoolTrapStub::Missing,
            get: ValTrapStub::Missing,
            set: BoolTrapStub::Missing,
            delete_property: BoolTrapStub::Missing,
            own_keys: OwnKeysTrapStub::Missing,
        }
    }
}

pub struct OrdinaryObject {
    pub prototype: Option<ObjId>,
    pub extensible: bool,
    pub props: Vec<PropEntry>,
    pub traps: HandlerTraps,
}

/// Proxy exotic object state (§10.5): `[[ProxyTarget]]` and `[[ProxyHandler]]`.
/// When revoked, BOTH `target` and `handler` are cleared to `None`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct ProxyRecord {
    pub target: Option<ObjId>,
    pub handler: Option<ObjId>,
}

/// Return record of `Proxy.revocable(target, handler)` (§28.2.2.1).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct RevocableProxy {
    pub proxy_id: ObjId,
    pub revoker_id: ObjId,
}

pub enum ObjectKind {
    Ordinary(OrdinaryObject),
    Proxy(ProxyRecord),
}

pub struct ObjectStore {
    pub objects: Vec<ObjectKind>,
}

pub open spec fn spec_entries_unique(props: Seq<PropEntry>) -> bool {
    forall|i: int, j: int| 0 <= i < j < props.len() ==> props[i].key != props[j].key
}

pub open spec fn spec_proxy_slot_wf(len: nat, p: ProxyRecord) -> bool {
    match (p.target, p.handler) {
        (None, None) => true,
        (Some(t), Some(h)) => (t as nat) < len && (h as nat) < len,
        _ => false,
    }
}

pub open spec fn spec_obj_kind_wf(len: nat, kind: &ObjectKind) -> bool {
    match kind {
        ObjectKind::Ordinary(ord) => {
            &&& match ord.prototype {
                None => true,
                Some(pid) => (pid as nat) < len,
            }
            &&& spec_entries_unique(ord.props@)
        },
        ObjectKind::Proxy(p) => spec_proxy_slot_wf(len, *p),
    }
}

impl ObjectStore {
    pub open spec fn wf(&self) -> bool {
        &&& self.objects@.len() < usize::MAX as int
        &&& forall|i: int| 0 <= i < self.objects@.len()
            ==> spec_obj_kind_wf(self.objects@.len(), #[trigger] &self.objects@[i])
    }

    pub open spec fn spec_is_revoked_proxy(&self, id: ObjId) -> bool {
        (id as int) < self.objects@.len()
            && match &self.objects@[id as int] {
                ObjectKind::Proxy(p) => (p.target is None) && (p.handler is None),
                ObjectKind::Ordinary(_) => false,
            }
    }

    /// When `obj_id` is a non-revoked `Proxy` directly wrapping an `OrdinaryObject` target,
    /// exposes that target for end-to-end stateful §6.1.7.3 postconditions.
    pub open spec fn spec_proxy_ordinary_target(&self, obj_id: ObjId) -> Option<&OrdinaryObject> {
        if (obj_id as int) < self.objects@.len() {
            match &self.objects@[obj_id as int] {
                ObjectKind::Proxy(ProxyRecord { target: Some(tid), handler: Some(_) }) => {
                    if (tid as int) < self.objects@.len() {
                        match &self.objects@[tid as int] {
                            ObjectKind::Ordinary(t_ord) => Some(t_ord),
                            ObjectKind::Proxy(_) => None,
                        }
                    } else {
                        None
                    }
                },
                _ => None,
            }
        } else {
            None
        }
    }

    pub fn new() -> (s: Self)
        ensures
            s.wf(),
            s.objects@.len() == 0,
    {
        ObjectStore { objects: Vec::new() }
    }

    pub fn alloc_ordinary(&mut self, prototype: Option<ObjId>, extensible: bool) -> (res: Result<ObjId, JsError>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            match res {
                Ok(id) => {
                    &&& (id as int) == old(self).objects@.len()
                    &&& final(self).objects@.len() == old(self).objects@.len() + 1
                    &&& forall|k: int| 0 <= k < old(self).objects@.len()
                        ==> final(self).objects@[k] == old(self).objects@[k]
                },
                Err(_) => final(self).objects@ == old(self).objects@,
            },
    {
        if let Some(pid) = prototype {
            if pid >= self.objects.len() {
                return Err(JsError::RangeError);
            }
        }
        if self.objects.len() >= usize::MAX - 1 {
            return Err(JsError::QuotaExceeded);
        }
        let id = self.objects.len();
        let ord = OrdinaryObject {
            prototype,
            extensible,
            props: Vec::new(),
            traps: HandlerTraps::empty(),
        };
        let ghost old_objs = self.objects@;
        self.objects.push(ObjectKind::Ordinary(ord));
        proof {
            assert forall|i: int| 0 <= i < self.objects@.len()
                implies spec_obj_kind_wf(self.objects@.len(), #[trigger] &self.objects@[i])
            by {
                if i < old_objs.len() as int {
                    assert(&self.objects@[i] == &old_objs[i]);
                    assert(spec_obj_kind_wf(old_objs.len(), &old_objs[i]));
                }
            };
        }
        Ok(id)
    }

    pub fn set_handler_traps(&mut self, handler_id: ObjId, traps: HandlerTraps) -> (res: Result<(), JsError>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).objects@.len() == old(self).objects@.len(),
            forall|k: int| 0 <= k < final(self).objects@.len() && k != handler_id as int
                ==> final(self).objects@[k] == old(self).objects@[k],
    {
        if handler_id >= self.objects.len() {
            return Err(JsError::RangeError);
        }
        let ghost old_objs = self.objects@;
        match &mut self.objects[handler_id] {
            ObjectKind::Ordinary(ord) => {
                ord.traps = traps;
                proof {
                    assert forall|i: int| 0 <= i < self.objects@.len()
                        implies spec_obj_kind_wf(self.objects@.len(), #[trigger] &self.objects@[i])
                    by {
                        if i != handler_id as int {
                            assert(&self.objects@[i] == &old_objs[i]);
                        }
                        assert(spec_obj_kind_wf(old_objs.len(), &old_objs[i]));
                    };
                }
                Ok(())
            },
            ObjectKind::Proxy(_) => Err(JsError::TypeError),
        }
    }

    /// ECMA-262 §10.5.14 `ProxyCreate(target, handler)`.
    pub fn proxy_create(&mut self, target: JsVal, handler: JsVal) -> (res: Result<ObjId, JsError>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            match res {
                Ok(pid) => {
                    &&& match (target, handler) {
                        (JsVal::Object(tid), JsVal::Object(hid)) => {
                            &&& (tid as int) < old(self).objects@.len()
                            &&& (hid as int) < old(self).objects@.len()
                            &&& (pid as int) == old(self).objects@.len()
                            &&& final(self).objects@.len() == old(self).objects@.len() + 1
                            &&& final(self).objects@[pid as int] == ObjectKind::Proxy(ProxyRecord {
                                target: Some(tid),
                                handler: Some(hid),
                            })
                        },
                        _ => false,
                    }
                    &&& forall|k: int| 0 <= k < old(self).objects@.len()
                        ==> final(self).objects@[k] == old(self).objects@[k]
                },
                Err(_) => final(self).objects@ == old(self).objects@,
            },
    {
        let tid = match target {
            JsVal::Object(id) => id,
            _ => return Err(JsError::TypeError),
        };
        let hid = match handler {
            JsVal::Object(id) => id,
            _ => return Err(JsError::TypeError),
        };
        if tid >= self.objects.len() || hid >= self.objects.len() {
            return Err(JsError::TypeError);
        }
        if self.objects.len() >= usize::MAX - 1 {
            return Err(JsError::QuotaExceeded);
        }
        let pid = self.objects.len();
        let ghost old_objs = self.objects@;
        self.objects.push(ObjectKind::Proxy(ProxyRecord {
            target: Some(tid),
            handler: Some(hid),
        }));
        proof {
            assert forall|i: int| 0 <= i < self.objects@.len()
                implies spec_obj_kind_wf(self.objects@.len(), #[trigger] &self.objects@[i])
            by {
                if i < old_objs.len() as int {
                    assert(&self.objects@[i] == &old_objs[i]);
                    assert(spec_obj_kind_wf(old_objs.len(), &old_objs[i]));
                }
            };
        }
        Ok(pid)
    }

    /// ECMA-262 §28.2.2.1 `Proxy.revocable(target, handler)`.
    pub fn proxy_revocable(&mut self, target: JsVal, handler: JsVal) -> (res: Result<RevocableProxy, JsError>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            match res {
                Ok(rv) => {
                    &&& (rv.proxy_id as int) < final(self).objects@.len()
                    &&& (rv.revoker_id as int) < final(self).objects@.len()
                    &&& !final(self).spec_is_revoked_proxy(rv.proxy_id)
                },
                Err(_) => true,
            },
    {
        if self.objects.len() >= usize::MAX - 2 {
            return Err(JsError::QuotaExceeded);
        }
        let proxy_id = self.proxy_create(target, handler)?;
        let revoker_id = self.alloc_ordinary(None, true)?;
        Ok(RevocableProxy { proxy_id, revoker_id })
    }

    /// ECMA-262 §28.2.2.1.1 Proxy Revocation Function:
    /// Clears BOTH `[[ProxyTarget]]` and `[[ProxyHandler]]` to `None` and returns `Undefined`
    /// (subsequent calls are idempotent no-ops returning `Undefined`).
    pub fn revoke_proxy(&mut self, proxy_id: ObjId) -> (res: Result<JsVal, JsError>)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).objects@.len() == old(self).objects@.len(),
            match res {
                Ok(v) => {
                    &&& v == JsVal::Undefined
                    &&& final(self).spec_is_revoked_proxy(proxy_id)
                    &&& final(self).objects@[proxy_id as int] == ObjectKind::Proxy(ProxyRecord {
                        target: None,
                        handler: None,
                    })
                    &&& forall|k: int| 0 <= k < final(self).objects@.len() && k != proxy_id as int
                        ==> final(self).objects@[k] == old(self).objects@[k]
                },
                Err(_) => final(self).objects@ == old(self).objects@,
            },
    {
        if proxy_id >= self.objects.len() {
            return Err(JsError::RangeError);
        }
        match self.objects[proxy_id] {
            ObjectKind::Proxy(_) => {
                let ghost old_objs = self.objects@;
                self.objects.set(proxy_id, ObjectKind::Proxy(ProxyRecord {
                    target: None,
                    handler: None,
                }));
                proof {
                    assert forall|i: int| 0 <= i < self.objects@.len()
                        implies spec_obj_kind_wf(self.objects@.len(), #[trigger] &self.objects@[i])
                    by {
                        if i != proxy_id as int {
                            assert(&self.objects@[i] == &old_objs[i]);
                            assert(spec_obj_kind_wf(old_objs.len(), &old_objs[i]));
                        }
                    };
                }
                Ok(JsVal::Undefined)
            },
            ObjectKind::Ordinary(_) => Err(JsError::TypeError),
        }
    }

    /// §10.5.13 `ValidateNonRevokedProxy(proxy)`: returns `(target, handler)` or throws `TypeError`.
    pub fn validate_non_revoked_proxy(&self, proxy_id: ObjId) -> (res: Result<(ObjId, ObjId), JsError>)
        requires
            self.wf(),
            (proxy_id as int) < self.objects@.len(),
        ensures
            match res {
                Ok((tid, hid)) => {
                    &&& !self.spec_is_revoked_proxy(proxy_id)
                    &&& (tid as int) < self.objects@.len()
                    &&& (hid as int) < self.objects@.len()
                    &&& self.objects@[proxy_id as int] == ObjectKind::Proxy(ProxyRecord {
                        target: Some(tid),
                        handler: Some(hid),
                    })
                },
                Err(e) => e == JsError::TypeError,
            },
            self.spec_is_revoked_proxy(proxy_id) ==> res == Err(JsError::TypeError),
    {
        proof {
            assert(spec_obj_kind_wf(self.objects@.len(), &self.objects@[proxy_id as int]));
        }
        match &self.objects[proxy_id] {
            ObjectKind::Proxy(ProxyRecord { target: Some(t), handler: Some(h) }) => Ok((*t, *h)),
            _ => Err(JsError::TypeError),
        }
    }
}

// -----------------------------------------------------------------------------------------------
// Ordinary + Proxy Essential Internal Methods (§10.1 & §10.5) & Reflect.* (§28.1)
// -----------------------------------------------------------------------------------------------

pub open spec fn spec_find_prop_from(
    props: Seq<PropEntry>,
    key: PropKey,
    idx: int,
) -> Option<PropertyDescriptor>
    decreases props.len() - idx,
{
    if idx < 0 || idx >= props.len() {
        None
    } else if props[idx].key == key {
        Some(props[idx].desc)
    } else {
        spec_find_prop_from(props, key, idx + 1)
    }
}

pub open spec fn spec_ordinary_own_prop(ord: &OrdinaryObject, key: PropKey) -> Option<PropertyDescriptor> {
    spec_find_prop_from(ord.props@, key, 0)
}

proof fn lemma_find_prop_none_when_absent(props: Seq<PropEntry>, key: PropKey, idx: int)
    requires
        0 <= idx <= props.len(),
        forall|k: int| idx <= k < props.len() ==> (#[trigger] props[k]).key != key,
    ensures
        spec_find_prop_from(props, key, idx) is None,
    decreases props.len() - idx,
{
    if idx < props.len() {
        assert(props[idx].key != key);
        lemma_find_prop_none_when_absent(props, key, idx + 1);
    }
}

fn find_prop_index(props: &Vec<PropEntry>, key: PropKey) -> (res: Option<usize>)
    ensures
        match res {
            Some(idx) => {
                &&& (idx as int) < props@.len()
                &&& props@[idx as int].key == key
                &&& spec_find_prop_from(props@, key, 0) == Some(props@[idx as int].desc)
            },
            None => {
                &&& (forall|k: int| 0 <= k < props@.len() ==> (#[trigger] props@[k]).key != key)
                &&& spec_find_prop_from(props@, key, 0) is None
            },
        },
{
    let n = props.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == props@.len(),
            forall|k: int| 0 <= k < i as int ==> (#[trigger] props@[k]).key != key,
            spec_find_prop_from(props@, key, 0) == spec_find_prop_from(props@, key, i as int),
        decreases n - i,
    {
        if prop_key_eq(props[i].key, key) {
            proof {
                assert(props@[i as int].key == key);
            }
            return Some(i);
        }
        i += 1;
    }
    None
}

/// Resolve a Proxy's `[[ProxyHandler]]` (which may itself be a chain of non-revoked `Proxy` objects!)
/// to the underlying `OrdinaryObject` handler (`Some(ord_id)`), or `None` when a meta-handler's
/// `get` trap returns `undefined`/`null` (so `GetMethod` treats the trap as absent and forwards to `target`).
pub fn resolve_handler_traps(
    store: &ObjectStore,
    hid: ObjId,
    fuel: usize,
) -> (res: Result<Option<ObjId>, JsError>)
    requires
        store.wf(),
        (hid as int) < store.objects@.len(),
    ensures
        match res {
            Ok(Some(ord_id)) => {
                &&& (ord_id as int) < store.objects@.len()
                &&& (store.objects@[ord_id as int] is Ordinary)
            },
            Ok(None) => true,
            Err(_) => true,
        },
        store.spec_is_revoked_proxy(hid) && fuel > 0 ==> res == Err(JsError::TypeError),
    decreases fuel,
{
    if fuel == 0 {
        return Err(JsError::RangeError);
    }
    match &store.objects[hid] {
        ObjectKind::Ordinary(_) => Ok(Some(hid)),
        ObjectKind::Proxy(_) => {
            let (next_target, meta_hid) = store.validate_non_revoked_proxy(hid)?;
            let meta_opt = resolve_handler_traps(store, meta_hid, fuel - 1)?;
            match meta_opt {
                None => resolve_handler_traps(store, next_target, fuel - 1),
                Some(meta_ord_id) => match &store.objects[meta_ord_id] {
                    ObjectKind::Ordinary(meta_ord) => match meta_ord.traps.get {
                        ValTrapStub::Missing => resolve_handler_traps(store, next_target, fuel - 1),
                        ValTrapStub::NotCallable => Err(JsError::TypeError),
                        ValTrapStub::Throw(v) => Err(JsError::Thrown(v)),
                        ValTrapStub::Return(JsVal::Undefined) | ValTrapStub::Return(JsVal::Null) => Ok(None),
                        ValTrapStub::Return(JsVal::Object(fn_obj)) => {
                            if fn_obj < store.objects.len() {
                                resolve_handler_traps(store, next_target, fuel - 1)
                            } else {
                                Err(JsError::TypeError)
                            }
                        },
                        ValTrapStub::Return(_) => Err(JsError::TypeError),
                    },
                    ObjectKind::Proxy(_) => Err(JsError::TypeError),
                },
            }
        },
    }
}

pub open spec fn spec_prevent_ext_preserves_shape_and_props(old_s: &ObjectStore, new_s: &ObjectStore) -> bool {
    &&& new_s.objects@.len() == old_s.objects@.len()
    &&& forall|k: int| 0 <= k < old_s.objects@.len() ==> match (#[trigger] &old_s.objects@[k], &new_s.objects@[k]) {
        (ObjectKind::Proxy(p1), ObjectKind::Proxy(p2)) => p1 == p2,
        (ObjectKind::Ordinary(o1), ObjectKind::Ordinary(o2)) => {
            o2.props@ == o1.props@
            && o2.prototype == o1.prototype
            && (!o1.extensible ==> !o2.extensible)
        },
        _ => false,
    }
}

pub open spec fn spec_delete_preserves_proxies_and_nonconfig(
    old_s: &ObjectStore,
    new_s: &ObjectStore,
    key: PropKey,
) -> bool {
    &&& new_s.objects@.len() == old_s.objects@.len()
    &&& forall|k: int| 0 <= k < old_s.objects@.len() ==> match (#[trigger] &old_s.objects@[k], &new_s.objects@[k]) {
        (ObjectKind::Proxy(p1), ObjectKind::Proxy(p2)) => p1 == p2,
        (ObjectKind::Ordinary(o1), ObjectKind::Ordinary(o2)) => {
            (!o1.extensible ==> !o2.extensible)
            && match spec_ordinary_own_prop(o1, key) {
                Some(td) => !spec_desc_configurable(td) ==> spec_ordinary_own_prop(o2, key) == Some(td),
                None => spec_ordinary_own_prop(o2, key) is None,
            }
        },
        _ => false,
    }
}

proof fn lemma_delete_preserves_transitive(
    s0: &ObjectStore,
    s1: &ObjectStore,
    s2: &ObjectStore,
    key: PropKey,
)
    requires
        spec_delete_preserves_proxies_and_nonconfig(s0, s1, key),
        spec_delete_preserves_proxies_and_nonconfig(s1, s2, key),
    ensures
        spec_delete_preserves_proxies_and_nonconfig(s0, s2, key),
{
    assert forall|k: int| 0 <= k < s0.objects@.len() implies match (#[trigger] &s0.objects@[k], &s2.objects@[k]) {
        (ObjectKind::Proxy(p1), ObjectKind::Proxy(p2)) => p1 == p2,
        (ObjectKind::Ordinary(o1), ObjectKind::Ordinary(o2)) => {
            (!o1.extensible ==> !o2.extensible)
            && match spec_ordinary_own_prop(o1, key) {
                Some(td) => !spec_desc_configurable(td) ==> spec_ordinary_own_prop(o2, key) == Some(td),
                None => spec_ordinary_own_prop(o2, key) is None,
            }
        },
        _ => false,
    } by {
        let _ = &s1.objects@[k];
    };
}

/// `O.[[GetPrototypeOf]]()` (§10.1.1 / §10.5.1).
pub fn object_get_prototype_of(
    store: &ObjectStore,
    obj_id: ObjId,
    fuel: usize,
) -> (res: Result<Option<ObjId>, JsError>)
    requires
        store.wf(),
        (obj_id as int) < store.objects@.len(),
    ensures
        store.spec_is_revoked_proxy(obj_id) && fuel > 0 ==> res == Err(JsError::TypeError),
        match (&store.objects@[obj_id as int], res) {
            (ObjectKind::Ordinary(ord), Ok(proto)) => proto == ord.prototype,
            _ => true,
        },
        // End-to-end stateful §6.1.7.3 [[GetPrototypeOf]] invariant on ObjectStore:
        match (store.spec_proxy_ordinary_target(obj_id), res) {
            (Some(t_ord), Ok(proto)) => !t_ord.extensible ==> proto == t_ord.prototype,
            _ => true,
        },
    decreases fuel,
{
    if fuel == 0 {
        return Err(JsError::RangeError);
    }
    proof {
        assert(spec_obj_kind_wf(store.objects@.len(), &store.objects@[obj_id as int]));
    }
    match &store.objects[obj_id] {
        ObjectKind::Ordinary(ord) => Ok(ord.prototype),
        ObjectKind::Proxy(_) => {
            let (tid, hid) = store.validate_non_revoked_proxy(obj_id)?;
            let stub = match resolve_handler_traps(store, hid, fuel - 1)? {
                None => ProtoTrapStub::Missing,
                Some(ord_hid) => match &store.objects[ord_hid] {
                    ObjectKind::Ordinary(h_ord) => h_ord.traps.get_prototype_of,
                    ObjectKind::Proxy(_) => ProtoTrapStub::Missing,
                },
            };
            match stub {
                ProtoTrapStub::Missing => object_get_prototype_of(store, tid, fuel - 1),
                ProtoTrapStub::NotCallable => Err(JsError::TypeError),
                ProtoTrapStub::Throw(v) => Err(JsError::Thrown(v)),
                ProtoTrapStub::Return(trap_out) => {
                    if let ProtoTrapOutput::Object(pid) = trap_out {
                        if pid >= store.objects.len() {
                            return Err(JsError::TypeError);
                        }
                    }
                    let target_ext = object_is_extensible(store, tid, fuel - 1)?;
                    if target_ext {
                        return proxy_validate_get_prototype_of(trap_out, true, None);
                    }
                    let target_proto = object_get_prototype_of(store, tid, fuel - 1)?;
                    proxy_validate_get_prototype_of(trap_out, false, target_proto)
                },
            }
        },
    }
}

/// `O.[[IsExtensible]]()` (§10.1.3 / §10.5.3).
pub fn object_is_extensible(
    store: &ObjectStore,
    obj_id: ObjId,
    fuel: usize,
) -> (res: Result<bool, JsError>)
    requires
        store.wf(),
        (obj_id as int) < store.objects@.len(),
    ensures
        store.spec_is_revoked_proxy(obj_id) && fuel > 0 ==> res == Err(JsError::TypeError),
        match (&store.objects@[obj_id as int], res) {
            (ObjectKind::Ordinary(ord), Ok(b)) => b == ord.extensible,
            _ => true,
        },
        // End-to-end stateful §6.1.7.3 [[IsExtensible]] invariant on ObjectStore:
        match (store.spec_proxy_ordinary_target(obj_id), res) {
            (Some(t_ord), Ok(b)) => b == t_ord.extensible,
            _ => true,
        },
    decreases fuel,
{
    if fuel == 0 {
        return Err(JsError::RangeError);
    }
    match &store.objects[obj_id] {
        ObjectKind::Ordinary(ord) => Ok(ord.extensible),
        ObjectKind::Proxy(_) => {
            let (tid, hid) = store.validate_non_revoked_proxy(obj_id)?;
            let stub = match resolve_handler_traps(store, hid, fuel - 1)? {
                None => BoolTrapStub::Missing,
                Some(ord_hid) => match &store.objects[ord_hid] {
                    ObjectKind::Ordinary(h_ord) => h_ord.traps.is_extensible,
                    ObjectKind::Proxy(_) => BoolTrapStub::Missing,
                },
            };
            match stub {
                BoolTrapStub::Missing => object_is_extensible(store, tid, fuel - 1),
                BoolTrapStub::NotCallable => Err(JsError::TypeError),
                BoolTrapStub::Throw(v) => Err(JsError::Thrown(v)),
                BoolTrapStub::Return(b)
                | BoolTrapStub::MutateTargetAndReturn(b)
                | BoolTrapStub::SealTargetAndReturn(b)
                | BoolTrapStub::SetTargetProtoSealAndReturn { ret: b, .. } => {
                    let target_ext = object_is_extensible(store, tid, fuel - 1)?;
                    proxy_validate_is_extensible(b, target_ext)
                },
            }
        },
    }
}

/// Ordinary prototype cycle check (§10.1.2.1 step 8): prevents prototype cycles so prototype chains are finite.
fn proto_creates_cycle(store: &ObjectStore, target_id: ObjId, candidate: Option<ObjId>, fuel: usize) -> (cyc: bool)
    requires
        store.wf(),
    decreases fuel,
{
    if fuel == 0 {
        return true;
    }
    match candidate {
        None => false,
        Some(p) => {
            if p == target_id {
                true
            } else if p >= store.objects.len() {
                true
            } else {
                match &store.objects[p] {
                    ObjectKind::Ordinary(ord) => proto_creates_cycle(store, target_id, ord.prototype, fuel - 1),
                    // §10.1.2.1 step 8.c.i: stop cycle walk if p's [[GetPrototypeOf]] is not ordinary
                    ObjectKind::Proxy(_) => false,
                }
            }
        },
    }
}

/// `O.[[SetPrototypeOf]](V)` (§10.1.2 / §10.5.2).
pub fn object_set_prototype_of(
    store: &mut ObjectStore,
    obj_id: ObjId,
    new_proto: Option<ObjId>,
    fuel: usize,
) -> (res: Result<bool, JsError>)
    requires
        old(store).wf(),
        (obj_id as int) < old(store).objects@.len(),
        match new_proto {
            None => true,
            Some(pid) => (pid as int) < old(store).objects@.len(),
        },
    ensures
        final(store).wf(),
        final(store).objects@.len() == old(store).objects@.len(),
        old(store).spec_is_revoked_proxy(obj_id) && fuel > 0 ==> res == Err(JsError::TypeError),
        forall|k: int| 0 <= k < old(store).objects@.len() ==> match (#[trigger] &old(store).objects@[k], &final(store).objects@[k]) {
            (ObjectKind::Proxy(p1), ObjectKind::Proxy(p2)) => p1 == p2,
            (ObjectKind::Ordinary(_), ObjectKind::Ordinary(_)) => true,
            _ => false,
        },
        // End-to-end stateful §6.1.7.3 [[SetPrototypeOf]] invariant on ObjectStore:
        match (final(store).spec_proxy_ordinary_target(obj_id), res) {
            (Some(t_ord), Ok(true)) => !t_ord.extensible ==> new_proto == t_ord.prototype,
            _ => true,
        },
    decreases fuel,
{
    if fuel == 0 {
        return Err(JsError::RangeError);
    }
    let is_ord = matches!(&store.objects[obj_id], ObjectKind::Ordinary(_));
    if is_ord {
        let (cur_proto, ext) = match &store.objects[obj_id] {
            ObjectKind::Ordinary(ord) => (ord.prototype, ord.extensible),
            ObjectKind::Proxy(_) => return Err(JsError::TypeError),
        };
        if opt_obj_eq(new_proto, cur_proto) {
            return Ok(true);
        }
        if !ext {
            return Ok(false);
        }
        let max_walk = store.objects.len() + 1;
        if proto_creates_cycle(store, obj_id, new_proto, max_walk) {
            return Ok(false);
        }
        let ghost old_objs = store.objects@;
        if let ObjectKind::Ordinary(ord) = &mut store.objects[obj_id] {
            ord.prototype = new_proto;
        }
        proof {
            assert forall|i: int| 0 <= i < store.objects@.len()
                implies spec_obj_kind_wf(store.objects@.len(), #[trigger] &store.objects@[i])
            by {
                if i != obj_id as int {
                    assert(&store.objects@[i] == &old_objs[i]);
                }
                assert(spec_obj_kind_wf(old_objs.len(), &old_objs[i]));
            };
            assert forall|k: int| 0 <= k < old_objs.len() implies match (#[trigger] &old_objs[k], &store.objects@[k]) {
                (ObjectKind::Proxy(p1), ObjectKind::Proxy(p2)) => p1 == p2,
                (ObjectKind::Ordinary(_), ObjectKind::Ordinary(_)) => true,
                _ => false,
            } by {
                if k != obj_id as int {
                    assert(&store.objects@[k] == &old_objs[k]);
                }
            };
        }
        Ok(true)
    } else {
        let (tid, hid) = store.validate_non_revoked_proxy(obj_id)?;
        let stub = match resolve_handler_traps(store, hid, fuel - 1)? {
            None => BoolTrapStub::Missing,
            Some(ord_hid) => match &store.objects[ord_hid] {
                ObjectKind::Ordinary(h_ord) => h_ord.traps.set_prototype_of,
                ObjectKind::Proxy(_) => BoolTrapStub::Missing,
            },
        };
        match stub {
            BoolTrapStub::Missing => {
                let r = object_set_prototype_of(store, tid, new_proto, fuel - 1)?;
                if !r {
                    return Ok(false);
                }
                let target_ext = object_is_extensible(store, tid, fuel - 1)?;
                if target_ext {
                    return Ok(true);
                }
                let target_proto = object_get_prototype_of(store, tid, fuel - 1)?;
                proxy_validate_set_prototype_of(true, new_proto, false, target_proto)
            },
            BoolTrapStub::NotCallable => Err(JsError::TypeError),
            BoolTrapStub::Throw(v) => Err(JsError::Thrown(v)),
            BoolTrapStub::MutateTargetAndReturn(b) => {
                let _ = object_set_prototype_of(store, tid, new_proto, fuel - 1)?;
                if !b {
                    return Ok(false);
                }
                let target_ext = object_is_extensible(store, tid, fuel - 1)?;
                if target_ext {
                    return Ok(true);
                }
                let target_proto = object_get_prototype_of(store, tid, fuel - 1)?;
                proxy_validate_set_prototype_of(true, new_proto, false, target_proto)
            },
            BoolTrapStub::SealTargetAndReturn(b) => {
                let _ = object_prevent_extensions(store, tid, fuel - 1)?;
                if !b {
                    return Ok(false);
                }
                let target_ext = object_is_extensible(store, tid, fuel - 1)?;
                if target_ext {
                    return Ok(true);
                }
                let target_proto = object_get_prototype_of(store, tid, fuel - 1)?;
                proxy_validate_set_prototype_of(true, new_proto, false, target_proto)
            },
            BoolTrapStub::SetTargetProtoSealAndReturn { proto, ret: b } => {
                if let Some(pid) = proto {
                    if pid >= store.objects.len() {
                        return Err(JsError::TypeError);
                    }
                }
                let ghost s0_objs = store.objects@;
                let _ = object_set_prototype_of(store, tid, proto, fuel - 1)?;
                let ghost s1_objs = store.objects@;
                let seal_res = object_prevent_extensions(store, tid, fuel - 1);
                proof {
                    assert forall|k: int| 0 <= k < s0_objs.len() implies match (#[trigger] &s0_objs[k], &store.objects@[k]) {
                        (ObjectKind::Proxy(p1), ObjectKind::Proxy(p2)) => p1 == p2,
                        (ObjectKind::Ordinary(_), ObjectKind::Ordinary(_)) => true,
                        _ => false,
                    } by {
                        let _ = &s1_objs[k];
                    };
                }
                let _ = seal_res?;
                if !b {
                    return Ok(false);
                }
                let target_ext = object_is_extensible(store, tid, fuel - 1)?;
                if target_ext {
                    return Ok(true);
                }
                let target_proto = object_get_prototype_of(store, tid, fuel - 1)?;
                proxy_validate_set_prototype_of(true, new_proto, false, target_proto)
            },
            BoolTrapStub::Return(b) => {
                if !b {
                    return Ok(false);
                }
                let target_ext = object_is_extensible(store, tid, fuel - 1)?;
                if target_ext {
                    return Ok(true);
                }
                let target_proto = object_get_prototype_of(store, tid, fuel - 1)?;
                proxy_validate_set_prototype_of(true, new_proto, false, target_proto)
            },
        }
    }
}

/// `O.[[PreventExtensions]]()` (§10.1.4 / §10.5.4).
pub fn object_prevent_extensions(
    store: &mut ObjectStore,
    obj_id: ObjId,
    fuel: usize,
) -> (res: Result<bool, JsError>)
    requires
        old(store).wf(),
        (obj_id as int) < old(store).objects@.len(),
    ensures
        final(store).wf(),
        final(store).objects@.len() == old(store).objects@.len(),
        spec_prevent_ext_preserves_shape_and_props(old(store), final(store)),
        old(store).spec_is_revoked_proxy(obj_id) && fuel > 0 ==> res == Err(JsError::TypeError),
        match (&final(store).objects@[obj_id as int], res) {
            (ObjectKind::Ordinary(ord), Ok(true)) => !ord.extensible,
            _ => true,
        },
        // End-to-end stateful §6.1.7.3 [[PreventExtensions]] invariant on ObjectStore:
        match (final(store).spec_proxy_ordinary_target(obj_id), res) {
            (Some(t_ord), Ok(true)) => !t_ord.extensible,
            _ => true,
        },
    decreases fuel,
{
    if fuel == 0 {
        return Err(JsError::RangeError);
    }
    let is_ord = matches!(&store.objects[obj_id], ObjectKind::Ordinary(_));
    if is_ord {
        let ghost old_objs = store.objects@;
        if let ObjectKind::Ordinary(ord) = &mut store.objects[obj_id] {
            ord.extensible = false;
        }
        proof {
            assert forall|i: int| 0 <= i < store.objects@.len()
                implies spec_obj_kind_wf(store.objects@.len(), #[trigger] &store.objects@[i])
            by {
                if i != obj_id as int {
                    assert(&store.objects@[i] == &old_objs[i]);
                }
                assert(spec_obj_kind_wf(old_objs.len(), &old_objs[i]));
            };
            assert forall|k: int| 0 <= k < old_objs.len() implies match (#[trigger] &old_objs[k], &store.objects@[k]) {
                (ObjectKind::Proxy(p1), ObjectKind::Proxy(p2)) => p1 == p2,
                (ObjectKind::Ordinary(o1), ObjectKind::Ordinary(o2)) => {
                    o2.props@ == o1.props@
                    && o2.prototype == o1.prototype
                    && (!o1.extensible ==> !o2.extensible)
                },
                _ => false,
            } by {
                if k != obj_id as int {
                    assert(&store.objects@[k] == &old_objs[k]);
                }
            };
        }
        Ok(true)
    } else {
        let (tid, hid) = store.validate_non_revoked_proxy(obj_id)?;
        let stub = match resolve_handler_traps(store, hid, fuel - 1)? {
            None => BoolTrapStub::Missing,
            Some(ord_hid) => match &store.objects[ord_hid] {
                ObjectKind::Ordinary(h_ord) => h_ord.traps.prevent_extensions,
                ObjectKind::Proxy(_) => BoolTrapStub::Missing,
            },
        };
        match stub {
            BoolTrapStub::Missing => {
                let r = object_prevent_extensions(store, tid, fuel - 1)?;
                proof {
                    let _ = &old(store).objects@[obj_id as int];
                }
                Ok(r)
            },
            BoolTrapStub::NotCallable => Err(JsError::TypeError),
            BoolTrapStub::Throw(v) => Err(JsError::Thrown(v)),
            BoolTrapStub::MutateTargetAndReturn(b) | BoolTrapStub::SealTargetAndReturn(b) => {
                let _ = object_prevent_extensions(store, tid, fuel - 1)?;
                let target_ext = object_is_extensible(store, tid, fuel - 1)?;
                proof {
                    let _ = &old(store).objects@[obj_id as int];
                }
                proxy_validate_prevent_extensions(b, target_ext)
            },
            BoolTrapStub::Return(b) | BoolTrapStub::SetTargetProtoSealAndReturn { ret: b, .. } => {
                if !b {
                    return Ok(false);
                }
                let target_ext = object_is_extensible(store, tid, fuel - 1)?;
                proxy_validate_prevent_extensions(true, target_ext)
            },
        }
    }
}

/// `O.[[GetOwnProperty]](P)` (§10.1.5 / §10.5.5).
pub fn object_get_own_property(
    store: &ObjectStore,
    obj_id: ObjId,
    key: PropKey,
    fuel: usize,
) -> (res: Result<Option<PropertyDescriptor>, JsError>)
    requires
        store.wf(),
        (obj_id as int) < store.objects@.len(),
    ensures
        store.spec_is_revoked_proxy(obj_id) && fuel > 0 ==> res == Err(JsError::TypeError),
        match (&store.objects@[obj_id as int], res) {
            (ObjectKind::Ordinary(ord), Ok(d)) => d == spec_ordinary_own_prop(ord, key),
            _ => true,
        },
        // End-to-end stateful §6.1.7.3 [[GetOwnProperty]] invariants on ObjectStore:
        match (store.spec_proxy_ordinary_target(obj_id), res) {
            (Some(t_ord), Ok(None)) => match spec_ordinary_own_prop(t_ord, key) {
                Some(td) => spec_desc_configurable(td) && t_ord.extensible,
                None => true,
            },
            (Some(t_ord), Ok(Some(rd))) => {
                let td_opt = spec_ordinary_own_prop(t_ord, key);
                &&& ((td_opt is None) ==> t_ord.extensible)
                &&& (!spec_desc_configurable(rd) ==> match td_opt {
                    Some(td) => !spec_desc_configurable(td),
                    None => false,
                })
                &&& match (rd, td_opt) {
                    (
                        PropertyDescriptor::Data { configurable: false, writable: false, .. },
                        Some(PropertyDescriptor::Data { writable: true, .. }),
                    ) => false,
                    _ => true,
                }
                &&& match td_opt {
                    Some(PropertyDescriptor::Data { value: tv, writable: false, configurable: false, enumerable: te }) => {
                        match rd {
                            PropertyDescriptor::Data { value: rv, writable: false, configurable: false, enumerable: re } =>
                                crate::types::spec_same_value(rv, tv) && re == te,
                            _ => false,
                        }
                    },
                    _ => true,
                }
            },
            _ => true,
        },
    decreases fuel,
{
    if fuel == 0 {
        return Err(JsError::RangeError);
    }
    match &store.objects[obj_id] {
        ObjectKind::Ordinary(ord) => {
            match find_prop_index(&ord.props, key) {
                Some(idx) => Ok(Some(ord.props[idx].desc)),
                None => Ok(None),
            }
        },
        ObjectKind::Proxy(_) => {
            let (tid, hid) = store.validate_non_revoked_proxy(obj_id)?;
            let stub = match resolve_handler_traps(store, hid, fuel - 1)? {
                None => OwnPropDescTrapStub::Missing,
                Some(ord_hid) => match &store.objects[ord_hid] {
                    ObjectKind::Ordinary(h_ord) => h_ord.traps.get_own_property_descriptor,
                    ObjectKind::Proxy(_) => OwnPropDescTrapStub::Missing,
                },
            };
            match stub {
                OwnPropDescTrapStub::Missing => {
                    let d_res = object_get_own_property(store, tid, key, fuel - 1)?;
                    proof {
                        if let Some(PropertyDescriptor::Data { value: v, .. }) = d_res {
                            crate::types::lemma_same_value_equivalence(v, v, v);
                        }
                    }
                    Ok(d_res)
                },
                OwnPropDescTrapStub::NotCallable => Err(JsError::TypeError),
                OwnPropDescTrapStub::Throw(v) => Err(JsError::Thrown(v)),
                OwnPropDescTrapStub::Return(trap_out) => {
                    let target_desc = object_get_own_property(store, tid, key, fuel - 1)?;
                    let target_ext = object_is_extensible(store, tid, fuel - 1)?;
                    proxy_validate_get_own_property(trap_out, target_desc, target_ext)
                },
            }
        },
    }
}

/// `O.[[DefineOwnProperty]](P, Desc)` (§10.1.6 / §10.5.6).
pub fn object_define_own_property(
    store: &mut ObjectStore,
    obj_id: ObjId,
    key: PropKey,
    desc: PartialDescriptor,
    fuel: usize,
) -> (res: Result<bool, JsError>)
    requires
        old(store).wf(),
        (obj_id as int) < old(store).objects@.len(),
    ensures
        final(store).wf(),
        final(store).objects@.len() == old(store).objects@.len(),
        old(store).spec_is_revoked_proxy(obj_id) && fuel > 0 ==> res == Err(JsError::TypeError),
    decreases fuel,
{
    if fuel == 0 {
        return Err(JsError::RangeError);
    }
    if !is_valid_partial_descriptor(desc) {
        return Err(JsError::TypeError);
    }
    let is_ord = matches!(&store.objects[obj_id], ObjectKind::Ordinary(_));
    if is_ord {
        let (ext, found) = match &store.objects[obj_id] {
            ObjectKind::Ordinary(ord) => {
                let idx_opt = find_prop_index(&ord.props, key);
                (ord.extensible, idx_opt)
            },
            ObjectKind::Proxy(_) => return Err(JsError::TypeError),
        };
        let cur_desc = match found {
            Some(idx) => match &store.objects[obj_id] {
                ObjectKind::Ordinary(ord) => Some(ord.props[idx].desc),
                ObjectKind::Proxy(_) => None,
            },
            None => None,
        };
        if !is_compatible_descriptor(ext, desc, cur_desc) {
            return Ok(false);
        }
        let applied = apply_descriptor(desc, cur_desc);
        let ghost old_objs = store.objects@;
        if let ObjectKind::Ordinary(ord) = &mut store.objects[obj_id] {
            proof {
                assert(spec_obj_kind_wf(old_objs.len(), &old_objs[obj_id as int]));
            }
            match found {
                Some(idx) => {
                    let ghost old_props = ord.props@;
                    ord.props.set(idx, PropEntry { key, desc: applied });
                    proof {
                        assert forall|a: int, b: int| 0 <= a < b < ord.props@.len()
                            implies ord.props@[a].key != ord.props@[b].key
                        by {
                            assert(ord.props@[a].key == old_props[a].key);
                            assert(ord.props@[b].key == old_props[b].key);
                        };
                    }
                },
                None => {
                    let ghost old_props = ord.props@;
                    ord.props.push(PropEntry { key, desc: applied });
                    proof {
                        assert forall|a: int, b: int| 0 <= a < b < ord.props@.len()
                            implies ord.props@[a].key != ord.props@[b].key
                        by {
                            if b == old_props.len() as int {
                                assert((#[trigger] old_props[a]).key != key);
                            } else {
                                assert(ord.props@[a].key == old_props[a].key);
                                assert(ord.props@[b].key == old_props[b].key);
                            }
                        };
                    }
                },
            }
        }
        proof {
            assert forall|i: int| 0 <= i < store.objects@.len()
                implies spec_obj_kind_wf(store.objects@.len(), #[trigger] &store.objects@[i])
            by {
                if i != obj_id as int {
                    assert(&store.objects@[i] == &old_objs[i]);
                    assert(spec_obj_kind_wf(old_objs.len(), &old_objs[i]));
                }
            };
        }
        Ok(true)
    } else {
        let (tid, hid) = store.validate_non_revoked_proxy(obj_id)?;
        let stub = match resolve_handler_traps(store, hid, fuel - 1)? {
            None => BoolTrapStub::Missing,
            Some(ord_hid) => match &store.objects[ord_hid] {
                ObjectKind::Ordinary(h_ord) => h_ord.traps.define_property,
                ObjectKind::Proxy(_) => BoolTrapStub::Missing,
            },
        };
        match stub {
            BoolTrapStub::Missing => object_define_own_property(store, tid, key, desc, fuel - 1),
            BoolTrapStub::NotCallable => Err(JsError::TypeError),
            BoolTrapStub::Throw(v) => Err(JsError::Thrown(v)),
            BoolTrapStub::MutateTargetAndReturn(b) => {
                let _ = object_define_own_property(store, tid, key, desc, fuel - 1)?;
                if !b {
                    return Ok(false);
                }
                let target_desc = object_get_own_property(store, tid, key, fuel - 1)?;
                let target_ext = object_is_extensible(store, tid, fuel - 1)?;
                proxy_validate_define_own_property(true, desc, target_desc, target_ext)
            },
            BoolTrapStub::SealTargetAndReturn(b) => {
                let _ = object_prevent_extensions(store, tid, fuel - 1)?;
                if !b {
                    return Ok(false);
                }
                let target_desc = object_get_own_property(store, tid, key, fuel - 1)?;
                let target_ext = object_is_extensible(store, tid, fuel - 1)?;
                proxy_validate_define_own_property(true, desc, target_desc, target_ext)
            },
            BoolTrapStub::Return(b) | BoolTrapStub::SetTargetProtoSealAndReturn { ret: b, .. } => {
                if !b {
                    return Ok(false);
                }
                let target_desc = object_get_own_property(store, tid, key, fuel - 1)?;
                let target_ext = object_is_extensible(store, tid, fuel - 1)?;
                proxy_validate_define_own_property(true, desc, target_desc, target_ext)
            },
        }
    }
}

/// `O.[[HasProperty]](P)` (§10.1.7 / §10.5.7).
pub fn object_has_property(
    store: &ObjectStore,
    obj_id: ObjId,
    key: PropKey,
    fuel: usize,
) -> (res: Result<bool, JsError>)
    requires
        store.wf(),
        (obj_id as int) < store.objects@.len(),
    ensures
        store.spec_is_revoked_proxy(obj_id) && fuel > 0 ==> res == Err(JsError::TypeError),
        match (&store.objects@[obj_id as int], res) {
            (ObjectKind::Ordinary(ord), Ok(false)) => spec_ordinary_own_prop(ord, key) is None,
            _ => true,
        },
        // End-to-end stateful §6.1.7.3 [[HasProperty]] invariant on ObjectStore:
        match (store.spec_proxy_ordinary_target(obj_id), res) {
            (Some(t_ord), Ok(false)) => match spec_ordinary_own_prop(t_ord, key) {
                None => true,
                Some(td) => spec_desc_configurable(td) && t_ord.extensible,
            },
            _ => true,
        },
    decreases fuel,
{
    if fuel == 0 {
        return Err(JsError::RangeError);
    }
    match &store.objects[obj_id] {
        ObjectKind::Ordinary(_) => {
            let own = object_get_own_property(store, obj_id, key, fuel - 1)?;
            if matches!(own, Some(_)) {
                return Ok(true);
            }
            let parent = object_get_prototype_of(store, obj_id, fuel - 1)?;
            match parent {
                None => Ok(false),
                Some(pid) => {
                    if pid >= store.objects.len() {
                        Err(JsError::TypeError)
                    } else {
                        let r = object_has_property(store, pid, key, fuel - 1)?;
                        Ok(r)
                    }
                },
            }
        },
        ObjectKind::Proxy(_) => {
            let (tid, hid) = store.validate_non_revoked_proxy(obj_id)?;
            let stub = match resolve_handler_traps(store, hid, fuel - 1)? {
                None => BoolTrapStub::Missing,
                Some(ord_hid) => match &store.objects[ord_hid] {
                    ObjectKind::Ordinary(h_ord) => h_ord.traps.has,
                    ObjectKind::Proxy(_) => BoolTrapStub::Missing,
                },
            };
            match stub {
                BoolTrapStub::Missing => object_has_property(store, tid, key, fuel - 1),
                BoolTrapStub::NotCallable => Err(JsError::TypeError),
                BoolTrapStub::Throw(v) => Err(JsError::Thrown(v)),
                BoolTrapStub::Return(b)
                | BoolTrapStub::MutateTargetAndReturn(b)
                | BoolTrapStub::SealTargetAndReturn(b)
                | BoolTrapStub::SetTargetProtoSealAndReturn { ret: b, .. } => {
                    if b {
                        return Ok(true);
                    }
                    let target_desc = object_get_own_property(store, tid, key, fuel - 1)?;
                    match target_desc {
                        None => Ok(false),
                        Some(_) => {
                            let target_ext = object_is_extensible(store, tid, fuel - 1)?;
                            proxy_validate_has_property(false, target_desc, target_ext)
                        },
                    }
                },
            }
        },
    }
}

/// `O.[[Get]](P, Receiver)` (§10.1.8 / §10.5.8).
pub fn object_get(
    store: &ObjectStore,
    obj_id: ObjId,
    key: PropKey,
    receiver: JsVal,
    fuel: usize,
) -> (res: Result<JsVal, JsError>)
    requires
        store.wf(),
        (obj_id as int) < store.objects@.len(),
    ensures
        store.spec_is_revoked_proxy(obj_id) && fuel > 0 ==> res == Err(JsError::TypeError),
        match (&store.objects@[obj_id as int], res) {
            (ObjectKind::Ordinary(ord), Ok(v)) => match spec_ordinary_own_prop(ord, key) {
                Some(PropertyDescriptor::Data { value: tv, .. }) => v == tv,
                Some(PropertyDescriptor::Accessor { get: None, .. }) => v == JsVal::Undefined,
                _ => true,
            },
            _ => true,
        },
        // End-to-end stateful §6.1.7.3 [[Get]] invariant on ObjectStore:
        match (store.spec_proxy_ordinary_target(obj_id), res) {
            (Some(t_ord), Ok(v)) => match spec_ordinary_own_prop(t_ord, key) {
                Some(PropertyDescriptor::Data { value: tv, writable: false, configurable: false, .. }) =>
                    crate::types::spec_same_value(v, tv),
                Some(PropertyDescriptor::Accessor { get: None, configurable: false, .. }) =>
                    v == JsVal::Undefined,
                _ => true,
            },
            _ => true,
        },
    decreases fuel,
{
    if fuel == 0 {
        return Err(JsError::RangeError);
    }
    match &store.objects[obj_id] {
        ObjectKind::Ordinary(_) => {
            let desc = object_get_own_property(store, obj_id, key, fuel - 1)?;
            match desc {
                None => {
                    let parent = object_get_prototype_of(store, obj_id, fuel - 1)?;
                    match parent {
                        None => Ok(JsVal::Undefined),
                        Some(pid) => {
                            if pid >= store.objects.len() {
                                Err(JsError::TypeError)
                            } else {
                                object_get(store, pid, key, receiver, fuel - 1)
                            }
                        },
                    }
                },
                Some(PropertyDescriptor::Data { value, .. }) => Ok(value),
                Some(PropertyDescriptor::Accessor { get, .. }) => {
                    match get {
                        None => Ok(JsVal::Undefined),
                        Some(getter_id) => Ok(JsVal::Object(getter_id)),
                    }
                },
            }
        },
        ObjectKind::Proxy(_) => {
            let (tid, hid) = store.validate_non_revoked_proxy(obj_id)?;
            let stub = match resolve_handler_traps(store, hid, fuel - 1)? {
                None => ValTrapStub::Missing,
                Some(ord_hid) => match &store.objects[ord_hid] {
                    ObjectKind::Ordinary(h_ord) => h_ord.traps.get,
                    ObjectKind::Proxy(_) => ValTrapStub::Missing,
                },
            };
            match stub {
                ValTrapStub::Missing => {
                    let v = object_get(store, tid, key, receiver, fuel - 1)?;
                    proof {
                        crate::types::lemma_same_value_equivalence(v, v, v);
                    }
                    Ok(v)
                },
                ValTrapStub::NotCallable => Err(JsError::TypeError),
                ValTrapStub::Throw(v) => Err(JsError::Thrown(v)),
                ValTrapStub::Return(trap_val) => {
                    let target_desc = object_get_own_property(store, tid, key, fuel - 1)?;
                    proxy_validate_get(trap_val, target_desc)
                },
            }
        },
    }
}

/// `O.[[Set]](P, V, Receiver)` (§10.1.9 / §10.5.9).
pub fn object_set(
    store: &mut ObjectStore,
    obj_id: ObjId,
    key: PropKey,
    val: JsVal,
    receiver: JsVal,
    fuel: usize,
) -> (res: Result<bool, JsError>)
    requires
        old(store).wf(),
        (obj_id as int) < old(store).objects@.len(),
    ensures
        final(store).wf(),
        final(store).objects@.len() == old(store).objects@.len(),
        old(store).spec_is_revoked_proxy(obj_id) && fuel > 0 ==> res == Err(JsError::TypeError),
    decreases fuel,
{
    if fuel == 0 {
        return Err(JsError::RangeError);
    }
    let is_ord = matches!(&store.objects[obj_id], ObjectKind::Ordinary(_));
    if is_ord {
        let own_desc = object_get_own_property(store, obj_id, key, fuel - 1)?;
        let resolved_desc = match own_desc {
            Some(d) => d,
            None => {
                let parent = object_get_prototype_of(store, obj_id, fuel - 1)?;
                match parent {
                    Some(pid) => {
                        if pid >= store.objects.len() {
                            return Err(JsError::TypeError);
                        }
                        return object_set(store, pid, key, val, receiver, fuel - 1);
                    },
                    None => PropertyDescriptor::Data {
                        value: JsVal::Undefined,
                        writable: true,
                        enumerable: true,
                        configurable: true,
                    },
                }
            },
        };
        match resolved_desc {
            PropertyDescriptor::Data { writable, .. } => {
                if !writable {
                    return Ok(false);
                }
                let recv_id = match receiver {
                    JsVal::Object(rid) => rid,
                    _ => return Ok(false),
                };
                if recv_id >= store.objects.len() {
                    return Ok(false);
                }
                let existing = object_get_own_property(store, recv_id, key, fuel - 1)?;
                match existing {
                    Some(PropertyDescriptor::Accessor { .. }) => Ok(false),
                    Some(PropertyDescriptor::Data { writable: false, .. }) => Ok(false),
                    Some(PropertyDescriptor::Data { .. }) => {
                        let upd = PartialDescriptor {
                            value: Some(val),
                            writable: None,
                            get: None,
                            set: None,
                            enumerable: None,
                            configurable: None,
                        };
                        object_define_own_property(store, recv_id, key, upd, fuel - 1)
                    },
                    None => {
                        let create = PartialDescriptor {
                            value: Some(val),
                            writable: Some(true),
                            get: None,
                            set: None,
                            enumerable: Some(true),
                            configurable: Some(true),
                        };
                        object_define_own_property(store, recv_id, key, create, fuel - 1)
                    },
                }
            },
            PropertyDescriptor::Accessor { set, .. } => {
                match set {
                    None => Ok(false),
                    Some(_) => Ok(true),
                }
            },
        }
    } else {
        let (tid, hid) = store.validate_non_revoked_proxy(obj_id)?;
        let stub = match resolve_handler_traps(store, hid, fuel - 1)? {
            None => BoolTrapStub::Missing,
            Some(ord_hid) => match &store.objects[ord_hid] {
                ObjectKind::Ordinary(h_ord) => h_ord.traps.set,
                ObjectKind::Proxy(_) => BoolTrapStub::Missing,
            },
        };
        match stub {
            BoolTrapStub::Missing => object_set(store, tid, key, val, receiver, fuel - 1),
            BoolTrapStub::NotCallable => Err(JsError::TypeError),
            BoolTrapStub::Throw(v) => Err(JsError::Thrown(v)),
            BoolTrapStub::MutateTargetAndReturn(b) => {
                let _ = object_set(store, tid, key, val, receiver, fuel - 1)?;
                if !b {
                    return Ok(false);
                }
                let target_desc = object_get_own_property(store, tid, key, fuel - 1)?;
                proxy_validate_set(true, val, target_desc)
            },
            BoolTrapStub::SealTargetAndReturn(b) => {
                let _ = object_prevent_extensions(store, tid, fuel - 1)?;
                if !b {
                    return Ok(false);
                }
                let target_desc = object_get_own_property(store, tid, key, fuel - 1)?;
                proxy_validate_set(true, val, target_desc)
            },
            BoolTrapStub::Return(b) | BoolTrapStub::SetTargetProtoSealAndReturn { ret: b, .. } => {
                if !b {
                    return Ok(false);
                }
                let target_desc = object_get_own_property(store, tid, key, fuel - 1)?;
                proxy_validate_set(true, val, target_desc)
            },
        }
    }
}

/// `O.[[Delete]](P)` (§10.1.10 / §10.5.10).
pub fn object_delete(
    store: &mut ObjectStore,
    obj_id: ObjId,
    key: PropKey,
    fuel: usize,
) -> (res: Result<bool, JsError>)
    requires
        old(store).wf(),
        (obj_id as int) < old(store).objects@.len(),
    ensures
        final(store).wf(),
        final(store).objects@.len() == old(store).objects@.len(),
        spec_delete_preserves_proxies_and_nonconfig(old(store), final(store), key),
        old(store).spec_is_revoked_proxy(obj_id) && fuel > 0 ==> res == Err(JsError::TypeError),
        // Ordinary [[Delete]] invariant: returns `Ok(true)` ==> own property is absent in `final(store)`,
        // and non-configurable own property returns `Ok(false)`!
        match (&old(store).objects@[obj_id as int], res) {
            (ObjectKind::Ordinary(old_ord), Ok(true)) => match spec_ordinary_own_prop(old_ord, key) {
                Some(td) => spec_desc_configurable(td),
                None => true,
            },
            _ => true,
        },
        match (&final(store).objects@[obj_id as int], res) {
            (ObjectKind::Ordinary(fin_ord), Ok(true)) => spec_ordinary_own_prop(fin_ord, key) is None,
            _ => true,
        },
        // End-to-end stateful §6.1.7.3 [[Delete]] invariants on ObjectStore (both pre-state & post-state!):
        match (old(store).spec_proxy_ordinary_target(obj_id), res) {
            (Some(old_t_ord), Ok(true)) => match spec_ordinary_own_prop(old_t_ord, key) {
                Some(td) => spec_desc_configurable(td),
                None => true,
            },
            _ => true,
        },
        match (final(store).spec_proxy_ordinary_target(obj_id), res) {
            (Some(fin_t_ord), Ok(true)) => match spec_ordinary_own_prop(fin_t_ord, key) {
                None => true,
                Some(td) => spec_desc_configurable(td) && fin_t_ord.extensible,
            },
            _ => true,
        },
    decreases fuel,
{
    if fuel == 0 {
        return Err(JsError::RangeError);
    }
    let is_ord = matches!(&store.objects[obj_id], ObjectKind::Ordinary(_));
    if is_ord {
        let found = match &store.objects[obj_id] {
            ObjectKind::Ordinary(ord) => find_prop_index(&ord.props, key),
            ObjectKind::Proxy(_) => None,
        };
        match found {
            None => Ok(true),
            Some(idx) => {
                let conf = match &store.objects[obj_id] {
                    ObjectKind::Ordinary(ord) => desc_configurable(ord.props[idx].desc),
                    ObjectKind::Proxy(_) => false,
                };
                if !conf {
                    return Ok(false);
                }
                let ghost old_objs = store.objects@;
                if let ObjectKind::Ordinary(ord) = &mut store.objects[obj_id] {
                    proof {
                        assert(spec_obj_kind_wf(old_objs.len(), &old_objs[obj_id as int]));
                    }
                    let n = ord.props.len();
                    let mut rebuilt: Vec<PropEntry> = Vec::new();
                    let mut i: usize = 0;
                    while i < n
                        invariant
                            i <= n,
                            idx < n,
                            n == ord.props@.len(),
                            ord.props@[idx as int].key == key,
                            spec_entries_unique(ord.props@),
                            rebuilt@.len() == (if i <= idx { i as int } else { i as int - 1 }),
                            forall|r: int| 0 <= r < rebuilt@.len() ==>
                                #[trigger] rebuilt@[r] == ord.props@[if r < idx as int { r } else { r + 1 }],
                            spec_entries_unique(rebuilt@),
                        decreases n - i,
                    {
                        if i != idx {
                            let entry = ord.props[i];
                            let ghost prev_rb = rebuilt@;
                            rebuilt.push(entry);
                            proof {
                                assert forall|r: int| 0 <= r < rebuilt@.len() implies
                                    #[trigger] rebuilt@[r] == ord.props@[if r < idx as int { r } else { r + 1 }]
                                by {
                                    if r < prev_rb.len() as int {
                                        assert(rebuilt@[r] == prev_rb[r]);
                                    }
                                };
                                assert forall|a: int, b: int| 0 <= a < b < rebuilt@.len()
                                    implies rebuilt@[a].key != rebuilt@[b].key
                                by {
                                    let sa = if a < idx as int { a } else { a + 1 };
                                    let sb = if b < idx as int { b } else { b + 1 };
                                    assert(rebuilt@[a] == ord.props@[sa]);
                                    assert(rebuilt@[b] == ord.props@[sb]);
                                    assert(ord.props@[sa].key != ord.props@[sb].key);
                                };
                            }
                        }
                        i += 1;
                    }
                    proof {
                        assert forall|r: int| 0 <= r < rebuilt@.len()
                            implies (#[trigger] rebuilt@[r]).key != key
                        by {
                            let sr = if r < idx as int { r } else { r + 1 };
                            assert(sr != idx as int);
                            assert(rebuilt@[r] == ord.props@[sr]);
                            assert(ord.props@[sr].key != ord.props@[idx as int].key);
                        };
                        lemma_find_prop_none_when_absent(rebuilt@, key, 0);
                    }
                    ord.props = rebuilt;
                }
                proof {
                    assert forall|i: int| 0 <= i < store.objects@.len()
                        implies spec_obj_kind_wf(store.objects@.len(), #[trigger] &store.objects@[i])
                    by {
                        if i != obj_id as int {
                            assert(&store.objects@[i] == &old_objs[i]);
                            assert(spec_obj_kind_wf(old_objs.len(), &old_objs[i]));
                        }
                    };
                    assert forall|k: int| 0 <= k < old_objs.len() implies match (#[trigger] &old_objs[k], &store.objects@[k]) {
                        (ObjectKind::Proxy(p1), ObjectKind::Proxy(p2)) => p1 == p2,
                        (ObjectKind::Ordinary(o1), ObjectKind::Ordinary(o2)) => {
                            (!o1.extensible ==> !o2.extensible)
                            && match spec_ordinary_own_prop(o1, key) {
                                Some(td) => !spec_desc_configurable(td) ==> spec_ordinary_own_prop(o2, key) == Some(td),
                                None => spec_ordinary_own_prop(o2, key) is None,
                            }
                        },
                        _ => false,
                    } by {
                        if k != obj_id as int {
                            assert(&store.objects@[k] == &old_objs[k]);
                        }
                    };
                }
                Ok(true)
            },
        }
    } else {
        let (tid, hid) = store.validate_non_revoked_proxy(obj_id)?;
        let stub = match resolve_handler_traps(store, hid, fuel - 1)? {
            None => BoolTrapStub::Missing,
            Some(ord_hid) => match &store.objects[ord_hid] {
                ObjectKind::Ordinary(h_ord) => h_ord.traps.delete_property,
                ObjectKind::Proxy(_) => BoolTrapStub::Missing,
            },
        };
        match stub {
            BoolTrapStub::Missing => {
                let r = object_delete(store, tid, key, fuel - 1)?;
                proof {
                    let _ = &old(store).objects@[obj_id as int];
                    let _ = &old(store).objects@[tid as int];
                }
                Ok(r)
            },
            BoolTrapStub::NotCallable => Err(JsError::TypeError),
            BoolTrapStub::Throw(v) => Err(JsError::Thrown(v)),
            BoolTrapStub::MutateTargetAndReturn(b) => {
                let _ = object_delete(store, tid, key, fuel - 1)?;
                if !b {
                    return Ok(false);
                }
                let target_desc = object_get_own_property(store, tid, key, fuel - 1)?;
                proof {
                    let _ = &old(store).objects@[obj_id as int];
                    let _ = &old(store).objects@[tid as int];
                }
                match target_desc {
                    None => Ok(true),
                    Some(_) => {
                        let target_ext = object_is_extensible(store, tid, fuel - 1)?;
                        proxy_validate_delete(true, target_desc, target_ext)
                    },
                }
            },
            BoolTrapStub::SealTargetAndReturn(b) => {
                let seal_res = object_prevent_extensions(store, tid, fuel - 1);
                proof {
                    assert forall|k: int| 0 <= k < old(store).objects@.len()
                        implies match (#[trigger] &old(store).objects@[k], &store.objects@[k]) {
                            (ObjectKind::Proxy(p1), ObjectKind::Proxy(p2)) => p1 == p2,
                            (ObjectKind::Ordinary(o1), ObjectKind::Ordinary(o2)) => {
                                (!o1.extensible ==> !o2.extensible)
                                && match spec_ordinary_own_prop(o1, key) {
                                    Some(td) => !spec_desc_configurable(td) ==> spec_ordinary_own_prop(o2, key) == Some(td),
                                    None => spec_ordinary_own_prop(o2, key) is None,
                                }
                            },
                            _ => false,
                        }
                    by {};
                }
                let _ = seal_res?;
                if !b {
                    return Ok(false);
                }
                let target_desc = object_get_own_property(store, tid, key, fuel - 1)?;
                proof {
                    let _ = &old(store).objects@[obj_id as int];
                    let _ = &old(store).objects@[tid as int];
                }
                match target_desc {
                    None => Ok(true),
                    Some(_) => {
                        let target_ext = object_is_extensible(store, tid, fuel - 1)?;
                        proxy_validate_delete(true, target_desc, target_ext)
                    },
                }
            },
            BoolTrapStub::Return(b) | BoolTrapStub::SetTargetProtoSealAndReturn { ret: b, .. } => {
                if !b {
                    return Ok(false);
                }
                let target_desc = object_get_own_property(store, tid, key, fuel - 1)?;
                match target_desc {
                    None => Ok(true),
                    Some(_) => {
                        let target_ext = object_is_extensible(store, tid, fuel - 1)?;
                        proxy_validate_delete(true, target_desc, target_ext)
                    },
                }
            },
        }
    }
}

/// `O.[[OwnPropertyKeys]]()` (§10.1.11 / §10.5.11):
/// Per ECMA-262 `OrdinaryOwnPropertyKeys`: String keys in creation order first, then Symbol keys in creation order,
/// and for Proxies enforces all §10.5.11 duplicate/non-configurable/non-extensible checks!
pub fn object_own_property_keys(
    store: &ObjectStore,
    obj_id: ObjId,
    fuel: usize,
) -> (res: Result<Vec<PropKey>, JsError>)
    requires
        store.wf(),
        (obj_id as int) < store.objects@.len(),
    ensures
        store.spec_is_revoked_proxy(obj_id) && fuel > 0 ==> res == Err(JsError::TypeError),
        match res {
            Ok(keys) => spec_no_duplicate_keys(keys@),
            Err(_) => true,
        },
    decreases fuel,
{
    if fuel == 0 {
        return Err(JsError::RangeError);
    }
    proof {
        assert(spec_obj_kind_wf(store.objects@.len(), &store.objects@[obj_id as int]));
    }
    match &store.objects[obj_id] {
        ObjectKind::Ordinary(ord) => {
            // Collect String keys first, then Symbol keys; verify uniqueness via check_no_duplicate_keys
            let n = ord.props.len();
            let mut out: Vec<PropKey> = Vec::new();
            let mut i: usize = 0;
            while i < n
                invariant
                    i <= n,
                    n == ord.props@.len(),
                decreases n - i,
            {
                if matches!(ord.props[i].key, PropKey::Str(_)) {
                    out.push(ord.props[i].key);
                }
                i += 1;
            }
            let mut j: usize = 0;
            while j < n
                invariant
                    j <= n,
                    n == ord.props@.len(),
                decreases n - j,
            {
                if matches!(ord.props[j].key, PropKey::Symbol(_)) {
                    out.push(ord.props[j].key);
                }
                j += 1;
            }
            if !check_no_duplicate_keys(out.as_slice()) {
                return Err(JsError::TypeError);
            }
            Ok(out)
        },
        ObjectKind::Proxy(_) => {
            let (tid, hid) = store.validate_non_revoked_proxy(obj_id)?;
            let resolved_hid = resolve_handler_traps(store, hid, fuel - 1)?;
            let trap_mode = match resolved_hid {
                None => 0u8,
                Some(ord_hid) => match &store.objects[ord_hid] {
                    ObjectKind::Ordinary(h_ord) => {
                        match &h_ord.traps.own_keys {
                            OwnKeysTrapStub::Missing => 0u8,
                            OwnKeysTrapStub::NotCallable => 1u8,
                            OwnKeysTrapStub::Throw(_) => 2u8,
                            OwnKeysTrapStub::InvalidReturnType => 3u8,
                            OwnKeysTrapStub::ReturnKeys(_) => 4u8,
                        }
                    },
                    ObjectKind::Proxy(_) => 0u8,
                },
            };
            if trap_mode == 0u8 {
                return object_own_property_keys(store, tid, fuel - 1);
            }
            if trap_mode == 1u8 {
                return Err(JsError::TypeError);
            }
            if trap_mode == 2u8 {
                if let Some(ord_hid) = resolved_hid {
                    if let ObjectKind::Ordinary(h_ord) = &store.objects[ord_hid] {
                        if let OwnKeysTrapStub::Throw(v) = h_ord.traps.own_keys {
                            return Err(JsError::Thrown(v));
                        }
                    }
                }
                return Err(JsError::TypeError);
            }
            if trap_mode == 3u8 {
                let empty: Vec<PropKey> = Vec::new();
                let empty_info: Vec<TargetKeyInfo> = Vec::new();
                return proxy_validate_own_property_keys(false, empty.as_slice(), empty_info.as_slice(), true);
            }
            let raw_keys = match resolved_hid {
                Some(ord_hid) => match &store.objects[ord_hid] {
                    ObjectKind::Ordinary(h_ord) => match &h_ord.traps.own_keys {
                        OwnKeysTrapStub::ReturnKeys(ks) => clone_prop_keys(ks.as_slice()),
                        _ => Vec::new(),
                    },
                    ObjectKind::Proxy(_) => Vec::new(),
                },
                None => Vec::new(),
            };
            let target_ext = object_is_extensible(store, tid, fuel - 1)?;
            let target_key_list = object_own_property_keys(store, tid, fuel - 1)?;
            let tk_len = target_key_list.len();
            let mut target_infos: Vec<TargetKeyInfo> = Vec::new();
            let mut idx: usize = 0;
            while idx < tk_len
                invariant
                    idx <= tk_len,
                    tk_len == target_key_list@.len(),
                    store.wf(),
                    !store.spec_is_revoked_proxy(obj_id),
                    (tid as int) < store.objects@.len(),
                    fuel >= 1,
                decreases tk_len - idx,
            {
                let k = target_key_list[idx];
                let d_opt = object_get_own_property(store, tid, k, fuel - 1)?;
                let conf = match d_opt {
                    Some(d) => desc_configurable(d),
                    None => true,
                };
                target_infos.push(TargetKeyInfo { key: k, configurable: conf });
                idx += 1;
            }
            proxy_validate_own_property_keys(true, raw_keys.as_slice(), target_infos.as_slice(), target_ext)
        },
    }
}

// -----------------------------------------------------------------------------------------------
// Reflect.* Built-in Operations (ECMA-262 §28.1)
// Every Reflect operation throws `TypeError` if `target` is not an Object!
// -----------------------------------------------------------------------------------------------

fn require_object_id(store: &ObjectStore, target: JsVal) -> (res: Result<ObjId, JsError>)
    requires
        store.wf(),
    ensures
        match res {
            Ok(id) => target == JsVal::Object(id) && (id as int) < store.objects@.len(),
            Err(e) => e == JsError::TypeError,
        },
{
    match target {
        JsVal::Object(id) => {
            if id < store.objects.len() {
                Ok(id)
            } else {
                Err(JsError::TypeError)
            }
        },
        _ => Err(JsError::TypeError),
    }
}

/// §28.1.7 `Reflect.getPrototypeOf(target)`
pub fn reflect_get_prototype_of(store: &ObjectStore, target: JsVal, fuel: usize) -> (res: Result<JsVal, JsError>)
    requires
        store.wf(),
{
    let oid = require_object_id(store, target)?;
    let proto = object_get_prototype_of(store, oid, fuel)?;
    match proto {
        None => Ok(JsVal::Null),
        Some(pid) => Ok(JsVal::Object(pid)),
    }
}

/// §28.1.12 `Reflect.setPrototypeOf(target, proto)`
pub fn reflect_set_prototype_of(
    store: &mut ObjectStore,
    target: JsVal,
    proto: JsVal,
    fuel: usize,
) -> (res: Result<bool, JsError>)
    requires
        old(store).wf(),
    ensures
        final(store).wf(),
{
    let oid = require_object_id(store, target)?;
    let new_proto = match proto {
        JsVal::Null => None,
        JsVal::Object(pid) => {
            if pid >= store.objects.len() {
                return Err(JsError::TypeError);
            }
            Some(pid)
        },
        _ => return Err(JsError::TypeError),
    };
    object_set_prototype_of(store, oid, new_proto, fuel)
}

/// §28.1.9 `Reflect.isExtensible(target)`
pub fn reflect_is_extensible(store: &ObjectStore, target: JsVal, fuel: usize) -> (res: Result<bool, JsError>)
    requires
        store.wf(),
{
    let oid = require_object_id(store, target)?;
    object_is_extensible(store, oid, fuel)
}

/// §28.1.10 `Reflect.preventExtensions(target)`
pub fn reflect_prevent_extensions(store: &mut ObjectStore, target: JsVal, fuel: usize) -> (res: Result<bool, JsError>)
    requires
        old(store).wf(),
    ensures
        final(store).wf(),
{
    let oid = require_object_id(store, target)?;
    object_prevent_extensions(store, oid, fuel)
}

/// §28.1.6 `Reflect.getOwnPropertyDescriptor(target, propertyKey)`
pub fn reflect_get_own_property_descriptor(
    store: &ObjectStore,
    target: JsVal,
    key: PropKey,
    fuel: usize,
) -> (res: Result<Option<PropertyDescriptor>, JsError>)
    requires
        store.wf(),
{
    let oid = require_object_id(store, target)?;
    object_get_own_property(store, oid, key, fuel)
}

/// §28.1.3 `Reflect.defineProperty(target, propertyKey, attributes)`
pub fn reflect_define_property(
    store: &mut ObjectStore,
    target: JsVal,
    key: PropKey,
    attributes: PartialDescriptor,
    fuel: usize,
) -> (res: Result<bool, JsError>)
    requires
        old(store).wf(),
    ensures
        final(store).wf(),
{
    let oid = require_object_id(store, target)?;
    object_define_own_property(store, oid, key, attributes, fuel)
}

/// §28.1.8 `Reflect.has(target, propertyKey)`
pub fn reflect_has(store: &ObjectStore, target: JsVal, key: PropKey, fuel: usize) -> (res: Result<bool, JsError>)
    requires
        store.wf(),
{
    let oid = require_object_id(store, target)?;
    object_has_property(store, oid, key, fuel)
}

/// §28.1.5 `Reflect.get(target, propertyKey [, receiver])`
pub fn reflect_get(
    store: &ObjectStore,
    target: JsVal,
    key: PropKey,
    receiver: Option<JsVal>,
    fuel: usize,
) -> (res: Result<JsVal, JsError>)
    requires
        store.wf(),
{
    let oid = require_object_id(store, target)?;
    let recv = match receiver {
        Some(r) => r,
        None => target,
    };
    object_get(store, oid, key, recv, fuel)
}

/// §28.1.11 `Reflect.set(target, propertyKey, V [, receiver])`
pub fn reflect_set(
    store: &mut ObjectStore,
    target: JsVal,
    key: PropKey,
    val: JsVal,
    receiver: Option<JsVal>,
    fuel: usize,
) -> (res: Result<bool, JsError>)
    requires
        old(store).wf(),
    ensures
        final(store).wf(),
{
    let oid = require_object_id(store, target)?;
    let recv = match receiver {
        Some(r) => r,
        None => target,
    };
    object_set(store, oid, key, val, recv, fuel)
}

/// §28.1.4 `Reflect.deleteProperty(target, propertyKey)`
pub fn reflect_delete_property(
    store: &mut ObjectStore,
    target: JsVal,
    key: PropKey,
    fuel: usize,
) -> (res: Result<bool, JsError>)
    requires
        old(store).wf(),
    ensures
        final(store).wf(),
{
    let oid = require_object_id(store, target)?;
    object_delete(store, oid, key, fuel)
}

/// §28.1.11 `Reflect.ownKeys(target)`
pub fn reflect_own_keys(store: &ObjectStore, target: JsVal, fuel: usize) -> (res: Result<Vec<PropKey>, JsError>)
    requires
        store.wf(),
    ensures
        match res {
            Ok(keys) => spec_no_duplicate_keys(keys@),
            Err(_) => true,
        },
{
    let oid = require_object_id(store, target)?;
    object_own_property_keys(store, oid, fuel)
}

// -----------------------------------------------------------------------------------------------
// Master §6.1.7.3 Trap Validation Invariant Theorems (Universally Quantified over Malicious Traps)
// -----------------------------------------------------------------------------------------------

/// Theorem (§6.1.7.3 Master Trap Soundness):
/// Even for arbitrary/malicious handler trap outputs:
/// 1. `isExtensible` cannot disagree with `target.isExtensible`.
/// 2. `preventExtensions` cannot report `true` while `target` remains extensible.
/// 3. `getPrototypeOf` & `setPrototypeOf` cannot report a prototype differing from a non-extensible target's prototype.
/// 4. `getOwnPropertyDescriptor` & `hasProperty` cannot hide a non-configurable target property or any own property of a non-extensible target.
/// 5. `get` cannot report a value `!SameValue(v, target.value)` on a non-configurable non-writable target data property,
///    nor a non-`undefined` value on a non-configurable getter-less target accessor property.
/// 6. `deleteProperty` cannot report `true` for a non-configurable target property or own property of a non-extensible target.
pub proof fn theorem_proxy_essential_invariants_against_malicious_traps(
    malicious_bool: bool,
    malicious_val: JsVal,
    malicious_proto: ProtoTrapOutput,
    malicious_desc: OwnPropDescTrapOutput,
    malicious_define: PartialDescriptor,
    target_desc: Option<PropertyDescriptor>,
    target_extensible: bool,
    target_proto: Option<ObjId>,
)
    ensures
        // [[IsExtensible]]: trap_bool != target_extensible ALWAYS rejects with TypeError
        malicious_bool != target_extensible
            ==> spec_validate_is_extensible(malicious_bool, target_extensible) == Err::<bool, JsError>(JsError::TypeError),
        // [[PreventExtensions]]: trap_bool == true && target_extensible ALWAYS rejects with TypeError
        (malicious_bool && target_extensible)
            ==> spec_validate_prevent_extensions(malicious_bool, target_extensible) == Err::<bool, JsError>(JsError::TypeError),
        // [[GetPrototypeOf]]: non-extensible target forces exact target_proto
        (!target_extensible && spec_validate_get_prototype_of(malicious_proto, target_extensible, target_proto) is Ok)
            ==> spec_validate_get_prototype_of(malicious_proto, target_extensible, target_proto) == Ok::<Option<ObjId>, JsError>(target_proto),
        // [[GetOwnProperty]]: hiding non-configurable target property ALWAYS rejects with TypeError
        (target_desc is Some && !spec_desc_configurable(target_desc.unwrap()))
            ==> spec_validate_get_own_property(OwnPropDescTrapOutput::Undefined, target_desc, target_extensible)
                == Err::<Option<PropertyDescriptor>, JsError>(JsError::TypeError),
        // [[HasProperty]]: hiding non-configurable target property ALWAYS rejects with TypeError
        (target_desc is Some && !spec_desc_configurable(target_desc.unwrap()))
            ==> spec_validate_has_property(false, target_desc, target_extensible)
                == Err::<bool, JsError>(JsError::TypeError),
        // [[Get]]: returning !SameValue on non-configurable non-writable data property ALWAYS rejects with TypeError
        match target_desc {
            Some(PropertyDescriptor::Data { value: tv, writable: false, configurable: false, .. }) =>
                !crate::types::spec_same_value(malicious_val, tv)
                    ==> spec_validate_get(malicious_val, target_desc) == Err::<JsVal, JsError>(JsError::TypeError),
            Some(PropertyDescriptor::Accessor { get: None, configurable: false, .. }) =>
                malicious_val != JsVal::Undefined
                    ==> spec_validate_get(malicious_val, target_desc) == Err::<JsVal, JsError>(JsError::TypeError),
            _ => true,
        },
        // [[Delete]]: reporting true on non-configurable target property ALWAYS rejects with TypeError
        (target_desc is Some && !spec_desc_configurable(target_desc.unwrap()))
            ==> spec_validate_delete(true, target_desc, target_extensible)
                == Err::<bool, JsError>(JsError::TypeError),
        // [[DefineOwnProperty]]: adding property to non-extensible target or forging non-configurable property ALWAYS rejects
        (target_desc is None && (!target_extensible || malicious_define.configurable == Some(false)) && spec_valid_partial_descriptor(malicious_define))
            ==> spec_validate_define_own_property(true, malicious_define, target_desc, target_extensible)
                == Err::<bool, JsError>(JsError::TypeError),
{
}

} // verus!
