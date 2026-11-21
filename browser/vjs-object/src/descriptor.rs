//! ECMAScript Property Descriptors (`ECMA-262 §6.2.6`) and
//! `ValidateAndApplyPropertyDescriptor` (`§10.1.6.3`), with machine-checked `exec == spec`
//! and non-configurable transition invariants.
use crate::value::{
    clone_js_val, same_value, JsError, JsVal, JsValView, ObjId,
};
#[cfg(verus_keep_ghost)]
use crate::value::{lemma_same_value_refl, spec_same_value};
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------------------
// Complete Stored Property Descriptor (`§6.1.7.1`)
// ---------------------------------------------------------------------------------------

pub enum CompleteDescView {
    Data {
        value: JsValView,
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

/// Complete property record stored in an ECMAScript object's own property table (`§6.1.7.1`).
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum CompleteDescriptor {
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

impl View for CompleteDescriptor {
    type V = CompleteDescView;

    open spec fn view(&self) -> CompleteDescView {
        match self {
            CompleteDescriptor::Data { value, writable, enumerable, configurable } =>
                CompleteDescView::Data {
                    value: value@,
                    writable: *writable,
                    enumerable: *enumerable,
                    configurable: *configurable,
                },
            CompleteDescriptor::Accessor { get, set, enumerable, configurable } =>
                CompleteDescView::Accessor {
                    get: *get,
                    set: *set,
                    enumerable: *enumerable,
                    configurable: *configurable,
                },
        }
    }
}

pub open spec fn spec_complete_is_data(d: CompleteDescView) -> bool {
    match d {
        CompleteDescView::Data { .. } => true,
        CompleteDescView::Accessor { .. } => false,
    }
}

pub open spec fn spec_complete_is_accessor(d: CompleteDescView) -> bool {
    match d {
        CompleteDescView::Data { .. } => false,
        CompleteDescView::Accessor { .. } => true,
    }
}

pub open spec fn spec_complete_enumerable(d: CompleteDescView) -> bool {
    match d {
        CompleteDescView::Data { enumerable, .. } => enumerable,
        CompleteDescView::Accessor { enumerable, .. } => enumerable,
    }
}

pub open spec fn spec_complete_configurable(d: CompleteDescView) -> bool {
    match d {
        CompleteDescView::Data { configurable, .. } => configurable,
        CompleteDescView::Accessor { configurable, .. } => configurable,
    }
}

pub fn clone_complete_descriptor(d: &CompleteDescriptor) -> (out: CompleteDescriptor)
    ensures
        out@ == d@,
{
    match d {
        CompleteDescriptor::Data { value, writable, enumerable, configurable } =>
            CompleteDescriptor::Data {
                value: clone_js_val(value),
                writable: *writable,
                enumerable: *enumerable,
                configurable: *configurable,
            },
        CompleteDescriptor::Accessor { get, set, enumerable, configurable } =>
            CompleteDescriptor::Accessor {
                get: *get,
                set: *set,
                enumerable: *enumerable,
                configurable: *configurable,
            },
    }
}

impl CompleteDescriptor {
    pub fn is_data(&self) -> (r: bool)
        ensures
            r == spec_complete_is_data(self@),
    {
        match self {
            CompleteDescriptor::Data { .. } => true,
            CompleteDescriptor::Accessor { .. } => false,
        }
    }

    pub fn is_accessor(&self) -> (r: bool)
        ensures
            r == spec_complete_is_accessor(self@),
    {
        match self {
            CompleteDescriptor::Data { .. } => false,
            CompleteDescriptor::Accessor { .. } => true,
        }
    }

    pub fn enumerable(&self) -> (r: bool)
        ensures
            r == spec_complete_enumerable(self@),
    {
        match self {
            CompleteDescriptor::Data { enumerable, .. } => *enumerable,
            CompleteDescriptor::Accessor { enumerable, .. } => *enumerable,
        }
    }

    pub fn configurable(&self) -> (r: bool)
        ensures
            r == spec_complete_configurable(self@),
    {
        match self {
            CompleteDescriptor::Data { configurable, .. } => *configurable,
            CompleteDescriptor::Accessor { configurable, .. } => *configurable,
        }
    }
}

// ---------------------------------------------------------------------------------------
// Partial / Generic PropertyDescriptor (`§6.2.6`)
// ---------------------------------------------------------------------------------------

pub struct PropDescView {
    pub value: Option<JsValView>,
    pub writable: Option<bool>,
    pub get: Option<Option<ObjId>>,
    pub set: Option<Option<ObjId>>,
    pub enumerable: Option<bool>,
    pub configurable: Option<bool>,
}

/// ECMA-262 §6.2.6 Property Descriptor Record (each attribute may be absent (`None`) or present (`Some`)).
/// For `get` and `set`: `None` means the field is absent; `Some(None)` means `undefined`;
/// `Some(Some(id))` means callable function object `id`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct PropertyDescriptor {
    pub value: Option<JsVal>,
    pub writable: Option<bool>,
    pub get: Option<Option<ObjId>>,
    pub set: Option<Option<ObjId>>,
    pub enumerable: Option<bool>,
    pub configurable: Option<bool>,
}

impl View for PropertyDescriptor {
    type V = PropDescView;

    open spec fn view(&self) -> PropDescView {
        PropDescView {
            value: match &self.value {
                None => None,
                Some(v) => Some(v@),
            },
            writable: self.writable,
            get: self.get,
            set: self.set,
            enumerable: self.enumerable,
            configurable: self.configurable,
        }
    }
}

pub fn clone_property_descriptor(d: &PropertyDescriptor) -> (out: PropertyDescriptor)
    ensures
        out@ == d@,
{
    PropertyDescriptor {
        value: match &d.value {
            None => None,
            Some(v) => Some(clone_js_val(v)),
        },
        writable: d.writable,
        get: d.get,
        set: d.set,
        enumerable: d.enumerable,
        configurable: d.configurable,
    }
}

impl PropertyDescriptor {
    pub fn empty() -> (d: PropertyDescriptor)
        ensures
            spec_is_empty_descriptor(d@),
            prop_desc_wf(d@),
    {
        PropertyDescriptor {
            value: None,
            writable: None,
            get: None,
            set: None,
            enumerable: None,
            configurable: None,
        }
    }

    pub fn data(
        value: JsVal,
        writable: bool,
        enumerable: bool,
        configurable: bool,
    ) -> (d: PropertyDescriptor)
        ensures
            d@ == (PropDescView {
                value: Some(value@),
                writable: Some(writable),
                get: None,
                set: None,
                enumerable: Some(enumerable),
                configurable: Some(configurable),
            }),
            spec_is_data_descriptor(d@),
            prop_desc_wf(d@),
    {
        PropertyDescriptor {
            value: Some(value),
            writable: Some(writable),
            get: None,
            set: None,
            enumerable: Some(enumerable),
            configurable: Some(configurable),
        }
    }

    pub fn accessor(
        get: Option<ObjId>,
        set: Option<ObjId>,
        enumerable: bool,
        configurable: bool,
    ) -> (d: PropertyDescriptor)
        ensures
            d@ == (PropDescView {
                value: None,
                writable: None,
                get: Some(get),
                set: Some(set),
                enumerable: Some(enumerable),
                configurable: Some(configurable),
            }),
            spec_is_accessor_descriptor(d@),
            prop_desc_wf(d@),
    {
        PropertyDescriptor {
            value: None,
            writable: None,
            get: Some(get),
            set: Some(set),
            enumerable: Some(enumerable),
            configurable: Some(configurable),
        }
    }
}

/// ECMA-262 §6.2.6.1 `IsAccessorDescriptor ( Desc )`.
pub open spec fn spec_is_accessor_descriptor(desc: PropDescView) -> bool {
    desc.get is Some || desc.set is Some
}

/// ECMA-262 §6.2.6.2 `IsDataDescriptor ( Desc )`.
pub open spec fn spec_is_data_descriptor(desc: PropDescView) -> bool {
    desc.value is Some || desc.writable is Some
}

/// ECMA-262 §6.2.6.3 `IsGenericDescriptor ( Desc )`.
pub open spec fn spec_is_generic_descriptor(desc: PropDescView) -> bool {
    !spec_is_accessor_descriptor(desc) && !spec_is_data_descriptor(desc)
}

pub open spec fn spec_is_empty_descriptor(desc: PropDescView) -> bool {
    desc.value is None
        && desc.writable is None
        && desc.get is None
        && desc.set is None
        && desc.enumerable is None
        && desc.configurable is None
}

/// ECMA-262 §6.2.6.5 step 22: a valid PropertyDescriptor cannot simultaneously be
/// both a Data Descriptor and an Accessor Descriptor.
pub open spec fn prop_desc_wf(desc: PropDescView) -> bool {
    !(spec_is_data_descriptor(desc) && spec_is_accessor_descriptor(desc))
}

pub proof fn lemma_descriptor_kind_partition(desc: PropDescView)
    requires
        prop_desc_wf(desc),
    ensures
        (spec_is_data_descriptor(desc) && !spec_is_accessor_descriptor(desc) && !spec_is_generic_descriptor(desc))
        || (!spec_is_data_descriptor(desc) && spec_is_accessor_descriptor(desc) && !spec_is_generic_descriptor(desc))
        || (!spec_is_data_descriptor(desc) && !spec_is_accessor_descriptor(desc) && spec_is_generic_descriptor(desc)),
{
}

pub fn is_accessor_descriptor(desc: &PropertyDescriptor) -> (r: bool)
    ensures
        r == spec_is_accessor_descriptor(desc@),
{
    desc.get.is_some() || desc.set.is_some()
}

pub fn is_data_descriptor(desc: &PropertyDescriptor) -> (r: bool)
    ensures
        r == spec_is_data_descriptor(desc@),
{
    desc.value.is_some() || desc.writable.is_some()
}

pub fn is_generic_descriptor(desc: &PropertyDescriptor) -> (r: bool)
    ensures
        r == spec_is_generic_descriptor(desc@),
{
    !is_accessor_descriptor(desc) && !is_data_descriptor(desc)
}

pub fn is_empty_descriptor(desc: &PropertyDescriptor) -> (r: bool)
    ensures
        r == spec_is_empty_descriptor(desc@),
{
    desc.value.is_none()
        && desc.writable.is_none()
        && desc.get.is_none()
        && desc.set.is_none()
        && desc.enumerable.is_none()
        && desc.configurable.is_none()
}

/// Validates §6.2.6.5 step 22 (`ToPropertyDescriptor` mixed data/accessor rejection -> `TypeError`).
pub fn validate_descriptor_fields(desc: &PropertyDescriptor) -> (res: Result<(), JsError>)
    ensures
        (res is Ok) <==> prop_desc_wf(desc@),
        res is Err ==> res == Err::<(), JsError>(JsError::TypeError),
{
    if is_data_descriptor(desc) && is_accessor_descriptor(desc) {
        Err(JsError::TypeError)
    } else {
        Ok(())
    }
}

/// ECMA-262 §6.2.6.4 `FromPropertyDescriptor ( Desc )`.
pub open spec fn spec_from_complete_descriptor(d: CompleteDescView) -> PropDescView {
    match d {
        CompleteDescView::Data { value, writable, enumerable, configurable } =>
            PropDescView {
                value: Some(value),
                writable: Some(writable),
                get: None,
                set: None,
                enumerable: Some(enumerable),
                configurable: Some(configurable),
            },
        CompleteDescView::Accessor { get, set, enumerable, configurable } =>
            PropDescView {
                value: None,
                writable: None,
                get: Some(get),
                set: Some(set),
                enumerable: Some(enumerable),
                configurable: Some(configurable),
            },
    }
}

pub fn from_complete_descriptor(d: &CompleteDescriptor) -> (out: PropertyDescriptor)
    ensures
        out@ == spec_from_complete_descriptor(d@),
        prop_desc_wf(out@),
{
    match d {
        CompleteDescriptor::Data { value, writable, enumerable, configurable } =>
            PropertyDescriptor::data(clone_js_val(value), *writable, *enumerable, *configurable),
        CompleteDescriptor::Accessor { get, set, enumerable, configurable } =>
            PropertyDescriptor::accessor(*get, *set, *enumerable, *configurable),
    }
}

/// ECMA-262 §6.2.6.6 `CompletePropertyDescriptor ( Desc )` producing a `CompleteDescriptor`.
pub open spec fn spec_complete_to_stored(desc: PropDescView) -> CompleteDescView {
    if spec_is_generic_descriptor(desc) || spec_is_data_descriptor(desc) {
        CompleteDescView::Data {
            value: match desc.value {
                Some(v) => v,
                None => JsValView::Undefined,
            },
            writable: match desc.writable {
                Some(w) => w,
                None => false,
            },
            enumerable: match desc.enumerable {
                Some(e) => e,
                None => false,
            },
            configurable: match desc.configurable {
                Some(c) => c,
                None => false,
            },
        }
    } else {
        CompleteDescView::Accessor {
            get: match desc.get {
                Some(g) => g,
                None => None,
            },
            set: match desc.set {
                Some(s) => s,
                None => None,
            },
            enumerable: match desc.enumerable {
                Some(e) => e,
                None => false,
            },
            configurable: match desc.configurable {
                Some(c) => c,
                None => false,
            },
        }
    }
}

pub open spec fn spec_complete_property_descriptor(desc: PropDescView) -> PropDescView {
    spec_from_complete_descriptor(spec_complete_to_stored(desc))
}

pub fn complete_to_stored(desc: &PropertyDescriptor) -> (out: CompleteDescriptor)
    requires
        prop_desc_wf(desc@),
    ensures
        out@ == spec_complete_to_stored(desc@),
{
    if is_generic_descriptor(desc) || is_data_descriptor(desc) {
        let val = match &desc.value {
            Some(v) => clone_js_val(v),
            None => JsVal::Undefined,
        };
        let writable = match desc.writable {
            Some(w) => w,
            None => false,
        };
        let enumerable = match desc.enumerable {
            Some(e) => e,
            None => false,
        };
        let configurable = match desc.configurable {
            Some(c) => c,
            None => false,
        };
        CompleteDescriptor::Data { value: val, writable, enumerable, configurable }
    } else {
        let get = match desc.get {
            Some(g) => g,
            None => None,
        };
        let set = match desc.set {
            Some(s) => s,
            None => None,
        };
        let enumerable = match desc.enumerable {
            Some(e) => e,
            None => false,
        };
        let configurable = match desc.configurable {
            Some(c) => c,
            None => false,
        };
        CompleteDescriptor::Accessor { get, set, enumerable, configurable }
    }
}

/// ECMA-262 §6.2.6.6 `CompletePropertyDescriptor ( Desc )`.
pub fn complete_property_descriptor(desc: &PropertyDescriptor) -> (out: PropertyDescriptor)
    requires
        prop_desc_wf(desc@),
    ensures
        out@ == spec_complete_property_descriptor(desc@),
        prop_desc_wf(out@),
{
    let stored = complete_to_stored(desc);
    from_complete_descriptor(&stored)
}

// ---------------------------------------------------------------------------------------
// ValidateAndApplyPropertyDescriptor (`ECMA-262 §10.1.6.3`)
// ---------------------------------------------------------------------------------------

/// ECMA-262 §10.1.6.3 `ValidateAndApplyPropertyDescriptor ( O, P, extensible, Desc, current )`.
/// When `apply == true` (`O` is an Object), returns `(true, Some(updated_desc))` on success.
/// When `apply == false` (`O` is `undefined`, §10.1.6.2 `IsCompatiblePropertyDescriptor`),
/// returns `(true, current)` on success.
/// On validation failure, always returns `(false, current)` with `current` unchanged.
pub open spec fn spec_validate_and_apply_property_descriptor(
    apply: bool,
    extensible: bool,
    desc: PropDescView,
    current: Option<CompleteDescView>,
) -> (bool, Option<CompleteDescView>) {
    if !prop_desc_wf(desc) {
        (false, current)
    } else {
        match current {
            // Step 2: If current is undefined
            None => {
                if !extensible {
                    (false, None)
                } else if !apply {
                    (true, None)
                } else {
                    (true, Some(spec_complete_to_stored(desc)))
                }
            },
            // Step 3: current is a fully populated Property Descriptor
            Some(cur) => {
                // Step 4: If Desc has no fields, return true
                if spec_is_empty_descriptor(desc) {
                    (true, Some(cur))
                } else {
                    // Step 5: If current.[[Configurable]] is false
                    let compat_ok = if !spec_complete_configurable(cur) {
                        // 5a: Desc.[[Configurable]] is true -> false
                        if desc.configurable == Some(true) {
                            false
                        }
                        // 5b: Desc.[[Enumerable]] != current.[[Enumerable]] -> false
                        else if desc.enumerable is Some
                            && desc.enumerable.unwrap() != spec_complete_enumerable(cur)
                        {
                            false
                        }
                        // 5c: !IsGenericDescriptor(Desc) && IsAccessor(Desc) != IsAccessor(current) -> false
                        else if !spec_is_generic_descriptor(desc)
                            && spec_is_accessor_descriptor(desc) != spec_complete_is_accessor(cur)
                        {
                            false
                        } else {
                            match cur {
                                // 5d: current is Accessor -> SameValue check on [[Get]] and [[Set]]
                                CompleteDescView::Accessor { get: cg, set: cs, .. } => {
                                    let get_ok = match desc.get {
                                        None => true,
                                        Some(dg) => dg == cg,
                                    };
                                    let set_ok = match desc.set {
                                        None => true,
                                        Some(ds) => ds == cs,
                                    };
                                    get_ok && set_ok
                                },
                                // 5e: current is Data -> if !current.[[Writable]], forbid writable=true and non-SameValue
                                CompleteDescView::Data { value: cv, writable: cw, .. } => {
                                    if !cw {
                                        if desc.writable == Some(true) {
                                            false
                                        } else {
                                            match desc.value {
                                                None => true,
                                                Some(dv) => spec_same_value(dv, cv),
                                            }
                                        }
                                    } else {
                                        true
                                    }
                                },
                            }
                        }
                    } else {
                        true
                    };

                    if !compat_ok {
                        (false, Some(cur))
                    } else if !apply {
                        (true, Some(cur))
                    } else {
                        // Step 6: Apply updates to O's property
                        let updated = match cur {
                            CompleteDescView::Data {
                                value: cv,
                                writable: cw,
                                enumerable: ce,
                                configurable: cc,
                            } => {
                                if spec_is_accessor_descriptor(desc) {
                                    // Step 6a: Convert configurable Data -> Accessor
                                    CompleteDescView::Accessor {
                                        get: match desc.get {
                                            Some(g) => g,
                                            None => None,
                                        },
                                        set: match desc.set {
                                            Some(s) => s,
                                            None => None,
                                        },
                                        enumerable: match desc.enumerable {
                                            Some(e) => e,
                                            None => ce,
                                        },
                                        configurable: match desc.configurable {
                                            Some(c) => c,
                                            None => cc,
                                        },
                                    }
                                } else {
                                    // Step 6c (Data)
                                    CompleteDescView::Data {
                                        value: match desc.value {
                                            Some(v) => v,
                                            None => cv,
                                        },
                                        writable: match desc.writable {
                                            Some(w) => w,
                                            None => cw,
                                        },
                                        enumerable: match desc.enumerable {
                                            Some(e) => e,
                                            None => ce,
                                        },
                                        configurable: match desc.configurable {
                                            Some(c) => c,
                                            None => cc,
                                        },
                                    }
                                }
                            },
                            CompleteDescView::Accessor {
                                get: cg,
                                set: cs,
                                enumerable: ce,
                                configurable: cc,
                            } => {
                                if spec_is_data_descriptor(desc) {
                                    // Step 6b: Convert configurable Accessor -> Data
                                    CompleteDescView::Data {
                                        value: match desc.value {
                                            Some(v) => v,
                                            None => JsValView::Undefined,
                                        },
                                        writable: match desc.writable {
                                            Some(w) => w,
                                            None => false,
                                        },
                                        enumerable: match desc.enumerable {
                                            Some(e) => e,
                                            None => ce,
                                        },
                                        configurable: match desc.configurable {
                                            Some(c) => c,
                                            None => cc,
                                        },
                                    }
                                } else {
                                    // Step 6c (Accessor)
                                    CompleteDescView::Accessor {
                                        get: match desc.get {
                                            Some(g) => g,
                                            None => cg,
                                        },
                                        set: match desc.set {
                                            Some(s) => s,
                                            None => cs,
                                        },
                                        enumerable: match desc.enumerable {
                                            Some(e) => e,
                                            None => ce,
                                        },
                                        configurable: match desc.configurable {
                                            Some(c) => c,
                                            None => cc,
                                        },
                                    }
                                }
                            },
                        };
                        (true, Some(updated))
                    }
                }
            },
        }
    }
}

pub open spec fn spec_is_compatible_property_descriptor(
    extensible: bool,
    desc: PropDescView,
    current: Option<CompleteDescView>,
) -> bool {
    spec_validate_and_apply_property_descriptor(false, extensible, desc, current).0
}

fn opt_obj_id_eq(a: Option<ObjId>, b: Option<ObjId>) -> (r: bool)
    ensures
        r == (a == b),
{
    match (a, b) {
        (None, None) => true,
        (Some(x), Some(y)) => x.0 == y.0,
        _ => false,
    }
}

/// Executable `ValidateAndApplyPropertyDescriptor` (§10.1.6.3), proved equal to
/// `spec_validate_and_apply_property_descriptor`.
pub fn validate_and_apply_property_descriptor(
    apply: bool,
    extensible: bool,
    desc: &PropertyDescriptor,
    current: &Option<CompleteDescriptor>,
) -> (res: (bool, Option<CompleteDescriptor>))
    requires
        prop_desc_wf(desc@),
    ensures
        ({
            let cur_view = match current {
                None => None,
                Some(c) => Some(c@),
            };
            let out_view = match &res.1 {
                None => None,
                Some(c) => Some(c@),
            };
            (res.0, out_view)
                == spec_validate_and_apply_property_descriptor(apply, extensible, desc@, cur_view)
        }),
{
    match current {
        None => {
            if !extensible {
                (false, None)
            } else if !apply {
                (true, None)
            } else {
                (true, Some(complete_to_stored(desc)))
            }
        },
        Some(cur) => {
            if is_empty_descriptor(desc) {
                return (true, Some(clone_complete_descriptor(cur)));
            }

            let cfg_is_true = match desc.configurable {
                Some(c) => c,
                None => false,
            };
            let enum_mismatch = match desc.enumerable {
                Some(e) => e != cur.enumerable(),
                None => false,
            };

            let compat_ok: bool = if !cur.configurable() {
                if cfg_is_true {
                    false
                } else if enum_mismatch {
                    false
                } else if !is_generic_descriptor(desc)
                    && is_accessor_descriptor(desc) != cur.is_accessor()
                {
                    false
                } else {
                    match cur {
                        CompleteDescriptor::Accessor { get: cg, set: cs, .. } => {
                            let get_ok = match desc.get {
                                None => true,
                                Some(dg) => opt_obj_id_eq(dg, *cg),
                            };
                            let set_ok = match desc.set {
                                None => true,
                                Some(ds) => opt_obj_id_eq(ds, *cs),
                            };
                            get_ok && set_ok
                        },
                        CompleteDescriptor::Data { value: cv, writable: cw, .. } => {
                            if !*cw {
                                let wr_is_true = match desc.writable {
                                    Some(w) => w,
                                    None => false,
                                };
                                if wr_is_true {
                                    false
                                } else {
                                    match &desc.value {
                                        None => true,
                                        Some(dv) => same_value(dv, cv),
                                    }
                                }
                            } else {
                                true
                            }
                        },
                    }
                }
            } else {
                true
            };

            if !compat_ok {
                return (false, Some(clone_complete_descriptor(cur)));
            }
            if !apply {
                return (true, Some(clone_complete_descriptor(cur)));
            }

            let updated = match cur {
                CompleteDescriptor::Data {
                    value: cv,
                    writable: cw,
                    enumerable: ce,
                    configurable: cc,
                } => {
                    if is_accessor_descriptor(desc) {
                        CompleteDescriptor::Accessor {
                            get: match desc.get {
                                Some(g) => g,
                                None => None,
                            },
                            set: match desc.set {
                                Some(s) => s,
                                None => None,
                            },
                            enumerable: match desc.enumerable {
                                Some(e) => e,
                                None => *ce,
                            },
                            configurable: match desc.configurable {
                                Some(c) => c,
                                None => *cc,
                            },
                        }
                    } else {
                        CompleteDescriptor::Data {
                            value: match &desc.value {
                                Some(v) => clone_js_val(v),
                                None => clone_js_val(cv),
                            },
                            writable: match desc.writable {
                                Some(w) => w,
                                None => *cw,
                            },
                            enumerable: match desc.enumerable {
                                Some(e) => e,
                                None => *ce,
                            },
                            configurable: match desc.configurable {
                                Some(c) => c,
                                None => *cc,
                            },
                        }
                    }
                },
                CompleteDescriptor::Accessor {
                    get: cg,
                    set: cs,
                    enumerable: ce,
                    configurable: cc,
                } => {
                    if is_data_descriptor(desc) {
                        CompleteDescriptor::Data {
                            value: match &desc.value {
                                Some(v) => clone_js_val(v),
                                None => JsVal::Undefined,
                            },
                            writable: match desc.writable {
                                Some(w) => w,
                                None => false,
                            },
                            enumerable: match desc.enumerable {
                                Some(e) => e,
                                None => *ce,
                            },
                            configurable: match desc.configurable {
                                Some(c) => c,
                                None => *cc,
                            },
                        }
                    } else {
                        CompleteDescriptor::Accessor {
                            get: match desc.get {
                                Some(g) => g,
                                None => *cg,
                            },
                            set: match desc.set {
                                Some(s) => s,
                                None => *cs,
                            },
                            enumerable: match desc.enumerable {
                                Some(e) => e,
                                None => *ce,
                            },
                            configurable: match desc.configurable {
                                Some(c) => c,
                                None => *cc,
                            },
                        }
                    }
                },
            };
            (true, Some(updated))
        },
    }
}

/// ECMA-262 §10.1.6.2 `IsCompatiblePropertyDescriptor ( Extensible, Desc, Current )`.
pub fn is_compatible_property_descriptor(
    extensible: bool,
    desc: &PropertyDescriptor,
    current: &Option<CompleteDescriptor>,
) -> (r: bool)
    requires
        prop_desc_wf(desc@),
    ensures
        ({
            let cur_view = match current {
                None => None,
                Some(c) => Some(c@),
            };
            r == spec_is_compatible_property_descriptor(extensible, desc@, cur_view)
        }),
{
    let (ok, _) = validate_and_apply_property_descriptor(false, extensible, desc, current);
    ok
}

// ---------------------------------------------------------------------------------------
// Core §10.1.6.3 / §6.1.7.3 Descriptor Transition Lemmas
// ---------------------------------------------------------------------------------------

/// Proves that `ValidateAndApplyPropertyDescriptor` preserves ALL §6.1.7.3 invariants
/// for any non-configurable property `cur`.
pub proof fn lemma_validate_nonconfigurable_invariants(
    apply: bool,
    extensible: bool,
    desc: PropDescView,
    cur: CompleteDescView,
)
    requires
        !spec_complete_configurable(cur),
    ensures
        ({
            let (_, out) = spec_validate_and_apply_property_descriptor(apply, extensible, desc, Some(cur));
            out is Some
            && ({
                let nc = out.unwrap();
                !spec_complete_configurable(nc)
                && spec_complete_enumerable(nc) == spec_complete_enumerable(cur)
                && spec_complete_is_data(nc) == spec_complete_is_data(cur)
                && spec_complete_is_accessor(nc) == spec_complete_is_accessor(cur)
                && (match (cur, nc) {
                    (
                        CompleteDescView::Data { value: cv, writable: cw, .. },
                        CompleteDescView::Data { value: nv, writable: nw, .. },
                    ) => (!cw ==> (!nw && spec_same_value(nv, cv))),
                    (
                        CompleteDescView::Accessor { get: cg, set: cs, .. },
                        CompleteDescView::Accessor { get: ng, set: ns, .. },
                    ) => ng == cg && ns == cs,
                    _ => false,
                })
            })
        }),
{
    if let CompleteDescView::Data { value: cv, .. } = cur {
        lemma_same_value_refl(cv);
    }
}

/// Explicit theorem: when `configurable == false`, `writable` `true -> false` is ALLOWED,
/// whereas `writable` `false -> true` is FORBIDDEN.
pub proof fn lemma_writable_transition_asymmetry(val: JsValView, enumerable: bool, extensible: bool)
    ensures
        ({
            let cur_writable = CompleteDescView::Data {
                value: val,
                writable: true,
                enumerable,
                configurable: false,
            };
            let cur_nonwritable = CompleteDescView::Data {
                value: val,
                writable: false,
                enumerable,
                configurable: false,
            };
            let to_false = PropDescView {
                value: None,
                writable: Some(false),
                get: None,
                set: None,
                enumerable: None,
                configurable: None,
            };
            let to_true = PropDescView {
                value: None,
                writable: Some(true),
                get: None,
                set: None,
                enumerable: None,
                configurable: None,
            };
            spec_validate_and_apply_property_descriptor(true, extensible, to_false, Some(cur_writable))
                == (true, Some(cur_nonwritable))
            && spec_validate_and_apply_property_descriptor(true, extensible, to_true, Some(cur_nonwritable))
                == (false, Some(cur_nonwritable))
        }),
{
}

/// Explicit theorem: when `configurable == false`, Data <-> Accessor transition is ALWAYS refused.
pub proof fn lemma_data_accessor_transition_refused_when_nonconfigurable(
    extensible: bool,
    desc: PropDescView,
    cur: CompleteDescView,
)
    requires
        prop_desc_wf(desc),
        !spec_complete_configurable(cur),
        (spec_complete_is_data(cur) && spec_is_accessor_descriptor(desc))
            || (spec_complete_is_accessor(cur) && spec_is_data_descriptor(desc)),
    ensures
        spec_validate_and_apply_property_descriptor(true, extensible, desc, Some(cur))
            == (false, Some(cur)),
{
}

} // verus!
