//! ECMA-262 §6.1 Primitive Language Values & §7.1 / §7.2 Type Conversion and Equality Operations.
//!
//! Models ECMAScript primitive values (`JsPrim`) and verifies `exec == spec` plus non-trivial
//! equivalence, symmetry, and refinement theorems for:
//! - `ToBoolean` (§7.1.2)
//! - `ToPrimitive` & `OrdinaryToPrimitive` (§7.1.1, §7.1.1.1) with explicit object caller hooks
//! - `ToNumeric` (§7.1.3) & `ToNumber` (§7.1.4)
//! - `ToString` (§7.1.17) & `typeof` (§13.5.3)
//! - `SameValue` (§7.2.10) & `SameValueZero` (§7.2.11)
//! - `IsLooselyEqual` (§7.2.14) & `IsStrictlyEqual` (§7.2.15)

use crate::bigint::{string_to_bigint, JsBigInt, SpecBigInt};
#[cfg(verus_keep_ghost)]
use crate::bigint::{spec_bigint_eq, spec_bigint_to_string_radix, spec_string_to_bigint};
use crate::number::{number_to_string, string_to_number, JsNumber};
#[cfg(verus_keep_ghost)]
use crate::number::{
    lemma_number_same_value_equivalence, lemma_number_same_value_zero_equivalence, spec_is_nan,
    spec_is_zero, spec_number_equal, spec_number_same_value, spec_number_same_value_zero,
    spec_number_to_exact_bigint, spec_number_to_string, spec_string_to_number,
};
use crate::utf16::Utf16Str;
use vstd::prelude::*;

verus! {

/// ECMAScript primitive value (`§6.1.1–§6.1.6`).
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum JsPrim {
    Undefined,
    Null,
    Bool(bool),
    Number(JsNumber),
    BigInt(JsBigInt),
    Str(Utf16Str),
    Symbol(u64),
}

/// Ghost model of `JsPrim`.
pub enum SpecPrim {
    Undefined,
    Null,
    Bool(bool),
    Number(JsNumber),
    BigInt(SpecBigInt),
    Str(Seq<u16>),
    Symbol(u64),
}

impl View for JsPrim {
    type V = SpecPrim;

    open spec fn view(&self) -> SpecPrim {
        match self {
            JsPrim::Undefined => SpecPrim::Undefined,
            JsPrim::Null => SpecPrim::Null,
            JsPrim::Bool(b) => SpecPrim::Bool(*b),
            JsPrim::Number(n) => SpecPrim::Number(*n),
            JsPrim::BigInt(bi) => SpecPrim::BigInt(bi@),
            JsPrim::Str(s) => SpecPrim::Str(s@),
            JsPrim::Symbol(id) => SpecPrim::Symbol(*id),
        }
    }
}

impl SpecPrim {
    pub open spec fn wf(self) -> bool {
        match self {
            SpecPrim::BigInt(bi) => bi.wf(),
            _ => true,
        }
    }
}

impl JsPrim {
    pub open spec fn wf(&self) -> bool {
        self@.wf()
    }
}

/// PreferredType hint for `ToPrimitive` (§7.1.1).
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum PreferredType {
    Default,
    String,
    Number,
}

/// TypeError / abrupt completion classifications for abstract type conversions.
/// `AbruptHookError(err_id)` preserves the exact caller-thrown error payload/handle `err_id`.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum TypeErrorKind {
    CannotConvertBigIntToNumber,
    CannotConvertSymbolToNumber,
    CannotConvertSymbolToString,
    ExoticToPrimitiveReturnedObject,
    OrdinaryToPrimitiveFailed,
    AbruptHookError(u64),
}

/// Input to `ToPrimitive` / `ToNumeric`: either already a primitive or an object handle.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum JsInput {
    Prim(JsPrim),
    Object(u64),
}

pub enum SpecInput {
    Prim(SpecPrim),
    Object(u64),
}

impl View for JsInput {
    type V = SpecInput;

    open spec fn view(&self) -> SpecInput {
        match self {
            JsInput::Prim(p) => SpecInput::Prim(p@),
            JsInput::Object(id) => SpecInput::Object(*id),
        }
    }
}

impl JsInput {
    pub open spec fn wf(&self) -> bool {
        match self {
            JsInput::Prim(p) => p.wf(),
            JsInput::Object(_) => true,
        }
    }
}

/// Caller-supplied outcome of invoking an object conversion method (`@@toPrimitive`, `toString`, `valueOf`).
/// `Threw(err_id)` carries the exact user-thrown exception handle/payload `err_id`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum MethodOutcome {
    NotCallable,
    ReturnedPrim(JsPrim),
    ReturnedObject,
    Threw(u64),
}

pub enum SpecMethodOutcome {
    NotCallable,
    ReturnedPrim(SpecPrim),
    ReturnedObject,
    Threw(u64),
}

impl View for MethodOutcome {
    type V = SpecMethodOutcome;

    open spec fn view(&self) -> SpecMethodOutcome {
        match self {
            MethodOutcome::NotCallable => SpecMethodOutcome::NotCallable,
            MethodOutcome::ReturnedPrim(p) => SpecMethodOutcome::ReturnedPrim(p@),
            MethodOutcome::ReturnedObject => SpecMethodOutcome::ReturnedObject,
            MethodOutcome::Threw(err_id) => SpecMethodOutcome::Threw(*err_id),
        }
    }
}

impl MethodOutcome {
    pub open spec fn wf(&self) -> bool {
        match self {
            MethodOutcome::ReturnedPrim(p) => p.wf(),
            _ => true,
        }
    }
}

/// Explicit caller hook modelling object dispatch for `ToPrimitive` (§7.1.1) and `OrdinaryToPrimitive` (§7.1.1.1).
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ObjectToPrimitiveHook {
    pub exotic_to_prim: MethodOutcome,
    pub to_string_slot: MethodOutcome,
    pub value_of_slot: MethodOutcome,
}

pub struct SpecObjectHook {
    pub exotic_to_prim: SpecMethodOutcome,
    pub to_string_slot: SpecMethodOutcome,
    pub value_of_slot: SpecMethodOutcome,
}

impl View for ObjectToPrimitiveHook {
    type V = SpecObjectHook;

    open spec fn view(&self) -> SpecObjectHook {
        SpecObjectHook {
            exotic_to_prim: self.exotic_to_prim@,
            to_string_slot: self.to_string_slot@,
            value_of_slot: self.value_of_slot@,
        }
    }
}

impl ObjectToPrimitiveHook {
    pub open spec fn wf(&self) -> bool {
        self.exotic_to_prim.wf() && self.to_string_slot.wf() && self.value_of_slot.wf()
    }
}

/// Result of `ToNumeric` (§7.1.3): either `Number` or `BigInt`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum JsNumeric {
    Number(JsNumber),
    BigInt(JsBigInt),
}

pub enum SpecNumeric {
    Number(JsNumber),
    BigInt(SpecBigInt),
}

impl View for JsNumeric {
    type V = SpecNumeric;

    open spec fn view(&self) -> SpecNumeric {
        match self {
            JsNumeric::Number(n) => SpecNumeric::Number(*n),
            JsNumeric::BigInt(b) => SpecNumeric::BigInt(b@),
        }
    }
}

// -------------------------------------------------------------------------------------------
// Specifications
// -------------------------------------------------------------------------------------------

/// ECMA-262 §7.1.2 ToBoolean(argument).
pub open spec fn spec_to_boolean(arg: SpecPrim) -> bool {
    match arg {
        SpecPrim::Undefined => false,
        SpecPrim::Null => false,
        SpecPrim::Bool(b) => b,
        SpecPrim::Number(n) => !spec_is_zero(n) && !spec_is_nan(n),
        SpecPrim::BigInt(bi) => bi.limbs.len() != 0,
        SpecPrim::Str(s) => s.len() != 0,
        SpecPrim::Symbol(_) => true,
    }
}

/// ECMA-262 §7.1.1.1 OrdinaryToPrimitive(O, hint).
pub open spec fn spec_ordinary_to_primitive(
    hook: SpecObjectHook,
    hint_string_first: bool,
) -> Result<SpecPrim, TypeErrorKind> {
    let (first, second) = if hint_string_first {
        (hook.to_string_slot, hook.value_of_slot)
    } else {
        (hook.value_of_slot, hook.to_string_slot)
    };
    match first {
        SpecMethodOutcome::ReturnedPrim(p) => Ok(p),
        SpecMethodOutcome::Threw(err_id) => Err(TypeErrorKind::AbruptHookError(err_id)),
        SpecMethodOutcome::NotCallable | SpecMethodOutcome::ReturnedObject => match second {
            SpecMethodOutcome::ReturnedPrim(p) => Ok(p),
            SpecMethodOutcome::Threw(err_id) => Err(TypeErrorKind::AbruptHookError(err_id)),
            SpecMethodOutcome::NotCallable | SpecMethodOutcome::ReturnedObject =>
                Err(TypeErrorKind::OrdinaryToPrimitiveFailed),
        },
    }
}

/// ECMA-262 §7.1.1 ToPrimitive(input [ , preferredType ]).
pub open spec fn spec_to_primitive(
    input: SpecInput,
    preferred: PreferredType,
    hook: SpecObjectHook,
) -> Result<SpecPrim, TypeErrorKind> {
    match input {
        SpecInput::Prim(p) => Ok(p),
        SpecInput::Object(_) => match hook.exotic_to_prim {
            SpecMethodOutcome::ReturnedPrim(p) => Ok(p),
            SpecMethodOutcome::ReturnedObject => Err(TypeErrorKind::ExoticToPrimitiveReturnedObject),
            SpecMethodOutcome::Threw(err_id) => Err(TypeErrorKind::AbruptHookError(err_id)),
            SpecMethodOutcome::NotCallable => {
                let hint_string_first = match preferred {
                    PreferredType::String => true,
                    PreferredType::Number | PreferredType::Default => false,
                };
                spec_ordinary_to_primitive(hook, hint_string_first)
            }
        },
    }
}

/// ECMA-262 §7.1.4 ToNumber(argument) on primitive values.
pub open spec fn spec_to_number(arg: SpecPrim) -> Result<JsNumber, TypeErrorKind> {
    match arg {
        SpecPrim::Undefined => Ok(JsNumber(0x7FF8_0000_0000_0000u64)),
        SpecPrim::Null => Ok(JsNumber(0u64)),
        SpecPrim::Bool(b) => Ok(if b { JsNumber(0x3FF0_0000_0000_0000u64) } else { JsNumber(0u64) }),
        SpecPrim::Number(n) => Ok(n),
        SpecPrim::BigInt(_) => Err(TypeErrorKind::CannotConvertBigIntToNumber),
        SpecPrim::Symbol(_) => Err(TypeErrorKind::CannotConvertSymbolToNumber),
        SpecPrim::Str(s) => Ok(spec_string_to_number(s)),
    }
}

/// ECMA-262 §7.1.3 ToNumeric(value).
pub open spec fn spec_to_numeric(
    input: SpecInput,
    hook: SpecObjectHook,
) -> Result<SpecNumeric, TypeErrorKind> {
    match spec_to_primitive(input, PreferredType::Number, hook) {
        Err(e) => Err(e),
        Ok(SpecPrim::BigInt(b)) => Ok(SpecNumeric::BigInt(b)),
        Ok(other) => match spec_to_number(other) {
            Err(e) => Err(e),
            Ok(n) => Ok(SpecNumeric::Number(n)),
        },
    }
}

/// ECMA-262 §7.1.17 ToString(argument) on primitive values.
pub open spec fn spec_to_string(arg: SpecPrim) -> Result<Seq<u16>, TypeErrorKind> {
    match arg {
        SpecPrim::Undefined => Ok(seq![0x75u16, 0x6Eu16, 0x64u16, 0x65u16, 0x66u16, 0x69u16, 0x6Eu16, 0x65u16, 0x64u16]),
        SpecPrim::Null => Ok(seq![0x6Eu16, 0x75u16, 0x6Cu16, 0x6Cu16]),
        SpecPrim::Bool(true) => Ok(seq![0x74u16, 0x72u16, 0x75u16, 0x65u16]),
        SpecPrim::Bool(false) => Ok(seq![0x66u16, 0x61u16, 0x6Cu16, 0x73u16, 0x65u16]),
        SpecPrim::Number(n) => Ok(spec_number_to_string(n)),
        SpecPrim::BigInt(b) => Ok(spec_bigint_to_string_radix(b, 10)),
        SpecPrim::Str(s) => Ok(s),
        SpecPrim::Symbol(_) => Err(TypeErrorKind::CannotConvertSymbolToString),
    }
}

/// ECMA-262 §13.5.3 The `typeof` Operator on primitive values.
pub open spec fn spec_typeof_prim(arg: SpecPrim) -> Seq<u16> {
    match arg {
        SpecPrim::Undefined => seq![0x75u16, 0x6Eu16, 0x64u16, 0x65u16, 0x66u16, 0x69u16, 0x6Eu16, 0x65u16, 0x64u16], // "undefined"
        SpecPrim::Null => seq![0x6Fu16, 0x62u16, 0x6Au16, 0x65u16, 0x63u16, 0x74u16], // "object"
        SpecPrim::Bool(_) => seq![0x62u16, 0x6Fu16, 0x6Fu16, 0x6Cu16, 0x65u16, 0x61u16, 0x6Eu16], // "boolean"
        SpecPrim::Number(_) => seq![0x6Eu16, 0x75u16, 0x6Du16, 0x62u16, 0x65u16, 0x72u16], // "number"
        SpecPrim::BigInt(_) => seq![0x62u16, 0x69u16, 0x67u16, 0x69u16, 0x6Eu16, 0x74u16], // "bigint"
        SpecPrim::Str(_) => seq![0x73u16, 0x74u16, 0x72u16, 0x69u16, 0x6Eu16, 0x67u16], // "string"
        SpecPrim::Symbol(_) => seq![0x73u16, 0x79u16, 0x6Du16, 0x62u16, 0x6Fu16, 0x6Cu16], // "symbol"
    }
}

/// ECMA-262 §7.2.10 SameValue(x, y).
pub open spec fn spec_same_value(x: SpecPrim, y: SpecPrim) -> bool {
    match (x, y) {
        (SpecPrim::Undefined, SpecPrim::Undefined) => true,
        (SpecPrim::Null, SpecPrim::Null) => true,
        (SpecPrim::Bool(a), SpecPrim::Bool(b)) => a == b,
        (SpecPrim::Number(a), SpecPrim::Number(b)) => spec_number_same_value(a, b),
        (SpecPrim::BigInt(a), SpecPrim::BigInt(b)) => spec_bigint_eq(a, b),
        (SpecPrim::Str(a), SpecPrim::Str(b)) => a == b,
        (SpecPrim::Symbol(a), SpecPrim::Symbol(b)) => a == b,
        _ => false,
    }
}

/// ECMA-262 §7.2.11 SameValueZero(x, y).
pub open spec fn spec_same_value_zero(x: SpecPrim, y: SpecPrim) -> bool {
    match (x, y) {
        (SpecPrim::Undefined, SpecPrim::Undefined) => true,
        (SpecPrim::Null, SpecPrim::Null) => true,
        (SpecPrim::Bool(a), SpecPrim::Bool(b)) => a == b,
        (SpecPrim::Number(a), SpecPrim::Number(b)) => spec_number_same_value_zero(a, b),
        (SpecPrim::BigInt(a), SpecPrim::BigInt(b)) => spec_bigint_eq(a, b),
        (SpecPrim::Str(a), SpecPrim::Str(b)) => a == b,
        (SpecPrim::Symbol(a), SpecPrim::Symbol(b)) => a == b,
        _ => false,
    }
}

/// ECMA-262 §7.2.15 IsStrictlyEqual(x, y).
pub open spec fn spec_is_strictly_equal(x: SpecPrim, y: SpecPrim) -> bool {
    match (x, y) {
        (SpecPrim::Undefined, SpecPrim::Undefined) => true,
        (SpecPrim::Null, SpecPrim::Null) => true,
        (SpecPrim::Bool(a), SpecPrim::Bool(b)) => a == b,
        (SpecPrim::Number(a), SpecPrim::Number(b)) => spec_number_equal(a, b),
        (SpecPrim::BigInt(a), SpecPrim::BigInt(b)) => spec_bigint_eq(a, b),
        (SpecPrim::Str(a), SpecPrim::Str(b)) => a == b,
        (SpecPrim::Symbol(a), SpecPrim::Symbol(b)) => a == b,
        _ => false,
    }
}

pub open spec fn spec_bool_to_number(b: bool) -> JsNumber {
    if b { JsNumber(0x3FF0_0000_0000_0000u64) } else { JsNumber(0u64) }
}

pub open spec fn spec_bigint_eq_number(bi: SpecBigInt, num: JsNumber) -> bool {
    match spec_number_to_exact_bigint(num) {
        None => false,
        Some(num_bi) => spec_bigint_eq(bi, num_bi),
    }
}

/// Core non-Boolean cases of ECMA-262 §7.2.14 IsLooselyEqual(x, y) on primitives.
pub open spec fn spec_loosely_equal_non_bool(x: SpecPrim, y: SpecPrim) -> bool {
    match (x, y) {
        (SpecPrim::Undefined, SpecPrim::Undefined) => true,
        (SpecPrim::Null, SpecPrim::Null) => true,
        (SpecPrim::Undefined, SpecPrim::Null) => true,
        (SpecPrim::Null, SpecPrim::Undefined) => true,
        (SpecPrim::Number(a), SpecPrim::Number(b)) => spec_number_equal(a, b),
        (SpecPrim::BigInt(a), SpecPrim::BigInt(b)) => spec_bigint_eq(a, b),
        (SpecPrim::Str(a), SpecPrim::Str(b)) => a == b,
        (SpecPrim::Symbol(a), SpecPrim::Symbol(b)) => a == b,
        (SpecPrim::Number(n), SpecPrim::Str(s)) => spec_number_equal(n, spec_string_to_number(s)),
        (SpecPrim::Str(s), SpecPrim::Number(n)) => spec_number_equal(spec_string_to_number(s), n),
        (SpecPrim::BigInt(bi), SpecPrim::Str(s)) => match spec_string_to_bigint(s) {
            None => false,
            Some(parsed) => spec_bigint_eq(bi, parsed),
        },
        (SpecPrim::Str(s), SpecPrim::BigInt(bi)) => match spec_string_to_bigint(s) {
            None => false,
            Some(parsed) => spec_bigint_eq(parsed, bi),
        },
        (SpecPrim::BigInt(bi), SpecPrim::Number(n)) => spec_bigint_eq_number(bi, n),
        (SpecPrim::Number(n), SpecPrim::BigInt(bi)) => spec_bigint_eq_number(bi, n),
        _ => false,
    }
}

/// ECMA-262 §7.2.14 IsLooselyEqual(x, y) on primitives (handling Boolean → Number coercion first when
/// types differ, and same-type `IsStrictlyEqual` when both are Booleans).
pub open spec fn spec_is_loosely_equal(x: SpecPrim, y: SpecPrim) -> bool {
    match (x, y) {
        (SpecPrim::Bool(a), SpecPrim::Bool(b)) => a == b,
        (SpecPrim::Bool(a), other) => spec_loosely_equal_non_bool(SpecPrim::Number(spec_bool_to_number(a)), other),
        (other, SpecPrim::Bool(b)) => spec_loosely_equal_non_bool(other, SpecPrim::Number(spec_bool_to_number(b))),
        _ => spec_loosely_equal_non_bool(x, y),
    }
}

/// ECMA-262 §7.2.14 IsLooselyEqual(x, y) extended to `SpecInput` (primitives + objects via `ToPrimitive`).
pub open spec fn spec_is_loosely_equal_input(
    x: SpecInput,
    y: SpecInput,
    hook_x: SpecObjectHook,
    hook_y: SpecObjectHook,
) -> Result<bool, TypeErrorKind> {
    match (x, y) {
        (SpecInput::Prim(px), SpecInput::Prim(py)) => Ok(spec_is_loosely_equal(px, py)),
        (SpecInput::Object(id1), SpecInput::Object(id2)) => Ok(id1 == id2),
        (SpecInput::Object(_), SpecInput::Prim(SpecPrim::Undefined | SpecPrim::Null)) => Ok(false),
        (SpecInput::Prim(SpecPrim::Undefined | SpecPrim::Null), SpecInput::Object(_)) => Ok(false),
        (SpecInput::Object(_), SpecInput::Prim(py)) => {
            let py_norm = match py {
                SpecPrim::Bool(b) => SpecPrim::Number(spec_bool_to_number(b)),
                other => other,
            };
            match spec_to_primitive(x, PreferredType::Default, hook_x) {
                Err(e) => Err(e),
                Ok(px) => Ok(spec_is_loosely_equal(px, py_norm)),
            }
        }
        (SpecInput::Prim(px), SpecInput::Object(_)) => {
            let px_norm = match px {
                SpecPrim::Bool(b) => SpecPrim::Number(spec_bool_to_number(b)),
                other => other,
            };
            match spec_to_primitive(y, PreferredType::Default, hook_y) {
                Err(e) => Err(e),
                Ok(py) => Ok(spec_is_loosely_equal(px_norm, py)),
            }
        }
    }
}

// -------------------------------------------------------------------------------------------
// Proofs & Algebraic Lemmas
// -------------------------------------------------------------------------------------------

/// `SameValue` is an equivalence relation over all ECMAScript primitive values.
pub proof fn lemma_same_value_equivalence(x: SpecPrim, y: SpecPrim, z: SpecPrim)
    ensures
        spec_same_value(x, x),
        spec_same_value(x, y) == spec_same_value(y, x),
        (spec_same_value(x, y) && spec_same_value(y, z)) ==> spec_same_value(x, z),
{
    if let SpecPrim::Number(nx) = x {
        lemma_number_same_value_equivalence(nx, nx, nx);
        if let SpecPrim::Number(ny) = y {
            lemma_number_same_value_equivalence(nx, ny, nx);
            if let SpecPrim::Number(nz) = z {
                lemma_number_same_value_equivalence(nx, ny, nz);
            }
        }
    }
}

/// `SameValueZero` is an equivalence relation over all ECMAScript primitive values.
pub proof fn lemma_same_value_zero_equivalence(x: SpecPrim, y: SpecPrim, z: SpecPrim)
    ensures
        spec_same_value_zero(x, x),
        spec_same_value_zero(x, y) == spec_same_value_zero(y, x),
        (spec_same_value_zero(x, y) && spec_same_value_zero(y, z)) ==> spec_same_value_zero(x, z),
{
    if let SpecPrim::Number(nx) = x {
        lemma_number_same_value_zero_equivalence(nx, nx, nx);
        if let SpecPrim::Number(ny) = y {
            lemma_number_same_value_zero_equivalence(nx, ny, nx);
            if let SpecPrim::Number(nz) = z {
                lemma_number_same_value_zero_equivalence(nx, ny, nz);
            }
        }
    }
}

/// `IsStrictlyEqual` implies `IsLooselyEqual`, and `IsLooselyEqual` is symmetric across all primitive types.
pub proof fn lemma_equality_hierarchy_and_symmetry(x: SpecPrim, y: SpecPrim)
    ensures
        spec_is_strictly_equal(x, y) == spec_is_strictly_equal(y, x),
        spec_is_strictly_equal(x, y) ==> spec_is_loosely_equal(x, y),
        spec_is_loosely_equal(x, y) == spec_is_loosely_equal(y, x),
{
}

/// `ToPrimitive` on any primitive input returns that primitive unchanged regardless of preferredType or hook.
pub proof fn lemma_to_primitive_idempotent_on_prim(
    p: SpecPrim,
    pref: PreferredType,
    hook: SpecObjectHook,
)
    ensures
        spec_to_primitive(SpecInput::Prim(p), pref, hook) == Ok(p),
{
}

/// ECMA-262 §7.1.1 & §7.1.1.1 short-circuit and abrupt-completion identity preservation:
/// - When the first candidate slot for `hint` returns a primitive `p` or throws `err_id`, the second
///   slot is completely ignored and the exact `Ok(p)` / `Err(AbruptHookError(err_id))` is returned.
/// - When `@@toPrimitive` throws `err_id`, `Err(AbruptHookError(err_id))` is returned without consulting
///   `OrdinaryToPrimitive` slots.
pub proof fn lemma_to_primitive_abrupt_and_short_circuit(
    obj_id: u64,
    p: SpecPrim,
    err_id: u64,
    other_slot: SpecMethodOutcome,
)
    ensures
        spec_to_primitive(
            SpecInput::Object(obj_id),
            PreferredType::Number,
            SpecObjectHook {
                exotic_to_prim: SpecMethodOutcome::NotCallable,
                value_of_slot: SpecMethodOutcome::ReturnedPrim(p),
                to_string_slot: other_slot,
            },
        ) == Ok(p),
        spec_to_primitive(
            SpecInput::Object(obj_id),
            PreferredType::Number,
            SpecObjectHook {
                exotic_to_prim: SpecMethodOutcome::NotCallable,
                value_of_slot: SpecMethodOutcome::Threw(err_id),
                to_string_slot: other_slot,
            },
        ) == Err(TypeErrorKind::AbruptHookError(err_id)),
        spec_to_primitive(
            SpecInput::Object(obj_id),
            PreferredType::String,
            SpecObjectHook {
                exotic_to_prim: SpecMethodOutcome::NotCallable,
                to_string_slot: SpecMethodOutcome::ReturnedPrim(p),
                value_of_slot: other_slot,
            },
        ) == Ok(p),
        spec_to_primitive(
            SpecInput::Object(obj_id),
            PreferredType::String,
            SpecObjectHook {
                exotic_to_prim: SpecMethodOutcome::NotCallable,
                to_string_slot: SpecMethodOutcome::Threw(err_id),
                value_of_slot: other_slot,
            },
        ) == Err(TypeErrorKind::AbruptHookError(err_id)),
        spec_to_primitive(
            SpecInput::Object(obj_id),
            PreferredType::Default,
            SpecObjectHook {
                exotic_to_prim: SpecMethodOutcome::Threw(err_id),
                to_string_slot: other_slot,
                value_of_slot: other_slot,
            },
        ) == Err(TypeErrorKind::AbruptHookError(err_id)),
{
}

// -------------------------------------------------------------------------------------------
// Executable Implementations
// -------------------------------------------------------------------------------------------

impl JsPrim {
    pub fn clone_prim(&self) -> (out: Self)
        ensures
            out@ == self@,
            self.wf() ==> out.wf(),
    {
        match self {
            JsPrim::Undefined => JsPrim::Undefined,
            JsPrim::Null => JsPrim::Null,
            JsPrim::Bool(b) => JsPrim::Bool(*b),
            JsPrim::Number(n) => JsPrim::Number(*n),
            JsPrim::BigInt(bi) => JsPrim::BigInt(bi.clone_bigint()),
            JsPrim::Str(s) => JsPrim::Str(s.clone_str()),
            JsPrim::Symbol(id) => JsPrim::Symbol(*id),
        }
    }
}

fn make_utf16_4(a: u16, b: u16, c: u16, d: u16) -> (out: Utf16Str)
    ensures
        out@ == seq![a, b, c, d],
{
    let mut v: Vec<u16> = Vec::with_capacity(4);
    v.push(a);
    v.push(b);
    v.push(c);
    v.push(d);
    proof {
        assert(v@ =~= seq![a, b, c, d]);
    }
    Utf16Str { units: v }
}

fn make_utf16_5(a: u16, b: u16, c: u16, d: u16, e: u16) -> (out: Utf16Str)
    ensures
        out@ == seq![a, b, c, d, e],
{
    let mut v: Vec<u16> = Vec::with_capacity(5);
    v.push(a);
    v.push(b);
    v.push(c);
    v.push(d);
    v.push(e);
    proof {
        assert(v@ =~= seq![a, b, c, d, e]);
    }
    Utf16Str { units: v }
}

fn make_utf16_6(a: u16, b: u16, c: u16, d: u16, e: u16, f: u16) -> (out: Utf16Str)
    ensures
        out@ == seq![a, b, c, d, e, f],
{
    let mut v: Vec<u16> = Vec::with_capacity(6);
    v.push(a);
    v.push(b);
    v.push(c);
    v.push(d);
    v.push(e);
    v.push(f);
    proof {
        assert(v@ =~= seq![a, b, c, d, e, f]);
    }
    Utf16Str { units: v }
}

fn make_utf16_7(a: u16, b: u16, c: u16, d: u16, e: u16, f: u16, g: u16) -> (out: Utf16Str)
    ensures
        out@ == seq![a, b, c, d, e, f, g],
{
    let mut v: Vec<u16> = Vec::with_capacity(7);
    v.push(a);
    v.push(b);
    v.push(c);
    v.push(d);
    v.push(e);
    v.push(f);
    v.push(g);
    proof {
        assert(v@ =~= seq![a, b, c, d, e, f, g]);
    }
    Utf16Str { units: v }
}

fn make_utf16_9(
    a: u16,
    b: u16,
    c: u16,
    d: u16,
    e: u16,
    f: u16,
    g: u16,
    h: u16,
    i: u16,
) -> (out: Utf16Str)
    ensures
        out@ == seq![a, b, c, d, e, f, g, h, i],
{
    let mut v: Vec<u16> = Vec::with_capacity(9);
    v.push(a);
    v.push(b);
    v.push(c);
    v.push(d);
    v.push(e);
    v.push(f);
    v.push(g);
    v.push(h);
    v.push(i);
    proof {
        assert(v@ =~= seq![a, b, c, d, e, f, g, h, i]);
    }
    Utf16Str { units: v }
}

/// ECMA-262 §7.1.2 ToBoolean(argument).
pub fn to_boolean(arg: &JsPrim) -> (b: bool)
    requires
        arg.wf(),
    ensures
        b == spec_to_boolean(arg@),
{
    match arg {
        JsPrim::Undefined => false,
        JsPrim::Null => false,
        JsPrim::Bool(b) => *b,
        JsPrim::Number(n) => !n.is_zero() && !n.is_nan(),
        JsPrim::BigInt(bi) => !bi.is_zero(),
        JsPrim::Str(s) => !s.is_empty(),
        JsPrim::Symbol(_) => true,
    }
}

fn ordinary_to_primitive_exec(
    hook: &ObjectToPrimitiveHook,
    hint_string_first: bool,
) -> (res: Result<JsPrim, TypeErrorKind>)
    requires
        hook.wf(),
    ensures
        match (res, spec_ordinary_to_primitive(hook@, hint_string_first)) {
            (Ok(p), Ok(sp)) => p.wf() && p@ == sp,
            (Err(e), Err(se)) => e == se,
            _ => false,
        },
{
    let (first, second) = if hint_string_first {
        (&hook.to_string_slot, &hook.value_of_slot)
    } else {
        (&hook.value_of_slot, &hook.to_string_slot)
    };
    match first {
        MethodOutcome::ReturnedPrim(p) => Ok(p.clone_prim()),
        MethodOutcome::Threw(err_id) => Err(TypeErrorKind::AbruptHookError(*err_id)),
        MethodOutcome::NotCallable | MethodOutcome::ReturnedObject => match second {
            MethodOutcome::ReturnedPrim(p) => Ok(p.clone_prim()),
            MethodOutcome::Threw(err_id) => Err(TypeErrorKind::AbruptHookError(*err_id)),
            MethodOutcome::NotCallable | MethodOutcome::ReturnedObject =>
                Err(TypeErrorKind::OrdinaryToPrimitiveFailed),
        },
    }
}

/// ECMA-262 §7.1.1 ToPrimitive(input [ , preferredType ]).
pub fn to_primitive(
    input: &JsInput,
    preferred: PreferredType,
    hook: &ObjectToPrimitiveHook,
) -> (res: Result<JsPrim, TypeErrorKind>)
    requires
        input.wf(),
        hook.wf(),
    ensures
        match (res, spec_to_primitive(input@, preferred, hook@)) {
            (Ok(p), Ok(sp)) => p.wf() && p@ == sp,
            (Err(e), Err(se)) => e == se,
            _ => false,
        },
{
    match input {
        JsInput::Prim(p) => Ok(p.clone_prim()),
        JsInput::Object(_) => match &hook.exotic_to_prim {
            MethodOutcome::ReturnedPrim(p) => Ok(p.clone_prim()),
            MethodOutcome::ReturnedObject => Err(TypeErrorKind::ExoticToPrimitiveReturnedObject),
            MethodOutcome::Threw(err_id) => Err(TypeErrorKind::AbruptHookError(*err_id)),
            MethodOutcome::NotCallable => {
                let hint_string_first = match preferred {
                    PreferredType::String => true,
                    PreferredType::Number | PreferredType::Default => false,
                };
                ordinary_to_primitive_exec(hook, hint_string_first)
            }
        },
    }
}

/// ECMA-262 §7.1.4 ToNumber(argument).
pub fn to_number(arg: &JsPrim) -> (res: Result<JsNumber, TypeErrorKind>)
    requires
        arg.wf(),
    ensures
        res == spec_to_number(arg@),
{
    match arg {
        JsPrim::Undefined => Ok(JsNumber::NAN),
        JsPrim::Null => Ok(JsNumber::POS_ZERO),
        JsPrim::Bool(b) => Ok(if *b { JsNumber::ONE } else { JsNumber::POS_ZERO }),
        JsPrim::Number(n) => Ok(*n),
        JsPrim::BigInt(_) => Err(TypeErrorKind::CannotConvertBigIntToNumber),
        JsPrim::Symbol(_) => Err(TypeErrorKind::CannotConvertSymbolToNumber),
        JsPrim::Str(s) => Ok(string_to_number(s)),
    }
}

/// ECMA-262 §7.1.3 ToNumeric(value).
pub fn to_numeric(
    input: &JsInput,
    hook: &ObjectToPrimitiveHook,
) -> (res: Result<JsNumeric, TypeErrorKind>)
    requires
        input.wf(),
        hook.wf(),
    ensures
        match (res, spec_to_numeric(input@, hook@)) {
            (Ok(JsNumeric::Number(n)), Ok(SpecNumeric::Number(sn))) => n == sn,
            (Ok(JsNumeric::BigInt(b)), Ok(SpecNumeric::BigInt(sb))) => b.wf() && b@ == sb,
            (Err(e), Err(se)) => e == se,
            _ => false,
        },
{
    match to_primitive(input, PreferredType::Number, hook) {
        Err(e) => Err(e),
        Ok(JsPrim::BigInt(b)) => Ok(JsNumeric::BigInt(b)),
        Ok(other) => match to_number(&other) {
            Err(e) => Err(e),
            Ok(n) => Ok(JsNumeric::Number(n)),
        },
    }
}

/// ECMA-262 §7.1.17 ToString(argument).
pub fn to_string(arg: &JsPrim) -> (res: Result<Utf16Str, TypeErrorKind>)
    requires
        arg.wf(),
    ensures
        match (res, spec_to_string(arg@)) {
            (Ok(s), Ok(ss)) => s@ == ss,
            (Err(e), Err(se)) => e == se,
            _ => false,
        },
{
    match arg {
        JsPrim::Undefined => Ok(make_utf16_9(0x75u16, 0x6Eu16, 0x64u16, 0x65u16, 0x66u16, 0x69u16, 0x6Eu16, 0x65u16, 0x64u16)),
        JsPrim::Null => Ok(make_utf16_4(0x6Eu16, 0x75u16, 0x6Cu16, 0x6Cu16)),
        JsPrim::Bool(true) => Ok(make_utf16_4(0x74u16, 0x72u16, 0x75u16, 0x65u16)),
        JsPrim::Bool(false) => Ok(make_utf16_5(0x66u16, 0x61u16, 0x6Cu16, 0x73u16, 0x65u16)),
        JsPrim::Number(n) => Ok(number_to_string(*n)),
        JsPrim::BigInt(b) => Ok(b.to_string_radix10()),
        JsPrim::Str(s) => Ok(s.clone_str()),
        JsPrim::Symbol(_) => Err(TypeErrorKind::CannotConvertSymbolToString),
    }
}

/// ECMA-262 §13.5.3 `typeof` operator on primitive values.
pub fn typeof_prim(arg: &JsPrim) -> (out: Utf16Str)
    ensures
        out@ == spec_typeof_prim(arg@),
{
    match arg {
        JsPrim::Undefined => make_utf16_9(0x75u16, 0x6Eu16, 0x64u16, 0x65u16, 0x66u16, 0x69u16, 0x6Eu16, 0x65u16, 0x64u16),
        JsPrim::Null => make_utf16_6(0x6Fu16, 0x62u16, 0x6Au16, 0x65u16, 0x63u16, 0x74u16),
        JsPrim::Bool(_) => make_utf16_7(0x62u16, 0x6Fu16, 0x6Fu16, 0x6Cu16, 0x65u16, 0x61u16, 0x6Eu16),
        JsPrim::Number(_) => make_utf16_6(0x6Eu16, 0x75u16, 0x6Du16, 0x62u16, 0x65u16, 0x72u16),
        JsPrim::BigInt(_) => make_utf16_6(0x62u16, 0x69u16, 0x67u16, 0x69u16, 0x6Eu16, 0x74u16),
        JsPrim::Str(_) => make_utf16_6(0x73u16, 0x74u16, 0x72u16, 0x69u16, 0x6Eu16, 0x67u16),
        JsPrim::Symbol(_) => make_utf16_6(0x73u16, 0x79u16, 0x6Du16, 0x62u16, 0x6Fu16, 0x6Cu16),
    }
}

/// ECMA-262 §7.2.10 SameValue(x, y).
pub fn same_value(x: &JsPrim, y: &JsPrim) -> (eq: bool)
    requires
        x.wf(),
        y.wf(),
    ensures
        eq == spec_same_value(x@, y@),
{
    match (x, y) {
        (JsPrim::Undefined, JsPrim::Undefined) => true,
        (JsPrim::Null, JsPrim::Null) => true,
        (JsPrim::Bool(a), JsPrim::Bool(b)) => *a == *b,
        (JsPrim::Number(a), JsPrim::Number(b)) => a.same_value(*b),
        (JsPrim::BigInt(a), JsPrim::BigInt(b)) => a.eq_bigint(b),
        (JsPrim::Str(a), JsPrim::Str(b)) => a.eq_str(b),
        (JsPrim::Symbol(a), JsPrim::Symbol(b)) => *a == *b,
        _ => false,
    }
}

/// ECMA-262 §7.2.11 SameValueZero(x, y).
pub fn same_value_zero(x: &JsPrim, y: &JsPrim) -> (eq: bool)
    requires
        x.wf(),
        y.wf(),
    ensures
        eq == spec_same_value_zero(x@, y@),
{
    match (x, y) {
        (JsPrim::Undefined, JsPrim::Undefined) => true,
        (JsPrim::Null, JsPrim::Null) => true,
        (JsPrim::Bool(a), JsPrim::Bool(b)) => *a == *b,
        (JsPrim::Number(a), JsPrim::Number(b)) => a.same_value_zero(*b),
        (JsPrim::BigInt(a), JsPrim::BigInt(b)) => a.eq_bigint(b),
        (JsPrim::Str(a), JsPrim::Str(b)) => a.eq_str(b),
        (JsPrim::Symbol(a), JsPrim::Symbol(b)) => *a == *b,
        _ => false,
    }
}

/// ECMA-262 §7.2.15 IsStrictlyEqual(x, y).
pub fn is_strictly_equal(x: &JsPrim, y: &JsPrim) -> (eq: bool)
    requires
        x.wf(),
        y.wf(),
    ensures
        eq == spec_is_strictly_equal(x@, y@),
{
    match (x, y) {
        (JsPrim::Undefined, JsPrim::Undefined) => true,
        (JsPrim::Null, JsPrim::Null) => true,
        (JsPrim::Bool(a), JsPrim::Bool(b)) => *a == *b,
        (JsPrim::Number(a), JsPrim::Number(b)) => a.equal(*b),
        (JsPrim::BigInt(a), JsPrim::BigInt(b)) => a.eq_bigint(b),
        (JsPrim::Str(a), JsPrim::Str(b)) => a.eq_str(b),
        (JsPrim::Symbol(a), JsPrim::Symbol(b)) => *a == *b,
        _ => false,
    }
}

fn loosely_equal_non_bool_exec(x: &JsPrim, y: &JsPrim) -> (eq: bool)
    requires
        x.wf(),
        y.wf(),
    ensures
        eq == spec_loosely_equal_non_bool(x@, y@),
{
    match (x, y) {
        (JsPrim::Undefined, JsPrim::Undefined) => true,
        (JsPrim::Null, JsPrim::Null) => true,
        (JsPrim::Undefined, JsPrim::Null) => true,
        (JsPrim::Null, JsPrim::Undefined) => true,
        (JsPrim::Number(a), JsPrim::Number(b)) => a.equal(*b),
        (JsPrim::BigInt(a), JsPrim::BigInt(b)) => a.eq_bigint(b),
        (JsPrim::Str(a), JsPrim::Str(b)) => a.eq_str(b),
        (JsPrim::Symbol(a), JsPrim::Symbol(b)) => *a == *b,
        (JsPrim::Number(n), JsPrim::Str(s)) => {
            let sn = string_to_number(s);
            n.equal(sn)
        }
        (JsPrim::Str(s), JsPrim::Number(n)) => {
            let sn = string_to_number(s);
            sn.equal(*n)
        }
        (JsPrim::BigInt(bi), JsPrim::Str(s)) => match string_to_bigint(s) {
            None => false,
            Some(parsed) => bi.eq_bigint(&parsed),
        },
        (JsPrim::Str(s), JsPrim::BigInt(bi)) => match string_to_bigint(s) {
            None => false,
            Some(parsed) => parsed.eq_bigint(bi),
        },
        (JsPrim::BigInt(bi), JsPrim::Number(n)) => match n.to_exact_bigint() {
            None => false,
            Some(num_bi) => bi.eq_bigint(&num_bi),
        },
        (JsPrim::Number(n), JsPrim::BigInt(bi)) => match n.to_exact_bigint() {
            None => false,
            Some(num_bi) => bi.eq_bigint(&num_bi),
        },
        _ => false,
    }
}

/// ECMA-262 §7.2.14 IsLooselyEqual(x, y) on primitives, proved equal to `spec_is_loosely_equal`.
pub fn is_loosely_equal(x: &JsPrim, y: &JsPrim) -> (eq: bool)
    requires
        x.wf(),
        y.wf(),
    ensures
        eq == spec_is_loosely_equal(x@, y@),
{
    match (x, y) {
        (JsPrim::Bool(a), JsPrim::Bool(b)) => *a == *b,
        (JsPrim::Bool(a), _) => {
            let num = JsPrim::Number(if *a { JsNumber::ONE } else { JsNumber::POS_ZERO });
            loosely_equal_non_bool_exec(&num, y)
        }
        (_, JsPrim::Bool(b)) => {
            let num = JsPrim::Number(if *b { JsNumber::ONE } else { JsNumber::POS_ZERO });
            loosely_equal_non_bool_exec(x, &num)
        }
        _ => loosely_equal_non_bool_exec(x, y),
    }
}

/// ECMA-262 §7.2.14 IsLooselyEqual(x, y) extended to `JsInput` (including Object → Primitive coercion).
pub fn is_loosely_equal_input(
    x: &JsInput,
    y: &JsInput,
    hook_x: &ObjectToPrimitiveHook,
    hook_y: &ObjectToPrimitiveHook,
) -> (res: Result<bool, TypeErrorKind>)
    requires
        x.wf(),
        y.wf(),
        hook_x.wf(),
        hook_y.wf(),
    ensures
        res == spec_is_loosely_equal_input(x@, y@, hook_x@, hook_y@),
{
    match (x, y) {
        (JsInput::Prim(px), JsInput::Prim(py)) => Ok(is_loosely_equal(px, py)),
        (JsInput::Object(id1), JsInput::Object(id2)) => Ok(*id1 == *id2),
        (JsInput::Object(_), JsInput::Prim(JsPrim::Undefined | JsPrim::Null)) => Ok(false),
        (JsInput::Prim(JsPrim::Undefined | JsPrim::Null), JsInput::Object(_)) => Ok(false),
        (JsInput::Object(_), JsInput::Prim(py)) => {
            let py_norm = match py {
                JsPrim::Bool(b) => JsPrim::Number(if *b { JsNumber::ONE } else { JsNumber::POS_ZERO }),
                other => other.clone_prim(),
            };
            match to_primitive(x, PreferredType::Default, hook_x) {
                Err(e) => Err(e),
                Ok(px) => Ok(is_loosely_equal(&px, &py_norm)),
            }
        }
        (JsInput::Prim(px), JsInput::Object(_)) => {
            let px_norm = match px {
                JsPrim::Bool(b) => JsPrim::Number(if *b { JsNumber::ONE } else { JsNumber::POS_ZERO }),
                other => other.clone_prim(),
            };
            match to_primitive(y, PreferredType::Default, hook_y) {
                Err(e) => Err(e),
                Ok(py) => Ok(is_loosely_equal(&px_norm, &py)),
            }
        }
    }
}

} // verus!
