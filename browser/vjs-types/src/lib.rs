//! `vjs_types`: Formally verified ECMAScript language types and abstract operations
//! (`docs/verified-browser-engine.md` §3.3, Step J1).
//!
//! Modules:
//! - `utf16`: UTF-16 code-unit strings (`Utf16Str`), ECMA-262 §6.1.4 & §11.1.4 surrogate decoding,
//!   UTF-8 / WTF-8 conversions, slicing, concatenation, `StringIndexOf`, `TrimString`, `IsLessThan`.
//! - `bigint`: Arbitrary-precision canonical signed integers (`JsBigInt`), arithmetic, comparisons,
//!   `StringToBigInt` (§7.1.14), and `BigInt::toString` (§6.1.6.2.21).
//! - `number`: Bit-exact IEEE-754 binary64 `JsNumber(u64)`, classification, comparisons,
//!   round-to-nearest-even arithmetic, `ToInt32`/`ToUint32`/`ToUint16`, `Number::toString`
//!   (§6.1.6.1.20), and `StringToNumber` (§7.1.4.1.1).
//! - `ops`: ECMAScript primitive language values (`JsPrim`) and abstract operations (`ToBoolean`,
//!   `ToPrimitive`, `ToNumeric`, `ToNumber`, `ToString`, `SameValue`, `SameValueZero`,
//!   `IsLooselyEqual`, `IsStrictlyEqual`).
#![forbid(unsafe_code)]

pub mod utf16;
pub mod bigint;
pub mod number;
pub mod ops;
