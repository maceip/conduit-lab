//! `vjs_builtins`: formally verified ECMAScript built-in libraries for `vjs` (Step J5).
//!
//! Covers ECMA-262 §25.5 JSON (Vest-style roundtrip + prefix security), §22.2 RegExp
//! (Warblre-style verified terminating matcher with empty-match progress guard), §21.4 Date
//! (calendar math + TimeClip + ISO-8601 roundtrip), §21.3 Math, §22.1 String, §23.1 Array,
//! and §24.1/§24.2 deterministic insertion-order Map and Set with SameValueZero equality.
#![forbid(unsafe_code)]

pub mod collections;
pub mod date;
pub mod json;
pub mod math_str_arr;
pub mod regexp;
