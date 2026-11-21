//! `vjs_object`: Formally verified ECMAScript object model (ECMA-262 §6.1.7, §6.2.6,
//! §7.3.15–7.3.16, §10.1, §10.4.2), index-based arena heap, property descriptors,
//! ordinary internal methods, Array exotic object, and machine-checked §6.1.7.3
//! Essential Internal Method Invariants.
#![forbid(unsafe_code)]

pub mod value;
pub mod string_to_f64;
pub mod descriptor;
pub mod heap;
pub mod ordinary;
pub mod array;
pub mod invariants_proof;
