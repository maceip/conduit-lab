//! `vjs_spec`: ECMA-262 `<emu-alg>` specifications compiled to Verus `spec fn` + proved `exec fn`.
//! Spec source: `tc39/ecma262@74c33d406ec1763ca9ee5ad9165571661649d6e6` (2026-11-20).
#![forbid(unsafe_code)]

pub mod runtime;
pub mod generated;
pub mod lemmas;

pub use runtime::*;
pub use generated::*;
#[allow(unused_imports)]
pub use lemmas::*;
