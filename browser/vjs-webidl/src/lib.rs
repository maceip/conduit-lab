//! `vjs_webidl`: Formally verified WHATWG Web IDL (§3.2) `ToIDL`/`ToJS` host boundary
//! and kernel-issued capability handle system (zero ambient authority).
//!
//! Spec source: whatwg/webidl@54a5f2de6a34e27a517a49370bc07d8943b0be11 (2026-11-14).
#![forbid(unsafe_code)]

pub mod conversions;
pub mod caps;
pub mod dispatch;
