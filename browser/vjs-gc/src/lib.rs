//! `vjs_gc` (J6 of `vjs`, `docs/verified-browser-engine.md` §3.3):
//! - `types`: ECMAScript runtime value atoms, `SameValue` (§7.2.10), verified string atom pool, and errors.
//! - `gc`: Formally verified iterative tricolor Mark-Sweep Garbage Collector with per-realm live
//!   byte/object quota tracking and machine-checked soundness, completeness, and `wf` preservation.
//! - `proxy`: Proxy exotic object (§10.5) & Reflect (§28.1) with machine-checked §6.1.7.3 essential
//!   internal-method invariants proved against arbitrary/malicious handler trap outputs.
//! - `promise_jobs`: Promises (§27.2) & FIFO Microtask Job Queue (§9.5) with machine-checked
//!   settle-once monotonicity and liveness-under-fuel theorems.
//! - `generator`: Generators (§27.5) & Async/Await continuation frames (§27.7) integrated with
//!   Promise reaction jobs, proving `Completed` absorption and `GeneratorValidate` re-entrancy safety.
#![forbid(unsafe_code)]

pub mod types;
pub mod gc;
pub mod proxy;
pub mod generator;
pub mod promise_jobs;
