// Upgraded engineering tradeoffs derived from docs/vjs-plan-review.md §1,
// synchronized with the current live J0–J7 verified crate implementation.
export interface Tradeoff {
  decision: string;
  givenUp: string;
  gained: string;
  residual: string;
}

export const TRADEOFFS: Tradeoff[] = [
  {
    decision: 'Interpreter + verified bytecode VM only; no optimizing JIT inside the trusted base.',
    givenUp: 'Peak throughput compared to TurboFan and Maglev on compute-heavy web apps.',
    gained: 'Eliminates the optimizing JIT bug class where 13 of Chrome’s last 20 ITW zero-days originated; J7 bytecode compilation carries a CompCert-style simulation proof.',
    residual: 'Bytecode VM speedups are measured on microbenchmarks so far; full real-site latency budgets remain to be measured after DOM wiring.',
  },
  {
    decision: 'Safe Rust (#![forbid(unsafe_code)]) with an index-based arena heap across all 11 crates.',
    givenUp: 'Zero-overhead raw pointers, direct C FFI shortcuts, and unchecked memory tricks.',
    gained: 'Use-after-free and out-of-bounds memory corruption are ruled out by Rust’s type system before Z3 checks a single invariant.',
    residual: 'Logical type confusion remains expressible unless ECMA-262 §6.1.7.3 object invariants hold across every exotic object—requiring strict coverage as built-ins expand.',
  },
  {
    decision: 'Verified tricolor mark-sweep garbage collector (J6 vjs_gc) under per-realm heap quotas.',
    givenUp: 'Generational or concurrent collector throughput and off-the-shelf allocator reuse.',
    gained: 'Reachable-object preservation and zero dangling arena indices are machine-proved alongside Promise FIFO liveness and Proxy invariants.',
    residual: 'Stop-the-world pause latency on large DOM-backed heaps has not yet been tuned for interactive 60fps browsing.',
  },
  {
    decision: 'ECMA-262 specs compiled from pinned ESMeta <emu-alg> clauses; generator untrusted, generated spec audited.',
    givenUp: 'Automatic tracking of living-standard edits without deliberate spec re-pinning.',
    gained: 'Removes manual transcription drift (JSCert’s failure mode) and cross-checks generated clauses against test262 and hundreds of thousands of differential cases.',
    residual: 'The pinned spec text sits in the trusted base: if a spec clause is wrong, the proof certifies the wrong behavior until differential tests catch it.',
  },
  {
    decision: 'Deterministic fuel semantics: every evaluation returns Done(v), OutOfFuel, or Unsupported(f).',
    givenUp: 'Unbounded script execution; real web pages need a host fuel policy.',
    gained: 'Termination is provable everywhere, Warblre-style RegExp execution kills catastrophic backtracking (ReDoS), and unsupported features refuse explicitly instead of guessing.',
    residual: 'Choosing an overly tight fuel budget can break legitimate pages, while a loose budget widens UI hang risk.',
  },
  {
    decision: 'Explicit Unsupported refusals with a monotonic coverage ratchet rather than silent fallbacks.',
    givenUp: 'Immediate drop-in compatibility with every legacy website on day one.',
    gained: 'Every verified section reports exact conformance counts; coverage only rises between releases and gaps are never papered over.',
    residual: 'Until crawl-corpus parity is reached, an unverified fallback renderer remains in the isolation envelope for unsupported sites.',
  },
  {
    decision: 'Generational kernel-issued capability handles across the verified Web IDL boundary (J4b vjs_webidl).',
    givenUp: 'Direct ambient access to host objects and low-friction DOM bindings.',
    gained: 'Zero ambient authority in script execution; no-use-after-revoke and cross-origin non-interference are proved across the ToJS/ToIDL boundary.',
    residual: 'Full browser DOM API surface (hundreds of Web IDL interfaces) still needs incremental binding coverage beyond the verified core.',
  },
  {
    decision: 'Per-algorithm exec == spec proofs with lexicographic decreases and strict per-function rlimits.',
    givenUp: 'Rapid unchecked feature velocity as language surface area grows.',
    gained: 'Every crate produces composable end-to-end theorems that re-verify reproducibly in CI with zero admit or assume escape hatches.',
    residual: 'Solver sensitivity to Z3 upgrades demands weekly upstream Verus tracking and disciplined proof modularity.',
  },
  {
    decision: 'Verify the JS/Wasm core and security kernel; contain HTML/CSS/XML and per-site GPU; ship no extension API in v1.',
    givenUp: 'Whole-browser verification ambition and browser extension ecosystem in release 1.',
    gained: 'Keeps the trusted computing base tractable while removing the extension/loader attack surface altogether.',
    residual: 'Containment depends on finishing the kernel isolation theorems and Nanvix sandboxing; 4/20 recent ITW CVEs (Dawn, Skia, ANGLE) remain unproved by design.',
  },
];
