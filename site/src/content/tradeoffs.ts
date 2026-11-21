// Condensed from docs/vjs-plan-review.md §1 ("Tradeoffs the plan is making").
export interface Tradeoff {
  decision: string;
  givenUp: string;
  gained: string;
  residual: string;
}

export const TRADEOFFS: Tradeoff[] = [
  {
    decision: 'Interpreter only; no JIT ever in the TCB. Bytecode + simulation proof deferred to J7.',
    givenUp: '~10–100× performance vs TurboFan/Maglev; verified-script mode is slow on day one.',
    gained: 'The JIT-compiler bug class — where most exploited V8 bugs live — becomes inexpressible.',
    residual: 'The bytecode-compiler proof is unsized and far out; perf is "measured at J7", not a requirement.',
  },
  {
    decision: 'Safe Rust, #![forbid(unsafe_code)], index-based arena heap.',
    givenUp: 'FFI/ecosystem convenience; raw speed.',
    gained: 'UAF / OOB-write memory corruption eliminated by construction, before any proof runs.',
    residual: 'Logical type confusion is still possible — caught only if the §6.1.7.3 invariant proofs cover every exotic object.',
  },
  {
    decision: 'Verified mark-sweep GC at J6; an unverified safe-Rust collector under a per-realm quota until then (J4).',
    givenUp: 'A simple bump/leak or off-the-shelf collector.',
    gained: 'No dangling indices, no GC-introduced UAF; worst case in the interim is leaks/slowdown, never UAF.',
    residual: 'GC-preservation proofs are among the hardest in the plan, and J6 is late in the order.',
  },
  {
    decision: 'Spec generated from ESMeta’s mechanized ECMA-262, pinned commit. Generator untrusted; generated spec trusted.',
    givenUp: 'Freedom from spec-drift management; the TCB now includes the spec text + human review.',
    gained: 'No transcription-error class (JSRef’s pitfall); line-by-line fidelity; differential-tested vs test262 + ESMeta.',
    residual: 'A wrong spec is a proved-wrong engine (Verdict’s caveat). A pinned commit means a continuous re-diff obligation.',
  },
  {
    decision: 'Fuel semantics: Done / OutOfFuel / Unsupported — nothing else.',
    givenUp: 'Liveness; real sites need a fuel policy that is itself an unverified operational knob.',
    gained: 'Termination provable everywhere; the Warblre regex port kills ReDoS; refusals are never wrong answers.',
    residual: 'Hangs become a DoS surface if the fuel policy is wrong; Warblre has 3 known test262 divergences.',
  },
  {
    decision: 'Explicit Unsupported + "verified script" mode; untrusted engine kept until crawl-corpus parity — removal measured, not scheduled.',
    givenUp: 'Web compatibility for years; the motivating attack surface (an unverified engine) ships in the meantime.',
    gained: 'An honesty ratchet: coverage published per section, never silently approximated.',
    residual: 'No timeline ⇒ the fallback could become permanent; parity is a functional bar, not a security bar.',
  },
  {
    decision: 'Kernel-issued capability handles; verified Web IDL ToJS/ToIDL conversion layer (J4b).',
    givenUp: 'Direct-binding performance and convenience.',
    gained: 'No ambient authority in the engine; a renderer compromise cannot forge capabilities.',
    residual: 'The largest unsized verification surface in the plan — now carries a phase and an exit criterion (J4b).',
  },
  {
    decision: 'Per-algorithm exec == spec proofs, lexicographic decreases, per-function rlimit budgets.',
    givenUp: 'Proof velocity as specs grow; solver stability.',
    gained: 'One composable end-to-end theorem per component, Verdict-style.',
    residual: 'ECMA-262 is several times JSRef’s ES5 ch. 8–14 scope; effort is explicitly unestimated.',
  },
  {
    decision: 'Verify the JS engine + kernel/policy; contain everything else (Quark shim). No extension API at release 1.',
    givenUp: 'Whole-stack verification ambition; extension ecosystem.',
    gained: 'A tractable TCB; renderers outside it; a usable browser before the proofs finish.',
    residual: 'Containment is only as good as the kernel theorems + Nanvix isolation; 4/20 recent ITW CVEs (graphics) stay outside verified scope.',
  },
];