// Pane 02 — what formal verification has actually shipped, with sources.
// Figures are the published ones; where a number is approximate it is marked ≈.
export interface VerifiedSystem {
  name: string;
  href: string;
  proved: string;
  scale: string;
  ships: string;
}

export const SYSTEMS: VerifiedSystem[] = [
  {
    name: 'seL4 (2009)',
    href: 'https://sel4.systems/',
    proved: 'Functional correctness of the kernel against an abstract spec; later integrity + confidentiality',
    scale: '8,700 LOC C · ≈20 person-years of proof',
    ships: 'High-assurance platforms (HACMS and successors)',
  },
  {
    name: 'CompCert (2009–)',
    href: 'https://compcert.org/',
    proved: 'Semantics preservation of C compilation, end to end',
    scale: 'Tens of thousands of lines of Coq',
    ships: 'Avionics / nuclear / railway toolchains',
  },
  {
    name: 'fiat-crypto (2017)',
    href: 'https://github.com/mit-plv/fiat-crypto',
    proved: 'Correctness of cryptographic field arithmetic',
    scale: 'Generated C/asm with machine-checked proofs',
    ships: 'BoringSSL → Chrome',
  },
  {
    name: 'HACL* / EverCrypt',
    href: 'https://github.com/hacl-star/hacl-star',
    proved: 'Memory safety, functional correctness, secret independence',
    scale: 'F* → verified C/asm',
    ships: 'Firefox (NSS)',
  },
  {
    name: 'Verdict (2025)',
    href: 'https://github.com/secure-foundations/verdict',
    proved: 'X.509 path validation == a readable policy spec',
    scale: 'Policies 372–405 lines · whole project verifies in 57 s',
    ships: 'Research (USENIX Security ’25) — this project’s TLS layer',
  },
  {
    name: 'Quark (2012)',
    href: 'https://www.usenix.org/conference/usenixsecurity12/technical-sessions/presentation/jang',
    proved: 'Tab non-interference, cookie integrity, address-bar correctness',
    scale: 'Coq kernel; unmodified WebKit as untrusted tabs',
    ships: 'Research browser — the pattern this engine copies',
  },
  {
    name: 'JSCert / JSRef (2014)',
    href: 'https://github.com/jscert/jscert',
    proved: 'ES5 semantics in Coq; extracted interpreter proved correct',
    scale: 'ES5 chapters 8–14; found bugs in browsers, the spec, test262',
    ships: 'Research — the cautionary tale vjs answers',
  },
  {
    name: 'Warblre (2024)',
    href: 'https://arxiv.org/abs/2403.11919',
    proved: 'ES2023 regex matching terminates and matches the spec',
    scale: 'Coq, spec text interleaved line by line · 495/498 test262',
    ships: 'Research — vjs ports its semantics (J5)',
  },
  {
    name: 'WasmCert / vWasm',
    href: 'https://github.com/WasmCert/WasmCert-Coq',
    proved: 'Wasm semantics; provably safe sandboxing of compiled code',
    scale: 'Coq / Isabelle',
    ships: 'Research — the route to containing an untrusted JIT',
  },
];

export const SCALE_ITEMS = [
  {
    id: 'sel4',
    label: 'seL4 kernel — verified (2009)',
    lines: 8_700,
    display: '8,700 LOC',
    tone: 'verified' as const,
    note: '≈20 person-years of Isabelle proof for this much C',
  },
  {
    id: 'linux',
    label: 'Linux kernel — unverified (2023)',
    lines: 36_000_000,
    display: '≈36,000,000 LOC',
    tone: 'critical' as const,
    note: 'Linux Foundation 2023 kernel report; drivers are the majority of the code',
  },
];