// Landmark shipped and research formal verification systems, with primary sources.
export interface VerifiedSystem {
  name: string;
  href: string;
  proved: string;
  scale: string;
  role: string;
}

export const SYSTEMS: VerifiedSystem[] = [
  {
    name: 'seL4 (2009)',
    href: 'https://sel4.systems/',
    proved: 'End-to-end functional correctness, integrity, and confidentiality of an OS microkernel',
    scale: '8,700 LOC C · ≈20 person-years (Isabelle/HOL)',
    role: 'Benchmark for small-kernel proof discipline',
  },
  {
    name: 'CompCert (2009–)',
    href: 'https://compcert.org/',
    proved: 'Semantics preservation across an optimizing C compiler pipeline',
    scale: 'Tens of thousands of lines of Coq',
    role: 'Simulation-proof pattern used in vjs_vm',
  },
  {
    name: 'fiat-crypto (2017)',
    href: 'https://github.com/mit-plv/fiat-crypto',
    proved: 'Correctness of generated elliptic-curve field arithmetic',
    scale: 'Verified C & assembly generation (Coq)',
    role: 'Ships inside BoringSSL → Chrome',
  },
  {
    name: 'HACL* / EverCrypt',
    href: 'https://github.com/hacl-star/hacl-star',
    proved: 'Memory safety, functional correctness, and secret independence',
    scale: 'F* extracted to verified C & assembly',
    role: 'Ships inside Firefox (NSS)',
  },
  {
    name: 'Verdict (2025)',
    href: 'https://github.com/secure-foundations/verdict',
    proved: 'X.509 certificate path validation equivalent to a readable policy spec',
    scale: '372–405 LOC policies · 57s full Verus verify',
    role: 'CONDUIT’s planned TLS validation layer & Vest/rspec! model',
  },
  {
    name: 'Quark (2012)',
    href: 'https://www.usenix.org/conference/usenixsecurity12/technical-sessions/presentation/jang',
    proved: 'Tab non-interference, cookie integrity, and address-bar authenticity',
    scale: 'Coq kernel gating unmodified WebKit renderers',
    role: 'Kernel-and-sandbox shim pattern CONDUIT adapts',
  },
  {
    name: 'JSCert / JSRef (2014)',
    href: 'https://github.com/jscert/jscert',
    proved: 'Mechanized ES5 semantics and verified extracted reference interpreter',
    scale: 'ES5 ch. 8–14 in Coq; surfaced spec & test262 bugs',
    role: 'Cautionary lesson: left parsing unverified (vjs_syntax proves lexer & parser)',
  },
  {
    name: 'Warblre (2024)',
    href: 'https://arxiv.org/abs/2403.11919',
    proved: 'ECMAScript 2023 RegExp compilation and matching always terminate cleanly',
    scale: 'Coq spec interleaved line by line · 495/498 test262',
    role: 'Terminating RegExp model ported into vjs_builtins',
  },
  {
    name: 'WasmCert / vWasm',
    href: 'https://github.com/WasmCert/WasmCert-Coq',
    proved: 'WebAssembly type soundness and provably safe linear-memory sandboxing',
    scale: 'Coq / Isabelle mechanized semantics & SFI',
    role: 'Linear-memory containment model proved in vwasm',
  },
];

export const SCALE_ITEMS = [
  {
    id: 'sel4',
    label: 'seL4 microkernel — proved (2009)',
    lines: 8_700,
    display: '8,700 LOC',
    tone: 'proved' as const,
    note: '≈20 person-years of Isabelle proof for a minimal, fixed C API',
  },
  {
    id: 'linux',
    label: 'Linux kernel — unverified (2023)',
    lines: 36_000_000,
    display: '≈36,000,000 LOC',
    tone: 'fail' as const,
    note: 'Linux Foundation 2023 report; device drivers dominate both size and bug counts',
  },
];
