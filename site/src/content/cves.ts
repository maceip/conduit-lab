// The last 20 Chrome CVEs Google confirmed exploited in the wild (as of 2026-11-20).
// Transcribed from docs/vjs-plan-review.md §2, where every row was verified against
// primary sources (Chrome Releases Blog ITW wording, cross-checked with CISA KEV
// v2026.11.18). Coverage classes follow §3 of that review:
//   construction — V8 block: no-JIT safe-Rust vjs + object-model invariants (0% built today)
//   containment  — lands in untrusted renderers / IPC; Quark-style kernel theorems apply
//   graphics     — Dawn / Skia / ANGLE: no verified replacement planned; contained, not proved
export type Coverage = 'construction' | 'containment' | 'graphics';

export interface CveRow {
  cve: string;
  patched: string;
  component: string;
  klass: string;
  coverage: Coverage;
  [key: string]: string;
}

export const CVES: CveRow[] = [
  { cve: 'CVE-2026-125350', patched: '2026-11-09', component: 'XML (Blink)', klass: 'use-after-free', coverage: 'containment' },
  { cve: 'CVE-2026-87491', patched: '2026-09-08', component: 'V8', klass: 'OOB write', coverage: 'construction' },
  { cve: 'CVE-2026-85046', patched: '2026-09-03', component: 'V8', klass: 'type confusion', coverage: 'construction' },
  { cve: 'CVE-2026-11645', patched: '2026-06-08', component: 'V8', klass: 'OOB read/write', coverage: 'construction' },
  { cve: 'CVE-2026-5281', patched: '2026-03-31', component: 'Dawn (WebGPU)', klass: 'use-after-free', coverage: 'graphics' },
  { cve: 'CVE-2026-3909', patched: '2026-03-13', component: 'Skia', klass: 'OOB write', coverage: 'graphics' },
  { cve: 'CVE-2026-3910', patched: '2026-03-12', component: 'V8', klass: 'inappropriate impl.', coverage: 'construction' },
  { cve: 'CVE-2026-2441', patched: '2026-02-13', component: 'CSS (Blink)', klass: 'use-after-free', coverage: 'containment' },
  { cve: 'CVE-2025-14174', patched: '2025-12-10', component: 'ANGLE', klass: 'OOB memory access', coverage: 'graphics' },
  { cve: 'CVE-2025-13223', patched: '2025-11-17', component: 'V8', klass: 'type confusion', coverage: 'construction' },
  { cve: 'CVE-2025-10585', patched: '2025-09-17', component: 'V8', klass: 'type confusion', coverage: 'construction' },
  { cve: 'CVE-2025-6558', patched: '2025-07-15', component: 'ANGLE + GPU', klass: 'validation → potential escape', coverage: 'graphics' },
  { cve: 'CVE-2025-6554', patched: '2025-06-30', component: 'V8', klass: 'type confusion (arb. r/w)', coverage: 'construction' },
  { cve: 'CVE-2025-5419', patched: '2025-06-02', component: 'V8', klass: 'OOB read/write', coverage: 'construction' },
  { cve: 'CVE-2025-2783', patched: '2025-03-25', component: 'Mojo (Windows)', klass: 'sandbox escape (handle)', coverage: 'containment' },
  { cve: 'CVE-2024-7965', patched: '2024-08-21', component: 'V8', klass: 'inappropriate impl.', coverage: 'construction' },
  { cve: 'CVE-2024-7971', patched: '2024-08-21', component: 'V8', klass: 'type confusion', coverage: 'construction' },
  { cve: 'CVE-2024-5274', patched: '2024-05-23', component: 'V8 (Windows)', klass: 'type confusion', coverage: 'construction' },
  { cve: 'CVE-2024-4947', patched: '2024-05-15', component: 'V8', klass: 'type confusion', coverage: 'construction' },
  { cve: 'CVE-2024-4761', patched: '2024-05-13', component: 'V8 (Mac first)', klass: 'OOB write', coverage: 'construction' },
];

export const COVERAGE_LABEL: Record<Coverage, string> = {
  construction: 'by construction (vjs)',
  containment: 'by containment (kernel)',
  graphics: 'not covered — contained',
};

export const coverageTone = (c: Coverage): 'verified' | 'warning' | 'critical' =>
  c === 'construction' ? 'verified' : c === 'containment' ? 'warning' : 'critical';

export const COVERAGE_DETAIL: Record<Coverage, string> = {
  construction:
    'By construction, once vjs is built: no JIT in the verified core, a safe-Rust arena heap, and object-model invariant proofs target exactly this bug class. vjs is not built yet, so today this class is only contained by the renderer sandbox.',
  containment:
    'By containment, if the kernel theorems land: the bug lives in an untrusted renderer or in IPC, and the verified kernel plus per-site sandbox is supposed to make a compromise non-escapable. The kernel theorems are still design.',
  graphics:
    'Not covered by proofs. Dawn, Skia and ANGLE have no verified replacement planned; GPU work runs per-site inside the renderer sandbox. Containment limits the blast radius but does not remove the bug class.',
};