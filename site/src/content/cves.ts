// Last 20 Chrome CVEs confirmed exploited in the wild by Google (as of 2026-11-20).
// Every row is verified against primary sources in docs/vjs-plan-review.md §2
// (Chrome Releases Blog ITW wording, cross-checked against CISA KEV v2026.11.18).
export type Coverage = 'construction' | 'containment' | 'graphics';

export interface CveRow {
  cve: string;
  patched: string;
  component: string;
  klass: string;
  fixedIn: string;
  reporter: string;
  kev: string;
  coverage: Coverage;
}

export const CVES: CveRow[] = [
  { cve: 'CVE-2026-125350', patched: '2026-11-09', component: 'XML (Blink)', klass: 'Use-after-free', fixedIn: '157.0.8103.50', reporter: 'Neonix Security + anonymous', kev: 'Added 2026-11-10', coverage: 'containment' },
  { cve: 'CVE-2026-87491', patched: '2026-09-08', component: 'V8', klass: 'Out-of-bounds write', fixedIn: '152.0.7977.x', reporter: 'Google (reported 2026-08-27)', kev: 'Added 2026-09-09', coverage: 'construction' },
  { cve: 'CVE-2026-85046', patched: '2026-09-03', component: 'V8', klass: 'Type confusion', fixedIn: '152.0.7977.82', reporter: 'Salvatore Gulizia', kev: 'Added 2026-09-04', coverage: 'construction' },
  { cve: 'CVE-2026-11645', patched: '2026-06-08', component: 'V8', klass: 'Out-of-bounds read/write', fixedIn: '149.0.7827.102', reporter: 'Pseudonymous', kev: 'Added 2026-06-09', coverage: 'construction' },
  { cve: 'CVE-2026-5281', patched: '2026-03-31', component: 'Dawn (WebGPU)', klass: 'Use-after-free', fixedIn: '146.0.7680.177', reporter: 'Undisclosed', kev: 'Not in KEV', coverage: 'graphics' },
  { cve: 'CVE-2026-3909', patched: '2026-03-13', component: 'Skia', klass: 'Out-of-bounds write', fixedIn: '146.0.7680.80', reporter: 'Google TAG (targeted)', kev: 'Not in KEV', coverage: 'graphics' },
  { cve: 'CVE-2026-3910', patched: '2026-03-12', component: 'V8', klass: 'Inappropriate implementation', fixedIn: '146.0.7680.75', reporter: 'Google TAG', kev: 'Added 2026-03-13', coverage: 'construction' },
  { cve: 'CVE-2026-2441', patched: '2026-02-13', component: 'CSS (Blink)', klass: 'Use-after-free', fixedIn: '145.0.7632.75', reporter: 'Shaheen Fazim', kev: 'Added 2026-02-17', coverage: 'containment' },
  { cve: 'CVE-2025-14174', patched: '2025-12-10', component: 'ANGLE', klass: 'Out-of-bounds memory access', fixedIn: '143.0.7499.109', reporter: 'Apple SEAR + Google TAG', kev: 'Added 2025-12-12', coverage: 'graphics' },
  { cve: 'CVE-2025-13223', patched: '2025-11-17', component: 'V8', klass: 'Type confusion', fixedIn: '142.0.7444.175', reporter: 'Google TAG', kev: 'Added 2025-11-19', coverage: 'construction' },
  { cve: 'CVE-2025-10585', patched: '2025-09-17', component: 'V8', klass: 'Type confusion', fixedIn: '140.0.7339.185', reporter: 'Google TAG', kev: 'Added 2025-09-23', coverage: 'construction' },
  { cve: 'CVE-2025-6558', patched: '2025-07-15', component: 'ANGLE + GPU', klass: 'Validation flaw (potential escape)', fixedIn: '138.0.7204.157', reporter: 'Google TAG (Lecitre, Stolyarov)', kev: 'Added 2025-07-22', coverage: 'graphics' },
  { cve: 'CVE-2025-6554', patched: '2025-06-30', component: 'V8', klass: 'Type confusion (arbitrary r/w)', fixedIn: '138.0.7204.96', reporter: 'Google TAG (Lecitre)', kev: 'Added 2025-07-02', coverage: 'construction' },
  { cve: 'CVE-2025-5419', patched: '2025-06-02', component: 'V8', klass: 'Out-of-bounds read/write', fixedIn: '137.0.7151.68', reporter: 'Google TAG (Lecitre, Sevens)', kev: 'Added 2025-06-05', coverage: 'construction' },
  { cve: 'CVE-2025-2783', patched: '2025-03-25', component: 'Mojo (Windows)', klass: 'Sandbox escape (incorrect handle)', fixedIn: '134.0.6998.165', reporter: 'Kaspersky', kev: 'Added 2025-03-27', coverage: 'containment' },
  { cve: 'CVE-2024-7965', patched: '2024-08-21', component: 'V8', klass: 'Inappropriate implementation', fixedIn: '128.0.6613.119', reporter: 'TheDog', kev: 'Added 2024-08-28', coverage: 'construction' },
  { cve: 'CVE-2024-7971', patched: '2024-08-21', component: 'V8', klass: 'Type confusion', fixedIn: '128.0.6613.119', reporter: 'Undisclosed', kev: 'Added 2024-08-26', coverage: 'construction' },
  { cve: 'CVE-2024-5274', patched: '2024-05-23', component: 'V8 (Windows)', klass: 'Type confusion', fixedIn: '125.0.6422.112', reporter: 'Google TAG + Chrome Security', kev: 'Added 2024-05-28', coverage: 'construction' },
  { cve: 'CVE-2024-4947', patched: '2024-05-15', component: 'V8', klass: 'Type confusion', fixedIn: '124.0.6367.201', reporter: 'Kaspersky (Berdnikov, Larin)', kev: 'Added 2024-05-20', coverage: 'construction' },
  { cve: 'CVE-2024-4761', patched: '2024-05-13', component: 'V8 (macOS first)', klass: 'Out-of-bounds write', fixedIn: '124.0.6367.207', reporter: 'Anonymous', kev: 'Added 2024-05-16', coverage: 'construction' },
];

export const COVERAGE_LABEL: Record<Coverage, string> = {
  construction: 'Eliminated in vjs',
  containment: 'Trapped by kernel',
  graphics: 'Unverified GPU (per-site)',
};

export const COVERAGE_SHORT: Record<Coverage, string> = {
  construction: 'Eliminated in vjs',
  containment: 'Kernel isolation',
  graphics: 'Unverified GPU',
};

export const coverageTone = (c: Coverage): 'proved' | 'warn' | 'fail' =>
  c === 'construction' ? 'proved' : c === 'containment' ? 'warn' : 'fail';

export const COVERAGE_DETAIL: Record<Coverage, string> = {
  construction:
    'Ruled out at compile time in vjs (J0–J7 crates verified with zero unsafe code): no optimizing JIT sits in the trusted base, memory lives in a safe-Rust indexed arena heap, and ECMA-262 §6.1.7.3 object invariants are proved. Wiring vjs behind the verified kernel is next.',
  containment:
    'Isolated once the browser kernel theorems land: XML and CSS parser bugs stay trapped inside a disposable per-site renderer, and typed Vest-encoded capability handles replace raw cross-process IPC. The kernel non-interference proofs are still design work.',
  graphics:
    'Outside formal verification. Dawn, Skia, and ANGLE have no verified replacements planned. Graphics translation and rasterization run per-site inside the renderer sandbox instead of a shared GPU process—containing the blast radius without pretending the GPU stack is proved.',
};
