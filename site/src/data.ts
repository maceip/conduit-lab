export const NR = 'not recorded';

export interface TrustedCounts {
  assume: number;
  admit: number;
  external_body: number;
  external: number;
  assume_specification: number;
  unsafe: number;
}

export interface RatchetCrate {
  name: string;
  path?: string;
  step?: string;
  scope?: string;
  theorem?: string;
  verify_exit: number;
  verified: number;
  errors: number;
  verify_seconds: number;
  trusted: TrustedCounts;
  source_lines: number;
  tests_exit: number;
  tests_passed: number;
  tests_failed: number;
  test_seconds: number;
  log?: string;
  proof_source?: string;
}

export interface RatchetTotals {
  crates: number;
  verified: number;
  errors: number;
  trusted: TrustedCounts;
  source_lines: number;
  tests_passed: number;
  tests_failed: number;
  verify_seconds: number;
  test_seconds: number;
}

export interface RatchetJStep {
  step: string;
  scope: string;
  theorem: string;
  status: string;
  verified: number;
  errors: number;
  trusted: number;
  tests_passed: number;
  verify_seconds: number;
  crate: string;
  crates?: string[];
  test262_passed: number;
  test262_total: number;
}

export interface RatchetSuite {
  suite: string;
  crate: string;
  step: string;
  passed: number;
  total: number;
  failed?: number;
  unsupported?: number;
  differential_cases?: number | null;
}

export interface VmBenchmark {
  name: string;
  iterations: number;
  ast_ms: number;
  bytecode_ms: number;
  speedup: number;
  result_verified_equal: boolean;
}

export interface Ratchet {
  generated_at: string;
  generator: string;
  crates: RatchetCrate[];
  verus: string;
  totals?: RatchetTotals;
  j_steps?: RatchetJStep[];
  test262_suites?: RatchetSuite[];
  vm_benchmarks?: VmBenchmark[];
  vm_benchmarks_geomean_speedup?: number;
}

export interface Stats {
  generated_at: string;
  host?: { system?: string; release?: string; machine?: string };
  toolchains?: Record<string, string>;
  duration_seconds?: number;
}

export async function loadJson<T>(url: string): Promise<T> {
  const r = await fetch(url, { cache: 'no-cache' });
  if (!r.ok) throw new Error(`HTTP ${r.status}`);
  return (await r.json()) as T;
}

export const sumTrusted = (t: TrustedCounts | undefined): number | null =>
  t ? Object.values(t).reduce((a, b) => a + b, 0) : null;

export const crateOk = (c: RatchetCrate | undefined): boolean =>
  !!c && c.verify_exit === 0 && c.errors === 0;

export const allCratesOk = (r: Ratchet | null): boolean =>
  !!r && r.crates.length > 0 && r.crates.every(crateOk);

export const trustedTotal = (c: RatchetCrate | undefined): number | null =>
  sumTrusted(c?.trusted);

export const ratchetTotals = (r: Ratchet | null): RatchetTotals | null => {
  if (!r) return null;
  if (r.totals) return r.totals;
  const trusted: TrustedCounts = {
    assume: 0,
    admit: 0,
    external_body: 0,
    external: 0,
    assume_specification: 0,
    unsafe: 0,
  };
  let verified = 0;
  let errors = 0;
  let source_lines = 0;
  let tests_passed = 0;
  let tests_failed = 0;
  let verify_seconds = 0;
  let test_seconds = 0;
  for (const c of r.crates) {
    verified += c.verified;
    errors += c.errors;
    source_lines += c.source_lines;
    tests_passed += c.tests_passed;
    tests_failed += c.tests_failed;
    verify_seconds += c.verify_seconds;
    test_seconds += c.test_seconds;
    trusted.assume += c.trusted.assume;
    trusted.admit += c.trusted.admit;
    trusted.external_body += c.trusted.external_body;
    trusted.external += c.trusted.external;
    trusted.assume_specification += c.trusted.assume_specification;
    trusted.unsafe += c.trusted.unsafe;
  }
  return {
    crates: r.crates.length,
    verified,
    errors,
    trusted,
    source_lines,
    tests_passed,
    tests_failed,
    verify_seconds: Math.round(verify_seconds * 100) / 100,
    test_seconds: Math.round(test_seconds * 100) / 100,
  };
};

export const fmtDate = (iso: string | undefined): string =>
  iso ? new Date(iso).toLocaleString(undefined, { dateStyle: 'medium', timeStyle: 'short' }) : NR;

export const REPO = 'https://github.com/maceip/conduit-lab';
export const BRANCH = 'main';
export const blobUrl = (path: string) => `${REPO}/blob/${BRANCH}/${path}`;
