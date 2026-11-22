export const NR = 'not recorded';

/** Textual trust markers by kind; the kinds are ratchet.py's MARKERS. */
export type TrustedCounts = Record<string, number>;

/** Functions Verus sent to the solver, by mode. */
export interface FunctionsByMode {
  exec: number;
  proof: number;
  spec: number;
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
  /** Verified as a root under `--no-cheating`. */
  no_cheating: boolean;
  functions_by_mode: FunctionsByMode;
  verify_seconds: number;
  trusted: TrustedCounts;
  vacuous_requires: number;
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
  functions_by_mode: FunctionsByMode;
  vacuous_requires: number;
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

export interface ProofShowcaseItem {
  label: string;
  crate: string;
  step: string;
  file: string;
  source: string;
  verified: number;
  errors: number;
  seconds: number;
  log: string;
  exit_code: number;
}

export interface Ratchet {
  generated_at: string;
  generator: string;
  crates: RatchetCrate[];
  verus: string;
  /** Digest of everything under browser/ the run depended on. */
  inputs_sha256?: string;
  totals?: RatchetTotals;
  j_steps?: RatchetJStep[];
  test262_suites?: RatchetSuite[];
  vm_benchmarks?: VmBenchmark[];
  vm_benchmarks_geomean_speedup?: number;
  proof_showcase?: ProofShowcaseItem[];
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

export async function loadText(url: string): Promise<string> {
  const r = await fetch(url, { cache: 'no-cache' });
  if (!r.ok) throw new Error(`HTTP ${r.status}`);
  return await r.text();
}

export const sumTrusted = (t: TrustedCounts | undefined): number | null =>
  t ? Object.values(t).reduce((a, b) => a + b, 0) : null;

/** Every check ratchet.py fails on. A field missing from the report counts as failing. */
export const crateOk = (c: RatchetCrate | undefined): boolean =>
  !!c &&
  c.verify_exit === 0 &&
  c.errors === 0 &&
  c.no_cheating === true &&
  sumTrusted(c.trusted) === 0 &&
  c.vacuous_requires === 0 &&
  c.tests_exit === 0 &&
  c.tests_failed === 0;

export const allCratesOk = (r: Ratchet | null): boolean =>
  !!r && r.crates.length > 0 && r.crates.every(crateOk);

export const trustedTotal = (c: RatchetCrate | undefined): number | null =>
  sumTrusted(c?.trusted);

export const sumDifferentialCases = (suites: RatchetSuite[] | undefined): number | null => {
  if (!suites || suites.length === 0) return null;
  let total = 0;
  for (const s of suites) {
    if (typeof s.differential_cases === 'number') total += s.differential_cases;
  }
  return total;
};

export const ratchetTotals = (r: Ratchet | null): RatchetTotals | null => {
  return r?.totals ?? null;
};

export const fmtDate = (iso: string | undefined): string =>
  iso ? new Date(iso).toLocaleString(undefined, { dateStyle: 'medium', timeStyle: 'short' }) : NR;

export const REPO = 'https://github.com/maceip/conduit-lab';
export const BRANCH = 'main';
export const blobUrl = (path: string) => `${REPO}/blob/${BRANCH}/${path}`;
