export const NR = 'not recorded';

export interface RatchetCrate {
  name: string;
  verify_exit: number;
  verified: number;
  errors: number;
  verify_seconds: number;
  trusted: {
    assume: number;
    admit: number;
    external_body: number;
    external: number;
    assume_specification: number;
    unsafe: number;
  };
  source_lines: number;
  tests_exit: number;
  tests_passed: number;
  tests_failed: number;
  test_seconds: number;
}

export interface Ratchet {
  generated_at: string;
  generator: string;
  crates: RatchetCrate[];
  verus: string;
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

export const crateOk = (c: RatchetCrate | undefined): boolean =>
  !!c && c.verify_exit === 0 && c.errors === 0;

export const trustedTotal = (c: RatchetCrate | undefined): number | null =>
  c ? Object.values(c.trusted).reduce((a, b) => a + b, 0) : null;

export const fmtDate = (iso: string | undefined): string =>
  iso ? new Date(iso).toLocaleString(undefined, { dateStyle: 'medium', timeStyle: 'short' }) : NR;

export const REPO = 'https://github.com/maceip/conduit-lab';
export const BRANCH = 'verified-browser-design';
export const blobUrl = (path: string) => `${REPO}/blob/${BRANCH}/${path}`;