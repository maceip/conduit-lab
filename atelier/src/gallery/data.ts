import ratchetDocument from '../../../browser/ratchet.json';
import statsDocument from '../../../data/stats.json';

/**
 * The atelier's data loader.
 *
 * Every figure the gallery shows comes from `browser/ratchet.json` or
 * `data/stats.json`, imported directly so Vite bundles the real reports at
 * build time. There is no mock data and no fallback number anywhere in this
 * module: a field the sources do not carry reads as {@link NOT_RECORDED},
 * never as a zero that would look like a measurement.
 */

/** Rendered in place of any figure the sources did not record. */
export const NOT_RECORDED = 'not recorded';

/**
 * A value that may or may not have been recorded.
 *
 * The `recorded` flag is what keeps a real zero (`trusted: 0`) distinguishable
 * from a missing field. Only `recorded: true` may be rendered as a number.
 */
export type Recorded<T> =
  | { readonly recorded: true; readonly value: T }
  | { readonly recorded: false; readonly value: null };

/* ------------------------------------------------------------------ *
 * Primitive readers
 * ------------------------------------------------------------------ */

function isRecord(value: unknown): value is Record<string, unknown> {
  return typeof value === 'object' && value !== null && !Array.isArray(value);
}

function readNumber(source: Record<string, unknown> | null, key: string): Recorded<number> {
  const value = source?.[key];
  return typeof value === 'number' && Number.isFinite(value)
    ? { recorded: true, value }
    : { recorded: false, value: null };
}

function readString(source: Record<string, unknown> | null, key: string): Recorded<string> {
  const value = source?.[key];
  return typeof value === 'string' && value.length > 0
    ? { recorded: true, value }
    : { recorded: false, value: null };
}

function readBoolean(source: Record<string, unknown> | null, key: string): Recorded<boolean> {
  const value = source?.[key];
  return typeof value === 'boolean' ? { recorded: true, value } : { recorded: false, value: null };
}

function readObject(
  source: Record<string, unknown> | null,
  key: string,
): Record<string, unknown> | null {
  const value = source?.[key];
  return isRecord(value) ? value : null;
}

function readArray(source: Record<string, unknown> | null, key: string): unknown[] | null {
  const value = source?.[key];
  return Array.isArray(value) ? value : null;
}

/* ------------------------------------------------------------------ *
 * Trusted items — the ratchet's obligation markers
 * ------------------------------------------------------------------ */

/**
 * The obligation markers `browser/scripts/ratchet.py` counts, in the order the
 * ratchet writes them.
 *
 * The categories are disjoint — `external_spec` counts every `external_*`
 * token except `external_body`, and `external` counts only the exact token —
 * so summing them gives the true trusted-item count. This is the same figure
 * the live site prints as "trusted items".
 */
export const OBLIGATION_KINDS = [
  'assume',
  'admit',
  'external_body',
  'external',
  'external_spec',
  'assume_specification',
  'axiom',
  'unproved_termination',
  'hidden_from_verus',
  'unsafe',
] as const;

export type ObligationKind = (typeof OBLIGATION_KINDS)[number];

/** Per-marker counts, each independently recorded or not. */
export type ObligationCounts = { readonly [K in ObligationKind]: Recorded<number> };

/** Reads the `trusted` marker record. */
export function readObligations(source: Record<string, unknown> | null): ObligationCounts {
  const counts = {} as { -readonly [K in ObligationKind]: Recorded<number> };
  for (const kind of OBLIGATION_KINDS) {
    counts[kind] = readNumber(source, kind);
  }
  return counts;
}

/**
 * Totals the obligation markers.
 *
 * Recorded only when at least one marker carries a number: an absent or empty
 * `trusted` object means nothing was measured, and that must not read as zero.
 */
export function sumObligations(counts: ObligationCounts): Recorded<number> {
  let total = 0;
  let measured = 0;
  for (const kind of OBLIGATION_KINDS) {
    const entry = counts[kind];
    if (entry.recorded) {
      total += entry.value;
      measured += 1;
    }
  }
  return measured > 0 ? { recorded: true, value: total } : { recorded: false, value: null };
}

/* ------------------------------------------------------------------ *
 * Ratchet facts
 * ------------------------------------------------------------------ */

/** One verified crate from `ratchet.json`. */
export interface CrateFacts {
  readonly name: string;
  readonly step: Recorded<string>;
  readonly scope: Recorded<string>;
  readonly theorem: Recorded<string>;
  readonly verified: Recorded<number>;
  readonly errors: Recorded<number>;
  readonly noCheating: Recorded<boolean>;
  readonly trusted: ObligationCounts;
  readonly trustedTotal: Recorded<number>;
  readonly vacuousRequires: Recorded<number>;
  readonly sourceLines: Recorded<number>;
  readonly testsPassed: Recorded<number>;
  readonly testsFailed: Recorded<number>;
  readonly verifySeconds: Recorded<number>;
}

/** One J-step from `ratchet.json`. */
export interface JStepFacts {
  readonly step: string;
  readonly crate: Recorded<string>;
  readonly status: Recorded<string>;
  readonly verified: Recorded<number>;
  readonly errors: Recorded<number>;
  readonly trusted: Recorded<number>;
  readonly testsPassed: Recorded<number>;
  readonly test262Passed: Recorded<number>;
  readonly test262Total: Recorded<number>;
}

/** One test262 suite from `ratchet.json`. */
export interface SuiteFacts {
  readonly suite: string;
  readonly crate: Recorded<string>;
  readonly step: Recorded<string>;
  readonly passed: Recorded<number>;
  readonly total: Recorded<number>;
  readonly differentialCases: Recorded<number>;
}

/** One VM benchmark from `ratchet.json`. */
export interface VmBenchmarkFacts {
  readonly name: string;
  readonly iterations: Recorded<number>;
  readonly astMs: Recorded<number>;
  readonly bytecodeMs: Recorded<number>;
  readonly speedup: Recorded<number>;
  readonly resultVerifiedEqual: Recorded<boolean>;
}

/** Everything the gallery can say about the ratchet. */
export interface RatchetFacts {
  readonly generatedAt: Recorded<string>;
  readonly generator: Recorded<string>;
  readonly verusVersion: Recorded<string>;
  readonly verusCommit: Recorded<string>;
  /** `totals.crates` — the ratchet's own crate count. */
  readonly crateCount: Recorded<number>;
  /** `totals.verified` — verified queries across every crate. */
  readonly verifiedQueries: Recorded<number>;
  readonly errorCount: Recorded<number>;
  /** The sum of every obligation marker. */
  readonly trustedItemCount: Recorded<number>;
  readonly obligations: ObligationCounts;
  readonly functionsByMode: {
    readonly exec: Recorded<number>;
    readonly proof: Recorded<number>;
    readonly spec: Recorded<number>;
  };
  readonly vacuousRequires: Recorded<number>;
  readonly sourceLines: Recorded<number>;
  readonly testsPassed: Recorded<number>;
  readonly testsFailed: Recorded<number>;
  readonly verifySeconds: Recorded<number>;
  readonly testSeconds: Recorded<number>;
  readonly crates: Recorded<readonly CrateFacts[]>;
  readonly jSteps: Recorded<readonly JStepFacts[]>;
  readonly test262Suites: Recorded<readonly SuiteFacts[]>;
  readonly vmBenchmarks: Recorded<readonly VmBenchmarkFacts[]>;
  readonly specPins: Recorded<readonly string[]>;
}

function readCrate(entry: unknown): CrateFacts | null {
  if (!isRecord(entry)) return null;
  const name = readString(entry, 'name');
  const trusted = readObligations(readObject(entry, 'trusted'));
  return {
    name: name.recorded ? name.value : '',
    step: readString(entry, 'step'),
    scope: readString(entry, 'scope'),
    theorem: readString(entry, 'theorem'),
    verified: readNumber(entry, 'verified'),
    errors: readNumber(entry, 'errors'),
    noCheating: readBoolean(entry, 'no_cheating'),
    trusted,
    trustedTotal: sumObligations(trusted),
    vacuousRequires: readNumber(entry, 'vacuous_requires'),
    sourceLines: readNumber(entry, 'source_lines'),
    testsPassed: readNumber(entry, 'tests_passed'),
    testsFailed: readNumber(entry, 'tests_failed'),
    verifySeconds: readNumber(entry, 'verify_seconds'),
  };
}

function readJStep(entry: unknown): JStepFacts | null {
  if (!isRecord(entry)) return null;
  const step = readString(entry, 'step');
  return {
    step: step.recorded ? step.value : '',
    crate: readString(entry, 'crate'),
    status: readString(entry, 'status'),
    verified: readNumber(entry, 'verified'),
    errors: readNumber(entry, 'errors'),
    trusted: readNumber(entry, 'trusted'),
    testsPassed: readNumber(entry, 'tests_passed'),
    test262Passed: readNumber(entry, 'test262_passed'),
    test262Total: readNumber(entry, 'test262_total'),
  };
}

function readSuite(entry: unknown): SuiteFacts | null {
  if (!isRecord(entry)) return null;
  const suite = readString(entry, 'suite');
  return {
    suite: suite.recorded ? suite.value : '',
    crate: readString(entry, 'crate'),
    step: readString(entry, 'step'),
    passed: readNumber(entry, 'passed'),
    total: readNumber(entry, 'total'),
    differentialCases: readNumber(entry, 'differential_cases'),
  };
}

function readVmBenchmark(entry: unknown): VmBenchmarkFacts | null {
  if (!isRecord(entry)) return null;
  const name = readString(entry, 'name');
  return {
    name: name.recorded ? name.value : '',
    iterations: readNumber(entry, 'iterations'),
    astMs: readNumber(entry, 'ast_ms'),
    bytecodeMs: readNumber(entry, 'bytecode_ms'),
    speedup: readNumber(entry, 'speedup'),
    resultVerifiedEqual: readBoolean(entry, 'result_verified_equal'),
  };
}

function mapArray<T>(raw: unknown[] | null, reader: (entry: unknown) => T | null): T[] {
  if (!raw) return [];
  const out: T[] = [];
  for (const entry of raw) {
    const parsed = reader(entry);
    if (parsed) out.push(parsed);
  }
  return out;
}

/**
 * Reads the ratchet report.
 *
 * Every accessor points at one exact path in the document. A path that is not
 * there yields `recorded: false` — the caller renders `not recorded`.
 */
export function readRatchetFacts(document: unknown): RatchetFacts {
  const root = isRecord(document) ? document : null;
  const totals = readObject(root, 'totals');
  const obligations = readObligations(readObject(totals, 'trusted'));
  const modes = readObject(totals, 'functions_by_mode');
  const crates = readArray(root, 'crates');
  const jSteps = readArray(root, 'j_steps');
  const suites = readArray(root, 'test262_suites');
  const benchmarks = readArray(root, 'vm_benchmarks');
  const specPins = readArray(root, 'spec_pins');

  return {
    generatedAt: readString(root, 'generated_at'),
    generator: readString(root, 'generator'),
    verusVersion: readString(root, 'verus'),
    verusCommit: readString(root, 'verus_commit'),
    crateCount: readNumber(totals, 'crates'),
    verifiedQueries: readNumber(totals, 'verified'),
    errorCount: readNumber(totals, 'errors'),
    trustedItemCount: sumObligations(obligations),
    obligations,
    functionsByMode: {
      exec: readNumber(modes, 'exec'),
      proof: readNumber(modes, 'proof'),
      spec: readNumber(modes, 'spec'),
    },
    vacuousRequires: readNumber(totals, 'vacuous_requires'),
    sourceLines: readNumber(totals, 'source_lines'),
    testsPassed: readNumber(totals, 'tests_passed'),
    testsFailed: readNumber(totals, 'tests_failed'),
    verifySeconds: readNumber(totals, 'verify_seconds'),
    testSeconds: readNumber(totals, 'test_seconds'),
    crates:
      crates === null
        ? { recorded: false, value: null }
        : { recorded: true, value: mapArray(crates, readCrate) },
    jSteps:
      jSteps === null
        ? { recorded: false, value: null }
        : { recorded: true, value: mapArray(jSteps, readJStep) },
    test262Suites:
      suites === null
        ? { recorded: false, value: null }
        : { recorded: true, value: mapArray(suites, readSuite) },
    vmBenchmarks:
      benchmarks === null
        ? { recorded: false, value: null }
        : { recorded: true, value: mapArray(benchmarks, readVmBenchmark) },
    specPins:
      specPins === null
        ? { recorded: false, value: null }
        : {
            recorded: true,
            value: specPins.filter((pin): pin is string => typeof pin === 'string'),
          },
  };
}

/* ------------------------------------------------------------------ *
 * Stats facts
 * ------------------------------------------------------------------ */

/** Everything the gallery can say about the stats report. */
export interface StatsFacts {
  readonly generatedAt: Recorded<string>;
  readonly generator: Recorded<string>;
  readonly durationSeconds: Recorded<number>;
  readonly hostMachine: Recorded<string>;
  readonly hostSystem: Recorded<string>;
  readonly hostRelease: Recorded<string>;
  readonly toolchains: { readonly [K in ToolchainKey]: Recorded<string> };
  readonly vstdVerified: Recorded<number>;
  readonly vstdErrors: Recorded<number>;
  readonly vstdSeconds: Recorded<number>;
  readonly leanBenchmarkCount: Recorded<number>;
  readonly repoCount: Recorded<number>;
  readonly cliCount: Recorded<number>;
  /** The browser totals carried inside `stats.json`. */
  readonly browserCrateCount: Recorded<number>;
  readonly browserVerified: Recorded<number>;
  /**
   * `stats.json` records no trusted-item count of its own — the ratchet report
   * is the only source for that figure, so this reads `not recorded`.
   */
  readonly trustedItemCount: Recorded<number>;
}

/** The toolchains `stats.json` reports on. */
export const TOOLCHAIN_KEYS = ['z3', 'rustc', 'verus', 'lean', 'lake', 'uv'] as const;

export type ToolchainKey = (typeof TOOLCHAIN_KEYS)[number];

/**
 * Reads the stats report.
 *
 * `stats.json` has no top-level `trusted` field: the trusted-item count lives
 * in `ratchet.json` (and in `stats.json`'s embedded `browser` copy). The
 * accessor below therefore reports `not recorded` rather than borrowing the
 * ratchet's number.
 */
export function readStatsFacts(document: unknown): StatsFacts {
  const root = isRecord(document) ? document : null;
  const host = readObject(root, 'host');
  const toolchains = readObject(root, 'toolchains');
  const vstd = readObject(readObject(root, 'verus'), 'vstd');
  const leanBenchmarks = readArray(readObject(root, 'lean'), 'benchmarks');
  const repos = readArray(root, 'repos');
  const cli = readArray(root, 'cli');
  const browserTotals = readObject(readObject(root, 'browser'), 'totals');

  const toolchainFacts: { -readonly [K in ToolchainKey]: Recorded<string> } = {
    z3: readString(toolchains, 'z3'),
    rustc: readString(toolchains, 'rustc'),
    verus: readString(toolchains, 'verus'),
    lean: readString(toolchains, 'lean'),
    lake: readString(toolchains, 'lake'),
    uv: readString(toolchains, 'uv'),
  };

  return {
    generatedAt: readString(root, 'generated_at'),
    generator: readString(root, 'generator'),
    durationSeconds: readNumber(root, 'duration_seconds'),
    hostMachine: readString(host, 'machine'),
    hostSystem: readString(host, 'system'),
    hostRelease: readString(host, 'release'),
    toolchains: toolchainFacts,
    vstdVerified: readNumber(vstd, 'verified'),
    vstdErrors: readNumber(vstd, 'errors'),
    vstdSeconds: readNumber(vstd, 'seconds'),
    leanBenchmarkCount:
      leanBenchmarks === null ? { recorded: false, value: null } : { recorded: true, value: leanBenchmarks.length },
    repoCount: repos === null ? { recorded: false, value: null } : { recorded: true, value: repos.length },
    cliCount: cli === null ? { recorded: false, value: null } : { recorded: true, value: cli.length },
    browserCrateCount: readNumber(browserTotals, 'crates'),
    browserVerified: readNumber(browserTotals, 'verified'),
    trustedItemCount: readNumber(root, 'trusted'),
  };
}

/* ------------------------------------------------------------------ *
 * The bundled reports
 * ------------------------------------------------------------------ */

/** `browser/ratchet.json`, imported at build time. */
export const RATCHET: RatchetFacts = readRatchetFacts(ratchetDocument);

/** `data/stats.json`, imported at build time. */
export const STATS: StatsFacts = readStatsFacts(statsDocument);

/* ------------------------------------------------------------------ *
 * Rendering helpers
 * ------------------------------------------------------------------ */

/**
 * Renders a recorded value, or `not recorded` when the field was absent.
 *
 * `format` is only ever called for a recorded value, so a formatter can never
 * be handed a placeholder.
 */
export function formatRecorded<T>(entry: Recorded<T>, format?: (value: T) => string): string {
  if (!entry.recorded) return NOT_RECORDED;
  return format ? format(entry.value) : String(entry.value);
}

/** True when the field was present in the source report. */
export function isRecorded<T>(entry: Recorded<T>): boolean {
  return entry.recorded;
}
