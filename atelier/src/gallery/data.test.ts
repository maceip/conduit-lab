import { describe, expect, it } from 'vitest';
import {
  NOT_RECORDED,
  OBLIGATION_KINDS,
  RATCHET,
  STATS,
  formatRecorded,
  readObligations,
  readRatchetFacts,
  readStatsFacts,
  sumObligations,
  type Recorded,
} from './data';

/**
 * The loader is wired to the real reports: `browser/ratchet.json` and
 * `data/stats.json`. As of the 2026-11-22 run the ratchet records 11 crates,
 * 4,102 verified queries and zero trusted items; `stats.json` records 2,354
 * verified vstd queries and carries no trusted-item count of its own.
 *
 * These assertions are deliberately written as invariants rather than
 * snapshots, so a regenerated report does not break the suite — but the
 * "trusted items are recorded and are zero" check is exact on purpose: a
 * ratchet regression must fail loudly rather than be smoothed over.
 */
describe('ratchet facts — the present-field path', () => {
  it('records the trusted-item count, and a recorded zero is not "not recorded"', () => {
    expect(RATCHET.trustedItemCount.recorded).toBe(true);
    expect(RATCHET.trustedItemCount.value).toBe(0);
  });

  it('totals the trusted-item count from the obligation markers', () => {
    const expected = OBLIGATION_KINDS.reduce((total, kind) => {
      const entry = RATCHET.obligations[kind];
      return entry.recorded ? total + entry.value : total;
    }, 0);
    expect(RATCHET.trustedItemCount.value).toBe(expected);
  });

  it('records every obligation marker individually', () => {
    for (const kind of OBLIGATION_KINDS) {
      const entry = RATCHET.obligations[kind];
      expect(entry.recorded, `${kind} should be recorded`).toBe(true);
    }
    expect(RATCHET.obligations.unsafe.value).toBe(0);
    expect(RATCHET.obligations.assume.value).toBe(0);
  });

  it('agrees with the crate list it was derived from', () => {
    expect(RATCHET.crateCount.recorded).toBe(true);
    expect(RATCHET.crates.recorded).toBe(true);
    if (!RATCHET.crates.recorded) throw new Error('crates should be recorded');
    expect(RATCHET.crateCount.value).toBe(RATCHET.crates.value.length);
  });

  it('totals the verified queries across every crate', () => {
    if (!RATCHET.crates.recorded) throw new Error('crates should be recorded');
    const summed = RATCHET.crates.value.reduce((total, crate) => {
      return crate.verified.recorded ? total + crate.verified.value : total;
    }, 0);
    expect(RATCHET.verifiedQueries.recorded).toBe(true);
    expect(RATCHET.verifiedQueries.value).toBe(summed);
  });

  it('records the run metadata', () => {
    expect(RATCHET.generatedAt.recorded).toBe(true);
    expect(RATCHET.generator.recorded).toBe(true);
    expect(RATCHET.verusVersion.recorded).toBe(true);
    expect(RATCHET.functionsByMode.exec.recorded).toBe(true);
  });
});

describe('ratchet facts — the absent-field path', () => {
  it('reports every field as not recorded for an empty document', () => {
    const facts = readRatchetFacts({});
    expect(facts.trustedItemCount.recorded).toBe(false);
    expect(facts.trustedItemCount.value).toBeNull();
    expect(facts.crateCount.recorded).toBe(false);
    expect(facts.verifiedQueries.recorded).toBe(false);
    expect(facts.crates.recorded).toBe(false);
    expect(facts.jSteps.recorded).toBe(false);
    expect(facts.generatedAt.recorded).toBe(false);
  });

  it('never turns a missing total into a zero', () => {
    const facts = readRatchetFacts({});
    expect(facts.trustedItemCount).not.toEqual({ recorded: true, value: 0 });
    expect(facts.errorCount.value).toBeNull();
    expect(facts.testsFailed.value).toBeNull();
  });

  it('never turns an empty marker record into a zero', () => {
    const facts = readRatchetFacts({ totals: { trusted: {} } });
    expect(facts.trustedItemCount.recorded).toBe(false);
    expect(sumObligations(facts.obligations).recorded).toBe(false);
  });

  it('never turns a missing marker record into a zero', () => {
    const facts = readRatchetFacts({ totals: { trusted: { assume: 0, admit: 0 } } });
    expect(facts.trustedItemCount.recorded).toBe(true);
    expect(facts.trustedItemCount.value).toBe(0);
    expect(facts.obligations.axiom.recorded).toBe(false);
    expect(facts.obligations.axiom.value).toBeNull();
  });

  it('sums nothing when no marker was measured', () => {
    const obligations = readObligations(null);
    const total = sumObligations(obligations);
    expect(total.recorded).toBe(false);
    expect(total.value).toBeNull();
  });

  it('renders a missing field as "not recorded"', () => {
    const missing: Recorded<number> = { recorded: false, value: null };
    expect(formatRecorded(missing)).toBe(NOT_RECORDED);
    expect(formatRecorded(missing, (value) => String(value))).toBe(NOT_RECORDED);
  });

  it('renders a recorded zero as a number', () => {
    expect(formatRecorded({ recorded: true, value: 0 })).toBe('0');
  });
});

describe('stats facts', () => {
  it('records the stats report fields', () => {
    expect(STATS.generatedAt.recorded).toBe(true);
    expect(STATS.durationSeconds.recorded).toBe(true);
    expect(STATS.vstdVerified.recorded).toBe(true);
    expect(STATS.hostSystem.recorded).toBe(true);
    expect(STATS.toolchains.z3.recorded).toBe(true);
  });

  it('agrees with the ratchet report it embeds', () => {
    expect(STATS.browserCrateCount.value).toBe(RATCHET.crateCount.value);
    expect(STATS.browserVerified.value).toBe(RATCHET.verifiedQueries.value);
  });

  it('reports the trusted-item count as not recorded — stats.json has no such field', () => {
    expect(STATS.trustedItemCount.recorded).toBe(false);
    expect(STATS.trustedItemCount.value).toBeNull();
  });

  it('reports every field as not recorded for an empty document', () => {
    const facts = readStatsFacts({});
    expect(facts.vstdVerified.recorded).toBe(false);
    expect(facts.repoCount.recorded).toBe(false);
    expect(facts.trustedItemCount.recorded).toBe(false);
  });
});
