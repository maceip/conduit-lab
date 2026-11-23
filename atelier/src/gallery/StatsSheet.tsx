import type { ReactElement } from 'react';
import type { Tone } from '../contract';
import {
  CountFigure,
  DeltaChip,
  OdometerReels,
  RadialGauge,
  RatchetCounter,
  SplitBar,
  StatTile,
  type SplitBarSegment,
} from '../viz/stats';
import { NOT_RECORDED, RATCHET, STATS, formatRecorded, type Recorded } from './data';

/** Groups thousands the way the reports are read. */
const group = (value: number): string => value.toLocaleString('en-US');

/**
 * A large figure, or `not recorded` when the report does not carry it.
 *
 * The animated components take a `number`, so they can only ever be given a
 * value that was really recorded. A missing field falls back to a tile that
 * says so — never to a zero.
 */
function Figure({
  entry,
  label,
  suffix,
}: {
  entry: Recorded<number>;
  label: string;
  suffix?: string;
}): ReactElement {
  if (!entry.recorded) {
    return <StatTile value={NOT_RECORDED} label={label} tone="neutral" />;
  }
  return <CountFigure value={entry.value} label={label} suffix={suffix} />;
}

/** A labelled figure that is already a string. */
function Tile({
  value,
  label,
  hint,
  tone = 'neutral',
}: {
  value: string;
  label: string;
  hint?: string;
  tone?: Tone;
}): ReactElement {
  return <StatTile value={value} label={label} hint={hint} tone={tone} />;
}

/** The test262 conformance measured across every suite the ratchet ran. */
function conformance(): { passed: number; total: number } | null {
  const suites = RATCHET.test262Suites;
  if (!suites.recorded) return null;
  let passed = 0;
  let total = 0;
  for (const suite of suites.value) {
    if (suite.passed.recorded) passed += suite.passed.value;
    if (suite.total.recorded) total += suite.total.value;
  }
  return total > 0 ? { passed, total } : null;
}

/** The differential cases the suites exercised. */
function differentialCases(): number | null {
  const suites = RATCHET.test262Suites;
  if (!suites.recorded) return null;
  let total = 0;
  let seen = 0;
  for (const suite of suites.value) {
    if (suite.differentialCases.recorded) {
      total += suite.differentialCases.value;
      seen += 1;
    }
  }
  return seen > 0 ? total : null;
}

/** The Z3 version, pulled out of the toolchain string the way the site reads it. */
function z3Version(): string {
  const z3 = STATS.toolchains.z3;
  if (!z3.recorded) return NOT_RECORDED;
  return z3.value.match(/version ([\d.]+)/)?.[1] ?? z3.value;
}

/**
 * The statistics sheet.
 *
 * Every figure here is read from `browser/ratchet.json` or `data/stats.json`
 * through the gallery's own loader. A field the reports do not carry renders
 * `not recorded` — there is no mock data on this sheet and no invented
 * number.
 */
export function StatsSheet(): ReactElement {
  const trusted = RATCHET.trustedItemCount;
  const conformanceFigures = conformance();
  const differential = differentialCases();
  const speedup = RATCHET.vmBenchmarksGeomeanSpeedup;

  const modeSegments: SplitBarSegment[] = [];
  if (RATCHET.functionsByMode.exec.recorded) {
    modeSegments.push({
      id: 'exec',
      label: 'exec — executable code',
      value: RATCHET.functionsByMode.exec.value,
      tone: 'neutral',
    });
  }
  if (RATCHET.functionsByMode.proof.recorded) {
    modeSegments.push({
      id: 'proof',
      label: 'proof — proof obligations',
      value: RATCHET.functionsByMode.proof.value,
      tone: 'proved',
    });
  }
  if (RATCHET.functionsByMode.spec.recorded) {
    modeSegments.push({
      id: 'spec',
      label: 'spec — specification steps',
      value: RATCHET.functionsByMode.spec.value,
      tone: 'warn',
    });
  }

  const modeRecorded = modeSegments.length > 0;

  const crates = RATCHET.crates;

  return (
    <section className="atelier__sheet" data-testid="stats-sheet">
      <div className="atelier__sheet-header">
        <h2 className="atelier__label">Stats — the ratchet, read live</h2>
        <p className="atelier__meta">
          browser/ratchet.json · data/stats.json · generated{' '}
          {formatRecorded(RATCHET.generatedAt)}
        </p>
      </div>

      {/* The signature piece: the trusted-item ratchet. */}
      <div className="atelier__hero">
        {trusted.recorded ? (
          <div className="atelier__card atelier__card--raised">
            <RatchetCounter trusted={trusted.value} testId="ratchet-counter" />
            <p className="atelier__note">
              The counter can only ever roll downwards. Neither report carries a prior-release
              figure, so no movement is claimed — the count holds.
            </p>
          </div>
        ) : (
          <Tile value={NOT_RECORDED} label="trusted items" tone="neutral" />
        )}

        <div className="atelier__card atelier__card--raised">
          <Figure entry={RATCHET.verifiedQueries} label="verified queries" />
          <p className="atelier__note">
            {formatRecorded(RATCHET.crateCount)} crates · {formatRecorded(RATCHET.sourceLines, group)}{' '}
            source lines
          </p>
        </div>

        <div className="atelier__card atelier__card--raised">
          {RATCHET.sourceLines.recorded ? (
            <OdometerReels value={RATCHET.sourceLines.value} />
          ) : (
            <Tile value={NOT_RECORDED} label="source lines" />
          )}
          <p className="atelier__label">source lines</p>
        </div>
      </div>

      {/* The headline figures, straight from the reports. */}
      <div className="atelier__tiles">
        <Tile
          value={formatRecorded(RATCHET.crateCount)}
          label="crates"
          hint="totals.crates"
          tone="proved"
        />
        <Tile
          value={formatRecorded(RATCHET.verifiedQueries, group)}
          label="verified queries"
          hint="totals.verified"
          tone="proved"
        />
        <Tile
          value={formatRecorded(RATCHET.errorCount)}
          label="errors"
          hint="totals.errors"
          tone={RATCHET.errorCount.recorded && RATCHET.errorCount.value > 0 ? 'fail' : 'proved'}
        />
        <Tile
          value={formatRecorded(RATCHET.testsPassed)}
          label="tests passed"
          hint={`${formatRecorded(RATCHET.testsFailed)} failed`}
          tone="proved"
        />
        <Tile
          value={formatRecorded(RATCHET.trustedItemCount)}
          label="trusted items"
          hint="assume · admit · unsafe"
          tone={trusted.recorded ? (trusted.value === 0 ? 'proved' : 'fail') : 'neutral'}
        />
        <Tile
          value={formatRecorded(STATS.vstdVerified, group)}
          label="vstd queries"
          hint="stats.json verus.vstd"
          tone="proved"
        />
        <Tile
          value={formatRecorded(STATS.durationSeconds, (v) => `${v}s`)}
          label="stats run"
          hint="stats.json duration_seconds"
        />
        <Tile
          value={formatRecorded(STATS.hostSystem)}
          label="host"
          hint={formatRecorded(STATS.hostMachine)}
        />
        <Tile
          value={z3Version()}
          label="z3"
          hint="stats.json toolchains.z3"
        />
        <Tile
          value={formatRecorded(STATS.toolchains.verus)}
          label="verus"
          hint="stats.json toolchains.verus"
        />
        <Tile
          value={formatRecorded(STATS.trustedItemCount)}
          label="trusted items (stats)"
          hint="stats.json carries no such field"
        />
        <Tile
          value={differential === null ? NOT_RECORDED : group(differential)}
          label="differential cases"
          hint="test262 suites"
        />
      </div>

      <div className="atelier__split">
        <div className="atelier__card">
          <p className="atelier__label">functions by mode</p>
          {modeRecorded ? (
            <SplitBar segments={modeSegments} />
          ) : (
            <Tile value={NOT_RECORDED} label="functions by mode" />
          )}
        </div>

        <div className="atelier__card">
          <p className="atelier__label">test262 conformance</p>
          {conformanceFigures ? (
            <RadialGauge
              value={conformanceFigures.passed}
              max={conformanceFigures.total}
              label={`${group(conformanceFigures.passed)} / ${group(conformanceFigures.total)}`}
            />
          ) : (
            <Tile value={NOT_RECORDED} label="test262 conformance" />
          )}
        </div>

        <div className="atelier__card">
          <p className="atelier__label">bytecode vs ast</p>
          {speedup.recorded ? (
            <>
              <p className="atelier__value">{speedup.value.toFixed(2)}×</p>
              <p className="atelier__note">
                geometric mean across the VM benchmarks ·{' '}
                <DeltaChip delta={Math.round((speedup.value - 1) * 100)} unit="%" />
              </p>
            </>
          ) : (
            <Tile value={NOT_RECORDED} label="bytecode speedup" />
          )}
        </div>
      </div>

      {/* The ratchet's own crate list. */}
      {crates.recorded ? (
        <table className="atelier__table" data-testid="ratchet-crates">
          <thead>
            <tr>
              <th scope="col">step</th>
              <th scope="col">crate</th>
              <th scope="col">verified</th>
              <th scope="col">errors</th>
              <th scope="col">trusted</th>
              <th scope="col">tests</th>
            </tr>
          </thead>
          <tbody>
            {crates.value.map((crate) => (
              <tr key={crate.name} data-crate={crate.name}>
                <td data-numeric="muted">{formatRecorded(crate.step)}</td>
                <td>{crate.name}</td>
                <td>{formatRecorded(crate.verified, group)}</td>
                <td>{formatRecorded(crate.errors)}</td>
                <td>{formatRecorded(crate.trustedTotal)}</td>
                <td>{formatRecorded(crate.testsPassed)}</td>
              </tr>
            ))}
          </tbody>
        </table>
      ) : (
        <Tile value={NOT_RECORDED} label="crate list" />
      )}
    </section>
  );
}
