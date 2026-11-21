import React, { useMemo, useState } from 'react';
import { Badge } from '@clickhouse/click-ui';
import { blobUrl } from './data';
import {
  CVES,
  COVERAGE_DETAIL,
  COVERAGE_LABEL,
  COVERAGE_SHORT,
  coverageTone,
  type Coverage,
} from './content/cves';
import { Field, Source } from './parts';

type FilterMode = 'all' | Coverage;

const SectionCoverage: React.FC = () => {
  const [filter, setFilter] = useState<FilterMode>('all');
  const [selectedCve, setSelectedCve] = useState<string>(CVES[0].cve);

  const tally = useMemo(
    () => ({
      construction: CVES.filter((c) => c.coverage === 'construction').length,
      containment: CVES.filter((c) => c.coverage === 'containment').length,
      graphics: CVES.filter((c) => c.coverage === 'graphics').length,
      v8: CVES.filter((c) => c.component.startsWith('V8')).length,
    }),
    [],
  );

  const visibleRows = useMemo(
    () => (filter === 'all' ? CVES : CVES.filter((c) => c.coverage === filter)),
    [filter],
  );

  const active =
    visibleRows.find((c) => c.cve === selectedCve) ?? visibleRows[0] ?? CVES[0];

  const filterButtons: Array<{ id: FilterMode; label: string; count: number }> = [
    { id: 'all', label: 'All CVEs', count: CVES.length },
    { id: 'construction', label: 'By construction', count: tally.construction },
    { id: 'containment', label: 'Containment', count: tally.containment },
    { id: 'graphics', label: 'Graphics gap', count: tally.graphics },
  ];

  return (
    <section className="ch-spec-row" id="coverage">
      <div className="ch-prose-col">
        <h2 className="ch-section-title">
          What attackers exploited in Chrome, and where this design answers it
        </h2>
        <p className="ch-prose-text" data-testid="coverage-tally">
          These are the last {CVES.length} Chrome vulnerabilities Google confirmed attackers
          exploited in the wild through 2026-11-20. V8 accounts for {tally.v8} of them.
        </p>

        <div className="ch-tally-list">
          <div className="ch-tally-item" data-tone="proved">
            <div className="ch-tally-ratio">
              {tally.construction}/{CVES.length}
            </div>
            <div className="ch-tally-copy">
              <strong>Eliminated by construction (vjs)</strong> — No optimizing JIT in the trusted
              base, a safe-Rust indexed arena heap, and proved §6.1.7.3 object invariants target V8
              type confusion and OOB bugs directly. J0–J7 crates are verified; browser kernel wiring
              is next.
            </div>
          </div>

          <div className="ch-tally-item" data-tone="warn">
            <div className="ch-tally-ratio">
              {tally.containment}/{CVES.length}
            </div>
            <div className="ch-tally-copy">
              <strong>Contained by kernel boundary</strong> — Blink XML/CSS UAFs and Mojo handle
              escapes land behind typed Vest-encoded IPC and per-site sandboxing once the kernel
              theorems land.
            </div>
          </div>

          <div className="ch-tally-item" data-tone="fail">
            <div className="ch-tally-ratio">
              {tally.graphics}/{CVES.length}
            </div>
            <div className="ch-tally-copy">
              <strong>Outside proof scope (GPU stack)</strong> — Dawn, Skia, and ANGLE carry no
              verified replacement. Graphics runs per-site inside the sandbox to limit blast radius
              rather than claiming a proof.
            </div>
          </div>
        </div>

        <div className="ch-detail-card" data-testid="cve-detail">
          <div className="ch-detail-head">
            <span className="ch-detail-id">{active.cve}</span>
            <Badge
              state={
                active.coverage === 'construction'
                  ? 'success'
                  : active.coverage === 'containment'
                  ? 'warning'
                  : 'danger'
              }
              text={COVERAGE_SHORT[active.coverage]}
            />
          </div>
          <dl className="ch-fields">
            <Field label="Component & bug class">
              {active.component} — {active.klass}
            </Field>
            <Field label="Patched in Chrome">
              {active.patched} · release <code>{active.fixedIn}</code> ({active.kev})
            </Field>
            <Field label="Reporter / campaign">{active.reporter}</Field>
            <Field label="This engine's answer">{COVERAGE_DETAIL[active.coverage]}</Field>
          </dl>
        </div>

        <p className="ch-prose-note">
          Every row was verified against Google Chrome Releases ITW notices and CISA KEV in{' '}
          <Source href={blobUrl('docs/vjs-plan-review.md')}>docs/vjs-plan-review.md §2</Source>.
        </p>
      </div>

      <div className="ch-artifact-col">
        <div className="ch-filter-bar" role="group" aria-label="Filter CVEs by coverage">
          {filterButtons.map((btn) => (
            <button
              key={btn.id}
              type="button"
              className="ch-filter-btn"
              data-active={filter === btn.id}
              data-testid={`cve-filter-${btn.id}`}
              aria-pressed={filter === btn.id}
              onClick={() => {
                setFilter(btn.id);
                const nextRows =
                  btn.id === 'all' ? CVES : CVES.filter((c) => c.coverage === btn.id);
                if (nextRows.length && !nextRows.some((r) => r.cve === selectedCve)) {
                  setSelectedCve(nextRows[0].cve);
                }
              }}
            >
              <span>{btn.label}</span>
              <span className="ch-filter-count">{btn.count}</span>
            </button>
          ))}
        </div>

        <div className="ch-table-card">
          <div className="ch-table-meta">
            <span data-testid="packet-count">{visibleRows.length} CVEs</span>
            <span>Select any row to inspect release provenance and coverage rationale</span>
          </div>
          <table className="ch-table ch-table-interactive" data-testid="cve-table">
            <thead>
              <tr>
                <th>CVE</th>
                <th>Patched</th>
                <th>Component</th>
                <th>Bug class</th>
                <th>Architectural answer</th>
              </tr>
            </thead>
            <tbody>
              {visibleRows.map((row) => {
                const isSelected = row.cve === active.cve;
                const tone = coverageTone(row.coverage);
                return (
                  <tr
                    key={row.cve}
                    data-testid={`cve-row-${row.cve}`}
                    data-selected={isSelected}
                    tabIndex={0}
                    onClick={() => setSelectedCve(row.cve)}
                    onKeyDown={(ev) => {
                      if (ev.key === 'Enter' || ev.key === ' ') {
                        ev.preventDefault();
                        setSelectedCve(row.cve);
                      }
                    }}
                  >
                    <td className="ch-mono ch-nowrap">
                      <span className="ch-status-dot" data-tone={tone} aria-hidden="true" />
                      {row.cve}
                    </td>
                    <td className="ch-mono ch-nowrap">{row.patched}</td>
                    <td>{row.component}</td>
                    <td>{row.klass}</td>
                    <td>
                      <span className="ch-tone-label" data-tone={tone}>
                        {COVERAGE_LABEL[row.coverage]}
                      </span>
                    </td>
                  </tr>
                );
              })}
            </tbody>
          </table>
        </div>
      </div>
    </section>
  );
};

export default SectionCoverage;
