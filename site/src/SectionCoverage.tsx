import React, { useMemo, useState } from 'react';
import { blobUrl } from './data';
import {
  CVES,
  COVERAGE_DETAIL,
  COVERAGE_LABEL,
  COVERAGE_SHORT,
  coverageTone,
  type Coverage,
} from './content/cves';
import { IconChevron } from './icons';
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

  const filterButtons: Array<{ id: FilterMode; label: string; count: string }> = [
    { id: 'all', label: 'All CVEs', count: `${CVES.length}` },
    { id: 'construction', label: 'Eliminated in vjs', count: `${tally.construction}/${CVES.length}` },
    { id: 'containment', label: 'Trapped by kernel', count: `${tally.containment}/${CVES.length}` },
    { id: 'graphics', label: 'Unverified GPU', count: `${tally.graphics}/${CVES.length}` },
  ];

  return (
    <section className="ch-appendix-section" id="coverage">
      <details className="ch-drawer" data-testid="cve-drawer">
        <summary className="ch-drawer-summary">
          <span className="ch-drawer-title">
            Empirical baseline: {CVES.length} exploited Chrome zero-days
          </span>
          <span className="ch-drawer-meta">
            {tally.v8}/{CVES.length} in V8 · CISA KEV &amp; Chrome Releases
          </span>
          <IconChevron size={15} className="ch-drawer-chev" />
        </summary>

        <div className="ch-drawer-body">
          <div className="ch-cve-toolbar">
            <div className="ch-filter-bar" role="group" aria-label="Filter CVEs by disposition">
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

            <span className="ch-prose-note">
              <span data-testid="packet-count">{visibleRows.length} CVEs</span> · Primary sources in{' '}
              <Source href={blobUrl('docs/vjs-plan-review.md')}>docs/vjs-plan-review.md §2</Source>
            </span>
          </div>

          <div className="ch-cve-split">
            <div className="ch-table-card">
              <table className="ch-table ch-table-compact ch-table-interactive" data-testid="cve-table">
                <thead>
                  <tr>
                    <th>CVE</th>
                    <th>Patched</th>
                    <th>Component</th>
                    <th>Flaw</th>
                    <th>Disposition</th>
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
                        <td className="ch-nowrap">
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

            <div className="ch-detail-card" data-testid="cve-detail">
              <div className="ch-detail-head">
                <span className="ch-detail-id">{active.cve}</span>
                <span className="ch-tone-label ch-mono-sm" data-tone={coverageTone(active.coverage)}>
                  {COVERAGE_SHORT[active.coverage]}
                </span>
              </div>
              <dl className="ch-fields">
                <Field label="Component & flaw">
                  {active.component} — {active.klass}
                </Field>
                <Field label="Patched in Chrome">
                  {active.patched} · release <code>{active.fixedIn}</code> ({active.kev})
                </Field>
                <Field label="Reported by">{active.reporter}</Field>
                <Field label="CONDUIT disposition">{COVERAGE_DETAIL[active.coverage]}</Field>
              </dl>
            </div>
          </div>
        </div>
      </details>
    </section>
  );
};

export default SectionCoverage;
