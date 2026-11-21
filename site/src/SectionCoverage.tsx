import React, { useState } from 'react';
import { IxPacketGrid, type PacketGridColumn } from '@maceip/ix-workbench-primitives';
import { blobUrl } from './data';
import { CVES, COVERAGE_LABEL, COVERAGE_DETAIL, coverageTone, type Coverage } from './content/cves';
import { Field, Source } from './parts';

const CVE_COLUMNS: PacketGridColumn[] = [
  { key: 'cve', label: 'CVE', mono: true, width: 1.3 },
  { key: 'patched', label: 'Patched', mono: true, width: 0.9 },
  { key: 'component', label: 'Component', width: 1 },
  { key: 'klass', label: 'Bug class', width: 1.3 },
  { key: 'coverageLabel', label: "This engine's answer", width: 1.5 },
];

const CVE_ROWS = CVES.map((c) => ({ ...c, coverageLabel: COVERAGE_LABEL[c.coverage] }));

const SectionCoverage: React.FC = () => {
  const [sel, setSel] = useState<number | null>(null);
  const tally = {
    construction: CVES.filter((c) => c.coverage === 'construction').length,
    containment: CVES.filter((c) => c.coverage === 'containment').length,
    graphics: CVES.filter((c) => c.coverage === 'graphics').length,
  };
  const c = sel === null ? null : CVES[sel];

  return (
    <section className="wb-row12" id="coverage">
      <div className="wb-c12 wb-col">
        <div className="wb-chapter">03 · Coverage</div>
        <h2 className="wb-h2">The bugs that actually get exploited, mapped to this engine</h2>
        <p className="wb-prose" data-testid="coverage-tally">
          Last 20 Chrome CVEs confirmed exploited in the wild (as of 2026-11-20).{' '}
          <strong>{tally.construction}/20</strong> answered by construction once vjs exists ·{' '}
          <strong>{tally.containment}/20</strong> by containment, if the kernel theorems land ·{' '}
          <strong>{tally.graphics}/20</strong> graphics (Dawn, Skia, ANGLE), contained only. V8 is
          13 of 20.
        </p>
        <div className="wb-grid-frame">
          <IxPacketGrid
            columns={CVE_COLUMNS}
            rows={CVE_ROWS}
            unitLabel="CVEs"
            emptyLabel="No CVEs loaded"
            getRowTone={(row) => coverageTone(row.coverage as Coverage)}
            selectedRowIndex={sel}
            onSelectRow={(_, i) => setSel(i)}
          />
        </div>
        <p className="wb-prose wb-note">
          Rail: green = by construction, amber = containment, red = contained only. Click a row
          for the full explanation. Every row was verified against primary sources in{' '}
          <Source href={blobUrl('docs/vjs-plan-review.md')}>docs/vjs-plan-review.md §2</Source>.
        </p>
        {c && (
          <div className="wb-box wb-cve-detail" data-testid="cve-detail">
            <div className="wb-box-t">
              {c.cve} · {COVERAGE_LABEL[c.coverage]}
            </div>
            <dl className="wb-fields">
              <Field label="Component">{c.component}</Field>
              <Field label="Bug class">{c.klass}</Field>
              <Field label="Patched">{c.patched}</Field>
              <Field label="This engine's answer">{COVERAGE_DETAIL[c.coverage]}</Field>
            </dl>
          </div>
        )}
      </div>
    </section>
  );
};

export default SectionCoverage;