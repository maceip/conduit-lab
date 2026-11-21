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
  const v8 = CVES.filter((c) => c.component.startsWith('V8')).length;
  const c = sel === null ? null : CVES[sel];

  return (
    <section className="wb-row12" id="coverage">
      <div className="wb-c12 wb-col">
        <div className="wb-chapter">01 · The bugs</div>
        <h2 className="wb-h2">What attackers exploited in Chrome, and what this design does about each</h2>
        <p className="wb-prose" data-testid="coverage-tally">
          These are the last {CVES.length} Chrome CVEs that Google marked as exploited in the wild,
          as of 2026-11-20. V8 accounts for {v8} of them.{' '}
          <strong>{tally.construction}/{CVES.length}</strong> are bug classes the planned JS engine,
          vjs, is designed to rule out by construction: it has no JIT, its heap is safe Rust, and
          its object model carries proved invariants. vjs is not built yet, so for now those bugs
          would only be contained by a sandbox, the same position Chrome is in.{' '}
          <strong>{tally.containment}/{CVES.length}</strong> are in renderer code or IPC, where the
          answer is containment by the proved kernel once its theorems exist.{' '}
          <strong>{tally.graphics}/{CVES.length}</strong> are in the GPU stack (Dawn, Skia, ANGLE).
          Nothing in this plan proves those.
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
          The rail color is the answer: green for by construction, amber for containment, red for
          contained only. Click a row for the full explanation. Each row was checked against
          Google's release notes and CISA's exploited-vulnerabilities catalog in{' '}
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