import React from 'react';
import { NR, ratchetTotals, type Ratchet } from './data';
import { SCALE_ITEMS, SYSTEMS } from './content/systems';
import { ScaleCompare, Source } from './parts';

const SectionWhy: React.FC<{ ratchet: Ratchet | null }> = ({ ratchet }) => {
  const totals = ratchetTotals(ratchet);
  const scaleItems = [
    ...SCALE_ITEMS,
    {
      id: 'conduit',
      label: 'CONDUIT — verified browser crates',
      lines: totals?.source_lines ?? 1,
      display: totals ? `${totals.source_lines.toLocaleString('en-US')} LOC` : NR,
      tone: 'proved' as const,
      note: '',
    },
  ];

  return (
    <section className="ch-spec-row" id="scope">
      <div className="ch-prose-col">
        <h2 className="ch-section-title">
          Scale &amp; Limits of Formal Verification
        </h2>

        <p className="ch-prose-text">
          seL4 took roughly twenty person-years to prove 8,700 lines of C, while Chromium and Linux
          sit near 36 million lines over unformalized GPU silicon. Comparing CONDUIT against prior
          verified systems shows what machine-checked proofs can cover—and what must remain isolated
          at runtime.
        </p>

        <ScaleCompare items={scaleItems} />
      </div>

      <div className="ch-artifact-col">
        <div className="ch-table-card">
          <table className="ch-table ch-table-compact" data-testid="systems-table">
            <thead>
              <tr>
                <th>System</th>
                <th>Proved target</th>
                <th>Scale</th>
                <th>Takeaway</th>
              </tr>
            </thead>
            <tbody>
              {SYSTEMS.map((s) => (
                <tr key={s.name}>
                  <td className="ch-mono ch-nowrap">
                    <Source href={s.href}>{s.name}</Source>
                  </td>
                  <td>{s.proved}</td>
                  <td className="ch-mono-sm">{s.scale}</td>
                  <td>{s.role}</td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
      </div>
    </section>
  );
};

export default SectionWhy;
