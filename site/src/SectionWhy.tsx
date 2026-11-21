import React from 'react';
import { NR, ratchetTotals, type Ratchet } from './data';
import { SCALE_ITEMS, SYSTEMS } from './content/systems';
import { DetailsRow, Field, ScaleCompare, Source } from './parts';

const CONSTRAINTS = [
  {
    k: '01',
    v: 'Proofs grow faster than the code they certify',
    body: 'seL4 required roughly 20 person-years to verify 8,700 lines of C. The Isabelle proof is an order of magnitude larger than the kernel itself, and complexity compounds with concurrency and mutable state machines. Scaling that directly to ~36 million lines of Linux or Chromium is not a viable plan.',
  },
  {
    k: '02',
    v: 'Moving specifications break proofs continuously',
    body: 'A formal theorem binds one exact code snapshot to one exact specification. General-purpose kernels and browsers merge thousands of changes monthly. seL4 stays verifiable by keeping its API tiny and fixed; CONDUIT pins standard commits and tracks upstream Verus weekly.',
  },
  {
    k: '03',
    v: 'Hardware and device drivers resist formalization',
    body: 'Drivers account for the majority of Linux source lines and vulnerabilities, yet talk to undocumented silicon nobody has formalized. Even seL4 excludes boot assembly and hardware semantics from its theorem. Unformalized code must be isolated and labeled untrusted.',
  },
  {
    k: '04',
    v: 'Prove the security boundary, isolate everything else',
    body: 'Every shipped formal-verification success targets compact, high-leverage surfaces: cryptographic arithmetic, compilers, microkernels, and certificate policy. Quark proved a Coq browser kernel in 2012 while running unmodified WebKit in sandboxed tabs. CONDUIT extends that boundary inward one crate at a time.',
  },
];

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
      note: totals
        ? `${totals.verified.toLocaleString('en-US')} verified functions across ${totals.crates} crates · ${totals.verify_seconds}s full re-verify`
        : 'Load browser/ratchet.json for live workspace scale',
    },
  ];

  return (
    <section className="ch-spec-row" id="scope">
      <div className="ch-prose-col">
        <div className="ch-section-lead">
          <img
            src="assets/flair-synthesis.webp"
            alt="Neuro-symbolic specification synthesis orbital core"
            className="ch-flair-medallion"
            width={76}
            height={76}
          />
          <h2 className="ch-section-title">
            Why verification targets boundaries instead of 36 million lines
          </h2>
        </div>

        <p className="ch-prose-text">
          seL4 proved an operating-system microkernel correct in 2009. Modern Linux is four thousand
          times larger and still carries no end-to-end proof. A full web browser hits the same four
          constraints, so CONDUIT follows the proven strategy: verify the security kernel and
          highest-risk engines, sandbox the rest, and never let the trusted base grow.
        </p>

        <ScaleCompare items={scaleItems} />

        <div className="ch-accordion-group" data-testid="reasons">
          {CONSTRAINTS.map((c, idx) => (
            <DetailsRow key={c.k} k={c.k} v={c.v} open={idx === 0}>
              <Field label="Engineering constraint">{c.body}</Field>
            </DetailsRow>
          ))}
        </div>

        <p className="ch-prose-note">
          Sources: seL4 SOSP &apos;09 · Linux Foundation 2023 Kernel Report · live{' '}
          <code>browser/ratchet.json</code>.
        </p>
      </div>

      <div className="ch-artifact-col">
        <div className="ch-table-card">
          <div className="ch-table-meta">
            <span>Prior art · What formal verification has shipped</span>
            <span>9 landmark systems</span>
          </div>
          <table className="ch-table" data-testid="systems-table">
            <thead>
              <tr>
                <th>System</th>
                <th>What was proved</th>
                <th>Scale / effort</th>
                <th>Role in CONDUIT</th>
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
