import React from 'react';
import { NR, ratchetTotals, type Ratchet } from './data';
import { SCALE_ITEMS, SYSTEMS } from './content/systems';
import { DetailsRow, Field, ScaleCompare, Source } from './parts';

const CONSTRAINTS = [
  {
    k: '01',
    v: 'Proofs outsize the code they verify',
    body: 'seL4 took roughly twenty person-years to verify 8,700 lines of C. The Isabelle proof is an order of magnitude larger than the kernel itself, and the effort climbs steeply with concurrency and mutable state. Applying that brute-force to 36 million lines of Linux or Chromium is not realistic.',
  },
  {
    k: '02',
    v: 'Fast-moving specs break proofs continuously',
    body: 'Every proof ties one code snapshot to one exact specification. General-purpose kernels and browsers merge thousands of commits a month. seL4 stays verifiable because its API barely moves; CONDUIT pins upstream standard commits and re-verifies against upstream Verus every week.',
  },
  {
    k: '03',
    v: 'Hardware and drivers have no formal model',
    body: 'Device drivers make up most of Linux—and most of its bugs—yet talk to undocumented silicon nobody has formalized. Even seL4 leaves boot assembly and hardware semantics outside its proof. Unformalized code has to be isolated and labeled untrusted.',
  },
  {
    k: '04',
    v: 'Prove the boundary, then shrink the sandbox',
    body: 'Every shipped verification win picked a small, high-leverage target: crypto math, compilers, microkernels, certificate validation. Quark proved a Coq browser kernel in 2012 while running unmodified WebKit in sandboxed tabs. CONDUIT follows that playbook and pushes verified Rust inward one crate at a time.',
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
            src="assets/sticker-knot.webp"
            alt="CONDUIT interlocked circuit boundary emblem"
            className="ch-sticker-medallion"
            width={72}
            height={72}
          />
          <h2 className="ch-section-title">
            Why nobody verifies all of Linux—or all of Chrome
          </h2>
        </div>

        <p className="ch-prose-text">
          seL4 proved an entire microkernel correct in 2009—all 8,700 lines of C took roughly
          twenty person-years. Linux is four thousand times larger, and modern browsers sit on the
          same scale. Real-world verification never proves everything at once: it proves the
          security kernel and highest-risk engines, sandboxes the rest, and expands coverage
          release by release.
        </p>

        <ScaleCompare items={scaleItems} />

        <div className="ch-accordion-group" data-testid="reasons">
          {CONSTRAINTS.map((c, idx) => (
            <DetailsRow key={c.k} k={c.k} v={c.v} open={idx === 0}>
              <Field label="Why it matters">{c.body}</Field>
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
            <span>What formal verification has actually shipped</span>
            <span>9 landmark systems</span>
          </div>
          <table className="ch-table" data-testid="systems-table">
            <thead>
              <tr>
                <th>System</th>
                <th>What it proved</th>
                <th>Scale &amp; effort</th>
                <th>Lesson for CONDUIT</th>
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
