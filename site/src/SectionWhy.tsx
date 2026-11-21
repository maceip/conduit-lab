import React from 'react';
import { NR, type Ratchet } from './data';
import { SYSTEMS, SCALE_ITEMS } from './content/systems';
import { DetailsRow, Field, ScaleCompare, Source } from './parts';

const REASONS = [
  {
    k: '1',
    v: 'Proofs cost more than the code',
    body: 'seL4 took ≈20 person-years for 8,700 lines of C. The Isabelle proof is an order of magnitude larger than the code it covers, and the ratio worsens with concurrency and driver state machines. Extrapolating it to ≈36M lines of Linux is not a plan.',
  },
  {
    k: '2',
    v: 'The specification keeps changing',
    body: 'A proof binds one code version to one spec version. Linux merges changes hourly and rewrites subsystems every release; a full-kernel proof would be obsolete before it finished. seL4 survives by keeping its API tiny and stable. This project pins spec commits and re-verifies against upstream Verus weekly.',
  },
  {
    k: '3',
    v: 'Drivers and hardware are not provable',
    body: "Drivers are most of Linux's code and most of its bugs, and they talk to hardware nobody has formalized. Even seL4's theorem excludes boot code, assembly and the hardware itself. The honest move is to contain that code, not to call it proved.",
  },
  {
    k: '4',
    v: 'Verify the boundary, contain the rest',
    body: 'Shipped verification picks small, stable targets: crypto arithmetic, compilers, microkernels, certificate validation. Quark proved a browser kernel in 2012 and ran unmodified WebKit as untrusted sandboxed tabs behind it. Security comes from the boundary, not from verifying the renderer.',
  },
];

const SectionWhy: React.FC<{ ratchet: Ratchet | null }> = ({ ratchet }) => {
  const vurl = ratchet?.crates.find((c) => c.name === 'vurl');
  const scaleItems = [
    ...SCALE_ITEMS,
    {
      id: 'vurl',
      label: 'vurl — this project',
      lines: vurl?.source_lines ?? 1,
      display: vurl ? `${vurl.source_lines.toLocaleString('en-US')} LOC` : NR,
      tone: 'neutral' as const,
      note: vurl
        ? `${vurl.verified} verified functions · ${vurl.verify_seconds}s to re-verify`
        : 'load browser/ratchet.json for the live numbers',
    },
  ];

  return (
    <section className="wb-row12" id="why">
      <div className="wb-c5 wb-col">
        <div className="wb-chapter">02 · Why no verified Linux</div>
        <h2 className="wb-h2">Verified kernels exist. Linux is not one.</h2>
        <p className="wb-prose">
          seL4 proved a whole operating-system kernel correct in 2009. Linux is about{' '}
          <strong>4,000× larger</strong> and still unverified. Size is not the only reason.
        </p>
        <ScaleCompare items={scaleItems} />
        <div data-testid="reasons">
          {REASONS.map((r, i) => (
            <DetailsRow key={r.k} k={r.k} v={r.v} open={i === 0}>
              <Field label="Why it blocks a verified Linux">{r.body}</Field>
            </DetailsRow>
          ))}
        </div>
        <p className="wb-prose">
          This project uses the same approach as Quark: verify the security kernel, run the real
          unverified engine in per-site sandboxes behind it, and replace components one by one.
          Verified coverage only increases between releases. Section 03 shows the current state.
        </p>
        <p className="wb-prose wb-note">
          Sources: seL4 SOSP'09; Linux Foundation 2023 kernel report; browser/ratchet.json.
        </p>
      </div>
      <div className="wb-c7 wb-col">
        <div className="wb-box-t">What verification has actually shipped</div>
        <div className="wb-table-wrap">
          <table className="wb-table" data-testid="systems-table">
            <thead>
              <tr>
                <th>System</th>
                <th>What is proved</th>
                <th>Scale / effort</th>
                <th>Where it ships</th>
              </tr>
            </thead>
            <tbody>
              {SYSTEMS.map((s) => (
                <tr key={s.name}>
                  <td className="mono"><Source href={s.href}>{s.name}</Source></td>
                  <td>{s.proved}</td>
                  <td>{s.scale}</td>
                  <td>{s.ships}</td>
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