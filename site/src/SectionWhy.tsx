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
    body: "Drivers are most of Linux's code and most of its bugs, and they talk to hardware nobody has formalized. Even seL4's theorem excludes boot code, assembly and the hardware itself. That code has to be isolated and labeled unproved.",
  },
  {
    k: '4',
    v: 'Verify the boundary, contain the rest',
    body: 'Shipped verification picks small, stable targets: crypto arithmetic, compilers, microkernels, certificate validation. Quark proved a browser kernel in Coq in 2012 and ran unmodified WebKit as untrusted sandboxed tabs behind it. Its theorems covered tab isolation, cookie integrity and the address bar, with no proof about WebKit at all.',
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
        <div className="wb-chapter">03 · Scope</div>
        <h2 className="wb-h2">Why nobody proves a whole browser, or a whole Linux</h2>
        <p className="wb-prose">
          seL4's proof of an operating-system kernel landed in 2009. Linux is about 4,000 times
          larger and has no such proof. A modern browser faces the same four obstacles, so this
          project does what every shipped verification effort did and picks the target small.
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
          This project follows Quark. It proves the security kernel, runs real unverified engines
          in per-site sandboxes behind it, and then replaces renderer components with verified
          ones, one at a time. Section 05 lists what exists and what is still design.
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