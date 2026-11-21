import React from 'react';
import { IxBlind } from '@siemens/ix-react';
import { NR, type Ratchet } from './data';
import { SYSTEMS, SCALE_ITEMS } from './content/systems';
import { SectionHead, ScaleCompare, Source } from './parts';

const PaneWhyHard: React.FC<{ ratchet: Ratchet | null }> = ({ ratchet }) => {
  const vurl = ratchet?.crates.find((c) => c.name === 'vurl');
  const scaleItems = [
    ...SCALE_ITEMS,
    {
      id: 'vurl',
      label: 'vurl — this project, today',
      lines: vurl?.source_lines ?? 1,
      display: vurl ? `${vurl.source_lines.toLocaleString('en-US')} LOC` : NR,
      tone: 'neutral' as const,
      note: vurl
        ? `${vurl.verified} verified functions · ${vurl.verify_seconds}s to re-verify everything`
        : 'load browser/ratchet.json to see the live numbers',
    },
  ];

  return (
    <>
      <SectionHead index="02 · The hard part" title="We have verified kernels. Just not Linux.">
        In 2009, the seL4 project proved an entire operating-system kernel correct — functional
        correctness, down to the C code. It is real, it ships, and it is roughly{' '}
        <strong>4,000× smaller than Linux</strong>. The question is not whether verification
        works. It is why it does not scale to the software you actually run.
      </SectionHead>

      <ScaleCompare items={scaleItems} />

      <div>
        <IxBlind label="1 · Proof cost grows faster than code" variant="alarm" collapsed={false}>
          <div className="wb-blind-body">
            seL4 took <strong>≈20 person-years</strong> for 8,700 lines of C — the Isabelle proof
            is an order of magnitude larger than the code it covers. Extrapolating that ratio to
            ≈36M lines of Linux is absurd, and the ratio only gets worse: concurrency, driver
            state machines and hardware interaction are exactly the parts where proofs explode.
            Verification effort does not scale linearly with anything.
          </div>
        </IxBlind>
        <IxBlind label="2 · The spec moves under your feet" variant="warning" collapsed>
          <div className="wb-blind-body">
            A proof is a snapshot: it binds <em>this</em> code to <em>this</em> spec. Linux merges
            changes hourly and rewrites subsystems every release; a full-kernel proof would be
            obsolete before it finished. seL4 survives by keeping its API deliberately tiny and
            stable. Living standards (WHATWG, ECMA-262) have the same problem — this project's
            answer is pinned spec commits, spec text kept beside every spec function, and CI that
            re-verifies against upstream Verus weekly instead of forking it.
          </div>
        </IxBlind>
        <IxBlind label="3 · Most of the code is the wrong target" variant="warning" collapsed>
          <div className="wb-blind-body">
            Drivers are the majority of Linux's lines and of its bugs — and they talk to hardware
            whose behavior no one has fully formalized. Even seL4's theorem excludes boot code,
            assembly, and the hardware itself. Verifying a driver against an idealized device
            model proves something weaker than "this driver works on your machine". The honest
            move is to <strong>contain</strong> that code, not to pretend it is proved.
          </div>
        </IxBlind>
        <IxBlind label="4 · You don't need to verify everything" variant="success" collapsed>
          <div className="wb-blind-body">
            The systems that ship verified today picked small, stable, spec-able targets:
            crypto arithmetic (fiat-crypto in BoringSSL/Chrome, HACL* in Firefox), a compiler
            (CompCert), a microkernel (seL4), a certificate validator (Verdict). Quark showed the
            browser version of the trick in 2012: prove a small <strong>kernel</strong> — tab
            isolation, cookie integrity, address-bar truth — and run unmodified WebKit as
            untrusted, sandboxed tabs. Security comes from the boundary, not from verifying the
            renderer.
          </div>
        </IxBlind>
      </div>

      <div>
        <div className="wb-eyebrow" style={{ marginBottom: 8 }}>What verification has actually shipped</div>
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

      <div className="wb-callout" data-tone="verified">
        <strong>That is exactly this project's bet.</strong> Don't verify a browser — verify its
        security kernel, run the real (unverified) engine in per-site sandboxes behind it, and
        replace components one by one with verified ones. A ratchet that only moves forward.
        Pane <strong>03</strong> shows where that stands today, and what each decision cost.
      </div>
    </>
  );
};

export default PaneWhyHard;