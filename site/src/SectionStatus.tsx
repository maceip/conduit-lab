import React from 'react';
import { IxProofDag } from '@maceip/ix-workbench-primitives';
import { NR, crateOk, trustedTotal, blobUrl, type Ratchet } from './data';
import { TRADEOFFS } from './content/tradeoffs';
import { VJS_STEPS, FUEL_THEOREM } from './content/vjs';
import { VURL_MODULES, VURL_DAG_NODES, VURL_DAG_EDGES } from './content/vurl';
import { DetailsRow, Field, Source } from './parts';

const SectionStatus: React.FC<{ ratchet: Ratchet | null }> = ({ ratchet }) => {
  const vurl = ratchet?.crates.find((c) => c.name === 'vurl');
  const ok = crateOk(vurl);
  const trusted = trustedTotal(vurl);

  return (
    <section className="wb-row12" id="status">
      <div className="wb-c7 wb-col">
        <div className="wb-chapter">05 · Status</div>
        <h2 className="wb-h2">What exists, and what is still design</h2>
        <div data-testid="modules">
          {VURL_MODULES.map((m, i) => (
            <DetailsRow key={m.id} k={`vurl · ${m.id}`} v={m.summary} tone={ok ? 'verified' : 'critical'} open={i === 0}>
              <Field label="Executable functions, proved equal to spec">
                <span className="wb-mono-list">{m.exec.join(' · ')}</span>
              </Field>
              <Field label="Theorems about the spec">
                <span className="wb-mono-list">{m.theorems.join(' · ')}</span>
              </Field>
              <Field label="Not covered">{m.gaps}</Field>
            </DetailsRow>
          ))}
        </div>
        <div className="wb-box">
          <div className="wb-box-t">What vjs must guarantee</div>
          <pre className="wb-code" data-testid="fuel-theorem">{FUEL_THEOREM}</pre>
        </div>
        <div data-testid="vjs-rows">
          {VJS_STEPS.map((s) => (
            <DetailsRow key={s.step} k={s.step} v={`${s.short} — design`}>
              <Field label="Scope">{s.scope}</Field>
              <Field label="Exit criterion (measured, not estimated)">{s.exit}</Field>
              <Field label="Status">
                Design. No implementation exists yet; the ratchet is the only progress number
                published.
              </Field>
            </DetailsRow>
          ))}
        </div>
        <div className="wb-dag-frame">
          {vurl ? (
            <IxProofDag
              nodes={VURL_DAG_NODES.map((n) => ({ ...n, state: ok ? 'verified' : 'invalidated' }))}
              edges={VURL_DAG_EDGES}
              width={700}
              nodeWidth={165}
            />
          ) : (
            <div className="wb-disclosure">
              <h3>Ratchet not loaded</h3>
              <p>The obligation graph is not drawn without real verification data.</p>
            </div>
          )}
        </div>
        <p className="wb-prose wb-note">
          Click a node to see which obligations depend on it. vurl does not yet cover validation
          errors, opaque and domain hosts, IDNA, or the main URL parser state machine. Sources:{' '}
          <Source href={blobUrl('docs/verified-browser-engine.md')}>design doc</Source> ·{' '}
          <Source href={blobUrl('browser/README.md')}>vurl README</Source> ·{' '}
          <Source href="browser/ratchet.json">raw ratchet</Source> ·{' '}
          <Source href={blobUrl('browser/url/tests/data/PROVENANCE')}>WPT provenance</Source>
        </p>
      </div>
      <div className="wb-c5 wb-col">
        <div className="wb-disclosure" data-testid="honesty-card">
          <h3>Only vurl is implemented</h3>
          <p>
            The JS engine (vjs), the kernel theorems and renderer isolation on Nanvix are
            design documents, not code. Until they exist, script would run in an untrusted engine
            inside a sandbox nobody has proved, which is where Chrome is today. The plan publishes
            no schedule. Progress is the ratchet report: proved functions, trusted items and test
            results from the last run.
          </p>
        </div>
        <div className="wb-box-t">Tradeoffs</div>
        <div data-testid="tradeoffs">
          {TRADEOFFS.map((t, i) => (
            <DetailsRow key={i} k={`${i + 1}`} v={t.decision} open={i === 0}>
              <Field label="Given up">{t.givenUp}</Field>
              <Field label="Gained">{t.gained}</Field>
              <Field label="Residual risk">{t.residual}</Field>
            </DetailsRow>
          ))}
        </div>
        <p className="wb-prose wb-note">
          Condensed from <Source href={blobUrl('docs/vjs-plan-review.md')}>docs/vjs-plan-review.md §1</Source>.
          {vurl ? ` Crate-wide: ${vurl.verified} verified functions, ${trusted} trusted items.` : ''}
        </p>
      </div>
    </section>
  );
};

export default SectionStatus;