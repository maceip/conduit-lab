import React from 'react';
import { IxProofDag } from '@maceip/ix-workbench-primitives';
import {
  NR,
  allCratesOk,
  crateOk,
  ratchetTotals,
  sumTrusted,
  trustedTotal,
  blobUrl,
  type Ratchet,
} from './data';
import { TRADEOFFS } from './content/tradeoffs';
import { VJS_STEPS, FUEL_THEOREM } from './content/vjs';
import { VURL_MODULES, VURL_DAG_NODES, VURL_DAG_EDGES } from './content/vurl';
import { DetailsRow, Field, Source } from './parts';

const SectionStatus: React.FC<{ ratchet: Ratchet | null }> = ({ ratchet }) => {
  const vurl = ratchet?.crates.find((c) => c.name === 'vurl');
  const vurlOk = crateOk(vurl);
  const allOk = allCratesOk(ratchet);
  const totals = ratchetTotals(ratchet);
  const totalTrusted = sumTrusted(totals?.trusted);
  const jStepMap = new Map((ratchet?.j_steps ?? []).map((s) => [s.step, s]));

  return (
    <section className="wb-row12" id="status">
      <div className="wb-c7 wb-col">
        <div className="wb-chapter">05 · Status</div>
        <h2 className="wb-h2">What is verified, and what is still design</h2>

        <div className="wb-box-t">Per-crate verification ratchet</div>
        {ratchet ? (
          <div className="wb-table-wrap">
            <table className="wb-table" data-testid="crates-table">
              <thead>
                <tr>
                  <th>Crate</th>
                  <th>Step</th>
                  <th>Verified</th>
                  <th>Trusted</th>
                  <th>Time</th>
                  <th>Tests</th>
                  <th>LOC</th>
                </tr>
              </thead>
              <tbody>
                {ratchet.crates.map((c) => {
                  const t = trustedTotal(c);
                  return (
                    <tr key={c.name}>
                      <td className="mono">{c.name}</td>
                      <td className="mono">{c.step ?? NR}</td>
                      <td className="mono">{c.verified.toLocaleString('en-US')}</td>
                      <td className="mono">{t === null ? NR : t}</td>
                      <td className="mono">{c.verify_seconds}s</td>
                      <td className="mono">
                        {c.tests_passed}/{c.tests_passed + c.tests_failed}
                      </td>
                      <td className="mono">{c.source_lines.toLocaleString('en-US')}</td>
                    </tr>
                  );
                })}
              </tbody>
            </table>
          </div>
        ) : (
          <div className="wb-disclosure" data-testid="crates-table-missing">
            <h3>Ratchet not loaded</h3>
            <p>Per-crate verification counts: {NR}.</p>
          </div>
        )}

        <div className="wb-box-t">vjs &amp; vwasm work order (J0–J7)</div>
        <div data-testid="vjs-rows">
          {VJS_STEPS.map((s, i) => {
            const live = jStepMap.get(s.step);
            const verified = live?.status === 'verified' && live.errors === 0;
            const summary = live
              ? `${s.short} — ${live.status} (${live.verified.toLocaleString('en-US')} fns · ${live.test262_passed}/${live.test262_total})`
              : `${s.short} — ${NR}`;
            return (
              <DetailsRow
                key={s.step}
                k={s.step}
                v={summary}
                tone={live ? (verified ? 'verified' : 'critical') : 'neutral'}
                open={i === 0}
              >
                <Field label="Crate">{live ? live.crate : NR}</Field>
                <Field label="Scope">{live ? live.scope : s.scope}</Field>
                <Field label="Theorem">{live ? live.theorem : s.exit}</Field>
                <Field label="Ratchet metrics">
                  {live
                    ? `${live.verified.toLocaleString('en-US')} verified · ${live.trusted} trusted · ${live.verify_seconds}s · ${live.tests_passed} crate tests · ${live.test262_passed}/${live.test262_total} conformance tests`
                    : NR}
                </Field>
              </DetailsRow>
            );
          })}
        </div>

        {ratchet?.vm_benchmarks && ratchet.vm_benchmarks.length > 0 && (
          <div className="wb-col" data-testid="vm-benchmarks">
            <div className="wb-box-t">
              J7 bytecode VM vs. AST interpreter (geomean{' '}
              {ratchet.vm_benchmarks_geomean_speedup !== undefined
                ? `${ratchet.vm_benchmarks_geomean_speedup}×`
                : NR}
              )
            </div>
            <div className="wb-table-wrap">
              <table className="wb-table">
                <thead>
                  <tr>
                    <th>Benchmark</th>
                    <th>AST (ms)</th>
                    <th>Bytecode (ms)</th>
                    <th>Speedup</th>
                    <th>Result == AST</th>
                  </tr>
                </thead>
                <tbody>
                  {ratchet.vm_benchmarks.map((b) => (
                    <tr key={b.name}>
                      <td className="mono">{b.name}</td>
                      <td className="mono">{b.ast_ms.toFixed(2)}</td>
                      <td className="mono">{b.bytecode_ms.toFixed(2)}</td>
                      <td className="mono">{b.speedup}×</td>
                      <td className="mono">{b.result_verified_equal ? 'equal' : 'mismatch'}</td>
                    </tr>
                  ))}
                </tbody>
              </table>
            </div>
          </div>
        )}

        <div className="wb-box-t">vurl modules &amp; obligation graph</div>
        <div data-testid="modules">
          {VURL_MODULES.map((m, i) => (
            <DetailsRow
              key={m.id}
              k={`vurl · ${m.id}`}
              v={m.summary}
              tone={vurlOk ? 'verified' : 'critical'}
              open={i === 0}
            >
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
          <div className="wb-box-t">What vjs guarantees</div>
          <pre className="wb-code" data-testid="fuel-theorem">{FUEL_THEOREM}</pre>
        </div>

        <div className="wb-dag-frame">
          {vurl ? (
            <IxProofDag
              nodes={VURL_DAG_NODES.map((n) => ({ ...n, state: vurlOk ? 'verified' : 'invalidated' }))}
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
          Click a node to see which obligations depend on it. Sources:{' '}
          <Source href={blobUrl('docs/verified-browser-engine.md')}>design doc</Source> ·{' '}
          <Source href={blobUrl('browser/README.md')}>browser README</Source> ·{' '}
          <Source href="browser/ratchet.json">raw ratchet</Source> ·{' '}
          <Source href={blobUrl('browser/url/tests/data/PROVENANCE')}>WPT provenance</Source>
        </p>
      </div>

      <div className="wb-c5 wb-col">
        <div className="wb-disclosure" data-testid="honesty-card">
          <h3>Verified engine crates; kernel &amp; browser UI still design</h3>
          <p>
            The URL algorithms (<code>vurl</code>), the full J0–J7 JavaScript engine
            (<code>vjs_spec</code> through <code>vjs_vm</code>), Web IDL boundary
            (<code>vjs_webidl</code>), and WebAssembly 1.0 sandbox (<code>vwasm</code>) are
            implemented and verified in Rust with Verus
            {totals
              ? ` (${totals.crates} crates, ${totals.verified.toLocaleString('en-US')} verified functions, ${totalTrusted} trusted items)`
              : ''}
            . The browser kernel theorems, Nanvix renderer isolation, HTML/CSS layout, and full
            browser UI remain design/next phases. Progress is published only from the live ratchet
            report.
          </p>
        </div>

        {ratchet?.test262_suites && ratchet.test262_suites.length > 0 && (
          <div className="wb-col" data-testid="suites-table">
            <div className="wb-box-t">Conformance &amp; differential suites</div>
            <div className="wb-table-wrap">
              <table className="wb-table">
                <thead>
                  <tr>
                    <th>Step</th>
                    <th>Suite</th>
                    <th>Pass</th>
                  </tr>
                </thead>
                <tbody>
                  {ratchet.test262_suites.map((s) => (
                    <tr key={`${s.step}-${s.suite}`}>
                      <td className="mono">{s.step}</td>
                      <td>{s.suite}</td>
                      <td className="mono">
                        {s.passed}/{s.total}
                      </td>
                    </tr>
                  ))}
                </tbody>
              </table>
            </div>
          </div>
        )}

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
          {totals && allOk
            ? ` Workspace-wide: ${totals.verified.toLocaleString('en-US')} verified functions across ${totals.crates} crates, ${totalTrusted} trusted items.`
            : ''}
        </p>
      </div>
    </section>
  );
};

export default SectionStatus;
