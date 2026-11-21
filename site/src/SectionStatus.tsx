import React from 'react';
import { Badge } from '@clickhouse/click-ui';
import {
  NR,
  allCratesOk,
  blobUrl,
  crateOk,
  ratchetTotals,
  sumDifferentialCases,
  sumTrusted,
  trustedTotal,
  type Ratchet,
} from './data';
import { TRADEOFFS } from './content/tradeoffs';
import { FUEL_THEOREM, VJS_STEPS } from './content/vjs';
import { VURL_DAG_EDGES, VURL_DAG_NODES, VURL_MODULES } from './content/vurl';
import { IconExternal } from './icons';
import { DetailsRow, Field, ProofDag, Source } from './parts';

const SectionStatus: React.FC<{ ratchet: Ratchet | null }> = ({ ratchet }) => {
  const vurl = ratchet?.crates.find((c) => c.name === 'vurl');
  const vurlOk = crateOk(vurl);
  const allOk = allCratesOk(ratchet);
  const totals = ratchetTotals(ratchet);
  const totalTrusted = sumTrusted(totals?.trusted);
  const totalDiffCases = sumDifferentialCases(ratchet?.test262_suites);
  const jStepMap = new Map((ratchet?.j_steps ?? []).map((s) => [s.step, s]));

  const maxBenchMs = Math.max(
    ...(ratchet?.vm_benchmarks ?? []).map((b) => Math.max(b.ast_ms, b.bytecode_ms)),
    1,
  );

  return (
    <section className="ch-status-section" id="ratchet">
      {/* Header + Accurate Scope Disclosure */}
      <div className="ch-spec-row ch-spec-row-flush">
        <div className="ch-prose-col">
          <div className="ch-section-lead">
            <img
              src="assets/flair-ratchet.webp"
              alt="Monotonic verification ratchet telemetry waveform"
              className="ch-flair-medallion"
              width={76}
              height={76}
            />
            <h2 className="ch-section-title">What is proved today, and what remains next-phase design</h2>
          </div>
          <p className="ch-prose-text">
            Every crate below compiles with <code>#![forbid(unsafe_code)]</code> and zero trusted
            escape hatches. Progress is tracked by a monotonic ratchet in{' '}
            <code>browser/scripts/ratchet.py</code>: verified function counts and conformance suites
            only move forward, and any PR that introduces an <code>admit()</code> or{' '}
            <code>assume()</code> breaks verification.
          </p>
        </div>

        <div className="ch-artifact-col">
          <div className="ch-honesty-card" data-testid="honesty-card">
            <div className="ch-honesty-header">
              <span>Current verification boundary — engine crates proved; browser kernel next</span>
              <Badge state="warning" text="SCOPE BOUNDARY" />
            </div>
            <p className="ch-prose-text">
              The WHATWG URL algorithms (<code>vurl</code>), the full J0–J7 JavaScript engine (
              <code>vjs_spec</code> through <code>vjs_vm</code>), the Web IDL capability boundary (
              <code>vjs_webidl</code>), and the sandboxed WebAssembly 1.0 interpreter (
              <code>vwasm</code>) are implemented and machine-verified in Rust
              {totals
                ? ` (${totals.crates} crates, ${totals.verified.toLocaleString('en-US')} verified functions, ${totalTrusted} trusted items)`
                : ''}
              . Browser kernel non-interference theorems, <code>rspec!</code> origin/CSP/CORS
              policies, Nanvix per-site sandboxing, HTML/CSS/XML integration, and browser chrome
              remain next phases.
            </p>
          </div>
        </div>
      </div>

      {/* Full-Width 11-Crate Verification Ratchet Ledger */}
      <div className="ch-block">
        <div className="ch-block-head">
          <h3>Per-crate verification ratchet</h3>
          <span className="ch-mono ch-muted">
            {totals
              ? `${totals.crates} crates · ${totals.verified.toLocaleString('en-US')} verified · ${totalTrusted} trusted · ${totals.verify_seconds}s`
              : NR}
          </span>
        </div>

        {ratchet ? (
          <div className="ch-table-card">
            <table className="ch-table" data-testid="crates-table">
              <thead>
                <tr>
                  <th>Crate</th>
                  <th>Track</th>
                  <th>Scope &amp; proved theorem</th>
                  <th className="ch-num">Verified</th>
                  <th className="ch-num">Trusted</th>
                  <th className="ch-num">Verify</th>
                  <th className="ch-num">Tests</th>
                  <th className="ch-num">LOC</th>
                  <th>Evidence</th>
                </tr>
              </thead>
              <tbody>
                {ratchet.crates.map((c) => {
                  const t = trustedTotal(c);
                  const ok = crateOk(c);
                  return (
                    <tr key={c.name}>
                      <td className="ch-mono ch-nowrap">
                        <span
                          className="ch-status-dot"
                          data-tone={ok ? 'proved' : 'fail'}
                          aria-hidden="true"
                        />
                        <strong>{c.name}</strong>
                      </td>
                      <td className="ch-mono ch-nowrap">{c.step ?? NR}</td>
                      <td>
                        <div className="ch-cell-primary">{c.scope ?? NR}</div>
                        {c.theorem && <div className="ch-cell-sub">{c.theorem}</div>}
                      </td>
                      <td className="ch-mono ch-num" data-tone={ok ? 'proved' : 'fail'}>
                        {c.verified.toLocaleString('en-US')}
                      </td>
                      <td className="ch-mono ch-num" data-tone={t === 0 ? 'proved' : 'fail'}>
                        {t === null ? NR : t}
                      </td>
                      <td className="ch-mono ch-num">{c.verify_seconds}s</td>
                      <td className="ch-mono ch-num">
                        {c.tests_passed}/{c.tests_passed + c.tests_failed}
                      </td>
                      <td className="ch-mono ch-num">{c.source_lines.toLocaleString('en-US')}</td>
                      <td className="ch-mono ch-nowrap">
                        {c.proof_source && (
                          <Source href={c.proof_source}>
                            proof <IconExternal size={11} />
                          </Source>
                        )}
                        {c.proof_source && c.log && ' · '}
                        {c.log && (
                          <Source href={c.log}>
                            log <IconExternal size={11} />
                          </Source>
                        )}
                      </td>
                    </tr>
                  );
                })}
              </tbody>
              {totals && (
                <tfoot>
                  <tr className="ch-total-row">
                    <td className="ch-mono">Workspace total</td>
                    <td className="ch-mono">{totals.crates} crates</td>
                    <td>{allOk ? 'All crates verified with zero errors and zero unsafe code' : 'Verification errors present'}</td>
                    <td className="ch-mono ch-num" data-tone={allOk ? 'proved' : 'fail'}>
                      {totals.verified.toLocaleString('en-US')}
                    </td>
                    <td className="ch-mono ch-num" data-tone={totalTrusted === 0 ? 'proved' : 'fail'}>
                      {totalTrusted ?? NR}
                    </td>
                    <td className="ch-mono ch-num">{totals.verify_seconds}s</td>
                    <td className="ch-mono ch-num">
                      {totals.tests_passed}/{totals.tests_passed + totals.tests_failed}
                    </td>
                    <td className="ch-mono ch-num">{totals.source_lines.toLocaleString('en-US')}</td>
                    <td className="ch-mono">
                      <Source href="browser/ratchet.json">ratchet.json</Source>
                    </td>
                  </tr>
                </tfoot>
              )}
            </table>
          </div>
        ) : (
          <div className="ch-disclosure-card" data-testid="crates-table-missing">
            <h3>Ratchet telemetry not loaded</h3>
            <p>Per-crate verification counts: {NR}.</p>
          </div>
        )}
      </div>

      {/* Two-Column Deep Engineering Telemetry */}
      <div className="ch-two-col-equal">
        {/* Left: J0-J7 Work Order + J7 VM Benchmarks + Fuel Theorem */}
        <div className="ch-col">
          <div className="ch-block">
            <div className="ch-block-head">
              <h3>J0–J7 JavaScript &amp; WebAssembly verification track</h3>
              <span className="ch-mono ch-muted">9 verified milestones</span>
            </div>
            <div className="ch-accordion-group" data-testid="vjs-rows">
              {VJS_STEPS.map((s, idx) => {
                const live = jStepMap.get(s.step);
                const verified = live?.status === 'verified' && live.errors === 0;
                const meta = live
                  ? `${live.verified.toLocaleString('en-US')} fns · ${live.test262_passed}/${live.test262_total}`
                  : NR;
                return (
                  <DetailsRow
                    key={s.step}
                    k={s.step}
                    v={s.short}
                    meta={meta}
                    tone={live ? (verified ? 'proved' : 'fail') : 'neutral'}
                    open={idx === 0}
                  >
                    <Field label="Crate(s)">{live ? <code>{live.crate}</code> : NR}</Field>
                    <Field label="Scope">{live ? live.scope : s.scope}</Field>
                    <Field label="Proved theorem">{live ? live.theorem : s.exit}</Field>
                    <Field label="Live ratchet metrics">
                      {live
                        ? `${live.verified.toLocaleString('en-US')} verified · ${live.trusted} trusted · ${live.verify_seconds}s verify · ${live.tests_passed} crate tests · ${live.test262_passed}/${live.test262_total} conformance`
                        : NR}
                    </Field>
                  </DetailsRow>
                );
              })}
            </div>
          </div>

          {ratchet?.vm_benchmarks && ratchet.vm_benchmarks.length > 0 && (
            <div className="ch-block" data-testid="vm-benchmarks">
              <div className="ch-bench-header">
                <img
                  src="assets/flair-differential.webp"
                  alt="Bytecode VM vs AST differential waveform"
                  className="ch-flair-thumb"
                  width={52}
                  height={52}
                />
                <div>
                  <h3>J7 bytecode VM vs. AST interpreter</h3>
                  <p className="ch-prose-note">
                    Geometric-mean speedup:{' '}
                    <strong className="ch-accent-text">
                      {ratchet.vm_benchmarks_geomean_speedup !== undefined
                        ? `${ratchet.vm_benchmarks_geomean_speedup}×`
                        : NR}
                    </strong>{' '}
                    with CompCert-style proved result equivalence (<code>VM == AST</code>).
                  </p>
                </div>
              </div>

              <div className="ch-table-card">
                <table className="ch-table ch-table-compact">
                  <thead>
                    <tr>
                      <th>Benchmark</th>
                      <th>AST vs. VM</th>
                      <th className="ch-num">AST</th>
                      <th className="ch-num">VM</th>
                      <th className="ch-num">Speedup</th>
                      <th className="ch-num">Equal</th>
                    </tr>
                  </thead>
                  <tbody>
                    {ratchet.vm_benchmarks.map((b) => (
                      <tr key={b.name}>
                        <td className="ch-mono ch-nowrap">{b.name}</td>
                        <td className="ch-bar-cell">
                          <div className="ch-bench-bars">
                            <div
                              className="ch-bench-bar ch-bench-ast"
                              style={{ width: `${(b.ast_ms / maxBenchMs) * 100}%` }}
                              title={`AST interpreter: ${b.ast_ms.toFixed(2)} ms`}
                            />
                            <div
                              className="ch-bench-bar ch-bench-vm"
                              style={{ width: `${(b.bytecode_ms / maxBenchMs) * 100}%` }}
                              title={`Bytecode VM: ${b.bytecode_ms.toFixed(2)} ms`}
                            />
                          </div>
                        </td>
                        <td className="ch-mono ch-num">{b.ast_ms.toFixed(1)}ms</td>
                        <td className="ch-mono ch-num">{b.bytecode_ms.toFixed(1)}ms</td>
                        <td className="ch-mono ch-num ch-accent-text">{b.speedup}×</td>
                        <td
                          className="ch-mono ch-num"
                          data-tone={b.result_verified_equal ? 'proved' : 'fail'}
                        >
                          {b.result_verified_equal ? 'equal' : 'mismatch'}
                        </td>
                      </tr>
                    ))}
                  </tbody>
                </table>
              </div>
            </div>
          )}

          <div className="ch-contract-box">
            <div className="ch-contract-title">The vjs fuel &amp; explicit refusal contract</div>
            <pre className="ch-contract-code" data-testid="fuel-theorem">
              {FUEL_THEOREM}
            </pre>
          </div>
        </div>

        {/* Right: Conformance & Differential Suites + Upgraded 9 Engineering Tradeoffs */}
        <div className="ch-col">
          {ratchet?.test262_suites && ratchet.test262_suites.length > 0 && (
            <div className="ch-block" data-testid="suites-table">
              <div className="ch-block-head">
                <h3>Conformance &amp; differential verification suites</h3>
                <span className="ch-mono ch-muted">
                  {totalDiffCases !== null
                    ? `${totalDiffCases.toLocaleString('en-US')} differential cases`
                    : NR}
                </span>
              </div>
              <div className="ch-table-card">
                <table className="ch-table ch-table-compact">
                  <thead>
                    <tr>
                      <th>Step</th>
                      <th>Suite</th>
                      <th className="ch-num">Pass</th>
                      <th className="ch-num">Diff cases</th>
                    </tr>
                  </thead>
                  <tbody>
                    {ratchet.test262_suites.map((s) => (
                      <tr key={`${s.step}-${s.suite}`}>
                        <td className="ch-mono ch-nowrap">{s.step}</td>
                        <td>{s.suite}</td>
                        <td className="ch-mono ch-num ch-nowrap" data-tone="proved">
                          {s.passed}/{s.total}
                        </td>
                        <td className="ch-mono ch-num ch-nowrap">
                          {typeof s.differential_cases === 'number'
                            ? s.differential_cases.toLocaleString('en-US')
                            : '—'}
                        </td>
                      </tr>
                    ))}
                  </tbody>
                </table>
              </div>
            </div>
          )}

          <div className="ch-block">
            <div className="ch-block-head">
              <h3>Nine engineering tradeoffs</h3>
              <span className="ch-mono ch-muted">Synced with plan review</span>
            </div>
            <div className="ch-accordion-group" data-testid="tradeoffs">
              {TRADEOFFS.map((t, idx) => (
                <DetailsRow key={idx} k={`T${idx + 1}`} v={t.decision} open={idx === 0}>
                  <Field label="Given up">{t.givenUp}</Field>
                  <Field label="Gained">{t.gained}</Field>
                  <Field label="Residual risk">{t.residual}</Field>
                </DetailsRow>
              ))}
            </div>
            <p className="ch-prose-note">
              Adapted from{' '}
              <Source href={blobUrl('docs/vjs-plan-review.md')}>docs/vjs-plan-review.md §1</Source>{' '}
              and updated to reflect completed J0–J7 crate verifications.
            </p>
          </div>
        </div>
      </div>

      {/* Full-Width vurl Modules & Zero-Overlap Proof Dependency Graph */}
      <div className="ch-spec-row ch-spec-row-sub">
        <div className="ch-prose-col">
          <h3 className="ch-subsection-title">vurl modules &amp; obligation graph</h3>
          <p className="ch-prose-text">
            Phase 1 transcribed WHATWG URL percent-encoding, IPv4, and IPv6 parsing into Verus.
            Each module separates specification, verified executable code, and proved algebraic
            properties—and explicitly documents what remains outside scope.
          </p>
          <div className="ch-accordion-group" data-testid="modules">
            {VURL_MODULES.map((m, idx) => (
              <DetailsRow
                key={m.id}
                k={m.id}
                v={m.summary}
                tone={vurlOk ? 'proved' : 'fail'}
                open={idx === 0}
              >
                <Field label="Proved executable functions">
                  <span className="ch-mono">{m.exec.join(' · ')}</span>
                </Field>
                <Field label="Proved theorems">
                  <span className="ch-mono">{m.theorems.join(' · ')}</span>
                </Field>
                <Field label="Explicitly out of scope">{m.gaps}</Field>
              </DetailsRow>
            ))}
          </div>
          <p className="ch-prose-note">
            Primary docs:{' '}
            <Source href={blobUrl('docs/verified-browser-engine.md')}>architecture plan</Source> ·{' '}
            <Source href={blobUrl('browser/README.md')}>browser README</Source> ·{' '}
            <Source href={blobUrl('browser/url/tests/data/PROVENANCE')}>WPT provenance</Source>.
          </p>
        </div>

        <div className="ch-artifact-col">
          {vurl ? (
            <ProofDag nodes={VURL_DAG_NODES} edges={VURL_DAG_EDGES} verified={vurlOk} />
          ) : (
            <div className="ch-disclosure-card">
              <h3>Obligation graph unavailable</h3>
              <p>The dependency graph renders only from live browser/ratchet.json data.</p>
            </div>
          )}
        </div>
      </div>
    </section>
  );
};

export default SectionStatus;
