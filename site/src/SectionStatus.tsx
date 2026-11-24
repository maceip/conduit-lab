import React from 'react';
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
import { FUEL_THEOREM } from './content/vjs';
import { VURL_DAG_EDGES, VURL_DAG_NODES } from './content/vurl';
import { BROWSER_SUBSYSTEMS, type SubsystemSelection } from './HeroArchitecture';
import { IconChevron, IconExternal } from './icons';
import { ProofDag, Source } from './parts';

const CRATE_TO_SUBSYSTEM = new Map<string, string>(
  BROWSER_SUBSYSTEMS.flatMap((s) => s.crates.map((crateName) => [crateName, s.id] as const)),
);

const SectionStatus: React.FC<{
  ratchet: Ratchet | null;
  selection?: SubsystemSelection;
}> = ({ ratchet, selection }) => {
  const activeSubId = selection ? (selection.hoveredId ?? selection.selectedId) : null;
  const vurl = ratchet?.crates.find((c) => c.name === 'vurl');
  const vurlOk = crateOk(vurl);
  const allOk = allCratesOk(ratchet);
  const totals = ratchetTotals(ratchet);
  const totalTrusted = sumTrusted(totals?.trusted);
  const totalDiffCases = sumDifferentialCases(ratchet?.test262_suites);

  const maxBenchMs = Math.max(
    ...(ratchet?.vm_benchmarks ?? []).map((b) => Math.max(b.ast_ms, b.bytecode_ms)),
    1,
  );

  return (
    <section className="ch-status-section" id="ratchet">
      {/* Header + Evolving Verification Process Components */}
      <div className="ch-spec-row ch-spec-row-flush">
        <div className="ch-prose-col">
          <h2 className="ch-section-title">Browser Engine Components</h2>
          <p className="ch-prose-text">
            Eleven Rust crates implement URL parsing, JavaScript execution, Web IDL bindings,
            WebAssembly 1.0, and HTML/CSS core—compiled under <code>#![forbid(unsafe_code)]</code>{' '}
            and checked with Verus <code>--no-cheating</code> on every CI run.
          </p>
        </div>

        <div className="ch-artifact-col">
          <div className="ch-scope-note" data-testid="honesty-card">
            <h3 className="ch-subhead">Evolving Verification Process Components</h3>
            <p className="ch-prose-text">
              URL parsing, ECMAScript, Web IDL capabilities, and WebAssembly 1.0 verify end-to-end
              today
              {totals
                ? ` (${totals.verified.toLocaleString('en-US')} queries, ${totalTrusted} trusted items)`
                : ''}
              . Browser kernel non-interference theorems, <code>rspec!</code> origin/cookie
              policies, Nanvix sandboxing, and full HTML/CSS layout remain in active development.
            </p>
          </div>
        </div>
      </div>

      {/* Full-Width 11-Crate Verification Ratchet Ledger */}
      {ratchet ? (
        <div className="ch-table-card">
          <table className="ch-table" data-testid="crates-table">
            <thead>
              <tr>
                <th>Module</th>
                <th>Verified contract</th>
                <th className="ch-num">Queries</th>
                <th className="ch-num">Trusted</th>
                <th className="ch-num">Verify</th>
                <th className="ch-num">Tests</th>
                <th>Artifacts</th>
              </tr>
            </thead>
            <tbody>
              {ratchet.crates.map((c) => {
                const t = trustedTotal(c);
                const ok = crateOk(c);
                const subId = CRATE_TO_SUBSYSTEM.get(c.name) ?? null;
                const isSubActive = Boolean(subId && activeSubId === subId);
                return (
                  <tr
                    key={c.name}
                    data-sub-active={isSubActive ? 'true' : undefined}
                    onMouseEnter={() => {
                      if (subId && selection) selection.setHoveredId(subId);
                    }}
                    onMouseLeave={() => {
                      if (subId && selection) selection.setHoveredId(null);
                    }}
                  >
                    <td className="ch-mono ch-nowrap">
                      <span
                        className="ch-status-dot"
                        data-tone={ok ? 'proved' : 'fail'}
                        aria-hidden="true"
                      />
                      <strong>{c.name}</strong>
                    </td>
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
                  <td className="ch-mono">Total</td>
                  <td>
                    {allOk
                      ? 'All crates verified with zero errors and zero unsafe code'
                      : 'Some crates fail a proof, trust, or test check'}
                  </td>
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

      {/* Secondary Engineering Deep-Dives (Collapsed by Default) */}
      <div className="ch-drawer-stack">
        <details className="ch-drawer" data-testid="bench-drawer">
          <summary className="ch-drawer-summary">
            <span className="ch-drawer-title">
              Conformance suites &amp; bytecode VM benchmarks
            </span>
            <span className="ch-drawer-meta">
              {ratchet?.vm_benchmarks_geomean_speedup !== undefined
                ? `${ratchet.vm_benchmarks_geomean_speedup}× VM speedup`
                : NR}
              {totalDiffCases !== null
                ? ` · ${totalDiffCases.toLocaleString('en-US')} diff cases`
                : ''}
            </span>
            <IconChevron size={15} className="ch-drawer-chev" />
          </summary>

          <div className="ch-drawer-body">
            <div className="ch-two-col-equal">
              <div className="ch-col">
                {ratchet?.vm_benchmarks && ratchet.vm_benchmarks.length > 0 && (
                  <div className="ch-block" data-testid="vm-benchmarks">
                    <div className="ch-block-head">
                      <h3>Bytecode VM vs. AST interpreter</h3>
                      <span className="ch-mono ch-accent-text">
                        {ratchet.vm_benchmarks_geomean_speedup !== undefined
                          ? `${ratchet.vm_benchmarks_geomean_speedup}× geomean`
                          : NR}
                      </span>
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
                  <div className="ch-contract-title">vjs fuel &amp; explicit refusal contract</div>
                  <pre className="ch-contract-code" data-testid="fuel-theorem">
                    {FUEL_THEOREM}
                  </pre>
                </div>
              </div>

              <div className="ch-col">
                {ratchet?.test262_suites && ratchet.test262_suites.length > 0 && (
                  <div className="ch-block" data-testid="suites-table">
                    <div className="ch-block-head">
                      <h3>Conformance &amp; differential suites</h3>
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
                            <th>Suite</th>
                            <th className="ch-num">Pass</th>
                            <th className="ch-num">Diff cases</th>
                          </tr>
                        </thead>
                        <tbody>
                          {ratchet.test262_suites.map((s) => (
                            <tr key={`${s.step}-${s.suite}`}>
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
              </div>
            </div>
          </div>
        </details>

        <details className="ch-drawer" data-testid="dag-drawer">
          <summary className="ch-drawer-summary">
            <span className="ch-drawer-title">vurl obligation dependency graph</span>
            <span className="ch-drawer-meta" data-tone={vurl ? (vurlOk ? 'proved' : 'fail') : 'neutral'}>
              {vurl ? (vurlOk ? 'WHATWG URL · verified' : 'WHATWG URL · check failed') : NR}
            </span>
            <IconChevron size={15} className="ch-drawer-chev" />
          </summary>

          <div className="ch-drawer-body">
            {vurl ? (
              <ProofDag nodes={VURL_DAG_NODES} edges={VURL_DAG_EDGES} verified={vurlOk} />
            ) : (
              <div className="ch-disclosure-card">
                <h3>Obligation graph unavailable</h3>
                <p>The dependency graph draws only from live browser/ratchet.json data.</p>
              </div>
            )}
          </div>
        </details>

        <details className="ch-drawer" data-testid="tradeoffs-drawer">
          <summary className="ch-drawer-summary">
            <span className="ch-drawer-title">Architectural tradeoffs &amp; residual risks</span>
            <span className="ch-drawer-meta">{TRADEOFFS.length} decisions</span>
            <IconChevron size={15} className="ch-drawer-chev" />
          </summary>

          <div className="ch-drawer-body">
            <div className="ch-table-card" data-testid="tradeoffs">
              <table className="ch-table ch-table-compact">
                <thead>
                  <tr>
                    <th>Decision</th>
                    <th>What we give up</th>
                    <th>What we gain</th>
                    <th>Residual risk</th>
                  </tr>
                </thead>
                <tbody>
                  {TRADEOFFS.map((t, idx) => (
                    <tr key={idx}>
                      <td className="ch-cell-primary">{t.decision}</td>
                      <td>{t.givenUp}</td>
                      <td>{t.gained}</td>
                      <td>{t.residual}</td>
                    </tr>
                  ))}
                </tbody>
              </table>
            </div>
            <p className="ch-prose-note">
              Full review in{' '}
              <Source href={blobUrl('docs/vjs-plan-review.md')}>docs/vjs-plan-review.md §1</Source>.
            </p>
          </div>
        </details>
      </div>
    </section>
  );
};

export default SectionStatus;
