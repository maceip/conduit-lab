import React, { useEffect, useState } from 'react';
import { Badge, Button } from '@clickhouse/click-ui';
import { loadText, NR, type ProofShowcaseItem, type Ratchet } from './data';
import {
  ADMIT_LINES,
  COUNTEREXAMPLE_LINES,
  TIMEOUT_LINES,
  VURL_VERIFIED_LINES,
  type ObligationState,
  type VerusCodeLine,
} from './content/vurl';
import { IconCheck, IconClock, IconExternal, IconShieldAlert, IconX } from './icons';
import { Source } from './parts';

interface StateConfig {
  id: ObligationState;
  label: string;
  summary: string;
  tone: 'proved' | 'fail' | 'warn';
  fileLabel: string;
  lines: VerusCodeLine[];
  defaultLine: number;
  badgeText: string;
  badgeState: 'success' | 'danger' | 'warning';
}

const OBLIGATION_STATES: StateConfig[] = [
  {
    id: 'verified',
    label: 'Verified',
    summary: 'Z3 proved UNSAT across every input',
    tone: 'proved',
    fileLabel: 'browser/url/src/percent.rs',
    lines: VURL_VERIFIED_LINES,
    defaultLine: 8,
    badgeText: 'PROVED (0 ADMITS)',
    badgeState: 'success',
  },
  {
    id: 'failed',
    label: 'Counterexample',
    summary: 'Z3 returns a concrete breaking input',
    tone: 'fail',
    fileLabel: 'illustrative mutation — not in vurl',
    lines: COUNTEREXAMPLE_LINES,
    defaultLine: 4,
    badgeText: 'FALSIFIED (SAT)',
    badgeState: 'danger',
  },
  {
    id: 'timeout',
    label: 'Rlimit timeout',
    summary: 'Solver budget exhausted; CI fails',
    tone: 'warn',
    fileLabel: 'illustrative timeout — not in vurl',
    lines: TIMEOUT_LINES,
    defaultLine: 4,
    badgeText: 'RLIMIT EXCEEDED',
    badgeState: 'warning',
  },
  {
    id: 'admit',
    label: 'Admit bypass',
    summary: 'Counted as trusted; rejected by ratchet',
    tone: 'warn',
    fileLabel: 'illustrative bypass — not in vurl',
    lines: ADMIT_LINES,
    defaultLine: 5,
    badgeText: 'TRUSTED BYPASS',
    badgeState: 'warning',
  },
];

const StateIcon: React.FC<{ state: ObligationState; size?: number }> = ({ state, size = 14 }) => {
  if (state === 'verified') return <IconCheck size={size} />;
  if (state === 'failed') return <IconX size={size} />;
  if (state === 'timeout') return <IconClock size={size} />;
  return <IconShieldAlert size={size} />;
};

const SectionVerus: React.FC<{ ratchet: Ratchet | null }> = ({ ratchet }) => {
  const [workbenchTab, setWorkbenchTab] = useState<'obligations' | 'live'>('obligations');
  const [mode, setMode] = useState<ObligationState>('verified');
  const [expandedLine, setExpandedLine] = useState<number>(8);

  const showcase: ProofShowcaseItem[] = ratchet?.proof_showcase ?? [];
  const [selectedProofCrate, setSelectedProofCrate] = useState<string>('');
  const [sourceCache, setSourceCache] = useState<Record<string, string>>({});
  const [sourceError, setSourceError] = useState<string | null>(null);
  const [loadingSource, setLoadingSource] = useState(false);

  const activeConfig = OBLIGATION_STATES.find((s) => s.id === mode)!;

  useEffect(() => {
    if (showcase.length > 0 && !selectedProofCrate) {
      setSelectedProofCrate(showcase[0].crate);
    }
  }, [showcase, selectedProofCrate]);

  const activeProof = showcase.find((item) => item.crate === selectedProofCrate) ?? showcase[0] ?? null;

  useEffect(() => {
    if (workbenchTab !== 'live' || !activeProof) return;
    if (sourceCache[activeProof.source]) {
      setSourceError(null);
      return;
    }
    let cancelled = false;
    setLoadingSource(true);
    setSourceError(null);
    loadText(activeProof.source)
      .then((text) => {
        if (!cancelled) {
          setSourceCache((prev) => ({ ...prev, [activeProof.source]: text }));
          setLoadingSource(false);
        }
      })
      .catch((err) => {
        if (!cancelled) {
          setSourceError(`Could not fetch ${activeProof.source} (${(err as Error).message}).`);
          setLoadingSource(false);
        }
      });
    return () => {
      cancelled = true;
    };
  }, [workbenchTab, activeProof, sourceCache]);

  const switchMode = (next: ObligationState) => {
    const cfg = OBLIGATION_STATES.find((s) => s.id === next)!;
    setWorkbenchTab('obligations');
    setMode(next);
    setExpandedLine(cfg.defaultLine);
  };

  const liveLines = activeProof && sourceCache[activeProof.source]
    ? sourceCache[activeProof.source].split('\n').slice(0, 42)
    : [];

  return (
    <section className="ch-spec-row" id="proofs">
      <div className="ch-prose-col">
        <div className="ch-section-lead">
          <img
            src="assets/sticker-scroll.webp"
            alt="Sealed formal specification scroll illustration"
            className="ch-sticker-medallion"
            width={72}
            height={72}
          />
          <h2 className="ch-section-title">What a proof guarantees that tests never can</h2>
        </div>

        <p className="ch-prose-text">
          Unit tests check only the cases a human remembered to write. Verus compiles Rust
          implementations together with Rust specifications into SMT queries for Z3: does{' '}
          <em>any</em> input exist that breaks the postcondition? An <code>UNSAT</code> answer
          proves the contract across every valid input; a <code>SAT</code> answer hands back a
          concrete counterexample.
        </p>

        <p className="ch-prose-text">
          Every proof obligation finishes in one of four states, and only one is a proof. Select a
          state below—the failure views inject a one-character typo into a real{' '}
          <code>vurl</code> helper because all verified crates carry zero failing obligations.
        </p>

        <div className="ch-state-selector" role="group" aria-label="Verus obligation states">
          {OBLIGATION_STATES.map((st) => (
            <button
              key={st.id}
              type="button"
              className="ch-state-btn"
              data-testid={`state-${st.id}`}
              data-active={workbenchTab === 'obligations' && mode === st.id}
              data-tone={st.tone}
              aria-pressed={workbenchTab === 'obligations' && mode === st.id}
              onClick={() => switchMode(st.id)}
            >
              <span className="ch-state-title" data-tone={st.tone}>
                <StateIcon state={st.id} size={14} />
                <span>{st.label}</span>
              </span>
              <span className="ch-state-summary">{st.summary}</span>
            </button>
          ))}
        </div>

        {workbenchTab === 'obligations' && mode === 'failed' && (
          <div className="ch-fix-action">
            <Button
              type="secondary"
              data-testid="btn-fix-typo"
              onClick={() => switchMode('verified')}
            >
              Fix typo (r &lt; 15 → r &lt; 16) &amp; verify
            </Button>
          </div>
        )}

        <p className="ch-prose-note">
          Every proof still trusts Verus, Z3, <code>rustc</code>, and the specification text
          itself. To catch specification mistakes, every spec is pinned to an upstream standard
          commit and differentially tested against WPT, <code>tc39/test262</code>, and{' '}
          <code>WebAssembly/spec</code>.
        </p>
      </div>

      <div className="ch-artifact-col">
        <div className="ch-workbench-tabs" role="tablist" aria-label="Proof workbench views">
          <button
            type="button"
            role="tab"
            className="ch-tab-btn"
            aria-selected={workbenchTab === 'obligations'}
            data-active={workbenchTab === 'obligations'}
            data-testid="tab-obligations"
            onClick={() => setWorkbenchTab('obligations')}
          >
            Obligation states (vurl)
          </button>
          <button
            type="button"
            role="tab"
            className="ch-tab-btn"
            aria-selected={workbenchTab === 'live'}
            data-active={workbenchTab === 'live'}
            data-testid="tab-live-proofs"
            onClick={() => setWorkbenchTab('live')}
          >
            Live crate proofs ({showcase.length || NR})
          </button>
        </div>

        {workbenchTab === 'obligations' ? (
          <>
            <div className="ch-verified-strip" data-tone={activeConfig.tone}>
              <span className="ch-mono" data-testid="verus-file">
                {activeConfig.fileLabel}
              </span>
              <Badge state={activeConfig.badgeState} text={activeConfig.badgeText} />
            </div>

            <div className="ch-code-workbench" data-testid="verus-code-workbench">
              <div className="ch-code-header">
                <span>Click any marked obligation line to inspect the Z3 verdict</span>
                <span className="ch-lane-note">Lanes: spec · exec · proof</span>
              </div>

              <div className="ch-code-lines">
                {activeConfig.lines.map((line) => {
                  const hasObl = !!line.obligation;
                  const isOpen = hasObl && expandedLine === line.lineNo;
                  const state = line.obligation?.state;
                  const rowTone =
                    state === 'verified'
                      ? 'proved'
                      : state === 'failed'
                      ? 'fail'
                      : state === 'timeout' || state === 'admit'
                      ? 'warn'
                      : undefined;

                  return (
                    <div
                      key={`${mode}-${line.lineNo}`}
                      className="ch-code-row"
                      data-state={isOpen ? rowTone : undefined}
                      data-clickable={hasObl}
                      onClick={hasObl ? () => setExpandedLine(line.lineNo) : undefined}
                    >
                      <span className="ch-lineno">{line.lineNo}</span>
                      <span className="ch-glyph" data-tone={rowTone}>
                        {state ? <StateIcon state={state} size={13} /> : null}
                      </span>
                      <span className="ch-lane-pill" data-lane={line.lane}>
                        {line.lane}
                      </span>
                      <span
                        className="ch-code-text"
                        data-testid={
                          isOpen ? `active-obligation-line-${line.lineNo}` : undefined
                        }
                      >
                        {line.text || '\u00a0'}
                      </span>

                      {isOpen && line.obligation && (
                        <div
                          className="ch-z3-inlay"
                          data-tone={rowTone}
                          data-testid={`inlay-${line.lineNo}`}
                        >
                          <div className="ch-inlay-head">
                            <span
                              className="ch-inlay-badge"
                              data-tone={rowTone}
                              data-testid={`inlay-state-${line.lineNo}`}
                            >
                              {line.obligation.state}
                            </span>
                            <strong>{line.obligation.summary}</strong>
                          </div>
                          <p className="ch-inlay-detail">{line.obligation.detail}</p>
                          {line.obligation.counterexample && (
                            <div className="ch-ce-table" data-testid="z3-counterexample">
                              {line.obligation.counterexample.map((row) => (
                                <div key={row.symbol} className="ch-ce-row">
                                  <span className="ch-ce-sym">{row.symbol}</span>
                                  <span className="ch-ce-sort">{row.sort}</span>
                                  <span className="ch-ce-val">{row.value}</span>
                                </div>
                              ))}
                            </div>
                          )}
                        </div>
                      )}
                    </div>
                  );
                })}
              </div>
            </div>

            <p className="ch-prose-note">
              Real <code>percent.rs</code> code transcribed from WHATWG URL §1.3. Beyond positive
              roundtrips, <code>vurl</code> also proves a negative edge case: for the six encode
              sets that omit <code>%</code>, <code>decode(encode(&quot;%41&quot;))</code> returns{' '}
              <code>&quot;A&quot;</code>, not <code>&quot;%41&quot;</code>.
            </p>
          </>
        ) : (
          <div className="ch-live-proof-panel" data-testid="live-proof-panel">
            {showcase.length > 0 && activeProof ? (
              <>
                <div className="ch-proof-picker" role="group" aria-label="Select verified crate proof">
                  {showcase.map((item) => (
                    <button
                      key={item.crate}
                      type="button"
                      className="ch-proof-pill"
                      data-testid={`proof-crate-${item.crate}`}
                      data-active={item.crate === activeProof.crate}
                      onClick={() => setSelectedProofCrate(item.crate)}
                    >
                      {item.label}
                    </button>
                  ))}
                </div>

                <div className="ch-verified-strip" data-tone={activeProof.errors === 0 ? 'proved' : 'fail'}>
                  <span className="ch-mono" data-testid="live-proof-file">
                    {activeProof.file}
                  </span>
                  <span className="ch-mono ch-proof-meta">
                    {activeProof.verified.toLocaleString('en-US')} verified · {activeProof.seconds}s
                  </span>
                </div>

                <div className="ch-code-workbench">
                  <div className="ch-code-header">
                    <span>Live excerpt fetched directly from {activeProof.source}</span>
                    <span className="ch-proof-links">
                      <Source href={activeProof.source}>
                        Full .rs <IconExternal size={11} />
                      </Source>
                      {' · '}
                      <Source href={activeProof.log}>
                        Raw Z3 log <IconExternal size={11} />
                      </Source>
                    </span>
                  </div>
                  {loadingSource ? (
                    <div className="ch-code-empty">Fetching verified source from {activeProof.source}…</div>
                  ) : sourceError ? (
                    <div className="ch-code-empty">{sourceError}</div>
                  ) : (
                    <div className="ch-code-lines" data-testid="live-proof-source">
                      {liveLines.map((text, idx) => (
                        <div key={idx} className="ch-code-row ch-code-row-plain">
                          <span className="ch-lineno">{idx + 1}</span>
                          <span className="ch-code-text">{text || '\u00a0'}</span>
                        </div>
                      ))}
                    </div>
                  )}
                </div>
              </>
            ) : (
              <div className="ch-disclosure-card">
                <h3>Proof showcase unavailable</h3>
                <p>Live crate proof files require browser/ratchet.json ({NR}).</p>
              </div>
            )}
          </div>
        )}
      </div>
    </section>
  );
};

export default SectionVerus;
