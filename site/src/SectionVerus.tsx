import React, { useEffect, useState } from 'react';
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
  tone: 'proved' | 'fail' | 'warn';
  fileLabel: string;
  lines: VerusCodeLine[];
  defaultLine: number;
}

const OBLIGATION_STATES: StateConfig[] = [
  {
    id: 'verified',
    label: 'Verified',
    tone: 'proved',
    fileLabel: 'browser/url/src/percent.rs',
    lines: VURL_VERIFIED_LINES,
    defaultLine: 8,
  },
  {
    id: 'failed',
    label: 'Counterexample',
    tone: 'fail',
    fileLabel: 'illustrative typo — not in vurl',
    lines: COUNTEREXAMPLE_LINES,
    defaultLine: 4,
  },
  {
    id: 'timeout',
    label: 'Timeout',
    tone: 'warn',
    fileLabel: 'illustrative timeout — not in vurl',
    lines: TIMEOUT_LINES,
    defaultLine: 4,
  },
  {
    id: 'admit',
    label: 'Admit',
    tone: 'warn',
    fileLabel: 'illustrative bypass — not in vurl',
    lines: ADMIT_LINES,
    defaultLine: 5,
  },
];

const StateIcon: React.FC<{ state: ObligationState; size?: number }> = ({ state, size = 13 }) => {
  if (state === 'verified') return <IconCheck size={size} />;
  if (state === 'failed') return <IconX size={size} />;
  if (state === 'timeout') return <IconClock size={size} />;
  return <IconShieldAlert size={size} />;
};

const SectionVerus: React.FC<{ ratchet: Ratchet | null }> = ({ ratchet }) => {
  const initialCrateParam =
    typeof window !== 'undefined' ? new URLSearchParams(window.location.search).get('crate') : null;
  const [workbenchTab, setWorkbenchTab] = useState<'obligations' | 'live'>(() =>
    initialCrateParam ? 'live' : 'obligations',
  );
  const [mode, setMode] = useState<ObligationState>('verified');
  const [expandedLine, setExpandedLine] = useState<number>(8);

  const showcase: ProofShowcaseItem[] = ratchet?.proof_showcase ?? [];
  const [selectedProofCrate, setSelectedProofCrate] = useState<string>(initialCrateParam ?? '');
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
    ? sourceCache[activeProof.source].split('\n').slice(0, 40)
    : [];

  return (
    <section className="ch-spec-row" id="proofs">
      <div className="ch-prose-col">
        <h2 className="ch-section-title">How Verus proves every possible input</h2>

        <p className="ch-prose-text">
          Verus never runs your function on inputs one by one. Instead, it compiles Rust into
          symbolic equations and asks Z3 whether a bug is mathematically possible:
        </p>

        <dl className="ch-arch-ledger ch-how-ledger" data-testid="how-verus-steps">
          <div className="ch-arch-row">
            <dt>1. Symbolic variables, not sample values</dt>
            <dd>
              In <code>upper_hex(n: u8)</code> (line 6), <code>n</code> becomes an unknown 8-bit
              symbol rather than a test literal, turning the <code>if / else</code> body into one
              equation.
            </dd>
          </div>
          <div className="ch-arch-row">
            <dt>2. Search for any input that breaks the rule</dt>
            <dd>
              Verus assumes valid inputs (<code>n &lt; 16</code>) and asks Z3 to find any input
              where the promised output fails. <code>UNSAT</code> means none exist; <code>SAT</code>{' '}
              returns the exact failing input.
            </dd>
          </div>
          <div className="ch-arch-row">
            <dt>3. Loop induction for unbounded slices</dt>
            <dd>
              A slice <code>&amp;[u8]</code> (line 11) can have any length, so Z3 proves your loop{' '}
              <code>invariant</code> (line 14) holds at <code>i = 0</code> and survives one step{' '}
              <code>i → i + 1</code> while <code>decreases n - i</code> shrinks to 0.
            </dd>
          </div>
        </dl>

        <div className="ch-state-selector ch-state-compact" role="group" aria-label="Verus obligation states">
          {OBLIGATION_STATES.map((st) => (
            <button
              key={st.id}
              type="button"
              className="ch-state-btn ch-state-btn-compact"
              data-testid={`state-${st.id}`}
              data-active={workbenchTab === 'obligations' && mode === st.id}
              data-tone={st.tone}
              aria-pressed={workbenchTab === 'obligations' && mode === st.id}
              onClick={() => switchMode(st.id)}
            >
              <span className="ch-state-title" data-tone={st.tone}>
                <StateIcon state={st.id} size={13} />
                <span>{st.label}</span>
              </span>
            </button>
          ))}
        </div>

        {workbenchTab === 'obligations' && mode === 'failed' && (
          <div className="ch-fix-action">
            <button
              type="button"
              className="ch-cta-secondary ch-btn-inline"
              data-testid="btn-fix-typo"
              onClick={() => switchMode('verified')}
            >
              Fix typo (r &lt; 15 → r &lt; 16) &amp; re-verify
            </button>
          </div>
        )}

        <p className="ch-prose-note">
          Specs are pinned to upstream WHATWG, ECMA-262, and Wasm commits and differentially tested
          against WPT and <code>tc39/test262</code> so specification bugs cannot hide behind a valid
          proof.
        </p>
      </div>

      <div className="ch-artifact-col">
        <div className="ch-code-workbench" data-testid="verus-code-workbench">
          <div className="ch-code-header">
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
                Obligation states
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
              <span className="ch-mono" data-testid="verus-file">
                {activeConfig.fileLabel}
              </span>
            ) : activeProof ? (
              <span className="ch-proof-links">
                <Source href={activeProof.source}>
                  <span data-testid="live-proof-file">{activeProof.file}</span>{' '}
                  <IconExternal size={11} />
                </Source>
                {' · '}
                <Source href={activeProof.log}>
                  log <IconExternal size={11} />
                </Source>
              </span>
            ) : null}
          </div>

          {workbenchTab === 'obligations' ? (
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
                  <React.Fragment key={`${mode}-${line.lineNo}`}>
                    <div
                      className="ch-code-row ch-code-row-clean"
                      data-state={isOpen ? rowTone : undefined}
                      data-clickable={hasObl}
                      onClick={hasObl ? () => setExpandedLine(line.lineNo) : undefined}
                    >
                      <span className="ch-lineno">{line.lineNo}</span>
                      <span className="ch-glyph" data-tone={rowTone}>
                        {state ? <StateIcon state={state} size={13} /> : null}
                      </span>
                      <span
                        className="ch-code-text"
                        data-testid={
                          isOpen ? `active-obligation-line-${line.lineNo}` : undefined
                        }
                      >
                        {line.text || '\u00a0'}
                      </span>
                    </div>

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
                        {line.obligation.vcFormula && (
                          <pre className="ch-vc-formula" data-testid="z3-vc-formula">
                            {line.obligation.vcFormula}
                          </pre>
                        )}
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
                  </React.Fragment>
                );
              })}
            </div>
          ) : (
            <div className="ch-live-proof-panel" data-testid="live-proof-panel">
              {showcase.length > 0 && activeProof ? (
                <>
                  <div className="ch-proof-picker ch-proof-picker-bar" role="group" aria-label="Select verified crate proof">
                    {showcase.map((item) => (
                      <button
                        key={item.crate}
                        type="button"
                        className="ch-proof-pill"
                        data-testid={`proof-crate-${item.crate}`}
                        data-active={item.crate === activeProof.crate}
                        onClick={() => setSelectedProofCrate(item.crate)}
                      >
                        {item.crate}
                      </button>
                    ))}
                  </div>

                  {loadingSource ? (
                    <div className="ch-code-empty">Fetching {activeProof.source}…</div>
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
                </>
              ) : (
                <div className="ch-code-empty">
                  Live crate proof files require browser/ratchet.json ({NR}).
                </div>
              )}
            </div>
          )}
        </div>
      </div>
    </section>
  );
};

export default SectionVerus;
