import React, { useState } from 'react';
import { NR, ratchetTotals, type Ratchet } from './data';
import { IconArrowRight, IconCheck, IconExternal, IconX } from './icons';
import { Source } from './parts';

type StepId = 'spec' | 'contract' | 'solver';

interface IntroStep {
  id: StepId;
  num: string;
  title: string;
  body: string;
  highlightLines: number[];
}

const INTRO_STEPS: IntroStep[] = [
  {
    id: 'spec',
    num: '01',
    title: 'Write what "correct" means in pure math (spec fn)',
    body: 'upper_hex_digit defines the target ASCII byte over unbounded natural numbers (nat) with zero overflow risk. Verus erases spec fn before codegen, so it adds zero runtime cost.',
    highlightLines: [1, 2, 3],
  },
  {
    id: 'contract',
    num: '02',
    title: 'Attach requires & ensures to executable Rust',
    body: 'requires n < 16 forces every caller to prove its input is a 4-bit nibble before compiling—which also proves 0x30 + n and 0x41 + n - 10 cannot overflow u8. ensures promises the returned byte matches the spec.',
    highlightLines: [5, 6, 7],
  },
  {
    id: 'solver',
    num: '03',
    title: 'Z3 negates ensures across every possible input',
    body: 'Instead of running sample tests, Verus treats n as an 8-bit symbolic bitvector and asks Z3 to find any n < 16 where r != upper_hex_digit(n). UNSAT proves no buggy input exists; SAT returns the exact breaking value.',
    highlightLines: [6, 7, 10, 12],
  },
];

const SectionProofIntro: React.FC<{ ratchet: Ratchet | null }> = ({ ratchet }) => {
  const [activeStep, setActiveStep] = useState<StepId>('solver');
  const [bugInjected, setBugInjected] = useState<boolean>(false);

  const totals = ratchetTotals(ratchet);
  const vurlCrate = ratchet?.crates.find((c) => c.name === 'vurl');
  const stepObj = INTRO_STEPS.find((s) => s.id === activeStep) ?? INTRO_STEPS[2];
  const highlighted = new Set<number>(stepObj.highlightLines);

  const codeLines: Array<{ lineNo: number; text: string }> = [
    { lineNo: 1, text: 'pub open spec fn upper_hex_digit(n: nat) -> u8 {' },
    { lineNo: 2, text: '    if n < 10 { (0x30 + n) as u8 } else { (0x41 + n - 10) as u8 }' },
    { lineNo: 3, text: '}' },
    { lineNo: 4, text: '' },
    { lineNo: 5, text: 'fn upper_hex(n: u8) -> (r: u8)' },
    { lineNo: 6, text: '    requires n < 16,' },
    { lineNo: 7, text: '    ensures  r == upper_hex_digit(n as nat),' },
    { lineNo: 8, text: '{' },
    { lineNo: 9, text: '    if n < 10 {' },
    { lineNo: 10, text: '        0x30 + n' },
    { lineNo: 11, text: '    } else {' },
    {
      lineNo: 12,
      text: bugInjected
        ? '        0x41 + n - 9   // 1-char off-by-one bug (passes 0..9 tests)'
        : '        0x41 + n - 10',
    },
    { lineNo: 13, text: '    }' },
    { lineNo: 14, text: '}' },
  ];

  return (
    <section className="ch-proof-intro-section" id="how-proofs-work" data-testid="proof-intro">
      <div className="ch-proof-intro-head">
        <h2 className="ch-section-title">How a Proof Is Built on One Function</h2>
        <p className="ch-prose-text">
          Before looking at{' '}
          {totals ? `${totals.verified.toLocaleString('en-US')} proof queries` : 'the crate ledger'}{' '}
          across the browser engine, here is how Verus proves a single 4-line function from{' '}
          <code>browser/url/src/percent.rs</code>—converting a nibble (<code>0..15</code>) into its
          ASCII hex digit (<code>&apos;0&apos;..&apos;9&apos;</code>,{' '}
          <code>&apos;A&apos;..&apos;F&apos;</code>):
        </p>
      </div>

      <div className="ch-proof-intro-grid">
        {/* Left: 3-step construction rail */}
        <div className="ch-proof-steps-col" role="tablist" aria-label="Steps to construct a Verus proof">
          {INTRO_STEPS.map((st) => {
            const isActive = activeStep === st.id;
            return (
              <button
                key={st.id}
                type="button"
                role="tab"
                aria-selected={isActive}
                className="ch-proof-step-btn"
                data-active={isActive}
                data-testid={`proof-intro-step-${st.id}`}
                onClick={() => setActiveStep(st.id)}
              >
                <div className="ch-proof-step-top">
                  <span className="ch-proof-step-num">{st.num}</span>
                  <strong className="ch-proof-step-title">{st.title}</strong>
                </div>
                <p className="ch-proof-step-body">{st.body}</p>
              </button>
            );
          })}

          <p className="ch-proof-intro-bridge">
            Scaling this exact pattern—adding loop <code>invariant</code>s and inductive{' '}
            <code>proof fn</code> lemmas for unbounded byte slices and ASTs—produces every verified
            component in the table below.{' '}
            <a className="ch-mono-link" href="workbench.html" data-testid="intro-to-workbench">
              Open full Proof Workbench <IconArrowRight size={11} />
            </a>
          </p>
        </div>

        {/* Right: Real upper_hex Verus function + interactive bug toggle + Z3 query */}
        <div className="ch-proof-intro-card" data-testid="proof-intro-card">
          <div className="ch-code-header">
            <div className="ch-workbench-tabs" role="group" aria-label="Contract verification mode">
              <button
                type="button"
                className="ch-tab-btn"
                data-active={!bugInjected}
                aria-pressed={!bugInjected}
                data-testid="intro-mode-verified"
                onClick={() => setBugInjected(false)}
              >
                Verified code
              </button>
              <button
                type="button"
                className="ch-tab-btn"
                data-active={bugInjected}
                aria-pressed={bugInjected}
                data-testid="intro-mode-bug"
                onClick={() => setBugInjected(true)}
              >
                Inject off-by-one bug
              </button>
            </div>

            {bugInjected ? (
              <span className="ch-mono ch-muted" data-testid="intro-file-label">
                illustrative bug — not in vurl
              </span>
            ) : vurlCrate?.proof_source ? (
              <Source href={vurlCrate.proof_source}>
                <span data-testid="intro-file-label">browser/url/src/percent.rs</span>{' '}
                <IconExternal size={11} />
              </Source>
            ) : (
              <span className="ch-mono" data-testid="intro-file-label">
                browser/url/src/percent.rs
              </span>
            )}
          </div>

          <div className="ch-intro-code-lines" data-testid="intro-code-lines">
            {codeLines.map((ln) => {
              const isBugLine = bugInjected && ln.lineNo === 12;
              const isHi = highlighted.has(ln.lineNo);
              return (
                <div
                  key={ln.lineNo}
                  className="ch-code-row ch-code-row-plain"
                  data-state={isBugLine ? 'fail' : isHi ? 'proved' : undefined}
                >
                  <span className="ch-lineno">{ln.lineNo}</span>
                  <span className="ch-code-text">{ln.text || '\u00a0'}</span>
                </div>
              );
            })}
          </div>

          <div
            className="ch-intro-verdict"
            data-tone={bugInjected ? 'fail' : 'proved'}
            data-testid="intro-z3-verdict"
          >
            <div className="ch-inlay-head">
              <span className="ch-inlay-badge" data-tone={bugInjected ? 'fail' : 'proved'}>
                {bugInjected ? (
                  <>
                    <IconX size={11} /> SAT · counterexample
                  </>
                ) : (
                  <>
                    <IconCheck size={11} /> UNSAT · proved
                  </>
                )}
              </span>
              <strong>
                {bugInjected
                  ? 'Z3 finds n = 10 (returns "B" instead of "A")'
                  : 'Zero counterexamples exist across all n < 16'}
              </strong>
            </div>

            <pre className="ch-vc-formula" data-testid="intro-vc-formula">
              {bugInjected
                ? 'assume: bvult(n, 16)\nbody:   r = ite(bvult(n, 10), 0x30 + n, 0x41 + n - 9)\nnegate: assert(r != upper_hex_digit(n))\nz3:     SAT -> n = 10 (0x0a), r = 0x42 ("B"), expected 0x41 ("A")'
                : `assume: bvult(n, 16)\nbody:   r = ite(bvult(n, 10), 0x30 + n, 0x41 + n - 10)\nnegate: assert(r != upper_hex_digit(n))   // search for any failing n\nz3:     UNSAT (${vurlCrate ? `${vurlCrate.verified} vurl queries verified in ${vurlCrate.verify_seconds}s` : NR})`}
            </pre>
          </div>
        </div>
      </div>
    </section>
  );
};

export default SectionProofIntro;
