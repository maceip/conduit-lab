import React, { useState } from 'react';
import { NR, ratchetTotals, type Ratchet } from './data';
import { IconArrowRight, IconCheck, IconExternal, IconX } from './icons';
import { Source } from './parts';

type StepId = 'spec' | 'contract' | 'solver';

function renderStylizedVerusLine(text: string): React.ReactNode {
  const commentIdx = text.indexOf('//');
  const codePart = commentIdx >= 0 ? text.slice(0, commentIdx) : text;
  const commentPart = commentIdx >= 0 ? text.slice(commentIdx) : '';

  const tokenRe =
    /\b(pub|open|spec|proof|fn|requires|ensures|decreases|invariant|if|else|as|let|assume|solve|UNSAT|SAT)\b|\b(nat|u8|BitVec)\b|\b(upper_hex_digit|upper_hex)\b|(0x[0-9a-fA-F]+|\b\d+\b)/g;

  const nodes: React.ReactNode[] = [];
  let last = 0;
  let match: RegExpExecArray | null;
  let key = 0;

  while ((match = tokenRe.exec(codePart)) !== null) {
    if (match.index > last) {
      nodes.push(codePart.slice(last, match.index));
    }
    const tok = match[0];
    if (match[1]) {
      const isSpecKw =
        tok === 'spec' ||
        tok === 'proof' ||
        tok === 'requires' ||
        tok === 'ensures' ||
        tok === 'assume' ||
        tok === 'solve' ||
        tok === 'UNSAT';
      const isFailKw = tok === 'SAT';
      nodes.push(
        <span
          key={key++}
          className={isFailKw ? 'ch-tok-fail' : isSpecKw ? 'ch-tok-spec' : 'ch-tok-kw'}
        >
          {tok}
        </span>,
      );
    } else if (match[2]) {
      nodes.push(
        <span key={key++} className="ch-tok-ty">
          {tok}
        </span>,
      );
    } else if (match[3]) {
      nodes.push(
        <span key={key++} className="ch-tok-fn">
          {tok}
        </span>,
      );
    } else {
      nodes.push(
        <span key={key++} className="ch-tok-num">
          {tok}
        </span>,
      );
    }
    last = match.index + tok.length;
  }
  if (last < codePart.length) {
    nodes.push(codePart.slice(last));
  }
  if (commentPart) {
    nodes.push(
      <span key={key++} className="ch-tok-cmt">
        {commentPart}
      </span>,
    );
  }
  return nodes;
}

const SectionProofIntro: React.FC<{ ratchet: Ratchet | null }> = ({ ratchet }) => {
  const [activeStep, setActiveStep] = useState<StepId>('solver');
  const [bugInjected, setBugInjected] = useState<boolean>(false);

  const totals = ratchetTotals(ratchet);
  const vurlCrate = ratchet?.crates.find((c) => c.name === 'vurl');

  const stepHighlights: Record<StepId, number[]> = {
    spec: [1, 2, 3],
    contract: [5, 6, 7],
    solver: [6, 7, 10, 12],
  };
  const highlighted = new Set<number>(stepHighlights[activeStep]);

  const stepCards: Array<{
    id: StepId;
    num: string;
    title: string;
    snippet: string[];
    body: string;
  }> = [
    {
      id: 'spec',
      num: '01',
      title: 'Define the right answer in plain math',
      snippet: [
        'pub open spec fn upper_hex_digit(n: nat) -> u8 {',
        '    if n < 10 { (0x30 + n) as u8 } else { (0x41 + n - 10) as u8 }',
        '}',
      ],
      body: 'Written with math integers that cannot overflow, then stripped out at compile time for zero runtime cost.',
    },
    {
      id: 'contract',
      num: '02',
      title: 'Add input and output rules to the Rust function',
      snippet: [
        'fn upper_hex(n: u8) -> (r: u8)',
        '    requires n < 16,                         // valid input: 0..15',
        '    ensures  r == upper_hex_digit(n as nat), // promised output',
        `{ if n < 10 { 0x30 + n } else { ${bugInjected ? '0x41 + n - 9' : '0x41 + n - 10'} } }`,
      ],
      body: 'Callers may only pass 0..15, and the function promises its returned byte always matches step 01 without overflowing.',
    },
    {
      id: 'solver',
      num: '03',
      title: 'Ask Z3 to find any input that gives the wrong answer',
      snippet: bugInjected
        ? [
            'let n: BitVec<8>;  assume(n < 16);',
            'let r = if n < 10 { 0x30 + n } else { 0x41 + n - 9 };',
            'solve(r != upper_hex_digit(n))  // SAT -> n = 10 ("B" != "A")',
          ]
        : [
            'let n: BitVec<8>;  assume(n < 16);',
            'let r = if n < 10 { 0x30 + n } else { 0x41 + n - 10 };',
            'solve(r != upper_hex_digit(n))  // UNSAT -> no such input exists',
          ],
      body: 'Instead of testing a few examples, Z3 solves one equation for a bug. When none exists, every valid input is proved.',
    },
  ];

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
        {/* Left: 3 code-bearing construction cards (01, 02, 03) */}
        <div className="ch-proof-steps-col" role="tablist" aria-label="Steps to construct a Verus proof">
          {stepCards.map((st) => {
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

                <pre className="ch-step-code-snippet" data-testid={`step-snippet-${st.id}`}>
                  {st.snippet.map((line, idx) => (
                    <div key={idx} className="ch-step-code-line">
                      {renderStylizedVerusLine(line)}
                    </div>
                  ))}
                </pre>

                <p className="ch-proof-step-body">{st.body}</p>
              </button>
            );
          })}

          <p className="ch-proof-intro-bridge">
            Repeating this same pattern—with loop rules (<code>invariant</code>) and helper proofs (
            <code>proof fn</code>) for variable-length slices and syntax trees—produces every
            verified crate below.{' '}
            <a className="ch-mono-link" href="workbench.html" data-testid="intro-to-workbench">
              Open full Proof Workbench <IconArrowRight size={11} />
            </a>
          </p>
        </div>

        {/* Right: Full upper_hex Verus module + interactive bug toggle + Z3 query */}
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
                  <span className="ch-code-text">
                    {ln.text ? renderStylizedVerusLine(ln.text) : '\u00a0'}
                  </span>
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
