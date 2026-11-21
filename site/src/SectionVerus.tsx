import React, { useState } from 'react';
import { IxVerusEditor, type VerusEditorLine } from '@maceip/ix-workbench-primitives';
import { VURL_EDITOR_LINES, BREAK_EDITOR_LINES } from './content/vurl';
import type { WorkbenchTone } from '@maceip/ix-workbench-primitives';

const STATES: Array<{
  key: string;
  tone: WorkbenchTone;
  title: string;
  meaning: string;
  lines: VerusEditorLine[];
  expand: number;
  file: string;
}> = [
  {
    key: 'verified',
    tone: 'verified',
    title: '✓ verified',
    meaning: 'exec matches the spec for every input',
    lines: VURL_EDITOR_LINES,
    expand: 9,
    file: 'browser/url/src/percent.rs',
  },
  {
    key: 'failed',
    tone: 'critical',
    title: '✗ counterexample',
    meaning: 'Z3 returns a concrete input that breaks the spec',
    lines: BREAK_EDITOR_LINES,
    expand: 3,
    file: 'example failure — not from vurl',
  },
  {
    key: 'timeout',
    tone: 'warning',
    title: '⏱ rlimit timeout',
    meaning: 'solver budget ran out; unfinished is not passed',
    lines: BREAK_EDITOR_LINES,
    expand: 7,
    file: 'example failure — not from vurl',
  },
  {
    key: 'admit',
    tone: 'warning',
    title: '! admit',
    meaning: 'human bypass; counted as trusted, never verified',
    lines: BREAK_EDITOR_LINES,
    expand: 8,
    file: 'example failure — not from vurl',
  },
];

const SectionVerus: React.FC = () => {
  const [state, setState] = useState('verified');
  const active = STATES.find((s) => s.key === state)!;

  return (
    <section className="wb-row12" id="verus">
      <div className="wb-c5 wb-col">
        <div className="wb-chapter">01 · What Verus is</div>
        <h2 className="wb-h2">Rust checked against a written spec, for every input</h2>
        <p className="wb-prose">
          Verus checks Rust code against a written specification. The Z3 solver proves the code
          matches the spec <strong>for every input</strong>, not for a sample of test cases. A
          test checks one run; a proof checks all runs.
        </p>
        <p className="wb-prose">
          An obligation has four states. Only one of them is a proof. Pick a state to see it in
          the editor — the counterexample, timeout and admit views are an illustrative one-character
          typo in a real vurl postcondition, because the actual crate has zero failed obligations.
        </p>
        <div className="wb-states" role="group" aria-label="Obligation states">
          {STATES.map((s) => (
            <button
              key={s.key}
              type="button"
              className="wb-state"
              data-tone={s.tone}
              data-testid={`state-${s.key}`}
              aria-pressed={state === s.key}
              onClick={() => setState(s.key)}
            >
              <b>{s.title}</b>
              <span>{s.meaning}</span>
            </button>
          ))}
        </div>
        <p className="wb-prose wb-note">
          What you still trust: Verus and Z3 themselves, the Rust compiler, and the spec. A proof
          only shows the code meets the spec as written; a wrong spec is a proved-wrong program.
          The specs here are differential-tested against the Web Platform Tests and pinned to an
          exact standard commit.
        </p>
      </div>
      <div className="wb-c7 wb-col">
        <div className="wb-editor-frame">
          <IxVerusEditor
            key={active.key}
            fileName={active.file}
            lines={active.lines}
            initialExpandedObligation={active.expand}
          />
        </div>
        <p className="wb-prose wb-note">
          Real code from this project: the WHATWG URL percent-encoding standard transcribed into a
          spec function, with the executable Rust proved equal to it. Click a gutter glyph to see
          what Z3 checked. vurl also proves a negative fact:{' '}
          <code>decode(encode("%41")) ≠ "%41"</code> for the six encode sets without <code>%</code>.
        </p>
      </div>
    </section>
  );
};

export default SectionVerus;