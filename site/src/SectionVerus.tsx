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
        <div className="wb-chapter">02 · Proofs</div>
        <h2 className="wb-h2">What a proof checks that a test cannot</h2>
        <p className="wb-prose">
          A test runs the code on the inputs someone thought of. Verus takes the Rust code plus a
          specification, also written in Rust, and turns each claim into a question for Z3: is
          there any input at all that breaks this? When Z3 answers no, the claim holds for every
          input. When it answers yes, it hands back the input.
        </p>
        <p className="wb-prose">
          Each claim, called an obligation, ends in one of four states, and only one of them is a
          proof. Pick a state to see it in the editor. The editor shows a real vurl
          postcondition. The counterexample, timeout and admit views add a one-character typo to
          it, because the real crate has no failing obligations to show.
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
          A proof still rests on Verus, Z3, the Rust compiler and the spec. If the spec is wrong,
          the code is proved to be wrong in the same way. So each spec here is pinned to an exact
          commit of the standard and tested against the Web Platform Tests and against the
          widely used <code>url</code> crate.
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
          This is percent-encoding from the WHATWG URL standard, transcribed into a spec function,
          with the executable Rust proved equal to it. Click a gutter glyph to see what Z3 checked.
          vurl also proves an edge case of the standard: for the six encode sets that do not
          contain <code>%</code>, <code>decode(encode("%41"))</code> is <code>"A"</code>, not{' '}
          <code>"%41"</code>.
        </p>
      </div>
    </section>
  );
};

export default SectionVerus;