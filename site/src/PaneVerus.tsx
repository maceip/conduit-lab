import React from 'react';
import { IxBlind } from '@siemens/ix-react';
import {
  IxVerusEditor,
  IxCausalChain,
  type CausalStepNode,
} from '@maceip/ix-workbench-primitives';
import { NR, trustedTotal, type Ratchet } from './data';
import { VURL_EDITOR_LINES, BREAK_EDITOR_LINES } from './content/vurl';
import { SectionHead } from './parts';

const ANATOMY: CausalStepNode[] = [
  {
    id: 'req',
    kind: 'requires',
    tone: 'neutral',
    location: 'percent.rs · hex_val',
    expression: 'requires is_ascii_hex_digit(b)',
  },
  {
    id: 'inv',
    kind: 'invariant',
    tone: 'neutral',
    location: 'percent.rs · percent_encode',
    expression:
      'spec_percent_encode(input@, set) == out@ + spec_percent_encode(input@.subrange(i, n), set)',
  },
  {
    id: 'ens',
    kind: 'ensures',
    tone: 'verified',
    location: 'percent.rs · percent_encode',
    expression: 'ensures out@ == spec_percent_encode(input@, set)',
  },
  {
    id: 'ce',
    kind: 'counterexample',
    tone: 'critical',
    location: 'illustrative · hex_val',
    expression: 'Z3 model: b = 0x46 ("F") ⇒ r = 15, which breaks the typo r < 15',
  },
];

const PaneVerus: React.FC<{ ratchet: Ratchet | null }> = ({ ratchet }) => {
  const vurl = ratchet?.crates.find((c) => c.name === 'vurl');
  const trusted = trustedTotal(vurl);
  return (
    <>
      <SectionHead index="01 · First contact" title="Verus: Rust that proves itself">
        Verus is Rust plus mathematical specifications. You write the code once, write what it
        must do (<code>requires</code> / <code>ensures</code>), and the Z3 SMT solver proves the
        code matches the spec <strong>for every possible input</strong> — not for a sample of
        test cases. A test checks one run; a proof checks all runs.
      </SectionHead>

      <div>
        <div className="wb-eyebrow" style={{ marginBottom: 8 }}>How it works — real code, real proofs</div>
        <p className="wb-prose" style={{ marginBottom: 10 }}>
          This is <code>browser/url/src/percent.rs</code> from this project: the WHATWG URL
          percent-encoding standard, transcribed line by line into a <code>spec fn</code>, with
          the executable Rust proved equal to it. Click a gutter glyph to see what Z3 discharged.
          Lanes: <strong>spec</strong> (the standard), <strong>exec</strong> (the running code),{' '}
          <strong>proof</strong> (the argument that ties them together).
        </p>
        <div className="wb-editor-frame">
          <IxVerusEditor
            fileName="browser/url/src/percent.rs"
            lines={VURL_EDITOR_LINES}
            initialExpandedObligation={9}
          />
        </div>
      </div>

      <div>
        <div className="wb-eyebrow" style={{ marginBottom: 8 }}>Anatomy of one proof</div>
        <IxCausalChain steps={ANATOMY} />
      </div>

      <SectionHead index="01 · The other half" title="How it breaks">
        Verification is not a rubber stamp. There are exactly four states an obligation can be
        in, and only one of them is a proof. The failure below is{' '}
        <strong>illustrative</strong> — a one-character typo in a real vurl postcondition —
        because the actual crate has zero failed obligations.
      </SectionHead>

      <div className="wb-editor-frame short">
        <IxVerusEditor
          fileName="illustrative — how a proof fails"
          lines={BREAK_EDITOR_LINES}
          initialExpandedObligation={3}
        />
      </div>

      <IxBlind
        label="Verification also proves negative facts"
        sublabel="a real vurl theorem, not a test"
        variant="success"
        collapsed={false}
      >
        <div className="wb-blind-body">
          <code>lemma_roundtrip_fails_without_percent</code> proves that for the six encode sets
          which do not contain <code>%</code>, decoding does <strong>not</strong> invert encoding:{' '}
          <code>decode(encode("%41")) == "A" ≠ "%41"</code>. Only the component and
          form-urlencoded sets contain <code>%</code> — which is exactly why{' '}
          <code>encodeURIComponent</code> output always decodes back cleanly. The proof covers
          all inputs; a test suite could only sample them.
        </div>
      </IxBlind>

      <div className="wb-callout" data-tone={trusted === 0 ? 'verified' : 'warning'} data-testid="trusted-callout">
        <strong>The escape hatches are counted.</strong> <code>assume</code>, <code>admit</code>,{' '}
        <code>external_body</code> and <code>unsafe</code> let a human bypass the prover — so the
        ratchet counts every one as <em>trusted</em>, never as verified. vurl today:{' '}
        <strong data-testid="trusted-count">{trusted === null ? NR : trusted}</strong> trusted items.
      </div>

      <p className="wb-prose">
        <strong>What you still trust:</strong> Verus and Z3 themselves (an <code>unsat</code> answer
        is accepted without a checked certificate), the Rust compiler, and — most importantly —{' '}
        <strong>the spec</strong>. A proof only shows the code meets the spec as written; a wrong
        spec is a proved-wrong program. That is why this project differential-tests its specs
        against the Web Platform Tests and real crates, and pins the exact standard commit.
      </p>
    </>
  );
};

export default PaneVerus;