import type { ReactElement } from 'react';
import {
  GcHeapScene,
  PrattParserScene,
  TriColorGcScene,
  type GcHeapEdge,
  type GcHeapObject,
} from '../viz/stage';
import { NOT_RECORDED, RATCHET, formatRecorded } from './data';

/**
 * The heap the tri-color scene draws.
 *
 * The marks mirror `vjs_gc::Color` (`browser/vjs-gc/src/gc.rs`): black is a
 * visited root, grey a discovered object on the worklist, white an unmarked
 * candidate. The graph is the shape of the J6 crate's own invariant — it is a
 * diagram of the rule, not a claimed measurement.
 */
const HEAP_OBJECTS: GcHeapObject[] = [
  { id: 'root', position: [0, 0, 0], color: 'black' },
  { id: 'grey-a', position: [-2.6, 0.4, 0], color: 'grey' },
  { id: 'grey-b', position: [2.6, 0.4, 0], color: 'grey' },
  { id: 'white-a', position: [-3.6, -1.8, 0], color: 'white' },
  { id: 'white-b', position: [3.6, -1.8, 0], color: 'white' },
  { id: 'white-c', position: [0, 2.6, 0], color: 'white' },
];

/** A heap that respects the barrier: no grey object holds a black pointer. */
const CLEAN_EDGES: GcHeapEdge[] = [
  { from: 'root', to: 'grey-a' },
  { from: 'root', to: 'grey-b' },
  { from: 'grey-a', to: 'white-a' },
  { from: 'grey-a', to: 'white-b' },
  { from: 'grey-b', to: 'white-c' },
];

/** The same heap with one pointer that breaks it: grey → black. */
const VIOLATION_EDGES: GcHeapEdge[] = [...CLEAN_EDGES, { from: 'grey-a', to: 'root' }];

/** The verified figures for one J step, read from the ratchet. */
function stepFigure(step: string, field: 'verified' | 'testsPassed' | 'test262Passed'): string {
  const steps = RATCHET.jSteps;
  if (!steps.recorded) return NOT_RECORDED;
  const found = steps.value.find((entry) => entry.step === step);
  if (!found) return NOT_RECORDED;
  return formatRecorded(found[field]);
}

/**
 * The scene sheet.
 *
 * Tier 2 is the interactive WebGL heap — shown twice, once with the barrier
 * held and once with it broken, because the violation is only visible when the
 * scene is turned. Tier 3 are the two step-through algorithm traces.
 */
export function SceneSheet(): ReactElement {
  return (
    <section className="atelier__sheet" data-testid="scene-sheet">
      <div className="atelier__sheet-header">
        <h2 className="atelier__label">Scenes — tier 2 and tier 3</h2>
        <p className="atelier__meta">WebGL heap · Pratt parser · tri-color mark-sweep</p>
      </div>

      <div className="atelier__grid atelier__grid--wide">
        <div className="atelier__scene" data-testid="scene-gc-heap">
          <GcHeapScene
            objects={HEAP_OBJECTS}
            edges={CLEAN_EDGES}
            title="Tri-color heap — barrier held"
          />
          <p className="atelier__caption">Tier 2 — tri-color heap, barrier held</p>
          <p className="atelier__note">
            No grey object holds a black pointer, so the invariant is intact. J6 verifies{' '}
            {stepFigure('J6', 'verified')} queries.
          </p>
        </div>

        <div className="atelier__scene" data-testid="scene-gc-heap-violation">
          <GcHeapScene
            objects={HEAP_OBJECTS}
            edges={VIOLATION_EDGES}
            title="Tri-color heap — barrier violation"
          />
          <p className="atelier__caption">Tier 2 — tri-color heap, barrier broken</p>
          <p className="atelier__note">
            One grey object now points at a black object. The scene detects the break and marks it
            in the failure colour.
          </p>
        </div>

        <div className="atelier__scene" data-testid="scene-pratt-parser">
          <PrattParserScene title="Pratt parser step-through" />
          <p className="atelier__caption">Tier 3 — Pratt parser, crate J3</p>
          <p className="atelier__note">
            Token stream → precedence climbing → AST, tracing{' '}
            {stepFigure('J3', 'verified')} verified queries in <code>vjs_syntax</code>.
          </p>
        </div>

        <div className="atelier__scene" data-testid="scene-tri-color-gc">
          <TriColorGcScene title="Tri-color mark-sweep step-through" />
          <p className="atelier__caption">Tier 3 — tri-color mark-sweep, crate J6</p>
          <p className="atelier__note">
            Roots → marking → sweeping, tracing{' '}
            {stepFigure('J6', 'test262Passed')} test262 cases.
          </p>
        </div>
      </div>
    </section>
  );
}
