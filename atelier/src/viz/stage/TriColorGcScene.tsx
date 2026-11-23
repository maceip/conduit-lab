import type { ReactElement } from 'react';
import { BOARD, DASH, STROKE } from '../../contract/tokens';
import { Box, DIAGRAM_VIEWBOX, Label, Line, reveal } from './diagram';
import { Stepper, type Step } from './stepper';
import { TRI_COLOR_FILL, TRI_COLOR_LABEL } from './triColor';

/**
 * Tier 3 — the tri-color mark-sweep collector, tracing `browser/vjs-gc`
 * (crate J6).
 *
 * The heap is a six-slot arena that exercises every phase of `mark_sweep`
 * as the crate implements it:
 *
 * ```
 *   0 global  →  1 scope  →  2 closure  →  3 context  ⇄  4 env
 *   5 orphan                                   (unreachable)
 * ```
 *
 * The `context`/`env` pair is a cycle, which is what makes the trace
 * interesting: the crate's worklist is last-in-first-out, so `env` is
 * scanned and blackened before `context`, and `context` — still grey —
 * ends up holding a pointer to an already-black object.
 *
 * Every phase boundary and invariant named below is quoted from
 * `browser/vjs-gc/src/gc.rs`.
 */

/** The tri-color mark of a slot, plus the swept state. */
type SlotMark = 'white' | 'grey' | 'black' | 'free';

interface GcSlot {
  /** Arena slot index. */
  index: number;
  /** Object name. */
  name: string;
  /** Tri-color mark. */
  mark: SlotMark;
}

/** Arena slot names, in slot order. */
const SLOT_NAMES = ['global', 'scope', 'closure', 'context', 'env', 'orphan'] as const;

/** Build a heap state from a list of marks, one per slot. */
function heapState(marks: readonly SlotMark[]): GcSlot[] {
  return SLOT_NAMES.map((name, index) => ({ index, name, mark: marks[index] ?? 'white' }));
}

/**
 * The heap after each step of the mark phase, exactly as the crate's
 * `mark_sweep` leaves it. The worklist is last-in-first-out: `worklist.pop()`
 * takes the most recently pushed slot.
 */
const PHASE_1A = heapState(['white', 'white', 'white', 'white', 'white', 'white']);
const PHASE_1B = heapState(['grey', 'white', 'white', 'white', 'white', 'white']);
const AFTER_MARK_ROOT = heapState(['black', 'grey', 'white', 'white', 'white', 'white']);
const AFTER_MARK_SCOPE = heapState(['black', 'black', 'grey', 'white', 'white', 'white']);
const AFTER_SCAN_CLOSURE = heapState(['black', 'black', 'black', 'grey', 'grey', 'white']);
/** `env` has been scanned and blackened; `context` is still grey. */
const AFTER_SCAN_ENV = heapState(['black', 'black', 'black', 'grey', 'black', 'white']);
/** The sweep has run: the orphan is back on the free list. */
const AFTER_SWEEP = heapState(['black', 'black', 'black', 'black', 'black', 'free']);

/** Geometry of the six slots. */
const SLOT_X = [120, 300, 480, 180, 380, 580] as const;
const SLOT_W = 84;
const SLOT_H = 36;
const ROW_ONE_Y = 78;
const ROW_TWO_Y = 170;

/** Fill and label tone for each mark. */
function markTone(mark: SlotMark): { fill: string; label: string } {
  if (mark === 'free') return { fill: 'none', label: BOARD.rib };
  const fill = TRI_COLOR_FILL[mark];
  const label = mark === 'black' ? BOARD.ink : BOARD.page;
  return { fill, label };
}

/** Draw the six-slot arena with its pointers. */
function HeapDiagram(props: {
  slots: readonly GcSlot[];
  t: number;
  /** Highlight the grey-to-black pointer as a barrier violation. */
  showViolation: boolean;
}): ReactElement {
  const { slots, t, showViolation } = props;

  const byIndex = new Map<number, GcSlot>();
  for (const slot of slots) byIndex.set(slot.index, slot);

  const slot0 = byIndex.get(0);
  const slot3 = byIndex.get(3);
  const slot4 = byIndex.get(4);
  const slot5 = byIndex.get(5);

  const centre = (index: number): [number, number] => {
    const x = SLOT_X[index] ?? 0;
    const y = index <= 2 ? ROW_ONE_Y : ROW_TWO_Y;
    return [x + SLOT_W / 2, y + SLOT_H / 2];
  };

  const pointers: Array<{ key: string; points: Array<[number, number]> }> = [
    { key: '0-1', points: [[204, 96], [300, 96]] },
    { key: '1-2', points: [[384, 96], [480, 96]] },
    { key: '2-3', points: [[504, 114], [504, 134], [222, 134], [222, 170]] },
    { key: '2-4', points: [[540, 114], [540, 146], [422, 146], [422, 170]] },
    { key: '3-4', points: [[264, 188], [380, 188]] },
    { key: '4-3', points: [[422, 206], [422, 226], [222, 226], [222, 206]] },
  ];

  const violationActive =
    showViolation &&
    slot3?.mark === 'grey' &&
    slot4?.mark === 'black';

  return (
    <g>
      {pointers.map((pointer, index) => {
        const isViolation = violationActive && pointer.key === '3-4';
        const progress = reveal(t, index, pointers.length);
        const stroke = isViolation ? BOARD.fail : BOARD.line;
        const strokeWidth = isViolation ? STROKE.cutEdge : STROKE.structure;
        const nodes = pointer.points;
        const first = nodes[0];
        if (!first) return null;
        return (
          <g key={pointer.key} opacity={progress}>
            {nodes.slice(1).map((point, legIndex) => {
              const from = nodes[legIndex];
              if (!from) return null;
              return (
                <Line
                  key={`${pointer.key}-${legIndex}`}
                  x1={from[0]}
                  y1={from[1]}
                  x2={point[0]}
                  y2={point[1]}
                  stroke={stroke}
                  strokeWidth={strokeWidth}
                  progress={progress}
                />
              );
            })}
          </g>
        );
      })}
      {slots.map((slot, index) => {
        const progress = reveal(t, index, slots.length);
        const tone = markTone(slot.mark);
        const x = SLOT_X[slot.index] ?? 0;
        const y = slot.index <= 2 ? ROW_ONE_Y : ROW_TWO_Y;
        const isViolationSource = violationActive && slot.index === 3;
        return (
          <g key={slot.name} opacity={progress}>
            <Box
              x={x}
              y={y}
              w={SLOT_W}
              h={SLOT_H}
              fill={tone.fill}
              stroke={isViolationSource ? BOARD.fail : BOARD.line}
              dash={slot.mark === 'free' ? DASH.hidden : undefined}
              progress={progress}
            />
            <Label
              x={x + SLOT_W / 2}
              y={y + 22}
              anchor="middle"
              color={tone.label}
              size={10}
              weight={600}
            >
              {slot.name}
            </Label>
            <Label
              x={x + SLOT_W / 2}
              y={y + 48}
              anchor="middle"
              color={BOARD.rib}
              size={8}
            >
              {slot.mark === 'free'
                ? 'SLOT::FREE'
                : `SLOT ${slot.index} · ${TRI_COLOR_LABEL[slot.mark]}`}
            </Label>
          </g>
        );
      })}
      {slot0 !== undefined && slot0.mark !== 'white' ? (
        <Label x={centre(0)[0]} y={ROW_ONE_Y - 12} anchor="middle" color={BOARD.accent} size={8}>
          ROOT
        </Label>
      ) : null}
      {slot5 !== undefined && slot5.mark === 'free' ? (
        <Label x={centre(5)[0]} y={ROW_TWO_Y - 12} anchor="middle" color={BOARD.fail} size={8}>
          RECLAIMED
        </Label>
      ) : null}
    </g>
  );
}

/** The worklist strip under the arena. */
function Worklist(props: { indices: readonly number[]; t: number }): ReactElement {
  const { indices, t } = props;
  const names = indices.map((index) => SLOT_NAMES[index] ?? String(index));
  return (
    <g opacity={reveal(t, 6, 7)}>
      <Label x={120} y={248} color={BOARD.rib} size={8}>
        WORKLIST
      </Label>
      <Label x={190} y={248} color={names.length === 0 ? BOARD.rib : BOARD.live} size={9}>
        {names.length === 0 ? 'EMPTY' : `[ ${names.join(' , ')} ]`}
      </Label>
    </g>
  );
}

/** The scene header. */
function SceneHeader(props: { title: string }): ReactElement {
  return (
    <g>
      <Label x={20} y={26} color={BOARD.inkHi} size={11} weight={600}>
        {props.title}
      </Label>
      <Label x={700} y={26} anchor="end" color={BOARD.rib}>
        VJS_GC — J6 — MARK_SWEEP
      </Label>
      <Line x1={20} y1={38} x2={700} y2={38} stroke={BOARD.rib} strokeWidth={STROKE.hatch} />
    </g>
  );
}

/** One step of the GC trace. */
function GcStep(props: {
  title: string;
  slots: readonly GcSlot[];
  worklist: readonly number[];
  t: number;
  violation: boolean;
  notes: readonly string[];
}): ReactElement {
  return (
    <svg
      viewBox={DIAGRAM_VIEWBOX}
      className="stage-diagram"
      role="img"
      aria-label={`${props.title} — tri-color garbage collector trace`}
      preserveAspectRatio="xMidYMid meet"
    >
      <SceneHeader title={props.title} />
      <HeapDiagram slots={props.slots} t={props.t} showViolation={props.violation} />
      <Worklist indices={props.worklist} t={props.t} />
      {props.notes.map((note, index) => (
        <Label
          key={note}
          x={120}
          y={268 + index * 17}
          color={index === 0 ? BOARD.ink : BOARD.rib}
          size={9}
        >
          {note}
        </Label>
      ))}
    </svg>
  );
}

/**
 * The steps of the scene, in the order `mark_sweep` runs them.
 *
 * Exported so the clause of every step can be asserted on directly — the
 * requirement is that each step names a real phase or invariant of the
 * crate, and that is only checkable if the whole table is reachable.
 */
export const TRICOLOR_GC_STEPS: Step[] = [
  {
    caption:
      'Every arena slot starts white: unvisited, and therefore still a candidate for reclamation.',
    clause: 'vjs_gc J6 — mark_sweep Phase 1a: the tricolor array is initialised to all Color::White',
    render: (t) => (
      <GcStep
        title="1 · PHASE 1A — ARENA"
        slots={PHASE_1A}
        worklist={[]}
        t={t}
        violation={false}
        notes={[
          'COLORS: VEC<COLOR>, ONE ENTRY PER ARENA SLOT — ALL SIX ARE Color::White.',
          'NOTHING IS REACHABLE YET, SO EVERYTHING IS STILL A CANDIDATE FOR RECLAMATION.',
        ]}
      />
    ),
  },
  {
    caption:
      'A root is live and reachable, so it is turned grey and pushed onto the worklist.',
    clause:
      'vjs_gc J6 — roots_valid(heap, roots); Phase 1b seeds the Gray worklist from the roots',
    render: (t) => (
      <GcStep
        title="2 · PHASE 1B — ROOT SET"
        slots={PHASE_1B}
        worklist={[0]}
        t={t}
        violation={false}
        notes={[
          'ROOTS_VALID REQUIRES EVERY ROOT TO BE LIVE BEFORE THE COLLECTOR WILL RUN AT ALL.',
          'SEEDING IS IDEMPOTENT: A ROOT THAT IS NOT WHITE IS NOT PUSHED TWICE.',
        ]}
      />
    ),
  },
  {
    caption:
      'Scanning the grey root’s edge turns the white object grey and pushes it onto the worklist.',
    clause:
      'vjs_gc J6 — Phase 2 worklist mark: Color::White becomes Color::Gray on a scanned edge (lemma_white_to_gray_upto)',
    render: (t) => (
      <GcStep
        title="3 · PHASE 2 — MARK"
        slots={AFTER_MARK_ROOT}
        worklist={[1]}
        t={t}
        violation={false}
        notes={[
          'EACH SCANNED EDGE TO A WHITE OBJECT COLOURS IT GREY AND QUEUES IT.',
          'THE MEASURE FALLS BY ONE PER MARKED SLOT, WHICH IS HOW THE LOOP IS PROVED TO TERMINATE.',
        ]}
      />
    ),
  },
  {
    caption:
      'Scanning the grey scope turns the white closure grey, and the closure joins the worklist.',
    clause:
      'vjs_gc J6 — Phase 2 worklist mark: Color::White becomes Color::Gray on a scanned edge (lemma_white_to_gray_upto)',
    render: (t) => (
      <GcStep
        title="4 · PHASE 2 — MARK"
        slots={AFTER_MARK_SCOPE}
        worklist={[2]}
        t={t}
        violation={false}
        notes={[
          'EACH SCANNED EDGE TO A WHITE OBJECT COLOURS IT GREY AND QUEUES IT.',
          'THE MEASURE FALLS BY ONE PER MARKED SLOT, WHICH IS HOW THE LOOP IS PROVED TO TERMINATE.',
        ]}
      />
    ),
  },
  {
    caption:
      'Once every outgoing edge of a grey object has been scanned, that object is blackened.',
    clause:
      'vjs_gc J6 — Phase 2: a popped Gray object is set to Color::Black after all its edges are scanned (lemma_gray_to_black_upto)',
    render: (t) => (
      <GcStep
        title="5 · PHASE 2 — SCAN"
        slots={AFTER_SCAN_CLOSURE}
        worklist={[3, 4]}
        t={t}
        violation={false}
        notes={[
          'GREY MEANS “ON THE WORKLIST AND NOT YET SCANNED”; BLACK MEANS “SCANNED, ALL EDGES SEEN”.',
          'CLOSURE IS BLACKENED, AND ITS TWO CHILDREN CONTEXT AND ENV ARE BOTH QUEUED GREY.',
        ]}
      />
    ),
  },
  {
    caption:
      'In the context/env cycle the last-in-first-out worklist blackens env before context, so a grey object is left holding a pointer to an already-black one.',
    clause:
      'vjs_gc J6 — Inv 5: Dijkstra’s Tricolor Invariant — no Black-to-White edge',
    render: (t) => (
      <GcStep
        title="6 · THE TRI-COLOR INVARIANT"
        slots={AFTER_SCAN_ENV}
        worklist={[3]}
        t={t}
        violation
        notes={[
          'A GREY OBJECT HOLDING A BLACK POINTER — THE EDGE DRAWN IN RED IS THE ONE TO LOOK AT.',
          'THE PROVED INVARIANT IS THE OTHER SIDE OF THE TRIANGLE: NO BLACK OBJECT EVER POINTS AT A WHITE ONE.',
        ]}
      />
    ),
  },
  {
    caption:
      'The sweep frees every slot that is not reachable from the roots; the orphan goes back on the free list.',
    clause:
      'vjs_gc J6 — Phase 3: Linear Sweep and Exact Per-Realm Quota Recomputation',
    render: (t) => (
      <GcStep
        title="7 · PHASE 3 — SWEEP"
        slots={AFTER_SWEEP}
        worklist={[]}
        t={t}
        violation={false}
        notes={[
          'THE SWEEP IS A SINGLE PASS OVER THE ARENA: LIVE SLOTS ARE KEPT, THE REST BECOME SlotView::Free.',
          'THE PER-REALM LIVE OBJECT AND BYTE COUNTS ARE RECOMPUTED EXACTLY AS THE SLOTS ARE FREED.',
        ]}
      />
    ),
  },
  {
    caption:
      'Five slots survive and one is reclaimed, and the freed counts are exact rather than an estimate.',
    clause:
      'vjs_gc J6 — mark_sweep ensures: completeness (garbage reclamation) and exact freed statistics',
  render: (t) => (
    <GcStep
      title="8 · RESULT"
      slots={AFTER_SWEEP}
      worklist={[]}
      t={t}
      violation={false}
      notes={[
        'GcStats { total_slots: 6, surviving_slots: 5, freed_slots: 1, freed_bytes: EXACT }',
        'COMPLETENESS: EVERY UNREACHABLE SLOT IS FREE. SOUNDNESS: EVERY REACHABLE SLOT IS UNCHANGED.',
      ]}
    />
  ),
  },
];

export interface TriColorGcSceneProps {
  className?: string;
  /** Accessible name for the scene. */
  title?: string;
}

/**
 * Tier 3 — the tri-color mark-sweep step-through scene.
 *
 * A 2D SVG diagram in the manim-dsa tradition, drawn in the drafter grammar.
 */
export function TriColorGcScene(props: TriColorGcSceneProps = {}): ReactElement {
  const { className, title = 'Tri-color mark-sweep step-through' } = props;
  const steps = TRICOLOR_GC_STEPS;
  return (
    <section
      className={className === undefined ? 'stage-scene' : `stage-scene ${className}`}
      data-testid="tri-color-gc-scene"
      aria-label={title}
    >
      <Stepper steps={steps} label={title} />
    </section>
  );
}
