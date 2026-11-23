import { BOARD } from '../../contract/tokens';

/**
 * Tri-color mark shared by the Tier 2 WebGL scene and the Tier 3 GC scene.
 *
 * The three marks mirror `vjs_gc::Color` (`browser/vjs-gc/src/gc.rs`):
 *
 * | mark    | crate          | meaning                                              |
 * |---------|----------------|------------------------------------------------------|
 * | `white` | `Color::White` | unvisited / unmarked candidate garbage                |
 * | `grey`  | `Color::Gray`  | discovered reachable object, queued on the worklist  |
 * | `black` | `Color::Black` | visited reachable object, outgoing edges all scanned |
 *
 * The crate spells it `Gray`; the drafting board calls it `grey`.
 */
export type TriColor = 'white' | 'grey' | 'black';

/** One heap object with its tri-color mark. */
export interface GcHeapObject {
  /** Stable identity, used to join objects to their pointers. */
  id: string;
  /** World position in the heap space. */
  position: [number, number, number];
  /** Tri-color mark. */
  color: TriColor;
}

/** A pointer from one heap object to another. */
export interface GcHeapEdge {
  from: string;
  to: string;
}

/** A pointer that breaks the tri-color barrier. */
export interface TriColorViolation {
  /** Source object id. */
  from: string;
  /** Target object id. */
  to: string;
  /** Why the pointer breaks the barrier. */
  reason: string;
}

/**
 * Fill for each tri-color mark.
 *
 * White is the proved / knockout tone (`--live`), grey is the label tone
 * (`--ink`), and black is the raised plate tone (`--raised`). The drafting
 * standard reserves `--accent` for live-verified status only, so it never
 * appears here.
 */
export const TRI_COLOR_FILL: Record<TriColor, string> = {
  white: BOARD.live,
  grey: BOARD.ink,
  black: BOARD.raised,
};

/** Uppercase mono label for each tri-color mark. */
export const TRI_COLOR_LABEL: Record<TriColor, string> = {
  white: 'WHITE',
  grey: 'GREY',
  black: 'BLACK',
};

/**
 * Why a grey-to-black pointer is a barrier violation.
 *
 * A grey object is still on the worklist: its outgoing edges have not all been
 * scanned. A black object has already been scanned, so it may already have
 * been swept past. A grey object holding a black pointer is the edge case the
 * tri-color scene exists to make visible — it is the pointer that a naive
 * sweep would follow past the mark phase.
 */
export const GREY_TO_BLACK_REASON =
  'grey object holds a pointer to an already-scanned black object';

/**
 * Find every pointer that breaks the tri-color barrier.
 *
 * The rule the scene enforces is the drafting-room one: **a grey object must
 * have no black pointer**. A pointer that does not join two known objects is
 * ignored rather than reported — the caller owns the heap's well-formedness.
 *
 * Note for readers of `browser/vjs-gc/src/gc.rs`: the invariant the Verus
 * proof carries is the other edge of the same triangle — `mark_sweep` Inv 5,
 * "Dijkstra's Tricolor Invariant — no Black-to-White edge". Both are real
 * states of a cyclic heap; the grey-to-black edge is the one this scene
 * highlights, and the black-to-white edge is the one the crate proves.
 */
export function findTriColorViolations(
  objects: readonly GcHeapObject[],
  edges: readonly GcHeapEdge[],
): TriColorViolation[] {
  const byId = new Map<string, GcHeapObject>();
  for (const object of objects) byId.set(object.id, object);

  const violations: TriColorViolation[] = [];
  for (const edge of edges) {
    const from = byId.get(edge.from);
    const to = byId.get(edge.to);
    if (!from || !to) continue;
    if (from.color === 'grey' && to.color === 'black') {
      violations.push({ from: edge.from, to: edge.to, reason: GREY_TO_BLACK_REASON });
    }
  }
  return violations;
}
