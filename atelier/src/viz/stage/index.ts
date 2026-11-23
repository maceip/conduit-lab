/**
 * Tier 2 and Tier 3 visualization components.
 *
 * - `GcHeapScene` — interactive WebGL tri-color GC heap (raw `three`).
 * - `PrattParserScene` / `TriColorGcScene` — 2D SVG step-through diagrams of
 *   the verified algorithms in `browser/vjs-syntax` (J3) and
 *   `browser/vjs-gc` (J6).
 */
export { GcHeapScene } from './GcHeapScene';
export type { GcHeapSceneProps } from './GcHeapScene';

export { createGcHeapScene } from './threeScene';
export type { GcHeapSceneHandle, GcHeapSceneOptions } from './threeScene';

export {
  findTriColorViolations,
  GREY_TO_BLACK_REASON,
  TRI_COLOR_FILL,
  TRI_COLOR_LABEL,
} from './triColor';
export type { GcHeapEdge, GcHeapObject, TriColor, TriColorViolation } from './triColor';
