/**
 * Section hatching.
 *
 * Section hatching on 45 degrees is the single most recognisable motorcycle
 * magazine cue, and adjacent parts must hatch in *opposite* directions so two
 * neighbouring cuts never read as one. That is handled here: the caller hands
 * over an index and the parity of that index picks the direction.
 *
 * The direction is applied with `patternTransform`, so the hatch is fixed to
 * the drawing plane (screen space) rather than to the part — exactly how a
 * drafted section reads.
 */

/** Hatch angle for a given pattern index: alternating 45 / 135 degrees. */
export type HatchAngle = 45 | 135;

export interface HatchPattern {
  /** DOM id of the `<pattern>` element, namespaced by the caller's prefix. */
  id: string;
  /** Hatch direction in degrees. */
  angle: HatchAngle;
  /** Pattern tile size in user units. */
  size: number;
}

/** Tile size of the hatch pattern, in user units. */
export const HATCH_SIZE = 6;

/**
 * Make an id safe for use in a `url(#...)` reference.
 *
 * React 19's `useId()` already yields URL-safe ids (`_R_1_`), but older React
 * versions use `:` — so the prefix is sanitised defensively. The digits React
 * appends are preserved, which keeps the ids unique across instances.
 */
export function safeId(raw: string): string {
  return raw.replace(/[^a-zA-Z0-9_-]/g, '_');
}

/**
 * Describe the hatch pattern for a sectioned part.
 *
 * @param idPrefix namespace for the DOM id (React `useId()` in the caller).
 * @param index index of the sectioned part; parity selects the direction so
 *   that adjacent sectioned parts hatch in opposite directions.
 */
export function hatchPattern(idPrefix: string, index: number): HatchPattern {
  const angle: HatchAngle = index % 2 === 0 ? 45 : 135;
  return {
    id: `${safeId(idPrefix)}-hatch-${index}`,
    angle,
    size: HATCH_SIZE,
  };
}
