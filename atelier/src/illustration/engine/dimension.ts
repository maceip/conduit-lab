import type { Vec2 } from '../../contract';

/**
 * Dimension lines.
 *
 * Drawing Standard 5.3 rule 6: extension lines from the feature, a dimension
 * line between them with tick terminators, and a mono value label.
 */
export interface Dimension {
  /** Extension line from the feature to the dimension line. */
  extensions: Array<{ a: Vec2; b: Vec2 }>;
  /** The dimension line itself. */
  line: { a: Vec2; b: Vec2 };
  /** Terminator ticks (45 degree slashes). */
  ticks: Array<{ a: Vec2; b: Vec2 }>;
  /** Label anchor (centred on the dimension line). */
  labelAt: Vec2;
  /** Label text. */
  label: string;
}

/** Distance the dimension line sits off the feature. */
export const DIMENSION_OFFSET = 18;

/** Length of the 45 degree terminator tick. */
export const DIMENSION_TICK = 6;

function tick(at: Vec2, horizontal: boolean): { a: Vec2; b: Vec2 } {
  const k = DIMENSION_TICK / 2;
  return horizontal
    ? { a: [at[0] - k, at[1] - k], b: [at[0] + k, at[1] + k] }
    : { a: [at[0] - k, at[1] - k], b: [at[0] + k, at[1] + k] };
}

/**
 * Build a dimension between two feature points. A horizontal pair is
 * dimensioned below the feature, a vertical pair to its right.
 */
export function dimensionLine(a: Vec2, b: Vec2, label: string): Dimension {
  const horizontal = Math.abs(b[0] - a[0]) >= Math.abs(b[1] - a[1]);
  if (horizontal) {
    const dimY = Math.max(a[1], b[1]) + DIMENSION_OFFSET;
    const p0: Vec2 = [a[0], dimY];
    const p1: Vec2 = [b[0], dimY];
    return {
      extensions: [
        { a, b: p0 },
        { a: b, b: p1 },
      ],
      line: { a: p0, b: p1 },
      ticks: [tick(p0, true), tick(p1, true)],
      labelAt: [(a[0] + b[0]) / 2, dimY - 5],
      label,
    };
  }
  const dimX = Math.max(a[0], b[0]) + DIMENSION_OFFSET;
  const p0: Vec2 = [dimX, a[1]];
  const p1: Vec2 = [dimX, b[1]];
  return {
    extensions: [
      { a, b: p0 },
      { a: b, b: p1 },
    ],
    line: { a: p0, b: p1 },
    ticks: [tick(p0, false), tick(p1, false)],
    labelAt: [dimX + 12, (a[1] + b[1]) / 2],
    label,
  };
}
