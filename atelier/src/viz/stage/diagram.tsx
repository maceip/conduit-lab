import type { CSSProperties, ReactElement, ReactNode } from 'react';
import { BOARD, DASH, STROKE } from '../../contract/tokens';

/**
 * Shared drafting primitives for the Tier 3 scenes.
 *
 * The scenes are 2D algorithm diagrams in the manim-dsa tradition, but drawn
 * in this repository's drafter grammar: hairline strokes, mono labels, and
 * depth carried by stroke weight rather than by fills used as shadow.
 */

/**
 * The stroke discipline of the drawing standard, applied to every line in
 * every scene: `non-scaling-stroke`, round caps, round joins. Stroke weight
 * is passed explicitly so a scene can promote a line to a cut edge.
 */
export const HAIRLINE = {
  strokeLinecap: 'round',
  strokeLinejoin: 'round',
  vectorEffect: 'non-scaling-stroke',
} as const;

/** The register: uppercase mono at 9px with wide tracking. */
export const MONO: CSSProperties = {
  fontFamily: "'JetBrains Mono', ui-monospace, SFMono-Regular, Menlo, monospace",
  fontSize: 9,
  letterSpacing: '0.08em',
};

/** The register at a larger size, for a scene title. */
export const MONO_TITLE: CSSProperties = {
  ...MONO,
  fontSize: 11,
  letterSpacing: '0.12em',
};

/** Viewport used by both scenes so the stepper keeps a stable frame. */
export const DIAGRAM_VIEWBOX = '0 0 720 300';

export interface BoxProps {
  x: number;
  y: number;
  w: number;
  h: number;
  stroke?: string;
  /** Dash pattern, e.g. `DASH.hidden`. */
  dash?: string;
  fill?: string;
  /** Reveal progress in `[0, 1]`; drives the draw-on of the outline. */
  progress?: number;
  strokeWidth?: number;
}

/** A hairline rectangle. The only shape a scene uses for a node. */
export function Box(props: BoxProps): ReactElement {
  const {
    x,
    y,
    w,
    h,
    stroke = BOARD.line,
    dash,
    fill = 'none',
    progress = 1,
    strokeWidth = STROKE.structure,
  } = props;
  const perimeter = 2 * (w + h);
  const offset = perimeter * (1 - Math.max(0, Math.min(1, progress)));
  return (
    <rect
      x={x}
      y={y}
      width={w}
      height={h}
      fill={fill}
      stroke={stroke}
      strokeDasharray={dash}
      strokeDashoffset={progress >= 1 ? undefined : offset}
      strokeWidth={strokeWidth}
      {...HAIRLINE}
    />
  );
}

export interface LineProps {
  x1: number;
  y1: number;
  x2: number;
  y2: number;
  stroke?: string;
  dash?: string;
  /** Reveal progress in `[0, 1]`. */
  progress?: number;
  strokeWidth?: number;
}

/** A hairline connector. */
export function Line(props: LineProps): ReactElement {
  const { x1, y1, x2, y2, stroke = BOARD.line, dash, progress = 1, strokeWidth = STROKE.structure } = props;
  const length = Math.hypot(x2 - x1, y2 - y1);
  const offset = length * (1 - Math.max(0, Math.min(1, progress)));
  return (
    <line
      x1={x1}
      y1={y1}
      x2={x2}
      y2={y2}
      stroke={stroke}
      strokeDasharray={dash}
      strokeDashoffset={progress >= 1 ? undefined : offset}
      strokeWidth={strokeWidth}
      {...HAIRLINE}
    />
  );
}

export interface LabelProps {
  x: number;
  y: number;
  children: ReactNode;
  color?: string;
  size?: number;
  /** `start` (default), `middle` or `end`. */
  anchor?: 'start' | 'middle' | 'end';
  weight?: number;
  opacity?: number;
  title?: string;
}

/** A mono label in the drafting register. */
export function Label(props: LabelProps): ReactElement {
  const {
    x,
    y,
    children,
    color = BOARD.ink,
    size = 9,
    anchor = 'start',
    weight = 500,
    opacity = 1,
    title,
  } = props;
  return (
    <text
      x={x}
      y={y}
      fill={color}
      textAnchor={anchor}
      opacity={opacity}
      style={{ ...MONO, fontSize: size, fontWeight: weight }}
    >
      {title === undefined ? children : title}
    </text>
  );
}

/**
 * Reveal progress for the `index`-th element of `total` as the step's
 * progress `t` runs from 0 to 1. Each element takes an equal slice of the
 * step, so the diagram draws itself on left to right.
 */
export function reveal(t: number, index: number, total: number): number {
  if (total <= 0) return 1;
  const slice = 1 / total;
  const local = (t - index * slice) / slice;
  return Math.max(0, Math.min(1, local));
}

/** Dash pattern for a hidden or structural line. */
export const HIDDEN_DASH = DASH.hidden;
