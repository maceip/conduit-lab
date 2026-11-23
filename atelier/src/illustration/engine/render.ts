import { createElement, type ReactElement, type ReactNode } from 'react';
import type { Tone, Vec2 } from '../../contract';
import { BOARD, DASH, SHADE, STROKE } from '../../contract/tokens';
import { BALLOON_R } from './balloon';
import { dimensionLine } from './dimension';
import { hatchPattern } from './hatch';
import type { RenderedPlate } from './index';

/**
 * Rendering: a projected plate -> SVG element tree.
 *
 * The renderer owns the Drawing Standard's stroke discipline (every stroke is
 * non-scaling, round capped, round joined), the hatch patterns, the balloons
 * and leaders, the parts list and the title block.
 *
 * No drop shadows and no gradient fills are used anywhere: depth comes from
 * the face shading ramp and from stroke weight alone.
 */

export interface RenderOptions {
  /** Namespace for every `id` in the SVG (React `useId()` in the caller). */
  idPrefix: string;
  /** Status semantics; drives the accent colour only. */
  tone: Tone;
  /** Show balloons and leader lines. */
  annotated: boolean;
  /** Accessible name; when absent the SVG is decorative. */
  title?: string;
  /** Rendered size in pixels. Omit for a fluid plate. */
  size?: number;
  /** Class applied to the root `<svg>`. */
  className?: string;
}

/** The register: mono, uppercase, tracked (Drawing Standard 5.4). */
const MONO = "'JetBrains Mono','SF Mono',ui-monospace,Menlo,Consolas,monospace";

/** Stroke attributes every stroked element carries. */
const STROKE_ATTRS = {
  vectorEffect: 'non-scaling-stroke',
  strokeLinecap: 'round',
  strokeLinejoin: 'round',
} as const;

/** Depth key for annotation drawn over the drawing (centrelines, dimensions). */
const OVERLAY_DEPTH = 1e9;

/** Tone -> the one colour the tone is allowed to drive. */
function toneColour(tone: Tone): string {
  switch (tone) {
    case 'proved':
      return BOARD.accent;
    case 'warn':
      return BOARD.warn;
    case 'fail':
      return BOARD.fail;
    case 'neutral':
    default:
      return BOARD.edgeHi;
  }
}

/** Inline style values used by the root `<svg>`. */
type StyleValue = { [key: string]: string | number };

function h(
  tag: string,
  props: Record<string, string | number | boolean | StyleValue | undefined> | null,
  ...children: ReactNode[]
): ReactElement {
  return createElement(tag, props ?? {}, ...children);
}

function pathOf(points: Vec2[]): string {
  let d = '';
  points.forEach((p, i) => {
    d += `${i === 0 ? 'M' : 'L'}${p[0].toFixed(2)},${p[1].toFixed(2)}`;
  });
  return `${d}Z`;
}

function viewBoxSize(viewBox: string): { width: number; height: number } {
  const parts = viewBox.split(' ').map((n) => Number(n));
  const width = parts[2] ?? 0;
  const height = parts[3] ?? 0;
  return { width, height };
}

/**
 * Build the SVG element tree for a projected assembly.
 */
export function renderPlate(plate: RenderedPlate, options: RenderOptions): ReactElement {
  const { idPrefix, tone, annotated, title } = options;
  const cutColour = toneColour(tone);
  const { width: vw, height: vh } = viewBoxSize(plate.viewBox);

  // Hatch patterns: one per sectioned part, alternating 45 / 135 degrees so
  // neighbouring cuts never read as one.
  const patterns = new Map<number, ReturnType<typeof hatchPattern>>();
  for (const face of plate.faces) {
    if (face.cut && face.hatch >= 0 && !patterns.has(face.hatch)) {
      patterns.set(face.hatch, hatchPattern(idPrefix, face.hatch));
    }
  }
  const defs = h(
    'defs',
    null,
    Array.from(patterns.values()).map((p) =>
      h(
        'pattern',
        {
          id: p.id,
          width: p.size,
          height: p.size,
          patternUnits: 'userSpaceOnUse',
          patternTransform: `rotate(${p.angle})`,
        },
        h('path', {
          d: `M0,0 V${p.size}`,
          stroke: BOARD.edgeHi,
          strokeWidth: STROKE.hatch,
          opacity: 0.5,
          fill: 'none',
          ...STROKE_ATTRS,
        }),
      ),
    ),
  );

  // Faces and edges are interleaved by depth so the painter's order matches
  // the published engine: a far edge never paints over a near face.
  type Item = { depth: number; node: ReactElement };
  const items: Item[] = [];

  for (const face of plate.faces) {
    if (face.hidden) continue;
    const base = face.cut ? SHADE[4] : SHADE[face.shade] ?? SHADE[0];
    items.push({
      depth: face.depth,
      node: h('path', {
        d: pathOf(face.points),
        fill: base,
        stroke: base,
        strokeWidth: STROKE.hatch,
        ...STROKE_ATTRS,
      }),
    });
    if (face.cut && face.hatch >= 0) {
      const pattern = patterns.get(face.hatch);
      if (pattern) {
        items.push({
          depth: face.depth,
          node: h('path', {
            d: pathOf(face.points),
            fill: `url(#${pattern.id})`,
            stroke: 'none',
          }),
        });
      }
    }
  }

  for (const edge of plate.edges) {
    const stroke =
      edge.kind === 'cut' ? cutColour : edge.kind === 'hidden' ? BOARD.rib : BOARD.line;
    const strokeWidth =
      edge.kind === 'cut'
        ? STROKE.cutEdge
        : edge.kind === 'hidden'
          ? STROKE.hidden
          : STROKE.structure;
    items.push({
      depth: edge.depth,
      node: h('line', {
        x1: edge.a[0].toFixed(2),
        y1: edge.a[1].toFixed(2),
        x2: edge.b[0].toFixed(2),
        y2: edge.b[1].toFixed(2),
        stroke,
        strokeWidth,
        ...(edge.kind === 'hidden' ? { strokeDasharray: DASH.hidden } : {}),
        ...STROKE_ATTRS,
      }),
    });
  }

  // Centrelines: dash-dot through every axis of symmetry.
  for (const cl of plate.centerlines) {
    items.push({
      depth: OVERLAY_DEPTH,
      node: h('line', {
        x1: cl.a[0].toFixed(2),
        y1: cl.a[1].toFixed(2),
        x2: cl.b[0].toFixed(2),
        y2: cl.b[1].toFixed(2),
        stroke: BOARD.line,
        strokeWidth: STROKE.centerline,
        strokeDasharray: DASH.centerline,
        ...STROKE_ATTRS,
      }),
    });
  }

  // Dimension lines: extension lines, terminator ticks and a mono label.
  for (const d of plate.dimensions) {
    const dim = dimensionLine(d.a, d.b, d.label);
    for (const ext of dim.extensions) {
      items.push({
        depth: OVERLAY_DEPTH,
        node: h('line', {
          x1: ext.a[0].toFixed(2),
          y1: ext.a[1].toFixed(2),
          x2: ext.b[0].toFixed(2),
          y2: ext.b[1].toFixed(2),
          stroke: BOARD.rib,
          strokeWidth: STROKE.hidden,
          ...STROKE_ATTRS,
        }),
      });
    }
    items.push({
      depth: OVERLAY_DEPTH,
      node: h('line', {
        x1: dim.line.a[0].toFixed(2),
        y1: dim.line.a[1].toFixed(2),
        x2: dim.line.b[0].toFixed(2),
        y2: dim.line.b[1].toFixed(2),
        stroke: BOARD.ink,
        strokeWidth: STROKE.structure,
        ...STROKE_ATTRS,
      }),
    });
    for (const t of dim.ticks) {
      items.push({
        depth: OVERLAY_DEPTH,
        node: h('line', {
          x1: t.a[0].toFixed(2),
          y1: t.a[1].toFixed(2),
          x2: t.b[0].toFixed(2),
          y2: t.b[1].toFixed(2),
          stroke: BOARD.ink,
          strokeWidth: STROKE.structure,
          ...STROKE_ATTRS,
        }),
      });
    }
    items.push({
      depth: OVERLAY_DEPTH,
      node: h(
        'text',
        {
          x: dim.labelAt[0].toFixed(2),
          y: dim.labelAt[1].toFixed(2),
          fill: BOARD.ink,
          fontFamily: MONO,
          fontSize: 9,
          letterSpacing: '0.06em',
          textAnchor: 'middle',
        },
        dim.label,
      ),
    });
  }

  items.sort((a, b) => a.depth - b.depth);

  const children: ReactNode[] = [defs, ...items.map((i) => i.node)];

  // Balloons and leaders.
  if (annotated) {
    for (const leader of plate.leaders) {
      children.push(
        h('polyline', {
          points: leader.points.map((p) => `${p[0].toFixed(2)},${p[1].toFixed(2)}`).join(' '),
          fill: 'none',
          stroke: BOARD.line,
          strokeWidth: STROKE.leader,
          strokeDasharray: DASH.hidden,
          ...STROKE_ATTRS,
        }),
      );
      const start = leader.points[0];
      if (start) {
        children.push(
          h('circle', {
            cx: start[0].toFixed(2),
            cy: start[1].toFixed(2),
            r: 2,
            fill: BOARD.live,
          }),
        );
      }
    }
    for (const balloon of plate.balloons) {
      children.push(
        h(
          'g',
          null,
          h('circle', {
            cx: balloon.at[0].toFixed(2),
            cy: balloon.at[1].toFixed(2),
            r: BALLOON_R,
            fill: BOARD.plate,
            stroke: cutColour,
            strokeWidth: 1,
            ...STROKE_ATTRS,
          }),
          h(
            'text',
            {
              x: balloon.at[0].toFixed(2),
              y: (balloon.at[1] + 3.2).toFixed(2),
              fill: BOARD.inkHi,
              fontFamily: MONO,
              fontSize: 9,
              letterSpacing: '0.04em',
              textAnchor: 'middle',
            },
            String(balloon.number),
          ),
        ),
      );
    }
  }

  // Parts list and title block.
  const bill = plate.bill;
  const caption = plate.caption;
  if (bill.length > 0 || caption) {
    const bandTop = vh - Math.max(bill.length > 0 ? 26 + bill.length * 15 : 0, caption ? 46 : 0);
    const listWidth = bill.length > 0 ? Math.min(vw * 0.55, 320) : 0;
    children.push(
      h('line', {
        x1: 0,
        y1: bandTop.toFixed(2),
        x2: vw,
        y2: bandTop.toFixed(2),
        stroke: BOARD.line,
        strokeWidth: STROKE.structure,
        ...STROKE_ATTRS,
      }),
    );
    if (bill.length > 0) {
      children.push(
        h(
          'text',
          {
            x: 4,
            y: (bandTop + 15).toFixed(2),
            fill: BOARD.ink,
            fontFamily: MONO,
            fontSize: 9,
            letterSpacing: '0.09em',
          },
          'PARTS LIST',
        ),
      );
      bill.forEach((row, i) => {
        const y = bandTop + 30 + i * 15;
        children.push(
          h(
            'text',
            {
              x: 4,
              y: y.toFixed(2),
              fill: BOARD.inkHi,
              fontFamily: MONO,
              fontSize: 9,
              letterSpacing: '0.04em',
            },
            String(row.number),
          ),
          h(
            'text',
            {
              x: 26,
              y: y.toFixed(2),
              fill: BOARD.ink,
              fontFamily: MONO,
              fontSize: 9,
              letterSpacing: '0.06em',
            },
            row.label.toUpperCase(),
          ),
          h(
            'text',
            {
              x: listWidth - 8,
              y: y.toFixed(2),
              fill: BOARD.ink,
              fontFamily: MONO,
              fontSize: 9,
              letterSpacing: '0.06em',
              textAnchor: 'end',
            },
            `x${row.count}`,
          ),
          h('line', {
            x1: 4,
            y1: (y + 4).toFixed(2),
            x2: listWidth - 8,
            y2: (y + 4).toFixed(2),
            stroke: BOARD.rib,
            strokeWidth: STROKE.hatch,
            ...STROKE_ATTRS,
          }),
        );
      });
      children.push(
        h('line', {
          x1: listWidth,
          y1: (bandTop + 4).toFixed(2),
          x2: listWidth,
          y2: (vh - 4).toFixed(2),
          stroke: BOARD.line,
          strokeWidth: STROKE.structure,
          ...STROKE_ATTRS,
        }),
      );
    }
    if (caption) {
      const right = vw - 8;
      children.push(
        h(
          'text',
          {
            x: right,
            y: (bandTop + 16).toFixed(2),
            fill: BOARD.inkHi,
            fontFamily: MONO,
            fontSize: 10,
            letterSpacing: '0.09em',
            textAnchor: 'end',
          },
          caption.name.toUpperCase(),
        ),
        h(
          'text',
          {
            x: right,
            y: (bandTop + 30).toFixed(2),
            fill: BOARD.ink,
            fontFamily: MONO,
            fontSize: 9,
            letterSpacing: '0.08em',
            textAnchor: 'end',
          },
          `${caption.figure} · SCALE ${caption.scale}`,
        ),
        h(
          'text',
          {
            x: right,
            y: (bandTop + 43).toFixed(2),
            fill: BOARD.ink,
            fontFamily: MONO,
            fontSize: 9,
            letterSpacing: '0.08em',
            textAnchor: 'end',
          },
          `${plate.partCount} PARTS · EXPLODED VIEW`,
        ),
      );
    }
  }

  const rootProps: Record<string, string | number | boolean | StyleValue | undefined> = {
    xmlns: 'http://www.w3.org/2000/svg',
    viewBox: plate.viewBox,
    preserveAspectRatio: 'xMidYMid meet',
    className: options.className,
    ...(options.size !== undefined
      ? { width: options.size, height: options.size }
      : { width: '100%', style: { width: '100%', height: 'auto', display: 'block' } }),
    ...(title
      ? { role: 'img', 'aria-label': title }
      : { 'aria-hidden': true, focusable: false }),
  };

  return h(
    'svg',
    rootProps,
    ...(title ? [h('title', null, title)] : []),
    ...children,
  );
}
