import { createElement, type ReactElement, type ReactNode } from 'react';
import type { Palette, Tone, Vec2 } from '../../contract';
import { BOARD, CUT_FACE, DASH, PALETTES, SHADE_BODY, STROKE } from '../../contract/tokens';
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

/**
 * Stroke attributes every stroked element carries. `stroke-linecap` and
 * `stroke-linejoin` are inherited, so they are set once on the drawing group
 * rather than repeated on every path; `vector-effect` is not inherited and
 * stays per element.
 */
const STROKE_ATTRS = {
  vectorEffect: 'non-scaling-stroke',
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

/**
 * The cut edge bounds a bright machined face, so it is drawn in a mid ink
 * rather than the light edge colour — a light line would vanish into the cut
 * it is supposed to define. A status tone still wins where one is set.
 */
function cutEdgeColour(tone: Tone): string {
  return tone === 'neutral' ? BOARD.ink : toneColour(tone);
}

/**
 * The colour of a face: the part's own palette ramp, except for a cut face,
 * which is a bright machined surface in the drawing convention.
 */
function faceColour(palette: Palette, shade: number, cut: boolean): string {
  if (cut) return CUT_FACE;
  const ramp: readonly string[] = PALETTES[palette];
  return ramp[shade] ?? ramp[ramp.length - 1] ?? SHADE_BODY[0];
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
    d += `${i === 0 ? 'M' : 'L'}${p[0].toFixed(1)},${p[1].toFixed(1)}`;
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
          key: `pattern-${p.id}`,
          id: p.id,
          width: p.size,
          height: p.size,
          patternUnits: 'userSpaceOnUse',
          patternTransform: `rotate(${p.angle})`,
        },
        h('path', {
          d: `M0,0 V${p.size}`,
          // The hatch lies on a bright cut face, so it is inked rather than
          // highlighted; a light line would disappear into the cut.
          stroke: BOARD.ink,
          strokeWidth: STROKE.hatch,
          opacity: 0.55,
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
    const base = faceColour(face.palette, face.shade, face.cut);
    items.push({
      depth: face.depth,
      node: h('path', {
        key: `face-${face.partId}-${items.length}`,
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
            key: `hatch-${face.partId}-${items.length}`,
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
      edge.kind === 'cut'
        ? cutEdgeColour(tone)
        : edge.kind === 'hidden'
          ? BOARD.rib
          : BOARD.line;
    const strokeWidth =
      edge.kind === 'cut'
        ? STROKE.cutEdge
        : edge.kind === 'hidden'
          ? STROKE.hidden
          : STROKE.structure;
    items.push({
      depth: edge.depth,
      node: h('line', {
        key: `edge-${items.length}`,
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
        key: `centreline-${plate.centerlines.indexOf(cl)}`,
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
          key: `dim-ext-${plate.dimensions.indexOf(d)}-${ext.a[0]}`,
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
        key: `dim-line-${plate.dimensions.indexOf(d)}`,
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
          key: `dim-tick-${plate.dimensions.indexOf(d)}-${t.a[0]}`,
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
          key: `dim-label-${plate.dimensions.indexOf(d)}`,
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

  // Every stroked element inside the drawing group inherits the round cap and
  // join; `vector-effect` stays on the elements themselves.
  const children: ReactNode[] = [defs];
  const drawing: ReactNode[] = items.map((i) => i.node);

  // Balloons and leaders.
  if (annotated) {
    for (const leader of plate.leaders) {
      drawing.push(
        h('polyline', {
          key: `leader-${leader.partId}`,
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
        drawing.push(
          h('circle', {
            key: `leader-dot-${leader.partId}`,
            cx: start[0].toFixed(2),
            cy: start[1].toFixed(2),
            r: 2,
            fill: BOARD.live,
          }),
        );
      }
    }
    for (const balloon of plate.balloons) {
      drawing.push(
        h(
          'g',
          { key: `balloon-${balloon.partId}` },
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
              key: `balloon-num-${balloon.partId}`,
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
    const captionHeight = caption ? 46 + (caption.legend ? caption.legend.length * 17 + 6 : 0) : 0;
    const bandTop = vh - Math.max(bill.length > 0 ? 26 + bill.length * 15 : 0, captionHeight);
    const listWidth = bill.length > 0 ? Math.min(vw * 0.55, 320) : 0;
    drawing.push(
      h('line', {
        key: 'band-rule',
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
      drawing.push(
        h(
          'text',
          {
            key: 'bill-header',
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
        drawing.push(
          h(
            'g',
            { key: `bill-row-${row.number}` },
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
          ),
        );
      });
      drawing.push(
        h('line', {
          key: 'bill-rule',
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
      drawing.push(
        h(
          'text',
          {
            key: 'caption-name',
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
            key: 'caption-figure',
            x: right,
            y: (bandTop + 30).toFixed(2),
            fill: BOARD.ink,
            fontFamily: MONO,
            fontSize: 9,
            letterSpacing: '0.08em',
            textAnchor: 'end',
          },
          `${caption.figure} · SCALE ${caption.scale} · ${plate.partCount} PARTS`,
        ),
      );
      if (caption.note) {
        drawing.push(
          h(
            'text',
            {
              key: 'caption-note',
              x: right,
              y: (bandTop + 43).toFixed(2),
              fill: BOARD.ink,
              fontFamily: MONO,
              fontSize: 9,
              letterSpacing: '0.08em',
              textAnchor: 'end',
            },
            caption.note.toUpperCase(),
          ),
        );
      }
      // Legend: the swatch states what the hatching means on this plate.
      const legend = caption.legend ?? [];
      const firstPattern = patterns.values().next().value;
      legend.forEach((entry, i) => {
        const y = bandTop + 46 + (caption.note ? 16 : 0) + i * 17;
        const swatchX = right - 206;
        drawing.push(
          h(
            'g',
            { key: `legend-swatch-${i}` },
            // A hatched swatch is a cut face: bright machined ground with the
            // section hatch laid over it, exactly as it appears in the drawing.
            h('rect', {
              x: swatchX,
              y: y - 11,
              width: 14,
              height: 14,
              fill: entry.hatched ? CUT_FACE : SHADE_BODY[2],
              stroke: BOARD.line,
              strokeWidth: STROKE.structure,
              ...STROKE_ATTRS,
            }),
            ...(entry.hatched && firstPattern
              ? [
                  h('rect', {
                    key: `legend-hatch-${i}`,
                    x: swatchX,
                    y: y - 11,
                    width: 14,
                    height: 14,
                    fill: `url(#${firstPattern.id})`,
                    stroke: 'none',
                  }),
                ]
              : []),
          ),
          h(
            'text',
            {
              key: `legend-label-${i}`,
              x: swatchX + 20,
              y: y,
              fill: BOARD.ink,
              fontFamily: MONO,
              fontSize: 9,
              letterSpacing: '0.08em',
            },
            entry.label.toUpperCase(),
          ),
        );
      });
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

  children.push(
    h(
      'g',
      { key: 'drawing', strokeLinecap: 'round', strokeLinejoin: 'round' },
      ...drawing,
    ),
  );

  return h(
    'svg',
    rootProps,
    ...(title ? [h('title', { key: 'svg-title' }, title)] : []),
    ...children,
  );
}
