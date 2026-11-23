import { useEffect, useMemo, useRef, type CSSProperties, type ReactElement } from 'react';
import { useReducedMotion } from '../../contract/motion';
import { BOARD } from '../../contract/tokens';
import { createGcHeapScene, type GcHeapSceneHandle } from './threeScene';
import {
  findTriColorViolations,
  TRI_COLOR_FILL,
  TRI_COLOR_LABEL,
  type GcHeapEdge,
  type GcHeapObject,
} from './triColor';

export interface GcHeapSceneProps {
  /** Objects in the heap. `color` is the tri-color mark. */
  objects: GcHeapObject[];
  /** Pointers between objects. */
  edges: GcHeapEdge[];
  /**
   * Highlight a tri-color barrier violation.
   *
   * Pass `undefined` to let the scene detect the violation itself (a grey
   * object holding a black pointer). Pass `null` to declare the heap clean.
   */
  violation?: { from: string; to: string } | null;
  className?: string;
  /** Accessible name for the scene. */
  title?: string;
}

const DEFAULT_TITLE = 'Tri-color garbage collector heap';

/**
 * The viewport holds the canvas and the label layer, and the label layer is
 * absolutely positioned over the canvas, so the viewport has to be its
 * positioning context. The scene carries its own layout: it must read the
 * same wherever it is mounted, without a stylesheet it cannot see.
 */
const VIEWPORT_STYLE: CSSProperties = {
  position: 'relative',
  display: 'grid',
  alignItems: 'center',
};

/** The label layer: over the canvas, clipped, and never interactive. */
const LABEL_LAYER_STYLE: CSSProperties = {
  position: 'absolute',
  inset: 0,
  overflow: 'hidden',
  pointerEvents: 'none',
};

/**
 * The canvas fills the card it is given.
 *
 * `three` writes an inline width and height on the canvas at construction, so
 * the board's own size has to win. The scene measures the canvas before it
 * sizes the drawing buffer, so a canvas that fills the card gets a matching
 * buffer and stays crisp.
 */
const CANVAS_STYLE: CSSProperties = {
  display: 'block',
  width: '100% !important',
  height: 'auto !important',
};

/**
 * Tier 2 — the interactive tri-color GC heap.
 *
 * Raw `three` inside a React wrapper; `@react-three/fiber` is not used
 * because it pins React 18 while the atelier app is React 19 (spec 6.4).
 *
 * The scene is client-side only. The canvas element is rendered during SSR
 * but no WebGL context is created until the effect runs, so the component is
 * safe to `renderToStaticMarkup`.
 *
 * When `useReducedMotion()` is true the scene renders one static frame and
 * never starts an animation loop (spec 7).
 */
export function GcHeapScene(props: GcHeapSceneProps): ReactElement {
  const { objects, edges, violation, className, title = DEFAULT_TITLE } = props;

  const canvasRef = useRef<HTMLCanvasElement | null>(null);
  const labelLayerRef = useRef<HTMLDivElement | null>(null);
  const sceneRef = useRef<GcHeapSceneHandle | null>(null);
  const reduced = useReducedMotion();

  // The violation the scene draws. An explicit prop wins; otherwise the
  // scene detects the barrier break itself.
  const detected = useMemo(() => findTriColorViolations(objects, edges), [objects, edges]);
  const activeViolation = violation === undefined ? (detected[0] ?? null) : violation;
  const hasViolation = activeViolation !== null;

  // Create the WebGL scene once per motion mode. The `typeof window` guard
  // keeps this off the server.
  useEffect(() => {
    if (typeof window === 'undefined') return;
    const canvas = canvasRef.current;
    if (!canvas) return;

    let handle: GcHeapSceneHandle | null = null;
    try {
      handle = createGcHeapScene(canvas, {
        reducedMotion: reduced,
        labelLayer: labelLayerRef.current,
      });
    } catch {
      // No WebGL context available (headless runner, no GPU). The legend and
      // the status line still render; the heap itself does not.
      return;
    }
    sceneRef.current = handle;
    handle.update(objects, edges, activeViolation);

    return () => {
      sceneRef.current = null;
      handle.dispose();
    };
  }, [reduced]);

  // Push heap changes into the live scene.
  useEffect(() => {
    const handle = sceneRef.current;
    if (!handle) return;
    handle.update(objects, edges, activeViolation);
  }, [objects, edges, activeViolation]);

  return (
    <figure
      className={className === undefined ? 'stage-gc-heap' : `stage-gc-heap ${className}`}
      data-testid="gc-heap-scene"
      data-violation={hasViolation ? 'true' : 'false'}
      data-violation-from={activeViolation?.from}
      data-violation-to={activeViolation?.to}
      role="group"
      aria-label={title}
    >
      <div className="stage-gc-heap-viewport" style={VIEWPORT_STYLE}>
        <canvas ref={canvasRef} className="stage-gc-heap-canvas" style={CANVAS_STYLE} aria-hidden="true" />
        <div
          ref={labelLayerRef}
          className="stage-gc-heap-labels"
          style={LABEL_LAYER_STYLE}
          aria-hidden="true"
        />
      </div>
      <figcaption className="stage-gc-heap-caption">
        <ul className="stage-gc-heap-legend">
          {(['white', 'grey', 'black'] as const).map((color) => (
            <li key={color} className="stage-gc-heap-legend-item">
              <span
                className="stage-gc-heap-swatch"
                style={{ background: TRI_COLOR_FILL[color] }}
                aria-hidden="true"
              />
              <span className="stage-gc-heap-legend-label">{TRI_COLOR_LABEL[color]}</span>
            </li>
          ))}
        </ul>
        <p
          className="stage-gc-heap-status"
          style={{ color: hasViolation ? BOARD.fail : BOARD.ink }}
          data-testid="gc-heap-status"
        >
          {hasViolation && activeViolation
            ? `BARRIER VIOLATION — ${activeViolation.from} → ${activeViolation.to}`
            : 'BARRIER HELD — no grey object holds a black pointer'}
        </p>
      </figcaption>
    </figure>
  );
}
