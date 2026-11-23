import { useEffect, useLayoutEffect, useRef, useState } from 'react';
import { DURATION, EASE } from '../../contract/tokens';
import { useReducedMotion } from '../../contract/motion';

/**
 * `useLayoutEffect` on the client, `useEffect` on the server.
 *
 * The count-up must be reset to its starting value BEFORE the browser paints,
 * or the visitor sees the final figure flash for one frame before it rolls.
 * On the server `useLayoutEffect` warns and does nothing, so the isomorphic
 * form keeps server rendering silent.
 */
const useIsomorphicLayoutEffect =
  typeof window === 'undefined' ? useEffect : useLayoutEffect;

/**
 * Evaluates a cubic-bezier timing function the way CSS does.
 *
 * The curve is read from the shared motion tokens, so the components and the
 * stylesheet agree on one easing vocabulary.
 */
export function cubicBezier(x1: number, y1: number, x2: number, y2: number): (x: number) => number {
  const ax = 3 * x1 - 3 * x2 + 1;
  const bx = 3 * x2 - 6 * x1;
  const cx = 3 * x1;
  const ay = 3 * y1 - 3 * y2 + 1;
  const by = 3 * y2 - 6 * y1;
  const cy = 3 * y1;

  const sampleX = (t: number) => ((ax * t + bx) * t + cx) * t;
  const sampleY = (t: number) => ((ay * t + by) * t + cy) * t;
  const slopeX = (t: number) => (3 * ax * t + 2 * bx) * t + cx;

  return (x: number): number => {
    if (x <= 0) return 0;
    if (x >= 1) return 1;

    // Newton-Raphson first; it converges in a handful of steps.
    let t = x;
    for (let i = 0; i < 8; i += 1) {
      const dx = sampleX(t) - x;
      if (Math.abs(dx) < 1e-6) return sampleY(t);
      const d = slopeX(t);
      if (Math.abs(d) < 1e-6) break;
      t -= dx / d;
    }

    // Bisection fallback for curves where the slope vanishes.
    let lo = 0;
    let hi = 1;
    t = x;
    for (let i = 0; i < 24; i += 1) {
      const v = sampleX(t);
      if (Math.abs(v - x) < 1e-6) break;
      if (v > x) hi = t;
      else lo = t;
      t = (lo + hi) / 2;
    }
    return sampleY(t);
  };
}

const CURVE = EASE.feature.match(/[\d.]+/g);
const FEATURE = cubicBezier(
  Number(CURVE?.[0] ?? 0.16),
  Number(CURVE?.[1] ?? 0.84),
  Number(CURVE?.[2] ?? 0.44),
  Number(CURVE?.[3] ?? 1),
);

export interface CountUpOptions {
  /** Travel time in milliseconds. */
  duration?: number;
  /** Starting value. Defaults to the target, which means no travel at all. */
  from?: number;
  /** Set false to hold the value still. */
  animate?: boolean;
}

export interface CountUpState {
  /** The value to display right now. */
  display: number;
  /** True once the displayed value is the final value. */
  settled: boolean;
}

/**
 * Animates a number towards `target`.
 *
 * The first render — server render and the first client render alike — shows
 * the FINAL value, so server markup and client hydration agree and a visitor
 * with reduced motion never sees a rolling number. The animation, when it
 * happens at all, starts from `from` in a layout effect before the first
 * paint.
 */
export function useCountUp(target: number, options: CountUpOptions = {}): CountUpState {
  const { duration = DURATION.d3, from = target, animate = true } = options;
  const reduced = useReducedMotion();
  const shouldAnimate = animate && !reduced && duration > 0 && from !== target;

  const [display, setDisplay] = useState(target);
  const [settled, setSettled] = useState(true);
  const frame = useRef<number | null>(null);

  useIsomorphicLayoutEffect(() => {
    if (!shouldAnimate) {
      setDisplay(target);
      setSettled(true);
      return undefined;
    }

    const startedAt = performance.now();
    const tick = (now: number) => {
      const t = Math.min(1, (now - startedAt) / duration);
      if (t >= 1) {
        // The final frame lands on the exact target, never an approximation.
        setDisplay(target);
        setSettled(true);
        frame.current = null;
        return;
      }
      setDisplay(from + (target - from) * FEATURE(t));
      frame.current = requestAnimationFrame(tick);
    };

    setDisplay(from);
    setSettled(false);
    frame.current = requestAnimationFrame(tick);

    return () => {
      if (frame.current !== null) cancelAnimationFrame(frame.current);
    };
  }, [target, from, duration, shouldAnimate]);

  return { display, settled };
}
