import {
  createElement,
  useCallback,
  useEffect,
  useMemo,
  useRef,
  useState,
  type ChangeEvent,
  type KeyboardEvent,
  type ReactElement,
  type ReactNode,
} from 'react';
import { useReducedMotion } from '../../contract/motion';
import { DURATION, EASE } from '../../contract/tokens';

/**
 * Tier 3 — shared stepper machinery.
 *
 * A step is a caption, an optional clause reference, and a `render` function
 * that takes a progress value in `[0, 1]` and returns the diagram for that
 * step. The progress value is what lets a scene draw itself on: a step
 * entering at `t = 0` is a linework that has not been drawn yet, and a step
 * at `t = 1` is fully drawn.
 *
 * This file is `.ts`, not `.tsx`, because the plan names it `stepper.ts` and
 * the atelier build wires imports by that path. A `.ts` file cannot contain
 * JSX syntax, so the component is assembled with `createElement`.
 */

/** One step of a step-through scene. */
export interface Step {
  /** Caption explaining what this step demonstrates. */
  caption: string;
  /**
   * The spec clause or invariant this step corresponds to, e.g.
   * "ECMA-262 §11.8.6". Rendered verbatim under the caption.
   */
  clause?: string;
  /** Per-step rendered content. `t` runs from 0 (undrawn) to 1 (complete). */
  render: (t: number) => ReactNode;
}

export interface StepperProps {
  steps: Step[];
  className?: string;
  /** Label for the transport controls, for screen readers. */
  label?: string;
}

/** Alias so the markup below reads closer to JSX than to `createElement`. */
const h = createElement;

/**
 * Read the four control points out of a CSS `cubic-bezier(...)` token so the
 * motion grammar has exactly one source of truth. The easing used by the
 * step transition is the easing named in `EASE.standard`.
 */
function parseCubicBezier(token: string): readonly [number, number, number, number] {
  const matches = token.match(/-?\d*\.?\d+(?:e[-+]?\d+)?/gi);
  if (!matches || matches.length < 4) return [0, 0, 1, 1];
  return [Number(matches[0]) || 0, Number(matches[1]) || 0, Number(matches[2]) || 1, Number(matches[3]) || 1];
}

/** One axis of a cubic bezier, evaluated at `t`. */
function bezierAxis(a: number, b: number, t: number): number {
  const mt = 1 - t;
  return 3 * mt * mt * t * a + 3 * mt * t * t * b + t * t * t;
}

/**
 * Build an easing function from the four control points of a CSS cubic
 * bezier, by solving for the parameter that puts the curve at `x`.
 */
function cubicBezierEase(
  x1: number,
  y1: number,
  x2: number,
  y2: number,
): (x: number) => number {
  return (x: number): number => {
    if (x <= 0) return 0;
    if (x >= 1) return 1;
    let low = 0;
    let high = 1;
    let t = x;
    for (let iteration = 0; iteration < 24; iteration += 1) {
      const cx = bezierAxis(x1, x2, t);
      if (Math.abs(cx - x) < 1e-6) break;
      if (cx < x) low = t;
      else high = t;
      t = (low + high) / 2;
    }
    return bezierAxis(y1, y2, t);
  };
}

/**
 * The step transport: play, pause, step forward, step back, reset, a
 * scrubbable range input, a step counter and a caption area.
 *
 * Keyboard operation: the root is focusable, and the arrow keys move between
 * steps, `Home` resets, `End` jumps to the last step and `Space` toggles
 * playback. `data-step-index` and `data-step-count` are exposed on the root
 * so Playwright can read the position.
 *
 * When `useReducedMotion()` is true the transition between steps is skipped
 * entirely — a step appears already drawn (spec 7).
 */
export function Stepper(props: StepperProps): ReactElement {
  const { steps, className, label = 'Algorithm stepper' } = props;

  const reduced = useReducedMotion();
  const [index, setIndex] = useState(0);
  const [playing, setPlaying] = useState(false);
  const [progress, setProgress] = useState(1);

  const count = steps.length;
  const lastIndex = count > 0 ? count - 1 : 0;
  const current = steps[index];

  const ease = useMemo(() => {
    const [x1, y1, x2, y2] = parseCubicBezier(EASE.standard);
    return cubicBezierEase(x1, y1, x2, y2);
  }, []);

  // Keep the position inside the step list when the list changes.
  useEffect(() => {
    setIndex((previous) => Math.min(previous, lastIndex));
  }, [lastIndex]);

  // Draw the step on. The first step is shown already drawn so that a static
  // render (SSR, or reduced motion) is never a half-drawn diagram.
  const isFirstStep = useRef(true);
  useEffect(() => {
    if (reduced) {
      setProgress(1);
      return;
    }
    if (isFirstStep.current) {
      isFirstStep.current = false;
      setProgress(1);
      return;
    }
    if (typeof requestAnimationFrame !== 'function') {
      setProgress(1);
      return;
    }
    let frame = 0;
    const start = performance.now();
    const tick = (now: number): void => {
      const linear = Math.min(1, (now - start) / DURATION.d2);
      setProgress(ease(linear));
      if (linear < 1) frame = requestAnimationFrame(tick);
    };
    frame = requestAnimationFrame(tick);
    return () => cancelAnimationFrame(frame);
  }, [index, reduced, ease]);

  // Autoplay: hold each step for one scene beat, then advance.
  useEffect(() => {
    if (!playing || count < 2) return;
    if (index >= lastIndex) {
      setPlaying(false);
      return;
    }
    const timer = setTimeout(() => setIndex(index + 1), DURATION.d4);
    return () => clearTimeout(timer);
  }, [playing, index, count, lastIndex]);

  const stepForward = useCallback(() => {
    setPlaying(false);
    setIndex((previous) => Math.min(previous + 1, lastIndex));
  }, [lastIndex]);

  const stepBack = useCallback(() => {
    setPlaying(false);
    setIndex((previous) => Math.max(previous - 1, 0));
  }, []);

  const reset = useCallback(() => {
    setPlaying(false);
    setIndex(0);
  }, []);

  const togglePlay = useCallback(() => {
    if (playing) {
      setPlaying(false);
      return;
    }
    if (index >= lastIndex) setIndex(0);
    setPlaying(true);
  }, [playing, index, lastIndex]);

  const onScrub = useCallback(
    (event: ChangeEvent<HTMLInputElement>) => {
      setPlaying(false);
      const next = Number(event.currentTarget.value);
      if (!Number.isFinite(next)) return;
      setIndex(Math.min(Math.max(next, 0), lastIndex));
    },
    [lastIndex],
  );

  const onKeyDown = useCallback(
    (event: KeyboardEvent<HTMLDivElement>) => {
      // Inner controls handle their own keys; the range input already moves
      // between steps with the arrow keys.
      if (event.target !== event.currentTarget) return;
      switch (event.key) {
        case 'ArrowRight':
        case 'ArrowDown':
          event.preventDefault();
          stepForward();
          break;
        case 'ArrowLeft':
        case 'ArrowUp':
          event.preventDefault();
          stepBack();
          break;
        case 'Home':
          event.preventDefault();
          reset();
          break;
        case 'End':
          event.preventDefault();
          setPlaying(false);
          setIndex(lastIndex);
          break;
        case ' ':
        case 'Spacebar':
          event.preventDefault();
          togglePlay();
          break;
        default:
          break;
      }
    },
    [stepForward, stepBack, reset, togglePlay, lastIndex],
  );

  const rootClass = className === undefined ? 'stage-stepper' : `stage-stepper ${className}`;

  const transport = h(
    'div',
    { className: 'stage-stepper-transport' },
    h('button', {
      type: 'button',
      className: 'stage-stepper-button',
      'data-testid': 'stepper-reset',
      'aria-label': 'Reset',
      onClick: reset,
    }),
    h('button', {
      type: 'button',
      className: 'stage-stepper-button',
      'data-testid': 'stepper-prev',
      'aria-label': 'Step back',
      disabled: index <= 0,
      onClick: stepBack,
    }),
    h('button', {
      type: 'button',
      className: 'stage-stepper-button',
      'data-testid': 'stepper-play',
      'aria-label': playing ? 'Pause' : 'Play',
      'aria-pressed': playing,
      'data-playing': playing ? 'true' : 'false',
      onClick: togglePlay,
    }),
    h('button', {
      type: 'button',
      className: 'stage-stepper-button',
      'data-testid': 'stepper-next',
      'aria-label': 'Step forward',
      disabled: index >= lastIndex,
      onClick: stepForward,
    }),
    h('input', {
      type: 'range',
      className: 'stage-stepper-range',
      'data-testid': 'stepper-range',
      'aria-label': 'Timeline',
      min: 0,
      max: Math.max(0, lastIndex),
      step: 1,
      value: index,
      onChange: onScrub,
    }),
    h(
      'span',
      { className: 'stage-stepper-counter', 'data-testid': 'stepper-counter' },
      `${count === 0 ? 0 : index + 1} / ${count}`,
    ),
  );

  return h(
    'div',
    {
      className: rootClass,
      'data-testid': 'stepper',
      'data-step-index': index,
      'data-step-count': count,
      role: 'group',
      'aria-label': label,
      tabIndex: 0,
      onKeyDown,
    },
    h(
      'div',
      { className: 'stage-stepper-stage', 'data-testid': 'stepper-stage' },
      current ? current.render(progress) : null,
    ),
    h(
      'div',
      { className: 'stage-stepper-caption' },
      h(
        'p',
        { className: 'stage-stepper-caption-text', 'data-testid': 'stepper-caption' },
        current ? current.caption : '',
      ),
      current && current.clause
        ? h(
            'p',
            { className: 'stage-stepper-clause', 'data-testid': 'stepper-clause' },
            current.clause,
          )
        : null,
    ),
    transport,
  );
}
