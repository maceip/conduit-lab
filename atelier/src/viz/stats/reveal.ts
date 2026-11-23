import { useEffect, useState } from 'react';
import { DURATION } from '../../contract/tokens';
import { useReducedMotion } from '../../contract/motion';

/**
 * Staggered reveal.
 *
 * Returns a tuple of booleans, one per step. Step `n` becomes true
 * `stagger * n` milliseconds after mount, so a component can reveal its
 * parts in order — value, then label, then hint.
 *
 * Under reduced motion every step is true immediately and no timer is
 * scheduled, so the component renders its final state with zero animation.
 */
export function useReveal(steps: number, stagger = DURATION.d1): boolean[] {
  const reduced = useReducedMotion();
  const [revealed, setRevealed] = useState<boolean[]>(() =>
    Array.from({ length: Math.max(0, steps) }, () => reduced),
  );

  useEffect(() => {
    if (reduced) {
      setRevealed(Array.from({ length: Math.max(0, steps) }, () => true));
      return undefined;
    }

    const timers = Array.from({ length: Math.max(0, steps) }, (_, index) =>
      window.setTimeout(() => {
        setRevealed((current) => {
          if (current[index]) return current;
          const next = [...current];
          next[index] = true;
          return next;
        });
      }, stagger * index),
    );

    return () => {
      for (const timer of timers) window.clearTimeout(timer);
    };
  }, [steps, stagger, reduced]);

  return revealed;
}
