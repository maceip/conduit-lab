import {
  createContext,
  useContext,
  useEffect,
  useMemo,
  useState,
  type ReactNode,
} from 'react';

interface MotionContextValue {
  reduced: boolean;
}

const MotionContext = createContext<MotionContextValue>({ reduced: false });

export function MotionProvider({ children }: { children: ReactNode }) {
  const [reduced, setReduced] = useState(false);

  useEffect(() => {
    const mq = window.matchMedia('(prefers-reduced-motion: reduce)');
    const apply = () => setReduced(mq.matches);
    apply();
    mq.addEventListener('change', apply);
    return () => mq.removeEventListener('change', apply);
  }, []);

  const value = useMemo(() => ({ reduced }), [reduced]);
  return <MotionContext.Provider value={value}>{children}</MotionContext.Provider>;
}

/** True when the visitor asked for reduced motion. Components must render
 *  the FINAL state immediately when this is true — never an intermediate frame. */
export function useReducedMotion(): boolean {
  return useContext(MotionContext).reduced;
}
