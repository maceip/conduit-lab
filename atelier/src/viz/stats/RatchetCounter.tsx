import { BOARD, DURATION } from '../../contract/tokens';
import { cx, formatNumber } from './format';
import { useCountUp } from './countUp';

export interface RatchetCounterProps {
  /** The current trusted-item count. */
  trusted: number;
  /** The count at the previous release, when one is known. */
  previous?: number;
  label?: string;
  className?: string;
  /** Test hook, written to `data-testid` on the root element. */
  testId?: string;
}

/** How the figure may move. There is deliberately no `up`. */
export type RatchetMotion = 'down' | 'hold' | 'violation';

export interface RatchetPlan {
  readonly motion: RatchetMotion;
  /**
   * The value the animation starts from.
   *
   * This is never greater than `trusted`, which is what guarantees the
   * counter can only ever roll downwards.
   */
  readonly from: number;
}

/**
 * Decides how the ratchet figure may move.
 *
 * Exported so the rule can be asserted directly rather than trusted: for any
 * pair of counts the start value is at or below the target, so no input can
 * ever produce an upward animation.
 */
export function planRatchet(trusted: number, previous?: number): RatchetPlan {
  if (previous === undefined) return { motion: 'hold', from: trusted };
  if (trusted > previous) return { motion: 'violation', from: trusted };
  if (trusted < previous) return { motion: 'down', from: previous };
  return { motion: 'hold', from: trusted };
}

/**
 * The trusted-item ratchet.
 *
 * The ratchet's whole meaning is that the trusted-item count never rises
 * between releases, so this component has one hard rule: it NEVER animates
 * upward.
 *
 * - the count fell  -> the figure rolls DOWN to the new value
 * - the count held  -> the figure holds still
 * - the count rose  -> VIOLATION. The figure does not roll up. It holds
 *                      static in the failure colour with the violation marked.
 *
 * An upward animation would be a lie about the invariant this component
 * exists to show.
 */
export function RatchetCounter({ trusted, previous, label, className, testId }: RatchetCounterProps) {
  const known = previous !== undefined;
  const plan = planRatchet(trusted, previous);
  const violation = plan.motion === 'violation';
  const falling = plan.motion === 'down';

  // Only a FALL is ever animated, and only downwards.
  const { display, settled } = useCountUp(trusted, {
    from: plan.from,
    animate: falling,
    duration: DURATION.d3,
  });

  const color = violation ? BOARD.fail : BOARD.accent;
  const text = formatNumber(display);

  return (
    <div
      className={cx('chRatchetCounter', className)}
      data-trusted={trusted}
      data-previous={known ? previous : ''}
      data-violation={violation ? 'true' : 'false'}
      data-settled={settled ? 'true' : 'false'}
      data-testid={testId}
      style={{ display: 'grid', gap: 4 }}
    >
      <span
        style={{
          color,
          fontSize: 32,
          lineHeight: 1.05,
          fontVariantNumeric: 'tabular-nums',
        }}
      >
        {text}
      </span>
      <span
        style={{
          color: BOARD.ink,
          fontSize: 9,
          letterSpacing: '0.12em',
          textTransform: 'uppercase',
        }}
      >
        {label ?? 'trusted items'}
      </span>
      {violation ? (
        <span
          data-violation-mark="true"
          style={{
            color: BOARD.fail,
            fontSize: 9,
            letterSpacing: '0.12em',
            textTransform: 'uppercase',
          }}
        >
          ratchet broken — count rose
        </span>
      ) : null}
    </div>
  );
}
