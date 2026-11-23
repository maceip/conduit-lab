import { BOARD, DURATION } from '../../contract/tokens';
import { cx, formatNumber } from './format';
import { useCountUp } from './countUp';

export interface CountFigureProps {
  /** The figure to count up to. */
  value: number;
  label?: string;
  /** Unit written after the figure, e.g. `ms`. */
  suffix?: string;
  /** Travel time in milliseconds. Defaults to the shared feature duration. */
  duration?: number;
  className?: string;
}

/**
 * A large figure that counts up to its value.
 *
 * The count runs on a decelerating curve and lands on the exact target — the
 * final frame is the target itself, not a rounded approximation of it. A
 * visitor who asked for reduced motion gets the final figure immediately.
 */
export function CountFigure({ value, label, suffix, duration = DURATION.d3, className }: CountFigureProps) {
  const { display, settled } = useCountUp(value, { duration, from: 0 });
  const text = `${formatNumber(display)}${suffix ?? ''}`;

  return (
    <div
      className={cx('chCountFigure', className)}
      data-settled={settled ? 'true' : 'false'}
      data-target={value}
      style={{ display: 'grid', gap: 4 }}
    >
      <span
        style={{
          color: BOARD.inkHi,
          fontSize: 32,
          lineHeight: 1.05,
          fontVariantNumeric: 'tabular-nums',
        }}
      >
        {text}
      </span>
      {label ? (
        <span
          style={{
            color: BOARD.ink,
            fontSize: 9,
            letterSpacing: '0.12em',
            textTransform: 'uppercase',
          }}
        >
          {label}
        </span>
      ) : null}
    </div>
  );
}
