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
 *
 * ACCESSIBILITY: the figure states a measured number, so assistive technology
 * must hear the TRUE value, not a mid-roll digit. The root carries the final
 * figure as its accessible name and the rolling digits are hidden from the
 * accessibility tree, so a screen reader never announces a number that is not
 * the real one.
 */
export function CountFigure({ value, label, suffix, duration = DURATION.d3, className }: CountFigureProps) {
  const { display, settled } = useCountUp(value, { duration, from: 0 });

  const finalText = `${formatNumber(value)}${suffix ?? ''}`;
  const rollingText = `${formatNumber(display)}${suffix ?? ''}`;

  return (
    <div
      className={cx('chCountFigure', className)}
      data-settled={settled ? 'true' : 'false'}
      data-target={value}
      aria-label={label ? `${finalText} ${label}` : finalText}
      style={{ display: 'grid', gap: 4 }}
    >
      <span
        aria-hidden="true"
        style={{
          color: BOARD.inkHi,
          fontSize: 32,
          lineHeight: 1.05,
          fontVariantNumeric: 'tabular-nums',
        }}
      >
        {rollingText}
      </span>
      {label ? (
        <span
          aria-hidden="true"
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
