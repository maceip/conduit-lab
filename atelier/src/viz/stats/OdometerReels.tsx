import { BOARD, DURATION, EASE } from '../../contract/tokens';
import { cx, formatNumber } from './format';
import { useCountUp } from './countUp';

export interface OdometerReelsProps {
  /** The number to show. */
  value: number;
  /** Number of reels. Defaults to the width of the value. */
  digits?: number;
  className?: string;
}

const REEL_HEIGHT = 14;
const DIGITS = ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9'];

/**
 * A column of digits that rolls like an odometer.
 *
 * Every reel starts and stops at the same moment — no per-digit stagger — and
 * each reel carries the full 0-9 strip so a roll can pass through the digits
 * between two values.
 *
 * ACCESSIBILITY: the reel strip is ten digits of geometry, not prose, so it
 * is hidden from the accessibility tree. The root carries the final figure as
 * its accessible name, so a screen reader hears "4,102" rather than thirty-six
 * characters of digit strip.
 */
export function OdometerReels({ value, digits, className }: OdometerReelsProps) {
  const { display, settled } = useCountUp(value, { from: 0 });

  const width = digits ?? Math.max(1, String(Math.trunc(Math.abs(value))).length);
  const padded = Math.trunc(Math.abs(display)).toString().padStart(width, '0');

  return (
    <div
      className={cx('chOdometerReels', className)}
      data-settled={settled ? 'true' : 'false'}
      data-digits={width}
      aria-label={formatNumber(value)}
      role="img"
      style={{ display: 'inline-flex', gap: 1, color: BOARD.inkHi }}
    >
      {padded.split('').map((digit, index) => (
        <span
          key={index}
          data-reel={index}
          aria-hidden="true"
          style={{
            display: 'block',
            height: REEL_HEIGHT,
            overflow: 'hidden',
            lineHeight: `${REEL_HEIGHT}px`,
            fontSize: 12,
            fontVariantNumeric: 'tabular-nums',
          }}
        >
          <span
            style={{
              display: 'block',
              // The reel is a one-character window onto the digit strip.
              // The strip is a single run of text, so it must be broken
              // per character and the window clipped to one character wide.
              lineHeight: '1em',
              width: '1ch',
              wordBreak: 'break-all',
              transform: `translateY(-${digit}em)`,
              transition: `transform ${DURATION.d2}ms ${EASE.standard}`,
            }}
          >
            {DIGITS.join('')}
          </span>
        </span>
      ))}
    </div>
  );
}
