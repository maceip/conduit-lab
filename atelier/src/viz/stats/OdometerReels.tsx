import { BOARD, DURATION, EASE } from '../../contract/tokens';
import { cx } from './format';
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
      style={{ display: 'inline-flex', gap: 1, color: BOARD.inkHi }}
    >
      {padded.split('').map((digit, index) => (
        <span
          key={index}
          data-reel={index}
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
