import { BOARD } from '../../contract/tokens';
import { cx, formatNumber } from './format';

export interface DeltaChipProps {
  /** Signed change. Positive is an improvement, negative a regression. */
  delta: number;
  /** Unit suffix, e.g. `%`. */
  unit?: string;
  className?: string;
}

/**
 * A signed change chip.
 *
 * Positive reads in the verified accent, negative in the failure colour, zero
 * in neutral ink. The sign is always written out, so a zero never reads as a
 * missing value.
 */
export function DeltaChip({ delta, unit, className }: DeltaChipProps) {
  const color = delta > 0 ? BOARD.accent : delta < 0 ? BOARD.fail : BOARD.ink;
  const tone = delta > 0 ? 'proved' : delta < 0 ? 'fail' : 'neutral';
  const text = `${delta > 0 ? '+' : ''}${formatNumber(delta)}${unit ?? ''}`;

  return (
    <span
      className={cx('chDeltaChip', className)}
      data-tone={tone}
      data-delta={delta}
      style={{ color, fontVariantNumeric: 'tabular-nums' }}
    >
      {text}
    </span>
  );
}
