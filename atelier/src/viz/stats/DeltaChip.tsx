import type { Tone } from '../../contract';
import { BOARD } from '../../contract/tokens';
import { cx, formatNumber } from './format';

export interface DeltaChipProps {
  /** Signed change. */
  delta: number;
  /** Unit suffix, e.g. `%`. */
  unit?: string;
  /**
   * The verdict this chip is asserting.
   *
   * A direction is not a verdict. "Verification time -44%" is good news and
   * must not be painted as a failure, while "trusted items +12" is a failure
   * even though the sign is positive. So the caller states the meaning, and
   * the chip colours itself from that.
   *
   * When omitted the chip falls back to reading the sign, which is right for
   * metrics where up is good and down is bad.
   */
  tone?: Tone;
  className?: string;
}

const TONE_COLOR: Record<Tone, string> = {
  proved: BOARD.accent,
  warn: BOARD.warn,
  fail: BOARD.fail,
  neutral: BOARD.ink,
};

/**
 * A signed change chip.
 *
 * The sign is always written out, so a zero never reads as a missing value.
 */
export function DeltaChip({ delta, unit, tone, className }: DeltaChipProps) {
  const resolved: Tone =
    tone ?? (delta > 0 ? 'proved' : delta < 0 ? 'fail' : 'neutral');
  const text = `${delta > 0 ? '+' : ''}${formatNumber(delta)}${unit ?? ''}`;

  return (
    <span
      className={cx('chDeltaChip', className)}
      data-tone={resolved}
      data-delta={delta}
      style={{ color: TONE_COLOR[resolved], fontVariantNumeric: 'tabular-nums' }}
    >
      {text}
    </span>
  );
}
