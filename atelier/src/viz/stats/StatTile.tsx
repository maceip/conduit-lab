import type { Tone } from '../../contract';
import { BOARD } from '../../contract/tokens';
import { cx } from './format';

export interface StatTileProps {
  /** The figure. A caller with no recorded value passes `not recorded`. */
  value: string;
  label: string;
  hint?: string;
  tone?: Tone;
  className?: string;
}

const TONE_COLOR: Record<Tone, string> = {
  proved: BOARD.accent,
  warn: BOARD.warn,
  fail: BOARD.fail,
  neutral: BOARD.inkHi,
};

/**
 * A labelled figure.
 *
 * The value is a string, not a number, because a field the reports do not
 * carry must read `not recorded` rather than a zero that looks measured.
 */
export function StatTile({ value, label, hint, tone = 'neutral', className }: StatTileProps) {
  return (
    <div
      className={cx('chStatTile', className)}
      data-tone={tone}
      style={{
        display: 'grid',
        gap: 4,
        padding: '12px 14px',
        border: `1px solid ${BOARD.rib}`,
        borderRadius: 10,
        background: BOARD.plate,
      }}
    >
      <span
        style={{
          color: TONE_COLOR[tone],
          fontSize: 24,
          lineHeight: 1.1,
          fontVariantNumeric: 'tabular-nums',
        }}
      >
        {value}
      </span>
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
      {hint ? (
        <span style={{ color: BOARD.ink, fontSize: 10, opacity: 0.75 }}>{hint}</span>
      ) : null}
    </div>
  );
}
