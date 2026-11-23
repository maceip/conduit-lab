import type { Tone } from '../../contract';
import { BOARD, DURATION, EASE } from '../../contract/tokens';
import { cx } from './format';
import { useReveal } from './reveal';

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
 *
 * The tile reveals in order — value, then label, then hint — one step apart.
 * Under reduced motion the whole tile is present at once.
 */
export function StatTile({ value, label, hint, tone = 'neutral', className }: StatTileProps) {
  const steps = hint ? 3 : 2;
  const revealed = useReveal(steps);
  const valueIn = revealed[0];
  const labelIn = revealed[1];
  const hintIn = revealed[2];

  const fade = (shown: boolean) => ({
    opacity: shown ? 1 : 0,
    transform: shown ? 'translateY(0)' : 'translateY(4px)',
    transition: `opacity ${DURATION.d2}ms ${EASE.standard}, transform ${DURATION.d2}ms ${EASE.standard}`,
  });

  return (
    <div
      className={cx('chStatTile', className)}
      data-tone={tone}
      data-revealed={revealed.every((step) => step) ? 'true' : 'false'}
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
          ...fade(valueIn === true),
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
          ...fade(labelIn === true),
        }}
      >
        {label}
      </span>
      {hint ? (
        <span style={fade(hintIn === true)}>
          <span style={{ color: BOARD.ink, fontSize: 10, opacity: 0.75 }}>{hint}</span>
        </span>
      ) : null}
    </div>
  );
}
