import { BOARD } from '../../contract/tokens';
import { cx, formatNumber } from './format';

export interface RadialGaugeProps {
  /** Current value. */
  value: number;
  /** Full-scale value. A non-positive maximum yields an empty gauge. */
  max: number;
  label?: string;
  className?: string;
}

const RADIUS = 34;
const CIRCUMFERENCE = 2 * Math.PI * RADIUS;

/**
 * A radial gauge whose sweep is driven by `value / max`.
 *
 * A non-positive `max` would make the ratio meaningless, so the gauge stays
 * empty rather than emitting `NaN` into the path.
 */
export function RadialGauge({ value, max, label, className }: RadialGaugeProps) {
  const ratio = max > 0 ? Math.min(1, Math.max(0, value / max)) : 0;
  const sweep = CIRCUMFERENCE * (1 - ratio);

  return (
    <figure
      className={cx('chRadialGauge', className)}
      data-ratio={ratio.toFixed(4)}
      style={{ margin: 0, display: 'inline-flex', flexDirection: 'column', alignItems: 'center', gap: 6 }}
    >
      <svg width="88" height="88" viewBox="0 0 88 88" role="img" aria-label={label ?? 'gauge'}>
        <circle
          cx="44"
          cy="44"
          r={RADIUS}
          fill="none"
          stroke={BOARD.rib}
          strokeWidth="6"
        />
        <circle
          cx="44"
          cy="44"
          r={RADIUS}
          fill="none"
          stroke={BOARD.accent}
          strokeWidth="6"
          strokeLinecap="round"
          strokeDasharray={CIRCUMFERENCE}
          strokeDashoffset={sweep}
          transform="rotate(-90 44 44)"
        />
        <text
          x="44"
          y="49"
          textAnchor="middle"
          fill={BOARD.inkHi}
          fontFamily="inherit"
          fontSize="16"
          style={{ fontVariantNumeric: 'tabular-nums' }}
        >
          {formatNumber(value)}
        </text>
      </svg>
      {label ? (
        <figcaption
          style={{
            color: BOARD.ink,
            fontSize: 9,
            letterSpacing: '0.09em',
            textTransform: 'uppercase',
          }}
        >
          {label}
        </figcaption>
      ) : null}
    </figure>
  );
}
