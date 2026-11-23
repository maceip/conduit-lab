import { BOARD, DURATION, EASE } from '../../contract/tokens';
import { cx, formatNumber } from './format';
import { useReveal } from './reveal';

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
 *
 * The arc sweeps open from empty. Under reduced motion it is drawn at its
 * final sweep immediately.
 */
export function RadialGauge({ value, max, label, className }: RadialGaugeProps) {
  const ratio = max > 0 ? Math.min(1, Math.max(0, value / max)) : 0;
  const sweep = CIRCUMFERENCE * (1 - ratio);
  const [swept] = useReveal(1);

  const shown = swept === true;

  return (
    <figure
      className={cx('chRadialGauge', className)}
      data-ratio={ratio.toFixed(4)}
      data-revealed={swept === true ? 'true' : 'false'}
      style={{ margin: 0, display: 'inline-flex', flexDirection: 'column', alignItems: 'center', gap: 6 }}
    >
      <svg
        width="88"
        height="88"
        viewBox="0 0 88 88"
        role="img"
        aria-label={label ? `${formatNumber(value)} ${label}` : `${formatNumber(value)} of ${formatNumber(max)}`}
      >
        <circle cx="44" cy="44" r={RADIUS} fill="none" stroke={BOARD.rib} strokeWidth="6" />
        <circle
          cx="44"
          cy="44"
          r={RADIUS}
          fill="none"
          stroke={BOARD.accent}
          strokeWidth="6"
          strokeLinecap="round"
          strokeDasharray={CIRCUMFERENCE}
          strokeDashoffset={shown ? sweep : CIRCUMFERENCE}
          transform="rotate(-90 44 44)"
          style={{ transition: `stroke-dashoffset ${DURATION.d3}ms ${EASE.standard}` }}
        />
        <text
          x="44"
          y="49"
          textAnchor="middle"
          fill={BOARD.inkHi}
          fontFamily="inherit"
          fontSize="16"
          aria-hidden="true"
          style={{ fontVariantNumeric: 'tabular-nums' }}
        >
          {formatNumber(value)}
        </text>
      </svg>
      {label ? (
        <figcaption
          aria-hidden="true"
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
