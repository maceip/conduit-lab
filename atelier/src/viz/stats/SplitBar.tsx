import type { Tone } from '../../contract';
import { BOARD } from '../../contract/tokens';
import { cx, formatNumber } from './format';

export interface SplitBarSegment {
  id: string;
  label: string;
  value: number;
  tone?: Tone;
}

export interface SplitBarProps {
  segments: SplitBarSegment[];
  className?: string;
}

const TONE_COLOR: Record<Tone, string> = {
  proved: BOARD.accent,
  warn: BOARD.warn,
  fail: BOARD.fail,
  neutral: BOARD.line,
};

/**
 * A stacked bar that splits a total into its parts.
 *
 * Segment widths are the segment's share of the total. Negative values are
 * clamped to zero rather than pushing the bar past its track, and the total
 * is shown beside the bar so the split can be read without hovering.
 */
export function SplitBar({ segments, className }: SplitBarProps) {
  const total = segments.reduce((sum, segment) => sum + Math.max(0, segment.value), 0);

  return (
    <div className={cx('chSplitBar', className)} data-total={total}>
      <div
        style={{
          display: 'flex',
          height: 10,
          borderRadius: 5,
          overflow: 'hidden',
          background: BOARD.rib,
        }}
      >
        {segments.map((segment) => {
          const share = total > 0 ? Math.max(0, segment.value) / total : 0;
          return (
            <div
              key={segment.id}
              data-segment={segment.id}
              style={{
                width: `${(share * 100).toFixed(4)}%`,
                background: TONE_COLOR[segment.tone ?? 'neutral'],
              }}
            />
          );
        })}
      </div>
      <ul
        style={{
          listStyle: 'none',
          margin: '10px 0 0',
          padding: 0,
          display: 'grid',
          gap: 6,
        }}
      >
        {segments.map((segment) => (
          <li
            key={segment.id}
            style={{
              display: 'flex',
              alignItems: 'center',
              gap: 8,
              color: BOARD.ink,
              fontSize: 10,
              letterSpacing: '0.05em',
            }}
          >
            <span
              aria-hidden="true"
              style={{
                width: 8,
                height: 8,
                flex: '0 0 auto',
                background: TONE_COLOR[segment.tone ?? 'neutral'],
              }}
            />
            <span style={{ flex: '1 1 auto' }}>{segment.label}</span>
            <span style={{ color: BOARD.inkHi, fontVariantNumeric: 'tabular-nums' }}>
              {formatNumber(segment.value)}
            </span>
          </li>
        ))}
      </ul>
    </div>
  );
}
