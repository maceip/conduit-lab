/**
 * Tier-1 visualization components — animated figures and statistics.
 *
 * Every figure these components show is read from `browser/ratchet.json` or
 * `data/stats.json`. Nothing here invents a number: a field the reports do
 * not carry is rendered as `not recorded` by the caller.
 */
export { CountFigure } from './CountFigure';
export type { CountFigureProps } from './CountFigure';

export { OdometerReels } from './OdometerReels';
export type { OdometerReelsProps } from './OdometerReels';

export { StatTile } from './StatTile';
export type { StatTileProps } from './StatTile';

export { SplitBar } from './SplitBar';
export type { SplitBarProps, SplitBarSegment } from './SplitBar';

export { RadialGauge } from './RadialGauge';
export type { RadialGaugeProps } from './RadialGauge';

export { DeltaChip } from './DeltaChip';
export type { DeltaChipProps } from './DeltaChip';

export { RatchetCounter } from './RatchetCounter';
export type { RatchetCounterProps } from './RatchetCounter';
