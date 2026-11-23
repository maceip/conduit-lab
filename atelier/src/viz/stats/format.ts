/**
 * Shared number formatting for the tier-1 statistics components.
 *
 * Every figure the gallery shows comes from `browser/ratchet.json` or
 * `data/stats.json`. This module only renders a number that has already been
 * read from one of those reports — it never invents one.
 */

const GROUPED = new Intl.NumberFormat('en-US');

/** Formats a number with thousands separators, e.g. `12480` -> `12,480`. */
export function formatNumber(value: number): string {
  return GROUPED.format(value);
}

/** Joins class names, ignoring empty ones. */
export function cx(...parts: Array<string | undefined | false>): string {
  return parts.filter((part): part is string => typeof part === 'string' && part.length > 0).join(' ');
}
