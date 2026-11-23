import type { Part } from '../../contract';

/**
 * Parts list / bill of materials.
 *
 * Drawing Standard 5.3 rule 7: a hairline-ruled table of balloon number, part
 * name and count. No quantities beyond the count and no dimensions — that is
 * `inkwork`'s territory, not this engine's.
 */
export interface BillRow {
  number: number;
  label: string;
  count: number;
}

/**
 * Build the parts-list rows for an assembly, in balloon order.
 *
 * Parts without a balloon number are not listed; every listed row counts one
 * physical item.
 */
export function billFor(parts: Part[]): BillRow[] {
  return parts
    .filter((p): p is Part & { balloon: number } => typeof p.balloon === 'number')
    .map((p) => ({ number: p.balloon, label: p.label, count: 1 }))
    .sort((a, b) => a.number - b.number);
}
