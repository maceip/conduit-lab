import type { Vec2 } from '../../contract';

/**
 * Balloons — circled part numbers.
 *
 * Drawing Standard 5.3 rule 3: circle `r = 9`, one stroke, numeral centred in
 * 9px mono, numbered in assembly order and mapped to the parts list.
 */
export const BALLOON_R = 9;

/** Gap between the drawing edge and the balloon circle. */
export const BALLOON_GAP = 10;

/** Minimum centre-to-centre spacing between two balloons on the same side. */
export const BALLOON_SPACING = BALLOON_R * 2 + 6;

export interface Bounds {
  minX: number;
  maxX: number;
  minY: number;
  maxY: number;
}

/** Which side of the drawing a balloon was placed on. */
export type BalloonSide = 'left' | 'right' | 'top' | 'bottom';

export interface BalloonPlacement {
  /** Centre of the balloon circle. */
  at: Vec2;
  /** Side of the drawing the balloon sits on. */
  side: BalloonSide;
}

/**
 * Choose the side of the drawing with the most room for a balloon, i.e. the
 * side the anchor is nearest to — the leader then has the shortest run and
 * crosses the least of the drawing.
 */
export function balloonSide(bounds: Bounds, from: Vec2): BalloonSide {
  const dLeft = from[0] - bounds.minX;
  const dRight = bounds.maxX - from[0];
  const dTop = from[1] - bounds.minY;
  const dBottom = bounds.maxY - from[1];
  const min = Math.min(dLeft, dRight, dTop, dBottom);
  if (min === dLeft) return 'left';
  if (min === dRight) return 'right';
  if (min === dTop) return 'top';
  return 'bottom';
}

/**
 * Place a balloon outside the drawing bounds on the given side, level with
 * its anchor. The result is outside the drawing and never overlaps it.
 */
export function balloonAnchor(bounds: Bounds, from: Vec2, side: BalloonSide): Vec2 {
  switch (side) {
    case 'left':
      return [bounds.minX - BALLOON_GAP - BALLOON_R, from[1]];
    case 'right':
      return [bounds.maxX + BALLOON_GAP + BALLOON_R, from[1]];
    case 'top':
      return [from[0], bounds.minY - BALLOON_GAP - BALLOON_R];
    case 'bottom':
    default:
      return [from[0], bounds.maxY + BALLOON_GAP + BALLOON_R];
  }
}

/**
 * Push balloons apart along their side so two circles never overlap.
 * Balloons keep their order; the whole run is recentred afterwards.
 */
export function separateBalloons(placed: BalloonPlacement[]): void {
  const sides: BalloonSide[] = ['left', 'right', 'top', 'bottom'];
  for (const side of sides) {
    const onSide = placed.filter((p) => p.side === side);
    if (onSide.length < 2) continue;
    const horizontal = side === 'left' || side === 'right';
    onSide.sort((a, b) => (horizontal ? a.at[1] - b.at[1] : a.at[0] - b.at[0]));
    for (let i = 1; i < onSide.length; i++) {
      const prev = onSide[i - 1];
      const cur = onSide[i];
      if (!prev || !cur) continue;
      const axis = horizontal ? 1 : 0;
      const delta = cur.at[axis]! - prev.at[axis]!;
      if (delta < BALLOON_SPACING) {
        const shift = BALLOON_SPACING - delta;
        const moved: Vec2 = [...cur.at];
        moved[axis] = cur.at[axis]! + shift;
        cur.at = moved;
      }
    }
  }
}
