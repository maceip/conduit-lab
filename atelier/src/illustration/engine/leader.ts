import type { Vec2 } from '../../contract';

/**
 * Leader lines.
 *
 * Drawing Standard 5.3 rule 2: a hairline leader runs from the part's own
 * surface out to the balloon. The polyline is built with one orthogonal
 * elbow so the run leaves the drawing along an axis and never turns through
 * an arbitrary angle — the classic drafting leader.
 */
export function leaderPath(from: Vec2, to: Vec2): Vec2[] {
  const dx = to[0] - from[0];
  const dy = to[1] - from[1];
  if (Math.abs(dx) >= Math.abs(dy)) {
    return [from, [to[0], from[1]], to];
  }
  return [from, [from[0], to[1]], to];
}
