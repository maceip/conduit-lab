import type { Part, Vec3 } from '../../contract';
import { add, mul, norm, sub } from './camera';

/**
 * Centrelines — dash-dot lines through every axis of symmetry, extending ~3%
 * past the feature (Drawing Standard 5.3 rule 5).
 */
export interface Centerline {
  a: Vec3;
  b: Vec3;
}

/** Fraction the centreline runs past each end of the feature. */
export const CENTERLINE_OVERSHOOT = 0.03;

function extend(a: Vec3, b: Vec3): Centerline {
  const dir = sub(b, a);
  const len = Math.hypot(dir[0], dir[1], dir[2]);
  const pad = len * CENTERLINE_OVERSHOOT;
  const unit = norm(dir);
  return { a: sub(a, mul(unit, pad)), b: add(b, mul(unit, pad)) };
}

/**
 * The symmetry axis of a part, in world space (before the explode offset is
 * applied).
 */
export function centerlineFor(part: Part): Centerline | null {
  const g = part.geometry;
  switch (g.kind) {
    case 'cyl': {
      return extend(g.from, g.to);
    }
    case 'tube': {
      const first = g.points[0];
      const last = g.points[g.points.length - 1];
      if (!first || !last) return null;
      return extend(first, last);
    }
    case 'loft': {
      const first = g.stations[0];
      const last = g.stations[g.stations.length - 1];
      if (!first || !last) return null;
      return extend(first, last);
    }
    case 'box': {
      const [x, y, z] = g.at;
      const [w, d, h] = g.size;
      return extend([x + w / 2, y + d / 2, z], [x + w / 2, y + d / 2, z + h]);
    }
    case 'revolve': {
      const first = g.profile[0];
      const last = g.profile[g.profile.length - 1];
      if (!first || !last) return null;
      return extend([0, 0, first[0]], [0, 0, last[0]]);
    }
    case 'extrude': {
      const xs = g.poly.map((p) => p[0]);
      const ys = g.poly.map((p) => p[1]);
      if (xs.length === 0 || ys.length === 0) return null;
      const cx = xs.reduce((s, v) => s + v, 0) / xs.length;
      const cy = ys.reduce((s, v) => s + v, 0) / ys.length;
      return extend([cx, cy, 0], [cx, cy, g.depth]);
    }
    default: {
      const never: never = g;
      throw new Error(`centerline: unsupported geometry ${JSON.stringify(never)}`);
    }
  }
}
