import type { Part, Vec3 } from '../../contract';
import { add, dot, mul, norm, sub } from './camera';
import type { Assembly } from './index';

/**
 * Exploded-axis offsets.
 *
 * The Drawing Standard: parts separate along one dominant axis with a
 * consistent gap, and the gap is uniform per assembly. `part.explode` is the
 * authored world-space offset; its component along the shared assembly axis is
 * the explode distance and is scaled by the assembly's gap multiplier. Any
 * component perpendicular to the axis is carried through unchanged so a
 * diagonal explode still reads.
 *
 * Assemblies in this package author every explode vector parallel to the
 * assembly axis, so the perpendicular term is always zero in practice.
 */
export function explodedOffset(part: Part, assembly: Assembly): Vec3 {
  const raw = part.explode;
  if (!raw) return [0, 0, 0];
  const axis = norm(assembly.axis);
  const along = dot(raw, axis);
  const perpendicular = sub(raw, mul(axis, along));
  return add(mul(axis, along * assembly.explodeScale), perpendicular);
}
