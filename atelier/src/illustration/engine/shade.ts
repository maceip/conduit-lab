import type { Vec3 } from '../../contract';
import { dot } from './camera';

/**
 * Face shading — a port of `shadeClass` in `v8-iso/iso-cad.mjs`.
 *
 * The published plates use the default `body` palette, whose four classes are
 * separated by these thresholds on `dot(normal, light)`:
 *
 *   b >  0.55  -> cad-bd-3
 *   b >  0.16  -> cad-bd-2
 *   b > -0.22  -> cad-bd-1
 *   else       -> cad-bd-0
 *
 * The thresholds are reused verbatim so an atelier face and a published face
 * with the same normal land on the same tone. `SHADE[0..3]` in
 * `contract/tokens` are byte-identical to the published `--bd0..--bd3`
 * (`#111315`, `#171a1d`, `#1e2226`, `#262b30`), which is what makes the two
 * sets read as one. `SHADE[4]` is reserved for sectioned material, which the
 * drafting convention draws in a distinct tone.
 */
export const SHADE_CLASS = {
  /** Above this the face is the brightest class. */
  hi3: 0.55,
  /** Above this the face is the upper-middle class. */
  hi2: 0.16,
  /** Above this the face is the lower-middle class; below it is the darkest. */
  hi1: -0.22,
} as const;

/** The four published body-palette classes, as ramp indices. */
export type ShadeClass = 0 | 1 | 2 | 3;

/** Classify a raw lambert value with the published thresholds. */
export function shadeClassIndex(b: number): ShadeClass {
  if (b > SHADE_CLASS.hi3) return 3;
  if (b > SHADE_CLASS.hi2) return 2;
  if (b > SHADE_CLASS.hi1) return 1;
  return 0;
}

/**
 * Shade ramp index for a face.
 *
 * @param normal world-space unit normal (the published engine shades the world
 *   normal against the world key light, so it is shaded before the view
 *   transform).
 * @param light unit key-light direction.
 * @returns ramp index 0..3 of the six-step `SHADE` ramp.
 */
export function shadeFor(normal: Vec3, light: Vec3): number {
  return shadeClassIndex(dot(normal, light));
}
