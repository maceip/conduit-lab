import type { Palette, Vec3 } from '../../contract';
import { dot } from './camera';

/**
 * Face shading — a port of `shadeClass` in `v8-iso/iso-cad.mjs`.
 *
 * The published plates are NOT drawn on one ramp. Each part selects a palette
 * and the shading ramp is applied *within* it, which is where their tonal
 * range comes from: a dark skid under a bright machined silo. Collapsing
 * every part onto a single ramp loses the form entirely, so the palette is a
 * first-class property of a part, not of the drawing.
 *
 * The thresholds below are the published ones, per palette:
 *
 *   body : b >  0.55 -> 3, b >  0.16 -> 2, b > -0.22 -> 1, else 0
 *   hi   : b >  0.52 -> 3, b >  0.12 -> 2, b > -0.25 -> 1, else 0
 *   dark : b >  0.35 -> 2, b > -0.15 -> 1, else 0
 *
 * and the ramps themselves live in `contract/tokens` as `SHADE_BODY`,
 * `SHADE_DARK` and `SHADE_HI` — byte-identical to the published
 * `--bd0..--bd3`, `--dk0..--dk2` and `--hi0..--hi3` custom properties, so an
 * atelier face and a published face with the same normal and palette land on
 * the same tone.
 */
export const SHADE_CLASS = {
  body: { hi3: 0.55, hi2: 0.16, hi1: -0.22 },
  hi: { hi3: 0.52, hi2: 0.12, hi1: -0.25 },
  dark: { hi3: 0.35, hi2: -0.15, hi1: null },
} as const satisfies Record<Palette, { hi3: number; hi2: number; hi1: number | null }>;

/**
 * Classify a raw lambert value (`dot(normal, light)`) into a ramp index for
 * the given palette.
 */
export function shadeClassIndex(b: number, palette: Palette = 'body'): number {
  if (palette === 'dark') {
    const t = SHADE_CLASS.dark;
    return b > t.hi3 ? 2 : b > t.hi2 ? 1 : 0;
  }
  if (palette === 'hi') {
    const t = SHADE_CLASS.hi;
    return b > t.hi3 ? 3 : b > t.hi2 ? 2 : b > t.hi1 ? 1 : 0;
  }
  const t = SHADE_CLASS.body;
  return b > t.hi3 ? 3 : b > t.hi2 ? 2 : b > t.hi1 ? 1 : 0;
}

/**
 * Shade ramp index for a face.
 *
 * @param normal world-space unit normal (the published engine shades the world
 *   normal against the world key light, so it is shaded before the view
 *   transform).
 * @param light unit key-light direction.
 * @param palette the part's body palette; defaults to `body`.
 * @returns index into the palette's ramp: 0..3 for `body` and `hi`, 0..2 for
 *   `dark`.
 */
export function shadeFor(normal: Vec3, light: Vec3, palette: Palette = 'body'): number {
  return shadeClassIndex(dot(normal, light), palette);
}
