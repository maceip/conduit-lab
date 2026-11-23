import type { Vec2, Vec3 } from '../../contract';

/**
 * Isometric camera — a verbatim port of the basis in `v8-iso/iso-cad.mjs`
 * (`createCad`). The published v8-iso plates and the atelier plates must read
 * as one set, so both the basis and the key light are reused exactly:
 *
 *   az = azDeg * PI/180
 *   el = elDeg * PI/180
 *   V  = [cos(el)cos(az), cos(el)sin(az), sin(el)]   // view direction
 *   Rx = [sin(az), -cos(az), 0]                     // screen right
 *   Ds = [sin(el)cos(az), sin(el)sin(az), -cos(el)]  // screen down
 *   project(p) = [dot(p, Rx), dot(p, Ds)]
 *
 *   L  = normalize([cos(az-0.55)*0.48, sin(az-0.55)*0.48, 0.88])
 *
 * `v8-iso/iso-cad.mjs` is read-only reference. Nothing here mutates it.
 */

/** Dot product of two 3-vectors. */
export function dot(a: Vec3, b: Vec3): number {
  return a[0] * b[0] + a[1] * b[1] + a[2] * b[2];
}

/** Cross product of two 3-vectors. */
export function cross(a: Vec3, b: Vec3): Vec3 {
  return [
    a[1] * b[2] - a[2] * b[1],
    a[2] * b[0] - a[0] * b[2],
    a[0] * b[1] - a[1] * b[0],
  ];
}

/** Vector subtraction. */
export function sub(a: Vec3, b: Vec3): Vec3 {
  return [a[0] - b[0], a[1] - b[1], a[2] - b[2]];
}

/** Vector addition. */
export function add(a: Vec3, b: Vec3): Vec3 {
  return [a[0] + b[0], a[1] + b[1], a[2] + b[2]];
}

/** Scalar multiply. */
export function mul(a: Vec3, s: number): Vec3 {
  return [a[0] * s, a[1] * s, a[2] * s];
}

/** Unit-length vector (a zero vector is returned unchanged). */
export function norm(a: Vec3): Vec3 {
  const l = Math.hypot(a[0], a[1], a[2]) || 1;
  return [a[0] / l, a[1] / l, a[2] / l];
}

/** Linear interpolation between two 3-vectors. */
export function lerp3(a: Vec3, b: Vec3, t: number): Vec3 {
  return [
    a[0] + (b[0] - a[0]) * t,
    a[1] + (b[1] - a[1]) * t,
    a[2] + (b[2] - a[2]) * t,
  ];
}

export interface Camera {
  readonly azDeg: number;
  readonly elDeg: number;
  /** Unit view direction. */
  readonly view: Vec3;
  /** Screen-right axis. */
  readonly right: Vec3;
  /** Screen-down axis. */
  readonly down: Vec3;
  /** Unit key light direction (world space). */
  readonly light: Vec3;
  /** Project a world point into screen space. */
  project(p: Vec3): Vec2;
  /** Rotate a world normal into view space (Rx, Ds, V). */
  viewNormal(n: Vec3): Vec3;
}

/**
 * Build the isometric camera. `azDeg` 42 / `elDeg` 30 are the published
 * defaults (see `ISO` in `contract/tokens`).
 */
export function cameraFor(azDeg: number, elDeg: number): Camera {
  const az = (azDeg * Math.PI) / 180;
  const el = (elDeg * Math.PI) / 180;
  const view: Vec3 = [Math.cos(el) * Math.cos(az), Math.cos(el) * Math.sin(az), Math.sin(el)];
  const right: Vec3 = [Math.sin(az), -Math.cos(az), 0];
  const down: Vec3 = [Math.sin(el) * Math.cos(az), Math.sin(el) * Math.sin(az), -Math.cos(el)];

  // Key light, copied from `iso-cad.mjs` so shading matches the published set.
  const lx = Math.cos(az - 0.55) * 0.48;
  const ly = Math.sin(az - 0.55) * 0.48;
  const lz = 0.88;
  const len = Math.hypot(lx, ly, lz);
  const light: Vec3 = [lx / len, ly / len, lz / len];

  return {
    azDeg,
    elDeg,
    view,
    right,
    down,
    light,
    project: (p: Vec3): Vec2 => [dot(p, right), dot(p, down)],
    viewNormal: (n: Vec3): Vec3 => [dot(n, right), dot(n, down), dot(n, view)],
  };
}
