import type { GeometrySpec, Vec2, Vec3 } from '../../contract';
import { add, cross, dot, mul, norm, sub } from './camera';

/**
 * Geometry: `GeometrySpec` -> world-space faces.
 *
 * Every primitive is a port of the matching routine in `v8-iso/iso-cad.mjs`
 * (`box3`, `cyl`, `revolve`, `loft`, `extrudePoly`, `sweepTube`), including the
 * face windings — the winding is what makes `faceNormal` point outward, and
 * outward normals are what make the v8-iso shade ramp come out identical.
 *
 * The frozen contract is smaller than the original engine, so two conventions
 * are fixed here and documented rather than guessed at:
 *
 *  - `revolve` is revolved about **+z through the world origin** (the contract
 *    carries no origin or axis). Use `loft` for a revolved shape that has to
 *    sit away from the origin.
 *  - `extrude` takes its polygon in the **xy plane** and sweeps it along **+z**
 *    from z = 0 to z = `depth` (the contract carries no u/v/w axes).
 *  - `loft` carries no cross-section, so the engine lofts a ruled **web** of
 *    constant half-width (`LOFT_HALF_WIDTH`) along the station polyline.
 */

/** Facet count used for cylinders and swept tubes. */
export const CYL_SEGMENTS = 20;
/** Facet count used for swept tubes. */
export const TUBE_SEGMENTS = 12;
/** Half-width of a lofted web, in world units. */
export const LOFT_HALF_WIDTH = 4;

export interface RawFace {
  /** World-space polygon (3 or 4 points, wound counter-clockwise seen from outside). */
  points: Vec3[];
  /** Outward unit normal. */
  normal: Vec3;
}

function at(pts: Vec3[], i: number): Vec3 {
  const p = pts[((i % pts.length) + pts.length) % pts.length];
  if (!p) throw new Error('geometry: empty polygon');
  return p;
}

/**
 * Newell's method — the exact normal calculation used by `iso-cad.mjs`.
 */
export function faceNormal(pts: Vec3[]): Vec3 {
  let nx = 0;
  let ny = 0;
  let nz = 0;
  for (let i = 0; i < pts.length; i++) {
    const a = at(pts, i);
    const b = at(pts, i + 1);
    nx += (a[1] - b[1]) * (a[2] + b[2]);
    ny += (a[2] - b[2]) * (a[0] + b[0]);
    nz += (a[0] - b[0]) * (a[1] + b[1]);
  }
  return norm([nx, ny, nz]);
}

function face(points: Vec3[]): RawFace {
  return { points, normal: faceNormal(points) };
}

/** Centroid of a polygon. */
export function centroid(points: Vec3[]): Vec3 {
  let x = 0;
  let y = 0;
  let z = 0;
  for (const p of points) {
    x += p[0];
    y += p[1];
    z += p[2];
  }
  const n = points.length || 1;
  return [x / n, y / n, z / n];
}

/** Area of a planar polygon in the xy plane (signed). */
function signedArea(poly: Vec2[]): number {
  let area = 0;
  for (let i = 0; i < poly.length; i++) {
    const a = poly[i];
    const b = poly[(i + 1) % poly.length];
    if (!a || !b) continue;
    area += a[0] * b[1] - b[0] * a[1];
  }
  return area;
}

/** Ear-clipping triangulation of a simple polygon — port of `triangulate2D`. */
export function triangulate2D(pts: Vec2[]): Array<[number, number, number]> {
  const n = pts.length;
  if (n < 3) return [];
  const area = signedArea(pts);
  const idx = Array.from({ length: n }, (_, i) => (area >= 0 ? i : n - 1 - i));
  const tris: Array<[number, number, number]> = [];
  const cross2 = (a: Vec2, b: Vec2, c: Vec2) =>
    (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0]);
  const inTri = (p: Vec2, a: Vec2, b: Vec2, c: Vec2) =>
    cross2(a, b, p) >= -1e-6 && cross2(b, c, p) >= -1e-6 && cross2(c, a, p) >= -1e-6;

  let guard = n * n * 2;
  while (idx.length > 3 && guard-- > 0) {
    let cut = false;
    for (let i = 0; i < idx.length; i++) {
      const i0 = idx[(i + idx.length - 1) % idx.length];
      const i1 = idx[i];
      const i2 = idx[(i + 1) % idx.length];
      if (i0 === undefined || i1 === undefined || i2 === undefined) continue;
      const a = pts[i0];
      const b = pts[i1];
      const c = pts[i2];
      if (!a || !b || !c) continue;
      if (cross2(a, b, c) <= 1e-6) continue;
      let blocked = false;
      for (const ik of idx) {
        if (ik === i0 || ik === i1 || ik === i2) continue;
        const p = pts[ik];
        if (!p) continue;
        if (inTri(p, a, b, c)) {
          blocked = true;
          break;
        }
      }
      if (!blocked) {
        tris.push([i0, i1, i2]);
        idx.splice(i, 1);
        cut = true;
        break;
      }
    }
    if (!cut) {
      const first = idx[0];
      const second = idx[1];
      const third = idx[2];
      if (first === undefined || second === undefined || third === undefined) break;
      tris.push([first, second, third]);
      idx.splice(1, 1);
    }
  }
  if (idx.length === 3) {
    const a = idx[0];
    const b = idx[1];
    const c = idx[2];
    if (a !== undefined && b !== undefined && c !== undefined) tris.push([a, b, c]);
  }
  return tris;
}

/** Box with `at` as the minimum corner and `size` as [width, depth, height]. */
function boxFaces(at0: Vec3, size: Vec3): RawFace[] {
  const [x, y, z] = at0;
  const [w, d, h] = size;
  const p000: Vec3 = [x, y, z];
  const p100: Vec3 = [x + w, y, z];
  const p110: Vec3 = [x + w, y + d, z];
  const p010: Vec3 = [x, y + d, z];
  const p001: Vec3 = [x, y, z + h];
  const p101: Vec3 = [x + w, y, z + h];
  const p111: Vec3 = [x + w, y + d, z + h];
  const p011: Vec3 = [x, y + d, z + h];
  // Windings copied from `box3` in iso-cad.mjs: every normal points outward.
  return [
    face([p001, p101, p111, p011]),
    face([p000, p010, p110, p100]),
    face([p010, p011, p111, p110]),
    face([p100, p110, p111, p101]),
    face([p000, p100, p101, p001]),
    face([p000, p001, p011, p010]),
  ];
}

/** Cylinder / truncated cone from `from` to `to`. */
function cylFaces(from: Vec3, to: Vec3, r0: number, r1: number): RawFace[] {
  const u = norm(sub(to, from));
  const ref: Vec3 = Math.abs(u[2]) < 0.85 ? [0, 0, 1] : [1, 0, 0];
  const e1 = norm(cross(ref, u));
  const e2 = norm(cross(u, e1));
  const ringAt = (c: Vec3, r: number, i: number): Vec3 => {
    const a = (Math.PI * 2 * i) / CYL_SEGMENTS;
    const ca = Math.cos(a);
    const sa = Math.sin(a);
    return [
      c[0] + r * (ca * e1[0] + sa * e2[0]),
      c[1] + r * (ca * e1[1] + sa * e2[1]),
      c[2] + r * (ca * e1[2] + sa * e2[2]),
    ];
  };
  const faces: RawFace[] = [];
  for (let i = 0; i < CYL_SEGMENTS; i++) {
    const j = (i + 1) % CYL_SEGMENTS;
    const b0 = ringAt(from, r0, i);
    const b1 = ringAt(from, r0, j);
    const t0 = ringAt(to, r1, i);
    const t1 = ringAt(to, r1, j);
    if (r0 <= 1e-4 && r1 <= 1e-4) continue;
    if (r0 <= 1e-4) faces.push(face([from, t1, t0]));
    else if (r1 <= 1e-4) faces.push(face([b0, b1, to]));
    else faces.push(face([b0, b1, t1, t0]));
  }
  if (r1 > 1e-4) {
    const top = Array.from({ length: CYL_SEGMENTS }, (_, i) => ringAt(to, r1, i));
    faces.push(face(top));
  }
  if (r0 > 1e-4) {
    const bottom = Array.from({ length: CYL_SEGMENTS }, (_, i) => ringAt(from, r0, CYL_SEGMENTS - 1 - i));
    faces.push(face(bottom));
  }
  return faces;
}

/**
 * Surface of revolution about +z through the origin.
 * `profile` is a list of [height, radius] pairs running bottom to top.
 */
function revolveFaces(profile: Vec2[], segments: number): RawFace[] {
  const segs = Math.max(3, Math.round(segments));
  const faces: RawFace[] = [];
  const pt = (s: number, r: number, a: number): Vec3 => [Math.cos(a) * r, Math.sin(a) * r, s];
  for (let k = 0; k < profile.length - 1; k++) {
    const p0 = profile[k];
    const p1 = profile[k + 1];
    if (!p0 || !p1) continue;
    const [s0, r0] = p0;
    const [s1, r1] = p1;
    if (r0 < 1e-4 && r1 < 1e-4) continue;
    for (let i = 0; i < segs; i++) {
      const a0 = (Math.PI * 2 * i) / segs;
      const a1 = (Math.PI * 2 * (i + 1)) / segs;
      const p00 = pt(s0, r0, a0);
      const p10 = pt(s0, r0, a1);
      const p11 = pt(s1, r1, a1);
      const p01 = pt(s1, r1, a0);
      if (r0 < 1e-4) faces.push(face([p00, p11, p01]));
      else if (r1 < 1e-4) faces.push(face([p00, p10, p11]));
      else faces.push(face([p00, p10, p11, p01]));
    }
  }
  // Close the shell when the profile stops at a finite radius (an open top).
  const first = profile[0];
  const last = profile[profile.length - 1];
  if (first && first[1] > 0.5) {
    const s = first[0];
    const r = first[1];
    const cap = Array.from({ length: segs }, (_, i) => pt(s, r, (Math.PI * 2 * (segs - 1 - i)) / segs));
    faces.push(face(cap));
  }
  if (last && last[1] > 0.5) {
    const s = last[0];
    const r = last[1];
    const cap = Array.from({ length: segs }, (_, i) => pt(s, r, (Math.PI * 2 * i) / segs));
    faces.push(face(cap));
  }
  return faces;
}

/**
 * Lofted web along the station polyline: a ruled surface of constant
 * half-width, emitted double sided so it reads from either side.
 */
function loftFaces(stations: Vec3[]): RawFace[] {
  if (stations.length < 2) return [];
  const faces: RawFace[] = [];
  for (let i = 0; i < stations.length - 1; i++) {
    const a = stations[i];
    const b = stations[i + 1];
    if (!a || !b) continue;
    const t = norm(sub(b, a));
    const ref: Vec3 = Math.abs(t[2]) < 0.99 ? [0, 0, 1] : [0, 1, 0];
    const w = norm(cross(t, ref));
    const off = mul(w, LOFT_HALF_WIDTH);
    const quad = [
      sub(a, off),
      add(a, off),
      add(b, off),
      sub(b, off),
    ];
    faces.push(face(quad));
    faces.push(face([quad[3]!, quad[2]!, quad[1]!, quad[0]!]));
  }
  return faces;
}

/** Extruded polygon: `poly` in the xy plane, swept along +z by `depth`. */
function extrudeFaces(poly: Vec2[], depth: number): RawFace[] {
  if (poly.length < 3) return [];
  const front: Vec3[] = poly.map(([u, v]) => [u, v, 0]);
  const back: Vec3[] = poly.map(([u, v]) => [u, v, depth]);
  const ccw = signedArea(poly) >= 0;
  const faces: RawFace[] = [];
  const n = poly.length;
  for (let i = 0; i < n; i++) {
    const j = (i + 1) % n;
    const fi = front[i];
    const fj = front[j];
    const bi = back[i];
    const bj = back[j];
    if (!fi || !fj || !bi || !bj) continue;
    faces.push(face(ccw ? [fj, fi, bi, bj] : [fi, fj, bj, bi]));
  }
  const tris = triangulate2D(poly);
  for (const [ia, ib, ic] of tris) {
    const pa = front[ia];
    const pb = front[ib];
    const pc = front[ic];
    const qa = back[ia];
    const qb = back[ib];
    const qc = back[ic];
    if (!pa || !pb || !pc || !qa || !qb || !qc) continue;
    faces.push(face([pa, pc, pb]));
    faces.push(face([qa, qb, qc]));
  }
  return faces;
}

/** Swept tube of constant radius along a polyline — port of `sweepTube`. */
function tubeFaces(points: Vec3[], radius: number): RawFace[] {
  if (points.length < 2) return [];
  const segs = TUBE_SEGMENTS;
  const tangents: Vec3[] = points.map((_, i): Vec3 => {
    if (i === 0) {
      const p0 = points[0];
      const p1 = points[1];
      return p0 && p1 ? norm(sub(p1, p0)) : [0, 0, 1];
    }
    if (i === points.length - 1) {
      const pn = points[i];
      const pp = points[i - 1];
      return pn && pp ? norm(sub(pn, pp)) : [0, 0, 1];
    }
    const a = points[i + 1];
    const b = points[i - 1];
    return a && b ? norm(sub(a, b)) : [0, 0, 1];
  });

  let t0: Vec3 = tangents[0] ?? [0, 0, 1];
  let n0: Vec3 = norm(cross(Math.abs(t0[2]) < 0.85 ? [0, 0, 1] : [1, 0, 0], t0));
  const rings: Vec3[][] = [];
  for (let i = 0; i < points.length; i++) {
    const centre = points[i];
    const ti = tangents[i];
    if (!centre || !ti) continue;
    if (i > 0) {
      const axis = cross(t0, ti);
      const sinA = Math.hypot(axis[0], axis[1], axis[2]);
      if (sinA > 1e-5) {
        const k = mul(axis, 1 / sinA);
        const cosA = Math.max(-1, Math.min(1, dot(t0, ti)));
        const kv = cross(k, n0);
        const kd = dot(k, n0);
        n0 = norm([
          n0[0] * cosA + kv[0] * sinA + k[0] * kd * (1 - cosA),
          n0[1] * cosA + kv[1] * sinA + k[1] * kd * (1 - cosA),
          n0[2] * cosA + kv[2] * sinA + k[2] * kd * (1 - cosA),
        ]);
      }
      t0 = ti;
    }
    const b0 = norm(cross(ti, n0));
    const ring: Vec3[] = [];
    for (let j = 0; j < segs; j++) {
      const a = (Math.PI * 2 * j) / segs;
      const ca = Math.cos(a) * radius;
      const sa = Math.sin(a) * radius;
      ring.push([
        centre[0] + ca * n0[0] + sa * b0[0],
        centre[1] + ca * n0[1] + sa * b0[1],
        centre[2] + ca * n0[2] + sa * b0[2],
      ]);
    }
    rings.push(ring);
  }
  if (rings.length < 2) return [];

  const faces: RawFace[] = [];
  for (let s = 0; s < rings.length - 1; s++) {
    const A = rings[s];
    const B = rings[s + 1];
    if (!A || !B) continue;
    const cA = centroid(A);
    const cB = centroid(B);
    const mid: Vec3 = [(cA[0] + cB[0]) / 2, (cA[1] + cB[1]) / 2, (cA[2] + cB[2]) / 2];
    for (let i = 0; i < A.length; i++) {
      const j = (i + 1) % A.length;
      const ai = A[i];
      const aj = A[j];
      const bi = B[i];
      const bj = B[j];
      if (!ai || !aj || !bi || !bj) continue;
      let quad = [ai, aj, bj, bi];
      const n = faceNormal(quad);
      const c = centroid(quad);
      if (dot(n, sub(c, mid)) < 0) quad = [ai, bi, bj, aj];
      faces.push(face(quad));
    }
  }
  const firstRing = rings[0];
  const lastRing = rings[rings.length - 1];
  if (firstRing) faces.push(face([...firstRing].reverse()));
  if (lastRing) faces.push(face([...lastRing]));
  return faces;
}

/** Build the world-space faces of a geometry spec. */
export function facesFor(spec: GeometrySpec): RawFace[] {
  switch (spec.kind) {
    case 'box':
      return boxFaces(spec.at, spec.size);
    case 'cyl':
      return cylFaces(spec.from, spec.to, spec.r0, spec.r1 ?? spec.r0);
    case 'revolve':
      return revolveFaces(spec.profile, spec.segments);
    case 'loft':
      return loftFaces(spec.stations);
    case 'extrude':
      return extrudeFaces(spec.poly, spec.depth);
    case 'tube':
      return tubeFaces(spec.points, spec.radius);
    default: {
      const never: never = spec;
      throw new Error(`geometry: unsupported spec ${JSON.stringify(never)}`);
    }
  }
}
