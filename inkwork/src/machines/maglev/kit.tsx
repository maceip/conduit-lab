import * as THREE from 'three';
import { M } from '../../scene/Part';
import { Box, Cyl, YZ_X, roundFrame, roundRect } from '../kit';

/**
 * Maglev procedural geometry kit — Shanghai SMT / Transrapid TR08.
 * Millimetres, +x is forward (nose apex at x = 27000), centred on z = 0.
 *
 * Authentic TR08 geometry:
 * 1. Continuous C1 strictly-convex parabolic-elliptical nose profile from roof
 *    (y = 7600) to rounded bullnose apex (x = 27000, y = 4220) — zero concave dent,
 *    zero flat razor lip.
 * 2. Inverted-U wrap-around cab skirts (y = 2380 at |z| = 1850) that shroud the
 *    sides of the 2800 mm concrete guideway beam over the front bogie while the
 *    inner tunnel ceiling (y = 3500) clears the beam top (y = 3400), sweeping
 *    gracefully upward into the bullnose chin ahead of x = 24000.
 * 3. Three-pane arched wrap-around cockpit visor (wide panoramic center windshield
 *    + raked A-pillars + left/right cab cheek windows aligned with the passenger
 *    glazing beltline), twin sweeping SMT cheatlines, and flush cheek headlights.
 */

const shellCache = new Map<string, THREE.BufferGeometry>();
function shellExtrude(key: string, shape: () => THREE.Shape, depth: number) {
  let g = shellCache.get(key);
  if (!g) {
    g = new THREE.ExtrudeGeometry(shape(), { depth, bevelEnabled: false, curveSegments: 20 });
    shellCache.set(key, g);
  }
  return g;
}

/** Hollow profile extruded along +x from x0 to x1 (cross-section in the y–z plane). */
export function ProfileShell({ k, shape, x0, x1, y = 0, z = 0 }: {
  k: string; shape: () => THREE.Shape; x0: number; x1: number; y?: number; z?: number;
}) {
  return <M clip geo={shellExtrude(`mg-${k}`, shape, x1 - x0)} p={[x0, y, z]} r={YZ_X} />;
}

/** Smoothly evaluate TR08 nose envelope at normalized axial station u in [0, 1]. */
export function tr08Envelope(u: number, floorY: number, roofY: number, halfW: number) {
  const uc = Math.min(1, Math.max(0, u));
  const yApex = floorY + 820; // 4220 mm — rounded bullnose center cleanly above 3400 mm beam

  // Strictly convex streamline crown: dy/du = 0 at u=0 (C1 roof tangency), vertical tangent at u=1
  const yTop = yApex + (roofY - yApex) * Math.pow(Math.max(0, 1 - Math.pow(uc, 1.32)), 0.68);

  // Planform half-width: full 1850 mm past front bogie (u <= 0.22), then elliptical bullet taper
  const wt = uc <= 0.20 ? 0 : (uc - 0.20) / 0.80;
  const w = halfW * Math.pow(Math.max(0, 1 - Math.pow(wt, 1.78)), 0.54);

  // Center underbelly clears beamTopY (3400) at y=3500 until u=0.56, then curves up into bullnose chin
  const bt = uc <= 0.56 ? 0 : (uc - 0.56) / 0.44;
  const yBelly = (floorY + 100) + (yApex - (floorY + 100)) * (1 - Math.pow(Math.max(0, 1 - bt), 0.68));

  // Outer wrap-around cheek skirt hem: shrouds guideway beam (y = floorY - 1020 = 2380) at cab/bogie,
  // then sweeps smoothly upward to merge with yBelly once nose narrows inside beam width.
  const st = uc <= 0.18 ? 0 : Math.min(1, (uc - 0.18) / 0.46);
  const skirtEase = st * st * (3 - 2 * st);
  const ySkirtRaw = (floorY - 1020) + ((floorY + 140) - (floorY - 1020)) * skirtEase;
  const ySkirt = uc < 0.64 ? Math.min(yBelly, ySkirtRaw) : yBelly;

  return { yTop, yBelly, ySkirt, w: Math.max(40, w), yApex };
}

/**
 * 24-point closed cross-section ring in (y, z) at station u in [0, 1].
 * At u < 0.56, forms the authentic Transrapid inverted-U wrap-around skirt around the beam;
 * at u >= 0.56, morphs smoothly into a closed elliptical-bullnose streamliner cross-section.
 */
function noseStationRing(u: number, floorY: number, roofY: number, halfW: number, inset = 0): Array<[number, number]> {
  const env = tr08Envelope(u, floorY, roofY, halfW);
  const w = Math.max(36, env.w - inset);
  const yTop = Math.max(env.yBelly + 60, env.yTop - inset);
  const yBelly = env.yBelly + inset * 0.65;
  const ySkirt = Math.min(yBelly, env.ySkirt + inset * 0.65);

  // How much wrap-around skirt hangs below yBelly on the ±z flanks outside z = ±1480
  const skirtDrop = Math.max(0, yBelly - ySkirt);
  const innerZ = Math.min(w * 0.78, Math.max(0, 1485 - inset * 0.5));
  const hasWrap = skirtDrop > 18 && w > 1520;

  const hBody = Math.max(80, yTop - ySkirt);
  const shoulderBlend = 0.68 + 0.18 * u; // smooth arch from flank into crown

  // Upper arch from +z flank (angle 0) to crown (angle pi/2) to -z flank (angle pi)
  const archPts = 13; // odd count puts exact point at z = 0 crown
  const upper: Array<[number, number]> = [];
  const yMid = ySkirt + hBody * 0.36;
  const aY = Math.max(40, yTop - yMid);
  for (let k = 0; k < archPts; k += 1) {
    const theta = (Math.PI * k) / (archPts - 1); // 0 (+z) .. pi (-z)
    const c = Math.cos(theta);
    const s = Math.sin(theta);
    // Superellipse arch (exponent ~1.65 near u=0 for rounded TR08 roof shoulders, 1.92 near tip)
    const exp = 2 / (1.28 - 0.24 * shoulderBlend * (1 - u));
    const z = Math.sign(c) * Math.pow(Math.abs(c), 2 / (2.35 - 0.45 * u)) * w;
    const y = yMid + Math.pow(Math.max(0, s), 1 / exp) * aY;
    upper.push([y, z]);
  }

  if (hasWrap) {
    // Inverted-U lower contour: -z flank down to ySkirt, step to -innerZ, up to yBelly, across beam, down +innerZ, out to +z
    return [
      [yBelly, 0],
      [yBelly, innerZ],
      [ySkirt + skirtDrop * 0.12, innerZ + (w - innerZ) * 0.22],
      [ySkirt, w * 0.96],
      [ySkirt + hBody * 0.14, w],
      ...upper,
      [ySkirt + hBody * 0.14, -w],
      [ySkirt, -w * 0.96],
      [ySkirt + skirtDrop * 0.12, -(innerZ + (w - innerZ) * 0.22)],
      [yBelly, -innerZ],
    ];
  }

  // Ahead of the skirt wrap: smooth convex lower chin curve from -w to +w through yBelly
  const chinDepth = Math.max(20, yMid - yBelly);
  return [
    [yBelly, 0],
    [yBelly + chinDepth * 0.14, w * 0.52],
    [yBelly + chinDepth * 0.48, w * 0.88],
    [yMid * 0.98 + yBelly * 0.02, w],
    ...upper,
    [yMid * 0.98 + yBelly * 0.02, -w],
    [yBelly + chinDepth * 0.48, -w * 0.88],
    [yBelly + chinDepth * 0.14, -w * 0.52],
  ];
}

/** Resample any closed 2D ring to a fixed vertex count N by arc parameter so all loft stations match. */
function resampleRing(pts: Array<[number, number]>, count: number): Array<[number, number]> {
  const n = pts.length;
  const dists = [0];
  for (let i = 0; i < n; i += 1) {
    const a = pts[i];
    const b = pts[(i + 1) % n];
    dists.push(dists[i] + Math.hypot(b[0] - a[0], b[1] - a[1]));
  }
  const total = Math.max(1e-3, dists[n]);
  const out: Array<[number, number]> = [];
  let seg = 0;
  for (let k = 0; k < count; k += 1) {
    const target = (total * k) / count;
    while (seg < n - 1 && dists[seg + 1] < target) seg += 1;
    const span = Math.max(1e-6, dists[seg + 1] - dists[seg]);
    const t = Math.min(1, Math.max(0, (target - dists[seg]) / span));
    const a = pts[seg];
    const b = pts[(seg + 1) % n];
    out.push([a[0] + (b[0] - a[0]) * t, a[1] + (b[1] - a[1]) * t]);
  }
  return out;
}

function buildLoftedNose(x0: number, x1: number, floorY: number, roofY: number, halfW: number): THREE.BufferGeometry {
  const key = `mg-tr08-nose-v3-${x0}-${x1}`;
  const cached = shellCache.get(key);
  if (cached) return cached;

  const steps = 30;
  const ringPts = 32;
  const outerRings: Array<{ x: number; pts: Array<[number, number]> }> = [];
  const innerRings: Array<{ x: number; pts: Array<[number, number]> }> = [];

  for (let i = 0; i <= steps; i += 1) {
    // Cosine-clustered near u=1 so the bullnose curvature is extra fine
    const lin = i / steps;
    const u = 0.65 * lin + 0.35 * Math.sin((lin * Math.PI) / 2);
    const x = x0 + (x1 - x0) * u;
    outerRings.push({ x, pts: resampleRing(noseStationRing(u, floorY, roofY, halfW, 0), ringPts) });
    const ui = Math.min(u, 0.965);
    innerRings.push({
      x: Math.min(x, x1 - 95),
      pts: resampleRing(noseStationRing(ui, floorY, roofY, halfW, 95), ringPts),
    });
  }

  const positions: number[] = [];
  const pushTri = (a: [number, number, number], b: [number, number, number], c: [number, number, number]) => {
    positions.push(a[0], a[1], a[2], b[0], b[1], b[2], c[0], c[1], c[2]);
  };
  const pushQuad = (
    a: [number, number, number],
    b: [number, number, number],
    c: [number, number, number],
    d: [number, number, number],
  ) => {
    pushTri(a, b, c);
    pushTri(a, c, d);
  };

  for (let i = 0; i < steps; i += 1) {
    const r0 = outerRings[i];
    const r1 = outerRings[i + 1];
    const in0 = innerRings[i];
    const in1 = innerRings[i + 1];
    for (let j = 0; j < ringPts; j += 1) {
      const jn = (j + 1) % ringPts;
      pushQuad(
        [r0.x, r0.pts[j][0], r0.pts[j][1]],
        [r1.x, r1.pts[j][0], r1.pts[j][1]],
        [r1.x, r1.pts[jn][0], r1.pts[jn][1]],
        [r0.x, r0.pts[jn][0], r0.pts[jn][1]],
      );
      pushQuad(
        [in0.x, in0.pts[j][0], in0.pts[j][1]],
        [in0.x, in0.pts[jn][0], in0.pts[jn][1]],
        [in1.x, in1.pts[jn][0], in1.pts[jn][1]],
        [in1.x, in1.pts[j][0], in1.pts[j][1]],
      );
    }
  }

  const tip = outerRings[steps];
  const yApex = floorY + 820;
  const tipCenter: [number, number, number] = [x1 + 55, yApex, 0];
  const o0 = outerRings[0];
  const i0 = innerRings[0];
  for (let j = 0; j < ringPts; j += 1) {
    const jn = (j + 1) % ringPts;
    pushTri(
      [tip.x, tip.pts[j][0], tip.pts[j][1]],
      tipCenter,
      [tip.x, tip.pts[jn][0], tip.pts[jn][1]],
    );
    pushQuad(
      [o0.x, o0.pts[j][0], o0.pts[j][1]],
      [o0.x, o0.pts[jn][0], o0.pts[jn][1]],
      [i0.x, i0.pts[jn][0], i0.pts[jn][1]],
      [i0.x, i0.pts[j][0], i0.pts[j][1]],
    );
  }

  const geo = new THREE.BufferGeometry();
  geo.setAttribute('position', new THREE.Float32BufferAttribute(positions, 3));
  geo.computeVertexNormals();
  shellCache.set(key, geo);
  return geo;
}

/** Conformed surface strip along the TR08 nose flank (used for sweeping SMT cheatlines & headlight pods). */
function buildNoseSurfaceRibbon(
  keySuffix: string,
  x0: number,
  x1: number,
  floorY: number,
  roofY: number,
  halfW: number,
  uStart: number,
  uEnd: number,
  yAt: (u: number) => [number, number],
  side: 1 | -1,
  outset = 26,
): THREE.BufferGeometry {
  const key = `mg-ribbon-${keySuffix}-${side}`;
  const cached = shellCache.get(key);
  if (cached) return cached;

  const segs = 14;
  const positions: number[] = [];
  const pushQuad = (
    a: [number, number, number],
    b: [number, number, number],
    c: [number, number, number],
    d: [number, number, number],
  ) => {
    positions.push(a[0], a[1], a[2], b[0], b[1], b[2], c[0], c[1], c[2]);
    positions.push(a[0], a[1], a[2], c[0], c[1], c[2], d[0], d[1], d[2]);
  };

  const zOnShell = (u: number, y: number, lift: number) => {
    const env = tr08Envelope(u, floorY, roofY, halfW);
    const yMid = env.ySkirt + (env.yTop - env.ySkirt) * 0.36;
    const aY = Math.max(60, env.yTop - yMid);
    const s = Math.min(0.98, Math.max(0, (y - yMid) / aY));
    const zBase = env.w * Math.pow(Math.max(0.04, 1 - Math.pow(s, 1.65)), 0.46);
    return side * (zBase + lift);
  };

  for (let i = 0; i < segs; i += 1) {
    const u0 = uStart + (uEnd - uStart) * (i / segs);
    const u1 = uStart + (uEnd - uStart) * ((i + 1) / segs);
    const xa = x0 + (x1 - x0) * u0;
    const xb = x0 + (x1 - x0) * u1;
    const [y0a, y1a] = yAt(u0);
    const [y0b, y1b] = yAt(u1);

    const o00: [number, number, number] = [xa, y0a, zOnShell(u0, y0a, outset)];
    const o01: [number, number, number] = [xa, y1a, zOnShell(u0, y1a, outset)];
    const o11: [number, number, number] = [xb, y1b, zOnShell(u1, y1b, outset)];
    const o10: [number, number, number] = [xb, y0b, zOnShell(u1, y0b, outset)];

    const b00: [number, number, number] = [xa, y0a, zOnShell(u0, y0a, -8)];
    const b01: [number, number, number] = [xa, y1a, zOnShell(u0, y1a, -8)];
    const b11: [number, number, number] = [xb, y1b, zOnShell(u1, y1b, -8)];
    const b10: [number, number, number] = [xb, y0b, zOnShell(u1, y0b, -8)];

    if (side === 1) {
      pushQuad(o00, o10, o11, o01);
      pushQuad(b01, o01, o11, b11);
      pushQuad(o00, b00, b10, o10);
    } else {
      pushQuad(o01, o11, o10, o00);
      pushQuad(b11, o11, o01, b01);
      pushQuad(o10, b10, b00, o00);
    }
  }

  const geo = new THREE.BufferGeometry();
  geo.setAttribute('position', new THREE.Float32BufferAttribute(positions, 3));
  geo.computeVertexNormals();
  shellCache.set(key, geo);
  return geo;
}

/**
 * Sculpted 7.2 m Shanghai SMT / Transrapid TR08 streamlined nose:
 * strictly convex parabolic profile, wrap-around lower bogie skirts,
 * sweeping forward cheatlines, coupler nose-cone seam, and flush twin LED headlights.
 */
export function AeroNose({ x0, x1, floorY, roofY, halfW }: {
  x0: number; x1: number; floorY: number; roofY: number; halfW: number;
}) {
  // Forward-sweeping SMT cheatline tapering from passenger beltline (F+1320) down toward the nose tip
  const upperBand = (u: number): [number, number] => {
    const yc = (floorY + 1320) - 420 * Math.pow(u / 0.80, 1.35);
    const halfH = 48 * (1 - 0.42 * (u / 0.80));
    return [yc - halfH, yc + halfH];
  };
  const lowerBand = (u: number): [number, number] => {
    const yc = (floorY + 1140) - 390 * Math.pow(u / 0.76, 1.35);
    const halfH = 29 * (1 - 0.45 * (u / 0.76));
    return [yc - halfH, yc + halfH];
  };
  // Flush cat-eye / oval-trapezoid headlight clusters on lower nose cheeks (u = 0.72..0.88)
  const headlampPod = (u: number): [number, number] => {
    const t = (u - 0.72) / 0.16;
    const arch = Math.sin(Math.PI * Math.min(1, Math.max(0, t)));
    const yc = (floorY + 1180) - 240 * t;
    const halfH = 42 + 78 * arch;
    return [yc - halfH, yc + halfH];
  };

  return (
    <>
      <M clip geo={buildLoftedNose(x0, x1, floorY, roofY, halfW)} />
      {/* Forward-sweeping SMT cheatlines along both cab cheeks */}
      <M clip geo={buildNoseSurfaceRibbon('band-hi', x0, x1, floorY, roofY, halfW, 0, 0.80, upperBand, 1, 22)} />
      <M clip geo={buildNoseSurfaceRibbon('band-hi', x0, x1, floorY, roofY, halfW, 0, 0.80, upperBand, -1, 22)} />
      <M clip geo={buildNoseSurfaceRibbon('band-lo', x0, x1, floorY, roofY, halfW, 0, 0.76, lowerBand, 1, 22)} />
      <M clip geo={buildNoseSurfaceRibbon('band-lo', x0, x1, floorY, roofY, halfW, 0, 0.76, lowerBand, -1, 22)} />
      {/* Flush sculpted twin LED headlight clusters */}
      <M clip geo={buildNoseSurfaceRibbon('lamp', x0, x1, floorY, roofY, halfW, 0.72, 0.88, headlampPod, 1, 34)} />
      <M clip geo={buildNoseSurfaceRibbon('lamp', x0, x1, floorY, roofY, halfW, 0.72, 0.88, headlampPod, -1, 34)} />
    </>
  );
}

/**
 * Authentic Transrapid TR08 3-pane arched wrap-around cockpit visor:
 * wide curved center windshield + raked A-pillar mullions + left/right cab cheek
 * quarter-windows aligned directly with the passenger window band (floorY + 1520..2420).
 */
function buildTr08Visor(x0: number, x1: number, floorY: number, roofY: number, halfW: number): THREE.BufferGeometry {
  const key = `mg-tr08-visor-v3-${x0}-${x1}`;
  const cached = shellCache.get(key);
  if (cached) return cached;

  const positions: number[] = [];
  const pushQuad = (
    a: [number, number, number],
    b: [number, number, number],
    c: [number, number, number],
    d: [number, number, number],
  ) => {
    positions.push(a[0], a[1], a[2], b[0], b[1], b[2], c[0], c[1], c[2]);
    positions.push(a[0], a[1], a[2], c[0], c[1], c[2], d[0], d[1], d[2]);
  };

  // Helper projecting (u, s in [-1, 1]) onto the upper nose surface + lift normal offset
  const frontVisorPt = (u: number, s: number, lift: number): [number, number, number] => {
    const x = x0 + (x1 - x0) * u;
    const env = tr08Envelope(u, floorY, roofY, halfW);
    const zSpan = env.w * 0.74;
    const z = s * zSpan;
    const yMid = env.ySkirt + (env.yTop - env.ySkirt) * 0.36;
    const aY = Math.max(60, env.yTop - yMid);
    const cNorm = Math.min(0.96, Math.abs(z) / Math.max(80, env.w));
    const sinTheta = Math.pow(Math.max(0.02, 1 - Math.pow(cNorm, 2.1)), 0.58);
    const y = yMid + sinTheta * aY + lift * 0.82;
    const zOut = z + Math.sign(s) * lift * 0.35;
    return [x + lift * 0.32, y, zOut];
  };

  const addVisorPatch = (uA: number, uB: number, sA: number, sB: number, lift: number, nu = 10, ns = 10) => {
    for (let i = 0; i < nu; i += 1) {
      const u0 = uA + (uB - uA) * (i / nu);
      const u1 = uA + (uB - uA) * ((i + 1) / nu);
      for (let k = 0; k < ns; k += 1) {
        const s0 = sA + (sB - sA) * (k / ns);
        const s1 = sA + (sB - sA) * ((k + 1) / ns);
        // Arched brow at aft edge & curved sill at forward edge (classic TR08 visor silhouette)
        const arch0 = 0.045 * (s0 * s0);
        const arch1 = 0.045 * (s1 * s1);
        const top00 = frontVisorPt(u0 + arch0 * (1 - i / nu), s0, lift);
        const top01 = frontVisorPt(u0 + arch1 * (1 - i / nu), s1, lift);
        const top11 = frontVisorPt(u1 + arch1 * (1 - (i + 1) / nu), s1, lift);
        const top10 = frontVisorPt(u1 + arch0 * (1 - (i + 1) / nu), s0, lift);
        pushQuad(top00, top01, top11, top10);

        // Perimeter frame walls so InkRenderer draws razor-sharp visor & A-pillar creases
        if (i === 0) {
          const b00 = frontVisorPt(u0 + arch0, s0, -14);
          const b01 = frontVisorPt(u0 + arch1, s1, -14);
          pushQuad(b00, b01, top01, top00);
        }
        if (i === nu - 1) {
          const b10 = frontVisorPt(u1, s0, -14);
          const b11 = frontVisorPt(u1, s1, -14);
          pushQuad(top10, top11, b11, b10);
        }
        if (k === 0) {
          const b00 = frontVisorPt(u0 + arch0 * (1 - i / nu), s0, -14);
          const b10 = frontVisorPt(u1 + arch0 * (1 - (i + 1) / nu), s0, -14);
          pushQuad(b00, top00, top10, b10);
        }
        if (k === ns - 1) {
          const b01 = frontVisorPt(u0 + arch1 * (1 - i / nu), s1, -14);
          const b11 = frontVisorPt(u1 + arch1 * (1 - (i + 1) / nu), s1, -14);
          pushQuad(top01, b01, b11, top11);
        }
      }
    }
  };

  // Outer black visor mask bezel + inner panoramic center windshield pane
  addVisorPatch(0.13, 0.57, -0.96, 0.96, 24, 10, 12);
  addVisorPatch(0.16, 0.54, -0.68, 0.68, 44, 8, 8);
  // Left & right angled cab front-quarter panes separated by A-pillars
  addVisorPatch(0.15, 0.49, 0.74, 0.94, 42, 6, 4);
  addVisorPatch(0.15, 0.49, -0.94, -0.74, 42, 6, 4);

  const geo = new THREE.BufferGeometry();
  geo.setAttribute('position', new THREE.Float32BufferAttribute(positions, 3));
  geo.computeVertexNormals();
  shellCache.set(key, geo);
  return geo;
}

export function FlushWindshield({ x0, x1, floorY, roofY, halfW }: {
  x0: number; x1: number; floorY: number; roofY: number; halfW: number;
}) {
  // Wrap-around cab side windows continuing the exact passenger glazing belt (floorY + 1520..2420) onto both cab cheeks
  const sideCheekWindow = (u: number): [number, number] => {
    const t = Math.min(1, Math.max(0, u / 0.42));
    const yBot = floorY + 1520 + 60 * t;
    const yTop = (floorY + 2420) - 520 * Math.pow(t, 1.35);
    return [yBot, Math.max(yBot + 140, yTop)];
  };

  return (
    <>
      <M clip geo={buildTr08Visor(x0, x1, floorY, roofY, halfW)} />
      <M clip geo={buildNoseSurfaceRibbon('cab-win-outer', x0, x1, floorY, roofY, halfW, 0.02, 0.42, sideCheekWindow, 1, 24)} />
      <M clip geo={buildNoseSurfaceRibbon('cab-win-inner', x0, x1, floorY, roofY, halfW, 0.04, 0.39, (u) => {
        const [yb, yt] = sideCheekWindow(u);
        return [yb + 55, yt - 55];
      }, 1, 40)} />
      <M clip geo={buildNoseSurfaceRibbon('cab-win-outer', x0, x1, floorY, roofY, halfW, 0.02, 0.42, sideCheekWindow, -1, 24)} />
      <M clip geo={buildNoseSurfaceRibbon('cab-win-inner', x0, x1, floorY, roofY, halfW, 0.04, 0.39, (u) => {
        const [yb, yt] = sideCheekWindow(u);
        return [yb + 55, yt - 55];
      }, -1, 40)} />
    </>
  );
}

/**
 * Levitation / guidance magnet array: a row of C-core poles between x0 and x1,
 * each with two pole shoes and a coil block, opening toward ±z (side).
 */
export function MagnetArray({ x0, x1, poles, h = 340, depth = 220, side = 1 }: {
  x0: number; x1: number; poles: number; w?: number; h?: number; depth?: number; side?: 1 | -1;
}) {
  const step = (x1 - x0) / poles;
  return (
    <>
      <Box c={[(x0 + x1) / 2, 0, side * depth * 0.34]} s={[x1 - x0, h * 0.92, depth * 0.26]} />
      {Array.from({ length: poles }, (_, i) => {
        const x = x0 + step * (i + 0.5);
        return (
          <group key={i}>
            <Box c={[x, 0, side * depth * 0.1]} s={[step * 0.7, h, depth * 0.44]} />
            <Box c={[x, h * 0.38, side * depth * 0.52]} s={[step * 0.7, h * 0.18, depth * 0.32]} />
            <Box c={[x, -h * 0.38, side * depth * 0.52]} s={[step * 0.7, h * 0.18, depth * 0.32]} />
            <Box c={[x, 0, side * -depth * 0.2]} s={[step * 0.58, h * 0.74, depth * 0.32]} />
          </group>
        );
      })}
    </>
  );
}

/**
 * Long-stator laminated pack: core stack with lamination lines, three-phase
 * winding bars on the outer face, mounting brackets back to the beam web.
 */
export function StatorPack({ x0, x1, h = 620, depth = 240, side = 1 }: {
  x0: number; x1: number; h?: number; depth?: number; side?: 1 | -1;
}) {
  const len = x1 - x0;
  const lam = Math.max(6, Math.round(len / 900));
  return (
    <>
      <Box c={[(x0 + x1) / 2, 0, side * depth / 2]} s={[len, h, depth]} />
      {Array.from({ length: lam }, (_, i) => (
        <Box key={i} c={[x0 + (len * (i + 1)) / (lam + 1), 0, side * (depth + 10)]} s={[12, h * 1.02, 18]} />
      ))}
      {[-1, 0, 1].map((row) => (
        <Box key={row} c={[(x0 + x1) / 2, row * h * 0.3, side * (depth + 36)]} s={[len, h * 0.15, 46]} />
      ))}
      {Array.from({ length: Math.max(2, Math.round(len / 2400)) }, (_, i) => (
        <Box key={`b${i}`} c={[x0 + (len * (i + 0.5)) / Math.max(2, Math.round(len / 2400)), 0, side * -110]} s={[90, h * 0.7, 220]} />
      ))}
    </>
  );
}

/** Eddy-current gap probe: barrel + stud. */
export function SensorHead({ x, y, z }: { x: number; y: number; z: number }) {
  return (
    <>
      <Cyl c={[x, y, z]} r={36} len={90} axis="y" seg={16} />
      <Cyl c={[x, y - 58, z]} r={22} len={50} axis="y" seg={12} />
    </>
  );
}

/** Car body cross-section (y–z plane, YZ_X): rounded roof, straight flanks, wrap skirt. */
export function carShellShape(width: number, floorY: number, roofY: number, wall = 90) {
  return roundFrame(floorY, -width / 2, roofY, width / 2, 620, wall);
}

/** Box beam cross-section (y–z plane): T-flange Transrapid prestressed guideway girder. */
export function beamShape(width: number, height: number, wall = 200) {
  const s = roundRect(-height / 2, -width / 2, height / 2, width / 2, 90)();
  const inner = roundRect(-height / 2 + wall, -width / 2 + wall, height / 2 - wall, width / 2 - wall, 60)();
  s.holes.push(new THREE.Path(inner.getPoints(10)));
  return s;
}

/** Plug door leaf: proud framed panel with recessed window & threshold step. */
export function DoorLeaf({ x, y0, y1, z, side, w = 1280 }: { x: number; y0: number; y1: number; z: number; side: 1 | -1; w?: number }) {
  const h = y1 - y0;
  const zOut = z + side * 48;
  return (
    <>
      <Box c={[x, (y0 + y1) / 2, zOut]} s={[w, h, 84]} />
      <Box c={[x, y0 + h * 0.64, zOut + side * 34]} s={[w * 0.64, h * 0.42, 34]} />
      <Box c={[x, y0 + h * 0.08, zOut + side * 38]} s={[w * 0.92, 48, 42]} />
    </>
  );
}

/** Window band: proud framed panoramic glazing bays outside the 1850 mm flank so every window draws cleanly. */
export function WindowBand({ x0, x1, y0, y1, z, side, panes = 8 }: { x0: number; x1: number; y0: number; y1: number; z: number; side: 1 | -1; panes?: number }) {
  const step = (x1 - x0) / panes;
  const h = y1 - y0;
  const yc = (y0 + y1) / 2;
  return (
    <>
      <Box c={[(x0 + x1) / 2, y1 + 32, z + side * 24]} s={[x1 - x0 + 120, 44, 48]} />
      <Box c={[(x0 + x1) / 2, y0 - 32, z + side * 24]} s={[x1 - x0 + 120, 44, 48]} />
      {Array.from({ length: panes }, (_, i) => {
        const x = x0 + step * (i + 0.5);
        return (
          <group key={i}>
            <Box c={[x, yc, z + side * 22]} s={[step * 0.80, h, 44]} />
            <Box c={[x, yc, z + side * 42]} s={[step * 0.68, h * 0.78, 22]} />
          </group>
        );
      })}
    </>
  );
}

/** Livery cheatline: proud architectural beltline rib along the flank. */
export function Stripe({ x0, x1, y, z, h = 90 }: { x0: number; x1: number; y: number; z: number; h?: number }) {
  return <Box c={[(x0 + x1) / 2, y, z]} s={[x1 - x0, h, 44]} />;
}

/** Bogie wrap arm: C-shaped levitation yoke descending around the stator beam. */
export function WrapArm({ x, side, topY, botY, z0, z1 }: { x: number; side: 1 | -1; topY: number; botY: number; z0: number; z1: number }) {
  return (
    <>
      <Box c={[x, (topY + botY) / 2, side * (z0 + z1) / 2]} s={[480, topY - botY, z1 - z0]} />
      <Box c={[x, topY - 220, side * (z1 - 260)]} s={[580, 380, 620]} />
      <Box c={[x, botY + 180, side * (z0 + 120)]} s={[560, 260, 680]} />
    </>
  );
}
