import * as THREE from 'three';
import { M } from '../../scene/Part';
import { Box, Cyl, YZ_X, roundFrame, roundRect } from '../kit';

/**
 * Maglev procedural geometry kit. Millimetres, +x is the direction of travel
 * (nose forward), the car and beam centred on z = 0. Hard-edged creases +
 * multi-station lofted aerodynamic nose so InkRenderer draws unmistakable
 * Transrapid TR08 bullet-train silhouettes, cab glazing, panoramic windows,
 * wrap-around levitation skirts, and twin hammerhead viaduct piers.
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

/** Parametric Transrapid TR08 aerodynamic nose station profile at u in [0, 1]. */
function noseStation(u: number, floorY: number, roofY: number, halfW: number, inset = 0): Array<[number, number]> {
  const ease = u * u * (3 - 2 * u);
  // Planform half-width: full 1850 mm at u=0, smooth parabolic-elliptic taper to spatulate prow
  const wScale = u < 0.08 ? 1 : Math.pow(Math.max(0.06, 1 - Math.pow((u - 0.08) / 0.92, 1.65)), 0.56);
  const w = Math.max(160, halfW * wScale - inset);

  // Upper profile: rounded roof -> raked 23° cab windshield -> sleek low duckbill hood -> splitter prow
  let yTop: number;
  if (u < 0.24) {
    const t = u / 0.24;
    yTop = roofY - 260 * (t * t);
  } else if (u < 0.68) {
    const t = (u - 0.24) / 0.44;
    yTop = (roofY - 260) - 2180 * (t * (0.85 + 0.15 * t));
  } else {
    const t = (u - 0.68) / 0.32;
    yTop = (roofY - 2440) - 1060 * (1 - Math.pow(1 - t, 1.5));
  }
  yTop -= inset;

  // Lower skirt & prow chin sweep
  const yBot = (floorY - 380) + 920 * Math.pow(ease, 1.35) + inset * 0.8;
  const h = Math.max(260, yTop - yBot);
  const yChine = yBot + h * (0.28 + 0.14 * ease);
  const yWaist = yBot + h * (0.58 - 0.06 * ease);
  const yShoulder = yTop - h * (0.16 * (1 - 0.45 * ease));

  // Cross-section ring in (y, z) around symmetry plane z = 0 (counter-clockwise looking -x)
  return [
    [yBot, 0],
    [yBot, w * 0.76],
    [yChine, w],
    [yWaist, w * 0.99],
    [yShoulder, w * 0.84],
    [yTop, w * 0.42],
    [yTop, 0],
    [yTop, -w * 0.42],
    [yShoulder, -w * 0.84],
    [yWaist, -w * 0.99],
    [yChine, -w],
    [yBot, -w * 0.76],
  ];
}

function buildLoftedNose(x0: number, x1: number, floorY: number, roofY: number, halfW: number): THREE.BufferGeometry {
  const key = `mg-aero-nose-${x0}-${x1}`;
  const cached = shellCache.get(key);
  if (cached) return cached;

  const steps = 18;
  const outerRings: Array<{ x: number; pts: Array<[number, number]> }> = [];
  const innerRings: Array<{ x: number; pts: Array<[number, number]> }> = [];
  for (let i = 0; i <= steps; i += 1) {
    const u = i / steps;
    const x = x0 + (x1 - x0) * u;
    outerRings.push({ x, pts: noseStation(u, floorY, roofY, halfW, 0) });
    innerRings.push({ x: Math.min(x, x1 - 110), pts: noseStation(Math.min(u, 0.96), floorY, roofY, halfW, 110) });
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

  const N = outerRings[0].pts.length;
  for (let i = 0; i < steps; i += 1) {
    const r0 = outerRings[i];
    const r1 = outerRings[i + 1];
    const in0 = innerRings[i];
    const in1 = innerRings[i + 1];
    for (let j = 0; j < N; j += 1) {
      const jn = (j + 1) % N;
      const p00: [number, number, number] = [r0.x, r0.pts[j][0], r0.pts[j][1]];
      const p01: [number, number, number] = [r0.x, r0.pts[jn][0], r0.pts[jn][1]];
      const p11: [number, number, number] = [r1.x, r1.pts[jn][0], r1.pts[jn][1]];
      const p10: [number, number, number] = [r1.x, r1.pts[j][0], r1.pts[j][1]];
      pushQuad(p00, p10, p11, p01);

      // Inner shell wall (reversed winding) so section cut shows real shell thickness
      const q00: [number, number, number] = [in0.x, in0.pts[j][0], in0.pts[j][1]];
      const q01: [number, number, number] = [in0.x, in0.pts[jn][0], in0.pts[jn][1]];
      const q11: [number, number, number] = [in1.x, in1.pts[jn][0], in1.pts[jn][1]];
      const q10: [number, number, number] = [in1.x, in1.pts[j][0], in1.pts[j][1]];
      pushQuad(q00, q01, q11, q10);
    }
  }

  // Close front prow cap and aft ring collar
  const tip = outerRings[steps];
  const tipCenter: [number, number, number] = [x1 + 90, (tip.pts[0][0] + tip.pts[6][0]) * 0.5, 0];
  for (let j = 0; j < N; j += 1) {
    const jn = (j + 1) % N;
    pushTri(
      [tip.x, tip.pts[j][0], tip.pts[j][1]],
      tipCenter,
      [tip.x, tip.pts[jn][0], tip.pts[jn][1]],
    );
    // Aft collar at x0
    const o0 = outerRings[0];
    const i0 = innerRings[0];
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

/** Sculpted 7.2 m Transrapid TR08 aerodynamic duckbill nose + lower headlight pods. */
export function AeroNose({ x0, x1, floorY, roofY, halfW }: {
  x0: number; x1: number; floorY: number; roofY: number; halfW: number;
}) {
  return (
    <>
      <M clip geo={buildLoftedNose(x0, x1, floorY, roofY, halfW)} />
      {/* Flush twin LED headlight housings on lower nose cheeks */}
      <Box c={[x1 - 1350, floorY + 860, 860]} s={[780, 180, 340]} r={[0, -0.32, -0.22]} />
      <Box c={[x1 - 1350, floorY + 860, -860]} s={[780, 180, 340]} r={[0, 0.32, -0.22]} />
    </>
  );
}

/** Flush curved wrap-around cockpit windshield conformed to the upper nose slope (u = 0.25..0.66). */
function buildFlushCanopy(x0: number, x1: number, floorY: number, roofY: number, halfW: number): THREE.BufferGeometry {
  const key = `mg-flush-canopy-${x0}-${x1}`;
  const cached = shellCache.get(key);
  if (cached) return cached;

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

  const uStart = 0.25;
  const uEnd = 0.65;
  const segs = 10;
  const arcPts = 9;

  const ringAt = (u: number, lift: number): Array<[number, number, number]> => {
    const x = x0 + (x1 - x0) * u;
    const st = noseStation(u, floorY, roofY, halfW, 0);
    const yCrown = st[6][0] + lift;
    const ySill = st[4][0] - 110 + lift * 0.5;
    const wMax = Math.abs(st[4][1]) * 0.9 + lift * 0.4;
    const out: Array<[number, number, number]> = [];
    for (let k = 0; k <= arcPts; k += 1) {
      const s = (k / arcPts) * 2 - 1; // -1 .. +1
      const z = s * wMax;
      const y = yCrown - (yCrown - ySill) * (s * s);
      out.push([x, y, z]);
    }
    return out;
  };

  for (let i = 0; i < segs; i += 1) {
    const u0 = uStart + (uEnd - uStart) * (i / segs);
    const u1 = uStart + (uEnd - uStart) * ((i + 1) / segs);
    const top0 = ringAt(u0, 38);
    const top1 = ringAt(u1, 38);
    const bot0 = ringAt(u0, -20);
    const bot1 = ringAt(u1, -20);
    for (let k = 0; k < arcPts; k += 1) {
      pushQuad(top0[k], top0[k + 1], top1[k + 1], top1[k]);
      pushQuad(bot0[k], bot1[k], bot1[k + 1], bot0[k + 1]);
    }
    // Side edges of canopy frame
    pushQuad(bot0[0], top0[0], top1[0], bot1[0]);
    pushQuad(top0[arcPts], bot0[arcPts], bot1[arcPts], top1[arcPts]);
    if (i === 0) {
      for (let k = 0; k < arcPts; k += 1) pushQuad(bot0[k], bot0[k + 1], top0[k + 1], top0[k]);
    }
    if (i === segs - 1) {
      for (let k = 0; k < arcPts; k += 1) pushQuad(top1[k], top1[k + 1], bot1[k + 1], bot1[k]);
    }
  }

  const geo = new THREE.BufferGeometry();
  geo.setAttribute('position', new THREE.Float32BufferAttribute(positions, 3));
  geo.computeVertexNormals();
  shellCache.set(key, geo);
  return geo;
}

export function FlushWindshield({ x0, x1, floorY, roofY, halfW }: {
  x0: number; x1: number; floorY: number; roofY: number; halfW: number;
}) {
  return <M clip geo={buildFlushCanopy(x0, x1, floorY, roofY, halfW)} />;
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
      {/* Continuous continuous panoramic glazing belt frame */}
      <Box c={[(x0 + x1) / 2, y1 + 32, z + side * 24]} s={[x1 - x0 + 120, 44, 48]} />
      <Box c={[(x0 + x1) / 2, y0 - 32, z + side * 24]} s={[x1 - x0 + 120, 44, 48]} />
      {Array.from({ length: panes }, (_, i) => {
        const x = x0 + step * (i + 0.5);
        return (
          <group key={i}>
            {/* Outer window bezel */}
            <Box c={[x, yc, z + side * 22]} s={[step * 0.80, h, 44]} />
            {/* Stepped inner glazing pane for crisp double-line crease */}
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
      {/* Inward lower hook reaching beneath the stator pack */}
      <Box c={[x, botY + 180, side * (z0 + 120)]} s={[560, 260, 680]} />
    </>
  );
}
