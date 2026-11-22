import * as THREE from 'three';
import { M } from '../../scene/Part';
import { Box, Cyl, YZ_X, roundFrame, roundRect } from '../kit';

/**
 * Maglev procedural geometry kit. Millimetres, +x is the direction of travel
 * (nose forward), the car and beam centred on z = 0. Hard-edged topology only —
 * C-core magnet poles, laminated stator packs, extruded hollow shells and a box
 * beam — so InkRenderer finds every crease and the section cut opens the
 * cavities. Shapes extruded along x use YZ_X: shape x → world y, shape y → world z.
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

/**
 * Levitation / guidance magnet array: a row of C-core poles between x0 and x1,
 * each with two pole shoes and a coil block, opening toward ±z (side).
 */
export function MagnetArray({ x0, x1, poles, w = 300, h = 340, depth = 220, side = 1 }: {
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
            {/* Core body */}
            <Box c={[x, 0, side * depth * 0.1]} s={[step * 0.7, h, depth * 0.44]} />
            {/* Pole shoes facing the air gap */}
            <Box c={[x, h * 0.38, side * depth * 0.52]} s={[step * 0.7, h * 0.18, depth * 0.32]} />
            <Box c={[x, -h * 0.38, side * depth * 0.52]} s={[step * 0.7, h * 0.18, depth * 0.32]} />
            {/* Coil block on the back leg */}
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
  // shape x → world y (vertical), shape y → world z (lateral)
  return roundFrame(floorY, -width / 2, roofY, width / 2, 620, wall);
}

/** Box beam cross-section (y–z plane): hollow rectangle, chamfered corners. */
export function beamShape(width: number, height: number, wall = 200) {
  const s = roundRect(-height / 2, -width / 2, height / 2, width / 2, 110)();
  const inner = roundRect(-height / 2 + wall, -width / 2 + wall, height / 2 - wall, width / 2 - wall, 80)();
  s.holes.push(new THREE.Path(inner.getPoints(10)));
  return s;
}

/** Plug door leaf: panel with a window recess and a gasket step. */
export function DoorLeaf({ x, y0, y1, z, side, w = 1300 }: { x: number; y0: number; y1: number; z: number; side: 1 | -1; w?: number }) {
  const h = y1 - y0;
  return (
    <>
      <Box c={[x, (y0 + y1) / 2, z]} s={[w, h, 130]} />
      <Box c={[x, y0 + h * 0.66, z + side * 70]} s={[w * 0.62, h * 0.42, 40]} />
      <Box c={[x, y0 + h * 0.16, z + side * 72]} s={[w * 0.9, 26, 36]} />
    </>
  );
}

/** Window band: glazed panes with mullions along a flank. */
export function WindowBand({ x0, x1, y0, y1, z, side, panes = 8 }: { x0: number; x1: number; y0: number; y1: number; z: number; side: 1 | -1; panes?: number }) {
  const step = (x1 - x0) / panes;
  return (
    <>
      {Array.from({ length: panes }, (_, i) => {
        const x = x0 + step * (i + 0.5);
        return (
          <group key={i}>
            <Box c={[x, (y0 + y1) / 2, z]} s={[step * 0.82, y1 - y0, 60]} />
            <Box c={[x, (y0 + y1) / 2, z + side * 36]} s={[step * 0.72, (y1 - y0) * 0.82, 20]} />
          </group>
        );
      })}
    </>
  );
}

/** Livery cheatline: thin raised strip along a flank. */
export function Stripe({ x0, x1, y, z, h = 90 }: { x0: number; x1: number; y: number; z: number; h?: number }) {
  return <Box c={[(x0 + x1) / 2, y, z]} s={[x1 - x0, h, 26]} />;
}

/** Bogie wrap arm: box section from the car floor down beside the beam. */
export function WrapArm({ x, side, topY, botY, z0, z1 }: { x: number; side: 1 | -1; topY: number; botY: number; z0: number; z1: number }) {
  return (
    <>
      <Box c={[x, (topY + botY) / 2, side * (z0 + z1) / 2]} s={[420, topY - botY, z1 - z0]} />
      <Box c={[x, topY - 220, side * (z1 - 260)]} s={[520, 380, 620]} />
      <Box c={[x, botY + 240, side * (z1 - 200)]} s={[560, 220, 560]} />
    </>
  );
}
