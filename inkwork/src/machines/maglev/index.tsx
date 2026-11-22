import { useRef, type ReactNode } from 'react';
import { useFrame } from '@react-three/fiber';
import * as THREE from 'three';
import { Part } from '../../scene/Part';
import { Callout } from '../../scene/Overlay';
import { useStudio } from '../../state';
import type { MachineDef } from '../types';
import { Box, Turn, level, poly, tube } from '../kit';
import { DoorLeaf, MagnetArray, ProfileShell, SensorHead, StatorPack, Stripe, WrapArm, WindowBand, beamShape } from './kit';
import { ANNOTATIONS, BOM, BOLT_SETS, CAMERA, CENTRE_LINES, DIMENSIONS, GUIDES, MG, NEIGHBOURS, PARTS, STEPS } from './data';
import { guidanceOffset, levitationGap } from './kinematics';
import { carbody } from './carbody';
import { bogie } from './bogie';
import { propulsion } from './propulsion';
import { guideway } from './guideway';
import { power } from './power';
import { braking } from './braking';

const F = MG.floorY;
const R = MG.roofY;

/** Shared animation phase; only advances while running. */
export const mgMotion = { phase: 0, gap: 0 };

export function MaglevDriver() {
  useFrame((_, rawDt) => {
    const run = useStudio.getState().running;
    if (run) mgMotion.phase += Math.min(rawDt, 0.05) * 1.2;
    // Ease the levitation gap open when running, closed when parked.
    const target = run ? 1 : 0;
    const k = 1 - Math.exp(-Math.min(rawDt, 0.05) * 2.2);
    mgMotion.gap += (target - mgMotion.gap) * k;
  }, -1);
  return null;
}

/** The vehicle lifts on its magnets and wanders ±1 mm on its guidance loop. */
function Levitating({ children }: { children: ReactNode }) {
  const ref = useRef<THREE.Group>(null);
  useFrame(() => {
    if (!ref.current) return;
    ref.current.position.y = levitationGap(mgMotion.gap);
    ref.current.position.z = guidanceOffset(mgMotion.phase) * mgMotion.gap;
  });
  return <group ref={ref}>{children}</group>;
}

/** Half car-body cross-section (open at z = 0), shape x → y, shape y → z. */
function halfShellShape(side: 1 | -1) {
  const w = (MG.carWidth / 2) * side;
  const pts: Array<[number, number]> = [
    [F, 0], [F, w], [F + 240, w], [R - 700, w], [R - 300, w * 0.92], [R, w * 0.5], [R, 0],
  ];
  const inner: Array<[number, number]> = pts.map(([y, z]) => [y + (y < R - 700 ? 90 : -70), z - side * 90]);
  return poly([...pts, ...inner.reverse()]);
}

/* ── Track (fixed) ────────────────────────────────────────────────── */

function BeamShell() {
  return (
    <Part id="beam-shell">
      <ProfileShell k="beam" shape={() => beamShape(MG.beamW, MG.beamH)} x0={MG.beamX0} x1={MG.beamX1} y={MG.beamBotY + MG.beamH / 2} />
      {/* Walkway edges along the top flanges */}
      <Box c={[(MG.beamX0 + MG.beamX1) / 2, MG.beamTopY + 40, MG.beamW / 2 - 140]} s={[MG.beamX1 - MG.beamX0, 80, 260]} />
      <Box c={[(MG.beamX0 + MG.beamX1) / 2, MG.beamTopY + 40, -(MG.beamW / 2 - 140)]} s={[MG.beamX1 - MG.beamX0, 80, 260]} />
      <Callout id="beam-shell" p={[-3000, MG.beamTopY + 200, 0]} />
    </Part>
  );
}

function PierSegment() {
  return (
    <Part id="pier-segment">
      <Box c={[11500, 600, 0]} s={[1800, 1200, 2200]} />
      <Box c={[11500, 1180, 0]} s={[3200, 240, 2600]} />
      {/* Spherical bearing pockets */}
      <Box c={[11500, 1310, 0]} s={[2600, 120, 2000]} />
      <Callout id="pier-segment" p={[11500, 300, 1200]} />
    </Part>
  );
}

function TrackGear() {
  return (
    <>
      <Part id="stator-pack-left">
        <group position={[0, 2400, 1250]}>
          <StatorPack x0={2000} x1={22000} side={1} />
        </group>
        <Callout id="stator-pack-left" p={[12000, 2750, 1500]} />
      </Part>
      <Part id="stator-pack-right">
        <group position={[0, 2400, -1250]}>
          <StatorPack x0={2000} x1={22000} side={-1} />
        </group>
        <Callout id="stator-pack-right" p={[12000, 2750, -1500]} />
      </Part>
      <Part id="guidance-rail-left">
        <Box c={[12000, 3080, 1520]} s={[22000, 140, 160]} />
        <Box c={[12000, 3170, 1520]} s={[22000, 40, 220]} />
        <Callout id="guidance-rail-left" p={[6000, 3220, 1520]} />
      </Part>
      <Part id="guidance-rail-right">
        <Box c={[12000, 3080, -1520]} s={[22000, 140, 160]} />
        <Box c={[12000, 3170, -1520]} s={[22000, 40, 220]} />
        <Callout id="guidance-rail-right" p={[6000, 3220, -1520]} />
      </Part>
      <Part id="brake-rail">
        <Box c={[12000, 1950, 1430]} s={[22000, 220, 120]} />
        <Box c={[12000, 1950, -1430]} s={[22000, 220, 120]} />
        <Callout id="brake-rail" p={[18000, 1950, 1500]} />
      </Part>
    </>
  );
}

/* ── Vehicle (levitates) ──────────────────────────────────────────── */

function Body() {
  return (
    <>
      <Part id="nose-cone">
        {/* Streamlined nose: revolved shell from the cab face to the tip */}
        <Turn
          k="mg-nose"
          axis="x"
          p={[0, F + 1650, 0]}
          profile={[
            [30, 27200], [620, 27060], [1180, 26700], [1620, 26100], [1830, 25300], [1860, 24300], [1860, 23950],
            [1770, 23950], [1770, 25240], [1560, 26020], [1120, 26600], [580, 26960], [10, 27110],
          ]}
          seg={56}
        />
        <Callout id="nose-cone" p={[25800, F + 1600, 400]} />
      </Part>
      <Part id="windshield">
        <Box c={[25350, F + 2450, 0]} s={[1500, 900, 1750]} r={[0, 0, -0.32]} />
        <Box c={[25350, F + 2450, 0]} s={[1560, 200, 1810]} r={[0, 0, -0.32]} />
        <Callout id="windshield" p={[25350, F + 2950, 700]} />
      </Part>
      <Part id="door-left">
        <DoorLeaf x={MG.doorFX} y0={F + 120} y1={F + 2170} z={1808} side={1} />
        <DoorLeaf x={MG.doorRX} y0={F + 120} y1={F + 2170} z={1808} side={1} />
        <Callout id="door-left" p={[MG.doorFX, F + 1200, 1900]} />
      </Part>
      <Part id="door-right">
        <DoorLeaf x={MG.doorFX} y0={F + 120} y1={F + 2170} z={-1808} side={-1} />
        <DoorLeaf x={MG.doorRX} y0={F + 120} y1={F + 2170} z={-1808} side={-1} />
        <Callout id="door-right" p={[MG.doorFX, F + 1200, -1900]} />
      </Part>
      <Part id="skirt-left">
        <Box c={[13500, F - 380, 1560]} s={[21600, 760, 560]} />
        <Box c={[13500, F - 80, 1560]} s={[21600, 160, 640]} />
        <Callout id="skirt-left" p={[15000, F - 420, 1750]} />
      </Part>
      <Part id="skirt-right">
        <Box c={[13500, F - 380, -1560]} s={[21600, 760, 560]} />
        <Box c={[13500, F - 80, -1560]} s={[21600, 160, 640]} />
        <Callout id="skirt-right" p={[15000, F - 420, -1750]} />
      </Part>
      <Part id="roof-fairing">
        <Box c={[14500, R + 120, 0]} s={[3200, 340, 2300]} />
        {[0, 1, 2, 3, 4].map((i) => (
          <Box key={i} c={[13300 + i * 560, R + 310, 0]} s={[220, 60, 2100]} />
        ))}
        <Callout id="roof-fairing" p={[14500, R + 340, 600]} />
      </Part>
    </>
  );
}

function Shells() {
  return (
    <>
      <Part id="side-shell-left">
        <ProfileShell k="shell-l" shape={halfShellShape(1)} x0={3000} x1={25500} />
        <WindowBand x0={4200} x1={24200} y0={F + 1500} y1={F + 2350} z={1812} side={1} panes={10} />
        <Stripe x0={3000} x1={25500} y={F + 1350} z={1846} h={110} />
        <Stripe x0={3000} x1={25500} y={F + 1180} z={1846} h={70} />
        <Callout id="side-shell-left" p={[10000, F + 2400, 1850]} />
      </Part>
      <Part id="side-shell-right">
        <ProfileShell k="shell-r" shape={halfShellShape(-1)} x0={3000} x1={25500} />
        <WindowBand x0={4200} x1={24200} y0={F + 1500} y1={F + 2350} z={-1812} side={-1} panes={10} />
        <Stripe x0={3000} x1={25500} y={F + 1350} z={-1846} h={110} />
        <Stripe x0={3000} x1={25500} y={F + 1180} z={-1846} h={70} />
        <Callout id="side-shell-right" p={[10000, F + 2400, -1850]} />
      </Part>
    </>
  );
}

function Bogies() {
  return (
    <>
      <Part id="bogie-front">
        <WrapArm x={MG.bogieFX} side={1} topY={F - 100} botY={2250} z0={1250} z1={2050} />
        <WrapArm x={MG.bogieFX} side={-1} topY={F - 100} botY={2250} z0={1250} z1={2050} />
        <Box c={[MG.bogieFX, F - 200, 0]} s={[1300, 320, 3200]} />
        <Callout id="bogie-front" p={[MG.bogieFX, 2150, 1600]} />
      </Part>
      <Part id="bogie-rear">
        <WrapArm x={MG.bogieRX} side={1} topY={F - 100} botY={2250} z0={1250} z1={2050} />
        <WrapArm x={MG.bogieRX} side={-1} topY={F - 100} botY={2250} z0={1250} z1={2050} />
        <Box c={[MG.bogieRX, F - 200, 0]} s={[1300, 320, 3200]} />
        <Callout id="bogie-rear" p={[MG.bogieRX, 2150, -1600]} />
      </Part>
    </>
  );
}

function Magnets() {
  const lev = (id: string, x: number, side: 1 | -1) => (
    <Part id={id}>
      <group position={[x, 2330, side * 1620]}>
        <MagnetArray x0={-850} x1={850} poles={12} side={side} />
      </group>
      <Callout id={id} p={[x, 2250, side * 1750]} />
    </Part>
  );
  const guid = (id: string, x: number, side: 1 | -1) => (
    <Part id={id}>
      <group position={[x, 2760, side * 1720]}>
        <MagnetArray x0={-650} x1={650} poles={8} w={220} h={260} depth={180} side={side} />
      </group>
      <Callout id={id} p={[x, 2860, side * 1850]} />
    </Part>
  );
  return (
    <>
      {lev('lev-magnet-fl', MG.bogieFX, 1)}
      {lev('lev-magnet-fr', MG.bogieFX, -1)}
      {lev('lev-magnet-rl', MG.bogieRX, 1)}
      {lev('lev-magnet-rr', MG.bogieRX, -1)}
      {guid('guid-magnet-fl', MG.bogieFX, 1)}
      {guid('guid-magnet-fr', MG.bogieFX, -1)}
      {guid('guid-magnet-rl', MG.bogieRX, 1)}
      {guid('guid-magnet-rr', MG.bogieRX, -1)}
    </>
  );
}

function Equipment() {
  return (
    <>
      <Part id="gap-sensors">
        {[MG.bogieFX, MG.bogieRX].map((x) => (
          <group key={x}>
            <SensorHead x={x - 700} y={2260} z={1450} />
            <SensorHead x={x + 700} y={2260} z={1450} />
            <SensorHead x={x - 700} y={2260} z={-1450} />
            <SensorHead x={x + 700} y={2260} z={-1450} />
          </group>
        ))}
        <Callout id="gap-sensors" p={[MG.bogieFX + 700, 2150, 700]} />
      </Part>
      <Part id="brake-magnets">
        {[MG.bogieFX, MG.bogieRX].map((x) => (
          <group key={x}>
            <group position={[x, 1980, 1620]}><MagnetArray x0={-560} x1={560} poles={4} w={240} h={240} depth={160} side={1} /></group>
            <group position={[x, 1980, -1620]}><MagnetArray x0={-560} x1={560} poles={4} w={240} h={240} depth={160} side={-1} /></group>
          </group>
        ))}
        <Callout id="brake-magnets" p={[MG.bogieRX, 1900, -1750]} />
      </Part>
      <Part id="battery-box">
        <Box c={[9000, 2950, 0]} s={[3200, 720, 2400]} />
        <Box c={[9000, 3340, 0]} s={[3260, 90, 2460]} />
        <Callout id="battery-box" p={[9000, 2850, 1100]} />
      </Part>
      <Part id="converter-cabinet">
        <Box c={[16000, 2820, -900]} s={[2400, 950, 1250]} />
        <Box c={[16000, 3320, -900]} s={[2460, 80, 1310]} />
        <Callout id="converter-cabinet" p={[16000, 2750, -1450]} />
      </Part>
      <Part id="hvac-unit">
        <Box c={[13000, 7730, 0]} s={[3600, 420, 2600]} />
        {[0, 1, 2, 3].map((i) => (
          <Box key={i} c={[11900 + i * 720, 7960, 0]} s={[200, 70, 2300]} />
        ))}
        <Callout id="hvac-unit" p={[13000, 8060, 800]} />
      </Part>
    </>
  );
}

export function Maglev() {
  return (
    <group>
      <BeamShell />
      <PierSegment />
      <TrackGear />
      <Levitating>
        <Body />
        <Shells />
        <Bogies />
        <Magnets />
        <Equipment />
      </Levitating>
    </group>
  );
}

export const maglev: MachineDef = level({
  id: 'maglev',
  unit: 10 / 36000,
  bounds: [[MG.beamX0, 0, -2600], [MG.noseX + 400, 8400, 2600]],
  name: 'Shanghai SMT Maglev',
  en: 'Shanghai SMT Maglev (Transrapid TR08)',
  subtitle: 'Assembly · EMS levitation · long-stator LSM · half-section',
  summary: '31 parts · 6 sub-assemblies · 10 mm levitation gap on a linear-motor guideway',
  drawingNo: 'GW-MV-00',
  scale: '1 : 100',
  parts: PARTS,
  boltSets: BOLT_SETS,
  neighbours: NEIGHBOURS,
  guides: GUIDES,
  centreLines: CENTRE_LINES,
  steps: STEPS,
  camera: CAMERA,
  Model: Maglev,
  Driver: MaglevDriver,
  children: {
    'nose-cone': 'maglev/carbody',
    'side-shell-left': 'maglev/carbody',
    'bogie-front': 'maglev/bogie',
    'lev-magnet-fl': 'maglev/bogie',
    'stator-pack-left': 'maglev/propulsion',
    'beam-shell': 'maglev/guideway',
    'battery-box': 'maglev/power',
    'brake-rail': 'maglev/braking',
    'brake-magnets': 'maglev/braking',
  },
  dimensions: DIMENSIONS,
  bom: BOM,
  annotations: ANNOTATIONS,
});

/** The six sub-assemblies (A–F), spread into ALL in machines/index.ts. */
export const MAGLEV_LEVELS = [carbody, bogie, propulsion, guideway, power, braking];
