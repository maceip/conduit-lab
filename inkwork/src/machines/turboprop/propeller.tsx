import { Part } from '../../scene/Part';
import { Callout } from '../../scene/Overlay';
import type { CameraDef, MachineDef, PartDef, StepDef, Vec3 } from '../types';
import { level } from '../kit';
import { BoltCircle, FlangeCollar } from './kit';
import { VariablePitchPropellerHub } from '../turboprop-kit';
import { ANNOTATIONS, TP } from './data';

const AY = TP.AY;
const U = TP.u;

/**
 * Sub-assembly A: propeller & pitch control (+x nose).
 * VariablePitchPropellerHub is sliced per element into the <Part>s: two spinner
 * pieces (cone + backplate) → four-arm hub → hydraulic pitch dome → 4 blades
 * (each exploding radially on its own).
 */

const PARTS: PartDef[] = [
  {
    id: 'spinner-front', index: 1, name: 'Spinner Cone (front piece)', en: 'Spinner Dome Front', role: 'Fairing',
    material: 'Glass fibre', description: 'Front half of the parabolic double-walled spinner (608 mm long), with a 2 mm anti-icing mat bonded inside.',
    explode: [620, 0, 0], stage: [0, 0.3],
  },
  {
    id: 'spinner-aft', index: 2, name: 'Spinner Bulkhead Backplate', en: 'Spinner Bulkhead Backplate', role: 'Fairing · load path',
    material: 'Glass fibre', description: 'Aft annular backplate (Ø660) mating with the cone, with four blade-root cutouts.',
    explode: [320, 0, 0], stage: [0.05, 0.35],
  },
  {
    id: 'pitch-lock-ring', index: 3, name: 'Pitch-Lock Bolt Ring', en: 'Pitch-Lock Bolt Ring', role: 'Locks pitch',
    material: '30CrMnSiA steel', description: 'Twelve M10 bolts lock the pitch piston around the circumference, 45 N·m preload; they back out 220 mm first.',
    explode: [540, 0, 0], stage: [0.1, 0.4],
  },
  {
    id: 'hub-spider', index: 4, name: 'Hub Spider', en: 'Prop Hub Spider', role: 'Torque path',
    material: '20CrMo forged steel', description: 'One-piece four-arm forging: central splined barrel plus four radial blade-root sockets; 12,000 h fatigue life.',
    explode: [180, 0, 0], stage: [0.35, 0.65],
  },
  {
    id: 'pitch-dome', index: 5, name: 'Pitch-Change Dome', en: 'Pitch-Change Dome', role: 'Feathering',
    material: '40Cr steel', description: 'Double-acting hydraulic cylinder (±25° travel) at 4 MPa, swinging the blades through the feathering shaft.',
    explode: [-260, 0, 0], stage: [0.35, 0.65],
  },
  {
    id: 'blade-1', index: 6, name: 'Blade 1', en: 'Blade 1', role: 'Thrust · up',
    material: 'TC4 titanium', description: '48°→16° washout twist, pitch axis at 42% chord, root counterweight clamp; radial fan +1.15u.',
    explode: [0, 520, 0], stage: [0.6, 0.9],
  },
  {
    id: 'blade-2', index: 7, name: 'Blade 2', en: 'Blade 2', role: 'Thrust · down',
    material: 'TC4 titanium', description: 'Same as blade 1 at 180°; root flange on 6×M16 bolts, centrifugal load ≈ 68 kN.',
    explode: [0, -520, 0], stage: [0.6, 0.9],
  },
  {
    id: 'blade-3', index: 8, name: 'Blade 3', en: 'Blade 3', role: 'Thrust · right',
    material: 'TC4 titanium', description: 'At 90°, counterweight in the root cavity; lightning strip along the leading edge for 40% of the chord.',
    explode: [0, 0, 520], stage: [0.62, 0.92],
  },
  {
    id: 'blade-4', index: 9, name: 'Blade 4', en: 'Blade 4', role: 'Thrust · left',
    material: 'TC4 titanium', description: 'At 270°; four blades spaced 90° apart, balanced to G2.5.',
    explode: [0, 0, -520], stage: [0.62, 0.92],
  },
];

const STEPS: StepDef[] = [
  {
    title: 'Propeller Group', en: 'Propeller Group',
    body: 'Four-blade constant-speed propeller: the four-arm hub carries the blade-root sockets, the hydraulic pitch cylinder sits behind, and the 12-bolt lock ring keeps pitch from creeping.',
    state: { explode: 0, section: true, running: false, select: 'hub-spider', focus: null },
  },
  {
    title: 'Exploded', en: 'Exploded',
    body: 'Spinner pieces and the lock ring leave first, then the hub and pitch dome part, and the four blades fan out radially by 1.15u each.',
    state: { explode: 1, section: false, running: false, select: null, focus: null },
  },
];

const CAMERA: CameraDef = {
  target: [1250, AY, 0],
  offset: [2300, 1000, 2700],
  orthoDistance: 8200,
  exploded: { target: [1500, AY, 0], scale: 1.6 },
};

/** The same propeller assembly, sliced by show/bladeIndices into each <Part>. */
const HubSlice = ({ show, bladeIndices }: { show: Parameters<typeof VariablePitchPropellerHub>[0]['show']; bladeIndices?: number[] }) => (
  <group position={[TP.hubX, AY, 0]}>
    <group scale={U}>
      <VariablePitchPropellerHub hubR={0.625} bladeTipR={2.7} show={show} bladeIndices={bladeIndices} />
    </group>
  </group>
);

export function PropellerGroup() {
  return (
    <group>
      <Part id="spinner-front">
        <HubSlice show={{ spinner: true }} />
        <Callout id="spinner-front" p={[1420, AY + 220, 60]} />
      </Part>
      <Part id="spinner-aft">
        <HubSlice show={{ backplate: true }} />
        <Callout id="spinner-aft" p={[980, AY + 250, 60]} />
      </Part>
      <Part id="pitch-lock-ring">
        <FlangeCollar k="tp-a-lock" x={TP.lockRingX} r={252} thick={36} bossCount={12} bossR={22} />
        <BoltCircle x={TP.lockRingX} r={272} count={12} d={20} len={52} />
        <Callout id="pitch-lock-ring" p={[TP.lockRingX, AY + 310, 80]} />
      </Part>
      <Part id="hub-spider">
        <HubSlice show={{ hub: true }} />
        <Callout id="hub-spider" p={[TP.hubX, AY + 260, 110]} />
      </Part>
      <Part id="pitch-dome">
        <HubSlice show={{ dome: true }} />
        <Callout id="pitch-dome" p={[TP.hubX - 120, AY - 190, 80]} />
      </Part>
      {[0, 1, 2, 3].map((i) => (
        <Part key={i} id={`blade-${i + 1}`}>
          <HubSlice show={{ blades: true }} bladeIndices={[i]} />
          <Callout id={`blade-${i + 1}`} p={[TP.hubX + (i === 0 ? 240 : i === 1 ? -240 : 80), AY + (i === 0 ? 820 : i === 1 ? -820 : 120), i === 2 ? 820 : i === 3 ? -820 : 120]} />
        </Part>
      ))}
    </group>
  );
}

export const propeller: MachineDef = level({
  id: 'turboprop/propeller',
  parent: 'turboprop',
  unit: 10 / 2400,
  bounds: [[820, AY - 1200, -1200], [1620, AY + 1200, 1200]],
  name: 'Propeller & Pitch Control',
  en: 'Propeller & Pitch Control',
  subtitle: 'Sub-assembly A · constant-speed propeller',
  summary: '9 parts · hydraulic pitch ±25°, 12-bolt lock ring',
  drawingNo: 'GW-TP-A',
  scale: '1 : 8',
  parts: PARTS,
  annotations: ANNOTATIONS,
  boltSets: {},
  neighbours: {
    'hub-spider': ['blade-1', 'blade-2', 'blade-3', 'blade-4', 'hub-spider'],
    'pitch-lock-ring': ['spinner-front', 'spinner-aft', 'pitch-lock-ring'],
  },
  guides: [
    { stage: 'blade-1', origin: [TP.hubX, AY + 500, 0] },
    { stage: 'hub-spider', origin: [TP.hubX, AY + 200, 0] },
    { stage: 'spinner-front', origin: [1400, AY + 120, 0] },
  ],
  centreLines: [[[820, AY, 0], [1640, AY, 0], TP.propR]] as Array<[Vec3, Vec3, number?]>,
  steps: STEPS,
  camera: CAMERA,
  Model: PropellerGroup,
});
