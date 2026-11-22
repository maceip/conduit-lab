import { Part } from '../../scene/Part';
import { Callout } from '../../scene/Overlay';
import type { CameraDef, MachineDef, PartDef, StepDef, Vec3 } from '../types';
import { Box, Cyl, level, Turn, tube } from '../kit';
import { FlangeCollar, GearDisc, Ribs, Shell } from './kit';
import { ANNOTATIONS, TP } from './data';

const AY = TP.AY;

/**
 * Sub-assembly C: accessory & air intake section — annular intake screen, front
 * bearing housing, accessory bevel gear, starter-generator pad, fuel pump housing.
 */

const PARTS: PartDef[] = [
  {
    id: 'inlet-screen', index: 1, name: 'Annular Inlet Screen', en: 'Annular Inlet Screen', role: 'FOD screen',
    material: 'Stainless mesh', description: 'Annular radial screen (416 mm inner, 544 mm outer) with 18 radial ribs and 4 mm mesh; anti-icing hot air feeds the annulus.',
    explode: [360, 0, 0], stage: [0, 0.3],
  },
  {
    id: 'front-bearing-housing', index: 2, name: 'Front Bearing Housing', en: 'Front Bearing Housing', role: 'Rotor support',
    material: '40CrNiMoA steel', description: 'Holds a double-row ball bearing (Ø85 bore) with four oil jets; screens at the front, compressor case aft.',
    explode: [180, 0, 0], stage: [0.15, 0.45],
  },
  {
    id: 'bevel-drive-gear', index: 3, name: 'Accessory Bevel Gear', en: 'Accessory Bevel Gear', role: 'Right-angle drive',
    material: '18Cr2Ni4WA steel', description: '27-tooth bevel pair (90° shaft angle) turning horizontal shaft power down to the vertical accessory shaft at 6,000 r/min.',
    explode: [0, -360, 0], stage: [0.5, 0.78],
  },
  {
    id: 'starter-gen-pad', index: 4, name: 'Starter-Generator Pad', en: 'Starter-Generator Pad', role: 'Start · generate',
    material: '2A14 aluminium', description: 'ISO 5 mounting pad (4×M12): 180 N·m of cranking torque in, 9 kW of generating power out.',
    explode: [-180, -420, 0], stage: [0.52, 0.8],
  },
  {
    id: 'fuel-pump-housing', index: 5, name: 'HP Fuel Pump Housing', en: 'HP Fuel Pump Housing', role: 'Fuel pump',
    material: '2A14 aluminium', description: 'Plunger pump housing (7 MPa outlet) on a 12-tooth spline, mounted coaxially with the governor.',
    explode: [-40, -420, 0], stage: [0.54, 0.82],
  },
];

const STEPS: StepDef[] = [
  {
    title: 'Accessory Section', en: 'Accessory Section',
    body: 'Air enters around the annular screen and turns axial through the front bearing housing windows; below, the bevel pair leads power to the starter-generator and the high-pressure fuel pump.',
    state: { explode: 0, section: true, running: false, select: 'inlet-screen', focus: null },
  },
  {
    title: 'Exploded', en: 'Exploded',
    body: 'The screen leaves first, then the bearing housing; the three accessories pull out radially along −y and the bevel gear last.',
    state: { explode: 1, section: false, running: false, select: null, focus: null },
  },
];

const CAMERA: CameraDef = {
  target: [280, AY - 120, 0],
  offset: [900, 460, 1100],
  orthoDistance: 3000,
  exploded: { target: [280, AY - 160, 0], scale: 1.7 },
};

export function AirflowGroup() {
  return (
    <group>
      <Part id="inlet-screen">
        <Turn k="tp-c-inout" axis="x" p={[0, AY, 0]} profile={tube(272, 296, 328, 12)} />
        <Turn k="tp-c-inin" axis="x" p={[0, AY, 0]} profile={tube(208, 296, 328, 12)} />
        <Ribs x={312} r0={214} r1={268} count={18} thick={10} />
        <Callout id="inlet-screen" p={[312, AY + 320, 100]} />
      </Part>
      <Part id="front-bearing-housing">
        <Shell k="tp-c-brg" t={14} profile={[[158, 240], [158, 318]]} />
        <FlangeCollar k="tp-c-brgfl" x={252} r={168} thick={24} bossCount={8} bossR={14} />
        <Turn k="tp-c-brgrace" axis="x" p={[0, AY, 0]} profile={tube(120, 252, 306, 12)} />
        <Callout id="front-bearing-housing" p={[280, AY + 210, 90]} />
      </Part>
      <Part id="bevel-drive-gear">
        <group position={[320, AY - 300, 0]}>
          <GearDisc k="tp-c-bevel" teeth={27} pitchR={72} addendum={6} bore={26} thick={34} />
          <Cyl c={[0, 0, 0]} r={26} len={60} axis="x" seg={16} />
        </group>
        <group position={[320, AY - 366, 0]} rotation={[0, 0, Math.PI / 2]}>
          <GearDisc k="tp-c-bevel2" teeth={27} pitchR={72} addendum={6} bore={26} thick={34} />
        </group>
        <Callout id="bevel-drive-gear" p={[320, AY - 330, 120]} />
      </Part>
      <Part id="starter-gen-pad">
        <Box c={[220, AY - 352, 0]} s={[150, 96, 150]} />
        <FlangeCollar k="tp-c-padfl" x={220} r={92} thick={22} bossCount={6} bossR={12} />
        <Callout id="starter-gen-pad" p={[220, AY - 430, 120]} />
      </Part>
      <Part id="fuel-pump-housing">
        <Cyl c={[220, AY - 430, 0]} r={78} len={110} axis="y" seg={24} />
        <Cyl c={[220, AY - 496, 0]} r={52} len={40} axis="y" seg={18} />
        <Callout id="fuel-pump-housing" p={[220, AY - 520, -90]} />
      </Part>
    </group>
  );
}

export const airflow: MachineDef = level({
  id: 'turboprop/airflow',
  parent: 'turboprop',
  unit: 10 / 620,
  bounds: [[180, AY - 560, -300], [360, AY + 340, 300]],
  name: 'Accessory & Air Intake Section',
  en: 'Accessory & Air Intake Section',
  subtitle: 'Sub-assembly C · annular intake · right-angle drive',
  summary: '5 parts · FOD screen, bevel drive to starter-generator and fuel pump',
  drawingNo: 'GW-TP-C',
  scale: '1 : 3',
  parts: PARTS,
  annotations: ANNOTATIONS,
  boltSets: {},
  neighbours: {
    'inlet-screen': ['front-bearing-housing', 'inlet-screen'],
    'bevel-drive-gear': ['starter-gen-pad', 'fuel-pump-housing', 'bevel-drive-gear'],
  },
  guides: [
    { stage: 'inlet-screen', origin: [320, AY + 300, 0] },
    { stage: 'bevel-drive-gear', origin: [320, AY - 360, 0] },
  ],
  centreLines: [[[180, AY, 0], [380, AY, 0], 220]] as Array<[Vec3, Vec3, number?]>,
  steps: STEPS,
  camera: CAMERA,
  Model: AirflowGroup,
});
