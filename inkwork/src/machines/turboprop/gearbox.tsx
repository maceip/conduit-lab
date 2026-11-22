import { Part, M } from '../../scene/Part';
import { Callout } from '../../scene/Overlay';
import { sphere } from '../../scene/geometry';
import type { CameraDef, MachineDef, PartDef, StepDef, Vec3 } from '../types';
import { Cyl, Hoop, level, Turn, tube } from '../kit';
import { BoltCircle, FlangeCollar, Ribs, Shell } from './kit';
import { ToothedGear } from '../turboprop-kit';
import { EpicyclicGearboxStage } from './EpicyclicGearbox';
import { ANNOTATIONS, TP } from './data';
import { STAGE1 } from './kinematics';

const AY = TP.AY;
const U = TP.u;

/**
 * Sub-assembly B: two-stage epicyclic reduction gearbox.
 * The gear train is one EpicyclicGearboxStage (sun / planets / pins / carrier /
 * ring telescoping 0.35u per element on their explode.ts windows, planets also
 * fanning +0.55u radially). Stage one 16/24/64 (5:1) plus stage two 16/8/32
 * (3:1) makes 15:1 with the ring gear fixed.
 */

const PARTS: PartDef[] = [
  {
    id: 'gearbox-casing', index: 1, name: 'Gearbox Casing', en: 'Gearbox Casing', role: 'Structural',
    material: 'AZ91C magnesium', description: '16 mm wall with twelve bolts on each flange; the cavity doubles as the oil sump, scavenge temperature 110 °C.',
    explode: [-420, 0, 0], stage: [0.3, 0.62],
  },
  {
    id: 'torque-meter', index: 2, name: 'Torque-Meter Cylinder', en: 'Torque-Meter Cylinder', role: 'Torque sensing',
    material: '40CrNiMoA steel', description: 'Elastic barrel 112 mm long, 290 mm outer diameter, with four strain-gauge bridges; ±0.5% torque accuracy.',
    explode: [0, 320, 0], stage: [0.25, 0.55],
  },
  {
    id: 'gear-train', index: 3, name: 'Epicyclic Gear Train', en: 'Epicyclic Gear Train', role: '15:1 reduction',
    material: 'Case-hardened 18Cr2Ni4WA', description: 'Stage one 16/24/64 (five planets) and stage two 16/8/32; sun +0.75u, planets +0.40u with a +0.55u radial fan, pins/carrier +0.05u, ring −0.30u — telescoping at 0.35u per element.',
    explode: [0, 0, 0], stage: [0.6, 0.9],
  },
  {
    id: 'bearing-inner', index: 4, name: 'Thrust Bearing Inner Race', en: 'Thrust Bearing Inner Race', role: 'Takes prop thrust',
    material: 'GCr15 bearing steel', description: 'Race outer diameter 210 mm, tracks hardened to HRC 62; carries ≈ 30 kN of propeller thrust at take-off.',
    explode: [220, 0, 0], stage: [0.55, 0.8],
  },
  {
    id: 'bearing-outer', index: 5, name: 'Thrust Bearing Outer Race', en: 'Thrust Bearing Outer Race', role: 'Loads into casing',
    material: 'GCr15 bearing steel', description: 'Shrunk into the front casing wall, passing propeller thrust into the casing and the mounting truss.',
    explode: [-180, 0, 0], stage: [0.55, 0.8],
  },
  {
    id: 'bearing-cage', index: 6, name: 'Ball Cage', en: 'Ball Cage', role: 'Holds the balls',
    material: 'Fabric phenolic', description: 'Eighteen Ø22 balls evenly spaced, cage guidance clearance 0.15 mm, splash lubricated.',
    explode: [0, 0, -420], stage: [0.58, 0.82],
  },
  {
    id: 'scavenge-pump-gear', index: 7, name: 'Oil Scavenge Pump Gear', en: 'Oil Scavenge Pump Gear', role: 'Scavenge',
    material: '45 steel', description: '14-tooth spur gear, module 2.5, three lightening holes in the web; pumps sump oil back to the tank at 12 L/min.',
    explode: [-320, -280, 0], stage: [0.5, 0.75],
  },
];

const STEPS: StepDef[] = [
  {
    title: 'Gear Train', en: 'Gear Train',
    body: 'Two planetary stages: 16/24/64 (5:1) then 16/8/32 (3:1) — fifteen to one. The ring is fixed, the sun turns backwards, and the slow carrier drives the hub while five planets spin on their pins.',
    state: { explode: 0, section: true, running: false, select: 'gear-train', focus: null },
  },
  {
    title: 'Exploded', en: 'Exploded',
    body: 'Casing and torque-meter leave first; the gear train telescopes at 0.35u per element with the planets fanning +0.55u radially, then the three bearing pieces and the scavenge gear pull out in turn.',
    state: { explode: 1, section: false, running: false, select: null, focus: null },
  },
];

const CAMERA: CameraDef = {
  target: [560, AY, 0],
  offset: [1100, 520, 1300],
  orthoDistance: 3600,
  exploded: { target: [560, AY, 0], scale: 1.7 },
};

export function GearboxGroup() {
  return (
    <group>
      <Part id="gearbox-casing">
        <Shell k="tp-b-case" t={16} profile={[[248, TP.gearX0], [272, 380], [272, 800], [258, TP.gearX1]]} />
        <FlangeCollar k="tp-b-fl0" x={330} r={282} thick={34} bossCount={12} bossR={20} />
        <FlangeCollar k="tp-b-fl1" x={846} r={268} thick={30} bossCount={12} bossR={18} />
        <BoltCircle x={352} r={302} count={12} d={18} len={44} />
        <Ribs x={430} r0={276} r1={318} count={5} thick={14} />
        <Ribs x={760} r0={262} r1={304} count={5} thick={14} />
        <Callout id="gearbox-casing" p={[380, AY + 330, 120]} />
      </Part>
      <Part id="torque-meter">
        <Cyl c={[TP.torqueX, AY, 0]} r={145} len={112} axis="x" seg={36} />
        <Turn k="tp-b-tq-ring" axis="x" p={[0, AY, 0]} profile={[[145, 640], [158, 646], [158, 668], [145, 674]]} />
        <Callout id="torque-meter" p={[TP.torqueX, AY + 210, 90]} />
      </Part>

      {/* EpicyclicGearboxStage: elements open on their explode.ts windows */}
      <Part id="gear-train">
        <group position={[TP.gearMidX, AY, 0]}>
          <group scale={U}>
            <EpicyclicGearboxStage
              teeth={{ sun: STAGE1.sun, planet: STAGE1.planet, ring: STAGE1.ring, count: STAGE1.count }}
              explodeOffsets={{ sunX: 0.75, planetsX: 0.4, pinsX: 0.05, carrierX: 0.05, ringX: -0.3, planetsRadial: 0.55 }}
              windows={{
                sunX: [0.6, 0.8],
                planetsX: [0.63, 0.83],
                planetsRadial: [0.63, 0.83],
                pinsX: [0.66, 0.86],
                carrierX: [0.66, 0.86],
                ringX: [0.69, 0.89],
              }}
            />
          </group>
        </group>
        <Callout id="gear-train" p={[TP.gearMidX - 60, AY + 260, 120]} />
      </Part>

      <Part id="bearing-inner">
        <Turn k="tp-b-bi" axis="x" p={[0, AY, 0]} profile={tube(105, 806, 836, 16)} />
        <Callout id="bearing-inner" p={[820, AY + 160, 70]} />
      </Part>
      <Part id="bearing-outer">
        <Turn k="tp-b-bo" axis="x" p={[0, AY, 0]} profile={tube(158, 806, 836, 16)} />
        <Callout id="bearing-outer" p={[820, AY + 210, -70]} />
      </Part>
      <Part id="bearing-cage">
        <Hoop k="tp-b-bc" c={[821, AY, 0]} R={132} r={9} axis="x" seg={40} />
        {Array.from({ length: 18 }, (_, i) => {
          const a = (i / 18) * Math.PI * 2;
          return <M key={i} geo={sphere(11)} p={[821, AY + Math.cos(a) * 132, Math.sin(a) * 132]} />;
        })}
        <Callout id="bearing-cage" p={[821, AY + 120, 140]} />
      </Part>
      <Part id="scavenge-pump-gear">
        <group position={[352, AY - 172, 0]}>
          <group scale={U}>
            <ToothedGear teeth={14} module={0.0125} thickness={0.055} boreR={0.03} lighteningHoles={3} />
          </group>
        </group>
        <Callout id="scavenge-pump-gear" p={[352, AY - 230, 90]} />
      </Part>
    </group>
  );
}

export const gearbox: MachineDef = level({
  id: 'turboprop/gearbox',
  parent: 'turboprop',
  unit: 10 / 700,
  bounds: [[280, AY - 320, -320], [900, AY + 320, 320]],
  name: 'Two-Stage Epicyclic Reduction Gearbox',
  en: 'Two-Stage Epicyclic Reduction Gearbox',
  subtitle: 'Sub-assembly B · 15:1 · fixed ring',
  summary: '7 parts · 16/24/64 + 16/8/32 planets, thrust bearing takes prop load',
  drawingNo: 'GW-TP-B',
  scale: '1 : 2',
  parts: PARTS,
  annotations: ANNOTATIONS,
  boltSets: {},
  neighbours: {
    'gear-train': ['torque-meter', 'gear-train'],
    'gearbox-casing': ['bearing-outer', 'torque-meter', 'gearbox-casing'],
  },
  guides: [
    { stage: 'gear-train', origin: [TP.gearMidX + 200, AY, 0] },
    { stage: 'torque-meter', origin: [TP.torqueX, AY + 240, 0] },
    { stage: 'bearing-cage', origin: [821, AY + 200, 0] },
  ],
  centreLines: [[[280, AY, 0], [920, AY, 0], 260]] as Array<[Vec3, Vec3, number?]>,
  steps: STEPS,
  camera: CAMERA,
  Model: GearboxGroup,
});
