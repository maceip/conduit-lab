import { Part } from '../../scene/Part';
import { Callout } from '../../scene/Overlay';
import type { CameraDef, MachineDef, PartDef, StepDef, Vec3 } from '../types';
import { Cyl, level, Rod, Turn, tube } from '../kit';
import { Shell } from './kit';
import { BladeRow, Labyrinth, RotorDisc } from './kit';
import { ANNOTATIONS, TP } from './data';

const AY = TP.AY;

/**
 * Sub-assembly F: gas generator & power turbines + exhaust — NGV ring, HP
 * turbine disk, inter-stage baffle, two counter-rotating free power turbines,
 * the concentric inner shaft, twin exhaust stubs and the tailcone.
 */

const PARTS: PartDef[] = [
  {
    id: 'ngv-ring', index: 1, name: 'Turbine NGV Ring', en: 'Turbine NGV Ring', role: 'Guidance',
    material: 'DS superalloy', description: '34 hollow guide vanes at 72° exit angle, accelerating and steering the gas into the HP rotor; film-cooled leading edges.',
    explode: [320, 0, 0], stage: [0, 0.3],
  },
  {
    id: 'hp-turbine-disk', index: 2, name: 'HP Turbine Disk', en: 'HP Turbine Disk', role: 'Drives compressor',
    material: 'DS superalloy', description: '29 blades of 48 mm height, 18 bore cooling holes; the gas work turns the spool directly (1.0ω).',
    explode: [160, 0, 0], stage: [0.08, 0.38],
  },
  {
    id: 'inter-baffle', index: 3, name: 'Inter-Stage Baffle', en: 'Inter-Stage Baffle', role: 'Heat shield · seal',
    material: 'GH4169', description: 'Splits the hot and cold cavities between the HP and power stages; four labyrinth teeth in the rim cut cooling-air mixing losses.',
    explode: [0, 260, 0], stage: [0.16, 0.46],
  },
  {
    id: 'pt-disk-1', index: 4, name: 'Power Turbine Disk 1', en: 'Power Turbine Disk 1', role: 'Output · 31 blades',
    material: 'FGH96 powder alloy', description: '31 blades of 56 mm height, aerodynamically decoupled from the HP turbine, counter-rotating (−0.75ω), 91% efficient.',
    explode: [-180, 0, 0], stage: [0.24, 0.54],
  },
  {
    id: 'pt-disk-2', index: 5, name: 'Power Turbine Disk 2', en: 'Power Turbine Disk 2', role: 'Output · 33 blades',
    material: 'FGH96 powder alloy', description: '33 blades of 56 mm height, coaxial with stage one; 3.2:1 pressure drop over the two stages, shaft power in the 1,500 shp class.',
    explode: [-360, 0, 0], stage: [0.32, 0.62],
  },
  {
    id: 'inner-shaft', index: 6, name: 'Free Power Turbine Shaft', en: 'Free Power Turbine Shaft', role: 'Power out',
    material: '40CrNiMoA steel', description: 'Ø124 × 1.7 m hollow shaft carrying power through the HP spool centre to the sun gear; two labyrinth packs separate hot and cold sides.',
    explode: [0, -320, 0], stage: [0.36, 0.66],
  },
  {
    id: 'exhaust-stubs', index: 7, name: 'Exhaust Duct Stubs ×2', en: 'Exhaust Duct Stubs ×2', role: 'Exhaust',
    material: 'Inconel 625', description: 'Twin stubs with a 220 mm bore canted up 15°, 3 mm wall with a bellows section for thermal growth; ≈ 700 °C exhaust.',
    explode: [-420, 0, 0], stage: [0.4, 0.7],
  },
  {
    id: 'tailcone', index: 8, name: 'Aft Tailcone', en: 'Aft Tailcone', role: 'Fairing',
    material: 'Inconel 625', description: 'The 100 mm tailcone mixes and straightens the two exhaust jets, cutting base drag; two thermocouples read the inner wall.',
    explode: [-580, 0, 0], stage: [0.44, 0.74],
  },
];

const STEPS: StepDef[] = [
  {
    title: 'Turbines & Exhaust', en: 'Turbines & Exhaust',
    body: 'Gas passes the guide vanes into the HP turbine (which turns the spool), then into the two counter-rotating free power turbines — the outer spool drives the compressor and the inner shaft the propeller, the two concentric shafts turning opposite ways across a labyrinth seal.',
    state: { explode: 0, section: true, running: false, select: 'pt-disk-2', focus: null },
  },
  {
    title: 'Exploded', en: 'Exploded',
    body: 'Guide ring, HP disk, baffle and both power disks telescope along the axis; the inner shaft drops out below, and the exhaust stubs and tailcone leave aft together.',
    state: { explode: 1, section: false, running: false, select: null, focus: null },
  },
];

const CAMERA: CameraDef = {
  target: [-1120, AY, 0],
  offset: [1150, 520, 1400],
  orthoDistance: 3600,
  exploded: { target: [-1180, AY, 0], scale: 1.8 },
};

export function TurbineGroup() {
  return (
    <group>
      <Part id="ngv-ring">
        <BladeRow k="tp-f-ngv" x={TP.ngvX} count={34} rootR={106} tipR={192} chord={36} thick={11} pitch={0.72} />
        <Turn k="tp-f-ngvring" axis="x" p={[0, AY, 0]} profile={tube(192, TP.ngvX - 22, TP.ngvX + 22, 12)} />
        <Callout id="ngv-ring" p={[TP.ngvX, AY + 240, 90]} />
      </Part>
      <Part id="hp-turbine-disk">
        <RotorDisc k="tp-f-hpdisc" x={TP.hpX} rimR={142} hubR={58} thick={46} tabs={18} />
        <BladeRow k="tp-f-hpbl" x={TP.hpX} count={29} rootR={88} tipR={TP.hpR} chord={44} thick={13} pitch={0.52} stagger={0.002} />
        <Callout id="hp-turbine-disk" p={[TP.hpX, AY + 220, -90]} />
      </Part>
      <Part id="inter-baffle">
        <Turn k="tp-f-baffle" axis="x" p={[0, AY, 0]} profile={[[70, TP.baffleX - 16], [152, TP.baffleX - 6], [152, TP.baffleX + 12], [70, TP.baffleX + 20]]} />
        <Labyrinth x0={TP.baffleX + 24} r={150} teeth={4} toothH={12} toothW={10} gap={18} />
        <Callout id="inter-baffle" p={[TP.baffleX, AY + 210, 90]} />
      </Part>
      <Part id="pt-disk-1">
        <RotorDisc k="tp-f-pt1" x={TP.pt1X} rimR={152} hubR={62} thick={44} tabs={18} />
        <BladeRow k="tp-f-pt1bl" x={TP.pt1X} count={31} rootR={92} tipR={TP.ptR} chord={48} thick={13} pitch={-0.5} stagger={0.002} />
        <Callout id="pt-disk-1" p={[TP.pt1X, AY + 230, -90]} />
      </Part>
      <Part id="pt-disk-2">
        <RotorDisc k="tp-f-pt2" x={TP.pt2X} rimR={152} hubR={62} thick={44} tabs={18} />
        <BladeRow k="tp-f-pt2bl" x={TP.pt2X} count={33} rootR={92} tipR={TP.ptR} chord={48} thick={13} pitch={-0.52} stagger={0.002} />
        <Callout id="pt-disk-2" p={[TP.pt2X, AY + 230, 90]} />
      </Part>
      <Part id="inner-shaft">
        <Cyl c={[(TP.pt2X + TP.gearMidX) / 2, AY, 0]} r={TP.shaftR} len={TP.gearMidX - TP.pt2X} axis="x" seg={28} />
        <Labyrinth x0={TP.pt2X + 34} r={72} teeth={5} />
        <Labyrinth x0={TP.linerX0 + 60} r={70} teeth={4} />
        <Callout id="inner-shaft" p={[-820, AY - 130, 90]} />
      </Part>
      <Part id="exhaust-stubs">
        {[1, -1].map((s) => (
          <group key={s}>
            <Rod a={[-1220, AY + 20, s * 150]} b={[-1280, AY + 60, s * 258]} r={112} seg={22} />
            <Cyl c={[-1360, AY + 72, s * 282]} r={112} len={190} axis="x" seg={22} r2={104} />
            <Turn k={`tp-f-rim-${s}`} axis="x" p={[0, AY + 72, s * 282]} profile={[[104, -1452], [118, -1458], [118, -1472], [104, -1478]]} />
          </group>
        ))}
        <Callout id="exhaust-stubs" p={[-1330, AY + 250, 150]} />
      </Part>
      <Part id="tailcone">
        <Shell k="tp-f-tail" t={14} profile={[[206, -1420], [150, -1466], [86, -1506], [58, -1520]]} />
        <Callout id="tailcone" p={[-1470, AY + 140, 80]} />
      </Part>
    </group>
  );
}

export const turbine: MachineDef = level({
  id: 'turboprop/turbine',
  parent: 'turboprop',
  unit: 10 / 900,
  bounds: [[-1580, AY - 320, -340], [-680, AY + 340, 340]],
  name: 'Gas Generator & Power Turbines',
  en: 'Gas Generator & Power Turbines + Exhaust',
  subtitle: 'Sub-assembly F · counter-rotating shafts · twin exhaust',
  summary: '8 parts · HP turbine turns the spool, two power turbines reach the prop through the inner shaft',
  drawingNo: 'GW-TP-F',
  scale: '1 : 3',
  parts: PARTS,
  annotations: ANNOTATIONS,
  boltSets: {},
  neighbours: {
    'pt-disk-2': ['inner-shaft', 'pt-disk-1', 'pt-disk-2'],
    'hp-turbine-disk': ['ngv-ring', 'inter-baffle', 'hp-turbine-disk'],
    'exhaust-stubs': ['tailcone', 'exhaust-stubs'],
  },
  guides: [
    { stage: 'ngv-ring', origin: [TP.ngvX + 120, AY + 240, 0] },
    { stage: 'inner-shaft', origin: [-900, AY - 180, 0] },
    { stage: 'exhaust-stubs', origin: [-1360, AY + 240, 0] },
  ],
  centreLines: [[[-1580, AY, 0], [-660, AY, 0], TP.ptR]] as Array<[Vec3, Vec3, number?]>,
  steps: STEPS,
  camera: CAMERA,
  Model: TurbineGroup,
});
