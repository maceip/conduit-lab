import { Part } from '../../scene/Part';
import { Callout } from '../../scene/Overlay';
import type { CameraDef, MachineDef, PartDef, StepDef, Vec3 } from '../types';
import { level, Turn, tube } from '../kit';
import { BladeRow, DiffuserPipes, Labyrinth, RotorDisc } from './kit';
import { ANNOTATIONS, TP } from './data';

const AY = TP.AY;

/**
 * Sub-assembly D: axial-centrifugal compressor spool — three axial rotors
 * (33/29/27 blades), three stator rings (23/21/19 vanes), the centrifugal
 * impeller and twelve radial diffuser pipes.
 */

const PARTS: PartDef[] = [
  {
    id: 'rotor-1', index: 1, name: 'Rotor Stage 1', en: 'Compressor Rotor 1', role: 'Boost · 33 blades',
    material: 'TC11 titanium', description: 'Ø420 disk, 33 blades at 32° stagger, triple fir-tree slots and 20 blade-root lugs around the rim.',
    explode: [420, 0, 0], stage: [0, 0.3],
  },
  {
    id: 'rotor-2', index: 2, name: 'Rotor Stage 2', en: 'Compressor Rotor 2', role: 'Boost · 29 blades',
    material: 'TC11 titanium', description: 'Ø390 disk, 29 blades at 38° stagger, friction-welded to the stage-one drum as one rotor.',
    explode: [210, 0, 0], stage: [0.08, 0.38],
  },
  {
    id: 'rotor-3', index: 3, name: 'Rotor Stage 3', en: 'Compressor Rotor 3', role: 'Boost · 27 blades',
    material: 'TC11 titanium', description: 'Ø360 disk, 27 blades at 44° stagger; overall pressure ratio across the three stages ≈ 4:1.',
    explode: [0, 0, 0], stage: [0.16, 0.46],
  },
  {
    id: 'stator-1', index: 4, name: 'Stator Ring 1', en: 'Stator Ring 1', role: 'Guide · 23 vanes',
    material: 'GH4169', description: '23 stator vanes welded into the inner ring at 28° camber, turning the flow axial before stage two.',
    explode: [300, 0, 0], stage: [0.04, 0.34],
  },
  {
    id: 'stator-2', index: 5, name: 'Stator Ring 2', en: 'Stator Ring 2', role: 'Guide · 21 vanes',
    material: 'GH4169', description: '21 vanes, 52 mm high, located in the casing by 24 radial pins in the rim.',
    explode: [90, 0, 0], stage: [0.12, 0.42],
  },
  {
    id: 'stator-3', index: 6, name: 'Stator Ring 3', en: 'Stator Ring 3', role: 'Guide · 19 vanes',
    material: 'GH4169', description: '19 vanes feeding the centrifugal impeller eye; exit Mach 0.55.',
    explode: [-120, 0, 0], stage: [0.2, 0.5],
  },
  {
    id: 'impeller', index: 7, name: 'Centrifugal Impeller', en: 'Centrifugal Impeller', role: 'Boost',
    material: 'TC4 titanium', description: '12 long + 12 short interleaved vanes, 26° exit angle, Ø460 tip; 4.2:1 in a single stage.',
    explode: [-300, 0, 0], stage: [0.28, 0.58],
  },
  {
    id: 'diffuser-pipes', index: 8, name: 'Radial Diffuser Pipes', en: 'Radial Diffuser Pipes', role: 'Diffusion',
    material: 'GH4169', description: 'Twelve pipes (28 mm bore) throw the flow radially off the impeller and bend it toward the combustor, 1.8:1 diffusion.',
    explode: [-300, 0, 320], stage: [0.32, 0.62],
  },
];

const STEPS: StepDef[] = [
  {
    title: 'Compressor Spool', en: 'Compressor Spool',
    body: 'Three axial stages ahead of a centrifugal stage: rotors and stators interleave and compress the air stage by stage, then the impeller throws it out radially through the diffuser pipes into the combustor.',
    state: { explode: 0, section: true, running: false, select: 'impeller', focus: null },
  },
  {
    title: 'Exploded', en: 'Exploded',
    body: 'Pulled out along the axis in a row: three rotors, three stators, impeller and diffuser pipes each step aside so no blade row overlaps another.',
    state: { explode: 1, section: false, running: false, select: null, focus: null },
  },
];

const CAMERA: CameraDef = {
  target: [-40, AY, 0],
  offset: [1000, 460, 1250],
  orthoDistance: 3200,
  exploded: { target: [-80, AY, 0], scale: 1.8 },
};

export function CompressorGroup() {
  const rotors = [
    { id: 'rotor-1', x: TP.rotor1X, tip: TP.rotorTipR[0], n: TP.bladeCounts[0] },
    { id: 'rotor-2', x: TP.rotor2X, tip: TP.rotorTipR[1], n: TP.bladeCounts[1] },
    { id: 'rotor-3', x: TP.rotor3X, tip: TP.rotorTipR[2], n: TP.bladeCounts[2] },
  ];
  const stators = [
    { id: 'stator-1', x: TP.stator1X, n: TP.statorCounts[0] },
    { id: 'stator-2', x: TP.stator2X, n: TP.statorCounts[1] },
    { id: 'stator-3', x: TP.stator3X, n: TP.statorCounts[2] },
  ];
  return (
    <group>
      {rotors.map(({ id, x, tip, n }) => (
        <Part key={id} id={id}>
          <RotorDisc k={`tp-d-${id}`} x={x} rimR={tip - 26} hubR={72} thick={42} tabs={20} />
          <BladeRow k={`tp-d-${id}`} x={x} count={n} rootR={96} tipR={tip} chord={42} thick={13} pitch={0.56} stagger={0.002} />
          <Labyrinth x0={x + 30} r={78} teeth={5} />
          <Callout id={id} p={[x, AY + tip + 70, 80]} />
        </Part>
      ))}
      {stators.map(({ id, x, n }) => (
        <Part key={id} id={id}>
          <BladeRow k={`tp-d-${id}`} x={x} count={n} rootR={102} tipR={TP.statorOuterR} chord={42} thick={12} pitch={-0.52} />
          <Turn k={`tp-d-${id}-ring`} axis="x" p={[0, AY, 0]} profile={tube(TP.statorOuterR, x - 26, x + 26, 12)} />
          <Callout id={id} p={[x, AY + TP.statorOuterR + 70, -80]} />
        </Part>
      ))}
      <Part id="impeller">
        <RotorDisc k="tp-d-imp" x={TP.impellerX} rimR={196} hubR={54} thick={64} tabs={12} />
        <BladeRow k="tp-d-imp-l" x={TP.impellerX} count={12} rootR={58} tipR={TP.impellerR} chord={62} thick={16} pitch={0.45} stagger={0.004} />
        <BladeRow k="tp-d-imp-s" x={TP.impellerX} count={12} rootR={58} tipR={TP.impellerR * 0.82} chord={44} thick={13} pitch={0.42} a0={Math.PI / 12} />
        <Callout id="impeller" p={[TP.impellerX, AY + 290, 90]} />
      </Part>
      <Part id="diffuser-pipes">
        <DiffuserPipes x={TP.impellerX} r0={TP.impellerR + 8} r1={286} count={12} r={15} />
        <Callout id="diffuser-pipes" p={[TP.impellerX - 60, AY + 320, -80]} />
      </Part>
    </group>
  );
}

export const compressor: MachineDef = level({
  id: 'turboprop/compressor',
  parent: 'turboprop',
  unit: 10 / 760,
  bounds: [[-360, AY - 320, -320], [300, AY + 320, 320]],
  name: 'Axial-Centrifugal Compressor Spool',
  en: 'Axial-Centrifugal Compressor Spool',
  subtitle: 'Sub-assembly D · three axial stages + centrifugal',
  summary: '8 parts · rotors 33/29/27, stators 23/21/19, twelve diffuser pipes',
  drawingNo: 'GW-TP-D',
  scale: '1 : 2',
  parts: PARTS,
  annotations: ANNOTATIONS,
  boltSets: {},
  neighbours: {
    impeller: ['diffuser-pipes', 'stator-3', 'impeller'],
    'rotor-1': ['stator-1', 'rotor-2', 'stator-2', 'rotor-3', 'rotor-1'],
  },
  guides: [
    { stage: 'rotor-1', origin: [TP.rotor1X + 120, AY + 260, 0] },
    { stage: 'impeller', origin: [TP.impellerX - 80, AY + 260, 0] },
    { stage: 'diffuser-pipes', origin: [TP.impellerX, AY + 320, 0] },
  ],
  centreLines: [[[-360, AY, 0], [320, AY, 0], TP.impellerR]] as Array<[Vec3, Vec3, number?]>,
  steps: STEPS,
  camera: CAMERA,
  Model: CompressorGroup,
});
