import { Part } from '../../scene/Part';
import { Callout } from '../../scene/Overlay';
import type { CameraDef, MachineDef, PartDef, StepDef, Vec3 } from '../types';
import { level, Turn, tube } from '../kit';
import { BladeRow, DiffuserPipes, Labyrinth, RotorDisc } from './kit';
import { TP } from './data';

const AY = TP.AY;

/**
 * 子组件 D · 轴流-离心压气机转子 / Axial-Centrifugal Compressor Spool。
 * 三级轴流转子（33/29/27 叶）+ 三级静子环（23/21/19 叶）+ 离心叶轮 + 12 根径向扩压管。
 */

const PARTS: PartDef[] = [
  {
    id: 'rotor-1', index: 1, name: '一级转子', en: 'Compressor Rotor 1', role: '增压 · 33 叶',
    material: '钛合金 TC11', description: '盘径 Ø420、33 叶、安装角 32°，三榫榫槽，轮缘周向 20 个叶根凸台。',
    explode: [420, 0, 0], stage: [0, 0.3],
  },
  {
    id: 'rotor-2', index: 2, name: '二级转子', en: 'Compressor Rotor 2', role: '增压 · 29 叶',
    material: '钛合金 TC11', description: '盘径 Ø390、29 叶、安装角 38°，与一级鼓筒摩擦焊成一体转子。',
    explode: [210, 0, 0], stage: [0.08, 0.38],
  },
  {
    id: 'rotor-3', index: 3, name: '三级转子', en: 'Compressor Rotor 3', role: '增压 · 27 叶',
    material: '钛合金 TC11', description: '盘径 Ø360、27 叶、安装角 44°；三级后总压比约 4:1。',
    explode: [0, 0, 0], stage: [0.16, 0.46],
  },
  {
    id: 'stator-1', index: 4, name: '一级静子环', en: 'Stator Ring 1', role: '整流 · 23 叶',
    material: 'GH4169', description: '23 片静叶焊在内环上，叶偏 28°，把气流扭回轴向进二级。',
    explode: [300, 0, 0], stage: [0.04, 0.34],
  },
  {
    id: 'stator-2', index: 5, name: '二级静子环', en: 'Stator Ring 2', role: '整流 · 21 叶',
    material: 'GH4169', description: '21 片、叶高 52 mm，外缘 24 个径向销定位在机匣上。',
    explode: [90, 0, 0], stage: [0.12, 0.42],
  },
  {
    id: 'stator-3', index: 6, name: '三级静子环', en: 'Stator Ring 3', role: '整流 · 19 叶',
    material: 'GH4169', description: '19 片，后接离心叶轮进口导叶，出口马赫数 0.55。',
    explode: [-120, 0, 0], stage: [0.2, 0.5],
  },
  {
    id: 'impeller', index: 7, name: '离心叶轮', en: 'Centrifugal Impeller', role: '增压',
    material: '钛合金 TC4', description: '12 长叶 + 12 短叶交错，出口角 26°，叶轮外径 Ø460，单级压比 4.2:1。',
    explode: [-300, 0, 0], stage: [0.28, 0.58],
  },
  {
    id: 'diffuser-pipes', index: 8, name: '径向扩压管', en: 'Radial Diffuser Pipes', role: '扩压',
    material: 'GH4169', description: '12 根扩压管（内径 28 mm）从叶轮外缘径向甩出再折向燃烧室，扩压比 1.8:1。',
    explode: [-300, 0, 320], stage: [0.32, 0.62],
  },
];

const STEPS: StepDef[] = [
  {
    title: '压气机', en: 'Compressor Spool',
    body: '轴流三级在前、离心级在后：转子与静子交错排布，空气逐级增压；离心叶轮把气流径向甩出经扩压管进燃烧室。',
    state: { explode: 0, section: true, running: false, select: 'impeller', focus: null },
  },
  {
    title: '分解', en: 'Exploded',
    body: '沿轴向拉成一串：三级转子、三级静子、叶轮与扩压管每级 0.4u 让开，叶排零重叠。',
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
  name: '轴流-离心压气机',
  en: 'Axial-Centrifugal Compressor Spool',
  subtitle: '子组件 D · 三级轴流 + 离心级',
  summary: '8 种零件 · 33/29/27 叶三转子 + 23/21/19 叶三静子 + 12 扩压管',
  drawingNo: 'GW-TP-D',
  scale: '1 : 2',
  parts: PARTS,
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
