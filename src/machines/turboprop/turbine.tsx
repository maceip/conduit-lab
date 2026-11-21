import { Part } from '../../scene/Part';
import { Callout } from '../../scene/Overlay';
import type { CameraDef, MachineDef, PartDef, StepDef, Vec3 } from '../types';
import { Cyl, level, Rod, Turn, tube } from '../kit';
import { Shell } from './kit';
import { BladeRow, Labyrinth, RotorDisc } from './kit';
import { TP } from './data';

const AY = TP.AY;

/**
 * 子组件 F · 燃气发生器与动力涡轮 + 排气 / Gas Generator & Power Turbines + Exhaust。
 * 导向器 + 高压涡轮盘 + 级间挡板 + 两级反转自由动力涡轮 + 同心内轴 + 双排气短管 + 尾锥。
 */

const PARTS: PartDef[] = [
  {
    id: 'ngv-ring', index: 1, name: '涡轮导向器环', en: 'Turbine NGV Ring', role: '导向',
    material: 'DS 高温合金', description: '34 片空心导向叶片，出口角 72°，把燃气加速并导向高压转子，前缘气膜冷却。',
    explode: [320, 0, 0], stage: [0, 0.3],
  },
  {
    id: 'hp-turbine-disk', index: 2, name: '高压涡轮盘', en: 'HP Turbine Disk', role: '驱动压气机',
    material: 'DS 高温合金', description: '29 叶、叶高 48 mm，盘心冷却孔 18 个；燃气做功直接带转子（1.0ω）。',
    explode: [160, 0, 0], stage: [0.08, 0.38],
  },
  {
    id: 'inter-baffle', index: 3, name: '级间挡板', en: 'Inter-Stage Baffle', role: '隔热 · 密封',
    material: 'GH4169', description: '挡板把高压级与动力级的冷热腔隔开，外缘 4 道迷宫齿，减少冷气掺混损失。',
    explode: [0, 260, 0], stage: [0.16, 0.46],
  },
  {
    id: 'pt-disk-1', index: 4, name: '动力涡轮一级盘', en: 'Power Turbine Disk 1', role: '输出功 · 31 叶',
    material: 'FGH96 粉末合金', description: '31 叶、叶高 56 mm，与高压涡轮气动解耦，反转（−0.75ω），效率 91%。',
    explode: [-180, 0, 0], stage: [0.24, 0.54],
  },
  {
    id: 'pt-disk-2', index: 5, name: '动力涡轮二级盘', en: 'Power Turbine Disk 2', role: '输出功 · 33 叶',
    material: 'FGH96 粉末合金', description: '33 叶、叶高 56 mm，与一级盘同轴；两级落压比 3.2:1，输出轴功率 1 500 shp 级。',
    explode: [-360, 0, 0], stage: [0.32, 0.62],
  },
  {
    id: 'inner-shaft', index: 6, name: '自由涡轮内轴', en: 'Free Power Turbine Shaft', role: '输出功率',
    material: '40CrNiMoA', description: 'Ø124×1.7 m 空心内轴，穿过高压转子中心把功率送到太阳轮；两道迷宫密封隔开冷热腔。',
    explode: [0, -320, 0], stage: [0.36, 0.66],
  },
  {
    id: 'exhaust-stubs', index: 7, name: '排气短管 ×2', en: 'Exhaust Duct Stubs ×2', role: '排气',
    material: 'Inconel 625', description: '双侧短管内径 220 mm、上偏 15°，壁厚 3 mm 波纹段吸收热膨胀，排气温度约 700 °C。',
    explode: [-420, 0, 0], stage: [0.4, 0.7],
  },
  {
    id: 'tailcone', index: 8, name: '尾锥', en: 'Aft Tailcone', role: '整流',
    material: 'Inconel 625', description: '长 100 mm 尾锥把两股排气掺混整流，减少后体阻力，内壁测温热电偶 2 点。',
    explode: [-580, 0, 0], stage: [0.44, 0.74],
  },
];

const STEPS: StepDef[] = [
  {
    title: '涡轮与排气', en: 'Turbines & Exhaust',
    body: '燃气先经导向器进高压涡轮（带转子），再进两级反转动力涡轮——外转子带压气机、内轴带螺旋桨，两轴同心反转，中间靠迷宫密封隔开。',
    state: { explode: 0, section: true, running: false, select: 'pt-disk-2', focus: null },
  },
  {
    title: '分解', en: 'Exploded',
    body: '导向器、高压盘、挡板、两级动力盘沿轴向伸开；内轴下沉拉出，排气短管与尾锥整体后脱。',
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
  name: '燃气发生器与动力涡轮',
  en: 'Gas Generator & Power Turbines + Exhaust',
  subtitle: '子组件 F · 双反转轴 · 双排气',
  summary: '8 种零件 · 高压涡轮带转子，两级动力涡轮经内轴带螺旋桨',
  drawingNo: 'GW-TP-F',
  scale: '1 : 3',
  parts: PARTS,
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
