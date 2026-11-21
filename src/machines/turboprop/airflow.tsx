import { Part } from '../../scene/Part';
import { Callout } from '../../scene/Overlay';
import type { CameraDef, MachineDef, PartDef, StepDef, Vec3 } from '../types';
import { Box, Cyl, level, Turn, tube } from '../kit';
import { FlangeCollar, GearDisc, Ribs, Shell } from './kit';
import { TP } from './data';

const AY = TP.AY;

/**
 * 子组件 C · 附件与进气段 / Accessory & Air Intake Section。
 * 环形径向进气滤网 + 压气机前轴承机匣 + 附件锥齿轮 + 起发座 + 高压燃油泵壳。
 */

const PARTS: PartDef[] = [
  {
    id: 'inlet-screen', index: 1, name: '进气滤网', en: 'Annular Inlet Screen', role: '防异物',
    material: '不锈钢丝网', description: '环形径向滤网（内径 416、外径 544 mm），18 根径向筋，网孔 4 mm，防冰热气从环腔通入。',
    explode: [360, 0, 0], stage: [0, 0.3],
  },
  {
    id: 'front-bearing-housing', index: 2, name: '前轴承机匣', en: 'Front Bearing Housing', role: '支承转子',
    material: '40CrNiMoA', description: '内装双列球轴承（Ø85 孔），滑油喷嘴 4 个；前接滤网，后接压气机机匣。',
    explode: [180, 0, 0], stage: [0.15, 0.45],
  },
  {
    id: 'bevel-drive-gear', index: 3, name: '附件锥齿轮', en: 'Accessory Bevel Gear', role: '直角传动',
    material: '18Cr2Ni4WA', description: '27 齿锥齿轮副（轴交角 90°），把水平轴功率转到竖直附件轴，转速 6 000 r/min。',
    explode: [0, -360, 0], stage: [0.5, 0.78],
  },
  {
    id: 'starter-gen-pad', index: 4, name: '起动发电机座', en: 'Starter-Generator Pad', role: '起动 · 发电',
    material: '铝合金 2A14', description: 'ISO 5 接口安装座（4×M12），起动扭矩 180 N·m，发电功率 9 kW。',
    explode: [-180, -420, 0], stage: [0.52, 0.8],
  },
  {
    id: 'fuel-pump-housing', index: 5, name: '高压燃油泵壳', en: 'HP Fuel Pump Housing', role: '增压供油',
    material: '铝合金 2A14', description: '柱塞泵壳（出口压力 7 MPa），花键接口 12 齿，与调速器同轴安装。',
    explode: [-40, -420, 0], stage: [0.54, 0.82],
  },
];

const STEPS: StepDef[] = [
  {
    title: '附件段', en: 'Accessory Section',
    body: '空气从环形滤网四周进入，经前轴承机匣的导流窗汇入轴向；下方锥齿轮副把功率引到起发与高压燃油泵。',
    state: { explode: 0, section: true, running: false, select: 'inlet-screen', focus: null },
  },
  {
    title: '分解', en: 'Exploded',
    body: '滤网前脱、轴承机匣随后；三个附件沿 −y 径向拉出，锥齿轮最后。',
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
  name: '附件与进气段',
  en: 'Accessory & Air Intake Section',
  subtitle: '子组件 C · 环形进气 · 直角传动',
  summary: '5 种零件 · 滤网防异物，锥齿轮驱动起发与高压燃油泵',
  drawingNo: 'GW-TP-C',
  scale: '1 : 3',
  parts: PARTS,
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
