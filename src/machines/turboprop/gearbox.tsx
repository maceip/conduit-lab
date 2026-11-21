import { Part, M } from '../../scene/Part';
import { Callout } from '../../scene/Overlay';
import { sphere } from '../../scene/geometry';
import type { CameraDef, MachineDef, PartDef, StepDef, Vec3 } from '../types';
import { Cyl, Hoop, level, Turn, tube } from '../kit';
import { BoltCircle, FlangeCollar, Ribs, Shell } from './kit';
import { ToothedGear } from '../turboprop-kit';
import { EpicyclicGearboxStage } from './EpicyclicGearbox';
import { TP } from './data';
import { STAGE1 } from './kinematics';

const AY = TP.AY;
const U = TP.u;

/**
 * 子组件 B · 两级行星减速齿轮箱 / Two-Stage Epicyclic Reduction Gearbox。
 * 轮系整体用 EpicyclicGearboxStage（太阳轮/行星轮/销轴/行星架/内齿圈按
 * explode.ts 时间窗沿 +x telescoping 0.35u/件，行星轮另径向 +0.55u）。
 * 一级 16/24/64（5:1）+ 二级 16/8/32（3:1）= 15:1，齿圈固定。
 */

const PARTS: PartDef[] = [
  {
    id: 'gearbox-casing', index: 1, name: '齿轮箱机匣', en: 'Gearbox Casing', role: '承力',
    material: '镁合金 AZ91C', description: '壁厚 16 mm，前后凸缘各 12 螺栓；内腔兼作滑油收油池，回油温度 110 °C。',
    explode: [-420, 0, 0], stage: [0.3, 0.62],
  },
  {
    id: 'torque-meter', index: 2, name: '扭矩计筒', en: 'Torque-Meter Cylinder', role: '测扭',
    material: '40CrNiMoA', description: '弹性筒长 112 mm、外径 290 mm，贴 4 组应变片，测扭精度 ±0.5%。',
    explode: [0, 320, 0], stage: [0.25, 0.55],
  },
  {
    id: 'gear-train', index: 3, name: '行星轮系', en: 'Epicyclic Gear Train', role: '15:1 减速',
    material: '18Cr2Ni4WA 渗碳', description: '一级 16/24/64（5 轮）+ 二级 16/8/32；太阳轮 +0.75u、行星轮 +0.40u 并径向 +0.55u、销轴/行星架 +0.05u、内齿圈 −0.30u 依次伸开（0.35u/件）。',
    explode: [0, 0, 0], stage: [0.6, 0.9],
  },
  {
    id: 'bearing-inner', index: 4, name: '推力轴承内圈', en: 'Thrust Bearing Inner Race', role: '承受桨拉力',
    material: 'GCr15', description: '内圈外径 210 mm，滚道淬硬 HRC 62，承受桨拉力约 30 kN（起飞状态）。',
    explode: [220, 0, 0], stage: [0.55, 0.8],
  },
  {
    id: 'bearing-outer', index: 5, name: '推力轴承外圈', en: 'Thrust Bearing Outer Race', role: '传力至机匣',
    material: 'GCr15', description: '外圈压装在机匣前壁，把桨拉力传给机匣与安装桁架。',
    explode: [-180, 0, 0], stage: [0.55, 0.8],
  },
  {
    id: 'bearing-cage', index: 6, name: '钢球保持架', en: 'Ball Cage', role: '保持钢球',
    material: '酚醛胶布', description: '18 粒 Ø22 钢球均布，保持架引导间隙 0.15 mm，飞溅润滑。',
    explode: [0, 0, -420], stage: [0.58, 0.82],
  },
  {
    id: 'scavenge-pump-gear', index: 7, name: '收油泵齿轮', en: 'Oil Scavenge Pump Gear', role: '回油',
    material: '45 钢', description: '直齿轮 14 齿、模数 2.5（腹板 3 个轻化孔），把收油池滑油泵回油箱，流量 12 L/min。',
    explode: [-320, -280, 0], stage: [0.5, 0.75],
  },
];

const STEPS: StepDef[] = [
  {
    title: '轮系', en: 'Gear Train',
    body: '两级行星：一级 16/24/64（5:1），二级 16/8/32（3:1），合计 15:1。齿圈固定，太阳轮反转，行星架慢转带动桨毂；5 个行星轮绕销轴差动自转。',
    state: { explode: 0, section: true, running: false, select: 'gear-train', focus: null },
  },
  {
    title: '分解', en: 'Exploded',
    body: '机匣、扭矩计筒先后脱开；轮系按 0.35u/件 telescoping 伸开，行星轮另径向 +0.55u 散开，轴承三件与收油泵齿轮依次拉出。',
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

      {/* 行星轮系：EpicyclicGearboxStage，元件按 explode.ts 时间窗伸开 */}
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
  name: '两级行星减速齿轮箱',
  en: 'Two-Stage Epicyclic Reduction Gearbox',
  subtitle: '子组件 B · 15:1 · 齿圈固定',
  summary: '7 种零件 · 16/24/64 + 16/8/32 两级行星，推力轴承承受桨拉力',
  drawingNo: 'GW-TP-B',
  scale: '1 : 2',
  parts: PARTS,
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
