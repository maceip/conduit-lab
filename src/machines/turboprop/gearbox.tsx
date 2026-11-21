import { Part, M } from '../../scene/Part';
import { Callout } from '../../scene/Overlay';
import { sphere } from '../../scene/geometry';
import type { CameraDef, MachineDef, PartDef, StepDef, Vec3 } from '../types';
import { Cyl, Hoop, level, Turn, tube } from '../kit';
import { GearDisc, GearWheel, RingGear, Ribs, Shell, FlangeCollar, BoltCircle } from './kit';
import { TP } from './data';
import { STAGE1 } from './kinematics';

const AY = TP.AY;

/**
 * 子组件 B · 两级行星减速齿轮箱 / Two-Stage Epicyclic Reduction Gearbox。
 * 一级 16/24/64（5:1）+ 二级 16/8/32（3:1）= 15:1；齿圈固定，行星架带桨毂。
 */

const PR = 105; // 一级行星销圆半径

const PARTS: PartDef[] = [
  {
    id: 'gearbox-casing', index: 1, name: '齿轮箱机匣', en: 'Gearbox Casing', role: '承力',
    material: '镁合金 AZ91C', description: '壁厚 16 mm，前后凸缘各 12 螺栓；内腔兼作滑油收油池，回油温度 110 °C。',
    explode: [-420, 0, 0], stage: [0.3, 0.62],
  },
  {
    id: 'torque-meter', index: 2, name: '扭矩计筒', en: 'Torque-Meter Cylinder', role: '测扭',
    material: '40CrNiMoA', description: '弹性筒长 112 mm、外径 290 mm，贴 4 组应变片，测扭精度 ±0.5%，信号送调速器。',
    explode: [0, 320, 0], stage: [0.25, 0.55],
  },
  {
    id: 'sun-gear', index: 3, name: '太阳轮轴', en: 'Sun Gear Shaft', role: '输入 · 16 齿',
    material: '18Cr2Ni4WA 渗碳', description: '模数 5、变位 +0.3，与自由涡轮内轴花键连接；轴向窜动由前端轴承限制在 0.1 mm。',
    explode: [420, 0, 0], stage: [0.6, 0.85],
  },
  {
    id: 'planet-gears', index: 4, name: '一级行星轮 ×5', en: 'Planet Gears ×5', role: '差动 · 24 齿',
    material: '18Cr2Ni4WA 渗碳', description: '5 轮均布（销圆 Ø210），齿面硬度 HRC 60，单轮传扭约 210 N·m。',
    explode: [0, 0, 420], stage: [0.62, 0.88],
  },
  {
    id: 'planet-pins', index: 5, name: '行星销', en: 'Planet Pins', role: '支承',
    material: '20CrMo 渗碳', description: 'Ø42×116 中空销（内孔 Ø16 通滑油），压入行星架，过盈 0.03 mm。',
    explode: [0, 220, 0], stage: [0.64, 0.9],
  },
  {
    id: 'carrier-cage', index: 6, name: '行星架', en: 'Planet Carrier', role: '输出',
    material: '20CrMo 锻钢', description: '厚 70 mm，5 个轻化孔（Ø62），中心花键 12 齿接桨毂，动平衡 G1.0。',
    explode: [-240, 0, 0], stage: [0.66, 0.92],
  },
  {
    id: 'ring-gear', index: 7, name: '内齿圈', en: 'Ring Gear', role: '固定 · 64 齿',
    material: '42CrMo 氮化', description: '64 齿内齿圈压入机匣内壁，齿面氮化 0.5 mm；15:1 减速比的"分母"就在这圈齿上。',
    explode: [0, -320, 0], stage: [0.68, 0.94],
  },
  {
    id: 'bearing-inner', index: 8, name: '推力轴承内圈', en: 'Thrust Bearing Inner Race', role: '承受桨拉力',
    material: 'GCr15', description: '内圈外径 210 mm，滚道淬硬 HRC 62，承受桨拉力约 30 kN（起飞状态）。',
    explode: [220, 0, 0], stage: [0.55, 0.8],
  },
  {
    id: 'bearing-outer', index: 9, name: '推力轴承外圈', en: 'Thrust Bearing Outer Race', role: '传力至机匣',
    material: 'GCr15', description: '外圈压装在机匣前壁，把桨拉力传给机匣与安装桁架。',
    explode: [-180, 0, 0], stage: [0.55, 0.8],
  },
  {
    id: 'bearing-cage', index: 10, name: '钢球保持架', en: 'Ball Cage', role: '保持钢球',
    material: '酚醛胶布', description: '18 粒 Ø22 钢球均布，保持架引导间隙 0.15 mm，飞溅润滑。',
    explode: [0, 0, -420], stage: [0.58, 0.82],
  },
  {
    id: 'scavenge-pump-gear', index: 11, name: '收油泵齿轮', en: 'Oil Scavenge Pump Gear', role: '回油',
    material: '45 钢', description: '直齿轮 14 齿、模数 2.5，把收油池滑油泵回油箱，流量 12 L/min。',
    explode: [-320, -280, 0], stage: [0.5, 0.75],
  },
];

const STEPS: StepDef[] = [
  {
    title: '轮系', en: 'Gear Train',
    body: '两级行星：一级 16/24/64（5:1），二级 16/8/32（3:1），合计 15:1。齿圈固定，太阳轮反转，行星架慢转带动桨毂。',
    state: { explode: 0, section: true, running: false, select: 'planet-gears', focus: null },
  },
  {
    title: '分解', en: 'Exploded',
    body: '机匣、扭矩计筒先后脱开；太阳轮、行星轮、销轴、行星架与内齿圈沿轴向/径向依次伸开。',
    state: { explode: 1, section: false, running: false, select: null, focus: null },
  },
];

const CAMERA: CameraDef = {
  target: [560, AY, 0],
  offset: [1100, 520, 1300],
  orthoDistance: 3600,
  exploded: { target: [560, AY, 0], scale: 1.7 },
};

function Planet({ i }: { i: number }) {
  const a = (i / STAGE1.count) * Math.PI * 2;
  return (
    <group rotation={[a, 0, 0]}>
      <group position={[TP.gearMidX, PR, 0]}>
        <group rotation={[0, 0, Math.PI / 2]}>
          <GearDisc k={`tp-b-planet-${i}`} teeth={STAGE1.planet} pitchR={60} addendum={5} bore={22} thick={40} />
          <Cyl c={[0, 0, 0]} r={26} len={56} axis="x" seg={16} />
        </group>
      </group>
    </group>
  );
}

export function GearboxGroup() {
  return (
    <group>
      <Part id="gearbox-casing">
        <Shell k="tp-b-case" t={16} profile={[[248, 320], [272, 380], [272, 800], [258, 860]]} />
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
      <Part id="sun-gear">
        <GearWheel k="tp-b-sun" x={TP.gearMidX} teeth={TP.sunTeeth} pitchR={40} addendum={5} bore={30} thick={42} hubR={34} hubLen={150} />
        <Cyl c={[TP.gearMidX + 120, AY, 0]} r={44} len={220} axis="x" seg={20} />
        <Callout id="sun-gear" p={[TP.gearMidX + 60, AY + 130, 70]} />
      </Part>
      <Part id="planet-gears">
        <group position={[0, AY, 0]}>
          <group position={[0, -AY, 0]}>
            {Array.from({ length: STAGE1.count }, (_, i) => <Planet key={i} i={i} />)}
          </group>
        </group>
        <Callout id="planet-gears" p={[TP.gearMidX - 40, AY + 190, 80]} />
      </Part>
      <Part id="planet-pins">
        {Array.from({ length: STAGE1.count }, (_, i) => {
          const a = (i / STAGE1.count) * Math.PI * 2;
          return (
            <group key={i}>
              <Cyl c={[TP.gearMidX - 40, AY + Math.cos(a) * PR, Math.sin(a) * PR]} r={21} len={116} axis="x" seg={14} />
              <Cyl c={[TP.gearMidX - 40, AY + Math.cos(a) * PR, Math.sin(a) * PR]} r={8} len={122} axis="x" seg={8} />
            </group>
          );
        })}
        <Callout id="planet-pins" p={[TP.gearMidX - 40, AY + 150, -120]} />
      </Part>
      <Part id="carrier-cage">
        <Cyl c={[TP.gearMidX - 40, AY, 0]} r={128} len={42} axis="x" seg={36} />
        <Cyl c={[TP.gearMidX - 40, AY, 0]} r={58} len={110} axis="x" seg={24} />
        <Callout id="carrier-cage" p={[TP.gearMidX - 40, AY - 180, 80]} />
      </Part>
      <Part id="ring-gear">
        <RingGear k="tp-b-ring" x={TP.gearMidX} teeth={TP.ringTeeth} innerR={155} outerR={215} thick={46} holes={12} />
        <Callout id="ring-gear" p={[TP.gearMidX, AY + 250, 70]} />
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
          <GearDisc k="tp-b-scav" teeth={14} pitchR={36} addendum={4} bore={12} thick={22} holes={3} />
          <Cyl c={[0, 0, 0]} r={12} len={34} axis="x" seg={12} />
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
  summary: '11 种零件 · 16/24/64 + 16/8/32 两级行星，推力轴承承受桨拉力',
  drawingNo: 'GW-TP-B',
  scale: '1 : 2',
  parts: PARTS,
  boltSets: {},
  neighbours: {
    'planet-gears': ['sun-gear', 'planet-pins', 'carrier-cage', 'ring-gear', 'planet-gears'],
    'gearbox-casing': ['ring-gear', 'bearing-outer', 'torque-meter', 'gearbox-casing'],
  },
  guides: [
    { stage: 'sun-gear', origin: [TP.gearMidX + 200, AY, 0] },
    { stage: 'ring-gear', origin: [TP.gearMidX, AY + 240, 0] },
    { stage: 'carrier-cage', origin: [TP.gearMidX - 40, AY - 200, 0] },
  ],
  centreLines: [[[280, AY, 0], [920, AY, 0], 260]] as Array<[Vec3, Vec3, number?]>,
  steps: STEPS,
  camera: CAMERA,
  Model: GearboxGroup,
});
