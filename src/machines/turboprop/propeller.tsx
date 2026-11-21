import { Part } from '../../scene/Part';
import { Callout } from '../../scene/Overlay';
import type { CameraDef, MachineDef, PartDef, StepDef, Vec3 } from '../types';
import { Cyl, Hoop, level, Rod, Turn, tube } from '../kit';
import { Shell } from './kit';
import { BoltCircle, FlangeCollar, PropBlade } from './kit';
import { TP } from './data';

const AY = TP.AY;

/**
 * 子组件 A · 螺旋桨与变距机构 / Propeller & Pitch Control（+x 桨头）。
 * 4 叶恒速桨 + 两片整流罩 + 4 臂桨毂 + 液压变距缸 + 12 螺栓锁紧环。
 * 单位与父级同为毫米；本级沿用同一坐标系（轴线 y=AY）。
 */

const PARTS: PartDef[] = [
  {
    id: 'spinner-front', index: 1, name: '整流罩前片', en: 'Spinner Dome Front', role: '整流',
    material: '玻璃钢', description: '椭球前片，长 200 mm，与后片在 x=980 对合，胶接加 8 颗 M6 环槽螺钉。',
    explode: [620, 0, 0], stage: [0, 0.3],
  },
  {
    id: 'spinner-aft', index: 2, name: '整流罩后片', en: 'Spinner Dome Aft', role: '整流',
    material: '玻璃钢', description: '后片长 220 mm，包住桨毂与变距缸，内壁贴 2 mm 防冰加热线。',
    explode: [320, 0, 0], stage: [0.05, 0.35],
  },
  {
    id: 'pitch-lock-ring', index: 3, name: '变距锁紧螺栓环', en: 'Pitch-Lock Bolt Ring', role: '锁紧',
    material: '30CrMnSiA', description: '12 条 M10 螺栓沿周向锁紧变距活塞，预紧 45 N·m，拆时先脱 220 mm。',
    explode: [540, 0, 0], stage: [0.1, 0.4],
  },
  {
    id: 'hub-spider', index: 4, name: '桨毂辐条', en: 'Prop Hub Spider', role: '传扭',
    material: '20CrMo 锻钢', description: '4 臂整体锻钢，臂宽 90 mm，臂端 6×M16 桨根螺栓孔，疲劳寿命 12 000 h。',
    explode: [180, 0, 0], stage: [0.35, 0.65],
  },
  {
    id: 'pitch-dome', index: 5, name: '液压变距缸', en: 'Pitch-Change Dome', role: '变距',
    material: '40Cr', description: '双向液压缸（行程 ±25°），工作油压 4 MPa，经变距轴拨动桨叶。',
    explode: [-260, 0, 0], stage: [0.35, 0.65],
  },
  {
    id: 'blade-1', index: 6, name: '桨叶 1', en: 'Blade 1', role: '拉力 · 上',
    material: '钛合金 TC4', description: '弦长 300→168 mm 收尖，扭转 22°，巡航桨距 25°；大梁实心钛，前缘不锈钢防蚀条。',
    explode: [0, 520, 0], stage: [0.6, 0.9],
  },
  {
    id: 'blade-2', index: 7, name: '桨叶 2', en: 'Blade 2', role: '拉力 · 下',
    material: '钛合金 TC4', description: '与 1 号同型、相位 180°；桨根法兰 6 螺栓，离心载荷约 68 kN。',
    explode: [0, -520, 0], stage: [0.6, 0.9],
  },
  {
    id: 'blade-3', index: 8, name: '桨叶 3', en: 'Blade 3', role: '拉力 · 右',
    material: '钛合金 TC4', description: '相位 90°，配重块在叶根内腔；雷击防护铜条从前缘延伸 40% 弦长。',
    explode: [0, 0, 520], stage: [0.62, 0.92],
  },
  {
    id: 'blade-4', index: 9, name: '桨叶 4', en: 'Blade 4', role: '拉力 · 左',
    material: '钛合金 TC4', description: '相位 270°；四叶按 90° 均布，动平衡精度 G2.5。',
    explode: [0, 0, -520], stage: [0.62, 0.92],
  },
];

const STEPS: StepDef[] = [
  {
    title: '桨组件', en: 'Propeller Group',
    body: '4 叶恒速螺旋桨：桨毂 4 臂接桨叶根法兰，液压变距缸在后，12 螺栓锁紧环保证桨距不漂移。',
    state: { explode: 0, section: true, running: false, select: 'hub-spider', focus: null },
  },
  {
    title: '分解', en: 'Exploded',
    body: '两片整流罩与锁紧环先脱，桨毂与变距缸分离，4 叶沿各自径向拉出。',
    state: { explode: 1, section: false, running: false, select: null, focus: null },
  },
];

const CAMERA: CameraDef = {
  target: [950, AY, 0],
  offset: [2100, 900, 2500],
  orthoDistance: 7200,
  exploded: { target: [1150, AY, 0], scale: 1.6 },
};

export function PropellerGroup() {
  return (
    <group>
      <Part id="spinner-front">
        <Shell k="tp-a-spinf" t={14} profile={[[34, 1180], [92, 1152], [152, 1112], [206, 1058], [240, 998], [245, 980]]} />
        <Callout id="spinner-front" p={[1120, AY + 160, 60]} />
      </Part>
      <Part id="spinner-aft">
        <Shell k="tp-a-spina" t={14} profile={[[245, 980], [250, 900], [250, 820], [246, 760]]} />
        <Callout id="spinner-aft" p={[880, AY + 220, 60]} />
      </Part>
      <Part id="pitch-lock-ring">
        <FlangeCollar k="tp-a-lock" x={720} r={252} thick={36} bossCount={12} bossR={22} />
        <BoltCircle x={720} r={272} count={12} d={20} len={52} />
        <Callout id="pitch-lock-ring" p={[720, AY + 310, 80]} />
      </Part>
      <Part id="hub-spider">
        {[0, 1, 2, 3].map((i) => {
          const a = (i / 4) * Math.PI * 2 + Math.PI / 4;
          return <Cyl key={i} c={[860, AY + Math.cos(a) * 155, Math.sin(a) * 155]} r={52} len={96} axis="x" seg={16} r2={44} />;
        })}
        <Cyl c={[860, AY, 0]} r={105} len={210} axis="x" seg={32} />
        <FlangeCollar k="tp-a-hubfl" x={800} r={128} thick={30} bossCount={8} bossR={16} />
        <Callout id="hub-spider" p={[860, AY + 260, 110]} />
      </Part>
      <Part id="pitch-dome">
        <Shell k="tp-a-dome" t={14} profile={[[222, 700], [222, 742], [188, 792], [132, 828], [78, 846], [78, 700]]} />
        <Cyl c={[770, AY, 0]} r={92} len={120} axis="x" seg={28} />
        <Turn k="tp-a-piston" axis="x" p={[0, AY, 0]} profile={tube(84, 706, 764, 10)} />
        <Callout id="pitch-dome" p={[770, AY - 190, 80]} />
      </Part>
      {[0, 1, 2, 3].map((i) => (
        <Part key={i} id={`blade-${i + 1}`}>
          <PropBlade i={i} x={TP.hubX} rootR={TP.bladeRootR} tipR={TP.propR} c0={300} c1={168} thick={42} pitch={0.44} />
          <Callout id={`blade-${i + 1}`} p={[TP.hubX, AY + (i === 0 ? 700 : i === 1 ? -700 : 40), i === 2 ? 700 : i === 3 ? -700 : 40]} />
        </Part>
      ))}
    </group>
  );
}

export const propeller: MachineDef = level({
  id: 'turboprop/propeller',
  parent: 'turboprop',
  unit: 10 / 2200,
  bounds: [[700, AY - 1150, -1150], [1220, AY + 1150, 1150]],
  name: '螺旋桨与变距机构',
  en: 'Propeller & Pitch Control',
  subtitle: '子组件 A · 恒速桨 · 4 叶',
  summary: '9 种零件 · 液压变距 ±25°，12 螺栓锁紧环',
  drawingNo: 'GW-TP-A',
  scale: '1 : 8',
  parts: PARTS,
  boltSets: {},
  neighbours: {
    'hub-spider': ['blade-1', 'blade-2', 'blade-3', 'blade-4', 'hub-spider'],
    'pitch-lock-ring': ['spinner-front', 'spinner-aft', 'pitch-lock-ring'],
  },
  guides: [
    { stage: 'blade-1', origin: [TP.hubX, AY + 500, 0] },
    { stage: 'hub-spider', origin: [860, AY + 200, 0] },
    { stage: 'spinner-front', origin: [1100, AY + 120, 0] },
  ],
  centreLines: [[[700, AY, 0], [1240, AY, 0], TP.propR]] as Array<[Vec3, Vec3, number?]>,
  steps: STEPS,
  camera: CAMERA,
  Model: PropellerGroup,
});
