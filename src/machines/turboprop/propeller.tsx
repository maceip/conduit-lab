import { Part } from '../../scene/Part';
import { Callout } from '../../scene/Overlay';
import type { CameraDef, MachineDef, PartDef, StepDef, Vec3 } from '../types';
import { level } from '../kit';
import { BoltCircle, FlangeCollar } from './kit';
import { VariablePitchPropellerHub } from '../turboprop-kit';
import { TP } from './data';

const AY = TP.AY;
const U = TP.u;

/**
 * 子组件 A · 螺旋桨与变距机构 / Propeller & Pitch Control（+x 桨头）。
 * VariablePitchPropellerHub 按元件切片包进各 <Part>：
 * 两片整流罩（锥 + 背板）→ 4 臂桨毂 → 液压变距缸 → 4 叶（各自径向爆炸）。
 */

const PARTS: PartDef[] = [
  {
    id: 'spinner-front', index: 1, name: '整流罩前片', en: 'Spinner Dome Front', role: '整流',
    material: '玻璃钢', description: '抛物线双层整流锥前片（长 608 mm），内壁贴 2 mm 防冰加热线。',
    explode: [620, 0, 0], stage: [0, 0.3],
  },
  {
    id: 'spinner-aft', index: 2, name: '整流罩背板', en: 'Spinner Bulkhead Backplate', role: '整流 · 承力',
    material: '玻璃钢', description: '后部环形背板（Ø660）与前片对合，带 4 个桨根让位缺口。',
    explode: [320, 0, 0], stage: [0.05, 0.35],
  },
  {
    id: 'pitch-lock-ring', index: 3, name: '变距锁紧螺栓环', en: 'Pitch-Lock Bolt Ring', role: '锁紧',
    material: '30CrMnSiA', description: '12 条 M10 螺栓沿周向锁紧变距活塞，预紧 45 N·m，拆时先脱 220 mm。',
    explode: [540, 0, 0], stage: [0.1, 0.4],
  },
  {
    id: 'hub-spider', index: 4, name: '桨毂辐条', en: 'Prop Hub Spider', role: '传扭',
    material: '20CrMo 锻钢', description: '4 臂整体锻钢：中心花键筒 + 4 个径向桨根承力套筒，疲劳寿命 12 000 h。',
    explode: [180, 0, 0], stage: [0.35, 0.65],
  },
  {
    id: 'pitch-dome', index: 5, name: '液压变距缸', en: 'Pitch-Change Dome', role: '变距',
    material: '40Cr', description: '双向液压缸（行程 ±25°），工作油压 4 MPa，经变距轴拨动桨叶。',
    explode: [-260, 0, 0], stage: [0.35, 0.65],
  },
  {
    id: 'blade-1', index: 6, name: '桨叶 1', en: 'Blade 1', role: '拉力 · 上',
    material: '钛合金 TC4', description: '48°→16° 洗出扭转、42% 弦长变距轴、桨根配重夹环；径向 +y 拉出 1.15u。',
    explode: [0, 520, 0], stage: [0.6, 0.9],
  },
  {
    id: 'blade-2', index: 7, name: '桨叶 2', en: 'Blade 2', role: '拉力 · 下',
    material: '钛合金 TC4', description: '与 1 号同型、相位 180°；桨根 6×M16 螺栓，离心载荷约 68 kN。',
    explode: [0, -520, 0], stage: [0.6, 0.9],
  },
  {
    id: 'blade-3', index: 8, name: '桨叶 3', en: 'Blade 3', role: '拉力 · 右',
    material: '钛合金 TC4', description: '相位 90°，配重块在叶根内腔；雷击防护铜条沿前缘 40% 弦长。',
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
    body: '4 叶恒速螺旋桨：4 臂桨毂接桨叶根套筒，液压变距缸在后，12 螺栓锁紧环保证桨距不漂移。',
    state: { explode: 0, section: true, running: false, select: 'hub-spider', focus: null },
  },
  {
    title: '分解', en: 'Exploded',
    body: '两片整流罩与锁紧环先脱，桨毂与变距缸分离，4 叶沿各自径向拉出 1.15u。',
    state: { explode: 1, section: false, running: false, select: null, focus: null },
  },
];

const CAMERA: CameraDef = {
  target: [1250, AY, 0],
  offset: [2300, 1000, 2700],
  orthoDistance: 8200,
  exploded: { target: [1500, AY, 0], scale: 1.6 },
};

/** 同一台变距桨组件，按 show/bladeIndices 切片装进各 <Part>。 */
const HubSlice = ({ show, bladeIndices }: { show: Parameters<typeof VariablePitchPropellerHub>[0]['show']; bladeIndices?: number[] }) => (
  <group position={[TP.hubX, AY, 0]}>
    <group scale={U}>
      <VariablePitchPropellerHub hubR={0.625} bladeTipR={2.7} show={show} bladeIndices={bladeIndices} />
    </group>
  </group>
);

export function PropellerGroup() {
  return (
    <group>
      <Part id="spinner-front">
        <HubSlice show={{ spinner: true }} />
        <Callout id="spinner-front" p={[1420, AY + 220, 60]} />
      </Part>
      <Part id="spinner-aft">
        <HubSlice show={{ backplate: true }} />
        <Callout id="spinner-aft" p={[980, AY + 250, 60]} />
      </Part>
      <Part id="pitch-lock-ring">
        <FlangeCollar k="tp-a-lock" x={TP.lockRingX} r={252} thick={36} bossCount={12} bossR={22} />
        <BoltCircle x={TP.lockRingX} r={272} count={12} d={20} len={52} />
        <Callout id="pitch-lock-ring" p={[TP.lockRingX, AY + 310, 80]} />
      </Part>
      <Part id="hub-spider">
        <HubSlice show={{ hub: true }} />
        <Callout id="hub-spider" p={[TP.hubX, AY + 260, 110]} />
      </Part>
      <Part id="pitch-dome">
        <HubSlice show={{ dome: true }} />
        <Callout id="pitch-dome" p={[TP.hubX - 120, AY - 190, 80]} />
      </Part>
      {[0, 1, 2, 3].map((i) => (
        <Part key={i} id={`blade-${i + 1}`}>
          <HubSlice show={{ blades: true }} bladeIndices={[i]} />
          <Callout id={`blade-${i + 1}`} p={[TP.hubX + (i === 0 ? 240 : i === 1 ? -240 : 80), AY + (i === 0 ? 820 : i === 1 ? -820 : 120), i === 2 ? 820 : i === 3 ? -820 : 120]} />
        </Part>
      ))}
    </group>
  );
}

export const propeller: MachineDef = level({
  id: 'turboprop/propeller',
  parent: 'turboprop',
  unit: 10 / 2400,
  bounds: [[820, AY - 1200, -1200], [1620, AY + 1200, 1200]],
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
    { stage: 'hub-spider', origin: [TP.hubX, AY + 200, 0] },
    { stage: 'spinner-front', origin: [1400, AY + 120, 0] },
  ],
  centreLines: [[[820, AY, 0], [1640, AY, 0], TP.propR]] as Array<[Vec3, Vec3, number?]>,
  steps: STEPS,
  camera: CAMERA,
  Model: PropellerGroup,
});
