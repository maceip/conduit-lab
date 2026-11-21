import { Part } from '../../scene/Part';
import { Callout } from '../../scene/Overlay';
import type { CameraDef, MachineDef, PartDef, StepDef, Vec3 } from '../types';
import { Hoop, level, Rod } from '../kit';
import { BoltCircle, FuelManifold, Shell } from './kit';
import { TP } from './data';

const AY = TP.AY;

/**
 * 子组件 E · 环形回流燃烧室 / Annular Reverse-Flow Combustor。
 * 外压力壳 + 火焰筒（3 排掺混孔）+ 14 喷嘴凸台 + 燃油总管 + 2 点火电嘴。
 */

const PARTS: PartDef[] = [
  {
    id: 'outer-case', index: 1, name: '外压力壳', en: 'Outer Pressure Vessel Shell', role: '承压',
    material: 'GH4169', description: '内径 580 mm、壁厚 18 mm，承受 4×10⁵ Pa；前后法兰各 12 螺栓，中分面开 14 喷嘴孔。',
    explode: [0, 0, -420], stage: [0, 0.32],
  },
  {
    id: 'flame-liner', index: 2, name: '火焰筒', en: 'Combustion Flame Liner', role: '燃烧 · 掺混',
    material: 'GH3044', description: '回流环形火焰筒（外径 460 mm、壁厚 3 mm），3 排掺混孔共 96 孔（每排 32 孔），气膜冷却贴壁。',
    explode: [0, 0, 420], stage: [0.12, 0.44],
  },
  {
    id: 'nozzle-bosses', index: 3, name: '喷嘴凸台 ×14', en: 'Fuel Nozzle Bosses ×14', role: '雾化',
    material: '1Cr18Ni9Ti', description: '14 个凸台均布（25.7° 间隔），雾化锥角 80°，喷嘴流量 0.12 L/s·个。',
    explode: [0, 380, 0], stage: [0.3, 0.6],
  },
  {
    id: 'manifold-tubing', index: 4, name: '燃油总管', en: 'Fuel Manifold Tubing', role: '均压供油',
    material: '1Cr18Ni9Ti', description: '环形总管外径 572 mm、管径 Ø34，各喷嘴支管等长均压，防止周向燃油分布不均。',
    explode: [0, 520, 0], stage: [0.34, 0.64],
  },
  {
    id: 'igniter-plugs', index: 5, name: '点火电嘴 ×2', en: 'Igniter Plugs ×2', role: '点火',
    material: '镍基合金', description: '2 支半导体电嘴（火花能量 2 J），位于火焰筒回流区，地面起动点火，空中可连续点火。',
    explode: [-120, 320, 0], stage: [0.38, 0.68],
  },
];

const STEPS: StepDef[] = [
  {
    title: '燃烧室', en: 'Combustor',
    body: '扩压后的空气分两股进火焰筒：主燃孔与燃油喷嘴形成回流区稳定火焰，掺混孔把燃气掺冷到涡轮前温度约 1 100 °C。',
    state: { explode: 0, section: true, running: false, select: 'flame-liner', focus: null },
  },
  {
    title: '分解', en: 'Exploded',
    body: '火焰筒与外压力壳对开，14 个喷嘴凸台随燃油总管径向拉出，点火电嘴最后。',
    state: { explode: 1, section: false, running: false, select: null, focus: null },
  },
];

const CAMERA: CameraDef = {
  target: [-540, AY, 0],
  offset: [1050, 500, 1300],
  orthoDistance: 3300,
  exploded: { target: [-540, AY, 0], scale: 1.7 },
};

export function CombustorGroup() {
  return (
    <group>
      <Part id="outer-case">
        <Shell
          k="tp-e-case"
          t={18}
          profile={[
            [252, 240], [292, 196], [292, 60], [292, -510], [308, -520], [308, -556], [288, -566], [276, -760],
          ]}
        />
        <BoltCircle x={225} r={318} count={12} d={18} len={44} />
        <Callout id="outer-case" p={[-320, AY + 320, 130]} />
      </Part>
      <Part id="flame-liner">
        <Shell k="tp-e-liner" t={10} profile={[[152, TP.linerX1], [232, TP.linerX1 - 24], [232, TP.linerX0 + 40], [168, TP.linerX0]]} />
        {[0, 1, 2].map((row) => {
          const x = TP.linerX1 - 90 - row * 105;
          return (
            <group key={row}>
              <Hoop k={`tp-e-hoop-${row}`} c={[x, AY, 0]} R={234} r={10} axis="x" seg={40} />
              {Array.from({ length: 12 }, (_, i) => {
                const a = (i / 12) * Math.PI * 2 + row * 0.13;
                return (
                  <Rod key={i} a={[x, AY + Math.cos(a) * 150, Math.sin(a) * 150]} b={[x, AY + Math.cos(a) * 238, Math.sin(a) * 238]} r={7} seg={8} />
                );
              })}
            </group>
          );
        })}
        <Callout id="flame-liner" p={[-500, AY + 280, 130]} />
      </Part>
      <Part id="nozzle-bosses">
        <FuelManifold x={-430} r={286} tubeR={17} />
        <Callout id="nozzle-bosses" p={[-430, AY + 330, -110]} />
      </Part>
      <Part id="manifold-tubing">
        <Hoop k="tp-e-manif" c={[-450, AY, 0]} R={286} r={17} axis="x" seg={48} />
        <Callout id="manifold-tubing" p={[-450, AY - 260, 130]} />
      </Part>
      <Part id="igniter-plugs">
        {[1, -1].map((s) => (
          <Rod key={s} a={[-560, AY + s * 120, 150]} b={[-560, AY + s * 246, 150]} r={14} seg={10} />
        ))}
        <Callout id="igniter-plugs" p={[-560, AY + 280, 160]} />
      </Part>
    </group>
  );
}

export const combustor: MachineDef = level({
  id: 'turboprop/combustor',
  parent: 'turboprop',
  unit: 10 / 1100,
  bounds: [[-800, AY - 340, -340], [280, AY + 360, 340]],
  name: '环形回流燃烧室',
  en: 'Annular Reverse-Flow Combustor',
  subtitle: '子组件 E · 14 喷嘴 · 回流火焰筒',
  summary: '5 种零件 · 3 排 96 掺混孔，涡轮前温度约 1 100 °C',
  drawingNo: 'GW-TP-E',
  scale: '1 : 3',
  parts: PARTS,
  boltSets: {},
  neighbours: {
    'flame-liner': ['nozzle-bosses', 'manifold-tubing', 'igniter-plugs', 'flame-liner'],
    'outer-case': ['flame-liner', 'outer-case'],
  },
  guides: [
    { stage: 'flame-liner', origin: [-520, AY + 280, 0] },
    { stage: 'manifold-tubing', origin: [-450, AY + 320, 0] },
  ],
  centreLines: [[[-800, AY, 0], [280, AY, 0], 290]] as Array<[Vec3, Vec3, number?]>,
  steps: STEPS,
  camera: CAMERA,
  Model: CombustorGroup,
});
