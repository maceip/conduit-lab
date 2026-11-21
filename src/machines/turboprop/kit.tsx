import * as THREE from 'three';
import { M } from '../../scene/Part';
import { gearShape } from '../../scene/geometry';
import { Box, Cyl, Fastener, Plate, Rod, Turn, XZ_Y, YZ_X, poly, type Dir } from '../kit';
import type { Vec3 } from '../types';
import { TP, AY } from './data';

/**
 * 涡桨发动机几何积木 / procedural geometry kit.
 *
 * 纪律：全部毫米；轴线在 (·, AY, 0)、沿 x；缓存键一律 tp- 前缀；
 * 转子/齿轮绝不留"占位圆柱"——叶片是带桨距的翼型，齿轮有齿廓与腹板轻化孔，
 * 机匣有凸缘螺栓座、加强肋与周向紧固件阵列。
 */

/* ── 翼型与叶片阵列 ─────────────────────────────────────────────── */

/** 翼型截面（弦长 c、厚 t），位于 (轴向, 周向) 平面。 */
export function airfoilShape(c: number, t: number) {
  return poly([
    [-c * 0.5, 0],
    [-c * 0.42, t * 0.42],
    [-c * 0.1, t * 0.5],
    [c * 0.35, t * 0.32],
    [c * 0.5, t * 0.06],
    [c * 0.5, -t * 0.06],
    [c * 0.35, -t * 0.32],
    [-c * 0.1, -t * 0.5],
    [-c * 0.42, -t * 0.42],
  ]);
}

/**
 * 径向叶片阵列：count 片绕 x 轴均布，每片绕自身径向轴倾斜 pitch（弦向桨距），
 * 相邻片再加 stagger 扭转差。count ∈ 19..37 为压气机/涡轮叶排，4 为螺旋桨。
 */
export function BladeRow({
  k, x, count, rootR, tipR, chord, thick, pitch, stagger = 0, a0 = 0, lean = 0,
}: {
  k: string; x: number; count: number; rootR: number; tipR: number;
  chord: number; thick: number; pitch: number; stagger?: number; a0?: number; lean?: number;
}) {
  const span = tipR - rootR;
  return (
    <>
      {Array.from({ length: count }, (_, i) => {
        const theta = (i / count) * Math.PI * 2 + a0;
        return (
          <group key={i} position={[0, AY, 0]}>
            <group rotation={[theta, 0, 0]}>
            <group position={[x, 0, 0]}>
              <group rotation={[0, pitch + (i - (count - 1) / 2) * stagger, 0]}>
                <Plate
                  k={`tp-${k}-bl${i}`}
                  shape={airfoilShape(chord, thick)}
                  depth={span}
                  p={[lean * span * 0.5, rootR, 0]}
                  r={XZ_Y}
                />
              </group>
            </group>
            </group>
          </group>
        );
      })}
    </>
  );
}

/** 桨叶：大展弦比翼型，根部弦长 c0、尖部弦长 c1，带 25° 巡航桨距。 */
export function PropBlade({ i, x, rootR, tipR, c0, c1, thick, pitch }: {
  i: number; x: number; rootR: number; tipR: number; c0: number; c1: number; thick: number; pitch: number;
}) {
  const theta = (i / 4) * Math.PI * 2 + Math.PI / 4;
  const span = tipR - rootR;
  return (
    <group position={[0, AY, 0]}>
      <group rotation={[theta, 0, 0]}>
      <group position={[x, 0, 0]}>
        <group rotation={[0, pitch, 0]}>
          {/* 根段与尖段两截翼型，弦长收窄模拟扭转桨叶 */}
          <Plate k={`tp-pb${i}-r`} shape={airfoilShape(c0, thick)} depth={span * 0.55} p={[0, rootR, 0]} r={XZ_Y} />
          <Plate k={`tp-pb${i}-t`} shape={airfoilShape(c1, thick * 0.7)} depth={span * 0.45} p={[0, rootR + span * 0.55, 0]} r={XZ_Y} />
          {/* 桨根接头 */}
          <Cyl c={[0, rootR + 18, 0]} r={38} len={90} axis="y" seg={20} />
        </group>
      </group>
      </group>
    </group>
  );
}

/* ── 齿轮（齿廓 + 腹板轻化孔） ──────────────────────────────────── */

/** 齿轮腹板：渐开线齿廓（梯形齿）+ 中孔 + 均布轻化孔。 */
export function gearWebShape(teeth: number, pitchR: number, addendum: number, bore: number, holes: Array<[number, number, number]>) {
  return () => {
    const s = gearShape(teeth, pitchR, addendum, bore);
    for (const [hx, hy, hr] of holes) {
      const h = new THREE.Path();
      h.absarc(hx, hy, hr, 0, Math.PI * 2, true);
      s.holes.push(h);
    }
    return s;
  };
}

/** 齿盘本体（原点处、轴线沿 x），行星轮在自己的径向坐标系里用。 */
export function GearDisc({ k, teeth, pitchR, addendum, bore, thick, holes = 5, holeR }: {
  k: string; teeth: number; pitchR: number; addendum: number; bore: number; thick: number; holes?: number; holeR?: number;
}) {
  const rHole = holeR ?? pitchR * 0.22;
  const ringR = pitchR * 0.55;
  const web = holes > 0
    ? Array.from({ length: holes }, (_, i) => {
      const a = (i / holes) * Math.PI * 2;
      return [Math.cos(a) * ringR, Math.sin(a) * ringR, rHole] as [number, number, number];
    })
    : [];
  return <Plate k={`tp-${k}-web`} shape={gearWebShape(teeth, pitchR, addendum, bore, web)} depth={thick} p={[0, 0, 0]} r={YZ_X} />;
}

/**
 * 行星/直齿轮：轴线沿 x 的齿圈盘，腹板开 count 个轻化孔，带轮毂短轴。
 * teeth ∈ 8..64；addendum/dedendum 由 gearShape 给出（齿顶高/齿根高 1.25 倍）。
 */
export function GearWheel({
  k, x, teeth, pitchR, addendum, bore, thick, holes = 5, holeR, hubR, hubLen = 0,
}: {
  k: string; x: number; teeth: number; pitchR: number; addendum: number; bore: number;
  thick: number; holes?: number; holeR?: number; hubR?: number; hubLen?: number;
}) {
  const rHole = holeR ?? pitchR * 0.22;
  const ringR = pitchR * 0.55;
  const web = holes > 0
    ? Array.from({ length: holes }, (_, i) => {
      const a = (i / holes) * Math.PI * 2;
      return [Math.cos(a) * ringR, Math.sin(a) * ringR, rHole] as [number, number, number];
    })
    : [];
  return (
    <>
      <Plate k={`tp-${k}-web`} shape={gearWebShape(teeth, pitchR, addendum, bore, web)} depth={thick} p={[x, AY, 0]} r={YZ_X} />
      {hubR !== undefined && hubLen > 0 && <Cyl c={[x, AY, 0]} r={hubR} len={hubLen} axis="x" seg={28} />}
    </>
  );
}

/** 内齿圈：环形齿圈（齿朝内），腹板均布销孔。 */
export function RingGear({
  k, x, teeth, innerR, outerR, thick, holes = 12,
}: {
  k: string; x: number; teeth: number; innerR: number; outerR: number; thick: number; holes?: number;
}) {
  // 内齿：齿顶在内侧。用外径盘挖出带齿的内孔——齿廓取反（把 gearShape 画在孔上）。
  const shape = () => {
    const s = new THREE.Shape();
    s.absarc(0, 0, outerR, 0, Math.PI * 2, false);
    const hole = new THREE.Path();
    const rOut = innerR;
    const rRoot = innerR * 1.12;
    const step = (Math.PI * 2) / teeth;
    const pts: Array<[number, number]> = [];
    for (let i = 0; i < teeth; i += 1) {
      const a = i * step;
      pts.push(
        [Math.cos(a - step * 0.3) * rRoot, Math.sin(a - step * 0.3) * rRoot],
        [Math.cos(a - step * 0.14) * rOut, Math.sin(a - step * 0.14) * rOut],
        [Math.cos(a + step * 0.14) * rOut, Math.sin(a + step * 0.14) * rOut],
        [Math.cos(a + step * 0.3) * rRoot, Math.sin(a + step * 0.3) * rRoot],
      );
    }
    hole.moveTo(...pts[0]);
    pts.slice(1).forEach((p) => hole.lineTo(...p));
    hole.closePath();
    s.holes.push(hole);
    for (let i = 0; i < holes; i += 1) {
      const a = (i / holes) * Math.PI * 2 + Math.PI / holes;
      const h = new THREE.Path();
      h.absarc(Math.cos(a) * (outerR + innerR) / 2, Math.sin(a) * (outerR + innerR) / 2, outerR * 0.07, 0, Math.PI * 2, true);
      s.holes.push(h);
    }
    return s;
  };
  return <Plate k={`tp-${k}`} shape={shape} depth={thick} p={[x, AY, 0]} r={YZ_X} />;
}

/* ── 机匣凸缘、加强肋、紧固件阵列 ───────────────────────────────── */

/** 周向螺栓阵列（凸缘法兰）。set 给出时螺栓随爆炸窗先脱。 */
export function BoltCircle({ x, r, count, d = 22, len = 46, dir = 'x', set }: {
  x: number; r: number; count: number; d?: number; len?: number; dir?: Dir; set?: string;
}) {
  return (
    <>
      {Array.from({ length: count }, (_, i) => {
        const a = (i / count) * Math.PI * 2;
        return (
          <Fastener key={i} p={[x, AY + Math.cos(a) * r, Math.sin(a) * r]} dir={dir} set={set} d={d} len={len} />
        );
      })}
    </>
  );
}

/** 凸缘环：带一圈凸起螺栓座（raised bolt bosses）的厚环。 */
export function FlangeCollar({ k, x, r, thick, bossCount = 12, bossR }: {
  k: string; x: number; r: number; thick: number; bossCount?: number; bossR?: number;
}) {
  const br = bossR ?? r * 0.09;
  return (
    <>
      <Cyl c={[x, AY, 0]} r={r} len={thick} axis="x" seg={48} />
      {Array.from({ length: bossCount }, (_, i) => {
        const a = (i / bossCount) * Math.PI * 2;
        return <Cyl key={i} c={[x, AY + Math.cos(a) * (r - br * 0.2), Math.sin(a) * (r - br * 0.2)]} r={br} len={thick + 14} axis="x" seg={12} />;
      })}
    </>
  );
}

/** 结构加强肋：沿周向的径向肋板。 */
export function Ribs({ x, r0, r1, count, thick = 14 }: { x: number; r0: number; r1: number; count: number; thick?: number }) {
  return (
    <>
      {Array.from({ length: count }, (_, i) => {
        const a = (i / count) * Math.PI * 2;
        const mid = (r0 + r1) / 2;
        return (
          <Box key={i} c={[x, AY + Math.cos(a) * mid, Math.sin(a) * mid]} s={[thick, r1 - r0, 16]} r={[a - Math.PI / 2, 0, 0]} />
        );
      })}
    </>
  );
}

/* ── 密封与管路 ─────────────────────────────────────────────────── */

/** 迷宫密封：轴上一叠方齿（气流曲折泄漏路径）。 */
export function Labyrinth({ x0, r, teeth, toothH = 14, toothW = 12, gap = 26 }: {
  x0: number; r: number; teeth: number; toothH?: number; toothW?: number; gap?: number;
}) {
  const profile: Array<[number, number]> = [];
  let x = x0;
  for (let i = 0; i < teeth; i += 1) {
    profile.push([r, x], [r + toothH, x], [r + toothH, x + toothW], [r, x + toothW]);
    x += toothW + gap;
  }
  profile.push([r, x], [r + 40, x], [r + 40, x0], [r, x0]);
  return <Turn k={`tp-lab-${x0}-${teeth}`} profile={profile} axis="x" seg={36} p={[0, AY, 0]} />;
}

/** 径向扩压管阵列：从叶轮外缘径向甩出、再折向 −x。 */
export function DiffuserPipes({ x, r0, r1, count, r }: { x: number; r0: number; r1: number; count: number; r: number }) {
  return (
    <>
      {Array.from({ length: count }, (_, i) => {
        const a = (i / count) * Math.PI * 2;
        const cy = Math.cos(a);
        const sz = Math.sin(a);
        return (
          <group key={i}>
            <Rod a={[x, AY + cy * r0, sz * r0]} b={[x, AY + cy * r1, sz * r1]} r={r} seg={12} />
            <Rod a={[x, AY + cy * r1, sz * r1]} b={[x - 80, AY + cy * r1, sz * r1]} r={r} seg={12} />
          </group>
        );
      })}
    </>
  );
}

/** 燃油总管环 + 14 个喷嘴凸台。 */
export function FuelManifold({ x, r, tubeR = 16 }: { x: number; r: number; tubeR?: number }) {
  return (
    <>
      <Turn k={`tp-manif-${x}`} profile={[[r - tubeR, x], [r, x], [r, x + 40], [r - tubeR, x + 40]]} axis="x" seg={48} p={[0, AY, 0]} />
      {Array.from({ length: 14 }, (_, i) => {
        const a = (i / 14) * Math.PI * 2;
        const cy = Math.cos(a);
        const sz = Math.sin(a);
        return (
          <group key={i}>
            <Rod a={[x, AY + cy * (r - 70), sz * (r - 70)]} b={[x, AY + cy * (r + 10), sz * (r + 10)]} r={22} seg={10} />
            <Rod a={[x, AY + cy * (r - 70), sz * (r - 70)]} b={[x - 60, AY + cy * (r - 130), sz * (r - 130)]} r={14} seg={10} />
          </group>
        );
      })}
    </>
  );
}

/** 转子盘：带榫槽凸台的实心盘（外缘一圈叶根凸台）。 */
export function RotorDisc({ k, x, rimR, hubR, thick, tabs = 24 }: {
  k: string; x: number; rimR: number; hubR: number; thick: number; tabs?: number;
}) {
  return (
    <>
      <Turn
        k={`tp-${k}-disc`}
        profile={[[hubR, x - thick / 2], [rimR, x - thick / 2], [rimR, x + thick / 2], [hubR, x + thick / 2]]}
        axis="x"
        seg={48}
        p={[0, AY, 0]}
      />
      <Cyl c={[x, AY, 0]} r={hubR * 1.25} len={thick * 2.2} axis="x" seg={32} />
      {Array.from({ length: tabs }, (_, i) => {
        const a = (i / tabs) * Math.PI * 2;
        return (
          <Box key={i} c={[x, AY + Math.cos(a) * rimR, Math.sin(a) * rimR]} s={[thick * 0.8, 18, 18]} r={[a - Math.PI / 2, 0, 0]} />
        );
      })}
    </>
  );
}

/** 薄壁回转壳（外轮廓 + 反向内轮廓，剖视是空心）。 */
export function Shell({ k, profile, t = TP.wall, seg = 48 }: { k: string; profile: Array<[number, number]>; t?: number; seg?: number }) {
  // profile 是外轮廓 (半径, x)；内轮廓沿径向缩 t。
  const outer = profile;
  const inner = [...profile].reverse().map(([r, x]): [number, number] => [Math.max(6, r - t), x]);
  return <Turn k={`tp-${k}`} profile={[...outer, ...inner]} axis="x" seg={seg} p={[0, AY, 0]} />;
}

export type { Vec3 };
