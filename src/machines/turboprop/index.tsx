import { useRef, type ReactNode } from 'react';
import { useFrame } from '@react-three/fiber';
import * as THREE from 'three';
import { Part } from '../../scene/Part';
import { Callout } from '../../scene/Overlay';
import { useStudio } from '../../state';
import type { MachineDef } from '../types';
import { ArcTurn, Box, Cyl, Hoop, Rod, Turn, level, tube } from '../kit';
import {
  BladeRow, BoltCircle, DiffuserPipes, FlangeCollar, FuelManifold, GearDisc, GearWheel,
  Labyrinth, PropBlade, Ribs, RingGear, RotorDisc, Shell,
} from './kit';
import {
  BOM, BOLT_SETS, CAMERA, CENTRE_LINES, DIMENSIONS, GUIDES, NEIGHBOURS, PARTS, STEPS, TP,
} from './data';
import { propeller } from './propeller';
import { gearbox } from './gearbox';
import { airflow } from './airflow';
import { compressor } from './compressor';
import { combustor } from './combustor';
import { turbine } from './turbine';
import { carrierAngle, freeAngle, hpAngle, planetCentre, planetSpin, STAGE1 } from './kinematics';

const AY = TP.AY;

/** 相位量（弧度）；只在「运转」时前进。所有转动件共用这一个相位。 */
export const tpMotion = { phase: 0 };

export function TurbopropDriver() {
  useFrame((_, rawDt) => {
    if (!useStudio.getState().running) return;
    tpMotion.phase += Math.min(rawDt, 0.05) * 0.9;
  }, -1);
  return null;
}

/** 绕发动机轴线（y=AY, z=0，沿 x）转动的组。 */
function SpinX({ which, children }: { which: 'hp' | 'free' | 'prop'; children: ReactNode }) {
  const ref = useRef<THREE.Group>(null);
  useFrame(() => {
    if (!ref.current) return;
    const ph = tpMotion.phase;
    ref.current.rotation.x = which === 'hp' ? hpAngle(ph) : which === 'free' ? freeAngle(ph) : carrierAngle(ph);
  });
  return (
    <group position={[0, AY, 0]}>
      <group ref={ref}>
        <group position={[0, -AY, 0]}>{children}</group>
      </group>
    </group>
  );
}

/** 一级行星轮：随行星架公转（0.05ω），绕自身销轴按真实齿数差动自转。 */
function PlanetGear({ i }: { i: number }) {
  const spin = useRef<THREE.Group>(null);
  useFrame(() => {
    if (spin.current) spin.current.rotation.x = planetSpin(tpMotion.phase);
  });
  const a0 = (i / STAGE1.count) * Math.PI * 2;
  const pr = 105;
  return (
    <group rotation={[a0, 0, 0]}>
      <group position={[0, pr, 0]}>
        <group rotation={[0, 0, Math.PI / 2]}>
          <group ref={spin}>
            <GearDisc k={`tp-planet-${i}`} teeth={STAGE1.planet} pitchR={60} addendum={5} bore={22} thick={40} />
            <Cyl c={[0, 0, 0]} r={26} len={56} axis="x" seg={16} />
          </group>
        </group>
      </group>
    </group>
  );
}

/* ── Wave 1 · 紧固件与外皮 ───────────────────────────────────────── */

function Spinner() {
  const t = 14;
  return (
    <Part id="spinner">
      <SpinX which="prop">
        {/* 前片：椭球整流罩 */}
        <Shell k="tp-spin-f" t={t} profile={[[34, 1180], [92, 1152], [152, 1112], [206, 1058], [240, 998], [245, 980]]} />
        {/* 后片：圆筒+收口，包住桨毂 */}
        <Shell k="tp-spin-a" t={t} profile={[[245, 980], [250, 900], [250, 820], [246, 760]]} />
      </SpinX>
      <Callout id="spinner" p={[1120, AY + 320, 60]} />
    </Part>
  );
}

function PitchLockRing() {
  return (
    <Part id="pitch-lock-ring">
      <SpinX which="prop">
        <FlangeCollar k="tp-lockring" x={720} r={252} thick={36} bossCount={12} bossR={22} />
        <BoltCircle x={720} r={272} count={12} d={20} len={52} set="pitch-bolts" />
      </SpinX>
      <Callout id="pitch-lock-ring" p={[660, AY + 460, 90]} />
    </Part>
  );
}

function CowlUpper() {
  // 上半短舱（y≥0）：ArcTurn 的 φ∈[π, 2π] 正好是上半。
  return (
    <Part id="cowl-upper">
      <ArcTurn
        k="tp-cowl-u"
        axis="x"
        p={[0, AY, 0]}
        phi0={Math.PI}
        phiLen={Math.PI}
        profile={[
          [300, 250], [336, 300], [340, 420], [340, -520], [326, -700], [300, -880],
          [286, -880], [312, -700], [326, -520], [326, 420], [322, 300], [286, 250],
        ]}
      />
      <Ribs x={520} r0={330} r1={362} count={6} thick={16} />
      <Ribs x={-280} r0={330} r1={362} count={6} thick={16} />
      <Callout id="cowl-upper" p={[40, AY + 420, 60]} />
    </Part>
  );
}

function CowlLower() {
  return (
    <Part id="cowl-lower">
      <ArcTurn
        k="tp-cowl-l"
        axis="x"
        p={[0, AY, 0]}
        phi0={0}
        phiLen={Math.PI}
        profile={[
          [300, 250], [336, 300], [340, 420], [340, -520], [326, -700], [300, -880],
          [286, -880], [312, -700], [326, -520], [326, 420], [322, 300], [286, 250],
        ]}
      />
      <Callout id="cowl-lower" p={[40, AY - 420, 60]} />
    </Part>
  );
}

function CombustorCase({ half }: { half: 'a' | 'b' }) {
  // 外机匣（压力壳）：x 240→−760，含压气机-扩压-燃烧段；±z 两半。
  const profile: Array<[number, number]> = [
    [252, 240], [292, 196], [292, 120], [312, 110], [312, 70], [292, 60],
    [292, -510], [308, -520], [308, -556], [288, -566], [276, -760],
    [258, -760], [270, -566], [272, -556], [272, -520], [274, -510],
    [274, 60], [294, 70], [294, 110], [274, 120], [274, 196], [236, 240],
  ];
  return (
    <Part id={`combustor-case-${half}`}>
      <ArcTurn
        k={`tp-case-${half}`}
        axis="x"
        p={[0, AY, 0]}
        phi0={half === 'a' ? -Math.PI / 2 : Math.PI / 2}
        phiLen={Math.PI}
        profile={profile}
      />
      {half === 'a' && <BoltCircle x={225} r={318} count={12} d={18} len={44} set="case-bolts" />}
      <Callout id={`combustor-case-${half}`} p={[-430, AY + (half === 'a' ? 480 : -480), half === 'a' ? 130 : -130]} />
    </Part>
  );
}

/* ── Wave 2 · 大部件分离 ─────────────────────────────────────────── */

function PropHub() {
  return (
    <Part id="prop-hub">
      <SpinX which="prop">
        {/* 4 臂整体锻钢桨毂辐条 */}
        {[0, 1, 2, 3].map((i) => {
          const a = (i / 4) * Math.PI * 2 + Math.PI / 4;
          return (
            <Box key={i} c={[860, AY + Math.cos(a) * 155, Math.sin(a) * 155]} s={[96, 190, 96]} r={[a - Math.PI / 2, 0, 0]} />
          );
        })}
        <Cyl c={[860, AY, 0]} r={105} len={210} axis="x" seg={32} />
        <FlangeCollar k="tp-hub-fl" x={800} r={128} thick={30} bossCount={8} bossR={16} />
        {/* 液压变距缸 */}
        <Shell k="tp-pitchdome" t={14} profile={[[222, 700], [222, 742], [188, 792], [132, 828], [78, 846], [78, 700]]} />
        <Cyl c={[770, AY, 0]} r={92} len={120} axis="x" seg={28} />
      </SpinX>
      <Callout id="prop-hub" p={[900, AY + 250, 110]} />
    </Part>
  );
}

function Gearbox() {
  return (
    <Part id="gearbox">
      {/* 镁合金机匣（挖空）+ 前后凸缘 */}
      <Shell k="tp-gearcase" t={16} profile={[[248, 320], [272, 380], [272, 800], [258, 860]]} />
      <FlangeCollar k="tp-gear-fl0" x={330} r={282} thick={34} bossCount={12} bossR={20} />
      <FlangeCollar k="tp-gear-fl1" x={846} r={268} thick={30} bossCount={12} bossR={18} />
      <BoltCircle x={352} r={302} count={12} d={18} len={44} set="gear-bolts" />
      <Ribs x={430} r0={276} r1={318} count={5} thick={14} />
      <Ribs x={760} r0={262} r1={304} count={5} thick={14} />
      {/* 扭矩计筒 */}
      <Cyl c={[TP.torqueX, AY, 0]} r={145} len={112} axis="x" seg={36} />
      <Turn k="tp-torque-ring" axis="x" p={[0, AY, 0]} profile={[[145, 640], [158, 646], [158, 668], [145, 674]]} />
      {/* 环形径向进气滤网 */}
      <Turn k="tp-inlet-outer" axis="x" p={[0, AY, 0]} profile={tube(272, 296, 328, 12)} />
      <Turn k="tp-inlet-inner" axis="x" p={[0, AY, 0]} profile={tube(208, 296, 328, 12)} />
      <Ribs x={312} r0={214} r1={268} count={18} thick={10} />
      {/* 压气机前轴承机匣 */}
      <Shell k="tp-brg-house" t={14} profile={[[158, 240], [158, 318]]} />
      <FlangeCollar k="tp-brg-fl" x={252} r={168} thick={24} bossCount={8} bossR={14} />
      {/* 前收油泵齿轮（嵌在机匣内） */}
      <group position={[352, AY - 172, 0]}>
        <GearDisc k="tp-scavenge" teeth={14} pitchR={36} addendum={4} bore={12} thick={22} holes={3} />
        <Cyl c={[0, 0, 0]} r={12} len={34} axis="x" seg={12} />
      </group>
      <Callout id="gearbox" p={[430, AY + 420, 120]} />
    </Part>
  );
}

function Exhaust() {
  return (
    <Part id="exhaust">
      {/* 双侧排气短管（上偏 15°） */}
      {[1, -1].map((s) => (
        <group key={s}>
          <Rod a={[-1220, AY + 20, s * 150]} b={[-1280, AY + 60, s * 258]} r={112} seg={22} />
          <Cyl c={[-1360, AY + 72, s * 282]} r={112} len={190} axis="x" seg={22} r2={104} />
          <Turn k={`tp-exh-rim-${s}`} axis="x" p={[0, AY + 72, s * 282]} profile={[[104, -1452], [118, -1458], [118, -1472], [104, -1478]]} />
        </group>
      ))}
      {/* 尾锥 */}
      <Shell k="tp-tailcone" t={14} profile={[[206, -1420], [150, -1466], [86, -1506], [58, -1520]]} />
      <Hoop k="tp-tail-rim" c={[-1424, AY, 0]} R={210} r={16} axis="x" seg={48} />
      <Callout id="exhaust" p={[-1420, AY + 330, 140]} />
    </Part>
  );
}

function FuelManifoldGroup() {
  return (
    <Part id="fuel-manifold">
      <FuelManifold x={-430} r={286} tubeR={17} />
      {/* 2 支点火电嘴 */}
      {[1, -1].map((s) => (
        <Rod key={s} a={[-560, AY + s * 120, 150]} b={[-560, AY + s * 246, 150]} r={14} seg={10} />
      ))}
      <Callout id="fuel-manifold" p={[-430, AY - 330, 100]} />
    </Part>
  );
}

function AccessoryDrive() {
  return (
    <Part id="accessory-drive">
      {/* 锥齿轮副 + 起动发电机座 + 高压燃油泵壳（−y 侧） */}
      <group position={[320, AY - 300, 0]}>
        <GearDisc k="tp-bevel-a" teeth={27} pitchR={72} addendum={6} bore={26} thick={34} />
        <Cyl c={[0, 0, 0]} r={26} len={60} axis="x" seg={16} />
      </group>
      <group position={[320, AY - 366, 0]} rotation={[0, 0, Math.PI / 2]}>
        <GearDisc k="tp-bevel-b" teeth={27} pitchR={72} addendum={6} bore={26} thick={34} />
      </group>
      <Box c={[220, AY - 352, 0]} s={[150, 96, 150]} />
      <Cyl c={[220, AY - 430, 0]} r={78} len={110} axis="y" seg={24} />
      <FlangeCollar k="tp-acc-fl" x={220} r={92} thick={22} bossCount={6} bossR={12} />
      <Callout id="accessory-drive" p={[340, AY - 560, 120]} />
    </Part>
  );
}

/* ── Wave 3 · 内部 telescoping 与径向扇出 ────────────────────────── */

function Blades() {
  return (
    <>
      {[0, 1, 2, 3].map((i) => (
        <Part key={i} id={`blade-${i + 1}`}>
          <SpinX which="prop">
            <PropBlade i={i} x={TP.hubX} rootR={TP.bladeRootR} tipR={TP.propR} c0={300} c1={168} thick={42} pitch={0.44} />
          </SpinX>
          <Callout id={`blade-${i + 1}`} p={[TP.hubX + (i === 0 ? 240 : i === 1 ? -240 : 80), AY + (i === 0 ? 860 : i === 1 ? -860 : 120), i === 2 ? 860 : i === 3 ? -860 : 120]} />
        </Part>
      ))}
    </>
  );
}

function GearTrain() {
  return (
    <>
      <Part id="sun-gear">
        <SpinX which="free">
          <GearWheel k="tp-sun" x={TP.gearMidX} teeth={TP.sunTeeth} pitchR={40} addendum={5} bore={30} thick={42} hubR={34} hubLen={150} />
          <Cyl c={[TP.gearMidX + 120, AY, 0]} r={44} len={220} axis="x" seg={20} />
        </SpinX>
        <Callout id="sun-gear" p={[TP.gearMidX + 260, AY + 380, 70]} />
      </Part>

      <Part id="planet-gears">
        <SpinX which="prop">
          <group position={[TP.gearMidX, AY, 0]}>
            {Array.from({ length: STAGE1.count }, (_, i) => <PlanetGear key={i} i={i} />)}
          </group>
        </SpinX>
        <Callout id="planet-gears" p={[TP.gearMidX - 140, AY + 560, 80]} />
      </Part>

      <Part id="planet-carrier">
        <SpinX which="prop">
          <Cyl c={[TP.gearMidX - 40, AY, 0]} r={128} len={42} axis="x" seg={36} />
          <Cyl c={[TP.gearMidX - 40, AY, 0]} r={58} len={110} axis="x" seg={24} />
          {Array.from({ length: STAGE1.count }, (_, i) => {
            const a = (i / STAGE1.count) * Math.PI * 2;
            return (
              <Rod
                key={i}
                a={[TP.gearMidX - 40, AY + Math.cos(a) * 26, Math.sin(a) * 26]}
                b={[TP.gearMidX - 40, AY + Math.cos(a) * 152, Math.sin(a) * 152]}
                r={21}
                seg={12}
              />
            );
          })}
        </SpinX>
        <Callout id="planet-carrier" p={[TP.gearMidX + 40, AY - 420, 80]} />
      </Part>

      <Part id="ring-gear">
        <RingGear k="tp-ring" x={TP.gearMidX} teeth={TP.ringTeeth} innerR={155} outerR={215} thick={46} holes={12} />
        <Callout id="ring-gear" p={[TP.gearMidX - 240, AY + 740, 70]} />
      </Part>
    </>
  );
}

function Spool() {
  const rotors = [
    { id: 'rotor-1', x: TP.rotor1X, tip: TP.rotorTipR[0], n: TP.bladeCounts[0], k: 0 },
    { id: 'rotor-2', x: TP.rotor2X, tip: TP.rotorTipR[1], n: TP.bladeCounts[1], k: 1 },
    { id: 'rotor-3', x: TP.rotor3X, tip: TP.rotorTipR[2], n: TP.bladeCounts[2], k: 2 },
  ];
  const stators = [
    { id: 'stator-1', x: TP.stator1X, n: TP.statorCounts[0], k: 3 },
    { id: 'stator-2', x: TP.stator2X, n: TP.statorCounts[1], k: 4 },
    { id: 'stator-3', x: TP.stator3X, n: TP.statorCounts[2], k: 5 },
  ];
  return (
    <>
      {rotors.map(({ id, x, tip, n, k }) => (
        <Part key={id} id={id}>
          <SpinX which="hp">
            <RotorDisc k={`tp-${id}`} x={x} rimR={tip - 26} hubR={72} thick={42} tabs={20} />
            <BladeRow k={`tp-${id}`} x={x} count={n} rootR={96} tipR={tip} chord={42} thick={13} pitch={0.56} stagger={0.002} />
            <Labyrinth x0={x + 30} r={78} teeth={5} />
          </SpinX>
          <Callout id={id} p={[x + 140, AY + tip + 120 + k * 190, 70]} />
        </Part>
      ))}
      {stators.map(({ id, x, n, k }) => (
        <Part key={id} id={id}>
          <BladeRow k={`tp-${id}`} x={x} count={n} rootR={102} tipR={TP.statorOuterR} chord={42} thick={12} pitch={-0.52} />
          <Turn k={`tp-${id}-ring`} axis="x" p={[0, AY, 0]} profile={tube(TP.statorOuterR, x - 26, x + 26, 12)} />
          <Callout id={id} p={[x - 60, AY + TP.statorOuterR + 210 + (k - 3) * 190, -70]} />
        </Part>
      ))}

      <Part id="impeller">
        <SpinX which="hp">
          <RotorDisc k="tp-imp" x={TP.impellerX} rimR={196} hubR={54} thick={64} tabs={12} />
          {/* 12 长叶 + 12 短叶（交错），出口角 26° */}
          <BladeRow k="tp-imp-l" x={TP.impellerX} count={12} rootR={58} tipR={TP.impellerR} chord={62} thick={16} pitch={0.45} a0={0} stagger={0.004} />
          <BladeRow k="tp-imp-s" x={TP.impellerX} count={12} rootR={58} tipR={TP.impellerR * 0.82} chord={44} thick={13} pitch={0.42} a0={Math.PI / 12} />
        </SpinX>
        <DiffuserPipes x={TP.impellerX} r0={TP.impellerR + 8} r1={286} count={12} r={15} />
        <Callout id="impeller" p={[TP.impellerX + 60, AY + 300 + 6 * 190, 80]} />
      </Part>
    </>
  );
}

function CombustorLiner() {
  return (
    <Part id="combustor-liner">
      {/* 回流环形火焰筒：外筒 + 内筒 + 3 排掺混孔 */}
      <Shell k="tp-liner" t={10} profile={[[152, TP.linerX1], [232, TP.linerX1 - 24], [232, TP.linerX0 + 40], [168, TP.linerX0]]} />
      {[0, 1, 2].map((row) => {
        const x = TP.linerX1 - 90 - row * 105;
        return (
          <group key={row}>
            <Hoop k={`tp-liner-hoop-${row}`} c={[x, AY, 0]} R={234} r={10} axis="x" seg={40} />
            {Array.from({ length: 12 }, (_, i) => {
              const a = (i / 12) * Math.PI * 2 + row * 0.13;
              return (
                <Rod key={i} a={[x, AY + Math.cos(a) * 150, Math.sin(a) * 150]} b={[x, AY + Math.cos(a) * 238, Math.sin(a) * 238]} r={7} seg={8} />
              );
            })}
          </group>
        );
      })}
      <Callout id="combustor-liner" p={[TP.linerX1 - 140, AY + 270 + 7 * 150, 80]} />
    </Part>
  );
}

function Turbines() {
  return (
    <>
      <Part id="hp-turbine">
        {/* 导向器环（静止） */}
        <BladeRow k="tp-ngv" x={TP.ngvX} count={34} rootR={106} tipR={192} chord={36} thick={11} pitch={0.72} />
        <Turn k="tp-ngv-ring" axis="x" p={[0, AY, 0]} profile={tube(192, TP.ngvX - 22, TP.ngvX + 22, 12)} />
        {/* 高压涡轮盘（1.0ω） */}
        <SpinX which="hp">
          <RotorDisc k="tp-hpdisc" x={TP.hpX} rimR={142} hubR={58} thick={46} tabs={18} />
          <BladeRow k="tp-hpbl" x={TP.hpX} count={29} rootR={88} tipR={TP.hpR} chord={44} thick={13} pitch={0.52} stagger={0.002} />
        </SpinX>
        {/* 级间挡板（静止） */}
        <Turn k="tp-baffle" axis="x" p={[0, AY, 0]} profile={[[70, TP.baffleX - 16], [152, TP.baffleX - 6], [152, TP.baffleX + 12], [70, TP.baffleX + 20]]} />
        <Callout id="hp-turbine" p={[TP.hpX + 120, AY + 240 + 8 * 150, 70]} />
      </Part>

      <Part id="pt-disk-1">
        <SpinX which="free">
          <RotorDisc k="tp-pt1disc" x={TP.pt1X} rimR={152} hubR={62} thick={44} tabs={18} />
          <BladeRow k="tp-pt1bl" x={TP.pt1X} count={31} rootR={92} tipR={TP.ptR} chord={48} thick={13} pitch={-0.5} stagger={0.002} />
          <Labyrinth x0={TP.pt1X + 34} r={72} teeth={5} />
        </SpinX>
        <Callout id="pt-disk-1" p={[TP.pt1X + 160, AY + 230 + 9 * 150, 70]} />
      </Part>

      <Part id="pt-disk-2">
        <SpinX which="free">
          <RotorDisc k="tp-pt2disc" x={TP.pt2X} rimR={152} hubR={62} thick={44} tabs={18} />
          <BladeRow k="tp-pt2bl" x={TP.pt2X} count={33} rootR={92} tipR={TP.ptR} chord={48} thick={13} pitch={-0.52} stagger={0.002} />
          {/* 同心内轴：穿过空心高压转子把功率送到太阳轮 */}
          <Cyl c={[(TP.pt2X + TP.gearMidX) / 2, AY, 0]} r={TP.shaftR} len={TP.gearMidX - TP.pt2X} axis="x" seg={28} />
          <Labyrinth x0={TP.pt2X + 34} r={72} teeth={5} />
          <Labyrinth x0={TP.linerX0 + 60} r={70} teeth={4} />
        </SpinX>
        <Callout id="pt-disk-2" p={[TP.pt2X + 200, AY + 230 + 10 * 150, -70]} />
      </Part>
    </>
  );
}

function MountTruss() {
  // 4 管空间桁架，最低点 y=0，上端接齿轮箱机匣。
  const feet: Array<[number, number]> = [[260, 230], [260, -230], [-260, 230], [-260, -230]];
  const tops: Array<[number, number]> = [[180, 150], [180, -150], [-180, 150], [-180, -150]];
  return (
    <Part id="mount-truss">
      {feet.map(([fx, fz], i) => (
        <Rod key={i} a={[fx, 0, fz]} b={[tops[i][0], AY - 300, tops[i][1]]} r={24} seg={12} />
      ))}
      <Rod a={[260, 60, 230]} b={[-260, 60, 230]} r={18} seg={10} />
      <Rod a={[260, 60, -230]} b={[-260, 60, -230]} r={18} seg={10} />
      <Rod a={[260, 60, 230]} b={[260, 60, -230]} r={18} seg={10} />
      <Rod a={[-260, 60, 230]} b={[-260, 60, -230]} r={18} seg={10} />
      <Box c={[0, AY - 318, 0]} s={[560, 42, 340]} />
      <Box c={[0, 14, 0]} s={[620, 28, 560]} />
      <Callout id="mount-truss" p={[-120, 120, 280]} />
    </Part>
  );
}

export function Turboprop() {
  return (
    <group>
      <Spinner />
      <PitchLockRing />
      <CowlUpper />
      <CowlLower />
      <CombustorCase half="a" />
      <CombustorCase half="b" />
      <PropHub />
      <Gearbox />
      <Exhaust />
      <FuelManifoldGroup />
      <AccessoryDrive />
      <Blades />
      <GearTrain />
      <Spool />
      <CombustorLiner />
      <Turbines />
      <MountTruss />
    </group>
  );
}

export const turboprop: MachineDef = level({
  id: 'turboprop',
  unit: 10 / 2700,
  bounds: [[TP.tailX - 60, 0, -TP.propR - 80], [TP.spinnerX1 + 60, TP.AY + TP.propR + 80, TP.propR + 80]],
  name: '涡轮螺旋桨发动机',
  en: 'Turboprop Engine',
  subtitle: '装配体 · 双转子 · 两级行星减速 · 半剖',
  summary: '31 种零件 · 6 个子组件 · 15:1 行星减速带动 4 叶恒速螺旋桨',
  drawingNo: 'GW-TP-00',
  scale: '1 : 10',
  parts: PARTS,
  boltSets: BOLT_SETS,
  neighbours: NEIGHBOURS,
  guides: GUIDES,
  centreLines: CENTRE_LINES,
  steps: STEPS,
  camera: CAMERA,
  Model: Turboprop,
  Driver: TurbopropDriver,
  children: {
    'prop-hub': 'turboprop/propeller',
    spinner: 'turboprop/propeller',
    'pitch-lock-ring': 'turboprop/propeller',
    gearbox: 'turboprop/gearbox',
    'accessory-drive': 'turboprop/airflow',
    'rotor-1': 'turboprop/compressor',
    impeller: 'turboprop/compressor',
    'combustor-liner': 'turboprop/combustor',
    'combustor-case-a': 'turboprop/combustor',
    'hp-turbine': 'turboprop/turbine',
    exhaust: 'turboprop/turbine',
  },
  dimensions: DIMENSIONS,
  bom: BOM,
});

/** 六个子组件（A–F），在 machines/index.ts 的 ALL 里展开。 */
export const TURBOPROP_LEVELS = [propeller, gearbox, airflow, compressor, combustor, turbine];
