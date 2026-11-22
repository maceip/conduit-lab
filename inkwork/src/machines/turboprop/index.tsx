import { useRef, type ReactNode } from 'react';
import { useFrame } from '@react-three/fiber';
import * as THREE from 'three';
import { Part } from '../../scene/Part';
import { Callout } from '../../scene/Overlay';
import { motion, useStudio } from '../../state';
import type { MachineDef } from '../types';
import { ArcTurn, Box, Cyl, Hoop, Rod, Turn, level, tube } from '../kit';
import {
  AnnularCombustorLiner, AxialBladeDisk, CentrifugalImpeller, HollowSteppedShaft, ToothedGear, VariablePitchPropellerHub,
} from '../turboprop-kit';
import { BladeRow, BoltCircle, DiffuserPipes, FlangeCollar, Ribs, Shell } from './kit';
import {
  ANNOTATIONS, BOM, BOLT_SETS, CAMERA, CENTRE_LINES, DIMENSIONS, GUIDES, NEIGHBOURS, PARTS, STEPS, TP,
} from './data';
import { propeller } from './propeller';
import { gearbox } from './gearbox';
import { airflow } from './airflow';
import { compressor } from './compressor';
import { combustor } from './combustor';
import { turbine } from './turbine';
import { carrierAngle, freeAngle, hpAngle, planetSpin, STAGE1 } from './kinematics';

const AY = TP.AY;
const U = TP.u;
/** Millimetre station → the component u design space (1u = TP.u mm). */
const at = (x: number, y = AY, z = 0) => [x, y, z] as [number, number, number];

/** Shared phase (radians); only advances while running. Every rotating part reads it. */
export const tpMotion = { phase: 0 };

export function TurbopropDriver() {
  useFrame((_, rawDt) => {
    if (!useStudio.getState().running) return;
    tpMotion.phase += Math.min(rawDt, 0.05) * 0.9;
  }, -1);
  return null;
}

/** Group spinning about the engine centreline (y=AY, z=0, along x). */
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

/**
 * First-stage planet: orbits with the carrier (0.05ω), spins on its pin at the
 * true epicyclic ratio, and fans out radially along that pin (map Planets +0.55u
 * = 220 mm). Gear axes stay parallel to the shaft — the correct spur planetary.
 */
function PlanetGear({ i }: { i: number }) {
  const spin = useRef<THREE.Group>(null);
  const orbit = useRef<THREE.Group>(null);
  useFrame(() => {
    const ph = tpMotion.phase;
    if (spin.current) spin.current.rotation.x = planetSpin(ph);
    // radial fan (planet window 0.63→0.83, map: Planets +0.55u = 220 mm)
    const t = Math.min(1, Math.max(0, (motion.explode - 0.63) / 0.2));
    const s = t * t * (3 - 2 * t);
    if (orbit.current) orbit.current.position.y = 100 + 220 * s;
  });
  const a0 = (i / STAGE1.count) * Math.PI * 2;
  return (
    <group rotation={[a0, 0, 0]}>
      <group ref={orbit} position={[0, 100, 0]}>
        <group ref={spin}>
          <group scale={U}>
            <ToothedGear teeth={STAGE1.planet} module={0.0125} thickness={0.1} boreR={0.055} lighteningHoles={4} />
          </group>
        </group>
      </group>
    </group>
  );
}

/* ── Wave 1 · fasteners & outer skins ───────────────────────────────────────── */

function Spinner() {
  return (
    <Part id="spinner">
      <SpinX which="prop">
        <group position={at(TP.hubX)}>
          <group scale={U}>
            <VariablePitchPropellerHub hubR={0.625} bladeTipR={2.7} show={{ spinner: true, backplate: true }} />
          </group>
        </group>
      </SpinX>
      <Callout id="spinner" p={[1420, AY + 260, 60]} />
    </Part>
  );
}

function PitchLockRing() {
  return (
    <Part id="pitch-lock-ring">
      <SpinX which="prop">
        <FlangeCollar k="tp-lockring" x={TP.lockRingX} r={252} thick={36} bossCount={12} bossR={22} />
        <BoltCircle x={TP.lockRingX} r={272} count={12} d={20} len={52} set="pitch-bolts" />
      </SpinX>
      <Callout id="pitch-lock-ring" p={[TP.lockRingX, AY + 320, 90]} />
    </Part>
  );
}

/** Nacelle / outer-case meridian ((r, x) outer contour) for the map stations. */
function nacelleProfile(): Array<[number, number]> {
  return [
    [330, 300], [372, 240], [380, 60], [380, -760], [368, -1020], [344, -1300],
    [322, -1300], [346, -1020], [358, -760], [358, 60], [350, 240], [310, 300],
  ];
}

function CowlUpper() {
  return (
    <Part id="cowl-upper">
      <ArcTurn k="tp-cowl-u" axis="x" p={[0, AY, 0]} phi0={Math.PI} phiLen={Math.PI} profile={nacelleProfile()} />
      <Ribs x={-160} r0={372} r1={406} count={6} thick={16} />
      <Ribs x={-900} r0={362} r1={396} count={6} thick={16} />
      <Callout id="cowl-upper" p={[-160, AY + 420, 60]} />
    </Part>
  );
}

function CowlLower() {
  return (
    <Part id="cowl-lower">
      <ArcTurn k="tp-cowl-l" axis="x" p={[0, AY, 0]} phi0={0} phiLen={Math.PI} profile={nacelleProfile()} />
      <Callout id="cowl-lower" p={[-160, AY - 420, 60]} />
    </Part>
  );
}

function CombustorCase({ half }: { half: 'a' | 'b' }) {
  // outer case (pressure shell): x 300→−1420 around compressor/diffuser/combustor; two ±z halves.
  const profile: Array<[number, number]> = [
    [252, 300], [312, 250], [332, 180], [332, -1180], [322, -1320], [308, -1420],
    [288, -1420], [302, -1320], [312, -1180], [312, 180], [294, 250], [236, 300],
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
      {half === 'a' && <BoltCircle x={272} r={352} count={12} d={18} len={44} set="case-bolts" />}
      <Callout id={`combustor-case-${half}`} p={[-420, AY + (half === 'a' ? 420 : -420), half === 'a' ? 130 : -130]} />
    </Part>
  );
}

/* ── Wave 2 · major groups ─────────────────────────────────────────── */

function PropHub() {
  return (
    <Part id="prop-hub">
      <SpinX which="prop">
        <group position={at(TP.hubX)}>
          <group scale={U}>
            <VariablePitchPropellerHub hubR={0.625} bladeTipR={2.7} show={{ hub: true, dome: true }} />
          </group>
        </group>
      </SpinX>
      <Callout id="prop-hub" p={[TP.hubX + 40, AY + 330, 110]} />
    </Part>
  );
}

function Gearbox() {
  return (
    <Part id="gearbox">
      {/* magnesium casing (hollowed) + front and aft flanges */}
      <Shell k="tp-gearcase" t={16} profile={[[248, TP.gearX0], [272, 380], [272, 800], [258, TP.gearX1]]} />
      <FlangeCollar k="tp-gear-fl0" x={330} r={282} thick={34} bossCount={12} bossR={20} />
      <FlangeCollar k="tp-gear-fl1" x={846} r={268} thick={30} bossCount={12} bossR={18} />
      <BoltCircle x={352} r={302} count={12} d={18} len={44} set="gear-bolts" />
      <Ribs x={430} r0={276} r1={318} count={5} thick={14} />
      <Ribs x={760} r0={262} r1={304} count={5} thick={14} />
      {/* torque-meter barrel */}
      <Cyl c={[TP.torqueX, AY, 0]} r={145} len={112} axis="x" seg={36} />
      <Turn k="tp-torque-ring" axis="x" p={[0, AY, 0]} profile={[[145, 640], [158, 646], [158, 668], [145, 674]]} />
      {/* annular intake screen + front bearing housing */}
      <Turn k="tp-inlet-outer" axis="x" p={[0, AY, 0]} profile={tube(272, 134, 166, 12)} />
      <Turn k="tp-inlet-inner" axis="x" p={[0, AY, 0]} profile={tube(208, 134, 166, 12)} />
      <Ribs x={150} r0={214} r1={268} count={18} thick={10} />
      <Shell k="tp-brg-house" t={14} profile={[[158, -60], [158, 20]]} />
      <FlangeCollar k="tp-brg-fl" x={-20} r={168} thick={24} bossCount={8} bossR={14} />
      {/* front oil scavenge gear */}
      <group position={[352, AY - 172, 0]}>
        <group scale={U}>
          <ToothedGear teeth={14} module={0.0125} thickness={0.055} boreR={0.03} lighteningHoles={3} />
        </group>
      </group>
      <Callout id="gearbox" p={[430, AY + 340, 120]} />
    </Part>
  );
}

function Exhaust() {
  return (
    <Part id="exhaust">
      {[1, -1].map((s) => (
        <group key={s}>
          <Rod a={[TP.exhaustX0, AY + 20, s * 150]} b={[TP.exhaustX0 - 60, AY + 60, s * 258]} r={112} seg={22} />
          <Cyl c={[TP.exhaustX0 - 150, AY + 72, s * 282]} r={112} len={190} axis="x" seg={22} r2={104} />
          <Turn k={`tp-exh-rim-${s}`} axis="x" p={[0, AY + 72, s * 282]} profile={[[104, -1522], [118, -1528], [118, -1542], [104, -1548]]} />
        </group>
      ))}
      <Shell k="tp-tailcone" t={14} profile={[[206, -1500], [150, -1556], [86, -1596], [58, -1620]]} />
      <Hoop k="tp-tail-rim" c={[-1504, AY, 0]} R={210} r={16} axis="x" seg={48} />
      <Callout id="exhaust" p={[-1480, AY + 300, 140]} />
    </Part>
  );
}

function FuelManifoldGroup() {
  // 14 swirl-cup nozzles on the liner aft dome + annular manifold + two igniter plugs.
  return (
    <Part id="fuel-manifold">
      <group position={at(TP.linerX0 + 40)}>
        <group scale={U}>
          <AnnularCombustorLiner
            innerWallR={0.55}
            outerWallR={0.75}
            length={1.15}
            show={{ body: false, grommets: false, nozzles: true }}
          />
        </group>
      </group>
      <Turn k="tp-manif" axis="x" p={[0, AY, 0]} profile={tube(330, TP.linerX0 + 120, TP.linerX0 + 160, 17)} />
      {[1, -1].map((s) => (
        <Rod key={s} a={[TP.linerX0 + 200, AY + s * 120, 190]} b={[TP.linerX0 + 200, AY + s * 260, 190]} r={14} seg={10} />
      ))}
      <Callout id="fuel-manifold" p={[TP.linerX0 + 120, AY - 330, 100]} />
    </Part>
  );
}

function AccessoryDrive() {
  return (
    <Part id="accessory-drive">
      <group position={[220, AY - 300, 0]}>
        <group scale={U}>
          <ToothedGear teeth={27} module={0.02} thickness={0.09} boreR={0.065} lighteningHoles={5} />
        </group>
        <Cyl c={[0, 0, 0]} r={26} len={60} axis="x" seg={16} />
      </group>
      <group position={[220, AY - 366, 0]} rotation={[0, 0, Math.PI / 2]}>
        <group scale={U}>
          <ToothedGear teeth={27} module={0.02} thickness={0.09} boreR={0.065} lighteningHoles={5} />
        </group>
      </group>
      <Box c={[140, AY - 352, 0]} s={[150, 96, 150]} />
      <Cyl c={[140, AY - 430, 0]} r={78} len={110} axis="y" seg={24} />
      <FlangeCollar k="tp-acc-fl" x={140} r={92} thick={22} bossCount={6} bossR={12} />
      <Callout id="accessory-drive" p={[220, AY - 520, 120]} />
    </Part>
  );
}

/* ── Wave 3 · internal telescoping & radial fan-out ────────────────────────── */

function Blades() {
  return (
    <>
      {[0, 1, 2, 3].map((i) => (
        <Part key={i} id={`blade-${i + 1}`}>
          <SpinX which="prop">
            <group position={at(TP.hubX)}>
              <group scale={U}>
                <VariablePitchPropellerHub
                  hubR={0.625}
                  bladeTipR={2.7}
                  collectivePitchDeg={26}
                  show={{ spinner: false, backplate: false, hub: false, dome: false, blades: true }}
                  bladeIndices={[i]}
                />
              </group>
            </group>
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
          <group position={at(TP.gearMidX)}>
            <group scale={U}>
              <ToothedGear teeth={TP.sunTeeth} module={0.0125} thickness={0.105} boreR={0.075} lighteningHoles={0} />
            </group>
            <HollowSteppedShaft
              innerR={48}
              steps={[
                { xStart: 80, xEnd: 260, outerR: 56, labyrinthGrooves: 3 },
              ]}
            />
          </group>
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
          <group position={at(TP.gearMidX - 40)}>
            <HollowSteppedShaft
              innerR={26}
              steps={[
                { xStart: -42, xEnd: -14, outerR: 142 },
                { xStart: 14, xEnd: 42, outerR: 142 },
              ]}
            />
            {Array.from({ length: STAGE1.count }, (_, i) => {
              const a = (i / STAGE1.count) * Math.PI * 2;
              return (
                <Rod
                  key={i}
                  a={[0, Math.cos(a) * 26, Math.sin(a) * 26]}
                  b={[0, Math.cos(a) * 152, Math.sin(a) * 152]}
                  r={21}
                  seg={12}
                />
              );
            })}
          </group>
        </SpinX>
        <Callout id="planet-carrier" p={[TP.gearMidX + 40, AY - 420, 80]} />
      </Part>

      <Part id="ring-gear">
        <group position={at(TP.gearMidX)}>
          <group scale={U}>
            <ToothedGear teeth={TP.ringTeeth} module={0.0125} thickness={0.115} internal outerRingR={0.56} />
          </group>
        </group>
        <Callout id="ring-gear" p={[TP.gearMidX - 240, AY + 250, 70]} />
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
            <group position={at(x)}>
              <group scale={U}>
                <AxialBladeDisk
                  bladeCount={n}
                  boreR={0.18}
                  hubR={(tip - 26) / U}
                  tipR={tip / U}
                  diskWidth={0.105}
                  chord={0.105}
                  bladeThickness={0.033}
                  staggerDeg={32 + k * 6}
                  twistDeg={16 - k * 2}
                />
              </group>
              <HollowSteppedShaft innerR={40} steps={[{ xStart: -30, xEnd: 30, outerR: 78, labyrinthGrooves: 4 }]} />
            </group>
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
          <group position={at(TP.impellerX)}>
            <group scale={U}>
              <CentrifugalImpeller
                boreR={0.14}
                inducerHubR={0.2}
                inducerTipR={0.5}
                exducerR={TP.impellerR / U}
                axialLength={0.36}
                exducerTipWidth={0.1}
                fullVaneCount={12}
                vaneThickness={0.04}
                backsweepDeg={38}
              />
            </group>
          </group>
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
      <group position={at((TP.linerX0 + TP.linerX1) / 2)}>
        <group scale={U}>
          <AnnularCombustorLiner
            innerWallR={TP.linerInR / U}
            outerWallR={TP.linerOutR / U}
            length={(TP.linerX1 - TP.linerX0) / U}
            wallThickness={0.025}
            nozzleCount={0}
          />
        </group>
      </group>
      <Callout id="combustor-liner" p={[TP.linerX1 - 140, AY + 330 + 7 * 150, 80]} />
    </Part>
  );
}

function Turbines() {
  return (
    <>
      <Part id="hp-turbine">
        {/* nozzle guide vane ring (static) */}
        <BladeRow k="tp-ngv" x={TP.ngvX} count={34} rootR={106} tipR={192} chord={36} thick={11} pitch={0.72} />
        <Turn k="tp-ngv-ring" axis="x" p={[0, AY, 0]} profile={tube(192, TP.ngvX - 22, TP.ngvX + 22, 12)} />
        {/* HP turbine disk (1.0ω) */}
        <SpinX which="hp">
          <group position={at(TP.hpX)}>
            <group scale={U}>
              <AxialBladeDisk
                bladeCount={29}
                boreR={0.145}
                hubR={0.22}
                tipR={TP.hpR / U}
                diskWidth={0.115}
                chord={0.11}
                bladeThickness={0.033}
                staggerDeg={38}
                twistDeg={14}
              />
            </group>
          </group>
        </SpinX>
        {/* inter-stage baffle (static) */}
        <Turn k="tp-baffle" axis="x" p={[0, AY, 0]} profile={[[70, TP.baffleX - 16], [152, TP.baffleX - 6], [152, TP.baffleX + 12], [70, TP.baffleX + 20]]} />
        <Callout id="hp-turbine" p={[TP.hpX + 120, AY + 240 + 8 * 150, 70]} />
      </Part>

      <Part id="pt-disk-1">
        <SpinX which="free">
          <group position={at(TP.pt1X)}>
            <group scale={U}>
              <AxialBladeDisk
                bladeCount={31}
                boreR={0.155}
                hubR={0.23}
                tipR={TP.ptR / U}
                diskWidth={0.11}
                chord={0.12}
                bladeThickness={0.033}
                staggerDeg={-30}
                twistDeg={12}
              />
            </group>
            <HollowSteppedShaft innerR={44} steps={[{ xStart: -30, xEnd: 30, outerR: 72, labyrinthGrooves: 5 }]} />
          </group>
        </SpinX>
        <Callout id="pt-disk-1" p={[TP.pt1X + 160, AY + 230 + 9 * 150, 70]} />
      </Part>

      <Part id="pt-disk-2">
        <SpinX which="free">
          <group position={at(TP.pt2X)}>
            <group scale={U}>
              <AxialBladeDisk
                bladeCount={33}
                boreR={0.155}
                hubR={0.23}
                tipR={TP.ptR / U}
                diskWidth={0.11}
                chord={0.12}
                bladeThickness={0.033}
                staggerDeg={-32}
                twistDeg={12}
              />
            </group>
            {/* concentric inner shaft: carries power through the hollow HP spool to the sun gear (labyrinth seals) */}
            <HollowSteppedShaft
              innerR={38}
              steps={[
                { xStart: 0, xEnd: 260, outerR: 78, labyrinthGrooves: 3 },
                { xStart: 260, xEnd: TP.gearMidX - TP.pt2X - 100, outerR: TP.shaftR, labyrinthGrooves: 8 },
              ]}
            />
          </group>
        </SpinX>
        <Callout id="pt-disk-2" p={[TP.pt2X + 200, AY + 230 + 10 * 150, -70]} />
      </Part>
    </>
  );
}

function MountTruss() {
  const feet: Array<[number, number]> = [[820, 230], [820, -230], [340, 230], [340, -230]];
  const tops: Array<[number, number]> = [[760, 150], [760, -150], [400, 150], [400, -150]];
  return (
    <Part id="mount-truss">
      {feet.map(([fx, fz], i) => (
        <Rod key={i} a={[fx, 0, fz]} b={[tops[i][0], AY - 300, tops[i][1]]} r={24} seg={12} />
      ))}
      <Rod a={[820, 60, 230]} b={[340, 60, 230]} r={18} seg={10} />
      <Rod a={[820, 60, -230]} b={[340, 60, -230]} r={18} seg={10} />
      <Rod a={[820, 60, 230]} b={[820, 60, -230]} r={18} seg={10} />
      <Rod a={[340, 60, 230]} b={[340, 60, -230]} r={18} seg={10} />
      <Box c={[580, AY - 318, 0]} s={[560, 42, 340]} />
      <Box c={[580, 14, 0]} s={[620, 28, 560]} />
      <Callout id="mount-truss" p={[460, 120, 280]} />
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
  unit: 10 / 3152,
  bounds: [[TP.tailX - 60, 0, -TP.propR - 80], [TP.spinnerX1 + 60, TP.AY + TP.propR + 80, TP.propR + 80]],
  name: 'Turboprop Engine',
  en: 'Turboprop Engine',
  subtitle: 'Assembly · twin-spool · 15:1 planetary · half-section',
  summary: '31 parts · 6 sub-assemblies · 15:1 planetary drive to a four-blade constant-speed propeller',
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
  annotations: ANNOTATIONS,
});

/** The six sub-assemblies (A–F), spread into ALL in machines/index.ts. */
export const TURBOPROP_LEVELS = [propeller, gearbox, airflow, compressor, combustor, turbine];
