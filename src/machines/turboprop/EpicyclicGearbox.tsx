import React, { useMemo, useRef } from 'react';
import { useFrame } from '@react-three/fiber';
import * as THREE from 'three';
import { M } from '../../scene/Part';
import { motion } from '../../state';
import { HollowSteppedShaft, ToothedGear } from '../turboprop-kit';

/**
 * 子组件 · 两级行星减速轮系（用户提供的 EpicyclicGearboxStage，接入 Inkwork）。
 *
 * 啮合约束 Z_ring = Z_sun + 2·Z_planet；5 行星时 (Z_s + Z_r)/5 ∈ ℤ 保证不顶齿。
 * 默认齿数 20/20/60（1:4 单级）；本机按 15:1 两级（16/24/64 + 16/8/32）传入。
 * explodeOffsets = 各元件的爆炸行程（u 单位）；windows = 0–1 时间窗，给出后
 * 由 useFrame 按 explode.ts 的滑杆逐帧推进（太阳轮/行星轮/销轴/行星架/内齿圈
 * 沿 +x 伸缩 + 行星轮径向散开）。
 */

export interface EpicyclicStageProps {
  /** Base axial position along the engine X centerline */
  xCenter?: number;
  /** Sun gear input angle in radians (driven by power turbine shaft) */
  sunRotationRad?: number;
  /** Per-frame angle sources (override the derived kinematics when given). */
  angles?: {
    sun: () => number;
    carrier?: () => number;
    planet?: () => number;
  };
  /** Per-element axial explosion travel (u units; wired to explode.ts). */
  explodeOffsets?: {
    ringX?: number;
    sunX?: number;
    carrierX?: number;
    planetsX?: number;
    planetsRadial?: number;
    pinsX?: number;
  };
  /** 0–1 explode slider windows per element; enables per-frame explosion. */
  windows?: {
    ringX?: [number, number];
    sunX?: [number, number];
    carrierX?: [number, number];
    planetsX?: [number, number];
    planetsRadial?: [number, number];
    pinsX?: [number, number];
  };
  /** Gear teeth / count (defaults = 20/20/60, 5 planets). */
  teeth?: { sun: number; planet: number; ring: number; count: number };
  gearWidth?: number;
  module?: number;
}

const smooth = (t: number) => {
  const x = Math.min(1, Math.max(0, t));
  return x * x * (3 - 2 * x);
};

export const EpicyclicGearboxStage: React.FC<EpicyclicStageProps> = ({
  xCenter = 0,
  sunRotationRad = 0,
  angles,
  explodeOffsets = {},
  windows,
  teeth,
  gearWidth = 0.36,
  module: m = 0.032,
}) => {
  const zSun = teeth?.sun ?? 20;
  const zPlanet = teeth?.planet ?? 20;
  const zRing = teeth?.ring ?? 60;
  const planetCount = teeth?.count ?? 5;

  // Pitch radii
  const rSun = (zSun * m) / 2;
  const rPlanet = (zPlanet * m) / 2;
  const rRing = (zRing * m) / 2;
  const rOrbit = rSun + rPlanet;

  // True epicyclic kinematic ratios (stationary ring gear):
  const carrierFromSun = sunRotationRad * (zSun / (zSun + zRing));
  const planetFromSun = -(zSun / zPlanet) * (sunRotationRad - carrierFromSun);
  // Half-tooth phase offset so planet teeth slot into sun valleys at theta = 0
  const meshPhaseOffset = Math.PI / zPlanet;

  // Per-element groups (animated when windows are given).
  const ringRef = useRef<THREE.Group>(null);
  const sunRef = useRef<THREE.Group>(null);
  const carrierRef = useRef<THREE.Group>(null);
  const planetsRef = useRef<THREE.Group>(null);
  const planetSpinRefs = useRef<Array<THREE.Group | null>>([]);
  const pinsRef = useRef<THREE.Group>(null);
  const planetOrbitRefs = useRef<Array<THREE.Group | null>>([]);

  const base = {
    ringX: explodeOffsets.ringX ?? 0,
    sunX: explodeOffsets.sunX ?? 0,
    carrierX: explodeOffsets.carrierX ?? 0,
    planetsX: explodeOffsets.planetsX ?? 0,
    planetsRadial: explodeOffsets.planetsRadial ?? 0,
    pinsX: explodeOffsets.pinsX ?? 0,
  };

  useFrame(() => {
    const travel = (key: keyof typeof base) => {
      const w = windows?.[key];
      if (!w) return base[key];
      return base[key] * smooth((motion.explode - w[0]) / (w[1] - w[0]));
    };
    if (ringRef.current) ringRef.current.position.x = travel('ringX');
    if (sunRef.current) sunRef.current.position.x = travel('sunX');
    if (carrierRef.current) carrierRef.current.position.x = travel('carrierX');
    if (planetsRef.current) planetsRef.current.position.x = travel('planetsX');
    if (pinsRef.current) pinsRef.current.position.x = travel('pinsX');
    const radial = travel('planetsRadial');

    const sunA = angles ? angles.sun() : sunRotationRad;
    const carrierA = angles?.carrier ? angles.carrier() : sunA * (zSun / (zSun + zRing));
    const planetA = angles?.planet
      ? angles.planet()
      : -(zSun / zPlanet) * (sunA - carrierA);

    if (carrierRef.current) carrierRef.current.rotation.x = carrierA;
    if (sunRef.current) sunRef.current.rotation.x = sunA;
    planetSpinRefs.current.forEach((g, i) => {
      if (!g) return;
      const orbitTheta = (i * Math.PI * 2) / planetCount;
      g.rotation.x = planetA + meshPhaseOffset + orbitTheta * (zSun / zPlanet);
      // Radial fan-out: each planet slides out along its own orbit radius.
      const orbit = planetOrbitRefs.current[i];
      if (orbit) orbit.position.y = rOrbit + radial;
    });
  });

  return (
    <group position={[xCenter, 0, 0]}>
      {/* 1. Stationary outer ring gear (internal teeth) */}
      <group ref={ringRef}>
        <ToothedGear
          teeth={zRing}
          module={m}
          thickness={gearWidth * 1.15}
          internal
          outerRingR={rRing + 0.18}
        />
      </group>

      {/* 2. Central high-speed sun gear */}
      <group ref={sunRef} rotation={[sunRotationRad, 0, 0]}>
        <ToothedGear teeth={zSun} module={m} thickness={gearWidth} boreR={0.16} />
      </group>

      {/* 3. Planet carrier cage + planets + journal pins */}
      <group ref={carrierRef}>
        {/* Front & aft carrier cage plates */}
        <HollowSteppedShaft
          innerR={0.26}
          steps={[
            { xStart: -gearWidth * 0.78, xEnd: -gearWidth * 0.58, outerR: rOrbit + 0.14 },
            { xStart: gearWidth * 0.58, xEnd: gearWidth * 0.78, outerR: rOrbit + 0.14 },
          ]}
        />
      </group>

      {/* Planet gears & pins distributed around the carrier orbit */}
      <group ref={planetsRef}>
        {Array.from({ length: planetCount }, (_, i) => {
          const orbitTheta = (i * Math.PI * 2) / planetCount;
          return (
            <group
              key={i}
              ref={(el) => {
                planetOrbitRefs.current[i] = el;
              }}
              rotation={[orbitTheta, 0, 0]}
            >
              <group position={[0, rOrbit, 0]}>
                <group
                  ref={(el) => {
                    planetSpinRefs.current[i] = el;
                  }}
                >
                  <ToothedGear
                    teeth={zPlanet}
                    module={m}
                    thickness={gearWidth * 0.96}
                    boreR={0.11}
                    lighteningHoles={4}
                  />
                </group>
              </group>
            </group>
          );
        })}
      </group>
      <group ref={pinsRef}>
        {Array.from({ length: planetCount }, (_, i) => {
          const orbitTheta = (i * Math.PI * 2) / planetCount;
          return (
            <group key={i} rotation={[orbitTheta, 0, 0]}>
              <group position={[0, rOrbit, 0]}>
                <HollowSteppedShaft
                  innerR={0.055}
                  steps={[
                    {
                      xStart: -gearWidth * 0.85,
                      xEnd: gearWidth * 0.85,
                      outerR: 0.108,
                    },
                  ]}
                />
              </group>
            </group>
          );
        })}
      </group>
    </group>
  );
};
