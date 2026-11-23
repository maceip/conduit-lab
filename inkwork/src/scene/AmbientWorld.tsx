import { useEffect, useMemo, useRef } from 'react';
import { useFrame, useThree } from '@react-three/fiber';
import * as THREE from 'three';
import { Box, poly } from '../machines/kit';
import { MG } from '../machines/maglev/data';
import {
  AeroNose,
  DoorLeaf,
  FlushWindshield,
  ProfileShell,
  StatorPack,
  Stripe,
  WindowBand,
  beamShape,
} from '../machines/maglev/kit';
import { OVERLAY_LAYER, ambientSceneDepth } from './InkRenderer';
import { inkUniforms, paletteUniforms } from './ink';
import { AmbientPart } from './Part';

const F = MG.floorY;
const R = MG.roofY;
const M_SCALE = 0.00072;

/** Closed exterior carbody cross-section matching AeroNose u=0 arch. */
function fullShellShape() {
  const halfW = MG.carWidth / 2;
  const ySkirt = F - 1020;
  const hBody = R - ySkirt;
  const yMid = ySkirt + hBody * 0.36;
  const aY = R - yMid;
  const arch: Array<[number, number]> = [];
  const n = 14;
  for (let k = 0; k <= n; k += 1) {
    const theta = (Math.PI * k) / n; // 0 (+z) .. pi (-z)
    const c = Math.cos(theta);
    const s = Math.sin(theta);
    const z = Math.sign(c) * Math.pow(Math.abs(c), 2 / 2.35) * halfW;
    const y = yMid + Math.pow(Math.max(0, s), 1 / (2 / 1.11)) * aY;
    arch.push([y, z]);
  }
  const outer: Array<[number, number]> = [
    [F + 100, 1480],
    [ySkirt, halfW * 0.96],
    [ySkirt + hBody * 0.14, halfW],
    ...arch,
    [ySkirt + hBody * 0.14, -halfW],
    [ySkirt, -halfW * 0.96],
    [F + 100, -1480],
  ];
  return poly(outer);
}

/**
 * Depth-occluded perspective floor datum lines at y = 0.
 * Samples the normal-pass depth buffer so lines pass cleanly behind the
 * foreground turboprop stand and every distant concrete viaduct pier, while
 * fading smoothly to zero toward the horizon.
 */
function InfiniteFloorGrid() {
  const { scene } = useThree();

  const floorObj = useMemo(() => {
    const positions: number[] = [];
    const span = 155;
    const step = 6.2;

    for (let x = -span; x <= span; x += step) {
      const segs = 28;
      for (let i = 0; i < segs; i += 1) {
        const z0 = -span + ((span * 2) * i) / segs;
        const z1 = -span + ((span * 2) * (i + 1)) / segs;
        positions.push(x, 0.008, z0, x, 0.008, z1);
      }
    }
    for (let z = -span; z <= span; z += step) {
      const segs = 28;
      for (let i = 0; i < segs; i += 1) {
        const x0 = -span + ((span * 2) * i) / segs;
        const x1 = -span + ((span * 2) * (i + 1)) / segs;
        positions.push(x0, 0.008, z, x1, 0.008, z);
      }
    }

    const geo = new THREE.BufferGeometry();
    geo.setAttribute('position', new THREE.Float32BufferAttribute(positions, 3));

    const mat = new THREE.ShaderMaterial({
      transparent: true,
      depthTest: false,
      depthWrite: false,
      uniforms: {
        uInk: paletteUniforms.uInk,
        uRes: inkUniforms.uRes,
        tSceneDepth: { value: null as THREE.Texture | null },
      },
      vertexShader: /* glsl */ `
        varying vec3 vWorld;
        varying float vViewZ;
        void main() {
          vec4 wp = modelMatrix * vec4(position, 1.0);
          vWorld = wp.xyz;
          vec4 mv = viewMatrix * wp;
          vViewZ = -mv.z;
          gl_Position = projectionMatrix * mv;
        }
      `,
      fragmentShader: /* glsl */ `
        uniform vec3 uInk;
        uniform vec2 uRes;
        uniform sampler2D tSceneDepth;
        varying vec3 vWorld;
        varying float vViewZ;
        void main() {
          vec2 uv = gl_FragCoord.xy / uRes;
          float sceneZ = texture2D(tSceneDepth, uv).x;
          if (sceneZ < 0.99999) discard;
          float r = length(vWorld.xz - vec2(-4.0, -6.0));
          float radial = exp(-r * 0.021);
          float farFade = 1.0 - smoothstep(85.0, 175.0, vViewZ);
          float nearSoft = smoothstep(7.0, 13.0, vViewZ);
          float a = 0.19 * radial * farFade * nearSoft;
          if (a < 0.004) discard;
          gl_FragColor = vec4(uInk, a);
        }
      `,
    });

    const lines = new THREE.LineSegments(geo, mat);
    lines.layers.set(OVERLAY_LAYER);
    lines.frustumCulled = false;
    lines.raycast = () => {};
    return { lines, geo, mat };
  }, []);

  useEffect(() => {
    scene.add(floorObj.lines);
    return () => {
      scene.remove(floorObj.lines);
      floorObj.geo.dispose();
      floorObj.mat.dispose();
    };
  }, [scene, floorObj]);

  useFrame(() => {
    if (ambientSceneDepth.value) {
      floorObj.mat.uniforms.tSceneDepth.value = ambientSceneDepth.value;
    }
  });

  return null;
}

/** Coupled trailing passenger coach matching the TR08 cross-section & window beltline. */
function TrailingCoach({ x0, x1, keyTag }: { x0: number; x1: number; keyTag: string }) {
  const len = x1 - x0;
  const midX = (x0 + x1) / 2;
  return (
    <group>
      <AmbientPart partId={0.145} tone={0.82}>
        <ProfileShell k={`amb-coach-${keyTag}`} shape={fullShellShape()} x0={x0} x1={x1} />
        {/* Inter-car aerodynamic diaphragm */}
        <Box c={[x0 - 260, F + 1950, 0]} s={[460, 3550, 3360]} />
      </AmbientPart>
      <AmbientPart partId={0.175} tone={0.65}>
        <WindowBand x0={x0 + 2400} x1={x1 - 2400} y0={F + 1520} y1={F + 2420} z={-1850} side={-1} panes={9} />
        <WindowBand x0={x0 + 2400} x1={x1 - 2400} y0={F + 1520} y1={F + 2420} z={1850} side={1} panes={9} />
        <DoorLeaf x={x0 + 1350} y0={F + 140} y1={F + 2320} z={-1850} side={-1} />
        <DoorLeaf x={x1 - 1350} y0={F + 140} y1={F + 2320} z={-1850} side={-1} />
      </AmbientPart>
      <AmbientPart partId={0.235} tone={0.75}>
        <Stripe x0={x0} x1={x1} y={F + 1320} z={-1868} h={96} />
        <Stripe x0={x0} x1={x1} y={F + 1140} z={-1868} h={58} />
        <Box c={[midX, R + 110, 0]} s={[len * 0.28, 210, 2050]} />
      </AmbientPart>
    </group>
  );
}

/**
 * Diagonal elevated Shanghai SMT Maglev viaduct + 3-car Transrapid TR08 trainset
 * sweeping behind the translucent hero sheet and past the foreground turboprop
 * toward the distant horizon.
 */
export function AmbientWorld() {
  const trainRef = useRef<THREE.Group>(null);

  useFrame(({ clock }) => {
    if (!trainRef.current) return;
    // Subtle 10 mm EMS non-contact levitation hover
    trainRef.current.position.y = 14 + Math.sin(clock.getElapsedTime() * 1.6) * 18;
  });

  const beamX0 = -350000;
  const beamX1 = 70000;
  const beamLen = beamX1 - beamX0;
  const beamMid = (beamX0 + beamX1) / 2;

  const pierStations = useMemo(() => {
    const xs: number[] = [];
    for (let px = 62000; px >= -334000; px -= 22000) {
      xs.push(px);
    }
    return xs;
  }, []);

  return (
    <group name="ambient-world">
      <InfiniteFloorGrid />

      <group position={[-24.9, 0, -7.7]} rotation={[0, -1.773, 0]} scale={M_SCALE}>
        {/* Continuous prestressed concrete box-girder guideway */}
        <AmbientPart partId={0.055} tone={0.85}>
          <ProfileShell
            k="amb-beam"
            shape={() => beamShape(MG.beamW, MG.beamH)}
            x0={beamX0}
            x1={beamX1}
            y={MG.beamBotY + MG.beamH / 2}
          />
          <Box c={[beamMid, MG.beamTopY + 40, MG.beamW / 2 - 140]} s={[beamLen, 80, 260]} />
          <Box c={[beamMid, MG.beamTopY + 40, -(MG.beamW / 2 - 140)]} s={[beamLen, 80, 260]} />
        </AmbientPart>

        {/* Long-stator linear motor packs & lateral guidance rails */}
        <AmbientPart partId={0.115} tone={0.78}>
          <Box c={[beamMid, 3080, -1520]} s={[beamLen, 140, 160]} />
          <Box c={[beamMid, 3080, 1520]} s={[beamLen, 140, 160]} />
          <Box c={[beamMid, 2400, -1380]} s={[beamLen, 210, 180]} />
          <group position={[-74000, 2400, -1250]}>
            <StatorPack x0={-26000} x1={28000} side={-1} />
          </group>
        </AmbientPart>

        {/* Repeating tapered concrete hammerhead viaduct piers stepping to infinity */}
        <AmbientPart partId={0.085} tone={0.88}>
          {pierStations.map((px) => (
            <group key={px}>
              <Box c={[px, 90, 0]} s={[2600, 180, 3200]} />
              <Box c={[px, 560, 0]} s={[1500, 760, 1700]} />
              <Box c={[px, 1040, 0]} s={[2400, 240, 3100]} />
              <Box c={[px, 1210, 760]} s={[900, 110, 720]} />
              <Box c={[px, 1210, -760]} s={[900, 110, 720]} />
            </group>
          ))}
        </AmbientPart>

        {/* Coupled 3-car Shanghai SMT Maglev (Transrapid TR08) trainset */}
        <group ref={trainRef}>
          <group position={[-85000, 0, 0]}>
            <AmbientPart partId={0.145} tone={0.82}>
              <AeroNose x0={19800} x1={27000} floorY={F} roofY={R} halfW={MG.carWidth / 2} />
              <ProfileShell k="amb-lead-shell" shape={fullShellShape()} x0={1200} x1={19800} />
              <Box c={[1050, F + 1950, 0]} s={[480, 3600, 3400]} />
            </AmbientPart>
            <AmbientPart partId={0.175} tone={0.65}>
              <FlushWindshield x0={19800} x1={27000} floorY={F} roofY={R} halfW={MG.carWidth / 2} />
              <WindowBand x0={4400} x1={17100} y0={F + 1520} y1={F + 2420} z={-1850} side={-1} panes={8} />
              <WindowBand x0={4400} x1={17100} y0={F + 1520} y1={F + 2420} z={1850} side={1} panes={8} />
              <DoorLeaf x={18200} y0={F + 140} y1={F + 2320} z={-1850} side={-1} />
              <DoorLeaf x={3400} y0={F + 140} y1={F + 2320} z={-1850} side={-1} />
            </AmbientPart>
            <AmbientPart partId={0.235} tone={0.75}>
              <Stripe x0={1200} x1={19800} y={F + 1320} z={-1868} h={96} />
              <Stripe x0={1200} x1={19800} y={F + 1140} z={-1868} h={58} />
              <Box c={[11200, R + 110, 0]} s={[5600, 220, 2100]} />
            </AmbientPart>
          </group>

          <TrailingCoach keyTag="c2" x0={-109700} x1={-84500} />
          <TrailingCoach keyTag="c3" x0={-134900} x1={-110200} />
        </group>
      </group>
    </group>
  );
}
