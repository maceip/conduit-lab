import React, { useMemo } from 'react';
import * as THREE from 'three';
import { toCreasedNormals } from 'three/examples/jsm/utils/BufferGeometryUtils.js';
import { M } from '../scene/Part';
import { cyl } from '../scene/geometry';

/**
 * Turboprop R3F procedural geometry kit (author-provided, wired into Inkwork).
 *
 * InkRenderer draws lines from depth breaks, normal creases and the stencil
 * section plane, so this kit keeps explicit hard-edge topology (closed lathed
 * manifolds, extruded tooth profiles, 3D airfoil skins). One adaptation: the
 * repo's ink materials run toCreasedNormals(π/5), which keeps smooth surfaces
 * smooth while creasing steps, tooth tips and roots — richer than a bare
 * computeVertexNormals() — so every mesh goes through crease() before return.
 * All meshes render via <M clip> for the ink material and the z = 0 cut. Axis +X.
 */

const X_TO_Z = new THREE.Matrix4().makeRotationY(Math.PI / 2);
const Y_TO_X = new THREE.Matrix4().makeRotationZ(-Math.PI / 2);

/** Hard-edge creasing, matching src/scene/geometry.ts. */
const crease = (g: THREE.BufferGeometry) => toCreasedNormals(g, Math.PI / 5);

export interface ShaftStep {
  xStart: number;
  xEnd: number;
  outerR: number;
  /** Optional flange or labyrinth seal collar along this segment */
  labyrinthGrooves?: number;
}

export interface HollowSteppedShaftProps {
  innerR: number;
  steps: ShaftStep[];
  radialSegments?: number;
}

/**
 * 1. HOLLOW CONCENTRIC STEPPED SHAFT
 * Builds a closed manifold LatheGeometry revolved around the X-axis.
 * Closed topology is required so the GLSL section-cut pass renders double-walled
 * cross-hatch shading between innerR and outerR instead of hollow paper shells.
 */
export const HollowSteppedShaft: React.FC<HollowSteppedShaftProps> = ({
  innerR,
  steps,
  radialSegments = 48,
}) => {
  const geometry = useMemo(() => {
    if (steps.length === 0) return new THREE.BufferGeometry();

    // LatheGeometry revolves a 2D (radius=x, height=y) profile around the Y-axis.
    // We build the closed loop in (r, x) and rotate Y -> X afterward.
    const pts: THREE.Vector2[] = [];
    const sorted = [...steps].sort((a, b) => a.xStart - b.xStart);
    const xMin = sorted[0].xStart;
    const xMax = sorted[sorted.length - 1].xEnd;

    // Start at inner bore, front face (xMin)
    pts.push(new THREE.Vector2(innerR, xMin));

    // Step along outer profile from xMin to xMax
    for (const s of sorted) {
      pts.push(new THREE.Vector2(s.outerR, s.xStart));

      if (s.labyrinthGrooves && s.labyrinthGrooves > 0) {
        const span = s.xEnd - s.xStart;
        const pitch = span / (s.labyrinthGrooves * 2 + 1);
        // Scale-free groove depth (the original 0.035 cap is scene-unit sized;
        // keep it proportional to the wall so mm-scale shafts still get grooves).
        const grooveDepth = Math.min(s.outerR * 0.08, (s.outerR - innerR) * 0.35);
        for (let i = 0; i < s.labyrinthGrooves; i++) {
          const gx0 = s.xStart + pitch * (2 * i + 1);
          const gx1 = gx0 + pitch;
          pts.push(new THREE.Vector2(s.outerR, gx0));
          pts.push(new THREE.Vector2(s.outerR - grooveDepth, gx0));
          pts.push(new THREE.Vector2(s.outerR - grooveDepth, gx1));
          pts.push(new THREE.Vector2(s.outerR, gx1));
        }
      }

      pts.push(new THREE.Vector2(s.outerR, s.xEnd));
    }

    // Close loop back along the inner bore from xMax to xMin
    pts.push(new THREE.Vector2(innerR, xMax));
    pts.push(new THREE.Vector2(innerR, xMin));

    const lathe = new THREE.LatheGeometry(pts, radialSegments);
    lathe.applyMatrix4(Y_TO_X);
    return crease(lathe);
  }, [innerR, steps, radialSegments]);

  return <M clip geo={geometry} />;
};

export interface SpurGearProps {
  teeth: number;
  module: number;
  thickness: number;
  boreR?: number;
  /** Internal ring gear when true; external sun/planet gear when false */
  internal?: boolean;
  /** Outer housing wall radius (required when internal = true) */
  outerRingR?: number;
  /** Adds Haynes-style circular lightening holes in the gear web */
  lighteningHoles?: number;
  pressureAngleDeg?: number;
}

/**
 * 2. INVOLUTE-APPROXIMATED SPUR / PLANETARY / INTERNAL RING GEAR
 * Extruded along +X (centered at x = 0) with sharp tooth flanks and web lightening holes
 * so InkRenderer picks up every tooth crest, root, and bore hole.
 */
export const ToothedGear: React.FC<SpurGearProps> = ({
  teeth,
  module: m,
  thickness,
  boreR = 0.1,
  internal = false,
  outerRingR,
  lighteningHoles = 0,
  pressureAngleDeg = 20,
}) => {
  const geometry = useMemo(() => {
    const pitchR = (teeth * m) / 2;
    const addendum = internal ? 0.85 * m : 1.0 * m;
    const dedendum = internal ? 1.25 * m : 1.2 * m;

    const rRoot = internal ? pitchR + dedendum : Math.max(boreR + 0.02, pitchR - dedendum);
    const rTip = internal ? pitchR - addendum : pitchR + addendum;

    const shape = new THREE.Shape();
    const stepAngle = (Math.PI * 2) / teeth;
    const alpha = (pressureAngleDeg * Math.PI) / 180;
    const halfPitchAngle = stepAngle / 4;
    const flankSlope = Math.tan(alpha) * (m / pitchR) * 0.65;

    const buildToothedLoop = (path: THREE.Shape | THREE.Path, reverse = false) => {
      for (let i = 0; i < teeth; i++) {
        const idx = reverse ? teeth - 1 - i : i;
        const baseTheta = idx * stepAngle;
        const dir = reverse ? -1 : 1;

        const a0 = baseTheta - dir * (halfPitchAngle + flankSlope);
        const a1 = baseTheta - dir * (halfPitchAngle - flankSlope);
        const a2 = baseTheta + dir * (halfPitchAngle - flankSlope);
        const a3 = baseTheta + dir * (halfPitchAngle + flankSlope);

        const p0 = new THREE.Vector2(Math.cos(a0) * rRoot, Math.sin(a0) * rRoot);
        const p1 = new THREE.Vector2(Math.cos(a1) * rTip, Math.sin(a1) * rTip);
        const p2 = new THREE.Vector2(Math.cos(a2) * rTip, Math.sin(a2) * rTip);
        const p3 = new THREE.Vector2(Math.cos(a3) * rRoot, Math.sin(a3) * rRoot);

        if (i === 0) {
          path.moveTo(p0.x, p0.y);
        } else {
          path.lineTo(p0.x, p0.y);
        }
        path.lineTo(p1.x, p1.y);
        path.lineTo(p2.x, p2.y);
        path.lineTo(p3.x, p3.y);
      }
      path.closePath();
    };

    if (!internal) {
      // External gear: outer boundary is teeth, inner hole is bore + lightening holes
      buildToothedLoop(shape, false);

      if (boreR > 0) {
        const boreHole = new THREE.Path();
        boreHole.absarc(0, 0, boreR, 0, Math.PI * 2, true);
        shape.holes.push(boreHole);
      }

      if (lighteningHoles > 0 && rRoot - boreR > 0.22) {
        const holeOrbitR = (rRoot + boreR) * 0.5;
        const holeR = Math.min(
          (rRoot - boreR) * 0.24,
          (Math.PI * holeOrbitR) / (lighteningHoles * 1.8)
        );
        for (let h = 0; h < lighteningHoles; h++) {
          const ha = (h * Math.PI * 2) / lighteningHoles;
          const lh = new THREE.Path();
          lh.absarc(
            Math.cos(ha) * holeOrbitR,
            Math.sin(ha) * holeOrbitR,
            holeR,
            0,
            Math.PI * 2,
            true
          );
          shape.holes.push(lh);
        }
      }
    } else {
      // Internal ring gear: outer boundary is smooth casing cylinder, inner hole is toothed profile
      const rOuter = outerRingR ?? rRoot + 2.5 * m;
      shape.absarc(0, 0, rOuter, 0, Math.PI * 2, false);
      const innerTeethHole = new THREE.Path();
      buildToothedLoop(innerTeethHole, true);
      shape.holes.push(innerTeethHole);
    }

    const extrude = new THREE.ExtrudeGeometry(shape, {
      depth: thickness,
      bevelEnabled: false,
      curveSegments: 24,
    });
    // Center extrusion along Z, then rotate Z -> X so gear axis is X
    extrude.translate(0, 0, -thickness / 2);
    extrude.applyMatrix4(X_TO_Z);
    return crease(extrude);
  }, [teeth, m, thickness, boreR, internal, outerRingR, lighteningHoles, pressureAngleDeg]);

  return <M clip geo={geometry} />;
};

export interface AxialCompressorStageProps {
  bladeCount: number;
  hubR: number;
  tipR: number;
  boreR: number;
  diskWidth: number;
  chord: number;
  bladeThickness?: number;
  /** Stagger angle at hub in degrees (measured from axial +X centerline) */
  staggerDeg: number;
  /** Spanwise twist from hub to tip in degrees */
  twistDeg?: number;
  /** Camber curvature ratio (0 = flat plate, 0.12 = realistic cambered airfoil) */
  camber?: number;
}

/**
 * 3. ANGLED & TWISTED AXIAL COMPRESSOR / TURBINE BLADE DISK
 * Builds a profiled rotor disk hub with a dovetail rim groove and an array of
 * spanwise-twisted, cambered 3D airfoil blades so silhouette & crease shaders
 * draw crisp cascade geometry at any camera angle.
 */
export const AxialBladeDisk: React.FC<AxialCompressorStageProps> = ({
  bladeCount,
  hubR,
  tipR,
  boreR,
  diskWidth,
  chord,
  bladeThickness = 0.022,
  staggerDeg,
  twistDeg = 16,
  camber = 0.1,
}) => {
  // 3A. Profiled rotor web + rim + bore hub (Lathe around X)
  const hubGeometry = useMemo(() => {
    const hw = diskWidth / 2;
    const webW = hw * 0.42;
    const boreSeatR = boreR + (hubR - boreR) * 0.28;
    const rimUndersideR = hubR - (hubR - boreR) * 0.18;

    const pts: THREE.Vector2[] = [
      // Inner bore
      new THREE.Vector2(boreR, -hw),
      // Front bore hub face -> web -> outer rim
      new THREE.Vector2(boreSeatR, -hw),
      new THREE.Vector2(boreSeatR, -webW),
      new THREE.Vector2(rimUndersideR, -webW),
      new THREE.Vector2(rimUndersideR, -hw),
      new THREE.Vector2(hubR, -hw),
      // Outer blade platform
      new THREE.Vector2(hubR, hw),
      // Aft rim -> web -> bore hub face
      new THREE.Vector2(rimUndersideR, hw),
      new THREE.Vector2(rimUndersideR, webW),
      new THREE.Vector2(boreSeatR, webW),
      new THREE.Vector2(boreSeatR, hw),
      new THREE.Vector2(boreR, hw),
      new THREE.Vector2(boreR, -hw),
    ];

    const lathe = new THREE.LatheGeometry(pts, 48);
    lathe.applyMatrix4(Y_TO_X);
    return crease(lathe);
  }, [hubR, boreR, diskWidth]);

  // 3B. Single twisted cambered airfoil mesh (instanced or cloned radially)
  const singleBladeGeometry = useMemo(() => {
    const spanSteps = 6;
    const chordSteps = 6;
    const positions: number[] = [];
    const indices: number[] = [];

    // Generate top and bottom airfoil skin vertices across span and chord
    // Local blade coords prior to radial placement:
    //   x = axial, y = radial (hubR..tipR), z = tangential
    for (let s = 0; s <= spanSteps; s++) {
      const vSpan = s / spanSteps;
      const r = THREE.MathUtils.lerp(hubR - 0.015, tipR, vSpan);
      const localChord = chord * THREE.MathUtils.lerp(1.0, 0.82, vSpan); // slight taper at tip
      const angleRad = THREE.MathUtils.degToRad(staggerDeg + twistDeg * vSpan);
      const cosA = Math.cos(angleRad);
      const sinA = Math.sin(angleRad);

      for (let c = 0; c <= chordSteps; c++) {
        const u = c / chordSteps; // 0 = leading edge, 1 = trailing edge
        const xc = (u - 0.5) * localChord;

        // Parabolic mean camber line + NACA-style thickness distribution
        const ycCamber = 4 * camber * localChord * u * (1 - u);
        const halfThick =
          bladeThickness *
          (1 - 0.35 * vSpan) *
          (2.969 * Math.sqrt(u) - 1.26 * u - 3.516 * u * u + 2.843 * u * u * u - 1.015 * Math.pow(u, 4));

        // Suction (upper) and Pressure (lower) surface points in 2D airfoil frame
        for (const side of [1, -1]) {
          const localT = ycCamber + side * halfThick;
          // Rotate by local stagger + twist angle into (axial=X, tangential=Z)
          const ax = xc * cosA - localT * sinA;
          const tz = xc * sinA + localT * cosA;
          // Project onto cylindrical radius r so tip and root conform to cylinder
          const theta = tz / r;
          const py = r * Math.cos(theta);
          const pz = r * Math.sin(theta);

          positions.push(ax, py, pz);
        }
      }
    }

    const stride = (chordSteps + 1) * 2;
    for (let s = 0; s < spanSteps; s++) {
      for (let c = 0; c < chordSteps; c++) {
        const i0 = s * stride + c * 2;
        const i1 = i0 + 2;
        const i2 = (s + 1) * stride + c * 2;
        const i3 = i2 + 2;

        // Suction surface (even offsets)
        indices.push(i0, i2, i1, i1, i2, i3);
        // Pressure surface (odd offsets)
        indices.push(i0 + 1, i1 + 1, i2 + 1, i1 + 1, i3 + 1, i2 + 1);
      }
    }

    // Tip cap (s = spanSteps) and root cap (s = 0)
    const topStart = spanSteps * stride;
    for (let c = 0; c < chordSteps; c++) {
      const t0 = topStart + c * 2;
      indices.push(t0, t0 + 1, t0 + 2, t0 + 1, t0 + 3, t0 + 2);
    }

    const geo = new THREE.BufferGeometry();
    geo.setAttribute('position', new THREE.Float32BufferAttribute(positions, 3));
    geo.setIndex(indices);
    return crease(geo);
  }, [hubR, tipR, chord, bladeThickness, staggerDeg, twistDeg, camber]);

  const bladeAngles = useMemo(
    () => Array.from({ length: bladeCount }, (_, i) => (i * Math.PI * 2) / bladeCount),
    [bladeCount]
  );

  return (
    <group>
      <M clip geo={hubGeometry} />
      {bladeAngles.map((angle, i) => (
        <M key={i} clip geo={singleBladeGeometry} r={[angle, 0, 0]} />
      ))}
    </group>
  );
};

/* ═══════════════════════════════════════════════════════════════════
 * 4–6. Centrifugal impeller / reverse-flow liner / 4-blade propeller
 * (author-provided). Same rules: hard-edge topology, <M clip>, crease().
 * These three live in the u design space (the map's units), so callers wrap
 * them in <group scale={TP.u}> inside the millimetre frame. Two render filters
 * (show / bladeIndices) let Inkwork <Part>s own single elements for explosion
 * and ballooning.
 * ═══════════════════════════════════════════════════════════════════ */

const _Y_TO_X = new THREE.Matrix4().makeRotationZ(-Math.PI / 2);

export interface CentrifugalImpellerProps {
  boreR?: number;
  inducerHubR?: number;
  inducerTipR?: number;
  exducerR?: number;
  axialLength?: number;
  exducerTipWidth?: number;
  /** Number of main full-length vanes (an equal number of splitter vanes are interleaved) */
  fullVaneCount?: number;
  vaneThickness?: number;
  /** Total azimuthal wrap angle of the vane from inducer to exducer (in degrees) */
  backsweepDeg?: number;
}

/**
 * 5. SINGLE-STAGE CENTRIFUGAL COMPRESSOR IMPELLER
 * Generates a curved meridional Lathe hub with interleaved full and splitter
 * 3D swept vanes that turn axial airflow (+X -> radial) into discharge.
 */
export const CentrifugalImpeller: React.FC<CentrifugalImpellerProps> = ({
  boreR = 0.34,
  inducerHubR = 0.56,
  inducerTipR = 0.92,
  exducerR = 1.48,
  axialLength = 0.62,
  exducerTipWidth = 0.14,
  fullVaneCount = 12,
  vaneThickness = 0.022,
  backsweepDeg = 38,
}) => {
  // 5A. Closed manifold impeller hub disk (Lathe around X)
  const hubGeometry = useMemo(() => {
    const xFront = axialLength / 2; // Inducer eye (+X side)
    const xBack = -axialLength / 2; // Exducer backplate (-X side)
    const curveSteps = 20;

    const pts: THREE.Vector2[] = [];
    // Start at front inner bore
    pts.push(new THREE.Vector2(boreR, xFront));
    pts.push(new THREE.Vector2(inducerHubR, xFront));

    // Quadratic meridional hub contour from axial inducer to radial exducer rim
    for (let i = 1; i <= curveSteps; i++) {
      const t = i / curveSteps;
      // r(t) accelerates outward toward exducerR
      const r = inducerHubR + (exducerR - inducerHubR) * Math.pow(t, 1.65);
      // x(t) sweeps from xFront down to xBack + exducerTipWidth
      const x =
        xFront - (axialLength - exducerTipWidth) * (1 - Math.pow(1 - t, 1.8));
      pts.push(new THREE.Vector2(r, x));
    }

    // Exducer perimeter rim and scalloped backplate web
    pts.push(new THREE.Vector2(exducerR, xBack));
    pts.push(new THREE.Vector2(inducerHubR * 1.15, xBack));
    pts.push(new THREE.Vector2(inducerHubR * 1.15, xBack + 0.06));
    pts.push(new THREE.Vector2(boreR + 0.12, xBack + 0.06));
    pts.push(new THREE.Vector2(boreR + 0.12, xBack));
    pts.push(new THREE.Vector2(boreR, xBack));
    pts.push(new THREE.Vector2(boreR, xFront));

    const lathe = new THREE.LatheGeometry(pts, 56);
    lathe.applyMatrix4(_Y_TO_X);
    return crease(lathe);
  }, [boreR, inducerHubR, exducerR, axialLength, exducerTipWidth]);

  // 5B. Helper to build a 3D swept vane mesh from meridional parameter tStart..1.0
  const buildVaneMesh = (tStart: number) => {
    const xFront = axialLength / 2;
    const uSteps = 16; // Meridional streamwise steps
    const vSteps = 4;  // Hub-to-shroud span steps
    const sweepRad = THREE.MathUtils.degToRad(backsweepDeg);

    const positions: number[] = [];
    const indices: number[] = [];

    for (let iu = 0; iu <= uSteps; iu++) {
      const t = THREE.MathUtils.lerp(tStart, 1.0, iu / uSteps);

      // Hub meridional point (rHub, xHub)
      const rHub = inducerHubR + (exducerR - inducerHubR) * Math.pow(t, 1.65);
      const xHub =
        xFront - (axialLength - exducerTipWidth) * (1 - Math.pow(1 - t, 1.8));

      // Shroud (tip) meridional point (rShroud, xShroud)
      const rShroud =
        inducerTipR + (exducerR - inducerTipR) * Math.pow(t, 1.95);
      const xShroud =
        xFront -
        (axialLength - exducerTipWidth * 1.05) * (1 - Math.pow(1 - t, 1.35));

      // Azimuthal wrap angle theta(t): inducer twist + backsweep toward exducer
      const thetaCenter = sweepRad * Math.pow(t, 1.4);

      for (let iv = 0; iv <= vSteps; iv++) {
        const s = iv / vSteps; // 0 = hub root, 1 = shroud tip
        const r = THREE.MathUtils.lerp(rHub - 0.015, rShroud, s);
        const x = THREE.MathUtils.lerp(xHub - 0.015, xShroud, s);
        // Slight lean across span from root to shroud
        const spanTheta = thetaCenter + (1 - t) * s * 0.18;

        for (const side of [1, -1]) {
          const dTheta = (side * vaneThickness * 0.5) / Math.max(0.2, r);
          const phi = spanTheta + dTheta;
          const py = r * Math.cos(phi);
          const pz = r * Math.sin(phi);
          positions.push(x, py, pz);
        }
      }
    }

    const stride = (vSteps + 1) * 2;
    for (let iu = 0; iu < uSteps; iu++) {
      for (let iv = 0; iv < vSteps; iv++) {
        const i0 = iu * stride + iv * 2;
        const i1 = i0 + 2;
        const i2 = (iu + 1) * stride + iv * 2;
        const i3 = i2 + 2;

        // Pressure & suction faces
        indices.push(i0, i2, i1, i1, i2, i3);
        indices.push(i0 + 1, i1 + 1, i2 + 1, i1 + 1, i3 + 1, i2 + 1);
      }
    }

    // Shroud tip cap (iv = vSteps)
    for (let iu = 0; iu < uSteps; iu++) {
      const c0 = iu * stride + vSteps * 2;
      const c1 = (iu + 1) * stride + vSteps * 2;
      indices.push(c0, c0 + 1, c1, c0 + 1, c1 + 1, c1);
    }

    // Leading edge cap (iu = 0) & Exducer trailing edge cap (iu = uSteps)
    for (let iv = 0; iv < vSteps; iv++) {
      const l0 = iv * 2;
      indices.push(l0, l0 + 2, l0 + 1, l0 + 1, l0 + 2, l0 + 3);
      const t0 = uSteps * stride + iv * 2;
      indices.push(t0, t0 + 1, t0 + 2, t0 + 1, t0 + 3, t0 + 2);
    }

    const geo = new THREE.BufferGeometry();
    geo.setAttribute('position', new THREE.Float32BufferAttribute(positions, 3));
    geo.setIndex(indices);
    return crease(geo);
  };

  const fullVaneGeo = useMemo(
    () => buildVaneMesh(0.0),
    // eslint-disable-next-line react-hooks/exhaustive-deps
    [inducerHubR, inducerTipR, exducerR, axialLength, exducerTipWidth, vaneThickness, backsweepDeg]
  );
  const splitterVaneGeo = useMemo(
    () => buildVaneMesh(0.38),
    // eslint-disable-next-line react-hooks/exhaustive-deps
    [inducerHubR, inducerTipR, exducerR, axialLength, exducerTipWidth, vaneThickness, backsweepDeg]
  );

  const sectorAngle = (Math.PI * 2) / fullVaneCount;

  return (
    <group>
      <M clip geo={hubGeometry} />
      {Array.from({ length: fullVaneCount }, (_, i) => {
        const baseAngle = i * sectorAngle;
        return (
          <React.Fragment key={i}>
            <M clip geo={fullVaneGeo} r={[baseAngle, 0, 0]} />
            <M clip geo={splitterVaneGeo} r={[baseAngle + sectorAngle * 0.5, 0, 0]} />
          </React.Fragment>
        );
      })}
    </group>
  );
};

export interface AnnularCombustorLinerProps {
  innerWallR?: number;
  outerWallR?: number;
  length?: number;
  wallThickness?: number;
  nozzleCount?: number;
  dilutionRows?: Array<{
    xOffset: number;
    count: number;
    holeR: number;
    onInnerWall?: boolean;
  }>;
  /** Render filter: split body / grommet rings / nozzle swirl cups across <Part>s. */
  show?: { body?: boolean; grommets?: boolean; nozzles?: boolean };
}

/**
 * 6. PERFORATED REVERSE-FLOW ANNULAR COMBUSTION LINER
 * Closed double-walled toroidal flame liner with louver steps, peripheral
 * fuel-nozzle swirl cups, and flanged primary/dilution air grommets.
 */
export const AnnularCombustorLiner: React.FC<AnnularCombustorLinerProps> = ({
  innerWallR = 0.88,
  outerWallR = 1.54,
  length = 1.15,
  wallThickness = 0.032,
  nozzleCount = 14,
  dilutionRows = [
    { xOffset: -0.28, count: 14, holeR: 0.065, onInnerWall: false },
    { xOffset: 0.02, count: 28, holeR: 0.045, onInnerWall: false },
    { xOffset: 0.28, count: 18, holeR: 0.075, onInnerWall: false },
    { xOffset: -0.12, count: 14, holeR: 0.055, onInnerWall: true },
    { xOffset: 0.22, count: 18, holeR: 0.06, onInnerWall: true },
  ],
  show = { body: true, grommets: true, nozzles: true },
}) => {
  // 6A. Closed U-shaped double-walled flame tube cross-section (Lathe around X)
  const linerBodyGeometry = useMemo(() => {
    const xFront = length / 2;
    const domeR = (outerWallR - innerWallR) / 2;
    const domeCenterR = (outerWallR + innerWallR) / 2;
    const xAft = -length / 2;
    const domeCenterX = xAft + domeR;
    const t = wallThickness;

    const pts: THREE.Vector2[] = [];

    // 1. Start at forward inner discharge lip (+X, innerWallR)
    pts.push(new THREE.Vector2(innerWallR, xFront));

    // Inner liner wall moving aft with 2 cooling louver steps
    pts.push(new THREE.Vector2(innerWallR, xFront - length * 0.35));
    pts.push(new THREE.Vector2(innerWallR + 0.025, xFront - length * 0.35));
    pts.push(new THREE.Vector2(innerWallR + 0.025, domeCenterX));

    // 2. Semicircular aft dome outer contour (180-degree curve)
    const domeSteps = 16;
    for (let i = 0; i <= domeSteps; i++) {
      const a = Math.PI + (i / domeSteps) * Math.PI; // PI -> 2*PI
      const r = domeCenterR + Math.cos(a) * domeR;
      const x = domeCenterX - Math.sin(a) * domeR;
      pts.push(new THREE.Vector2(r, x));
    }

    // 3. Outer liner wall moving forward (+X) with stepped cooling louvers
    pts.push(new THREE.Vector2(outerWallR, domeCenterX + length * 0.28));
    pts.push(new THREE.Vector2(outerWallR - 0.028, domeCenterX + length * 0.28));
    pts.push(new THREE.Vector2(outerWallR - 0.028, domeCenterX + length * 0.56));
    pts.push(new THREE.Vector2(outerWallR - 0.052, domeCenterX + length * 0.56));
    pts.push(new THREE.Vector2(outerWallR - 0.052, xFront));

    // 4. Offset inward by wallThickness `t` and trace back along the inside surface
    pts.push(new THREE.Vector2(outerWallR - 0.052 - t, xFront));
    pts.push(new THREE.Vector2(outerWallR - 0.052 - t, domeCenterX + length * 0.56));
    pts.push(new THREE.Vector2(outerWallR - 0.028 - t, domeCenterX + length * 0.56));
    pts.push(new THREE.Vector2(outerWallR - 0.028 - t, domeCenterX + length * 0.28));
    pts.push(new THREE.Vector2(outerWallR - t, domeCenterX + length * 0.28));

    for (let i = domeSteps; i >= 0; i--) {
      const a = Math.PI + (i / domeSteps) * Math.PI;
      const r = domeCenterR + Math.cos(a) * (domeR - t);
      const x = domeCenterX - Math.sin(a) * (domeR - t);
      pts.push(new THREE.Vector2(r, x));
    }

    pts.push(new THREE.Vector2(innerWallR + 0.025 + t, domeCenterX));
    pts.push(new THREE.Vector2(innerWallR + 0.025 + t, xFront - length * 0.35));
    pts.push(new THREE.Vector2(innerWallR + t, xFront - length * 0.35));
    pts.push(new THREE.Vector2(innerWallR + t, xFront));
    pts.push(new THREE.Vector2(innerWallR, xFront));

    const lathe = new THREE.LatheGeometry(pts, 64);
    lathe.applyMatrix4(_Y_TO_X);
    return crease(lathe);
  }, [innerWallR, outerWallR, length, wallThickness]);

  // 6B. Reusable flanged dilution hole grommet factory (radial axis along +Y)
  const grommetGeos = useMemo(
    () =>
      dilutionRows.map((row) => {
        const rimR = row.holeR * 1.38;
        const h = wallThickness * 1.45;
        const pts = [
          new THREE.Vector2(row.holeR, -h),
          new THREE.Vector2(rimR, -h),
          new THREE.Vector2(rimR, h),
          new THREE.Vector2(row.holeR, h),
          new THREE.Vector2(row.holeR, -h),
        ];
        return crease(new THREE.LatheGeometry(pts, 20));
      }),
    [dilutionRows, wallThickness]
  );

  // 6C. Aft dome fuel-nozzle swirl cup boss (aligned along +X at domeCenterR)
  const nozzleBossGeo = useMemo(() => {
    const pts = [
      new THREE.Vector2(0.045, -0.08),
      new THREE.Vector2(0.095, -0.08),
      new THREE.Vector2(0.095, 0.02),
      new THREE.Vector2(0.125, 0.05),
      new THREE.Vector2(0.045, 0.05),
      new THREE.Vector2(0.045, -0.08),
    ];
    const lathe = new THREE.LatheGeometry(pts, 20);
    lathe.applyMatrix4(_Y_TO_X);
    return crease(lathe);
  }, []);

  const domeCenterR = (outerWallR + innerWallR) / 2;
  const xAft = -length / 2;

  return (
    <group>
      {/* Main Double-Walled Toroidal Liner */}
      {show.body === true && <M clip geo={linerBodyGeometry} />}

      {/* 14x Aft Dome Fuel Nozzle Swirl Cups */}
      {show.nozzles === true &&
        Array.from({ length: nozzleCount }, (_, i) => {
          const theta = (i * Math.PI * 2) / nozzleCount;
          return (
            <M
              key={`nozzle-${i}`}
              clip
              geo={nozzleBossGeo}
              p={[xAft, Math.cos(theta) * domeCenterR, Math.sin(theta) * domeCenterR]}
            />
          );
        })}

      {/* Peripheral Primary & Secondary Dilution Air Grommet Rings */}
      {show.grommets === true &&
        dilutionRows.map((row, rIdx) => {
          const wallR = row.onInnerWall ? innerWallR + 0.015 : outerWallR - 0.025;
          return (
            <group key={`row-${rIdx}`} position={[row.xOffset, 0, 0]}>
              {Array.from({ length: row.count }, (_, i) => {
                const theta = (i * Math.PI * 2) / row.count;
                return (
                  <group key={i} rotation={[theta, 0, 0]}>
                    <M clip geo={grommetGeos[rIdx]} p={[0, wallR, 0]} />
                  </group>
                );
              })}
            </group>
          );
        })}
    </group>
  );
};

export interface VariablePitchPropellerProps {
  hubR?: number;
  bladeTipR?: number;
  /** Collective blade pitch angle in degrees (feather = 82, cruise = 28, beta/reverse = -12) */
  collectivePitchDeg?: number;
  /** Explosion offsets for Wave 1 (spinner), Wave 2 (hub), and Wave 3 (radial blades) */
  explodeOffsets?: {
    spinnerX?: number;
    pitchDomeX?: number;
    bladeRadial?: number;
    backplateX?: number;
  };
  /** Render filter: split spinner / backplate / hub / dome / blades across <Part>s. */
  show?: { spinner?: boolean; backplate?: boolean; hub?: boolean; dome?: boolean; blades?: boolean };
  /** Render only these blade quadrants (0..3) so Blade_1..4 each own one. */
  bladeIndices?: number[];
}

/**
 * 7. 4-BLADE CONSTANT-SPEED / VARIABLE-PITCH PROPELLER & HUB ASSEMBLY
 * 4-arm forged hub spider, hydraulic pitch dome, parabolic spinner with blade
 * root collars, and 4 spanwise-twisted NACA airfoil propeller blades.
 */
export const VariablePitchPropellerHub: React.FC<VariablePitchPropellerProps> = ({
  hubR = 0.42,
  bladeTipR = 3.1,
  collectivePitchDeg = 26,
  explodeOffsets = {},
  show = { spinner: true, backplate: true, hub: true, dome: true, blades: true },
  bladeIndices = [0, 1, 2, 3],
}) => {
  const {
    spinnerX = 0,
    pitchDomeX = 0,
    bladeRadial = 0,
    backplateX = 0,
  } = explodeOffsets;

  // 7A. Central Splined Hub Barrel & Forward Hydraulic Pitch-Change Cylinder
  const centerBarrelGeo = useMemo(() => {
    const pts = [
      new THREE.Vector2(0.14, -0.32),
      new THREE.Vector2(hubR * 0.78, -0.32),
      new THREE.Vector2(hubR * 0.78, 0.32),
      new THREE.Vector2(0.14, 0.32),
      new THREE.Vector2(0.14, -0.32),
    ];
    const lathe = new THREE.LatheGeometry(pts, 32);
    lathe.applyMatrix4(_Y_TO_X);
    return crease(lathe);
  }, [hubR]);

  const radialSocketGeo = useMemo(() => {
    // Radial blade retention socket sleeve (along +Y)
    const pts = [
      new THREE.Vector2(0.15, 0.12),
      new THREE.Vector2(0.24, 0.12),
      new THREE.Vector2(0.24, hubR + 0.04),
      new THREE.Vector2(0.28, hubR + 0.04),
      new THREE.Vector2(0.28, hubR + 0.11),
      new THREE.Vector2(0.15, hubR + 0.11),
      new THREE.Vector2(0.15, 0.12),
    ];
    const lathe = new THREE.LatheGeometry(pts, 28);
    return crease(lathe);
  }, [hubR]);

  const pitchDomeGeo = useMemo(() => {
    const pts = [
      new THREE.Vector2(0.0, 0.68),
      new THREE.Vector2(0.22, 0.64),
      new THREE.Vector2(0.24, 0.32),
      new THREE.Vector2(0.31, 0.32),
      new THREE.Vector2(0.31, 0.27),
      new THREE.Vector2(0.16, 0.27),
      new THREE.Vector2(0.16, 0.58),
      new THREE.Vector2(0.0, 0.61),
    ];
    const lathe = new THREE.LatheGeometry(pts, 32);
    lathe.applyMatrix4(_Y_TO_X);
    return crease(lathe);
  }, []);

  // 7B. Parabolic Double-Walled Spinner Cone (ready for section: true)
  const spinnerConeGeo = useMemo(() => {
    const xBase = -0.34;
    const xTip = 1.18;
    const rBase = hubR * 1.32;
    const t = 0.032;
    const steps = 20;
    const pts: THREE.Vector2[] = [];

    // Outer nose contour
    for (let i = 0; i <= steps; i++) {
      const u = i / steps; // 0 = base, 1 = nose tip
      const x = THREE.MathUtils.lerp(xBase, xTip, u);
      const r = rBase * Math.sqrt(Math.max(0, 1 - Math.pow(u, 1.35)));
      pts.push(new THREE.Vector2(r, x));
    }
    // Inner wall contour back to base flange
    for (let i = steps; i >= 0; i--) {
      const u = i / steps;
      const x = THREE.MathUtils.lerp(xBase, xTip - t * 1.4, u);
      const r = Math.max(
        0,
        (rBase - t) * Math.sqrt(Math.max(0, 1 - Math.pow(u, 1.35)))
      );
      pts.push(new THREE.Vector2(r, x));
    }
    pts.push(pts[0].clone());

    const lathe = new THREE.LatheGeometry(pts, 48);
    lathe.applyMatrix4(_Y_TO_X);
    return crease(lathe);
  }, [hubR]);

  // 7C. Single Pitched Propeller Blade (Root Shank + Counterweight Clamp + Twisted Airfoil)
  // Oriented with radial span along +Y so rotation around Y changes collective blade pitch
  const propellerBladeGeo = useMemo(() => {
    const spanSteps = 18;
    const chordSteps = 8;
    const yRoot = hubR + 0.08;
    const yTip = bladeTipR;

    const positions: number[] = [];
    const indices: number[] = [];

    for (let is = 0; is <= spanSteps; is++) {
      const v = is / spanSteps; // 0 = root cuff, 1 = blade tip
      const y = THREE.MathUtils.lerp(yRoot, yTip, v);

      // Chord distribution: narrow cylindrical shank -> wide mid-blade paddle -> tapered tip
      const chord =
        0.48 *
        (0.42 + 1.15 * Math.sin(Math.PI * Math.pow(v, 0.65))) *
        (1 - 0.22 * Math.pow(v, 3));

      // Thickness transitions from thick structural cuff at root to thin airfoil at tip
      const maxThick = THREE.MathUtils.lerp(0.11, 0.018, Math.pow(v, 0.55));

      // Built-in washout twist: 34 deg at root down to 6 deg at tip (added to collectivePitchDeg)
      const localTwistRad = THREE.MathUtils.degToRad(34 * (1 - 0.82 * v));
      const cosT = Math.cos(localTwistRad);
      const sinT = Math.sin(localTwistRad);

      for (let ic = 0; ic <= chordSteps; ic++) {
        const u = ic / chordSteps; // 0 = leading edge, 1 = trailing edge
        const xc = (u - 0.42) * chord; // Pitch axis at 42% chord
        const camber = 0.07 * chord * 4 * u * (1 - u) * (1 - 0.4 * v);
        const halfT =
          maxThick *
          (2.969 * Math.sqrt(u) -
            1.26 * u -
            3.516 * u * u +
            2.843 * Math.pow(u, 3) -
            1.015 * Math.pow(u, 4));

        for (const side of [1, -1]) {
          const yt = camber + side * halfT;
          // Rotate chord section around radial +Y pitch axis
          const px = xc * sinT + yt * cosT;
          const pz = xc * cosT - yt * sinT;
          positions.push(px, y, pz);
        }
      }
    }

    const stride = (chordSteps + 1) * 2;
    for (let is = 0; is < spanSteps; is++) {
      for (let ic = 0; ic < chordSteps; ic++) {
        const i0 = is * stride + ic * 2;
        const i1 = i0 + 2;
        const i2 = (is + 1) * stride + ic * 2;
        const i3 = i2 + 2;

        indices.push(i0, i1, i2, i1, i3, i2);
        indices.push(i0 + 1, i2 + 1, i1 + 1, i1 + 1, i2 + 1, i3 + 1);
      }
    }

    // Tip cap (is = spanSteps) & root cap (is = 0)
    const tipStart = spanSteps * stride;
    for (let ic = 0; ic < chordSteps; ic++) {
      const t0 = tipStart + ic * 2;
      indices.push(t0, t0 + 2, t0 + 1, t0 + 1, t0 + 2, t0 + 3);
    }

    const geo = new THREE.BufferGeometry();
    geo.setAttribute('position', new THREE.Float32BufferAttribute(positions, 3));
    geo.setIndex(indices);
    return crease(geo);
  }, [hubR, bladeTipR]);

  const bladeShankGeo = useMemo(() => {
    // Cylindrical retention shank + pitch counterweight collar
    const pts = [
      new THREE.Vector2(0.08, hubR * 0.45),
      new THREE.Vector2(0.145, hubR * 0.45),
      new THREE.Vector2(0.145, hubR + 0.08),
      new THREE.Vector2(0.21, hubR + 0.08),
      new THREE.Vector2(0.21, hubR + 0.14),
      new THREE.Vector2(0.08, hubR + 0.14),
      new THREE.Vector2(0.08, hubR * 0.45),
    ];
    const lathe = new THREE.LatheGeometry(pts, 24);
    return crease(lathe);
  }, [hubR]);

  const pitchRad = THREE.MathUtils.degToRad(collectivePitchDeg);

  return (
    <group>
      {/* 1. Aft Spinner Bulkhead Flange */}
      {show.backplate === true && (
        <group position={[backplateX, 0, 0]}>
          <M clip geo={crease(cyl(hubR * 1.32, hubR * 1.32, 0.05, 48))} r={[0, 0, -Math.PI / 2]} />
        </group>
      )}

      {/* 2. Forged 4-Arm Hub Spider */}
      {show.hub === true && (
        <group>
          <M clip geo={centerBarrelGeo} />
          {[0, 1, 2, 3].map((i) => (
            <group key={`socket-${i}`} rotation={[(i * Math.PI) / 2, 0, 0]}>
              <M clip geo={radialSocketGeo} />
            </group>
          ))}
        </group>
      )}

      {/* 3. Forward Hydraulic Pitch-Change Dome */}
      {show.dome === true && (
        <group position={[pitchDomeX, 0, 0]}>
          <M clip geo={pitchDomeGeo} />
        </group>
      )}

      {/* 4. 4x Variable-Pitch Propeller Blades (explode radially along local +Y) */}
      {show.blades === true &&
        bladeIndices.map((i) => (
          <group key={`blade-${i}`} rotation={[(i * Math.PI) / 2, 0, 0]}>
            <group position={[0, bladeRadial, 0]} rotation={[0, pitchRad, 0]}>
              <M clip geo={bladeShankGeo} />
              <M clip geo={propellerBladeGeo} />
            </group>
          </group>
        ))}

      {/* 5. Parabolic Nose Spinner Cone */}
      {show.spinner === true && (
        <group position={[spinnerX, 0, 0]}>
          <M clip geo={spinnerConeGeo} />
        </group>
      )}
    </group>
  );
};
