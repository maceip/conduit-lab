import type { Part, Vec2, Vec3 } from '../../contract';
import { add, cameraFor, dot, norm, sub } from './camera';
import { centroid, facesFor } from './geometry';
import { shadeFor } from './shade';
import { explodedOffset } from './explode';
import { centerlineFor } from './centerline';
import { billFor, type BillRow } from './partsList';
import {
  BALLOON_R,
  balloonAnchor,
  balloonSide,
  separateBalloons,
  type BalloonPlacement,
  type Bounds,
} from './balloon';
import { leaderPath } from './leader';

export { BALLOON_R } from './balloon';
export { renderPlate, type RenderOptions } from './render';
export { hatchPattern, type HatchPattern } from './hatch';
export { dimensionLine, type Dimension } from './dimension';
export { leaderPath } from './leader';
export { centerlineFor } from './centerline';
export { explodedOffset } from './explode';
export { billFor, type BillRow } from './partsList';
export { shadeFor, shadeClassIndex, SHADE_CLASS } from './shade';
export { facesFor, type RawFace } from './geometry';
export { cameraFor, type Camera } from './camera';

export type { Vec2, Vec3, Part, Tone } from '../../contract';

/**
 * A projected, drawable face.
 *
 * `partId` and `hatch` extend the minimal contract with what the renderer
 * needs to keep adjacent sections apart; `depth` carries the painter's-order
 * key so faces and edges interleave exactly as the published engine draws
 * them.
 */
export interface Face {
  /** Projected 2D points in the viewBox coordinate space. */
  points: Vec2[];
  /** Unit normal in view space. */
  normal: Vec3;
  /** Shade ramp index. */
  shade: number;
  /** True when this face is a cut surface and must be hatched. */
  cut: boolean;
  /** True when the face is back-facing and should be drawn as a hidden edge. */
  hidden: boolean;
  /** Owning part. */
  partId: string;
  /** Hatch pattern index for a cut face, -1 otherwise. */
  hatch: number;
  /** Painter's-order depth (larger is nearer the camera). */
  depth: number;
}

export interface Edge {
  a: Vec2;
  b: Vec2;
  kind: 'structure' | 'cut' | 'hidden' | 'centerline';
  /** Painter's-order depth. */
  depth: number;
}

/** Title-block caption for a plate. */
export interface Caption {
  /** Figure number, e.g. "FIG 09". */
  figure: string;
  /** Plate name. */
  name: string;
  /** Scale statement, e.g. "NTS". */
  scale: string;
}

export interface Assembly {
  parts: Part[];
  /** Camera azimuth/elevation in degrees. */
  azDeg: number;
  elDeg: number;
  /** Assembly axis used for explode offsets. */
  axis: Vec3;
  /** Explode gap multiplier. */
  explodeScale: number;
  /** Optional parts list rendered beneath the plate. */
  partsList: boolean;
  /** Optional title-block caption. */
  caption?: Caption;
  /** Optional dimension lines, given in world coordinates. */
  dimensions?: Array<{ a: Vec3; b: Vec3; label: string }>;
}

export interface RenderedPlate {
  /** viewBox attribute value, e.g. "0 0 640 480". */
  viewBox: string;
  faces: Face[];
  edges: Edge[];
  /** Balloon anchors in viewBox space, one per part that has a balloon. */
  balloons: Array<{ partId: string; number: number; at: Vec2 }>;
  /** Leader polylines from part anchor to balloon anchor. */
  leaders: Array<{ partId: string; points: Vec2[] }>;
  /** Centreline segments. */
  centerlines: Array<{ a: Vec2; b: Vec2 }>;
  /** Dimension lines with terminator ticks and a value label. */
  dimensions: Array<{ a: Vec2; b: Vec2; label: string }>;
  /** Parts-list rows. */
  bill: BillRow[];
  /** Total number of parts in the assembly. */
  partCount: number;
  /** Title-block caption, when the assembly carries one. */
  caption?: Caption;
}

/** Crease angle above which an edge is drawn as a contour (v8-iso default). */
const CREASE_DEG = 34;
const COS_CREASE = Math.cos((CREASE_DEG * Math.PI) / 180);

/** Vertical offset of the drawn edge in front of its face, as in iso-cad. */
const EDGE_DEPTH_BIAS = 0.12;

/** Radius used to round numeric output, keeping the projection deterministic. */
const PRECISION = 1000;

function round(n: number): number {
  return Math.round(n * PRECISION) / PRECISION;
}

function round2(p: Vec2): Vec2 {
  return [round(p[0]), round(p[1])];
}

/**
 * The axis a section plane runs through, per geometry kind. A cut face is the
 * visible face most aligned with it.
 */
function sectionNormal(spec: Part['geometry']): Vec3 {
  switch (spec.kind) {
    case 'cyl':
      return norm(sub(spec.to, spec.from));
    case 'tube': {
      const first = spec.points[0];
      const last = spec.points[spec.points.length - 1];
      return first && last ? norm(sub(last, first)) : [0, 0, 1];
    }
    case 'box':
    case 'revolve':
    case 'extrude':
    case 'loft':
      return [0, 0, 1];
    default: {
      const never: never = spec;
      throw new Error(`engine: unsupported geometry ${JSON.stringify(never)}`);
    }
  }
}

/** Signed area of a projected polygon. */
function projectedArea(points: Vec2[]): number {
  let area = 0;
  for (let i = 0; i < points.length; i++) {
    const a = points[i];
    const b = points[(i + 1) % points.length];
    if (!a || !b) continue;
    area += a[0] * b[1] - b[0] * a[1];
  }
  return Math.abs(area) / 2;
}

/** Centroid of a projected polygon. */
function centroid2(points: Vec2[]): Vec2 {
  let x = 0;
  let y = 0;
  for (const p of points) {
    x += p[0];
    y += p[1];
  }
  const n = points.length || 1;
  return [x / n, y / n];
}

interface FaceRecord {
  normal: Vec3;
  visible: boolean;
  cut: boolean;
  depth: number;
}

/**
 * Project an assembly into drawable geometry. Pure — no DOM, no React.
 */
export function projectAssembly(assembly: Assembly): RenderedPlate {
  const camera = cameraFor(assembly.azDeg, assembly.elDeg);

  // Sectioned parts take a hatch index in assembly order, so two sectioned
  // parts that sit next to each other always hatch in opposite directions.
  const hatchOf = new Map<string, number>();
  let hatchCount = 0;
  for (const part of assembly.parts) {
    if (part.sectioned) hatchOf.set(part.id, hatchCount++);
  }

  const faces: Face[] = [];
  const edges: Edge[] = [];
  const centerlines: Array<{ a: Vec2; b: Vec2 }> = [];
  /** Balloon anchors per ballooned part, in assembly order. */
  const anchors = new Map<string, Vec2>();

  for (const part of assembly.parts) {
    const offset = explodedOffset(part, assembly);
    const raw = facesFor(part.geometry);
    const world = raw.map((f) => ({
      points: f.points.map((p) => add(p, offset)),
      normal: f.normal,
    }));

    const records: FaceRecord[] = world.map((f) => {
      const c = centroid(f.points);
      return {
        normal: f.normal,
        visible: dot(f.normal, camera.view) > 1e-5,
        cut: false,
        depth: dot(c, camera.view),
      };
    });

    // Choose the cut face: the visible face most aligned with the section
    // axis. A part only counts as sectioned when it has a real cut to show.
    let cutIndex = -1;
    if (part.sectioned) {
      const sec = sectionNormal(part.geometry);
      let best = -Infinity;
      world.forEach((f, i) => {
        if (!records[i]?.visible) return;
        const d = dot(f.normal, sec);
        if (d > best) {
          best = d;
          cutIndex = i;
        }
      });
      if (best < 0.25) cutIndex = -1;
      if (cutIndex >= 0) {
        const rec = records[cutIndex];
        if (rec) rec.cut = true;
      }
    }

    // Project the faces.
    const projected = world.map((f, i) => {
      const rec = records[i];
      return {
        points: f.points.map((p) => camera.project(p)),
        normal: camera.viewNormal(f.normal),
        shade: shadeFor(f.normal, camera.light),
        cut: rec?.cut ?? false,
        hidden: !(rec?.visible ?? false),
        partId: part.id,
        hatch: part.sectioned ? (hatchOf.get(part.id) ?? -1) : -1,
        depth: rec?.depth ?? 0,
      };
    });

    // The balloon anchor sits on the part's own surface: the centre of its
    // largest visible face.
    let bestArea = -1;
    let anchor: Vec2 | null = null;
    projected.forEach((f) => {
      if (f.hidden) return;
      const area = projectedArea(f.points);
      if (area > bestArea) {
        bestArea = area;
        anchor = centroid2(f.points);
      }
    });
    if (anchor && typeof part.balloon === 'number') {
      anchors.set(part.id, anchor);
    }

    faces.push(...projected);

    // Edge map, ported from `addMesh` in iso-cad.mjs.
    const vKey = (p: Vec3) => `${Math.round(p[0] * 50)},${Math.round(p[1] * 50)},${Math.round(p[2] * 50)}`;
    const edgeMap = new Map<string, { a: Vec3; b: Vec3; faces: FaceRecord[] }>();
    world.forEach((f, fi) => {
      const rec = records[fi];
      if (!rec) return;
      const keys = f.points.map(vKey);
      for (let i = 0; i < f.points.length; i++) {
        const j = (i + 1) % f.points.length;
        const k0 = keys[i];
        const k1 = keys[j];
        if (k0 === undefined || k1 === undefined || k0 === k1) continue;
        const a = f.points[i];
        const b = f.points[j];
        if (!a || !b) continue;
        const ek = k0 < k1 ? `${k0}|${k1}` : `${k1}|${k0}`;
        let ent = edgeMap.get(ek);
        if (!ent) {
          ent = { a, b, faces: [] };
          edgeMap.set(ek, ent);
        }
        ent.faces.push(rec);
      }
    });

    for (const ent of edgeMap.values()) {
      const visFaces = ent.faces.filter((f) => f.visible);
      if (visFaces.length === 0) {
        // Entirely behind the camera: a hidden edge.
        edges.push({
          a: camera.project(ent.a),
          b: camera.project(ent.b),
          kind: 'hidden',
          depth: dot(centroid([ent.a, ent.b]), camera.view) - EDGE_DEPTH_BIAS,
        });
        continue;
      }
      let isContour = visFaces.length === 1;
      if (visFaces.length >= 2) {
        const f0 = visFaces[0];
        const f1 = visFaces[1];
        if (f0 && f1) isContour = dot(f0.normal, f1.normal) < COS_CREASE;
      }
      if (!isContour) continue;
      const isCut = visFaces.some((f) => f.cut);
      let maxD = -Infinity;
      for (const f of visFaces) if (f.depth > maxD) maxD = f.depth;
      edges.push({
        a: camera.project(ent.a),
        b: camera.project(ent.b),
        kind: isCut ? 'cut' : 'structure',
        depth: maxD + EDGE_DEPTH_BIAS,
      });
    }

    // Centreline through the part's axis of symmetry.
    const cl = centerlineFor(part);
    if (cl) {
      centerlines.push({
        a: camera.project(add(cl.a, offset)),
        b: camera.project(add(cl.b, offset)),
      });
    }
  }

  faces.sort((a, b) => a.depth - b.depth);
  edges.sort((a, b) => a.depth - b.depth);

  // Dimension lines are authored in world coordinates and projected here.
  const dimensions: RenderedPlate['dimensions'] = (assembly.dimensions ?? []).map((d) => ({
    a: camera.project(d.a),
    b: camera.project(d.b),
    label: d.label,
  }));

  // Bounds of the drawn geometry.
  let minX = Infinity;
  let maxX = -Infinity;
  let minY = Infinity;
  let maxY = -Infinity;
  const grow = (x: number, y: number): void => {
    if (x < minX) minX = x;
    if (x > maxX) maxX = x;
    if (y < minY) minY = y;
    if (y > maxY) maxY = y;
  };
  for (const f of faces) {
    for (const p of f.points) grow(p[0], p[1]);
  }
  for (const d of dimensions) {
    grow(d.a[0], d.a[1]);
    grow(d.b[0], d.b[1]);
  }
  if (!Number.isFinite(minX)) {
    minX = 0;
    maxX = 0;
    minY = 0;
    maxY = 0;
  }
  const bounds: Bounds = { minX, maxX, minY, maxY };

  // Balloons: outside the drawing, on the side with the most room.
  const placements: BalloonPlacement[] = [];
  const ballooned = assembly.parts.filter(
    (p): p is Part & { balloon: number } => typeof p.balloon === 'number' && anchors.has(p.id),
  );
  for (const part of ballooned) {
    const anchor = anchors.get(part.id);
    if (!anchor) continue;
    const side = balloonSide(bounds, anchor);
    placements.push({ at: balloonAnchor(bounds, anchor, side), side });
  }
  separateBalloons(placements);

  const balloons: RenderedPlate['balloons'] = [];
  const leaders: RenderedPlate['leaders'] = [];
  ballooned.forEach((part, i) => {
    const placement = placements[i];
    const anchor = anchors.get(part.id);
    if (!placement || !anchor) return;
    balloons.push({ partId: part.id, number: part.balloon, at: placement.at });
    leaders.push({ partId: part.id, points: leaderPath(anchor, placement.at) });
  });

  // Content bounds include the balloon circles.
  let contentMinX = bounds.minX;
  let contentMaxX = bounds.maxX;
  let contentMinY = bounds.minY;
  let contentMaxY = bounds.maxY;
  for (const b of balloons) {
    if (b.at[0] - BALLOON_R < contentMinX) contentMinX = b.at[0] - BALLOON_R;
    if (b.at[0] + BALLOON_R > contentMaxX) contentMaxX = b.at[0] + BALLOON_R;
    if (b.at[1] - BALLOON_R < contentMinY) contentMinY = b.at[1] - BALLOON_R;
    if (b.at[1] + BALLOON_R > contentMaxY) contentMaxY = b.at[1] + BALLOON_R;
  }

  const bill = assembly.partsList ? billFor(assembly.parts) : [];
  const bandHeight = Math.max(bill.length > 0 ? 26 + bill.length * 15 : 0, assembly.caption ? 46 : 0);

  const spanX = Math.max(80, contentMaxX - contentMinX);
  const spanY = Math.max(80, contentMaxY - contentMinY);
  const padX = Math.max(16, spanX * 0.08);
  const padY = Math.max(14, spanY * 0.08);
  const vw = Math.ceil(spanX + padX * 2);
  const vh = Math.ceil(spanY + padY * 2 + bandHeight);
  const ox = padX - contentMinX;
  const oy = padY - contentMinY;

  const shift = (p: Vec2): Vec2 => [p[0] + ox, p[1] + oy];

  return {
    viewBox: `0 0 ${vw} ${vh}`,
    faces: faces.map((f) => ({
      ...f,
      points: f.points.map((p) => round2(shift(p))),
    })),
    edges: edges.map((e) => ({ ...e, a: round2(shift(e.a)), b: round2(shift(e.b)) })),
    balloons: balloons.map((b) => ({ ...b, at: round2(shift(b.at)) })),
    leaders: leaders.map((l) => ({ ...l, points: l.points.map((p) => round2(shift(p))) })),
    centerlines: centerlines.map((c) => ({ a: round2(shift(c.a)), b: round2(shift(c.b)) })),
    dimensions: dimensions.map((d) => ({
      a: round2(shift(d.a)),
      b: round2(shift(d.b)),
      label: d.label,
    })),
    bill,
    partCount: assembly.parts.length,
    ...(assembly.caption ? { caption: assembly.caption } : {}),
  };
}
