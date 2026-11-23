import * as THREE from 'three';
import { useMachine } from '../machines';
import { isEmbed, motion, useStudio } from '../state';
import type { BomCallout, DimensionDef } from '../machines/types';
import { useDrawing } from './DrawingRig';
import { project, type DrawingLayout } from './layout';

/** Rectangle of a world box in one orthographic view. */
function viewRect(layout: DrawingLayout, view: 'front' | 'top' | 'left', box: THREE.Box3) {
  const a = project(layout, view, box.min);
  const b = project(layout, view, box.max);
  return { x0: Math.min(a.x, b.x), x1: Math.max(a.x, b.x), y0: Math.min(a.y, b.y), y1: Math.max(a.y, b.y) };
}

/**
 * Projection lines for the focused part: length aligned between front and top,
 * height level between front and left, width equal from top to left via the 45° line.
 */
function ProjectionLines({ layout, box }: { layout: DrawingLayout; box: THREE.Box3 }) {
  const f = viewRect(layout, 'front', box);
  const t = viewRect(layout, 'top', box);
  const l = viewRect(layout, 'left', box);
  // On the 45° line, a depth z sits at (left x of z, top y of z).
  const miter = (y: number) => layout.anchors.left.x + (y - layout.anchors.top.y);
  const zMin = layout.bounds.min.z;
  const zMax = layout.bounds.max.z;
  const m0 = project(layout, 'top', new THREE.Vector3(0, 0, zMin)).y - 30;
  const m1 = project(layout, 'top', new THREE.Vector3(0, 0, zMax)).y + 30;
  return (
    <g className="proj">
      {[f.x0, f.x1].map((x) => <line key={`v${x}`} x1={x} y1={f.y1} x2={x} y2={t.y0} />)}
      {[f.y0, f.y1].map((y) => <line key={`h${y}`} x1={f.x1} y1={y} x2={l.x0} y2={y} />)}
      {[t.y0, t.y1].map((y) => (
        <polyline key={`w${y}`} points={`${t.x1},${y} ${miter(y)},${y} ${miter(y)},${l.y1}`} />
      ))}
      <line className="miter" x1={miter(m0)} y1={m0} x2={miter(m1)} y2={m1} />
      {[f, t, l].map((r, i) => <rect key={i} className="box" x={r.x0} y={r.y0} width={r.x1 - r.x0} height={r.y1 - r.y0} />)}
    </g>
  );
}

/** Centre crosses for revolved features whose axis points straight at a view. */
function CentreCrosses({ layout, lines }: { layout: DrawingLayout; lines: Array<[number[], number[], number?]> }) {
  const crosses: Array<{ x: number; y: number; r: number }> = [];
  for (const [a, b, radius] of lines) {
    if (!radius) continue;
    const d = new THREE.Vector3(b[0] - a[0], b[1] - a[1], b[2] - a[2]).normalize();
    const p = new THREE.Vector3(...(a as [number, number, number]));
    const r = radius * layout.scale + 10;
    // Axis along z faces the front view, along y the top view, along x the left view.
    if (Math.abs(d.z) > 0.99) crosses.push({ ...project(layout, 'front', p), r });
    if (Math.abs(d.y) > 0.99) crosses.push({ ...project(layout, 'top', p), r });
    if (Math.abs(d.x) > 0.99) crosses.push({ ...project(layout, 'left', p), r });
  }
  return (
    <g className="cross">
      {crosses.map((c, i) => (
        <g key={i}>
          <line x1={c.x - c.r} y1={c.y} x2={c.x + c.r} y2={c.y} />
          <line x1={c.x} y1={c.y - c.r} x2={c.x} y2={c.y + c.r} />
        </g>
      ))}
    </g>
  );
}

/**
 * Dimension chains: from–to offset `offset` px in a view, with extension lines,
 * arrows and the number. The length chain sits on the front view, the rotor
 * diameter on the left view beside the centre cross.
 */
function Dim({ layout, d }: { layout: DrawingLayout; d: DimensionDef }) {
  const a = project(layout, d.view, new THREE.Vector3(...d.from));
  const b = project(layout, d.view, new THREE.Vector3(...d.to));
  const dir = b.clone().sub(a);
  const len = dir.length();
  if (len < 2) return null;
  dir.divideScalar(len);
  const n = new THREE.Vector2(-dir.y, dir.x).multiplyScalar(d.offset);
  const a2 = a.clone().add(n);
  const b2 = b.clone().add(n);
  // 45° engineering arrowhead
  const tick = (at: THREE.Vector2, toward: THREE.Vector2) => {
    const t = toward.clone().sub(at).normalize();
    const w = new THREE.Vector2(-t.y, t.x).multiplyScalar(3.2);
    const tip = at.clone();
    const back = at.clone().addScaledVector(t, 11);
    return `${back.x + w.x},${back.y + w.y} ${tip.x},${tip.y} ${back.x - w.x},${back.y - w.y}`;
  };
  const mid = a2.clone().add(b2).multiplyScalar(0.5);
  return (
    <g className="dim" stroke="currentColor" fill="none" opacity={0.85}>
      <line x1={a.x} y1={a.y} x2={a2.x + n.x * 0.12} y2={a2.y + n.y * 0.12} strokeWidth={1} />
      <line x1={b.x} y1={b.y} x2={b2.x + n.x * 0.12} y2={b2.y + n.y * 0.12} strokeWidth={1} />
      <line x1={a2.x} y1={a2.y} x2={b2.x} y2={b2.y} strokeWidth={1.4} />
      <polygon points={tick(a2, b2)} fill="currentColor" stroke="none" />
      <polygon points={tick(b2, a2)} fill="currentColor" stroke="none" />
      <rect x={mid.x - 22} y={mid.y - 9} width={44} height={18} fill="var(--paper, #fff)" stroke="none" opacity={0.92} />
      <text x={mid.x} y={mid.y + 4.5} textAnchor="middle" fill="currentColor" stroke="none" fontSize={12.5} fontFamily="inherit">{d.label}</text>
    </g>
  );
}

/**
 * BOM balloon with a leader-rail route: datum dot on the part, a 45° elbow,
 * then a horizontal landing shelf to the balloon docked on the top rail
 * (above the front view) or the bottom rail (the gap above the top view).
 * Anchors ride each part's explosion travel so leaders track parts t=0→1.
 */
function Balloon({ layout, b, index, name, tint, explode, stage, unit }: {
  layout: DrawingLayout;
  b: BomCallout;
  index: number;
  name: string;
  tint?: string;
  explode: [number, number, number];
  stage: [number, number];
  unit: number;
}) {
  const front = layout.views.find((v) => v.id === 'front')!.rect;
  const top = layout.views.find((v) => v.id === 'top')!.rect;
  // Live anchor: assembled position + the part's own explosion travel.
  let w = 0;
  if (stage[1] > stage[0]) {
    const x = Math.min(1, Math.max(0, (motion.explode - stage[0]) / (stage[1] - stage[0])));
    w = x * x * (3 - 2 * x);
  }
  const live = new THREE.Vector3(
    b.p[0] + explode[0] * w * unit,
    b.p[1] + explode[1] * w * unit,
    b.p[2] + explode[2] * w * unit,
  );
  const anchor = project(layout, 'front', live);
  const rail = b.rail ?? 'top';
  const railY = rail === 'top'
    ? Math.max(86, front.y - 24 - (index % 2) * 34)
    : top.y - 30 - (index % 2) * 34;
  const [edx, edy] = b.elbowOffset ?? [20, rail === 'top' ? -40 : 46];
  const elbow = { x: anchor.x + edx, y: railY + (edy > 0 ? -Math.abs(edy) * 0.2 : Math.abs(edy) * 0.2) };
  const bx = elbow.x + (edx >= 0 ? 26 : -26);
  const stroke = tint ?? 'currentColor';
  return (
    <g className="balloon" stroke={stroke} fill="none" opacity={0.92}>
      {/* 45° elbow then a horizontal landing shelf */}
      <polyline points={`${anchor.x},${anchor.y} ${elbow.x},${railY} ${bx},${railY}`} fill="none" strokeWidth={1} />
      <circle cx={anchor.x} cy={anchor.y} r={2.2} fill={stroke} stroke="none" />
      <circle cx={bx} cy={railY} r={11} strokeWidth={1.3} fill="var(--paper, #fff)" />
      <text x={bx} y={railY + 3.9} textAnchor="middle" fill={stroke} stroke="none" fontSize={11} fontFamily="inherit">{String(index).padStart(2, '0')}</text>
      {b.code && (
        <text x={bx + (edx >= 0 ? 15 : -15)} y={railY + 3.6} textAnchor={edx >= 0 ? 'start' : 'end'} fill={stroke} stroke="none" fontSize={9} fontFamily="inherit" opacity={0.85}>{b.code}</text>
      )}
      <title>{[b.code, name, b.title, b.material, b.qty ? `×${b.qty}` : ''].filter(Boolean).join(' · ')}</title>
    </g>
  );
}

/** Labels, projection lines and title block over the three-view drawing. */
export function DrawingSheet() {
  const machine = useMachine();
  const { layout, box } = useDrawing();
  const projection = useStudio((s) => s.projection);
  const section = useStudio((s) => s.section);
  const labels = useStudio((s) => s.labels);
  const focus = useStudio((s) => s.hovered ?? s.selected);
  if (!layout) return null;
  const part = focus ? machine.parts.find((p) => p.id === focus) : undefined;
  const tb = layout.titleBlock;
  // Never dump 30+ circular BOM balloons onto compact/embedded plates; only render monochrome balloons when full-studio labels are explicitly enabled.
  const showBalloons = !isEmbed && labels && layout.views[0].rect.w > 480;
  const dims = (() => {
    const all = machine.dimensions ?? [];
    if (!isEmbed) return all;
    const overallFront = all.find((d) => d.view === 'front');
    const overallLeft = all.find((d) => d.view === 'left' && d.offset >= 100) ?? all.find((d) => d.view === 'left');
    return [
      overallFront ? { ...overallFront, offset: 26 } : null,
      overallLeft ? { ...overallLeft, offset: 28 } : null,
    ].filter((d): d is DimensionDef => d !== null);
  })();
  return (
    <div className="sheet" aria-hidden="true">
      <svg className="sheet-svg">
        <CentreCrosses layout={layout} lines={machine.centreLines} />
        {projection && box && <ProjectionLines layout={layout} box={box} />}
        {dims.map((d, i) => <Dim key={i} layout={layout} d={d} />)}
        {showBalloons && machine.bom?.map((b) => {
          const item = machine.parts.find((pp) => pp.id === b.id);
          return item ? (
            <Balloon
              key={b.id}
              layout={layout}
              b={b}
              index={item.index}
              name={item.name}
              explode={item.explode}
              stage={item.stage}
              unit={machine.unit ?? 1}
            />
          ) : null;
        })}
      </svg>
      {layout.views.map((v) => (
        <span
          key={v.id}
          className={`sheet-label sheet-label--${v.id}`}
          style={{
            left: v.rect.x + v.rect.w / 2,
            top: isEmbed && v.id === 'front' ? Math.max(8, v.rect.y - 16) : v.rect.y + v.rect.h + 4,
          }}
        >
          {v.id === 'front' && section ? 'Section Front View' : v.label}
        </span>
      ))}
      {part && (
        <span className="sheet-focus" style={{ left: layout.views[0].rect.x, top: layout.views[0].rect.y - 26 }}>
          {String(part.index).padStart(2, '0')} {part.name}
        </span>
      )}
      <table className="sheet-title" style={{ left: tb.x, top: tb.y, width: tb.w }}>
        <tbody>
          <tr>
            <td rowSpan={2} className="sheet-title-name">{machine.name}</td>
            <td>Scale</td><td>{machine.scale}</td>
          </tr>
          <tr>
            <td>Dwg No</td><td>{machine.drawingNo}</td>
          </tr>
          <tr>
            <td>Inkwork · Engineering Drawing</td><td>Proj</td><td>1st Angle</td>
          </tr>
        </tbody>
      </table>
    </div>
  );
}
