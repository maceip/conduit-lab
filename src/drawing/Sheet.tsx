import * as THREE from 'three';
import { useMachine } from '../machines';
import type { BomCallout, DimensionDef } from '../machines/types';
import { useStudio } from '../state';
import { useDrawing } from './DrawingRig';
import { project, type DrawingLayout } from './layout';

/** Rectangle of a world box in one orthographic view. */
function viewRect(layout: DrawingLayout, view: 'front' | 'top' | 'left', box: THREE.Box3) {
  const a = project(layout, view, box.min);
  const b = project(layout, view, box.max);
  return { x0: Math.min(a.x, b.x), x1: Math.max(a.x, b.x), y0: Math.min(a.y, b.y), y1: Math.max(a.y, b.y) };
}

/**
 * Projection lines for the focused part: 长对正 between front and top,
 * 高平齐 between front and left, 宽相等 from top to left through the 45° line.
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
 * 尺寸链：从 from 到 to 在指定视图上偏移 offset 像素，画界线、箭头与数字。
 * 总长/分段链在主视图（长对正），转子直径在左视图（圆的十字中心线旁）。
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
  // 45° 工程箭头
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

/** BOM 气泡：编号 + 引线，统一排在主视图上沿。 */
function Balloon({ layout, b, i, index, name }: { layout: DrawingLayout; b: BomCallout; i: number; index: number; name: string }) {
  const p = project(layout, 'front', new THREE.Vector3(...b.p));
  const front = layout.views.find((v) => v.id === 'front')!.rect;
  const bx = p.x;
  const by = Math.max(86, front.y - 22 - (i % 3) * 34);
  return (
    <g className="balloon" stroke="currentColor" fill="none" opacity={0.9}>
      <line x1={bx} y1={by + 11} x2={p.x} y2={p.y} strokeWidth={1} />
      <circle cx={p.x} cy={p.y} r={2.2} fill="currentColor" stroke="none" />
      <circle cx={bx} cy={by} r={12} strokeWidth={1.3} fill="var(--paper, #fff)" />
      <text x={bx} y={by + 4.2} textAnchor="middle" fill="currentColor" stroke="none" fontSize={11.5} fontFamily="inherit">{String(index).padStart(2, '0')}</text>
      <title>{name}</title>
    </g>
  );
}

/** Labels, projection lines and title block over the three-view drawing. */
export function DrawingSheet() {
  const machine = useMachine();
  const { layout, box } = useDrawing();
  const projection = useStudio((s) => s.projection);
  const section = useStudio((s) => s.section);
  const focus = useStudio((s) => s.hovered ?? s.selected);
  if (!layout) return null;
  const part = focus ? machine.parts.find((p) => p.id === focus) : undefined;
  const tb = layout.titleBlock;
  return (
    <div className="sheet" aria-hidden="true">
      <svg className="sheet-svg">
        <CentreCrosses layout={layout} lines={machine.centreLines} />
        {projection && box && <ProjectionLines layout={layout} box={box} />}
        {machine.dimensions?.map((d, i) => <Dim key={i} layout={layout} d={d} />)}
        {machine.bom?.map((b, i) => {
          const part = machine.parts.find((pp) => pp.id === b.id);
          return part ? <Balloon key={b.id} layout={layout} b={b} i={i} index={part.index} name={part.name} /> : null;
        })}
      </svg>
      {layout.views.map((v) => (
        <span key={v.id} className={`sheet-label sheet-label--${v.id}`} style={{ left: v.rect.x + v.rect.w / 2, top: v.rect.y + v.rect.h + 4 }}>
          {v.id === 'front' && section ? '全剖主视图' : v.label}
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
            <td>比例</td><td>{machine.scale}</td>
          </tr>
          <tr>
            <td>图号</td><td>{machine.drawingNo}</td>
          </tr>
          <tr>
            <td>格物 · 工程制图</td><td>投影</td><td>第一角</td>
          </tr>
        </tbody>
      </table>
    </div>
  );
}
