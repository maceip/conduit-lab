import * as THREE from 'three';
import { useMachine } from '../machines';
import { MACHINE_LANDMARKS, type PrimaryLandmark } from '../machines/landmarks';
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
  const miter = (y: number) => layout.anchors.left.x + (y - layout.anchors.top.y);
  const zMin = layout.bounds.min.z;
  const zMax = layout.bounds.max.z;
  const m0 = project(layout, 'top', new THREE.Vector3(0, 0, zMin)).y - 24;
  const m1 = project(layout, 'top', new THREE.Vector3(0, 0, zMax)).y + 24;
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
    const r = radius * layout.scale + 8;
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

/** Dimension chain with extension lines, 45° arrowheads and mono label. */
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
  const tick = (at: THREE.Vector2, toward: THREE.Vector2) => {
    const t = toward.clone().sub(at).normalize();
    const w = new THREE.Vector2(-t.y, t.x).multiplyScalar(2.6);
    const tip = at.clone();
    const back = at.clone().addScaledVector(t, 8.5);
    return `${back.x + w.x},${back.y + w.y} ${tip.x},${tip.y} ${back.x - w.x},${back.y - w.y}`;
  };
  const mid = a2.clone().add(b2).multiplyScalar(0.5);
  return (
    <g className="dim" stroke="var(--hair-strong)" fill="none">
      <line x1={a.x} y1={a.y} x2={a2.x + n.x * 0.1} y2={a2.y + n.y * 0.1} strokeWidth={0.9} />
      <line x1={b.x} y1={b.y} x2={b2.x + n.x * 0.1} y2={b2.y + n.y * 0.1} strokeWidth={0.9} />
      <line x1={a2.x} y1={a2.y} x2={b2.x} y2={b2.y} strokeWidth={1.05} />
      <polygon points={tick(a2, b2)} fill="var(--ink-2)" stroke="none" />
      <polygon points={tick(b2, a2)} fill="var(--ink-2)" stroke="none" />
      <rect x={mid.x - 26} y={mid.y - 8} width={52} height={16} fill="var(--paper)" stroke="none" />
      <text x={mid.x} y={mid.y + 3.8} textAnchor="middle" fill="var(--ink)" stroke="none" fontSize={10.5} fontFamily="var(--font-mono)">
        {d.label}
      </text>
    </g>
  );
}

/**
 * Slotted, collision-free monochrome subsystem callout for embedded Ortho sheets:
 * 3 top-rail slots + 3 bottom-rail slots across Section Front View, following
 * docs/drawing-standard.md §3 Rules 2 & 3 (dashed leader, terminal dot, mono tag).
 */
function SheetCallout({
  layout,
  lm,
  unit,
  active,
  onSelect,
  onHover,
}: {
  layout: DrawingLayout;
  lm: PrimaryLandmark;
  unit: number;
  active: boolean;
  onSelect: () => void;
  onHover: (hovering: boolean) => void;
}) {
  const front = layout.views.find((v) => v.id === 'front')!.rect;
  const leftView = layout.views.find((v) => v.id === 'left')!.rect;
  const pt = new THREE.Vector3(lm.anchor[0] * unit, lm.anchor[1] * unit, lm.anchor[2] * unit);
  const anchor = project(layout, 'front', pt);

  // Span callout rail from left margin up to just before Left View / Isometric so 3 pills never overlap
  const spanLeft = Math.max(12, front.x - 58);
  const spanRight = Math.max(spanLeft + 360, Math.min(leftView.x - 10, front.x + front.w + 64));
  const spanW = spanRight - spanLeft;
  const pillW = Math.min(148, Math.floor((spanW - 20) / 3));
  const pillH = 19;
  const step = (spanW - pillW) / 2;
  const slotX = spanLeft + pillW / 2 + lm.slot * step;
  const railY = lm.rail === 'top' ? Math.max(25, front.y - 18) : front.y + front.h + 24;
  const elbowX = anchor.x + Math.sign(slotX - anchor.x) * Math.min(22, Math.abs(slotX - anchor.x) * 0.45);
  const stroke = active ? 'var(--rust)' : 'var(--hair-strong)';
  const numStr = String(lm.index).padStart(2, '0');

  return (
    <g
      className={`sheet-callout${active ? ' is-active' : ''}`}
      data-testid={`ortho-callout-${lm.partId}`}
      onClick={onSelect}
      onPointerEnter={() => onHover(true)}
      onPointerLeave={() => onHover(false)}
      style={{ pointerEvents: 'auto', cursor: 'pointer' }}
    >
      <polyline
        points={`${anchor.x},${anchor.y} ${elbowX},${railY} ${slotX},${railY}`}
        fill="none"
        stroke={stroke}
        strokeWidth={0.95}
        strokeDasharray="2.5 2"
      />
      <circle cx={anchor.x} cy={anchor.y} r={2.2} fill={active ? 'var(--rust)' : 'var(--ink)'} />
      <rect
        x={slotX - pillW / 2}
        y={railY - pillH / 2}
        width={pillW}
        height={pillH}
        rx={2}
        fill="var(--paper-hi)"
        stroke={stroke}
        strokeWidth={1}
      />
      <text
        x={slotX - pillW / 2 + 6}
        y={railY + 3.4}
        fill={active ? 'var(--rust)' : 'var(--ink-3)'}
        fontSize={9}
        fontWeight={600}
        fontFamily="var(--font-mono)"
      >
        {numStr}
      </text>
      <text
        x={slotX - pillW / 2 + 23}
        y={railY + 3.4}
        fill="var(--ink)"
        fontSize={9}
        fontFamily="var(--font-mono)"
      >
        {lm.short}
      </text>
      <title>{`${numStr} ${lm.short} → ${lm.counterpart}`}</title>
    </g>
  );
}

/** Full-studio BOM balloon (used only in standalone un-embedded /inkwork/ mode). */
function Balloon({ layout, b, index, name, explode, stage, unit }: {
  layout: DrawingLayout;
  b: BomCallout;
  index: number;
  name: string;
  explode: [number, number, number];
  stage: [number, number];
  unit: number;
}) {
  const front = layout.views.find((v) => v.id === 'front')!.rect;
  const top = layout.views.find((v) => v.id === 'top')!.rect;
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
  const [edx] = b.elbowOffset ?? [20, rail === 'top' ? -40 : 46];
  const elbowX = anchor.x + edx;
  const bx = elbowX + (edx >= 0 ? 26 : -26);
  return (
    <g className="balloon" stroke="var(--hair-strong)" fill="none" opacity={0.92}>
      <polyline points={`${anchor.x},${anchor.y} ${elbowX},${railY} ${bx},${railY}`} fill="none" strokeWidth={1} strokeDasharray="2.5 2" />
      <circle cx={anchor.x} cy={anchor.y} r={2.2} fill="var(--ink)" stroke="none" />
      <circle cx={bx} cy={railY} r={10} strokeWidth={1.1} fill="var(--paper)" />
      <text x={bx} y={railY + 3.6} textAnchor="middle" fill="var(--ink)" stroke="none" fontSize={10} fontFamily="var(--font-mono)">{String(index).padStart(2, '0')}</text>
      <title>{[b.code, name, b.title, b.material].filter(Boolean).join(' · ')}</title>
    </g>
  );
}

/** Labels, slotted subsystem callouts, dimensions, projection lines, and ISO title block. */
export function DrawingSheet() {
  const machine = useMachine();
  const { layout, box } = useDrawing();
  const projection = useStudio((s) => s.projection);
  const section = useStudio((s) => s.section);
  const labels = useStudio((s) => s.labels);
  const selected = useStudio((s) => s.selected);
  const hovered = useStudio((s) => s.hovered);
  const set = useStudio((s) => s.set);
  if (!layout) return null;

  const focus = hovered ?? selected;
  const part = focus ? machine.parts.find((p) => p.id === focus) : undefined;
  const tb = layout.titleBlock;
  const landmarks = isEmbed ? (MACHINE_LANDMARKS[machine.id] ?? []) : [];
  const showStudioBalloons = !isEmbed && labels && layout.views[0].rect.w > 480;

  const dims = (() => {
    const all = machine.dimensions ?? [];
    if (!isEmbed) return all;
    const overallFront = all.find((d) => d.view === 'front');
    const overallLeft = all.find((d) => d.view === 'left' && d.offset >= 100) ?? all.find((d) => d.view === 'left');
    // Place overall length cleanly beneath Top View so the Front↔Top gap stays 100% dedicated to bottom-rail callouts
    const zBot = layout.bounds.max.z;
    const topLength: DimensionDef | null = overallFront
      ? {
          from: [overallFront.from[0], 0, zBot],
          to: [overallFront.to[0], 0, zBot],
          view: 'top',
          label: `${overallFront.label} mm`,
          offset: 16,
        }
      : null;
    const leftWidth: DimensionDef | null = overallLeft
      ? { ...overallLeft, label: `${overallLeft.label} mm`, offset: 20 }
      : null;
    return [topLength, leftWidth].filter((d): d is DimensionDef => d !== null);
  })();

  return (
    <div className="sheet" aria-hidden="true">
      <svg className="sheet-svg">
        <CentreCrosses layout={layout} lines={machine.centreLines} />
        {projection && box && <ProjectionLines layout={layout} box={box} />}
        {dims.map((d, i) => <Dim key={i} layout={layout} d={d} />)}
        {landmarks.map((lm) => (
          <SheetCallout
            key={lm.partId}
            layout={layout}
            lm={lm}
            unit={machine.unit ?? 1}
            active={focus === lm.partId}
            onSelect={() => set({ selected: selected === lm.partId ? null : lm.partId })}
            onHover={(h) => set({ hovered: h ? lm.partId : null })}
          />
        ))}
        {showStudioBalloons && machine.bom?.map((b) => {
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
      {layout.views.map((v) => {
        let style: React.CSSProperties;
        if (isEmbed) {
          if (v.id === 'front') style = { left: v.rect.x, top: 6, transform: 'none' };
          else if (v.id === 'left') style = { left: v.rect.x + v.rect.w / 2, top: 6 };
          else if (v.id === 'iso') style = { left: v.rect.x + v.rect.w / 2, top: Math.max(8, v.rect.y - 15) };
          else style = { left: v.rect.x + v.rect.w / 2, top: v.rect.y + v.rect.h + 31 };
        } else {
          style = { left: v.rect.x + v.rect.w / 2, top: v.rect.y + v.rect.h + 4 };
        }
        return (
          <span key={v.id} className={`sheet-label sheet-label--${v.id}`} style={style}>
            {v.id === 'front' && section ? 'Section Front View' : v.label}
          </span>
        );
      })}
      {!isEmbed && part && (
        <span className="sheet-focus" style={{ left: layout.views[0].rect.x, top: layout.views[0].rect.y - 26 }}>
          {String(part.index).padStart(2, '0')} {part.name}
        </span>
      )}
      <table className="sheet-title" data-testid="ortho-title-block" style={{ left: tb.x, top: tb.y, width: tb.w }}>
        <tbody>
          {isEmbed ? (
            <>
              <tr>
                <td className="sheet-title-name">{machine.name}</td>
                <td>Scale {machine.scale}</td>
              </tr>
              <tr>
                <td>{machine.parts.length} parts · 1st Angle</td>
                <td>Dwg {machine.drawingNo}</td>
              </tr>
            </>
          ) : (
            <>
              <tr>
                <td rowSpan={2} className="sheet-title-name">{machine.name}</td>
                <td>Scale</td><td>{machine.scale}</td>
              </tr>
              <tr>
                <td>Dwg</td><td>{machine.drawingNo}</td>
              </tr>
              <tr>
                <td>{machine.parts.length} parts · 1st Angle</td><td>Unit</td><td>mm</td>
              </tr>
            </>
          )}
        </tbody>
      </table>
    </div>
  );
}
