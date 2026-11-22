# CONDUIT Shared UI Components

All app-owned UI lives in **one** shared file — `site/src/parts.tsx` — plus one icon file,
`site/src/icons.tsx`. There is no `src/components/` directory: the whole component library is
these two files. Styling is a `ch-`-prefixed CSS layer in `site/src/site.css` (see
`theme.md` for tokens and the section index).

Component inventory:

| Component | File | Role |
|---|---|---|
| `StatTile` | `site/src/parts.tsx` | Metric tile — big number + label + hint + tone |
| `Field` | `site/src/parts.tsx` | Definition-list row (dt/dd) |
| `DetailsRow` | `site/src/parts.tsx` | Disclosure row with status dot, key, value, meta, chevron |
| `ScaleCompare` | `site/src/parts.tsx` | Log-scale horizontal bar comparison |
| `ArchitectureDiagram` | `site/src/parts.tsx` | Tiered trust-boundary diagram (ingress → kernel → renderers) |
| `ProofDag` | `site/src/parts.tsx` | Interactive SVG proof-obligation dependency graph |
| `Source` | `site/src/parts.tsx` | Monospace source link |
| `Icon*` (8) | `site/src/icons.tsx` | 16×16 stroked icon set |
| `ClickUIProvider`, `Switch`, `Badge`, `Button` | `@clickhouse/click-ui` | Theme provider + a few controls |

---

## `site/src/parts.tsx` — FULL SOURCE

```tsx
import React, { useState } from 'react';
import { IconArrowDown, IconArrowRight, IconCheck, IconChevron, IconShieldAlert, IconX } from './icons';
import type { ProofDagEdge, ProofDagNode } from './content/vurl';

export type Tone = 'proved' | 'warn' | 'fail' | 'neutral';

export const StatTile: React.FC<{
  value: string;
  label: string;
  hint?: string;
  tone?: Tone;
  testId?: string;
}> = ({ value, label, hint, tone = 'neutral', testId }) => (
  <div className="ch-metric-tile" data-tone={tone}>
    <div className="ch-metric-top">
      <div className="ch-metric-value" data-tone={tone} data-testid={testId ?? `stat-${label}`}>
        {value}
      </div>
      {tone === 'proved' && <IconCheck size={15} className="ch-metric-icon" />}
      {tone === 'fail' && <IconX size={15} className="ch-metric-icon" />}
      {tone === 'warn' && <IconShieldAlert size={15} className="ch-metric-icon" />}
    </div>
    <div className="ch-metric-label">{label}</div>
    {hint && <div className="ch-metric-hint">{hint}</div>}
  </div>
);

export const Field: React.FC<{ label: string; children: React.ReactNode }> = ({ label, children }) => (
  <div className="ch-field">
    <dt>{label}</dt>
    <dd>{children}</dd>
  </div>
);

export const DetailsRow: React.FC<{
  k: string;
  v: string;
  meta?: string;
  tone?: Tone;
  open?: boolean;
  children: React.ReactNode;
}> = ({ k, v, meta, tone = 'neutral', open = false, children }) => (
  <details className="ch-det" data-tone={tone} open={open}>
    <summary className="ch-det-summary">
      <span className="ch-det-dot" data-tone={tone} aria-hidden="true" />
      <span className="ch-det-k">{k}</span>
      <span className="ch-det-v">{v}</span>
      {meta && <span className="ch-det-meta">{meta}</span>}
      <IconChevron size={14} className="ch-det-chev" />
    </summary>
    <div className="ch-det-body">
      <dl className="ch-fields">{children}</dl>
    </div>
  </details>
);

export const ScaleCompare: React.FC<{
  items: Array<{
    id: string;
    label: string;
    lines: number;
    display: string;
    tone: Tone;
    note: string;
  }>;
}> = ({ items }) => {
  const maxLog = Math.max(...items.map((i) => Math.log10(Math.max(i.lines, 1))));
  return (
    <div className="ch-scale" data-testid="scale-compare">
      {items.map((item) => (
        <div key={item.id} className="ch-scale-row">
          <div className="ch-scale-label">
            <span>{item.label}</span>
            <strong data-testid={`scale-${item.id}`}>{item.display}</strong>
          </div>
          <div className="ch-scale-track">
            <div
              className="ch-scale-bar"
              data-tone={item.tone}
              style={{ width: `${(Math.log10(Math.max(item.lines, 1)) / maxLog) * 100}%` }}
            />
          </div>
          <div className="ch-scale-note">{item.note}</div>
        </div>
      ))}
      <div className="ch-scale-axis">Logarithmic scale — each major step represents 10× more source code.</div>
    </div>
  );
};

export const ArchitectureDiagram: React.FC = () => (
  <div className="ch-arch-diagram" data-testid="shim-diagram" aria-label="Verified kernel and sandboxed renderer architecture">
    {/* Tier 1: Network Ingress */}
    <div className="ch-tier">
      <div className="ch-tier-head">Ingress · Transport &amp; Certificate Boundary</div>
      <div className="ch-ingress-row">
        <div className="ch-node" data-trust="untrusted">
          <div className="ch-node-title">Network Transport</div>
          <div className="ch-node-sub">rustls sockets · untrusted I/O</div>
        </div>
        <span className="ch-flow-arrow" aria-hidden="true">
          <IconArrowRight size={15} />
        </span>
        <div className="ch-node" data-trust="verified">
          <div className="ch-node-title">X.509 Path Validation</div>
          <div className="ch-node-sub">Verdict policy · proved in Verus</div>
        </div>
      </div>
    </div>

    <div className="ch-tier-connector" aria-hidden="true">
      <IconArrowDown size={15} />
      <span>validated bytes enter kernel</span>
    </div>

    {/* Tier 2: Verified Security Kernel */}
    <div className="ch-kernel-shell">
      <div className="ch-kernel-head">
        <span>VERIFIED SECURITY KERNEL (Verus)</span>
        <span className="ch-kernel-tag">Owns every security decision</span>
      </div>
      <div className="ch-kernel-grid">
        <div className="ch-node" data-trust="verified">
          <div className="ch-node-title">Network Parsers</div>
          <div className="ch-node-sub">vurl (proved) · HTTP · MIME · Cookie</div>
        </div>
        <div className="ch-node" data-trust="verified">
          <div className="ch-node-title">Origin &amp; Policy</div>
          <div className="ch-node-sub">SOP · CSP · CORS · Mixed content</div>
        </div>
        <div className="ch-node" data-trust="verified">
          <div className="ch-node-title">Kernel &amp; Chrome</div>
          <div className="ch-node-sub">Tabs · Cap handles · Address bar</div>
        </div>
      </div>
      <div className="ch-kernel-foot">
        <span>Composited frames &amp; input events route through display output only from the kernel.</span>
      </div>
    </div>

    {/* IPC Capability Boundary */}
    <div className="ch-ipc-rail">
      <IconArrowDown size={14} />
      <span>Typed Vest-encoded IPC — capability handles only, zero ambient authority</span>
      <IconArrowDown size={14} />
    </div>

    {/* Tier 3: Per-Site Sandboxed Renderers */}
    <div className="ch-renderers-grid">
      {[
        { title: 'Renderer · Origin A', detail: 'vjs (J0–J7 proved) + vjs_webidl + vwasm; unverified html5ever, Stylo, per-site GPU' },
        { title: 'Renderer · Origin B', detail: 'Isolated Nanvix / OS sandbox — cannot open sockets, read cross-site cookies, or forge handles' },
        { title: 'Renderer · Origin N', detail: 'Per-site GPU translation & rasterization confines Dawn/Skia/ANGLE flaws to a single origin' },
      ].map((r) => (
        <div key={r.title} className="ch-node" data-trust="untrusted">
          <div className="ch-node-title">{r.title}</div>
          <div className="ch-node-sub">{r.detail}</div>
        </div>
      ))}
    </div>

    <p className="ch-arch-caption">
      <strong>Target isolation theorem:</strong> A compromised renderer can misrender only its own
      origin. It cannot exfiltrate cross-origin cookies, forge kernel capabilities, or spoof the
      address bar—making the browser usable while verified components replace unverified layers one
      crate at a time.
    </p>
  </div>
);

export const ProofDag: React.FC<{
  nodes: ProofDagNode[];
  edges: ProofDagEdge[];
  verified: boolean;
}> = ({ nodes, edges, verified }) => {
  const [selectedId, setSelectedId] = useState<string | null>('spec_encode');

  const nodeW = 248;
  const nodeH = 44;
  const colX = [24, 412];
  const rowPitch = 58;
  const topPad = 40;
  const maxRow = Math.max(...nodes.map((n) => n.row));
  const svgW = colX[1] + nodeW + 24;
  const svgH = Math.ceil(topPad + (maxRow + 1) * rowPitch + 20);

  const pos = new Map<string, { x: number; y: number }>();
  for (const n of nodes) {
    pos.set(n.id, { x: colX[n.layer], y: topPad + n.row * rowPitch });
  }

  const upstream = new Set<string>();
  const downstream = new Set<string>();
  if (selectedId) {
    for (const e of edges) {
      if (e.to === selectedId) upstream.add(e.from);
      if (e.from === selectedId) downstream.add(e.to);
    }
  }

  const selectedNode = nodes.find((n) => n.id === selectedId) ?? null;

  return (
    <div className="ch-dag-wrap" data-testid="vurl-dag">
      <div className="ch-dag-bar">
        <span data-testid="dag-summary">
          <strong>{nodes.length} obligations</strong> · {edges.length} dependency edges
        </span>
        <span className="ch-dag-status" data-tone={verified ? 'proved' : 'fail'}>
          {verified ? 'All verified (0 errors)' : 'A proof, trust, or test check failed'}
        </span>
      </div>

      <div className="ch-dag-canvas">
        <svg
          viewBox={`0 0 ${svgW} ${svgH}`}
          className="ch-dag-svg"
          role="img"
          aria-label="vurl proof obligation dependency graph"
        >
          <text x={colX[0]} y={22} className="ch-dag-colhead">
            SPECS &amp; VERIFIED PRIMITIVES
          </text>
          <text x={colX[1]} y={22} className="ch-dag-colhead">
            IMPLEMENTATIONS &amp; THEOREMS
          </text>

          {/* Edges */}
          {edges.map((e) => {
            const a = pos.get(e.from);
            const b = pos.get(e.to);
            if (!a || !b) return null;
            const x1 = a.x + nodeW;
            const y1 = a.y + nodeH / 2;
            const x2 = b.x;
            const y2 = b.y + nodeH / 2;
            const mx = (x1 + x2) / 2;
            const active =
              !selectedId || e.from === selectedId || e.to === selectedId;
            return (
              <path
                key={`${e.from}-${e.to}`}
                d={`M ${x1} ${y1} C ${mx} ${y1}, ${mx} ${y2}, ${x2} ${y2}`}
                className="ch-dag-edge"
                data-active={active}
                data-tone={verified ? 'proved' : 'fail'}
              />
            );
          })}

          {/* Nodes */}
          {nodes.map((n) => {
            const p = pos.get(n.id)!;
            const isSelected = n.id === selectedId;
            const isRelated = upstream.has(n.id) || downstream.has(n.id);
            const dimmed = !!selectedId && !isSelected && !isRelated;
            return (
              <g
                key={n.id}
                transform={`translate(${p.x}, ${p.y})`}
                className="ch-dag-node"
                data-testid={`dag-node-${n.id}`}
                data-selected={isSelected}
                data-related={isRelated}
                data-dimmed={dimmed}
                data-tone={verified ? 'proved' : 'fail'}
                role="button"
                tabIndex={0}
                aria-pressed={isSelected}
                onClick={() => setSelectedId((prev) => (prev === n.id ? null : n.id))}
                onKeyDown={(ev) => {
                  if (ev.key === 'Enter' || ev.key === ' ') {
                    ev.preventDefault();
                    setSelectedId((prev) => (prev === n.id ? null : n.id));
                  }
                }}
              >
                <rect width={nodeW} height={nodeH} rx={4} className="ch-dag-rect" />
                <circle cx={14} cy={nodeH / 2} r={3.5} className="ch-dag-dot" />
                <text x={26} y={19} className="ch-dag-title">
                  {n.label}
                </text>
                <text x={26} y={34} className="ch-dag-sub">
                  {n.subsystem}
                </text>
              </g>
            );
          })}
        </svg>
      </div>

      <div className="ch-dag-inspector" data-testid="dag-inspector">
        {selectedNode ? (
          <span>
            <code>{selectedNode.label}</code> ({selectedNode.subsystem}) ·{' '}
            {upstream.size > 0
              ? `depends on ${Array.from(upstream).join(', ')}`
              : 'root specification / primitive'}{' '}
            ·{' '}
            {downstream.size > 0
              ? `verified dependents: ${Array.from(downstream).join(', ')}`
              : 'leaf proved theorem / implementation'}
          </span>
        ) : (
          <span>Select any node to trace upstream specifications and downstream proof obligations.</span>
        )}
      </div>
    </div>
  );
};

export const Source: React.FC<{ href: string; children: React.ReactNode }> = ({ href, children }) => (
  <a className="ch-mono-link" href={href} target="_blank" rel="noreferrer">
    {children}
  </a>
);
```

---

## `site/src/icons.tsx` — FULL SOURCE

16×16 viewBox, `fill: none`, `stroke: currentColor`, `stroke-width: 1.6`, round caps/joins.
All icons inherit `currentColor`, so they take the tone color of their container.

```tsx
import React from 'react';

interface IconProps {
  size?: number;
  className?: string;
}

const base = (size: number, className?: string) => ({
  width: size,
  height: size,
  viewBox: '0 0 16 16',
  fill: 'none',
  stroke: 'currentColor',
  strokeWidth: 1.6,
  strokeLinecap: 'round' as const,
  strokeLinejoin: 'round' as const,
  'aria-hidden': true as const,
  className,
});

export const IconCheck: React.FC<IconProps> = ({ size = 14, className }) => (
  <svg {...base(size, className)}>
    <circle cx="8" cy="8" r="6.25" />
    <path d="M5.2 8.2 7.1 10.1 11 6.1" />
  </svg>
);

export const IconX: React.FC<IconProps> = ({ size = 14, className }) => (
  <svg {...base(size, className)}>
    <circle cx="8" cy="8" r="6.25" />
    <path d="M5.7 5.7 10.3 10.3M10.3 5.7 5.7 10.3" />
  </svg>
);

export const IconClock: React.FC<IconProps> = ({ size = 14, className }) => (
  <svg {...base(size, className)}>
    <circle cx="8" cy="8" r="6.25" />
    <path d="M8 4.7V8l2.4 1.5" />
  </svg>
);

export const IconShieldAlert: React.FC<IconProps> = ({ size = 14, className }) => (
  <svg {...base(size, className)}>
    <path d="M8 1.8 13.5 4v3.8c0 3.2-2.2 5.4-5.5 6.4C4.7 13.2 2.5 11 2.5 7.8V4L8 1.8Z" />
    <path d="M8 5.4v3.2M8 11.1h.01" />
  </svg>
);

export const IconCopy: React.FC<IconProps> = ({ size = 13, className }) => (
  <svg {...base(size, className)}>
    <rect x="5.5" y="5.5" width="8" height="8" rx="1.5" />
    <path d="M10.5 5.5V3.8A1.3 1.3 0 0 0 9.2 2.5H3.8A1.3 1.3 0 0 0 2.5 3.8v5.4a1.3 1.3 0 0 0 1.3 1.3h1.7" />
  </svg>
);

export const IconExternal: React.FC<IconProps> = ({ size = 12, className }) => (
  <svg {...base(size, className)}>
    <path d="M6.5 3.5H3.5a1 1 0 0 0-1 1v8a1 1 0 0 0 1 1h8a1 1 0 0 0 1-1v-3" />
    <path d="M9.2 2.5h4.3v4.3M13.5 2.5 7.5 8.5" />
  </svg>
);

export const IconChevron: React.FC<IconProps> = ({ size = 14, className }) => (
  <svg {...base(size, className)}>
    <path d="M6 4.2 10 8l-4 3.8" />
  </svg>
);

export const IconArrowDown: React.FC<IconProps> = ({ size = 14, className }) => (
  <svg {...base(size, className)}>
    <path d="M8 2.5v10.5M4.5 9.5 8 13l3.5-3.5" />
  </svg>
);

export const IconArrowRight: React.FC<IconProps> = ({ size = 14, className }) => (
  <svg {...base(size, className)}>
    <path d="M2.5 8h10.5M9.5 4.5 13 8l-3.5 3.5" />
  </svg>
);
```

---

## CSS for the shared primitives

Extracted from `site/src/site.css`. Line numbers given for targeted `--context-file` ranges.

### StatTile — `site.css:642-712`

```css
.ch-metrics-grid {
  display: grid;
  grid-template-columns: repeat(4, minmax(0, 1fr));
  gap: 12px;
}

.ch-metric-tile {
  padding: 12px 16px;
  background: var(--ch-bg-card);
  border: 1px solid var(--ch-border-subtle);
  border-radius: 4px;
  display: flex;
  flex-direction: column;
  justify-content: center;
}

.ch-metric-tile[data-tone='proved'] {
  border-color: var(--ch-status-proved-bdr);
}

.ch-metric-tile[data-tone='fail'] {
  border-color: var(--ch-status-fail-bdr);
}

.ch-metric-top {
  display: flex;
  align-items: center;
  justify-content: space-between;
  gap: 8px;
}

.ch-metric-value {
  font-family: var(--ch-font-mono);
  font-size: 24px;
  font-weight: 700;
  font-variant-numeric: tabular-nums;
  line-height: 1.1;
  color: var(--ch-text-primary);
}

.ch-metric-value[data-tone='proved'] {
  color: var(--ch-status-proved);
}

.ch-metric-value[data-tone='fail'] {
  color: var(--ch-status-fail);
}

.ch-metric-tile[data-tone='proved'] .ch-metric-icon {
  color: var(--ch-status-proved);
}

.ch-metric-tile[data-tone='fail'] .ch-metric-icon {
  color: var(--ch-status-fail);
}

.ch-metric-label {
  margin-top: 5px;
  font-family: var(--ch-font-mono);
  font-size: 10.5px;
  letter-spacing: 0.06em;
  text-transform: uppercase;
  color: var(--ch-text-muted);
}

.ch-metric-hint {
  margin-top: 3px;
  font-size: 11.5px;
  color: var(--ch-text-muted);
}
```

### Digest pill — `site.css:713-762`

```css
.ch-digest-stack {
  display: flex;
  flex-direction: column;
  justify-content: center;
  gap: 8px;
}

.ch-digest-pill {
  display: flex;
  align-items: center;
  justify-content: space-between;
  gap: 10px;
  width: 100%;
  min-height: 36px;
  padding: 6px 12px;
  font-family: var(--ch-font-mono);
  font-size: 11.5px;
  background: var(--ch-bg-card);
  border: 1px solid var(--ch-border-subtle);
  border-radius: 4px;
  color: var(--ch-text-primary);
  white-space: nowrap;
  cursor: pointer;
  transition: border-color 120ms ease, background-color 120ms ease;
}

.ch-digest-pill:hover {
  border-color: var(--ch-border-strong);
  background: var(--ch-bg-card-hover);
}

.ch-digest-left {
  display: inline-flex;
  align-items: center;
  gap: 8px;
  min-width: 0;
  overflow: hidden;
  text-overflow: ellipsis;
}

.ch-digest-meta {
  display: inline-flex;
  align-items: center;
  gap: 6px;
  padding-left: 10px;
  border-left: 1px solid var(--ch-border-subtle);
  color: var(--ch-text-muted);
  white-space: nowrap;
}
```

### Field / DetailsRow — `site.css:1560-1679`

```css
.ch-accordion-group {
  display: flex;
  flex-direction: column;
  gap: 8px;
}

.ch-det {
  background: var(--ch-bg-card);
  border: 1px solid var(--ch-border-subtle);
  border-radius: 4px;
}

.ch-det[open] {
  border-color: var(--ch-border-strong);
}

.ch-det-summary {
  display: flex;
  align-items: center;
  gap: 10px;
  padding: 10px 14px;
  cursor: pointer;
  list-style: none;
  font-size: 13.5px;
  font-weight: 500;
  color: var(--ch-text-primary);
}

.ch-det-summary::-webkit-details-marker {
  display: none;
}

.ch-det-summary:hover {
  background: var(--ch-bg-card-hover);
}

.ch-det-dot {
  width: 7px;
  height: 7px;
  border-radius: 50%;
  background: var(--ch-text-muted);
  flex-shrink: 0;
}

.ch-det-dot[data-tone='proved'] { background: var(--ch-status-proved); }
.ch-det-dot[data-tone='warn']   { background: var(--ch-status-warn); }
.ch-det-dot[data-tone='fail']   { background: var(--ch-status-fail); }

.ch-det-k {
  font-family: var(--ch-font-mono);
  font-size: 12px;
  font-weight: 700;
  color: var(--ch-accent-text);
  flex-shrink: 0;
}

.ch-det-v {
  flex: 1 1 auto;
  min-width: 0;
  color: var(--ch-text-primary);
}

.ch-det-meta {
  font-family: var(--ch-font-mono);
  font-size: 11.5px;
  color: var(--ch-text-muted);
  white-space: nowrap;
}

.ch-det-chev {
  color: var(--ch-text-muted);
  flex-shrink: 0;
  transition: transform 140ms ease;
}

.ch-det[open] .ch-det-chev {
  transform: rotate(90deg);
}

.ch-det-body {
  padding: 10px 14px 14px;
  border-top: 1px solid var(--ch-border-subtle);
}

.ch-fields { margin: 0; }

.ch-field { padding: 7px 0; }

.ch-field + .ch-field {
  border-top: 1px solid var(--ch-border-subtle);
}

.ch-field dt {
  font-family: var(--ch-font-mono);
  font-size: 10.5px;
  font-weight: 600;
  text-transform: uppercase;
  letter-spacing: 0.06em;
  color: var(--ch-text-muted);
}

.ch-field dd {
  margin: 4px 0 0;
  font-size: 13.5px;
  line-height: 1.58;
  color: var(--ch-text-secondary);
}
```

### ScaleCompare — `site.css:1502-1558`

```css
.ch-scale {
  display: flex;
  flex-direction: column;
  gap: 14px;
  padding: 16px;
  background: var(--ch-bg-card);
  border: 1px solid var(--ch-border-subtle);
  border-radius: 4px;
}

.ch-scale-label {
  display: flex;
  justify-content: space-between;
  gap: 10px;
  font-size: 13px;
  margin-bottom: 5px;
  color: var(--ch-text-primary);
}

.ch-scale-label strong {
  font-family: var(--ch-font-mono);
  font-variant-numeric: tabular-nums;
}

.ch-scale-track {
  height: 12px;
  background: var(--ch-bg-code);
  border: 1px solid var(--ch-border-subtle);
  border-radius: 3px;
  overflow: hidden;
}

.ch-scale-bar {
  height: 100%;
  min-width: 4px;
  background: var(--ch-accent);
}

.ch-scale-bar[data-tone='proved'] { background: var(--ch-status-proved); }
.ch-scale-bar[data-tone='fail']   { background: var(--ch-status-fail); }

.ch-scale-note {
  margin-top: 4px;
  font-size: 12px;
  color: var(--ch-text-muted);
}

.ch-scale-axis {
  font-size: 11.5px;
  color: var(--ch-text-muted);
  font-style: italic;
}
```

### Filter bar / tab bar / state selector buttons — `site.css:1058-1099, 1104-1201`

```css
.ch-filter-bar {
  display: flex;
  flex-wrap: wrap;
  gap: 8px;
}

.ch-filter-btn {
  display: inline-flex;
  align-items: center;
  gap: 8px;
  padding: 7px 12px;
  background: var(--ch-bg-card);
  border: 1px solid var(--ch-border-subtle);
  border-radius: 4px;
  color: var(--ch-text-secondary);
  font-family: var(--ch-font-sans);
  font-size: 12.5px;
  font-weight: 600;
  cursor: pointer;
  transition: border-color 120ms ease, background-color 120ms ease, color 120ms ease;
}

.ch-filter-btn:hover {
  background: var(--ch-bg-card-hover);
  color: var(--ch-text-primary);
}

.ch-filter-btn[data-active='true'] {
  background: var(--ch-accent-dim);
  border-color: var(--ch-accent-bdr);
  color: var(--ch-text-primary);
}

.ch-filter-count {
  font-family: var(--ch-font-mono);
  font-size: 11px;
  color: var(--ch-text-muted);
}

.ch-filter-btn[data-active='true'] .ch-filter-count {
  color: var(--ch-accent-text);
}

.ch-state-selector {
  display: grid;
  grid-template-columns: 1fr 1fr;
  gap: 8px;
}

.ch-state-btn {
  display: flex;
  flex-direction: column;
  align-items: flex-start;
  gap: 4px;
  padding: 10px 12px;
  background: var(--ch-bg-card);
  border: 1px solid var(--ch-border-subtle);
  border-radius: 4px;
  color: var(--ch-text-primary);
  cursor: pointer;
  text-align: left;
  transition: border-color 120ms ease, background-color 120ms ease;
}

.ch-state-btn:hover { background: var(--ch-bg-card-hover); }

.ch-state-btn[data-active='true'][data-tone='proved'] {
  border-color: var(--ch-status-proved-bdr);
  background: var(--ch-status-proved-dim);
}
.ch-state-btn[data-active='true'][data-tone='fail'] {
  border-color: var(--ch-status-fail-bdr);
  background: var(--ch-status-fail-dim);
}
.ch-state-btn[data-active='true'][data-tone='warn'] {
  border-color: var(--ch-status-warn-bdr);
  background: var(--ch-status-warn-dim);
}

.ch-state-title {
  display: inline-flex;
  align-items: center;
  gap: 6px;
  font-family: var(--ch-font-mono);
  font-size: 12px;
  font-weight: 700;
}

.ch-state-title[data-tone='proved'] { color: var(--ch-status-proved); }
.ch-state-title[data-tone='fail']   { color: var(--ch-status-fail); }
.ch-state-title[data-tone='warn']   { color: var(--ch-status-warn); }

.ch-state-summary {
  font-size: 11.5px;
  line-height: 1.45;
  color: var(--ch-text-muted);
}

.ch-workbench-tabs {
  display: flex;
  gap: 8px;
}

.ch-tab-btn {
  padding: 8px 14px;
  background: var(--ch-bg-card);
  border: 1px solid var(--ch-border-subtle);
  border-radius: 4px;
  font-family: var(--ch-font-mono);
  font-size: 12px;
  font-weight: 600;
  color: var(--ch-text-secondary);
  cursor: pointer;
}

.ch-tab-btn:hover {
  background: var(--ch-bg-card-hover);
  color: var(--ch-text-primary);
}

.ch-tab-btn[data-active='true'] {
  border-color: var(--ch-accent-bdr);
  background: var(--ch-accent-dim);
  color: var(--ch-text-primary);
}
```

### Code workbench + Z3 inlay — `site.css:1228-1414`

```css
.ch-code-workbench {
  background: var(--ch-bg-code);
  border: 1px solid var(--ch-border-subtle);
  border-radius: 4px;
  overflow: hidden;
  font-family: var(--ch-font-mono);
}

.ch-code-header {
  display: flex;
  flex-wrap: wrap;
  align-items: center;
  justify-content: space-between;
  gap: 12px;
  padding: 9px 14px;
  background: var(--ch-bg-card);
  border-bottom: 1px solid var(--ch-border-subtle);
  font-size: 11.5px;
  color: var(--ch-text-secondary);
}

.ch-code-lines {
  padding: 8px 0;
  max-height: 540px;
  overflow-y: auto;
}

.ch-code-row {
  display: grid;
  grid-template-columns: 36px 24px 54px minmax(0, 1fr);
  align-items: baseline;
  padding: 2px 14px;
  line-height: 23px;
  font-size: 12.5px;
}

.ch-code-row[data-clickable='true'] { cursor: pointer; }
.ch-code-row[data-clickable='true']:hover { background: var(--ch-bg-card-hover); }

.ch-code-row[data-state='proved'] { background: var(--ch-status-proved-dim); }
.ch-code-row[data-state='fail']   { background: var(--ch-status-fail-dim); }
.ch-code-row[data-state='warn']   { background: var(--ch-status-warn-dim); }

.ch-lineno {
  color: var(--ch-text-muted);
  text-align: right;
  padding-right: 12px;
  font-size: 11px;
  user-select: none;
}

.ch-glyph { display: inline-flex; align-items: center; justify-content: center; user-select: none; }
.ch-glyph[data-tone='proved'] { color: var(--ch-status-proved); }
.ch-glyph[data-tone='fail']   { color: var(--ch-status-fail); }
.ch-glyph[data-tone='warn']   { color: var(--ch-status-warn); }

.ch-lane-pill {
  display: inline-block;
  font-size: 9.5px;
  text-transform: uppercase;
  padding: 0 5px;
  margin-right: 10px;
  border-radius: 3px;
  line-height: 17px;
  text-align: center;
  border: 1px solid var(--ch-border-subtle);
  color: var(--ch-text-muted);
}

.ch-lane-pill[data-lane='spec'] {
  color: var(--ch-accent-text);
  border-color: var(--ch-accent-bdr);
}

.ch-lane-pill[data-lane='proof'] {
  color: var(--ch-status-proved);
  border-color: var(--ch-status-proved-bdr);
}

.ch-code-text {
  white-space: pre-wrap;
  word-break: break-word;
  color: var(--ch-text-primary);
}

.ch-z3-inlay {
  grid-column: 1 / -1;
  margin: 6px 0 8px 36px;
  padding: 12px 14px;
  background: var(--ch-bg-card);
  border: 1px solid var(--ch-border-strong);
  border-radius: 4px;
  font-family: var(--ch-font-sans);
  font-size: 13px;
  line-height: 1.55;
}

.ch-z3-inlay[data-tone='proved'] { border-color: var(--ch-status-proved-bdr); }
.ch-z3-inlay[data-tone='fail']   { border-color: var(--ch-status-fail-bdr); }
.ch-z3-inlay[data-tone='warn']   { border-color: var(--ch-status-warn-bdr); }

.ch-inlay-head {
  display: flex;
  align-items: center;
  gap: 10px;
  flex-wrap: wrap;
  margin-bottom: 6px;
  color: var(--ch-text-primary);
}

.ch-inlay-badge {
  font-family: var(--ch-font-mono);
  font-size: 10.5px;
  font-weight: 700;
  text-transform: uppercase;
  letter-spacing: 0.05em;
  padding: 2px 7px;
  border-radius: 3px;
  border: 1px solid var(--ch-border-strong);
}

.ch-inlay-badge[data-tone='proved'] {
  color: var(--ch-status-proved);
  border-color: var(--ch-status-proved-bdr);
  background: var(--ch-status-proved-dim);
}
.ch-inlay-badge[data-tone='fail'] {
  color: var(--ch-status-fail);
  border-color: var(--ch-status-fail-bdr);
  background: var(--ch-status-fail-dim);
}
.ch-inlay-badge[data-tone='warn'] {
  color: var(--ch-status-warn);
  border-color: var(--ch-status-warn-bdr);
  background: var(--ch-status-warn-dim);
}

.ch-inlay-detail {
  margin: 0;
  color: var(--ch-text-secondary);
}
```

### Data table — `site.css:2020-2107`

```css
.ch-table-card {
  background: var(--ch-bg-card);
  border: 1px solid var(--ch-border-subtle);
  border-radius: 4px;
  overflow-x: auto;
}

.ch-table-meta {
  display: flex;
  align-items: center;
  justify-content: space-between;
  gap: 12px;
  flex-wrap: wrap;
  padding: 10px 14px;
  background: var(--ch-bg-bar);
  border-bottom: 1px solid var(--ch-border-subtle);
  font-family: var(--ch-font-mono);
  font-size: 11.5px;
  color: var(--ch-text-muted);
}

.ch-table {
  width: 100%;
  border-collapse: collapse;
  font-size: 13px;
}

.ch-table th {
  text-align: left;
  padding: 10px 12px;
  background: var(--ch-bg-bar);
  border-bottom: 1px solid var(--ch-border-subtle);
  font-family: var(--ch-font-mono);
  font-size: 10.5px;
  font-weight: 600;
  letter-spacing: 0.06em;
  text-transform: uppercase;
  color: var(--ch-text-muted);
  white-space: nowrap;
}

.ch-table td {
  padding: 10px 12px;
  border-bottom: 1px solid var(--ch-border-subtle);
  vertical-align: top;
  line-height: 1.48;
  color: var(--ch-text-secondary);
}

.ch-table tbody tr:last-child td { border-bottom: none; }
.ch-table tbody tr:hover td { background: var(--ch-bg-card-hover); }

.ch-table-interactive tbody tr { cursor: pointer; }

.ch-table-interactive tbody tr[data-selected='true'] td {
  background: var(--ch-accent-dim);
  color: var(--ch-text-primary);
}

.ch-num {
  text-align: right;
  font-variant-numeric: tabular-nums;
}

.ch-cell-primary {
  color: var(--ch-text-primary);
  font-weight: 500;
}

.ch-cell-sub {
  margin-top: 2px;
  font-size: 12px;
  color: var(--ch-text-muted);
}

.ch-total-row td {
  background: var(--ch-bg-bar);
  border-top: 1px solid var(--ch-border-strong);
  font-weight: 700;
  color: var(--ch-text-primary);
}
```

### Source link — `site.css:2109-2123`

```css
.ch-mono-link {
  display: inline-flex;
  align-items: center;
  gap: 3px;
  font-family: var(--ch-font-mono);
  font-size: 12px;
  font-weight: 600;
  color: var(--ch-accent-text);
  text-decoration: underline;
  text-underline-offset: 3px;
}

.ch-mono-link:hover {
  filter: brightness(1.15);
}
```

### Architecture diagram — `site.css:1683-1873`

```css
.ch-arch-section {
  padding-top: 44px;
  border-top: 1px solid var(--ch-border-subtle);
  display: flex;
  flex-direction: column;
  gap: 24px;
  scroll-margin-top: 70px;
}

.ch-arch-split {
  display: grid;
  grid-template-columns: minmax(0, 5fr) minmax(0, 7fr);
  gap: 24px;
  align-items: stretch;
}

.ch-iso-frame {
  margin: 0;
  background: var(--ch-bg-card);
  border: 1px solid var(--ch-border-subtle);
  border-radius: 6px;
  overflow: hidden;
  display: flex;
  flex-direction: column;
}

.ch-iso-frame img {
  display: block;
  width: 100%;
  height: auto;
  flex: 1 1 auto;
  object-fit: cover;
}

.ch-iso-frame figcaption {
  padding: 12px 16px;
  border-top: 1px solid var(--ch-border-subtle);
  font-size: 12.5px;
  line-height: 1.55;
  color: var(--ch-text-muted);
}

.ch-arch-diagram {
  padding: 18px;
  background: var(--ch-bg-card);
  border: 1px solid var(--ch-border-subtle);
  border-radius: 6px;
  display: flex;
  flex-direction: column;
  gap: 12px;
}

.ch-tier-head {
  font-family: var(--ch-font-mono);
  font-size: 10.5px;
  font-weight: 600;
  text-transform: uppercase;
  letter-spacing: 0.08em;
  color: var(--ch-text-muted);
  margin-bottom: 8px;
}

.ch-ingress-row {
  display: grid;
  grid-template-columns: minmax(0, 1fr) auto minmax(0, 1fr);
  gap: 10px;
  align-items: center;
}

.ch-flow-arrow {
  color: var(--ch-text-muted);
  display: inline-flex;
  align-items: center;
}

.ch-tier-connector {
  display: flex;
  align-items: center;
  justify-content: center;
  gap: 8px;
  font-family: var(--ch-font-mono);
  font-size: 11px;
  color: var(--ch-status-proved);
}

.ch-kernel-shell {
  padding: 14px;
  background: var(--ch-status-proved-dim);
  border: 1px solid var(--ch-status-proved-bdr);
  border-radius: 5px;
  display: flex;
  flex-direction: column;
  gap: 10px;
}

.ch-kernel-head {
  display: flex;
  align-items: center;
  justify-content: space-between;
  gap: 10px;
  flex-wrap: wrap;
  font-family: var(--ch-font-mono);
  font-size: 11.5px;
  font-weight: 700;
  letter-spacing: 0.08em;
  color: var(--ch-status-proved);
}

.ch-kernel-tag {
  font-weight: 500;
  letter-spacing: 0.02em;
  color: var(--ch-text-secondary);
}

.ch-kernel-grid,
.ch-renderers-grid {
  display: grid;
  grid-template-columns: repeat(3, minmax(0, 1fr));
  gap: 10px;
}

.ch-node {
  padding: 10px 12px;
  background: var(--ch-bg-card);
  border: 1px solid var(--ch-border-subtle);
  border-radius: 4px;
}

.ch-node[data-trust='verified'] {
  border-color: var(--ch-status-proved-bdr);
}

.ch-node[data-trust='untrusted'] {
  border-style: dashed;
  border-color: var(--ch-border-strong);
}

.ch-node-title {
  font-family: var(--ch-font-mono);
  font-size: 12px;
  font-weight: 700;
  color: var(--ch-text-primary);
}

.ch-node-sub {
  margin-top: 4px;
  font-size: 11.5px;
  line-height: 1.48;
  color: var(--ch-text-muted);
}

.ch-kernel-foot {
  font-size: 12px;
  color: var(--ch-text-secondary);
}

.ch-ipc-rail {
  display: flex;
  align-items: center;
  justify-content: center;
  gap: 10px;
  padding: 7px 12px;
  background: var(--ch-accent-dim);
  border: 1px dashed var(--ch-accent-bdr);
  border-radius: 4px;
  font-family: var(--ch-font-mono);
  font-size: 11.5px;
  color: var(--ch-accent-text);
  text-align: center;
}

.ch-arch-caption {
  margin: 4px 0 0;
  font-size: 13px;
  line-height: 1.58;
  color: var(--ch-text-secondary);
}

.ch-arch-caption strong { color: var(--ch-text-primary); }
```

---

## `@clickhouse/click-ui` usage (external, v0.16)

| Import | Where | Role |
|---|---|---|
| `ClickUIProvider` | `site/src/App.tsx:113` | Wraps the whole app; receives `theme` (`'dark' \| 'light'`) |
| `Switch` | `site/src/App.tsx:156` | Light/dark toggle in the topbar; `data-testid="theme-switch"` |
| `Badge` | `SectionVerus.tsx`, `SectionStatus.tsx`, `SectionCoverage.tsx` | Status chips |
| `Button` | `SectionVerus.tsx` | Action buttons in the live-proof workbench |

These render with Click UI's own styled-components theme, **not** the `--ch-*` layer. When a new
surface needs a button or badge, prefer the app's own `.ch-*` classes so the page stays visually
consistent with the hand-written system.
