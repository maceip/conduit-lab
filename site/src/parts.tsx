import React, { useState } from 'react';
import { IconArrowDown, IconArrowRight } from './icons';
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
    <div className="ch-metric-value" data-tone={tone} data-testid={testId ?? `stat-${label}`}>
      {value}
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
        </div>
      ))}
      <div className="ch-scale-axis">Logarithmic scale (10× per step).</div>
    </div>
  );
};

export const ArchitectureDiagram: React.FC = () => (
  <div className="ch-arch-diagram" data-testid="shim-diagram" aria-label="Verified kernel and sandboxed renderer architecture">
    <div className="ch-ingress-row">
      <div className="ch-node" data-trust="untrusted">
        <div className="ch-node-title">TLS &amp; Sockets</div>
        <div className="ch-node-sub">rustls · untrusted network I/O</div>
      </div>
      <span className="ch-flow-arrow" aria-hidden="true">
        <IconArrowRight size={15} />
      </span>
      <div className="ch-node" data-trust="verified">
        <div className="ch-node-title">X.509 Validation</div>
        <div className="ch-node-sub">Verdict policy · Verus</div>
      </div>
    </div>

    <div className="ch-tier-connector" aria-hidden="true">
      <IconArrowDown size={14} />
    </div>

    <div className="ch-kernel-shell">
      <div className="ch-kernel-head">
        <span>VERIFIED SECURITY KERNEL (Verus)</span>
      </div>
      <div className="ch-kernel-grid">
        <div className="ch-node" data-trust="verified">
          <div className="ch-node-title">Boundary Parsers</div>
          <div className="ch-node-sub">vurl · HTTP · Cookie</div>
        </div>
        <div className="ch-node" data-trust="verified">
          <div className="ch-node-title">Origin Policy</div>
          <div className="ch-node-sub">SOP · CSP · CORS</div>
        </div>
        <div className="ch-node" data-trust="verified">
          <div className="ch-node-title">Capability Table</div>
          <div className="ch-node-sub">Tabs · Handles · UI</div>
        </div>
      </div>
    </div>

    <div className="ch-ipc-rail">
      <IconArrowDown size={13} />
      <span>Typed Vest IPC · capability handles only</span>
    </div>

    <div className="ch-renderers-grid ch-renderers-two">
      <div className="ch-node" data-trust="untrusted">
        <div className="ch-node-title">Per-Site Renderer (Origin A)</div>
        <div className="ch-node-sub">Proved vjs (J0–J7) + vjs_webidl + vwasm; sandboxed html5ever, Stylo, GPU</div>
      </div>
      <div className="ch-node" data-trust="untrusted">
        <div className="ch-node-title">Per-Site Renderer (Origin B)</div>
        <div className="ch-node-sub">Isolated Nanvix / OS process — no ambient sockets, cookies, or cross-origin memory</div>
      </div>
    </div>
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
          <strong>{nodes.length} obligations</strong> · {edges.length} edges
        </span>
        <span className="ch-dag-status" data-tone={verified ? 'proved' : 'fail'}>
          {verified ? 'All verified' : 'Check failed'}
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
            SPECS &amp; PRIMITIVES
          </text>
          <text x={colX[1]} y={22} className="ch-dag-colhead">
            IMPLEMENTATIONS &amp; THEOREMS
          </text>

          {edges.map((e) => {
            const a = pos.get(e.from);
            const b = pos.get(e.to);
            if (!a || !b) return null;
            const x1 = a.x + nodeW;
            const y1 = a.y + nodeH / 2;
            const x2 = b.x;
            const y2 = b.y + nodeH / 2;
            const mx = (x1 + x2) / 2;
            const active = !selectedId || e.from === selectedId || e.to === selectedId;
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
            <code>{selectedNode.label}</code> ·{' '}
            {upstream.size > 0
              ? `depends on ${Array.from(upstream).join(', ')}`
              : 'root spec'}{' '}
            {downstream.size > 0 ? `→ ${Array.from(downstream).join(', ')}` : ''}
          </span>
        ) : (
          <span>Click any node to trace dependencies.</span>
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
