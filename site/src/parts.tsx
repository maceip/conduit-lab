import React, { useEffect, useRef, useState } from 'react';
import type { ProofDagEdge, ProofDagNode } from './content/vurl';

export type Tone = 'proved' | 'warn' | 'fail' | 'neutral';
export type PlatePreset = 'assembled' | 'section' | 'exploded' | 'drawing';

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

export const PlateFrame: React.FC<{
  machine: 'turboprop' | 'maglev';
  title: string;
  subtitle: string;
  theme: 'dark' | 'light';
  defaultPreset?: PlatePreset;
  testId: string;
}> = ({ machine, title, subtitle, theme, defaultPreset = 'assembled', testId }) => {
  const [preset, setPreset] = useState<PlatePreset>(defaultPreset);
  const iframeRef = useRef<HTMLIFrameElement | null>(null);
  const initialThemeRef = useRef<'dark' | 'light'>(theme);
  const initialPresetRef = useRef<PlatePreset>(defaultPreset);

  useEffect(() => {
    iframeRef.current?.contentWindow?.postMessage({ type: 'conduit-theme', theme }, '*');
  }, [theme]);

  const selectPreset = (next: PlatePreset) => {
    setPreset(next);
    iframeRef.current?.contentWindow?.postMessage({ type: 'conduit-plate-state', preset: next }, '*');
  };

  const modes: Array<{ id: PlatePreset; label: string }> = [
    { id: 'assembled', label: 'Assembled' },
    { id: 'section', label: 'Cutaway' },
    { id: 'exploded', label: 'Exploded' },
    { id: 'drawing', label: 'Ortho' },
  ];

  return (
    <figure className="ch-plate-frame" data-testid={testId}>
      <header className="ch-plate-header">
        <div className="ch-plate-heading">
          <strong className="ch-plate-title">{title}</strong>
          <span className="ch-plate-sub">{subtitle}</span>
        </div>

        <div className="ch-plate-modes" role="group" aria-label={`${title} view modes`}>
          {modes.map((m) => (
            <button
              key={m.id}
              type="button"
              className="ch-plate-mode-btn"
              data-active={preset === m.id}
              data-testid={`${testId}-mode-${m.id}`}
              aria-pressed={preset === m.id}
              onClick={() => selectPreset(m.id)}
            >
              {m.label}
            </button>
          ))}
        </div>
      </header>

      <iframe
        ref={iframeRef}
        className="ch-inkwork-frame"
        src={`inkwork/index.html?embed=1&theme=${initialThemeRef.current}&preset=${initialPresetRef.current}#${machine}`}
        title={`${title} — ${subtitle}`}
        onLoad={(ev) => {
          ev.currentTarget.contentWindow?.postMessage({ type: 'conduit-theme', theme }, '*');
          ev.currentTarget.contentWindow?.postMessage({ type: 'conduit-plate-state', preset }, '*');
        }}
      />
    </figure>
  );
};

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
  <dl className="ch-arch-ledger" data-testid="shim-diagram" aria-label="Verified kernel and sandboxed renderer boundaries">
    <div className="ch-arch-row">
      <dt>Network ingress</dt>
      <dd>Untrusted <code>rustls</code> sockets feed Verdict X.509 certificate validation in Verus.</dd>
    </div>
    <div className="ch-arch-row">
      <dt>Verified security kernel</dt>
      <dd>
        <code>vurl</code> boundary parsers, SOP/CSP/CORS origin policy, and capability handle table
        (Verus).
      </dd>
    </div>
    <div className="ch-arch-row">
      <dt>Typed Vest IPC</dt>
      <dd>
        Capability handles cross into disposable per-site renderers running proved <code>vjs</code>{' '}
        (J0–J7), <code>vjs_webidl</code>, and <code>vwasm</code> alongside isolated HTML/CSS/GPU.
      </dd>
    </div>
  </dl>
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
                <rect width={nodeW} height={nodeH} rx={3} className="ch-dag-rect" />
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
