import React from 'react';
import type { WorkbenchTone } from '@maceip/ix-workbench-primitives';

export const SectionHead: React.FC<{
  index: string;
  title: string;
  children?: React.ReactNode;
}> = ({ index, title, children }) => (
  <div className="wb-section-head">
    <div className="wb-eyebrow">{index}</div>
    <h2>{title}</h2>
    {children && <p>{children}</p>}
  </div>
);

export const Stat: React.FC<{ value: string; label: string; tone?: WorkbenchTone }> = ({
  value,
  label,
  tone = 'neutral',
}) => (
  <div className="wb-stat" data-tone={tone}>
    <strong data-testid={`stat-${label}`}>{value}</strong>
    <span>{label}</span>
  </div>
);

export const ScaleCompare: React.FC<{
  items: Array<{
    id: string;
    label: string;
    lines: number;
    display: string;
    tone: WorkbenchTone;
    note: string;
  }>;
}> = ({ items }) => {
  const maxLog = Math.max(...items.map((i) => Math.log10(Math.max(i.lines, 1))));
  return (
    <div className="wb-scale" data-testid="scale-compare">
      {items.map((item) => (
        <div key={item.id} className="wb-scale-row">
          <div className="wb-scale-label">
            <span>{item.label}</span>
            <strong data-testid={`scale-${item.id}`}>{item.display}</strong>
          </div>
          <div className="wb-scale-track">
            <div
              className="wb-scale-bar"
              data-tone={item.tone}
              style={{ width: `${(Math.log10(Math.max(item.lines, 1)) / maxLog) * 100}%` }}
            />
          </div>
          <div className="wb-scale-note">{item.note}</div>
        </div>
      ))}
      <div className="wb-scale-axis">log₁₀ scale — each grid step is 10× more code</div>
    </div>
  );
};

export const ShimDiagram: React.FC = () => (
  <div className="wb-shim" data-testid="shim-diagram" aria-label="Verified shim architecture">
    <div className="wb-shim-row">
      <div className="wb-shim-box" data-trust="untrusted">
        <b>network</b>
        <span>rustls</span>
      </div>
      <div className="wb-shim-arrow">→</div>
      <div className="wb-shim-box" data-trust="verified">
        <b>TLS certificates</b>
        <span>Verdict (proved)</span>
      </div>
      <div className="wb-shim-arrow">→</div>
      <div className="wb-shim-kernel">
        <div className="wb-shim-kernel-title">VERIFIED KERNEL (Verus)</div>
        <div className="wb-shim-row">
          <div className="wb-shim-box" data-trust="verified">
            <b>Net parsers</b>
            <span>URL · HTTP · MIME · cookie</span>
          </div>
          <div className="wb-shim-box" data-trust="verified">
            <b>Origin / policy</b>
            <span>SOP · CSP · CORS · mixed content</span>
          </div>
          <div className="wb-shim-box" data-trust="verified">
            <b>Kernel</b>
            <span>tabs · IPC · nav · address bar</span>
          </div>
        </div>
      </div>
      <div className="wb-shim-arrow">→</div>
      <div className="wb-shim-box" data-trust="untrusted">
        <b>display</b>
        <span>pixels · input</span>
      </div>
    </div>
    <div className="wb-shim-ipc">typed IPC (Vest-encoded) — the only door between the two worlds</div>
    <div className="wb-shim-row">
      {[1, 2, 3].map((n) => (
        <div key={n} className="wb-shim-box wb-shim-renderer" data-trust="untrusted">
          <b>renderer · site {n === 3 ? '…' : n}</b>
          <span>html5ever · Stylo · JS · GPU — one Nanvix process per site</span>
        </div>
      ))}
    </div>
    <div className="wb-shim-caption">
      A compromised renderer can only misrender its own origin. That is the theorem the kernel
      proves — and the reason the browser is usable before most of it is verified.
    </div>
  </div>
);

export const Source: React.FC<{ href: string; children: React.ReactNode }> = ({ href, children }) => (
  <a className="wb-link" href={href} target="_blank" rel="noreferrer">
    {children}
  </a>
);