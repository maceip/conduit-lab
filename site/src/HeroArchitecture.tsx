import React, { useState } from 'react';
import { NR, crateOk, sumTrusted, type Ratchet, type RatchetCrate } from './data';

export type SubsystemOwnership = 'verified' | 'implementing' | 'delegated';

export interface BrowserSubsystem {
  id: string;
  label: string;
  title: string;
  ownership: SubsystemOwnership;
  crates: string[];
  row: 'ingress' | 'renderer';
  role: string;
  boundary: string;
}

/**
 * Canonical browser engine component map shared 1-to-1 between the left pipeline
 * flowchart and the right browser wireframe treemap (docs/verified-browser-engine.md §3.2).
 */
export const BROWSER_SUBSYSTEMS: BrowserSubsystem[] = [
  {
    id: 'net',
    label: 'tls / net',
    title: 'TLS & Network Ingress',
    ownership: 'delegated',
    crates: [],
    row: 'ingress',
    role: 'Untrusted rustls sockets; X.509 certificate validation delegated to Verdict.',
    boundary: 'External dependency — not rewritten from scratch',
  },
  {
    id: 'vurl',
    label: 'vurl',
    title: 'WHATWG URL Parser',
    ownership: 'verified',
    crates: ['vurl'],
    row: 'ingress',
    role: 'Percent-encoding, IPv4/IPv6 canonicalization, and spec-equivalent URL parsing.',
    boundary: 'Formally verified in Rust + Verus',
  },
  {
    id: 'kernel',
    label: 'kernel',
    title: 'Security Kernel & Policy',
    ownership: 'implementing',
    crates: [],
    row: 'ingress',
    role: 'Origin isolation, SOP/CSP/CORS policies (rspec!), address-bar integrity, and Vest IPC.',
    boundary: 'In active Rust + Verus development',
  },
  {
    id: 'html_css',
    label: 'html / css',
    title: 'HTML, CSS & Layout',
    ownership: 'implementing',
    crates: [],
    row: 'renderer',
    role: 'HTML5 tokenizer, DOM invariants, and CSS layout — ratcheting from untrusted Rust to Verus.',
    boundary: 'In active Rust + Verus development',
  },
  {
    id: 'vjs',
    label: 'vjs',
    title: 'JavaScript Engine (vjs)',
    ownership: 'verified',
    crates: [
      'vjs_spec',
      'vjs_types',
      'vjs_object',
      'vjs_syntax',
      'vjs',
      'vjs_builtins',
      'vjs_gc',
      'vjs_vm',
    ],
    row: 'renderer',
    role: 'Safe-Rust ECMA-262 lexer, parser, arena heap, tricolor GC, interpreter, and bytecode VM.',
    boundary: 'Formally verified in Rust + Verus',
  },
  {
    id: 'webidl',
    label: 'webidl',
    title: 'Web IDL Capability Bridge',
    ownership: 'verified',
    crates: ['vjs_webidl'],
    row: 'renderer',
    role: 'Verified ToJS/ToIDL conversions and kernel-issued capability handles with zero ambient authority.',
    boundary: 'Formally verified in Rust + Verus',
  },
  {
    id: 'vwasm',
    label: 'vwasm',
    title: 'WebAssembly 1.0 Runtime',
    ownership: 'verified',
    crates: ['vwasm'],
    row: 'renderer',
    role: 'Verified Wasm 1.0 LEB128 binary decoder and sandbox-contained interpreter.',
    boundary: 'Formally verified in Rust + Verus',
  },
  {
    id: 'dawn',
    label: 'dawn',
    title: 'GPU, WebGPU & Raster (Dawn)',
    ownership: 'delegated',
    crates: [],
    row: 'renderer',
    role: 'Compositor, Skia-class raster, and WebGPU/ANGLE stack — contained per-site, not rewritten in Verus.',
    boundary: 'Not implementing directly — isolated per-site',
  },
  {
    id: 'sandbox',
    label: 'sandbox',
    title: 'Per-Site Process Sandbox',
    ownership: 'delegated',
    crates: [],
    row: 'renderer',
    role: 'Nanvix micro-VM / OS process containment bounding unverified rendering and GPU layers.',
    boundary: 'Isolation substrate — hosts untrusted layers',
  },
];

interface LiveSubsystemState {
  tone: 'proved' | 'implementing' | 'delegated' | 'fail' | 'neutral';
  matchedCrates: RatchetCrate[];
  verifiedQueries: number | null;
  sourceLines: number | null;
  trustedCount: number | null;
  statusText: string;
}

function resolveLiveState(sub: BrowserSubsystem, ratchet: Ratchet | null): LiveSubsystemState {
  if (sub.ownership === 'implementing') {
    return {
      tone: 'implementing',
      matchedCrates: [],
      verifiedQueries: null,
      sourceLines: null,
      trustedCount: null,
      statusText: 'Implementing in Rust',
    };
  }
  if (sub.ownership === 'delegated') {
    return {
      tone: 'delegated',
      matchedCrates: [],
      verifiedQueries: null,
      sourceLines: null,
      trustedCount: null,
      statusText: 'Not implementing directly',
    };
  }
  if (!ratchet) {
    return {
      tone: 'neutral',
      matchedCrates: [],
      verifiedQueries: null,
      sourceLines: null,
      trustedCount: null,
      statusText: NR,
    };
  }
  const matched = sub.crates
    .map((name) => ratchet.crates.find((c) => c.name === name))
    .filter((c): c is RatchetCrate => Boolean(c));
  const allPresent = matched.length === sub.crates.length && matched.length > 0;
  const ok = allPresent && matched.every((c) => crateOk(c));
  const queries = matched.reduce((acc, c) => acc + c.verified, 0);
  const lines = matched.reduce((acc, c) => acc + c.source_lines, 0);
  const trusted = matched.reduce((acc, c) => acc + (sumTrusted(c.trusted) ?? 0), 0);
  return {
    tone: ok ? 'proved' : 'fail',
    matchedCrates: matched,
    verifiedQueries: allPresent ? queries : null,
    sourceLines: allPresent ? lines : null,
    trustedCount: allPresent ? trusted : null,
    statusText: ok ? 'Verified in Rust (Verus)' : 'Verification check failed',
  };
}

export const HeroArchitecturePair: React.FC<{
  ratchet: Ratchet | null;
  leftSlotTop?: React.ReactNode;
}> = ({ ratchet, leftSlotTop }) => {
  const [selectedId, setSelectedId] = useState<string>('vjs');
  const [hoveredId, setHoveredId] = useState<string | null>(null);

  const activeId = hoveredId ?? selectedId;
  const states = new Map<string, LiveSubsystemState>(
    BROWSER_SUBSYSTEMS.map((s) => [s.id, resolveLiveState(s, ratchet)]),
  );
  const activeSub = BROWSER_SUBSYSTEMS.find((s) => s.id === activeId) ?? BROWSER_SUBSYSTEMS[4];
  const activeLive = states.get(activeSub.id)!;

  const ingressFlow = BROWSER_SUBSYSTEMS.filter((s) => s.row === 'ingress');
  const rendererFlow = BROWSER_SUBSYSTEMS.filter((s) => s.row === 'renderer' && s.id !== 'sandbox');
  const sandboxSub = BROWSER_SUBSYSTEMS.find((s) => s.id === 'sandbox')!;

  const renderFlowNode = (sub: BrowserSubsystem) => {
    const live = states.get(sub.id)!;
    const isActive = activeId === sub.id;
    const isSelected = selectedId === sub.id;
    return (
      <button
        key={sub.id}
        type="button"
        className="ch-flow-pill"
        data-ownership={sub.ownership}
        data-tone={live.tone}
        data-active={isActive}
        aria-pressed={isSelected}
        data-testid={`flowchart-node-${sub.id}`}
        onClick={() => setSelectedId(sub.id)}
        onMouseEnter={() => setHoveredId(sub.id)}
        onMouseLeave={() => setHoveredId(null)}
        onFocus={() => setHoveredId(sub.id)}
        onBlur={() => setHoveredId(null)}
      >
        <span className="ch-flow-pill-label">{sub.label}</span>
      </button>
    );
  };

  const renderMapCell = (id: string, extraClass = '', compact = false) => {
    const sub = BROWSER_SUBSYSTEMS.find((s) => s.id === id)!;
    const live = states.get(sub.id)!;
    const isActive = activeId === sub.id;
    const isSelected = selectedId === sub.id;
    const subMeta =
      sub.ownership === 'verified'
        ? live.verifiedQueries !== null
          ? `${live.verifiedQueries.toLocaleString('en-US')} q`
          : NR
        : sub.ownership === 'implementing'
          ? 'rust · wip'
          : 'external';
    return (
      <button
        type="button"
        className={`ch-tmap-cell ${extraClass}`.trim()}
        data-ownership={sub.ownership}
        data-tone={live.tone}
        data-active={isActive}
        aria-pressed={isSelected}
        data-testid={`treemap-cell-${sub.id}`}
        onClick={() => setSelectedId(sub.id)}
        onMouseEnter={() => setHoveredId(sub.id)}
        onMouseLeave={() => setHoveredId(null)}
        onFocus={() => setHoveredId(sub.id)}
        onBlur={() => setHoveredId(null)}
      >
        <span className="ch-tmap-name">{sub.label}</span>
        {!compact && <span className="ch-tmap-meta">{subMeta}</span>}
      </button>
    );
  };

  return (
    <div className="ch-hero-grid" data-testid="hero-architecture-grid">
      {/* Left Column: Hero Liquid-Glass Thesis Card + Synchronized Component Flowchart */}
      <div className="ch-hero-left-col">
        {leftSlotTop}

        <section
          className="ch-arch-panel ch-flowchart-panel"
          aria-label="Browser component flowchart"
          data-testid="browser-flowchart"
        >
          <header className="ch-arch-panel-head">
            <span className="ch-arch-panel-title">Browser pipeline</span>
            <div className="ch-arch-legend" aria-label="Component ownership legend">
              <span className="ch-arch-key">
                <i className="ch-arch-swatch" data-swatch="verified" aria-hidden="true" />
                Verified
              </span>
              <span className="ch-arch-key">
                <i className="ch-arch-swatch" data-swatch="implementing" aria-hidden="true" />
                In progress
              </span>
              <span className="ch-arch-key">
                <i className="ch-arch-swatch" data-swatch="delegated" aria-hidden="true" />
                Not direct
              </span>
            </div>
          </header>

          <div className="ch-flow-body">
            <div className="ch-flow-track" aria-label="Ingress and kernel flow">
              <span className="ch-flow-track-tag">Host</span>
              <div className="ch-flow-chain">
                {ingressFlow.map((sub, i) => (
                  <React.Fragment key={sub.id}>
                    {renderFlowNode(sub)}
                    {i < ingressFlow.length - 1 && (
                      <span className="ch-flow-arrow" aria-hidden="true">
                        →
                      </span>
                    )}
                  </React.Fragment>
                ))}
              </div>
            </div>

            <div className="ch-flow-ipc-bridge" aria-hidden="true">
              <span className="ch-flow-ipc-line" />
              <span className="ch-flow-ipc-label">typed IPC</span>
              <span className="ch-flow-ipc-line" />
            </div>

            <div className="ch-flow-track" aria-label="Per-site renderer flow">
              <span className="ch-flow-track-tag">Site</span>
              <div className="ch-flow-chain">
                {rendererFlow.map((sub, i) => (
                  <React.Fragment key={sub.id}>
                    {renderFlowNode(sub)}
                    {i < rendererFlow.length - 1 && (
                      <span className="ch-flow-arrow" aria-hidden="true">
                        →
                      </span>
                    )}
                  </React.Fragment>
                ))}
                <span className="ch-flow-sandbox-slot">{renderFlowNode(sandboxSub)}</span>
              </div>
            </div>
          </div>

          <div className="ch-arch-inspector" data-testid="arch-inspector">
            <div className="ch-arch-inspector-head">
              <strong className="ch-arch-inspector-name">{activeSub.title}</strong>
              <span className="ch-arch-inspector-status" data-tone={activeLive.tone}>
                {activeLive.statusText}
              </span>
            </div>
            <p className="ch-arch-inspector-role">{activeSub.role}</p>
            <div className="ch-arch-inspector-foot">
              {activeSub.ownership === 'verified' ? (
                <span>
                  {activeLive.verifiedQueries !== null
                    ? `${activeSub.crates.length} ${activeSub.crates.length === 1 ? 'crate' : 'crates'} · ${activeLive.verifiedQueries.toLocaleString('en-US')} proof queries · ${activeLive.sourceLines?.toLocaleString('en-US')} LOC · ${activeLive.trustedCount} trusted`
                    : `Live proof telemetry: ${NR}`}
                </span>
              ) : (
                <span>{activeSub.boundary}</span>
              )}
              {activeSub.ownership === 'verified' && (
                <a className="ch-mono-link" href="#ratchet">
                  Crate ledger →
                </a>
              )}
            </div>
          </div>
        </section>
      </div>

      {/* Right Column: Interactive Browser Wireframe Treemap */}
      <aside
        className="ch-arch-panel ch-browser-map-panel"
        aria-label="Browser wireframe subsystem treemap"
        data-testid="browser-treemap"
      >
        <header className="ch-arch-panel-head">
          <span className="ch-arch-panel-title">Browser anatomy treemap</span>
          <span className="ch-arch-panel-hint">Synchronized · hover or click</span>
        </header>

        <div className="ch-wireframe-shell">
          {/* Browser Window Chrome: Tab Strip (Kernel) + Address Bar (TLS/Net + vurl) */}
          <div className="ch-wf-chrome">
            <div className="ch-wf-tabbar">
              <div className="ch-wf-dots" aria-hidden="true">
                <span />
                <span />
                <span />
              </div>
              {renderMapCell('kernel', 'ch-tmap-kernel')}
            </div>

            <div className="ch-wf-addrbar">
              {renderMapCell('net', 'ch-tmap-net', true)}
              {renderMapCell('vurl', 'ch-tmap-vurl')}
            </div>
          </div>

          {/* Browser Viewport: Squarified Proportional Treemap of Renderer Subsystems */}
          <div className="ch-wf-viewport" role="group" aria-label="Browser viewport subsystem map">
            <div className="ch-tmap-grid">
              <div className="ch-tmap-col-left">
                {renderMapCell('vjs', 'ch-tmap-vjs')}
                <div className="ch-tmap-subrow">
                  {renderMapCell('webidl', 'ch-tmap-webidl')}
                  {renderMapCell('vwasm', 'ch-tmap-vwasm')}
                </div>
              </div>
              <div className="ch-tmap-col-right">
                {renderMapCell('html_css', 'ch-tmap-html')}
                {renderMapCell('dawn', 'ch-tmap-dawn')}
              </div>
            </div>
            {renderMapCell('sandbox', 'ch-tmap-sandbox')}
          </div>
        </div>
      </aside>
    </div>
  );
};

export default HeroArchitecturePair;
